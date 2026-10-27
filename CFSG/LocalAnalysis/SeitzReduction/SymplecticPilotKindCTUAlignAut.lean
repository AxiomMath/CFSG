module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTUnitaryModel
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormRealization
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphUnitaryModel
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphTorusLift
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatStatement

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix
open CFSG.LieType.Universal.Unitary (SU antidiag conjTr mem_SU)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag

section Aut

variable {F : Type} [Field F] {f r : ℕ}

theorem ctua_unitaryFieldData (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 1 ≤ f) :
    UnitaryFieldData 2 f F :=
  ⟨Nat.prime_two, hf, by rw [hF, ← pow_mul, mul_comm]⟩

@[expose] noncomputable def ctuaAntidiagGL (r : ℕ) (F : Type) [Field F] : GL (Fin r) F :=
  ⟨antidiag r, antidiag r, CFSG.LieType.Universal.Unitary.antidiag_mul_self r,
    CFSG.LieType.Universal.Unitary.antidiag_mul_self r⟩

theorem coe_ctuaAntidiagGL :
    ((ctuaAntidiagGL r F : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) = antidiag r := rfl

theorem isPrimeFormGram_ctuaAntidiagGL : IsPrimeFormGram (ctuaAntidiagGL r F) where
  symm := by
    ext i j
    rw [transpose_apply, coe_ctuaAntidiagGL]
    simp only [antidiag, of_apply]
    by_cases h : i = Fin.rev j
    · rw [ite_eq_left h, ite_eq_left (by rw [h, Fin.rev_rev])]
    · rw [ite_eq_right h, ite_eq_right (fun h' => h (by rw [h', Fin.rev_rev]))]
  prime := by
    intro i j
    rw [coe_ctuaAntidiagGL]
    simp only [antidiag, of_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _

theorem map_unitaryInvolution_eq_bar [Finite F] [CharP F 2] (h : UnitaryFieldData 2 f F)
    (M : Matrix (Fin r) (Fin r) F) :
    M.map (unitaryInvolution F 2 f) = M.map h.bar := by
  ext i j
  rw [map_apply, map_apply, unitaryInvolution_apply, h.bar_apply]

theorem SU_eq_gramSU [Finite F] [CharP F 2] (h : UnitaryFieldData 2 f F) :
    SU (unitaryInvolution F 2 f) r = gramSU h (antidiag r : Matrix (Fin r) (Fin r) F) := by
  ext g
  rw [mem_SU, mem_gramSU, conjTr, map_unitaryInvolution_eq_bar h]
  exact and_comm

theorem conjTr_mul_antidiag_of_mem_primeFormUnitary [Finite F] [CharP F 2]
    (h : UnitaryFieldData 2 f F) {A : GL (Fin r) F}
    (hA : A ∈ primeFormUnitary h (antidiag r : Matrix (Fin r) (Fin r) F)) :
    conjTr (unitaryInvolution F 2 f) (A : Matrix (Fin r) (Fin r) F) * antidiag r *
      (A : Matrix (Fin r) (Fin r) F) = antidiag r := by
  rw [conjTr, map_unitaryInvolution_eq_bar h]
  exact mem_primeFormUnitary.1 hA

theorem isPerfect_SU_ctua [Finite F] [CharP F 2] (hF : Nat.card F = (2 ^ f) ^ 2) (hr : 3 ≤ r)
    (hrq : ¬(r = 3 ∧ 2 ^ f = 2)) : Group.IsPerfect (SU (unitaryInvolution F 2 f) r) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq := CFSG.LieType.Universal.Unitary.isQuasisimple_SU (F := F) (p := 2) (f := f) hF hr
    (fun h' => hrq ⟨(Prod.mk.inj h').1, (Prod.mk.inj h').2⟩)
  exact hq.1

theorem exists_conj_glAut_of_mulAut_SU [Finite F] [CharP F 2] (hF : Nat.card F = (2 ^ f) ^ 2)
    (hf : 1 ≤ f) (hr : 3 ≤ r) (hrq : ¬(r = 3 ∧ 2 ^ f = 2))
    (α : MulAut (SU (unitaryInvolution F 2 f) r)) :
    ∃ (A : GL (Fin r) F) (φ : F ≃+* F),
      conjTr (unitaryInvolution F 2 f) (A : Matrix (Fin r) (Fin r) F) * antidiag r *
        (A : Matrix (Fin r) (Fin r) F) = antidiag r ∧
      ∀ x, ((α x : SU (unitaryInvolution F 2 f) r) : GL (Fin r) F) =
        A * glAut φ (x : GL (Fin r) F) * A⁻¹ := by
  set h := ctua_unitaryFieldData hF hf with hh
  have hC : IsPrimeFormGram (ctuaAntidiagGL r F) := isPrimeFormGram_ctuaAntidiagGL
  set C : Matrix (Fin r) (Fin r) F := ((ctuaAntidiagGL r F : GL (Fin r) F) :
    Matrix (Fin r) (Fin r) F) with hCdef
  have hE : SU (unitaryInvolution F 2 f) r = gramSU h C := SU_eq_gramSU h
  set E : SU (unitaryInvolution F 2 f) r ≃* gramSU h C := MulEquiv.subgroupCongr hE with hEdef
  set β : MulAut (gramSU h C) := (E.symm.trans α).trans E with hβdef
  set Q : gramSU h C ⧸ center (gramSU h C) ≃* primeFormP h C :=
    QuotientGroup.quotientMulEquivOfEq
      (F4Pilot.center_gramSU_eq_normOneScalars h hC hr hrq) with hQdef
  set αb : MulAut (primeFormP h C) := MulAut.congr Q (F4Pilot.centerQuotientAut β) with hαb
  have hαbmk : ∀ g : gramSU h C, αb (g : primeFormP h C) = ((β g : gramSU h C) :
      primeFormP h C) := by
    intro g
    rw [hαb, MulAut.congr_apply]
    have e1 : Q.symm (g : primeFormP h C) = QuotientGroup.mk' _ g := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    rw [MulEquiv.trans_apply, MulEquiv.trans_apply, e1, F4Pilot.centerQuotientAut_mk]
    rfl
  obtain ⟨⟨A, φ⟩, hAφ⟩ := primeFormPsi_surjective h hC hr hrq αb
  set γ : MulAut (gramSU h C) := (primeFormFieldSU h hC φ).trans (primeFormConjSU h C A)
    with hγdef
  have : Group.IsPerfect (gramSU h C) := by
    have := isPerfect_SU_ctua hF hr hrq
    exact Group.IsPerfect.ofSurjective (f := E.toMonoidHom) E.surjective
  have hβγ : β = γ := by
    refine F4Pilot.graphTorus_mulAut_eq_of_inv_mul_mem_center fun g => ?_
    apply normOneScalars_le_center h _ r
    rw [← QuotientGroup.eq]
    rw [← hαbmk, ← hAφ, primeFormPsi_apply, MulAut.mul_apply]
    change primeFormConjAut h C A (primeFormFieldAut h hC φ (g : primeFormP h C)) = _
    rw [primeFormFieldAut_mk, primeFormConjAut_mk]
    rfl
  refine ⟨A, φ, conjTr_mul_antidiag_of_mem_primeFormUnitary h A.2, fun x => ?_⟩
  have e1 : E (α x) = β (E x) := by
    rw [hβdef, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  have e2 : ((E (α x) : gramSU h C) : GL (Fin r) F) = ((α x : SU _ r) : GL (Fin r) F) := rfl
  rw [← e2, e1, hβγ]
  rfl

end Aut

end CFSG.SeitzReduction.SymplecticPilot
