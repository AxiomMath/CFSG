module

public import CFSG.LocalAnalysis.ComponentClassification.Sol78Functor
public import CFSG.LocalAnalysis.SignalizerFunctor.AmbientCommutators

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup

variable {X : Type} [Group X]

theorem map_pPrimeCore_map_subtype (φ : MulAut X) (H : Subgroup X) :
    ((pPrimeCore 2 H).map H.subtype).map φ.toMonoidHom =
      (pPrimeCore 2 (H.map φ.toMonoidHom)).map (H.map φ.toMonoidHom).subtype := by
  let ψ : H ≃* H.map φ.toMonoidHom := φ.subgroupMap H
  rw [← pPrimeCore_map_iso 2 ψ, Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem map_pPrimeCore_map_subtype_of_eq (φ : MulAut X) {H K : Subgroup X}
    (hK : H.map φ.toMonoidHom = K) :
    ((pPrimeCore 2 H).map H.subtype).map φ.toMonoidHom = (pPrimeCore 2 K).map K.subtype := by
  subst hK
  exact map_pPrimeCore_map_subtype φ H

theorem map_centralizer_singleton_aut (φ : MulAut X) (b : X) :
    (centralizer ({b} : Set X)).map φ.toMonoidHom = centralizer ({φ b} : Set X) := by
  ext h
  simp only [mem_map, mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨g, hg, rfl⟩
    rw [← map_mul, ← map_mul, hg]
  · intro hh
    refine ⟨φ.symm h, ?_, by simp⟩
    apply φ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hh

theorem map_centralizer_aut (φ : MulAut X) (E : Subgroup X) :
    (centralizer (E : Set X)).map φ.toMonoidHom =
      centralizer ((E.map φ.toMonoidHom : Subgroup X) : Set X) := by
  ext h
  simp only [mem_map, mem_centralizer_iff, MulEquiv.coe_toMonoidHom, SetLike.mem_coe]
  constructor
  · rintro ⟨g, hg, rfl⟩ _ ⟨e, he, rfl⟩
    rw [← map_mul, ← map_mul, hg e he]
  · intro hh
    refine ⟨φ.symm h, fun e he => ?_, by simp⟩
    apply φ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hh _ ⟨e, he, rfl⟩

theorem thetaFunctor_map_aut (φ : MulAut X) (E : Subgroup X) (b : X) :
    (SolAltLit.thetaFunctor E b).map φ.toMonoidHom =
      SolAltLit.thetaFunctor (E.map φ.toMonoidHom) (φ b) := by
  unfold SolAltLit.thetaFunctor
  rw [Subgroup.map_sup, Subgroup.map_commutator, Subgroup.map_inf _ _ _ φ.injective,
    map_pPrimeCore_map_subtype_of_eq φ (map_centralizer_singleton_aut φ b),
    map_pPrimeCore_map_subtype_of_eq φ (map_centralizer_aut φ E)]

theorem signalizerCompletion_map_aut (φ : MulAut X) (E B : Subgroup X) :
    (Sol78.signalizerCompletion E B).map φ.toMonoidHom =
      Sol78.signalizerCompletion (E.map φ.toMonoidHom) (B.map φ.toMonoidHom) := by
  unfold Sol78.signalizerCompletion
  simp only [Subgroup.map_iSup, thetaFunctor_map_aut]
  apply le_antisymm
  · refine iSup₂_le fun b hb => iSup_le fun hb1 => ?_
    refine le_iSup₂_of_le (f := fun (c : X) (_ : c ∈ B.map φ.toMonoidHom) =>
      ⨆ (_ : c ≠ 1), SolAltLit.thetaFunctor (E.map φ.toMonoidHom) c) (φ b) ⟨b, hb, rfl⟩
      (le_iSup_of_le (fun h => hb1 (φ.injective (by rw [h, map_one]))) le_rfl)
  · refine iSup₂_le fun c hc => iSup_le fun hc1 => ?_
    obtain ⟨b, hb, rfl⟩ := hc
    refine le_iSup₂_of_le (f := fun (b : X) (_ : b ∈ B) =>
      ⨆ (_ : b ≠ 1), SolAltLit.thetaFunctor (E.map φ.toMonoidHom) (φ b)) b hb
      (le_iSup_of_le (fun h => hc1 (by rw [MulEquiv.coe_toMonoidHom, h, map_one])) le_rfl)

theorem normalizer_le_normalizer_signalizerCompletion_self (F : Subgroup X) :
    normalizer (F : Set X) ≤ normalizer (Sol78.signalizerCompletion F F : Set X) := by
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq] at hg ⊢
  have h1 := signalizerCompletion_map_aut (MulAut.conj g) F F
  have hg' : F.map (MulAut.conj g).toMonoidHom = F := hg
  rw [hg'] at h1
  exact h1

theorem oddCore_le_normalizer_of_theta [Finite X] {E W : Subgroup X} {b : X}
    (hE : IsPGroup 2 E) (hEb : E ≤ centralizer ({b} : Set X))
    (hθ : SolAltLit.thetaFunctor E b ≤ W)
    (hN : normalizer (E : Set X) ≤ normalizer (W : Set X)) :
    (pPrimeCore 2 (centralizer ({b} : Set X))).map (centralizer ({b} : Set X)).subtype ≤
      normalizer (W : Set X) := by
  set O := (pPrimeCore 2 (centralizer ({b} : Set X))).map (centralizer ({b} : Set X)).subtype
    with hOdef
  have hEO : E ≤ normalizer (O : Set X) :=
    hEb.trans (Sol78.le_normalizer_map_subtype (pPrimeCore 2 (centralizer ({b} : Set X))))
  have hcop : Nat.Coprime 2 (Nat.card O) := by
    rw [hOdef, Subgroup.card_map_of_injective (centralizer ({b} : Set X)).subtype_injective]
    exact pPrimeCore_coprime_card
  rw [← SignalizerFunctor.Helpers.coprime_normalized_commutator_factorization 2 Nat.prime_two
    E O hE hEO hcop]
  refine sup_le ?_ ?_
  · exact (le_sup_left.trans hθ).trans le_normalizer
  · intro x hx
    exact hN (Subgroup.centralizer_le_normalizer (E : Set X) (mem_inf.mp hx).2)

end CFSG.ComponentClassification.SolMax
