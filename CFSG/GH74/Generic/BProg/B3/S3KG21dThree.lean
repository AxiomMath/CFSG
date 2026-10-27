module

public import CFSG.GH74.Generic.BProg.B3.S3KG21dDesc
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.AutAlternatingFour
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.LinearThreeEquiv
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.LinearRingEquiv
public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.GH74.Generic.BProg.B3.S3KG

open Matrix Subgroup CFSG.GorensteinWalter

theorem ker_conj_eq_center {G : Type*} [Group G] :
    (MulAut.conj : G →* MulAut G).ker = center G := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
  constructor
  · intro h x
    have hx := congrArg (fun φ : MulAut G => φ x) h
    simp only [MulAut.conj_apply, MulAut.one_apply] at hx
    calc x * g = g * x * g⁻¹ * g := by rw [hx]
      _ = g * x := by group
  · intro h
    refine MulEquiv.ext fun x => ?_
    rw [MulAut.conj_apply, MulAut.one_apply, ← h x, mul_inv_cancel_right]

variable {F : Type} [Field F] [Finite F]

theorem card_psl_of_card_eq_three (h3 : Nat.card F = 3) :
    Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) = 12 := by
  have : Fintype F := Fintype.ofFinite F
  have e : ZMod 3 ≃+* F :=
    ZMod.ringEquivOfPrime F Nat.prime_three (by rw [← Nat.card_eq_fintype_card, h3])
  rw [← nat_card_psl2_zmod3]
  exact Nat.card_congr (psl2RingEquiv e.symm).toEquiv

theorem card_mulAut_psl_of_card_eq_three (h3 : Nat.card F = 3) :
    Nat.card (MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) = 24 := by
  have : Fintype F := Fintype.ofFinite F
  have e : ZMod 3 ≃+* F :=
    ZMod.ringEquivOfPrime F Nat.prime_three (by rw [← Nat.card_eq_fintype_card, h3])
  let eA : PSL2 F ≃* alternatingGroup (Fin 4) :=
    (psl2RingEquiv e.symm).trans psl2_three_equiv_alternatingGroup
  let eAut : Equiv.Perm (Fin 4) ≃* MulAut (alternatingGroup (Fin 4)) :=
    MulEquiv.ofBijective _ GroupTheory.AutAlternating.aut_alternatingGroup_four_bijective_conj
  have hPerm : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
    rw [Nat.card_perm]
    norm_num [Nat.card_eq_fintype_card, Nat.factorial]
  calc Nat.card (MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F))
      = Nat.card (MulAut (alternatingGroup (Fin 4))) := Nat.card_congr (MulAut.congr eA).toEquiv
    _ = Nat.card (Equiv.Perm (Fin 4)) := (Nat.card_congr eAut.toEquiv).symm
    _ = 24 := hPerm

theorem exists_inner_of_card_eq_three (h3 : Nat.card F = 3)
    (V : Subgroup (MulAut (Matrix.SpecialLinearGroup (Fin 2) F))) (h4 : 4 ≤ Nat.card V) :
    ∃ v ∈ V, v ≠ 1 ∧ ∃ s : Matrix.SpecialLinearGroup (Fin 2) F, v = MulAut.conj s := by
  classical
  have hF : ringChar F ≠ 2 := by
    have : Fintype F := Fintype.ofFinite F
    intro h2
    have h := FiniteField.even_card_iff_char_two.mp h2
    rw [← Nat.card_eq_fintype_card, h3] at h
    omega
  by_contra hcon
  push Not at hcon
  set I := (MulAut.conj : Matrix.SpecialLinearGroup (Fin 2) F →* MulAut _).range with hIdef
  have hinj : Function.Injective
      (fun p : V × I => (p.1 : MulAut (Matrix.SpecialLinearGroup (Fin 2) F)) * p.2) := by
    rintro ⟨⟨v, hv⟩, ⟨i, hi⟩⟩ ⟨⟨w, hw⟩, ⟨j, hj⟩⟩ h
    simp only at h
    have hvw : w⁻¹ * v = j * i⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h, mul_inv_cancel_right]
    obtain ⟨s, hs⟩ : w⁻¹ * v ∈ I := hvw ▸ mul_mem hj (inv_mem hi)
    have h1 : w⁻¹ * v = 1 := by
      by_contra hne
      exact hcon _ (mul_mem (inv_mem hw) hv) hne s hs.symm
    have hvw' : v = w := (inv_mul_eq_one.mp h1).symm
    subst hvw'
    have hij : i = j := mul_left_cancel h
    subst hij
    rfl
  have hI : Nat.card I = 12 := by
    rw [← card_psl_of_card_eq_three h3]
    exact Nat.card_congr ((QuotientGroup.quotientKerEquivRange _).symm.trans
      (QuotientGroup.quotientMulEquivOfEq ker_conj_eq_center)).toEquiv
  have hA := card_mulAut_psl_of_card_eq_three h3
  have : Finite (MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) :=
    Nat.finite_of_card_ne_zero (by rw [hA]; norm_num)
  have hAS : Nat.card (MulAut (Matrix.SpecialLinearGroup (Fin 2) F)) ≤ 24 :=
    hA ▸ Nat.card_le_card_of_injective _ (descend_injective hF)
  have : Finite (MulAut (Matrix.SpecialLinearGroup (Fin 2) F)) :=
    Finite.of_injective _ (descend_injective hF)
  have hle := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_prod, hI] at hle
  omega

end CFSG.GH74.Generic.BProg.B3.S3KG
