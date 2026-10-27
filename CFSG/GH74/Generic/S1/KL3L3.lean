module

public import CFSG.GH74.Generic.S1.KL3Ord
public import CFSG.GH74.Generic.S1.KL3Shape
public import CFSG.GH74.GLS.Stage4.SDWLayerFieldU

public section

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.IVK CFSG.GH74.GLS.IVK.Proofs2
  CFSG.ClassicalInvolution
open scoped MatrixGroups

namespace CFSG.GH74.Generic.S1

theorem kl3_solvable_of_quot {G : Type} [Group G] (N : Subgroup G) [N.Normal] [Finite N]
    (hN : Nat.card N = 1 ∨ Nat.card N = 3) [Group.IsSolvable (G ⧸ N)] : Group.IsSolvable G := by
  have hNs : Group.IsSolvable ↥N := by
    rcases hN with h | h
    · have : Subsingleton ↥N := (Nat.card_eq_one_iff_unique.1 h).1
      infer_instance
    · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have : IsCyclic ↥N := isCyclic_of_prime_card h
      infer_instance
  exact Group.isSolvable_of_ker_le_range N.subtype (QuotientGroup.mk' N) (by
    intro x hx
    exact ⟨⟨x, (QuotientGroup.eq_one_iff x).1 hx⟩, rfl⟩)


theorem kl3FamL3 : KL3FamL3 := by
  intro S _ _ _ p f hp hp2 hf hmodel F _ _ Pb yb hcfg
  obtain ⟨hF3, ⟨e⟩, hyb, hy2, hsolv⟩ := hcfg
  have hL : IsLnEps 3 S 1 (p ^ f) := by
    obtain ⟨-, K, hK1, hK2, hK, e'⟩ := hmodel
    exact Or.inl ⟨rfl, K, hK1, hK2, hK, e'⟩
  obtain ⟨F₀, hF₀, hFin, N, hN, hcard, hNcard, ⟨iso⟩⟩ := ivk_4_1a_L3 S p f hp hp2 hL yb hy2
  have hq : Group.IsSolvable (GL (Fin 2) F₀ ⧸ N) :=
    Group.isSolvable_of_isSolvable_injective (f := iso.symm.toMonoidHom) iso.symm.injective
  have hNfin : Finite N := by
    rcases hNcard with h | h <;> exact Nat.finite_of_card_ne_zero (by omega)
  have hGL : Group.IsSolvable (GL (Fin 2) F₀) := kl3_solvable_of_quot N hNcard
  have hSL : Group.IsSolvable SL(2, F₀) :=
    Group.isSolvable_of_isSolvable_injective (f := Matrix.SpecialLinearGroup.toGL)
      Matrix.SpecialLinearGroup.toGL_injective
  have hodd : Odd (Nat.card F₀) := by rw [hcard]; exact (hp.odd_of_ne_two hp2).pow
  have h3 := natCard_eq_three_of_isSolvable_sl2 hodd hSL
  rw [hcard] at h3
  obtain ⟨rfl, rfl⟩ := kl3_prime_pow_eq_three hp hf h3
  have h := kl5_card_mul_gcd_psl (n := 3) (by norm_num) hmodel
  rw [show Finset.Icc 2 3 = {2, 3} by rfl, Finset.prod_pair (by norm_num)] at h
  norm_num at h
  exact h

theorem kl3FamU3 : KL3FamU3 := by
  intro S _ _ _ p f hp hp2 hf hmodel F _ _ Pb yb hcfg
  obtain ⟨hF3, ⟨e⟩, hyb, hy2, hsolv⟩ := hcfg
  have hU : IsLnEps 3 S (-1) (p ^ f) := by
    obtain ⟨-, K, hK1, hK2, hK, e'⟩ := hmodel
    exact Or.inr ⟨rfl, K, hK1, hK2, hK, e'⟩
  obtain ⟨F₀, hF₀, hFin, N, hN, hcard, hNcard, ⟨iso⟩⟩ := ivk_4_1a_U3 S p f hp hp2 hU yb hy2
  have hq : Group.IsSolvable (↥(GU2Stated (p ^ f) F₀) ⧸ N) :=
    Group.isSolvable_of_isSolvable_injective (f := iso.symm.toMonoidHom) iso.symm.injective
  have hNfin : Finite N := by
    rcases hNcard with h | h <;> exact Nat.finite_of_card_ne_zero (by omega)
  have hGU : Group.IsSolvable ↥(GU2Stated (p ^ f) F₀) := kl3_solvable_of_quot N hNcard
  have hdata : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f F₀ :=
    ⟨hp, hf, by rw [hcard, ← pow_mul, mul_comm]⟩
  obtain ⟨k, hk, hkfin, hkcard, ⟨ek⟩⟩ :=
    CFSG.GH74.GLS.Stage4.Rest.FieldU3.sdwU_exists_ker_equiv hdata
  have hker : Group.IsSolvable ↥(CFSG.GH74.GLS.Stage4.Rest.FieldU3.sdwUDet (p ^ f) F₀).ker :=
    inferInstance
  have hSL : Group.IsSolvable SL(2, k) :=
    Group.isSolvable_of_isSolvable_injective (f := ek.symm.toMonoidHom) ek.symm.injective
  have hodd : Odd (Nat.card k) := by rw [hkcard]; exact (hp.odd_of_ne_two hp2).pow
  have h3 := natCard_eq_three_of_isSolvable_sl2 hodd hSL
  rw [hkcard] at h3
  obtain ⟨rfl, rfl⟩ := kl3_prime_pow_eq_three hp hf h3
  have h := kl5_card_mul_gcd_psu_three hmodel
  norm_num at h
  exact kl3_false_of_card (N := 6048) h (by decide) (kl3_dvd_card hF3 e)

end CFSG.GH74.Generic.S1
