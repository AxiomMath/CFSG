module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4SlcProj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7EndM

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def Asc82Sec9T0 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z g : G) (B : Subgroup G),
    Sec8Base G t L S z g B →
      (∃ s : G, orderOf s = 2 ∧ s ∈ centralizer ({t} : Set G) ∧
        ∃ α : ℤˣ, InducesTypeSome L s 6 (-1) 3 α) →
      ∃ (B' : Subgroup G) (t₀ : G), Sec9Ctx G t L S z g B' t₀

variable {G : Type} [Group G]

theorem sec9g_commute_of_commutator_central [Finite G] {L : Subgroup G} (hL : IsOm6M L) {s b : G}
    (hs : s ∈ normalizer (L : Set G)) (hb : b ∈ L) (hb2 : b * b = 1)
    (hc : s * b * s⁻¹ * b⁻¹ ∈ centerIn L) : s * b = b * s := by
  set c : G := s * b * s⁻¹ * b⁻¹ with hcdef
  have hcomm : ∀ k ∈ L, c * k = k * c := ((sec4_mem_centerIn_iff c).mp hc).2
  have hsq : (s * b * s⁻¹) * (s * b * s⁻¹) = 1 := by
    rw [show s * b * s⁻¹ * (s * b * s⁻¹) = s * (b * b) * s⁻¹ by group, hb2]
    group
  have heq : s * b * s⁻¹ = c * b := by rw [hcdef]; group
  have hcc : c * c = 1 := by
    have h : (c * b) * (c * b) = 1 := by rw [← heq]; exact hsq
    calc c * c = (c * c) * (b * b) := by rw [hb2, mul_one]
      _ = c * (c * b) * b := by group
      _ = c * (b * c) * b := by rw [hcomm b hb]
      _ = (c * b) * (c * b) := by group
      _ = 1 := h
  have hcL : c ∈ L := ((sec4_mem_centerIn_iff c).mp hc).1
  have hc1 : c = 1 := by
    by_contra hne
    have hcent : c ∈ centralizer (L : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (hcomm y hy).symm
    have hco : orderOf c = 2 := by
      have hdvd : orderOf c ∣ 2 :=
        orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact hcc)
      have hne1 : orderOf c ≠ 1 := fun h => hne (orderOf_eq_one_iff.mp h)
      have hpos : 0 < orderOf c := orderOf_pos c
      have hle : orderOf c ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
      omega
    exact (sec711M_not_central hL hcL hco) hcent
  have hcm : s * b * s⁻¹ * b⁻¹ = 1 := by rw [← hcdef]; exact hc1
  have h1 : s * b * s⁻¹ = b := mul_inv_eq_one.mp hcm
  calc s * b = (s * b * s⁻¹) * s := by group
    _ = b * s := by rw [h1]

end CFSG.OddStandard.SmallF3.Omega
