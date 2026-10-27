module

public import CFSG.ClassicalInvolution.Asc77.AscThmAMain

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.ClassicalInvolution.Generic

variable {p f : ℕ} [Fact p.Prime]

theorem exists_normal_simple_of_l17_3 (h : L17_3 p f) (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} (hΩ : HypOmegaMod p f Ω)
    (hsolv : ∀ N : Subgroup G, N.Normal → Group.IsSolvable ↥N → N = ⊥)
    (hgen : (⨆ J ∈ Ω, J) = ⊤) {K : Subgroup G} (hK : K ∈ Ω)
    (htrans : ∀ J ∈ Ω, ∃ g : G, conjSub g K = J) :
    ∃ F : Subgroup G, F.Normal ∧ IsSimpleGroup ↥F ∧ (∃ x ∈ F, ∃ y ∈ F, x * y ≠ y * x) ∧
      Subgroup.centralizer (F : Set G) = ⊥ := by
  obtain ⟨z, hz⟩ := hΩ.exists_uniqueInvolution hp hq hK
  obtain ⟨L, hL, hLn, -, -, h3⟩ := h hp hq G Ω hΩ hsolv hgen K hK z hz
  obtain ⟨hs, hC⟩ := h3 (Or.inl htrans)
  refine ⟨L, hLn, hs, ?_, hC⟩
  by_contra hab
  push Not at hab
  have hQ : CFSG.IsQuasisimple ↥L := ((CFSG.isComponent_iff_open L).mpr hL).1
  have hnt : Nontrivial ↥L := CFSG.LocalCores.isQuasisimple_nontrivial hQ
  have hle : ⁅L, L⁆ ≤ ⊥ := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    rw [Subgroup.mem_bot, commutatorElement_def, hab x hx y hy, mul_inv_cancel_right,
      mul_inv_cancel]
  have hperf : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.mp hQ.1
  exact (Subgroup.nontrivial_iff_ne_bot L).mp hnt (le_bot_iff.mp (hperf ▸ hle))

theorem exists_normal_simple_of_l6_2 (h62 : L6_2 p f) (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} (hΩ : HypOmegaMod p f Ω)
    (hsolv : ∀ N : Subgroup G, N.Normal → Group.IsSolvable ↥N → N = ⊥)
    (hgen : (⨆ J ∈ Ω, J) = ⊤) {K : Subgroup G} (hK : K ∈ Ω)
    (htrans : ∀ J ∈ Ω, ∃ g : G, conjSub g K = J) :
    ∃ F : Subgroup G, F.Normal ∧ IsSimpleGroup ↥F ∧ (∃ x ∈ F, ∃ y ∈ F, x * y ≠ y * x) ∧
      Subgroup.centralizer (F : Set G) = ⊥ :=
  exists_normal_simple_of_l17_3 (l17_3_of_l6_2 h62) hp hq hΩ hsolv hgen hK htrans

end CFSG.ClassicalInvolution.Asc77
