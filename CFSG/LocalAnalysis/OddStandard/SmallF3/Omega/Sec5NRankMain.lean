module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5NRankPsi
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5NRankEx

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem sec5nr_main (hS : Asc82SchurU43) {G : Type} [Group G] [Finite G] {L : Subgroup G} {z : G}
    {K₁ K₂ : Subgroup G} (hz2 : orderOf z = 2) (hL : IsOm6Z2 L) (hodd : oddCoreIn L = ⊥)
    (hK₁ : Sl23PocketIn L z K₁) (hprod : K₁ ⊔ K₂ = twoRes (L ⊓ centralizer ({z} : Set G)))
    {n : ℕ} {E : Subgroup G}
    (hE : E ≤ normalizer (L : Set G) ⊓ normalizer ((K₁ ⊔ K₂ : Subgroup G) : Set G))
    (hab : IsElemAbelianModSub (twoCoreIn (K₁ ⊔ K₂) ⊔
      (normalizer (L : Set G) ⊓ centralizer ((K₁ ⊔ K₂ : Subgroup G) : Set G))) E)
    (hn : (twoCoreIn (K₁ ⊔ K₂) ⊔
      (normalizer (L : Set G) ⊓ centralizer ((K₁ ⊔ K₂ : Subgroup G) : Set G))).relIndex E =
        2 ^ n) : n ≤ 2 := by
  obtain ⟨Ψ, hΨ, hrange0⟩ := sec5nr_exists_psi hS hL hodd hz2 hK₁
  have hrange : Ψ.range = K₁ ⊔ K₂ := hrange0.trans hprod.symm
  have hKL : K₁ ⊔ K₂ ≤ L := by
    rw [hprod]
    exact sec5cd_twoRes_le inf_le_left
  rw [← hrange] at hE hab hn hKL
  have hS' : NrSetting Ψ E := hΨ.setting (hE.trans inf_le_right)
  rw [hΨ.twoCoreIn_range] at hab hn
  have hgen : Ψ.range ≤ Subgroup.closure {g : G | g ∈ Ψ.range ∧ Odd (orderOf g)} := by
    intro x hx
    rw [hrange0] at hx
    refine Subgroup.closure_mono ?_ hx
    intro g hg
    exact ⟨by rw [hrange0]; exact Subgroup.subset_closure hg, hg.2⟩
  have hA_le : nrQ Ψ ⊔ (normalizer (L : Set G) ⊓ centralizer (Ψ.range : Set G)) ≤ nrQC Ψ := by
    refine sup_le nrQ_le_nrQC fun g hg => mem_nrQC_of_comm fun x hx => ?_
    exact Subgroup.mem_centralizer_iff.mp hg.2 x (nrQ_le_range hx)
  have hAE : ∀ e ∈ E, e ∈ nrQC Ψ →
      e ∈ nrQ Ψ ⊔ (normalizer (L : Set G) ⊓ centralizer (Ψ.range : Set G)) := by
    intro e he h
    obtain ⟨a, ha, c, hc, rfl⟩ := h
    have haK : a ∈ Ψ.range := nrQ_le_range ha
    have hcN : c ∈ normalizer (Ψ.range : Set G) := by
      have h1 : a⁻¹ * (a * c) ∈ normalizer (Ψ.range : Set G) :=
        mul_mem (Subgroup.le_normalizer (inv_mem haK)) (hE he).2
      simpa using h1
    have hcL : c ∈ normalizer (L : Set G) := by
      have h1 : a⁻¹ * (a * c) ∈ normalizer (L : Set G) :=
        mul_mem (Subgroup.le_normalizer (inv_mem (hKL haK))) (hE he).1
      simpa using h1
    have hcC : c ∈ centralizer (Ψ.range : Set G) :=
      Subgroup.mem_centralizer_iff.mpr (hΨ.comm_range hcN hc hgen)
    exact mul_mem (Subgroup.mem_sup_left ha)
      (Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨hcL, hcC⟩))
  have hab' : ∀ a ∈ E, ∀ b ∈ E, a * b * a⁻¹ * b⁻¹ ∈ nrQC Ψ ∧ a * a ∈ nrQC Ψ :=
    fun a ha b hb => ⟨hA_le (hab a ha b hb).1, hA_le (hab a ha b hb).2⟩
  have hsub : (nrQC Ψ).subgroupOf E =
      (nrQ Ψ ⊔ (normalizer (L : Set G) ⊓ centralizer (Ψ.range : Set G))).subgroupOf E := by
    ext e
    exact ⟨fun h => hAE e e.2 h, fun h => hA_le h⟩
  have hn' : (nrQC Ψ).relIndex E = 2 ^ n := by
    rw [← hn, Subgroup.relIndex, Subgroup.relIndex, hsub]
  exact sec5nr_ex hS' hab' hn'

theorem asc82FactOm6NRank_of (hS : Asc82SchurU43) : Asc82FactOm6NRank := by
  intro G _ _ L z K₁ K₂ hL hodd hz2 hK₁ _ _ _ hprod n E hE hab hn
  exact sec5nr_main hS hz2 hL hodd hK₁ hprod hE hab hn

end CFSG.OddStandard.SmallF3.Omega
