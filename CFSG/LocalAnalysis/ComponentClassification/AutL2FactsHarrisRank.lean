module

public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsHarrisShapeStd

public noncomputable section

namespace CFSG.ComponentClassification.AutL2Facts

open CFSG GorensteinWalter Subgroup

variable {F : Type} [Field F] [Finite F]

theorem exists_closure_map {G G' : Type*} [Group G] [Group G'] (Φ : G ≃* G')
    {Q : Subgroup G'}
    (h : ∃ s : Finset G, s.card ≤ 3 ∧ closure (s : Set G) = Q.map Φ.symm.toMonoidHom) :
    ∃ s' : Finset G', s'.card ≤ 3 ∧ closure (s' : Set G') = Q := by
  classical
  obtain ⟨s, hs, hcl⟩ := h
  refine ⟨s.image Φ, (Finset.card_image_le).trans hs, ?_⟩
  rw [Finset.coe_image]
  have := MonoidHom.map_closure Φ.toMonoidHom (s : Set G)
  rw [hcl, map_map_symm_mulEquiv] at this
  exact this.symm

theorem closure_eq_of_le_sylS0 {Q : Subgroup (PGammaL2 F)} (hQ : Q ≤ sylS0 F) :
    ∃ s : Finset (PGammaL2 F), s.card ≤ 3 ∧ closure (s : Set (PGammaL2 F)) = Q := by
  classical
  have := isCyclic_ringAut F
  obtain ⟨σ₀, hσ₀⟩ :=
    (Subgroup.isCyclic_iff_exists_zpowers_eq_top (Q.map (fieldProj F))).mp inferInstance
  obtain ⟨g, hgQ, hgσ⟩ : σ₀ ∈ Q.map (fieldProj F) := hσ₀ ▸ mem_zpowers σ₀
  set τh : Fˣ →* PGammaL2 F := (SemidirectProduct.inl : PGL2 F →* PGammaL2 F).comp (tor F)
  have hτh : ∀ a, τh a = nm F a false 1 := fun a => inl_tor a
  obtain ⟨b₀, hb₀⟩ :=
    (Subgroup.isCyclic_iff_exists_zpowers_eq_top (Q.comap τh)).mp inferInstance
  have hh₁ : nm F b₀ false 1 ∈ Q := by
    rw [← hτh]
    exact (show b₀ ∈ Q.comap τh from hb₀ ▸ mem_zpowers b₀)
  have hrot : ∀ a, nm F a false 1 ∈ Q → nm F a false 1 ∈ zpowers (nm F b₀ false 1) := by
    intro a ha
    have : a ∈ zpowers b₀ := by rw [hb₀]; exact (show τh a ∈ Q by rw [hτh]; exact ha)
    obtain ⟨k, rfl⟩ := this
    exact ⟨k, (nm_false_zpow' b₀ k).symm⟩
  let h₂ : PGammaL2 F :=
    if h : ∃ a, nm F a true 1 ∈ Q then nm F h.choose true 1 else 1
  have hh₂ : h₂ ∈ Q := by
    simp only [h₂]
    split_ifs with h
    · exact h.choose_spec
    · exact one_mem _
  refine ⟨{nm F b₀ false 1, h₂, g}, ?_, ?_⟩
  · exact (Finset.card_insert_le _ _).trans (Nat.succ_le_succ ((Finset.card_insert_le _ _).trans
      (by simp)))
  · apply le_antisymm
    · rw [closure_le]
      intro x hx
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact hh₁
      · exact hh₂
      · exact hgQ
    · intro x hx
      have hs1 : nm F b₀ false 1 ∈ closure (({nm F b₀ false 1, h₂, g} : Finset _) :
          Set (PGammaL2 F)) := subset_closure (by simp)
      have hs2 : h₂ ∈ closure (({nm F b₀ false 1, h₂, g} : Finset _) : Set (PGammaL2 F)) :=
        subset_closure (by simp)
      have hs3 : g ∈ closure (({nm F b₀ false 1, h₂, g} : Finset _) : Set (PGammaL2 F)) :=
        subset_closure (by simp)
      have hxr : fieldProj F x ∈ zpowers σ₀ := by rw [hσ₀]; exact ⟨x, hx, rfl⟩
      obtain ⟨j, hj⟩ := hxr
      have hyQ : x * g ^ (-j) ∈ Q := mul_mem hx (zpow_mem hgQ _)
      have hyr : (x * g ^ (-j)).right = 1 := by
        have h1 : fieldProj F (x * g ^ (-j)) = 1 := by
          rw [map_mul, map_zpow, hgσ, ← hj, zpow_neg, mul_inv_cancel]
        exact h1
      obtain ⟨a, -, ε, τ, -, hy⟩ := hQ hyQ
      have hτ : τ = 1 := by rw [← nm_right a ε τ, ← hy, hyr]
      subst hτ
      have hx' : x = x * g ^ (-j) * g ^ j := by group
      rw [hx']
      refine mul_mem ?_ (zpow_mem hs3 j)
      rw [hy]
      cases ε
      · exact (zpowers_le.mpr hs1) (hrot a (hy ▸ hyQ))
      · have hex : ∃ a, nm F a true 1 ∈ Q := ⟨a, hy ▸ hyQ⟩
        have hh₂' : h₂ = nm F hex.choose true 1 := by
          simp only [h₂]
          split_ifs
          rfl
        have hprod : nm F a true 1 * h₂ ∈ Q := mul_mem (hy ▸ hyQ) hh₂
        rw [hh₂', nm_mul] at hprod
        simp only [fu_one, twist_true, Bool.xor_self] at hprod
        have hr := hrot _ hprod
        have : nm F a true 1 = nm F (a * hex.choose⁻¹) false 1 * h₂ := by
          rw [hh₂', nm_mul]
          simp [fu_one]
        rw [this]
        exact mul_mem ((zpowers_le.mpr hs1) hr) hs2

theorem HarrisHyp.rank_le_three (hH : HarrisHyp F) {K : Subgroup (PGammaL2 F)}
    (hK : pGammaL2PSLRange F ≤ K) (hk : ∃ k ∈ K, IsFieldInvModel k)
    {T : Subgroup (PGammaL2 F)} (hT : IsSylowIn T K) {Q : Subgroup (PGammaL2 F)} (hQ : Q ≤ T) :
    ∃ s : Finset (PGammaL2 F), s.card ≤ 3 ∧ closure (s : Set (PGammaL2 F)) = Q := by
  obtain ⟨g, -, rfl, -⟩ := hH.exists_sylowShape hK hk hT
  apply exists_closure_map (MulAut.conj g)
  apply closure_eq_of_le_sylS0
  calc Q.map (MulAut.conj g).symm.toMonoidHom ≤
      ((stdTS F K).map (MulAut.conj g).toMonoidHom).map (MulAut.conj g).symm.toMonoidHom :=
        Subgroup.map_mono hQ
    _ = stdTS F K := map_symm_map_mulEquiv _ _
    _ ≤ sylS0 F := inf_le_left

end CFSG.ComponentClassification.AutL2Facts
