module

public import CFSG.LieType.SeitzGeneration.ExcHighThree.KillsRootCombF4
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.C14IdxA2SumFree
public import CFSG.HardMathSupport.C14IdxFixedBruhat
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyCover
public import CFSG.LieType.AlgebraicGroups.KernelRootBruhat
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartOne.KLR.SL2Gen
public import CFSG.RankThree.PartOne.RF4.Basic
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.HardMathSupport.C14Idx

open CFSG.LieType.Steinberg.Adjoint
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.RF4 CFSG.RankThree.PartOne.KLR
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.SeitzReduction
  CFSG.LieType.SeitzGeneration.ExcHighThree

theorem a2PairRoots_subset_kernelRoots {τ : Tag} {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {α β : Fin τ.rank → ℤ}
    (hα : α ∈ kernelRoots χ) (hβ : β ∈ kernelRoots χ) (hsum : α + β ∈ kernelRoots χ) :
    a2PairRoots α β ⊆ kernelRoots χ :=
  fun _ hγ => mem_kernelRoots_of_mem_a2PairRoots hα hβ hsum hγ

theorem map_a2PairRoots {τ : Tag}
    {θ : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ} {α β : Fin τ.rank → ℤ}
    (hαroot : IsRoot τ α) (hβroot : IsRoot τ β) (hsum : IsRoot τ (α + β))
    (hadd : θ (α + β) = θ α + θ β)
    (hneg : ∀ x, IsRoot τ x → θ (-x) = -θ x) {δ : Fin τ.rank → ℤ}
    (hδ : δ ∈ a2PairRoots α β) : θ δ ∈ a2PairRoots (θ α) (θ β) := by
  simp only [a2PairRoots, Set.mem_insert_iff, Set.mem_singleton_iff] at hδ ⊢
  rcases hδ with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl hadd))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (hneg α hαroot))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hneg β hβroot)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by
      rw [hneg (α + β) hsum, hadd, neg_add])))))

theorem iform_eq_zero_of_mem_a2PairRoots
    {τ : Tag} {α β γ δ : Fin τ.rank → ℤ}
    (horth : ∀ x ∈ ({α, β} : Set (Fin τ.rank → ℤ)),
      ∀ y ∈ ({γ, δ} : Set (Fin τ.rank → ℤ)), iform x y = 0)
    {x y : Fin τ.rank → ℤ} (hx : x ∈ a2PairRoots α β) (hy : y ∈ a2PairRoots γ δ) :
    iform x y = 0 := by
  have hαγ : iform α γ = 0 := horth α (by simp) γ (by simp)
  have hαδ : iform α δ = 0 := horth α (by simp) δ (by simp)
  have hβγ : iform β γ = 0 := horth β (by simp) γ (by simp)
  have hβδ : iform β δ = 0 := horth β (by simp) δ (by simp)
  simp only [a2PairRoots, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;>
    (try simp only [iform_add_left, iform_add_right, iform_neg_left, iform_neg_right]) <;>
    simp [hαγ, hαδ, hβγ, hβδ]

theorem dualRoot_add_of_quadForm_eq
    {α β : Fin ReeTag.F4.tag.rank → ℤ}
    (hα : IsRoot ReeTag.F4.tag α) (hβ : IsRoot ReeTag.F4.tag β)
    (hsum : IsRoot ReeTag.F4.tag (α + β))
    (hqαβ : ReeTag.F4.quadForm α = ReeTag.F4.quadForm β)
    (hqsum : ReeTag.F4.quadForm (α + β) = ReeTag.F4.quadForm α) :
    ReeTag.F4.dualRoot (α + β) = ReeTag.F4.dualRoot α + ReeTag.F4.dualRoot β := by
  funext j
  have hd1 : (ReeTag.F4.dualRoot (α + β) j : ℚ) = (ReeTag.F4.duality (α + β)) j := by
    rw [ReeTag.duality_eq_dualRoot hsum]
  have hd2 : (ReeTag.F4.dualRoot α j : ℚ) = (ReeTag.F4.duality α) j := by
    rw [ReeTag.duality_eq_dualRoot hα]
  have hd3 : (ReeTag.F4.dualRoot β j : ℚ) = (ReeTag.F4.duality β) j := by
    rw [ReeTag.duality_eq_dualRoot hβ]
  have h1 : (ReeTag.F4.dualRoot (α + β) j : ℚ) =
      ((ReeTag.F4.dualRoot α j : ℚ) + (ReeTag.F4.dualRoot β j : ℚ)) := by
    rw [hd1, hd2, hd3]
    have hfun : (fun i => ((α i + β i : ℤ) : ℚ)) = fun i => (α i : ℚ) + (β i : ℚ) := by
      funext i; simp
    have hS : ReeTag.F4.dualMap (fun i => (α i : ℚ) + (β i : ℚ)) =
        ReeTag.F4.dualMap (fun i => (α i : ℚ)) +
          ReeTag.F4.dualMap (fun i => (β i : ℚ)) := by
      rw [← map_add]; rfl
    simp only [ReeTag.duality, ReeTag.lengthParam, Pi.add_apply, hqαβ, hqsum,
      Pi.smul_apply, smul_eq_mul]
    rw [hfun, hS]
    simp only [Pi.add_apply]
    field_simp
  exact_mod_cast h1

theorem f4_adj_value_kernelRoots
    {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin ReeTag.F4.tag.rank → ℤ) →* M}
    {α β : Fin ReeTag.F4.tag.rank → ℤ}
    (hα : α ∈ simpleRoots (kernelRoots χ)) (hβ : β ∈ simpleRoots (kernelRoots χ))
    (hne : α ≠ β) (hnz : iform α β ≠ 0) :
    (iform α α = 2 ∧ iform β β = 2 ∧ iform α β = -1) ∨
      ((iform α α = 4 ∨ iform β β = 4) ∧ iform α β = -2) := by
  have hαu : α ∈ unionSimpleRoots χ Set.univ := by
    rw [← mem_simpleRoots_unionRoots_iff, unionRoots_univ_eq_kernelRoots]; exact hα
  have hβu : β ∈ unionSimpleRoots χ Set.univ := by
    rw [← mem_simpleRoots_unionRoots_iff, unionRoots_univ_eq_kernelRoots]; exact hβ
  obtain ⟨i, -, hαi⟩ := hαu
  obtain ⟨j, -, hβj⟩ := hβu
  have hij : i = j := by
    by_contra h
    exact hnz (iform_eq_zero_of_mem_componentRoots h (simpleRoots_subset hαi)
      (simpleRoots_subset hβj))
  rw [← hij] at hβj
  exact f4_adj_value (isRootComponent_componentRoots i) hαi hβj hne hnz

theorem a2_quadForm_add_eq
    {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin ReeTag.F4.tag.rank → ℤ) →* M}
    {α β : Fin ReeTag.F4.tag.rank → ℤ}
    (hα : α ∈ simpleRoots (kernelRoots χ)) (hβ : β ∈ simpleRoots (kernelRoots χ))
    (hne : α ≠ β) (hsum : IsRoot ReeTag.F4.tag (α + β))
    (hq : iform α α = iform β β) : iform (α + β) (α + β) = iform α α := by
  classical
  have hαu : α ∈ unionSimpleRoots χ Set.univ := by
    rw [← mem_simpleRoots_unionRoots_iff, unionRoots_univ_eq_kernelRoots]; exact hα
  have hβu : β ∈ unionSimpleRoots χ Set.univ := by
    rw [← mem_simpleRoots_unionRoots_iff, unionRoots_univ_eq_kernelRoots]; exact hβ
  obtain ⟨i, -, hαi⟩ := hαu
  obtain ⟨j, -, hβj⟩ := hβu
  have hαk : α ∈ kernelRoots χ := simpleRoots_subset hα
  have hβk : β ∈ kernelRoots χ := simpleRoots_subset hβ
  have hsumk : α + β ∈ kernelRoots χ := ⟨hsum, by
    rw [ofAdd_add, map_mul, hαk.2, hβk.2, one_mul]⟩
  have hmkα : (⟦⟨α, hαk⟩⟧ : KernelComponent χ) = i := by
    obtain ⟨h, hh⟩ := simpleRoots_subset hαi
    simpa using hh
  have hαj' : α ∈ componentRoots χ i := simpleRoots_subset hαi
  have hnz : iform α β ≠ 0 := by
    intro h0
    have hif : iform α (α + β) ≠ 0 := by
      rw [iform_add_right, h0, add_zero]
      exact (iform_self_pos_of_isRoot (simpleRoots_isRoot hα)).ne'
    have hsumcomp : α + β ∈ componentRoots χ i := by
      refine ⟨hsumk, ?_⟩
      rw [← mk_eq_of_iform_ne_zero (α := ⟨α, hαk⟩) (β := ⟨α + β, hsumk⟩) hif]
      exact hmkα
    have hβcomp : β ∈ componentRoots χ i := by
      have hneg : -α ∈ componentRoots χ i :=
        (isRootComponent_componentRoots i).neg_mem α hαj'
      have hroot : IsRoot ReeTag.F4.tag ((α + β) + (-α)) := by
        simpa using simpleRoots_isRoot hβ
      have h := (isRootComponent_componentRoots i).add_mem (α + β) hsumcomp (-α) hneg hroot
      simpa using h
    have hcα : corootPair α (α + β) = 2 := by
      rw [corootPair, iform_add_right, h0, add_zero]
      exact Int.mul_ediv_cancel _ (iform_self_pos_of_isRoot (simpleRoots_isRoot hα)).ne'
    have hsub1 : β - α ∈ componentRoots χ i := by
      have h := (isRootComponent_componentRoots i).reflection_mem (α + β) hsumcomp α hαj'
      rw [rootReflection_smul (simpleRoots_isRoot hα), hcα, two_zsmul] at h
      rwa [show (α + β) - (α + α) = β - α by abel] at h
    have hsub1k : β - α ∈ kernelRoots χ := by
      have h := componentRoots_subset_unionRoots (J := Set.univ) (Set.mem_univ i) hsub1
      simpa only [unionRoots_univ_eq_kernelRoots] using h
    have h1 : 0 < height (β - α) ∨ height (β - α) < 0 :=
      IsRoot.height_pos_or_neg hsub1k.1
    have hαs : α ∈ posRoots (kernelRoots χ) := ⟨hαk, simpleRoots_height_pos hα⟩
    have hβs : β ∈ posRoots (kernelRoots χ) := ⟨hβk, simpleRoots_height_pos hβ⟩
    have hsimpleα := (mem_simpleRoots.1 hα).2.2
    have hsimpleβ := (mem_simpleRoots.1 hβ).2.2
    rcases h1 with hpos | hneg
    · have hsubpos : β - α ∈ posRoots (kernelRoots χ) := ⟨hsub1k, hpos⟩
      exact hsimpleβ (β - α) hsubpos α hαs (by abel)
    · have hβcomp' : α - β ∈ componentRoots χ i := by
        have h := (isRootComponent_componentRoots i).neg_mem (β - α) hsub1
        simpa [neg_sub] using h
      have hsub2k : α - β ∈ kernelRoots χ := by
        have h := componentRoots_subset_unionRoots (J := Set.univ) (Set.mem_univ i) hβcomp'
        simpa only [unionRoots_univ_eq_kernelRoots] using h
      have hsubpos : α - β ∈ posRoots (kernelRoots χ) := ⟨hsub2k, by
        have hh : height (α - β) = -height (β - α) := by rw [height_sub, height_sub]; ring
        linarith⟩
      exact hsimpleα (α - β) hsubpos β hβs (by abel)
  have hij : i = j := by
    by_contra h
    exact hnz (iform_eq_zero_of_mem_componentRoots h hαj' (simpleRoots_subset hβj))
  rw [← hij] at hβj
  have h := f4_adj_value (isRootComponent_componentRoots i) hαi hβj hne hnz
  rw [iform_add_left, iform_add_right, iform_add_right, iform_comm β α]
  change iform (τ := Tag.F4) α α + iform (τ := Tag.F4) α β +
      (iform (τ := Tag.F4) α β + iform (τ := Tag.F4) β β) = iform (τ := Tag.F4) α α
  have hq' : iform (τ := Tag.F4) α α = iform (τ := Tag.F4) β β := hq
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h3⟩
  · have h1' : iform (τ := Tag.F4) α α = 2 := h1
    have h2' : iform (τ := Tag.F4) β β = 2 := h2
    have h3' : iform (τ := Tag.F4) α β = -1 := h3
    nlinarith
  · rcases h1 with h1 | h1
    · have h1' : iform (τ := Tag.F4) α α = 4 := h1
      have h3' : iform (τ := Tag.F4) α β = -2 := h3
      nlinarith
    · have h1' : iform (τ := Tag.F4) β β = 4 := h1
      have h3' : iform (τ := Tag.F4) α β = -2 := h3
      nlinarith

private theorem iform_self_mem_a2PairRoots
    {α β x : Fin ReeTag.F4.tag.rank → ℤ}
    (hq : iform α α = iform β β) (hsum : iform (α + β) (α + β) = iform α α)
    (hx : x ∈ a2PairRoots α β) : iform x x = iform α α := by
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · rfl
  · exact hq.symm
  · exact hsum
  · rw [iform_neg_left, iform_neg_right]; simp
  · rw [iform_neg_left, iform_neg_right]; simp [hq]
  · rw [iform_neg_left, iform_neg_right]; simp [hsum]

private theorem a2_no_root_sum
    {γ δ : Fin ReeTag.F4.tag.rank → ℤ}
    (h0 : iform γ δ = 0)
    (hqγ : iform γ γ = 2 ∨ iform γ γ = 4)
    (hqδ : iform δ δ = 2 ∨ iform δ δ = 4)
    (hq6 : iform γ γ + iform δ δ = 6) :
    ∀ a b : ℕ, 0 < a → 0 < b → ¬IsRoot ReeTag.F4.tag (a • γ + b • δ) := by
  intro a b ha hb hroot
  have hval := iform_self_cases (τ := ReeTag.F4.tag) noG2_F4 hroot
  rw [← Nat.cast_smul_eq_nsmul ℤ a γ, ← Nat.cast_smul_eq_nsmul ℤ b δ] at hval
  rw [iform_add_left, iform_add_right, iform_add_right, iform_smul_left, iform_smul_left,
    iform_smul_right, iform_smul_right, h0] at hval
  simp only [iform_smul_left, iform_smul_right] at hval
  rw [iform_comm δ γ, h0] at hval
  ring_nf at hval
  have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
  rcases hqγ with h1 | h1 <;> rcases hqδ with h2 | h2 <;>
    rcases hval with hv | hv <;> nlinarith [hv, hq6, h1, h2, ha', hb']

theorem a2Cycle_commute
    {L : Type} [Field L] {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin ReeTag.F4.tag.rank → ℤ) →* M} {w : WeylGroup ReeTag.F4.tag}
    {θ : (Fin ReeTag.F4.tag.rank → ℤ) → Fin ReeTag.F4.tag.rank → ℤ}
    (hθ : ∀ β, θ β = w • ReeTag.F4.dualRoot β)
    (hΨ : Set.BijOn (fun α => w • ReeTag.F4.dualRoot α) (kernelRoots χ) (kernelRoots χ))
    {α β : Fin ReeTag.F4.tag.rank → ℤ}
    (hα : α ∈ simpleRoots (kernelRoots χ)) (hβ : β ∈ simpleRoots (kernelRoots χ))
    (hsum : IsRoot ReeTag.F4.tag (α + β))
    (hadd : θ (α + β) = θ α + θ β)
    (hneg : ∀ x, IsRoot ReeTag.F4.tag x → θ (-x) = -θ x)
    (hq : iform α α = iform β β)
    (hqsum : iform (α + β) (α + β) = iform α α)
    (hqθ : iform (θ α) (θ α) = iform (θ β) (θ β))
    (hqθsum : iform (θ α + θ β) (θ α + θ β) = iform (θ α) (θ α))
    (hqmul : iform α α * iform (θ α) (θ α) = 8)
    (horth : ∀ x ∈ ({α, β} : Set (Fin ReeTag.F4.tag.rank → ℤ)),
      ∀ y ∈ ({θ α, θ β} : Set (Fin ReeTag.F4.tag.rank → ℤ)), iform x y = 0) :
    ∀ γ ∈ a2PairRoots α β, ∀ δ ∈ a2PairRoots α β, ∀ s t : L,
      Commute (pinnedX ReeTag.F4.tag L γ s) (pinnedX ReeTag.F4.tag L (θ δ) t) := by
  intro γ hγ δ hδ s t
  have hαroot : IsRoot ReeTag.F4.tag α := simpleRoots_isRoot hα
  have hβroot : IsRoot ReeTag.F4.tag β := simpleRoots_isRoot hβ
  have hαker : α ∈ kernelRoots χ := simpleRoots_subset hα
  have hβker : β ∈ kernelRoots χ := simpleRoots_subset hβ
  have hsumker : α + β ∈ kernelRoots χ := ⟨hsum, by
    rw [ofAdd_add, map_mul, hαker.2, hβker.2, one_mul]⟩
  have hδ' : θ δ ∈ a2PairRoots (θ α) (θ β) :=
    map_a2PairRoots hαroot hβroot hsum hadd hneg hδ
  have hγroot : IsRoot ReeTag.F4.tag γ :=
    (a2PairRoots_subset_kernelRoots hαker hβker hsumker hγ).1
  have hθδroot : IsRoot ReeTag.F4.tag (θ δ) := by
    have h : θ δ ∈ kernelRoots χ := by
      simpa [hθ] using hΨ.mapsTo (a2PairRoots_subset_kernelRoots hαker hβker hsumker hδ)
    exact h.1
  have hqγ : iform γ γ = iform α α := iform_self_mem_a2PairRoots hq hqsum hγ
  have hqθδ : iform (θ δ) (θ δ) = iform (θ α) (θ α) :=
    iform_self_mem_a2PairRoots hqθ hqθsum hδ'
  have hqα : iform α α = 2 ∨ iform α α = 4 := f4_iform_self hαroot
  have hqθα : iform (θ α) (θ α) = 2 ∨ iform (θ α) (θ α) = 4 := by
    have h : θ α ∈ kernelRoots χ := by simpa [hθ] using hΨ.mapsTo hαker
    exact f4_iform_self h.1
  have hq6 : iform γ γ + iform (θ δ) (θ δ) = 6 := by
    rw [hqγ, hqθδ]
    rcases hqα with h1 | h1 <;> rcases hqθα with h2 | h2 <;> rw [h1, h2] at hqmul ⊢ <;> omega
  have hne : γ ≠ θ δ := by
    intro h
    rw [h] at hqγ
    have hqq : iform α α = iform (θ α) (θ α) := by rw [← hqγ, hqθδ]
    rcases hqα with h1 | h1 <;> rcases hqθα with h2 | h2 <;> nlinarith
  have hne' : γ ≠ -θ δ := by
    intro h
    have hqq : iform γ γ = iform (θ δ) (θ δ) := by
      rw [h, iform_neg_left, iform_neg_right]
      simp
    rw [hqγ, hqθδ] at hqq
    rcases hqα with h1 | h1 <;> rcases hqθα with h2 | h2 <;> nlinarith
  have h0 : iform γ (θ δ) = 0 := iform_eq_zero_of_mem_a2PairRoots horth hγ hδ'
  exact commute_pinnedX_of_forall_not_isRoot L hγroot hθδroot hne hne'
    (a2_no_root_sum h0 (by rw [hqγ]; exact hqα) (by rw [hqθδ]; exact hqθα)
      hq6) s t

end CFSG.HardMathSupport.C14Idx
