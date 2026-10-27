module

public import CFSG.ClassicalInvolution.Asc77.AscT7V4

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson

namespace T7V

set_option linter.unusedSectionVars false

section Family

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}

open Classical in
theorem exists_sylow_family (hΩ : HypOmegaMod p f Ω) (hz : IsUniqueInvolution K z)
    (s : Finset (Subgroup G)) (hs : ∀ M ∈ s, M ∈ twinSet Ω K) :
    ∃ R : Subgroup G → Subgroup G, (∀ M ∈ s, IsSylow2In (R M) M) ∧
      (∀ M ∈ s, ∀ M' ∈ s, M ≠ M' → Commutes (R M) (R M')) ∧
      IsPGroup 2 ↥(⨆ M ∈ s, R M) := by
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨fun _ => ⊥, by simp, by simp, ?_⟩
    exact (isPGroup_two_bot (G := G)).to_le
      (iSup₂_le fun M hM => absurd hM (Finset.notMem_empty M))
  | insert M₀ s hM₀ ih =>
    obtain ⟨R, hRs, hRc, hRP⟩ := ih (fun M hM => hs M (Finset.mem_insert_of_mem hM))
    have hM₀K : M₀ ∈ twinSet Ω K := hs M₀ (Finset.mem_insert_self _ _)
    have hz₀ : IsUniqueInvolution M₀ z := isUniqueInvolution_of_mem_twinSet hz hM₀K
    have hPN : (⨆ M ∈ s, R M) ≤ Subgroup.normalizer (M₀ : Set G) := by
      refine iSup₂_le fun M hM => ?_
      have hMK : M ∈ twinSet Ω K := hs M (Finset.mem_insert_of_mem hM)
      have hne : M ≠ M₀ := fun e => hM₀ (by rw [← e]; exact hM)
      exact (hRs M hM).1.trans (hΩ.le_normalizer_of_twin hMK.1 hM₀K.1 hne
        (isUniqueInvolution_of_mem_twinSet hz hMK) hz₀)
    obtain ⟨R₀, hR₀, hP₀⟩ := exists_isPGroup_sup_sylow hRP hPN
    have hupd : ∀ M ∈ s, Function.update R M₀ R₀ M = R M := fun M hM =>
      Function.update_of_ne (fun e => hM₀ (by rw [← e]; exact hM)) _ _
    have hle : ∀ M ∈ s, R M ≤ (⨆ M ∈ s, R M) ⊔ R₀ := fun M hM =>
      le_sup_of_le_left (le_iSup₂ (f := fun M (_ : M ∈ s) => R M) M hM)
    refine ⟨Function.update R M₀ R₀, ?_, ?_, ?_⟩
    · intro M hM
      rcases Finset.mem_insert.mp hM with rfl | hMs
      · simpa using hR₀
      · rw [hupd M hMs]
        exact hRs M hMs
    ·
      have hcomm₀ : ∀ M ∈ s, Commutes (R M) R₀ := by
        intro M hM
        have hMK : M ∈ twinSet Ω K := hs M (Finset.mem_insert_of_mem hM)
        have hne : M ≠ M₀ := fun e => hM₀ (by rw [← e]; exact hM)
        exact hΩ.commutes_of_twin_of_isPGroup hMK.1 hM₀K.1 hne
          (isUniqueInvolution_of_mem_twinSet hz hMK) hz₀ (hRs M hM).1 hR₀.1
          (hP₀.to_le (sup_le (hle M hM) le_sup_right))
      intro M hM M' hM' hne
      rcases Finset.mem_insert.mp hM with rfl | hMs <;>
        rcases Finset.mem_insert.mp hM' with rfl | hMs'
      · exact absurd rfl hne
      · rw [Function.update_self, hupd M' hMs']
        exact (hcomm₀ M' hMs').symm
      · rw [Function.update_self, hupd M hMs]
        exact hcomm₀ M hMs
      · rw [hupd M hMs, hupd M' hMs']
        exact hRc M hMs M' hMs' hne
    · refine hP₀.to_le (iSup₂_le fun M hM => ?_)
      rcases Finset.mem_insert.mp hM with rfl | hMs
      · rw [Function.update_self]
        exact le_sup_right
      · rw [hupd M hMs]
        exact hle M hMs

end Family

section Wyl

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' K₃ : Subgroup G} {z u₁ u₂ u₃ : G}

@[expose] def Hyp22SettingWyl (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' K₃ : Subgroup G) (z u₁ u₂ u₃ : G), Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃ →
      ∀ W ∈ WSet Ω, MuIsoWylD4 Ω W

theorem exists_reps_of_family (h : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃)
    (S : Finset (Subgroup G)) (hKS : K ∈ S) (hS : ∀ M ∈ S, M ∈ twinSet Ω K) :
    ∃ W ∈ WSet Ω, ∃ ρ : Subgroup G → Rep Ω W, ∀ M ∈ S, (ρ M).K = M := by
  have hp : p ≠ 2 := h.stand.odd
  have hq : 5 ≤ p ^ f := h.stand.five
  have hΩ : HypOmegaMod p f Ω := h.stand.hyp
  obtain ⟨R, hRs, -, hRP⟩ := exists_sylow_family hΩ h.hz S hS
  obtain ⟨W, hW, hWD⟩ := exists_W_of_isPGroup hp hq hΩ hRP
  have hex : ∀ M ∈ S, ∃ ρ : Rep Ω W, ρ.K = M := fun M hM => by
    obtain ⟨ρ, hρK, -⟩ := T7D.exists_rep hp hq hΩ hW (hS M hM).1 (hRs M hM)
      (hWD (R M) (mem_RSet_of_isSylow2In (hS M hM).1 (hRs M hM))
        (le_iSup₂_of_le M hM le_rfl))
    exact ⟨ρ, hρK⟩
  have : Nonempty (Rep Ω W) := ⟨(hex K hKS).choose⟩
  choose! ρ hρ using hex
  exact ⟨W, hW, ρ, hρ⟩

theorem twins_card_le_four (h : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃)
    (hnc : ∀ W ∈ WSet Ω, (∃ ρ : Rep Ω W, ρ.K = K) → ¬ DbarConnected Ω W)
    (S : Finset (Subgroup G)) (hKS : K ∈ S) (hS : ∀ M ∈ S, M ∈ twinSet Ω K) : S.card ≤ 4 := by
  classical
  obtain ⟨W, hW, ρ, hρ⟩ := exists_reps_of_family h S hKS hS
  have hnc' : ¬ DbarConnected Ω W := hnc W hW ⟨ρ K, hρ K hKS⟩
  have c : Thompson.Ctx p f Ω W := T7D.ctx_of_stand h.stand hW
  have hP : PartIHyp p f Ω := ⟨c.hp, c.hq, c.hΩ, c.hA⟩
  let g : Subgroup G → ↥(muGroup Ω W) := fun M => T7D.imgQ (ρ M)
  have hinj : Set.InjOn g (↑S : Set (Subgroup G)) := by
    intro M hM M' hM' e
    have := c.K_eq_of_img_eq (ρ M) (ρ M') (congrArg Subtype.val e)
    rwa [hρ M hM, hρ M' hM'] at this
  have hsub : (↑(S.image g) : Set ↥(muGroup Ω W)) ⊆
      Star3T.cent (muDelta Ω W) (g K) := by
    intro y hy
    obtain ⟨M, hM, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hy)
    by_cases hMK : M = K
    · rw [hMK]
      exact Star3T.self_mem_cent (T7D.imgQ_mem _)
    · refine ⟨T7D.imgQ_mem _, (Subtype.ext (c.comm_of_omega (ρ K) (ρ M) ?_)).symm⟩
      rw [hρ K hKS, hρ M hM]
      exact adj_of_twins h (hS K hKS) (hS M hM) hMK
  have hcard : S.card ≤ (Star3T.cent (muDelta Ω W) (g K)).ncard := by
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rwa [Set.ncard_coe_finset, Finset.card_image_of_injOn hinj] at this
  rcases thompsonClique G Ω hP W hW hnc' (g K) (T7D.imgQ_mem _) with h1 | h1 | ⟨h1, -⟩ <;> omega

theorem exists_fourth_twin (h : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃)
    (hnc : ∀ W ∈ WSet Ω, (∃ ρ : Rep Ω W, ρ.K = K) → ¬ DbarConnected Ω W) :
    ∃ K₄ ∈ twinSet Ω K, K₄ ≠ K ∧ K₄ ≠ K' ∧ K₄ ≠ K₃ := by
  classical
  have hK : K ∈ twinSet Ω K := mem_twinSet_self h.stand.mem h.hz
  obtain ⟨W, hW, ρ, hρ⟩ := exists_reps_of_family h ({K, K', K₃} : Finset (Subgroup G))
    (by simp) (by
      intro M hM
      simp only [Finset.mem_insert, Finset.mem_singleton] at hM
      rcases hM with rfl | rfl | rfl
      · exact hK
      · exact h.hK'
      · exact h.hK₃)
  have hρ₁ : (ρ K).K = K := hρ K (by simp)
  have hρ₂ : (ρ K').K = K' := hρ K' (by simp)
  have hρ₃ : (ρ K₃).K = K₃ := hρ K₃ (by simp)
  have hnc' : ¬ DbarConnected Ω W := hnc W hW ⟨ρ K, hρ₁⟩
  have c : Thompson.Ctx p f Ω W := T7D.ctx_of_stand h.stand hW
  have hz' : IsUniqueInvolution K' z := h.hzK'
  have hz₃ : IsUniqueInvolution K₃ z := h.hzK₃
  obtain ⟨ρ₄, h41, h42, h43, h4a, -, -, -⟩ := c.exists_fourth hnc' (ρ K) (ρ K') (ρ K₃)
    (by rw [hρ₁, hρ₂]; exact adj_of_twins h hK h.hK' h.hne)
    (by rw [hρ₁, hρ₃]; exact adj_of_twins h hK h.hK₃ h.hK₃K)
    (by rw [hρ₂, hρ₃]; exact adj_of_twins h h.hK' h.hK₃ h.hK₃K')
    (by rw [hρ₁]; exact h.hz) (by rw [hρ₂]; exact hz') (by rw [hρ₃]; exact hz₃)
  rw [hρ₁] at h41 h4a
  rw [hρ₂] at h42
  rw [hρ₃] at h43
  have hmem : ρ₄.K ∈ twinSet Ω K := by
    rw [← h.perp]
    exact Or.inr h4a
  exact ⟨ρ₄.K, hmem, h41, h42, h43⟩

theorem hyp22FourTwins_of_wyl (hR : Hyp22SettingWyl p f) : Hyp22FourTwins p f := by
  classical
  intro G _ _ _ Ω K K' K₃ z u₁ u₂ u₃ hs
  have hnc : ∀ W ∈ WSet Ω, (∃ ρ : Rep Ω W, ρ.K = K) → ¬ DbarConnected Ω W :=
    fun W hW ⟨ρ₀, hρ₀⟩ =>
      not_dbarConnected_of_wyl hs hW ρ₀ hρ₀ (hR G Ω K K' K₃ z u₁ u₂ u₃ hs W hW)
  obtain ⟨K₄, hK₄, h41, h42, h43⟩ := exists_fourth_twin hs hnc
  refine ⟨K₄, hK₄, h41, h42, h43, fun M hM => ?_⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨hMK, hMK', hMK₃, hMK₄⟩ := hcon
  have hK : K ∈ twinSet Ω K := mem_twinSet_self hs.stand.mem hs.hz
  have hle := twins_card_le_four hs hnc ({K, K', K₃, K₄, M} : Finset (Subgroup G)) (by simp)
    (by
      intro N hN
      simp only [Finset.mem_insert, Finset.mem_singleton] at hN
      rcases hN with rfl | rfl | rfl | rfl | rfl
      · exact hK
      · exact hs.hK'
      · exact hs.hK₃
      · exact hK₄
      · exact hM)
  have hKK' : K ≠ K' := hs.hne.symm
  have hKK₃ : K ≠ K₃ := hs.hK₃K.symm
  have hKK₄ : K ≠ K₄ := h41.symm
  have hK'K₃ : K' ≠ K₃ := hs.hK₃K'.symm
  have hK'K₄ : K' ≠ K₄ := h42.symm
  have hK₃K₄ : K₃ ≠ K₄ := h43.symm
  have h5 : ({K, K', K₃, K₄, M} : Finset (Subgroup G)).card = 5 := by
    rw [Finset.card_insert_of_notMem (by simp [hKK', hKK₃, hKK₄, hMK.symm]),
      Finset.card_insert_of_notMem (by simp [hK'K₃, hK'K₄, hMK'.symm]),
      Finset.card_insert_of_notMem (by simp [hK₃K₄, hMK₃.symm]),
      Finset.card_insert_of_notMem (by simp [hMK₄.symm]), Finset.card_singleton]
  omega

end Wyl

end T7V

end CFSG.ClassicalInvolution.Asc77
