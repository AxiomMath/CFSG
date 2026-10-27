module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterDataCartan
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterLevelNuMain
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterStepMove
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitarySemilinearFour

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup

@[expose] def U3C1OuterLevelDataFpfInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ) (t : G) (T R₂ D : Subgroup G) (d : G)
    (V : Subgroup G) (k : ℕ), U3C1OuterStepHyp G L f t T R₂ D d V k → U3C1CartanFpf L T D d →
    ∃ U U₁ : Subgroup G, U3C1OuterLevelData G L f t T D V U U₁ k

@[expose] def U3C1OuterLevelFpfInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ) (t : G) (T R₂ D : Subgroup G) (d : G)
    (V : Subgroup G) (k : ℕ),
    U3Start G L f t T → (∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) →
    U3R2 G L (szT₁ L T) R₂ t f → (∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹) → (∃ r ∈ R₂, r ^ 2 ≠ 1) →
    (∃ v ∈ T, v ^ 2 = 1 ∧ v ∉ szT₁ L T ⊔ zpowers t) → U3C1CartanFpf L T D d →
    U3C1OuterConf G L f t T R₂ D V k → (¬ ∃ S : Sylow 2 G, (S : Subgroup G) = T ⊔ V) →
    (∃ y ∈ normalizer (szR (szT₁ L T) V t : Set G), ∃ r ∈ V, (∀ x ∈ V, x ^ 2 ≠ r) ∧
      y * t * y⁻¹ = r * t) →
    ∃ V' : Subgroup G, V ≤ V' ∧ U3C1OuterConf G L f t T R₂ D V' (k + 1)

@[expose] def U3C1OuterNextFpfInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ) (t : G) (T R₂ D : Subgroup G) (d : G)
    (V : Subgroup G) (k : ℕ),
    U3Start G L f t T → (∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) →
    U3R2 G L (szT₁ L T) R₂ t f → (∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹) → (∃ r ∈ R₂, r ^ 2 ≠ 1) →
    (∃ v ∈ T, v ^ 2 = 1 ∧ v ∉ szT₁ L T ⊔ zpowers t) → U3C1CartanFpf L T D d →
    U3C1OuterConf G L f t T R₂ D V k → (¬ ∃ S : Sylow 2 G, (S : Subgroup G) = T ⊔ V) →
    ∃ V' : Subgroup G, V ≤ V' ∧ U3C1OuterConf G L f t T R₂ D V' (k + 1)

theorem U3C1OuterLevelData.exists_conf_succ {G : Type} [Group G]
    [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T R₂ D : Subgroup G} {d : G} {V U U₁ : Subgroup G}
    {k : ℕ} (H : U3C1OuterStepHyp G L f t T R₂ D d V k)
    (hL : U3C1OuterLevelData G L f t T D V U U₁ k) (hMH : U3C1OuterMuHighInput)
    (hM1 : U3C1OuterMuOneInput) (hM1S : U3C1OuterMuOneSylowInput) (hS : U3C1OuterStructureInput)
    (hN : U3C1OuterNuInput) :
    ∃ V' : Subgroup G, V ≤ V' ∧ U3C1OuterConf G L f t T R₂ D V' (k + 1) := by
  obtain ⟨h, hS2, -, -, -, hv, hC, hc, -, -⟩ := id H
  have hμ : U₁ ≤ centralizer (V : Set G) := by
    rcases Nat.lt_or_ge k 2 with hk | hk
    · have hk1 : k = 1 := by have := hc.one_le; omega
      subst hk1
      by_cases hsyl : ∃ S : Sylow 2 G, (S : Subgroup G) = U ⊔ T
      · exact hM1S G L f t T R₂ D d V U U₁ H hL hsyl
      · exact hM1 G L f t T R₂ D d V U U₁ H hL hsyl
    · exact hMH G L f t T R₂ D d V U U₁ k H hL hk
  have hlam := hL.lambda h hS2 hc
  have hF := hS G L f t T R₂ D d V U U₁ k H hL hμ hlam
  obtain ⟨-, -, -, hTN₁, -, -, -⟩ := h.start_of_card_sylow hS2
  have hVV₁ := hL.V_le_V₁ hc
  have hV₁c : ∀ y ∈ szT₁ L T, ∀ u ∈ outerV₁ L T U₁, y * u = u * y := fun y hy u hu =>
    mem_centralizer_iff.mp (mem_outerV₁.mp hu).2 y hy
  have hTV₁ : T ≤ normalizer (outerV₁ L T U₁ : Set G) := fun s hs =>
    mem_normalizer_outerV₁ (hL.T_le hs) (hTN₁ hs)
  have hDV₁ : D ≤ normalizer (outerV₁ L T U₁ : Set G) := fun x hx =>
    mem_normalizer_outerV₁ (hL.D_le hx) (hC.le_normalizer hx)
  have hσ : ∀ u ∈ outerV₁ L T U₁, u * t * u⁻¹ * t⁻¹ ∈ V := fun u hu =>
    hL.comm_t_mem h hS2 hc (hL.U₁_le (mem_outerV₁.mp hu).1)
  by_cases hsyl : ∃ S : Sylow 2 G, (S : Subgroup G) = T ⊔ outerV₁ L T U₁
  · exact (h.outerStep_false_of_sylow hS2 hv hC hc.one_le hV₁c hF.comm hc.le hVV₁ hc.pow hF.card
      hF.sq_mem hF.omega hc.inv hTV₁ hDV₁ hsyl).elim
  · have hesc := h.outerStep_exists_escape hS2 hv hC hc.one_le hV₁c hF.comm hc.le hVV₁ hc.card
      hc.pow hF.card hF.sq_mem hF.omega hc.inv hσ hTV₁ hDV₁ hsyl
    have hν := hN G L f t T R₂ D d V U U₁ k H hL hμ hlam hF hesc
    exact ⟨outerV₁ L T U₁, hVV₁, hL.conf_succ h hS2 hC hc hF hν⟩

theorem u3C1OuterLevelFpfInput_of_inputs
    (hD : U3C1OuterLevelDataFpfInput) (hMH : U3C1OuterMuHighInput) (hM1 : U3C1OuterMuOneInput)
    (hM1S : U3C1OuterMuOneSylowInput) (hS : U3C1OuterStructureInput) (hN : U3C1OuterNuInput) :
    U3C1OuterLevelFpfInput := by
  intro G _ _ L f t T R₂ D d V k h hS2 hR hinv hne hv hC hc hnS hmove
  have H : U3C1OuterStepHyp G L f t T R₂ D d V k :=
    ⟨h, hS2, hR, hinv, hne, hv, hC.toU3C1Cartan, hc, hnS, hmove⟩
  obtain ⟨U, U₁, hL⟩ := hD G L f t T R₂ D d V k H hC
  exact hL.exists_conf_succ H hMH hM1 hM1S hS hN

namespace U3C1OuterConf

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}
  {T R₂ D V : Subgroup G} {k : ℕ}

theorem exists_sylow_of_nextFpf (hnext : U3C1OuterNextFpfInput) (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (hR : U3R2 G L (szT₁ L T) R₂ t f) (hinv : ∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹)
    (hne : ∃ r ∈ R₂, r ^ 2 ≠ 1) (hv : ∃ v ∈ T, v ^ 2 = 1 ∧ v ∉ szT₁ L T ⊔ zpowers t) {d : G}
    (hC : U3C1CartanFpf L T D d) (hc : U3C1OuterConf G L f t T R₂ D V k)
    (h1 : k = 1 → ¬ ∃ S : Sylow 2 G, (S : Subgroup G) = T ⊔ V) :
    ∃ (V' : Subgroup G) (k' : ℕ), 2 ≤ k' ∧ V ≤ V' ∧ U3C1OuterConf G L f t T R₂ D V' k' ∧
      ∃ S : Sylow 2 G, (S : Subgroup G) = T ⊔ V' := by
  suffices key : ∀ (m : ℕ) (V : Subgroup G) (k : ℕ), Nat.card G - Nat.card V = m →
      U3C1OuterConf G L f t T R₂ D V k →
      (k = 1 → ¬ ∃ S : Sylow 2 G, (S : Subgroup G) = T ⊔ V) →
      ∃ (V' : Subgroup G) (k' : ℕ), 2 ≤ k' ∧ V ≤ V' ∧ U3C1OuterConf G L f t T R₂ D V' k' ∧
        ∃ S : Sylow 2 G, (S : Subgroup G) = T ⊔ V' from key _ V k rfl hc h1
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro V k hm hc h1
    by_cases hS : ∃ S : Sylow 2 G, (S : Subgroup G) = T ⊔ V
    · refine ⟨V, k, ?_, le_rfl, hc, hS⟩
      have := hc.one_le
      by_contra hk
      exact h1 (by omega) hS
    · obtain ⟨V', hVV', hc'⟩ := hnext G L f t T R₂ D d V k h hS2 hR hinv hne hv hC hc hS
      have hq : 1 < 2 ^ f := Nat.one_lt_two_pow (by have := h.two_le; omega)
      have hlt : Nat.card V < Nat.card V' := by
        rw [hc.card, hc'.card]
        exact Nat.pow_lt_pow_right hq (by omega)
      have hle := Subgroup.card_le_card_group V'
      obtain ⟨V'', k'', hk'', hV'V'', hc'', hS''⟩ := ih _ (by omega) V' (k + 1) rfl hc'
        (fun hk => absurd hk (by have := hc.one_le; omega))
      exact ⟨V'', k'', hk'', hVV'.trans hV'V'', hc'', hS''⟩

end U3C1OuterConf

section Certificates

theorem u3C1OuterNextFpfInput_of_move_level (hM : U3C1OuterMoveInput)
    (hL : U3C1OuterLevelFpfInput) : U3C1OuterNextFpfInput := by
  intro G _ _ L f t T R₂ D d V k h hS2 hR hinv hne hv hC hc hnS
  refine hL G L f t T R₂ D d V k h hS2 hR hinv hne hv hC hc hnS ?_
  rcases Nat.lt_or_ge k 2 with hk | hk
  · have hk1 : k = 1 := by have := hc.one_le; omega
    subst hk1
    have hV := hc.eq_of_one hR
    subst hV
    obtain ⟨y, hyR, r, hr, hrA, hyt⟩ := h.exists_move_of_inv_of_not_isSylow hS2 hR hinv hnS
      (h.normalizer_S₁_le_normalizer_szA₁_of_card_sylow hS2 hR)
    exact ⟨y, hyR, r, hr, fun x hx hxr => hrA (hxr ▸ hR.sq_mem x hx), hyt⟩
  · exact hM G L f t T R₂ D d V k h hS2 hR hinv hne hv hC.toU3C1Cartan hc hk hnS

theorem u3C1NcycSylowStageInput_of_nextFpf (hnext : U3C1OuterNextFpfInput) :
    U3C1NcycSylowStageInput := by
  intro G _ _ L f t T R₂ h hS2 hR hinv hne hv hS₁
  obtain ⟨D, d, hC⟩ := h.exists_u3C1CartanFpf hS2
  have hc1 := h.u3C1OuterConf_one hS2 hR hinv hC.toU3C1Cartan
  obtain ⟨V, k, hk, -, hc, hsyl⟩ :=
    hc1.exists_sylow_of_nextFpf hnext h hS2 hR hinv hne hv hC (fun _ => hS₁)
  exact ⟨V, hc.R₂_le, fun y hy u hu => mem_centralizer_iff.mp (hc.le_centralizer hu) y hy,
    hc.comm, hc.le, fun u hu htu => hc.mem_szA₁_of_conj_eq hu htu, hc.T_le,
    hc.exists_pow_four_ne h hS2 hk, hc.sign h hS2 hC.toU3C1Cartan, hsyl⟩

theorem u3C1NcycSylowStageInput_of_dataFpf (hD : U3C1OuterLevelDataFpfInput)
    (hM1 : U3C1OuterMuOneInput) (hM1S : U3C1OuterMuOneSylowInput) : U3C1NcycSylowStageInput :=
  u3C1NcycSylowStageInput_of_nextFpf (u3C1OuterNextFpfInput_of_move_level u3C1OuterMoveInput_holds
    (u3C1OuterLevelFpfInput_of_inputs hD u3C1OuterMuHighInput_holds hM1 hM1S
      u3C1OuterStructureInput_holds u3C1OuterNuInput_holds))

end Certificates

end CFSG.SeitzReduction.RankOne
