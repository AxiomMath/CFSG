module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalJZeroTwoQTwo
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalJZeroTwoQTwoTriality
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalJZeroTwoQTwoCand
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveSevenPSpMain
public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineJTwo
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveSevenExc
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveSevenOmega

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

@[expose] def D4QTwoCandidateOuterInput : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    (LieModel S .PSL 2 7 2 ∨ LieModel S .PSL 3 7 1 ∨ LieModel S .PSU 3 7 1) →
    ∀ τ : MulAut S, orderOf τ = 2 → τ ∉ (MulAut.conj : S →* MulAut S).range →
    ∀ D : Subgroup (fixedSubgroup τ), CFSG.IsComponent D →
      LieModel (D ⧸ center D) .PSL 3 2 1 → center D = ⊥ →
      SeitzReduction.F4Pilot.FixedCentralizerTwoFree τ D → 168 < Nat.card (fixedSubgroup τ)

@[expose] def D4QTwoSevenFamilyInput (t : StatedLieTag) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ n f : ℕ, StatedLieAdmissible t n 7 f → LieModel S t n 7 f → GH74.Gen4 S →
    ∀ τ : MulAut S, orderOf τ = 2 →
    ∀ D : Subgroup (fixedSubgroup τ), CFSG.IsComponent D →
      LieModel (D ⧸ center D) .PSL 3 2 1 → center D = ⊥ →
      (SeitzReduction.F4Pilot.FixedCentralizerTwoFree τ D ∨
        (τ ∈ (MulAut.conj : S →* MulAut S).range ∧
          SeitzReduction.LinearPilot.FixedCentralizerTwoSmall τ D)) →
      168 < Nat.card (fixedSubgroup τ) ∧
        (τ ∈ (MulAut.conj : S →* MulAut S).range → 336 < Nat.card (fixedSubgroup τ))

theorem lt_of_two_pow_dvd_of_dvd {n k : ℕ} (hn : 0 < n) (h168 : 168 ∣ n) (h2 : 2 ^ k ∣ n) :
    (4 ≤ k → 168 < n) ∧ (5 ≤ k → 336 < n) := by
  refine ⟨fun hk => ?_, fun hk => ?_⟩
  · have h16 : 16 ∣ n := (pow_dvd_pow 2 hk).trans h2
    omega
  · have h32 : 32 ∣ n := (pow_dvd_pow 2 hk).trans h2
    omega

theorem card_dvd_card_fixedSubgroup_of_lieModel {S : Type} [Group S] [Finite S] {τ : MulAut S}
    {D : Subgroup (fixedSubgroup τ)} (hDm : LieModel (D ⧸ center D) .PSL 3 2 1)
    (hZD : center D = ⊥) : 168 ∣ Nat.card (fixedSubgroup τ) := by
  have h1 : Nat.card (D ⧸ center D) = 168 :=
    SeitzReduction.LinearPilot.card_of_lieModel_PSL_three_two hDm
  have h2 : Nat.card D = Nat.card (D ⧸ center D) * Nat.card (center D) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  rw [h1] at h2
  rw [hZD, card_bot, mul_one] at h2
  rw [← h2]
  exact card_subgroup_dvd_card D

theorem d4QTwoSevenFamilyInput_of_two_pow {t : StatedLieTag}
    (h : ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      ∀ n f : ℕ, StatedLieAdmissible t n 7 f → LieModel S t n 7 f → ∀ τ : MulAut S,
      orderOf τ = 2 → ∀ D : Subgroup (fixedSubgroup τ), CFSG.IsComponent D →
      LieModel (D ⧸ center D) .PSL 3 2 1 →
      2 ^ 4 ∣ Nat.card (fixedSubgroup τ) ∧
        (τ ∈ (MulAut.conj : S →* MulAut S).range → 2 ^ 5 ∣ Nat.card (fixedSubgroup τ))) :
    D4QTwoSevenFamilyInput t := by
  intro S _ _ hS hna n f hadm hSm _ τ hτ D hD hDm hZD _
  obtain ⟨h4, h5⟩ := h S hS hna n f hadm hSm τ hτ D hD hDm
  have h168 := card_dvd_card_fixedSubgroup_of_lieModel hDm hZD
  exact ⟨(lt_of_two_pow_dvd_of_dvd Nat.card_pos h168 h4).1 le_rfl,
    fun hi => (lt_of_two_pow_dvd_of_dvd Nat.card_pos h168 (h5 hi)).2 le_rfl⟩

theorem d4QTwoSevenFamilyInput_of_not_gen4 {t : StatedLieTag}
    (h : ∀ (S : Type) [Group S] [Finite S] (n f : ℕ), LieModel S t n 7 f → ¬ GH74.Gen4 S) :
    D4QTwoSevenFamilyInput t :=
  fun S _ _ _ _ n f _ hSm hgen => absurd hgen (h S n f hSm)

theorem d4QTwoSevenFamilyInput_of_not_admissible {t : StatedLieTag}
    (ht : ∀ n f : ℕ, ¬ StatedLieAdmissible t n 7 f) : D4QTwoSevenFamilyInput t :=
  fun _ _ _ _ _ n f hadm => absurd hadm (ht n f)

theorem exists_elemAbelian_eight_of_inner {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) {τ : MulAut S} (hτ : orderOf τ = 2)
    (hi : τ ∈ (MulAut.conj : S →* MulAut S).range) {D : Subgroup (fixedSubgroup τ)}
    (hDm : LieModel (D ⧸ center D) .PSL 3 2 1) (hZD : center D = ⊥) :
    ∃ E : Subgroup S, (∀ x ∈ E, x * x = 1) ∧ Nat.card E = 8 := by
  obtain ⟨s, rfl⟩ := hi
  have hinj := ComponentClassification.CatLeaf.mulAut_conj_injective_of_simple (S := S) hna
  have hs : orderOf s = 2 := by
    rw [← orderOf_injective _ hinj s]
    exact hτ
  have hss : s * s = 1 := by rw [← sq, ← hs, pow_orderOf_eq_one]
  have hs1 : s ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at hs
    exact absurd hs (by norm_num)
  have hDm' : LieModel D .PSL 3 2 1 := LieType.CurtisTits.lieModel_of_mulEquiv
    (SeitzReduction.quotientCenterMulEquiv hZD) hDm
  obtain ⟨e⟩ := SeitzReduction.LinearPilot.nonempty_equiv_GL32_of_lieModel hDm'
  have hfix : ∀ y : fixedSubgroup (MulAut.conj s), (y : S) * s = s * y := by
    intro y
    have h1 : s * (y : S) * s⁻¹ = y := y.2
    calc (y : S) * s = s * y * s⁻¹ * s := by rw [h1]
      _ = s * y := by group
  set a : S := (((e.symm gl32a : D) : fixedSubgroup (MulAut.conj s)) : S) with ha
  set b : S := (((e.symm gl32b : D) : fixedSubgroup (MulAut.conj s)) : S) with hb
  have hcoe : ∀ x y : D, ((((x * y : D) : fixedSubgroup (MulAut.conj s)) : S)) =
      (((x : D) : fixedSubgroup (MulAut.conj s)) : S) *
        (((y : D) : fixedSubgroup (MulAut.conj s)) : S) := fun _ _ => rfl
  have haa : a * a = 1 := by
    rw [ha, ← hcoe, ← map_mul, gl32a_mul_self, map_one]
    rfl
  have hbb : b * b = 1 := by
    rw [hb, ← hcoe, ← map_mul, gl32b_mul_self, map_one]
    rfl
  have hab : a * b = b * a := by
    rw [ha, hb, ← hcoe, ← hcoe, ← map_mul, ← map_mul, gl32a_mul_gl32b]
  have hinjD : ∀ x y : D, (((x : D) : fixedSubgroup (MulAut.conj s)) : S) =
      (((y : D) : fixedSubgroup (MulAut.conj s)) : S) → x = y :=
    fun x y h => Subtype.ext (Subtype.ext h)
  have ha1 : a ≠ 1 := fun h1 => gl32a_ne_one (by
    have h3 := congrArg e (hinjD (e.symm gl32a) 1 h1)
    rwa [e.apply_symm_apply, map_one] at h3)
  have hb1 : b ≠ 1 := fun h1 => gl32b_ne.1 (by
    have h3 := congrArg e (hinjD (e.symm gl32b) 1 h1)
    rwa [e.apply_symm_apply, map_one] at h3)
  have hba : b ≠ a := fun h1 => gl32b_ne.2 (by
    have h3 := congrArg e (hinjD (e.symm gl32b) (e.symm gl32a) h1)
    rwa [e.apply_symm_apply, e.apply_symm_apply] at h3)
  have has : a * s = s * a := hfix _
  have hbs : b * s = s * b := hfix _
  set D' : Subgroup S := D.map (fixedSubgroup (MulAut.conj s)).subtype with hD'
  have hVD : zpowers a ⊔ zpowers b ≤ D' :=
    sup_le ((zpowers_le).2 ⟨_, (e.symm gl32a).2, rfl⟩) ((zpowers_le).2 ⟨_, (e.symm gl32b).2, rfl⟩)
  have hsD : s ∉ D' := by
    rintro ⟨y, hyD, hy⟩
    have hy' : (y : S) = s := hy
    have hyZ : (⟨y, hyD⟩ : D) ∈ center D := by
      rw [mem_center_iff]
      intro z
      apply hinjD
      change ((z : fixedSubgroup (MulAut.conj s)) : S) * y = y * z
      rw [hy']
      exact hfix _
    rw [hZD, mem_bot] at hyZ
    apply hs1
    rw [← hy']
    have h3 : y = 1 := congrArg Subtype.val hyZ
    rw [h3]
    rfl
  obtain ⟨hEel, -, hEcard⟩ := elemAbelian_eight_of_commute haa hbb hss ha1 hb1 hba hab has hbs
    fun h3 => hsD (hVD h3)
  exact ⟨_, fun x hx => by rw [← sq]; exact hEel.2 x hx, hEcard⟩

theorem false_of_inner_of_twoRank_le_two {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (hr : CFSG.Open.twoRank S ≤ 2) {τ : MulAut S}
    (hτ : orderOf τ = 2) (hi : τ ∈ (MulAut.conj : S →* MulAut S).range)
    {D : Subgroup (fixedSubgroup τ)} (hDm : LieModel (D ⧸ center D) .PSL 3 2 1)
    (hZD : center D = ⊥) : False := by
  obtain ⟨E, hE, hE8⟩ := exists_elemAbelian_eight_of_inner hS hna hτ hi hDm hZD
  have h4 := SeitzReduction.LinearPilot.card_le_four_of_twoRank_le_two hr E hE
  omega

theorem twoRank_le_two_of_sevenList {S : Type} [Group S] [Finite S]
    (h : LieModel S .PSL 2 7 2 ∨ LieModel S .PSL 3 7 1 ∨ LieModel S .PSU 3 7 1) :
    CFSG.Open.twoRank S ≤ 2 := by
  have hp : (7 : ℕ).Prime := by norm_num
  have hp2 : (7 : ℕ) ≠ 2 := by norm_num
  rcases h with h | h | h
  · exact GH74.SmallRanks.twoRank_le_two_of_statedClassicalModel_PSL_two_odd hp hp2
      (LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h)
  · exact GH74.Filter.t_PSL_three_odd S 7 1 hp2
      (LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h)
  · exact GH74.Filter.t_PSU_three_odd S 7 1 hp2
      (LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h)

theorem d4QTwoSevenFamilyInput_of_list {t : StatedLieTag}
    (hl : SeitzReduction.LinearPilot.LFiveSevenListFamilyInput t)
    (hcand : D4QTwoCandidateOuterInput) : D4QTwoSevenFamilyInput t := by
  intro S _ _ hS hna n f hadm hSm _ τ hτ D hD hDm hZD h2
  have hlist := hl S hS hna n f hadm hSm τ hτ D hD hDm h2
  by_cases hi : τ ∈ (MulAut.conj : S →* MulAut S).range
  · exact (false_of_inner_of_twoRank_le_two hS hna (twoRank_le_two_of_sevenList hlist) hτ hi
      hDm hZD).elim
  · rcases h2 with h2 | ⟨hi', -⟩
    · exact ⟨hcand S hS hna hlist τ hτ hi D hD hDm hZD h2, fun hi' => absurd hi' hi⟩
    · exact absurd hi' hi

theorem d4QTwoSevenFamilyInput_of_twisted {t : StatedLieTag}
    (ht : t = .twistedB2 ∨ t = .twistedF4 ∨ t = .twistedG2 ∨ t = .Tits) :
    D4QTwoSevenFamilyInput t := by
  refine d4QTwoSevenFamilyInput_of_not_admissible fun n f hadm => ?_
  rcases ht with rfl | rfl | rfl | rfl <;> obtain ⟨-, -, -, h, -⟩ := hadm <;> omega

theorem d4QTwoCandidateOuterInput_holds :
    D4QTwoCandidateOuterInput := by
  intro S _ _ _ _ hcase τ hτ hout D hD hDm hZD h2
  have h168 := card_dvd_card_fixedSubgroup_of_lieModel hDm hZD
  have hpos : 0 < Nat.card (fixedSubgroup τ) := Nat.card_pos
  rcases hcase with hm | hm | hm
  · have h16 := sixteen_dvd_card_fixed_psl_two_fortyNine hm hτ hout
      ((by norm_num : 2 ^ 3 ∣ 168).trans h168)
    exact (lt_of_two_pow_dvd_of_dvd hpos h168 h16).1 le_rfl
  · have h336 := dvd_card_fixed_psl_three_seven hm hτ hout
    omega
  · have h336 := dvd_card_fixed_psu_three_seven hm hτ
      (SeitzReduction.LinearPilot.sevenL3Group_of_hyp hD hDm (Or.inl h2))
    omega

section Families

set_option linter.unusedSectionVars false


theorem d4QTwoSevenFamilyInput_PSL (hcand : D4QTwoCandidateOuterInput) :
    D4QTwoSevenFamilyInput .PSL :=
  d4QTwoSevenFamilyInput_of_list SeitzReduction.LinearPilot.lFiveSevenListFamilyInput_PSL_holds
    hcand

theorem d4QTwoSevenFamilyInput_PSU (hcand : D4QTwoCandidateOuterInput) :
    D4QTwoSevenFamilyInput .PSU :=
  d4QTwoSevenFamilyInput_of_list SeitzReduction.LinearPilot.lFiveSevenListFamilyInput_PSU_holds
    hcand

theorem d4QTwoSevenFamilyInput_PSp (hcand : D4QTwoCandidateOuterInput) :
    D4QTwoSevenFamilyInput .PSp :=
  d4QTwoSevenFamilyInput_of_list (SeitzReduction.LinearPilot.lFiveSevenListFamilyInput_PSp_of_PSp47
    SeitzReduction.LinearPilot.lFiveSevenPSp47Input_holds) hcand

theorem d4QTwoSevenFamilyInput_orthogonal (hcand : D4QTwoCandidateOuterInput) :
    D4QTwoSevenFamilyInput .POmegaOdd ∧ D4QTwoSevenFamilyInput .POmegaPlus ∧
      D4QTwoSevenFamilyInput .POmegaMinus :=
  ⟨d4QTwoSevenFamilyInput_of_list
      SeitzReduction.LinearPilot.lFiveSevenListFamilyInput_POmegaOdd_holds hcand,
    d4QTwoSevenFamilyInput_of_list
      SeitzReduction.LinearPilot.lFiveSevenListFamilyInput_POmegaPlus_holds hcand,
    d4QTwoSevenFamilyInput_of_list
      SeitzReduction.LinearPilot.lFiveSevenListFamilyInput_POmegaMinus_holds hcand⟩

theorem d4QTwoSevenFamilyInput_large :
    D4QTwoSevenFamilyInput .F4 ∧ D4QTwoSevenFamilyInput .E6 ∧ D4QTwoSevenFamilyInput .E7 ∧
      D4QTwoSevenFamilyInput .E8 ∧ D4QTwoSevenFamilyInput .twistedE6 :=
  ⟨d4QTwoSevenFamilyInput_of_not_gen4 fun S _ _ _ f hSm => GH74.Filter.t_F4_odd S 7 f
      (by norm_num) (GH74.chevalleyExceptionalModel_of_lieModel (by decide) hSm),
    d4QTwoSevenFamilyInput_of_not_gen4 fun S _ _ _ f hSm => GH74.Filter.t_E6_odd S 7 f
      (by norm_num) (GH74.chevalleyExceptionalModel_of_lieModel (by decide) hSm),
    d4QTwoSevenFamilyInput_of_not_gen4 fun S _ _ _ f hSm => GH74.Filter.t_E7_odd S 7 f
      (by norm_num) (GH74.chevalleyExceptionalModel_of_lieModel (by decide) hSm),
    d4QTwoSevenFamilyInput_of_not_gen4 fun S _ _ _ f hSm => GH74.Filter.t_E8_odd S 7 f
      (by norm_num) (GH74.chevalleyExceptionalModel_of_lieModel (by decide) hSm),
    d4QTwoSevenFamilyInput_of_not_gen4 fun S _ _ _ f hSm => GH74.Filter.t_2E6_odd S 7 f
      (by norm_num) (GH74.chevalleyExceptionalModel_of_lieModel (by decide) hSm)⟩

theorem d4QTwoSevenFamilyInput_G2 : D4QTwoSevenFamilyInput .G2 := by
  refine d4QTwoSevenFamilyInput_of_two_pow fun S _ _ _ _ m f _ hSm τ hτ _ _ _ => ?_
  obtain rfl := SeitzReduction.RankOne.FiveEx.eq_zero_of_lieModel_exc (by decide) hSm
  have h6 := SeitzReduction.RankOne.excTwoPartInput_G2_of_pow (s := 4) (by norm_num)
    (by norm_num) (by norm_num)
    (SeitzReduction.LinearPilot.SevenList.sixteen_dvd_seven_pow_sq_sub_one f) (by norm_num) le_rfl
    S hSm τ hτ
  exact ⟨(pow_dvd_pow 2 (by norm_num)).trans h6, fun _ => (pow_dvd_pow 2 (by norm_num)).trans h6⟩

theorem d4QTwoSevenFamilyInput_trialityD4
    (h3D4 : SeitzReduction.RankOne.TrialityInnerTwoPartInput 7 1 5) :
    D4QTwoSevenFamilyInput .trialityD4 := by
  refine d4QTwoSevenFamilyInput_of_two_pow fun S _ _ _ _ m f hadm hSm τ hτ D hD hDm => ?_
  obtain rfl := SeitzReduction.RankOne.FiveEx.eq_zero_of_lieModel_exc (by decide) hSm
  by_cases hi : τ ∈ (MulAut.conj : S →* MulAut S).range
  · obtain ⟨d, -, hDd⟩ :=
      SeitzReduction.RankOne.FiveEx.exists_lieModel_PSL_of_isComponent_trialityD4_inner
        (by norm_num) (by norm_num) hadm hSm τ hτ hi D hD
    obtain ⟨-, -, h7'⟩ := SeitzReduction.LinearPilot.eq_seven_of_lieModel_PSL_three_two hDm
      (by norm_num) (SeitzReduction.CrossChar.statedLieAdmissible_of_lieModel hDd) hDd
    have hf1 : f = 1 := Nat.eq_one_of_mul_eq_one_right
      (SeitzReduction.LinearPilot.SevenList.eq_one_of_seven_pow_eq_seven h7')
    subst hf1
    have h5 := h3D4 S hSm τ hτ hi
    exact ⟨(pow_dvd_pow 2 (by norm_num)).trans h5, fun _ => h5⟩
  · have h6 := SeitzReduction.RankOne.two_pow_six_dvd_card_fixed_trialityD4_outer (by norm_num)
      (by norm_num) hSm τ hτ hi
    exact ⟨(pow_dvd_pow 2 (by norm_num)).trans h6, fun h => absurd h hi⟩

theorem d4QTwoSevenFamilyInput_all (hcand : D4QTwoCandidateOuterInput) :
    ∀ t, D4QTwoSevenFamilyInput t := by
  intro t
  obtain ⟨hOO, hOP, hOM⟩ := d4QTwoSevenFamilyInput_orthogonal hcand
  obtain ⟨hF4, hE6, hE7, hE8, h2E6⟩ := d4QTwoSevenFamilyInput_large
  cases t
  exacts [d4QTwoSevenFamilyInput_PSL hcand, d4QTwoSevenFamilyInput_PSU hcand,
    d4QTwoSevenFamilyInput_PSp hcand, hOO, hOP, hOM, d4QTwoSevenFamilyInput_G2, hF4, hE6, hE7,
    hE8, h2E6, d4QTwoSevenFamilyInput_trialityD4 (trialityInnerTwoPartInput_of_pow (s := 4)
      (by norm_num) (by norm_num) (by norm_num) (sixteen_dvd_seven_pow_sq_sub_one' 1)
      (by norm_num) (by norm_num)),
    d4QTwoSevenFamilyInput_of_twisted (Or.inl rfl),
    d4QTwoSevenFamilyInput_of_twisted (Or.inr (Or.inr (Or.inl rfl))),
    d4QTwoSevenFamilyInput_of_twisted (Or.inr (Or.inl rfl)),
    d4QTwoSevenFamilyInput_of_twisted (Or.inr (Or.inr (Or.inr rfl)))]

theorem d4QTwo_oddLie (h7 : ∀ t, D4QTwoSevenFamilyInput t) {S : Type} [Group S] [Finite S]
    (hS : IsSimpleGroup S) (hna : ∃ a b : S, a * b ≠ b * a) (hodd : OddLieType S)
    (hgen : GH74.Gen4 S) {τ : MulAut S} (hτ : orderOf τ = 2) {D : Subgroup (fixedSubgroup τ)}
    (hD : CFSG.IsComponent D) (hDm : LieModel (D ⧸ center D) .PSL 3 2 1) (hZD : center D = ⊥)
    (h2 : SeitzReduction.F4Pilot.FixedCentralizerTwoFree τ D ∨
      (τ ∈ (MulAut.conj : S →* MulAut S).range ∧
        SeitzReduction.LinearPilot.FixedCentralizerTwoSmall τ D)) :
    168 < Nat.card (fixedSubgroup τ) ∧
      (τ ∈ (MulAut.conj : S →* MulAut S).range → 336 < Nat.card (fixedSubgroup τ)) := by
  obtain ⟨t, n, p, f, hp, hp2, hadm, hL⟩ := hodd
  rcases SeitzReduction.gls3OddLieAutComponentsInput S t n p f hp hp2 hadm hL τ hτ D hD with
    ⟨t', n', f', hadm', hL'⟩ | ⟨-, -, -, hK⟩
  · obtain ⟨-, -, hpow⟩ :=
      SeitzReduction.LinearPilot.eq_seven_of_lieModel_PSL_three_two hDm hp2 hadm' hL'
    obtain ⟨rfl, -⟩ := SeitzReduction.LinearPilot.eq_seven_of_pow_eq_seven hp hpow
    exact h7 t S hS hna n f hadm hL hgen τ hτ D hD hDm hZD h2
  · exfalso
    have h504 : Nat.card D = 504 := by
      rw [SeitzReduction.LinearPilot.card_of_lieModel_PSL_two hK]
      decide
    have h168 := SeitzReduction.LinearPilot.card_of_lieModel_PSL_three_two hDm
    have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup (center D)
    rw [h504, h168, hZD, card_bot] at hmul
    norm_num at hmul

theorem d4QTwo_sporadic {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (hsp : NativeSporadic.SporadicRep S) {τ : MulAut S}
    (hτ : orderOf τ = 2) {D : Subgroup (fixedSubgroup τ)} (hD : CFSG.IsComponent D)
    (hDm : LieModel (D ⧸ center D) .PSL 3 2 1) (hZD : center D = ⊥)
    (h2 : SeitzReduction.F4Pilot.FixedCentralizerTwoFree τ D ∨
      (τ ∈ (MulAut.conj : S →* MulAut S).range ∧
        SeitzReduction.LinearPilot.FixedCentralizerTwoSmall τ D)) :
    168 < Nat.card (fixedSubgroup τ) ∧
      (τ ∈ (MulAut.conj : S →* MulAut S).range → 336 < Nat.card (fixedSubgroup τ)) := by
  obtain ⟨e⟩ := SeitzReduction.LinearPilot.eq_J2_of_lFiveSmallKind_sporadic hS hna hsp hτ hD hDm h2
  have h168 := card_dvd_card_fixedSubgroup_of_lieModel hDm hZD
  by_cases hi : τ ∈ (MulAut.conj : S →* MulAut S).range
  · exfalso
    obtain ⟨s, rfl⟩ := hi
    have hinj := ComponentClassification.CatLeaf.mulAut_conj_injective_of_simple (S := S) hna
    have hs : orderOf s = 2 := by
      rw [← orderOf_injective _ hinj s]
      exact hτ
    rw [SeitzReduction.SporadicRefine.fixedSubgroup_conj_eq_centralizerOf s] at h168
    rcases SeitzReduction.SporadicRefine.j2_card_centralizer e hs with hC | hC <;>
      rw [hC] at h168 <;> norm_num at h168
  · have h336 := SeitzReduction.SporadicRefine.j2_card_fixedSubgroup_outer e hτ hi
    exact ⟨by omega, fun h => absurd h hi⟩

theorem d4QTwoSmallKindInput_of (hcand : D4QTwoCandidateOuterInput) :
    D4QTwoSmallKindInput := by
  intro S _ _ hq hZ hsm hgen τ hτ D hD hDm hZD h2
  obtain ⟨-, hsq, ⟨a₀, b₀, hab₀⟩⟩ := hq
  have hS : IsSimpleGroup S := by
    have := hsq
    exact (SeitzReduction.quotientCenterMulEquiv hZ).symm.isSimpleGroup
  have hna : ∃ a b : S, a * b ≠ b * a := by
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a₀
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b₀
    exact ⟨a, b, fun h => hab₀ (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h])⟩
  obtain ⟨-, h4 | ⟨-, hodd'⟩ | ⟨-, hsp⟩⟩ := hsm
  · exact absurd h4.1 (by norm_num)
  · obtain ⟨t, n, p, f, hp, hp2, hadm, hL⟩ := hodd'
    exact d4QTwo_oddLie (d4QTwoSevenFamilyInput_all hcand) hS hna
      ⟨t, n, p, f, hp, hp2, hadm, LieType.CurtisTits.lieModel_of_mulEquiv
        (SeitzReduction.quotientCenterMulEquiv hZ) hL⟩ hgen hτ hD hDm hZD h2
  · obtain ⟨s, ⟨e⟩⟩ := hsp
    exact d4QTwo_sporadic hS hna ⟨s, ⟨(SeitzReduction.quotientCenterMulEquiv hZ).symm.trans e⟩⟩
      hτ hD hDm hZD h2

theorem d4QTwoSmallKindInput_holds :
    D4QTwoSmallKindInput :=
  d4QTwoSmallKindInput_of d4QTwoCandidateOuterInput_holds

end Families

section Main


namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem yamada_5_4_two
    (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hf : f = 1) :
    ∃ Kc : Subgroup (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) ⧸
        CFSG.oddCore (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G))),
      CFSG.IsComponent Kc ∧
      ((d.leviJ₀.map L.subtype).subgroupOf
          (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G))).map
          (QuotientGroup.mk' (CFSG.oddCore
            (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)))) ≤
        Kc ⊔ Kc.map (MulAut.conj (QuotientGroup.mk' (CFSG.oddCore
          (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)))
            ⟨t, h.t_mem_centralizer_J₀ d⟩)).toMonoidHom ∧
      ((Kc.map (MulAut.conj (QuotientGroup.mk' (CFSG.oddCore
          (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)))
            ⟨t, h.t_mem_centralizer_J₀ d⟩)).toMonoidHom = Kc ∧
          ((d.leviJ₀.map L.subtype).subgroupOf
            (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G))).map
            (QuotientGroup.mk' (CFSG.oddCore
              (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)))) < Kc ∧
          QuotientGroup.mk' (CFSG.oddCore
            (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)))
              ⟨t, h.t_mem_centralizer_J₀ d⟩ ∉ Kc ∧
          (∃ hsN : QuotientGroup.mk' (CFSG.oddCore
              (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)))
                ⟨t, h.t_mem_centralizer_J₀ d⟩ ∈ normalizer (Kc : Set _),
            Kc.normalizerMonoidHom ⟨_, hsN⟩ ∉ (MulAut.conj : Kc →* MulAut Kc).range) ∧
          center Kc = ⊥ ∧ LieModel Kc .PSL 3 2 (2 * f)) ∨
        (Kc.map (MulAut.conj (QuotientGroup.mk' (CFSG.oddCore
            (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)))
              ⟨t, h.t_mem_centralizer_J₀ d⟩)).toMonoidHom ≠ Kc ∧
          ⁅Kc, Kc.map (MulAut.conj (QuotientGroup.mk' (CFSG.oddCore
            (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)))
              ⟨t, h.t_mem_centralizer_J₀ d⟩)).toMonoidHom⁆ = ⊥ ∧
          center Kc = ⊥ ∧
          Nonempty (Kc ≃* (((d.leviJ₀.map L.subtype).subgroupOf
            (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G))).map
            (QuotientGroup.mk' (CFSG.oddCore
              (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)))) : Subgroup _)))) :=
  h.yamada_5_4_two_of_input d hf d4QTwoSmallKindInput_holds

end Setup

end Main

end CFSG.LocalAnalysis.EvenBN.TrialityD4
