module

public import CFSG.LieType.SteinbergBRAutGL32
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilySmall
import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2Small

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.LinearPilot

open CFSG Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.SeitzReduction.RankOne (normal_of_isComponent_of_twoSmall card_le_two_of_le_centralizer
  quotientCenterAutHom quotientCenterAutHom_injective card_le_of_isPGroup_of_card_dvd
  card_eq_card_inf_centralizer_mul_card_range)

theorem card_of_lieModel_PSL_three_two {X : Type} [Group X] (hX : LieModel X .PSL 3 2 1) :
    Nat.card X = 168 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_two (hX.statedClassicalModel (by decide))

theorem nonempty_equiv_GL32_of_lieModel {X : Type} [Group X] (h : LieModel X .PSL 3 2 1) :
    Nonempty (X ≃* CFSG.QuasithinUnique.Setup.Family.GL32) := by
  rcases h with ⟨-, hc⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · obtain ⟨-, K, hK, hKf, hcard, ⟨e⟩⟩ := hc
    exact ⟨e.trans ((CFSG.QuasithinUnique.Setup.Family.statedProjSL_equiv_of_card_two 3 K
      (by rw [hcard]; norm_num)).trans (CFSG.QuasithinUnique.Setup.Family.slEquivGL 3))⟩
  all_goals exact absurd h0 (by norm_num)

theorem card_mulAut_of_lieModel_PSL_three_two {X : Type} [Group X] (hX : LieModel X .PSL 3 2 1) :
    Nat.card (MulAut X) = 336 := by
  obtain ⟨e⟩ := nonempty_equiv_GL32_of_lieModel hX
  rw [Nat.card_congr (MulAut.congr e).toEquiv, CFSG.LieType.SteinbergBR.AutGL32.card_mulAut_GL32]

theorem fixedCentralizerTwoSmall_of_twoFree' {S : Type} [Group S] {σ : MulAut S}
    {D : Subgroup (fixedSubgroup σ)} (h : F4Pilot.FixedCentralizerTwoFree σ D) :
    FixedCentralizerTwoSmall σ D := by
  intro U hU hUD hUσ
  rw [h U hU hUD hUσ, card_bot]
  norm_num

theorem fixedCentralizerTwoSmall_of_lFive_hyp {S : Type} [Group S] {σ : MulAut S}
    {D : Subgroup (fixedSubgroup σ)}
    (h : F4Pilot.FixedCentralizerTwoFree σ D ∨
      (σ ∈ (MulAut.conj : S →* MulAut S).range ∧ FixedCentralizerTwoSmall σ D)) :
    FixedCentralizerTwoSmall σ D :=
  h.elim fixedCentralizerTwoSmall_of_twoFree' And.right

theorem card_le_of_isPGroup_fixedSubgroup_lThree {J : Type} [Group J] [Finite J] {τ : MulAut J}
    {D : Subgroup (fixedSubgroup τ)} (hD : IsComponent D)
    (hDm : LieModel (D ⧸ center D) .PSL 3 2 1) (h2 : FixedCentralizerTwoSmall τ D)
    {Q : Subgroup (fixedSubgroup τ)} (hQ : IsPGroup 2 Q) : Nat.card Q ≤ 32 := by
  have hN : D.Normal := normal_of_isComponent_of_twoSmall hD h2
  have hQN : Q ≤ normalizer (D : Set (fixedSubgroup τ)) := by
    rw [normalizer_eq_top_iff.mpr hN]
    exact le_top
  have hcard := card_eq_card_inf_centralizer_mul_card_range hQN
  have h1 : Nat.card (Q ⊓ centralizer (D : Set (fixedSubgroup τ)) : Subgroup _) ≤ 2 :=
    card_le_two_of_le_centralizer h2 (hQ.to_le inf_le_left) inf_le_right
  set R := (D.normalizerMonoidHom.comp (inclusion hQN)).range with hR
  have hRp : IsPGroup 2 R := hQ.of_surjective _
    (D.normalizerMonoidHom.comp (inclusion hQN)).rangeRestrict_surjective
  have : Group.IsPerfect D := hD.1.1
  have hA := card_mulAut_of_lieModel_PSL_three_two hDm
  have : Finite (MulAut (D ⧸ center D)) := Nat.finite_of_card_ne_zero (by rw [hA]; norm_num)
  have h3 : Nat.card (R.map (quotientCenterAutHom D)) ≤ 16 :=
    card_le_of_isPGroup_of_card_dvd (hRp.map _) (u := 21) (by decide) (by norm_num)
      (by rw [hA])
  rw [card_map_of_injective quotientCenterAutHom_injective] at h3
  rw [hcard]
  calc _ ≤ 2 * 16 := Nat.mul_le_mul h1 h3
    _ = 32 := by norm_num

theorem not_sixtyFour_dvd_card_fixedSubgroup_lThree {J : Type} [Group J] [Finite J]
    {τ : MulAut J} {D : Subgroup (fixedSubgroup τ)} (hD : IsComponent D)
    (hDm : LieModel (D ⧸ center D) .PSL 3 2 1) (h2 : FixedCentralizerTwoSmall τ D) :
    ¬ 64 ∣ Nat.card (fixedSubgroup τ) := by
  intro h64
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := Sylow.exists_subgroup_card_pow_prime (G := fixedSubgroup τ) 2 (n := 6)
    (by norm_num; exact h64)
  have h1 := card_le_of_isPGroup_fixedSubgroup_lThree hD hDm h2 (IsPGroup.of_card hQ)
  rw [hQ] at h1
  norm_num at h1

theorem commutator_eq_self_of_isPerfect {G : Type*} [Group G] {D : Subgroup G}
    (hD : Group.IsPerfect D) : ⁅D, D⁆ = D := by
  have h2 := Subgroup.map_commutator (⊤ : Subgroup ↥D) ⊤ D.subtype
  rw [← commutator_def, Group.IsPerfect.commutator_eq_top, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype] at h2
  exact h2.symm

theorem le_of_isPerfect_of_index_dvd_two {G : Type*} [Group G] {D H : Subgroup G}
    (hD : Group.IsPerfect D) (hH : H.index ∣ 2) : D ≤ H := by
  rcases (Nat.dvd_prime Nat.prime_two).1 hH with h1 | h2
  · rw [Subgroup.index_eq_one.1 h1]
    exact le_top
  · rw [← commutator_eq_self_of_isPerfect hD, Subgroup.commutator_le]
    intro x _ y _
    have hx := Subgroup.mul_self_mem_of_index_two h2 x
    have hxy := Subgroup.mul_self_mem_of_index_two h2 (x⁻¹ * y)
    have hy := Subgroup.mul_self_mem_of_index_two h2 y⁻¹
    rw [commutatorElement_def]
    have he : x * y * x⁻¹ * y⁻¹ = (x * x) * ((x⁻¹ * y) * (x⁻¹ * y)) * (y⁻¹ * y⁻¹) := by group
    rw [he]
    exact H.mul_mem (H.mul_mem hx hxy) hy

theorem false_of_lThree_of_centralizer_eq_bot {C : Type} [Group C] [Finite C] {D : Subgroup C}
    [D.Normal] (hDp : Group.IsPerfect D) (hDm : LieModel (D ⧸ center D) .PSL 3 2 1)
    (hcen : centralizer (D : Set C) = ⊥) {a : C} (ha : orderOf a = 2)
    (hdvd : 168 ∣ Nat.card (centralizer {a} : Subgroup C) ∨
      60 ∣ Nat.card (centralizer {a} : Subgroup C) ∨
      72 ∣ Nat.card (centralizer {a} : Subgroup C)) : False := by
  have : Group.IsPerfect D := hDp
  set ψ : C →* MulAut (D ⧸ center D) := (quotientCenterAutHom D).comp MulAut.conjNormal with hψ
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have h3 : (MulAut.conjNormal g : MulAut D) = 1 :=
      quotientCenterAutHom_injective (hg.trans (map_one _).symm)
    have hgC : g ∈ centralizer (D : Set C) := by
      rw [mem_centralizer_iff]
      intro d hd
      have h4 := congrArg (fun φ : MulAut D => ((φ ⟨d, hd⟩ : D) : C)) h3
      simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h4
      calc d * g = g * d * g⁻¹ * g := by rw [h4]
        _ = g * d := by group
    rw [hcen] at hgC
    exact mem_bot.mp hgC
  have hA := card_mulAut_of_lieModel_PSL_three_two hDm
  have : Finite (MulAut (D ⧸ center D)) := Nat.finite_of_card_ne_zero (by rw [hA]; norm_num)
  have hC : Nat.card C ∣ 336 := hA ▸ Subgroup.card_dvd_of_injective ψ hψinj
  set H : Subgroup C := centralizer {a} with hHdef
  have hCa : Nat.card H ∣ 336 := (card_subgroup_dvd_card H).trans hC
  have h168 : 168 ∣ Nat.card H := by
    rcases hdvd with h | h | h
    · exact h
    · exact absurd (h.trans hCa) (by norm_num)
    · exact absurd (h.trans hCa) (by norm_num)
  have hidx : H.index ∣ 2 := by
    obtain ⟨k, hk⟩ := h168
    obtain ⟨m, hm⟩ := hC
    have hmul := H.card_mul_index
    have e1 : 168 * 2 = 168 * (k * (H.index * m)) := by
      calc 168 * 2 = 336 := by norm_num
        _ = Nat.card C * m := hm
        _ = (Nat.card H * H.index) * m := by rw [hmul]
        _ = 168 * (k * (H.index * m)) := by rw [hk]; ring
    have e2 : 2 = k * (H.index * m) := Nat.eq_of_mul_eq_mul_left (by norm_num) e1
    exact ⟨k * m, by rw [e2]; ring⟩
  have hDH : D ≤ H := le_of_isPerfect_of_index_dvd_two hDp hidx
  have haC : a ∈ centralizer (D : Set C) := by
    rw [mem_centralizer_iff]
    intro d hd
    have h1 := hDH hd
    rw [hHdef, mem_centralizer_singleton_iff] at h1
    exact h1
  rw [hcen, mem_bot] at haC
  rw [haC, orderOf_one] at ha
  exact absurd ha (by norm_num)

theorem eq_commutator_of_isComponent_of_isQuasisimple {G : Type*} [Group G] [Finite G]
    {B : Subgroup G} (hB : IsComponent B) (hq : IsQuasisimple (commutator G)) :
    B = commutator G := by
  have hc : IsComponent (commutator G) := ⟨hq, Subgroup.Normal.isSubnormal inferInstance⟩
  rcases CFSG.LocalCores.distinct_components_commute hB hc with h | h
  · exact h
  · exfalso
    have hBB : ⁅B, B⁆ = B := commutator_eq_self_of_isPerfect hB.1.1
    have hBQ : B ≤ commutator G := by
      rw [← hBB, _root_.commutator_def]
      exact Subgroup.commutator_mono le_top le_top
    have hBC : B ≤ centralizer (B : Set G) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h).trans (Subgroup.centralizer_le hBQ)
    have hbot : B = ⊥ := by
      rw [← hBB]
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hBC
    have hnt := CFSG.LocalCores.isQuasisimple_nontrivial hB.1
    rw [hbot] at hnt
    obtain ⟨x, y, hxy⟩ := hnt
    exact hxy (Subsingleton.elim x y)

noncomputable def commutatorSubgroupEquiv {G : Type*} [Group G] (H : Subgroup G) :
    commutator H ≃* (⁅H, H⁆ : Subgroup G) :=
  ((commutator H).equivMapOfInjective H.subtype H.subtype_injective).trans
    (MulEquiv.subgroupCongr (by
      rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype]))

theorem card_quotient_center_of_isComponent_of_commutator {G : Type*} [Group G] {H : Subgroup G}
    [Finite H] (hq : IsQuasisimple (⁅H, H⁆ : Subgroup G)) {B : Subgroup H} (hB : IsComponent B) :
    Nat.card (B ⧸ center B) =
      Nat.card ((⁅H, H⁆ : Subgroup G) ⧸ center (⁅H, H⁆ : Subgroup G)) := by
  have hq' : IsQuasisimple (commutator H) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (commutatorSubgroupEquiv H).symm hq
  have hBeq := eq_commutator_of_isComponent_of_isQuasisimple hB hq'
  subst hBeq
  exact Nat.card_congr (QuotientGroup.congr _ _ (commutatorSubgroupEquiv H)
    (Subgroup.map_center_eq _)).toEquiv

end CFSG.SeitzReduction.LinearPilot
