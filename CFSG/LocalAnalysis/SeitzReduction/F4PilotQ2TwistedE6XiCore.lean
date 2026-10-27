module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2TwistedE6XiStep3

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
open CFSG.LieType.Ree (ReeTag)
open CFSG.Quasithin (perfectCore)

section General

theorem dvd_index_center_of_surjective {E R : Type*} [Group E] [Group R] (f : E →* R)
    (hf : Function.Surjective f) (Kc : Subgroup R) {p : ℕ} (hp : p ∣ (center Kc).index) :
    p ∣ (center E).index := by
  set Z' := (center E).map f with hZ'
  have hZ'c : Z' ≤ center R := by
    rintro _ ⟨z, hz, rfl⟩
    rw [mem_center_iff]
    intro r
    obtain ⟨x, rfl⟩ := hf r
    rw [← map_mul, ← map_mul, (mem_center_iff.1 hz) x]
  have : Z'.Normal := Subgroup.normal_of_le_center hZ'c
  have h1 : (center Kc).index ∣ (Z'.subgroupOf Kc).index := by
    apply Subgroup.index_dvd_of_le
    intro x hx
    rw [mem_subgroupOf] at hx
    rw [mem_center_iff]
    intro y
    exact Subtype.ext ((mem_center_iff.1 (hZ'c hx)) y)
  have h2 : (Z'.subgroupOf Kc).index ∣ Z'.index := Subgroup.relIndex_dvd_index_of_normal Z' Kc
  have h3 : Z'.index ∣ (center E).index := Subgroup.index_map_dvd (center E) hf
  exact hp.trans (h1.trans (h2.trans h3))

theorem prime_dvd_index_center_of_le_range {G : Type*} [Group G] [Finite G] {H : Subgroup G}
    (N : Subgroup H) [N.Normal] {E : Subgroup G} (hEH : E ≤ H)
    (hE : ∀ P : Subgroup G, ⁅P, P⁆ = P → P ≤ H → P ≤ E) {Kc : Subgroup (H ⧸ N)}
    (hKp : ⁅Kc, Kc⁆ = Kc) {p : ℕ} (hp : p ∣ (center Kc).index) :
    p * Nat.card (center E) ∣ Nat.card E := by
  set π := QuotientGroup.mk' N with hπ
  set f₀ : E →* H ⧸ N := π.comp (Subgroup.inclusion hEH) with hf₀
  have hKr : Kc ≤ f₀.range := by
    set Q := Kc.comap π with hQdef
    have hQ : Q.map π = Kc :=
      Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N) Kc
    have hPQ : (perfectCore Q).map π = Kc := by
      rw [CFSG.Quasithin.map_perfectCore, hQ]
      exact CFSG.Quasithin.perfectCore_eq_self_of_perfect hKp
    have hPE : (perfectCore Q).map H.subtype ≤ E := by
      refine hE _ ?_ ?_
      · rw [← map_commutator, CFSG.Quasithin.perfectCore_perfect]
      · rintro _ ⟨q, -, rfl⟩
        exact q.2
    intro k hk
    rw [← hPQ] at hk
    obtain ⟨q, hq, rfl⟩ := hk
    have hqE : (q : G) ∈ E := hPE ⟨q, hq, rfl⟩
    exact ⟨⟨q, hqE⟩, rfl⟩
  set Kc' : Subgroup f₀.range := Kc.subgroupOf f₀.range with hKc'
  have hidx : (center Kc').index = (center Kc).index := by
    have h1 := Subgroup.index_map_equiv (center Kc') (Subgroup.subgroupOfEquivOfLe hKr)
    rw [Subgroup.map_center_eq] at h1
    exact h1.symm
  have h1 := dvd_index_center_of_surjective f₀.rangeRestrict f₀.rangeRestrict_surjective Kc'
    (hidx ▸ hp)
  rw [← Subgroup.card_mul_index (center E)]
  obtain ⟨c, hc⟩ := h1
  rw [hc]
  exact ⟨c, by ring⟩

end General

section Long

theorem prime_mul_card_center_dvd_of_twoKindAt {G : Type} [Group G] [Finite G]
    {L : Subgroup G} {K : Type} [Field K] {e : L ≃* adjointGroup .F4 K} {t : G}
    {X₀ : Subgroup (adjointGroup .F4 K)} {κ : Sp6Kind} (hκ : TwoKindAt e t X₀ κ)
    (hne : κ ≠ .swap) {p : ℕ} (hp : ∀ (S : Type) [Group S], Sp6KindType S 1 κ → p ∣ Nat.card S) :
    p * Nat.card (center (centralizerPerfectCore (subgroupToG e X₀))) ∣
      Nat.card (centralizerPerfectCore (subgroupToG e X₀)) := by
  obtain ⟨htX, Kc, hKc, -, h1 | h2⟩ := hκ
  · obtain ⟨-, -, -, -, -, -, hty⟩ := h1
    have hpK : p ∣ (center Kc).index := hp _ hty
    have hKp : ⁅Kc, Kc⁆ = Kc := Subgroup.isPerfect_iff.1 hKc.1.1
    exact prime_dvd_index_center_of_le_range _ (centralizerPerfectCore_le_centralizer _)
      (fun P hP hPH => le_centralizerPerfectCore hP hPH) hKp hpK
  · exact absurd h2.1 hne

theorem eleven_mul_card_center_dvd_of_twoKindAt_unitary6 {G : Type} [Group G] [Finite G]
    {L : Subgroup G} {K : Type} [Field K] {e : L ≃* adjointGroup .F4 K} {t : G}
    {X₀ : Subgroup (adjointGroup .F4 K)} (hκ : TwoKindAt e t X₀ .unitary6) :
    11 * Nat.card (center (centralizerPerfectCore (subgroupToG e X₀))) ∣
      Nat.card (centralizerPerfectCore (subgroupToG e X₀)) := by
  refine prime_mul_card_center_dvd_of_twoKindAt hκ (by decide) fun S _ hS => ?_
  have hLie : LieModel S .PSU 6 2 1 := hS
  have hcard : Nat.card S = CFSG.Open.ordTwistedA 5 2 := by
    rcases hLie with ⟨-, hc⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · exact (CFSG.Timmesfeld.card_statedClassicalModel_two hc).2.1 rfl
    all_goals exact absurd h0 (by norm_num)
  rw [hcard]
  decide +kernel

end Long

section Short

@[expose] def TwoOmegaPlusEightCoreElevenInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K : Type) [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (e : L ≃* adjointGroup .F4 K) (t : G), F4Work L K t 1 →
    ∀ X₀ : Subgroup (adjointGroup .F4 K),
      X₀ ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K) → IsCyclic X₀ →
      Nat.card X₀ = 3 → TwoKindAt e t X₀ .omegaPlus8 →
      ¬ 11 ∣ Nat.card (centralizerPerfectCore (subgroupToG e X₀))

theorem twoTwistedE6CoreNotDvdInput_of_omegaPlus8 (h : TwoOmegaPlusEightCoreElevenInput) :
    TwoTwistedE6CoreNotDvdInput := by
  intro G _ _ L K _ _ _ e t hw X₀ hXJ hcyc hX₀ hκ hκ' hdvd
  have h11 := eleven_mul_card_center_dvd_of_twoKindAt_unitary6 hκ
  have hpos : 0 < Nat.card (center (centralizerPerfectCore (subgroupToG e X₀))) := Nat.card_pos
  refine h G L K (e.trans (graphAutF4 K).symm) t hw X₀ hXJ hcyc hX₀ hκ' ?_
  have h2 := h11.trans hdvd
  rw [mul_comm 11] at h2
  exact Nat.dvd_of_mul_dvd_mul_left hpos h2

end Short

end CFSG.SeitzReduction.F4Pilot
