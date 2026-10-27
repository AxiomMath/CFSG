module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicMovedPerfect
public import CFSG.Monster.Existence.Census.TwoClasses
public import CFSG.Monster.AxisCount.HSCount
public import CFSG.Monster.SteinbergMBXGeneratedPerfectCover
public import CFSG.Monster.SteinbergMHmatInnerAut
public import CFSG.Sporadic.Schreier.Co1OddInner
public import CFSG.Sporadic.Co2Schreier.FullAut
public import CFSG.RankThree.PartOne.SPOR.OuterM

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Monster

open Subgroup CFSG.Open CFSG.ComponentClassification.RankTwoSporadic
open CFSG.Monster CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated
open CFSG.Monster.B CFSG.Monster.B.Short CFSG.Monster.Existence
open scoped commutatorElement

theorem centDer_tStar :
    centDer Gmat tStar = Cgen := by
  rw [centDer, AxisCount.HS.centralizer_tStar_eq_Cgen]
  exact commutator_self_of_commutator_eq_top short_centralizer_generated_perfect_cover.1

theorem isQuasisimple_Cgen :
    CFSG.Open.IsQuasisimple ↥Cgen := by
  obtain ⟨h1, -, -, ⟨e⟩, -, hs, -⟩ := short_centralizer_generated_perfect_cover
  exact ⟨h1, e.isSimpleGroup⟩

theorem mem_zpowers_of_mem_centralizer_Cgen
    {b : SpaceB ≃ₗ[ℚ] SpaceB} (hb : b ∈ Cgen) (hbc : b ∈ centralizer (Cgen : Set _)) :
    b ∈ zpowers tStar := by
  have hcen : (⟨b, hb⟩ : ↥Cgen) ∈ center ↥Cgen := by
    rw [mem_center_iff]
    intro g
    exact Subtype.ext ((mem_centralizer_iff.mp hbc) g g.2)
  rw [short_centralizer_generated_perfect_cover.2.1] at hcen
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hcen
  exact mem_zpowers_iff.mpr ⟨k, congrArg Subtype.val hk⟩

theorem yWitness_tStar
    {E : Subgroup (SpaceB ≃ₗ[ℚ] SpaceB)} (hEG : E ≤ Gmat) (hE : IsElemAbelian 2 E)
    (hE4 : 4 ≤ Nat.card E) (ht : tStar ∈ E) : YWitness Gmat E := by
  obtain ⟨b, hbE, hbz⟩ := exists_not_mem_zpowers_of_isElemAbelian hE4
    (by rw [sq]; exact B.tStar_mul_self)
  have hbt : b * tStar = tStar * b :=
    congrArg Subtype.val (hE.1.is_comm.comm ⟨b, hbE⟩ ⟨tStar, ht⟩)
  have hbC : b ∈ Cgen := by
    rw [← AxisCount.HS.centralizer_tStar_eq_Cgen]
    exact ⟨hEG hbE, mem_centralizer_singleton_iff.mpr hbt⟩
  have ht1 : tStar ≠ 1 := fun h => by
    have := B.orderOf_tStar
    rw [h, orderOf_one] at this
    exact absurd this (by norm_num)
  refine yWitness_of_perfect ht ht1 hbE (P := Cgen) centDer_tStar.ge
    (commutator_self_of_commutator_eq_top short_centralizer_generated_perfect_cover.1)
    (fourProp_of_quasisimple isQuasisimple_Cgen
      ⟨TwoA.Census.cSqrt, Jstar_le_Cgen TwoA.Census.cSqrt_mem_Jstar,
        by rw [TwoA.Census.orderOf_cSqrt]⟩)
    (le_normalizer hbC) fun hbc => hbz (mem_zpowers_of_mem_centralizer_Cgen hbC hbc)

theorem centDer_xmat :
    centDer Gmat xmat = Hmat := by
  rw [centDer, Gmat_inf_centralizer_xmat]
  have := (Hmat_perfect_and_inner_of_Co1_inner (Sporadic.Co1Schreier.full_automorphisms_inner_of_inputs
      Sporadic.Co2Schreier.CTUC_Co2_full_automorphisms_inner)).1
  exact Subgroup.commutator_eq_self

theorem invariant_le_or_eq_Qmat {M : Subgroup (SpaceB ≃ₗ[ℚ] SpaceB)} (hMQ : M ≤ Qmat)
    (hM : ∀ p ∈ Hmat, ∀ y ∈ M, p * y * p⁻¹ ∈ M) : M ≤ zpowers xmat ∨ M = Qmat := by
  have hxc : ∀ p ∈ Hmat, p * xmat = xmat * p := fun p hp => by
    rw [← Gmat_inf_centralizer_xmat] at hp
    exact mem_centralizer_singleton_iff.mp hp.2
  have hZ : ∀ z ∈ zpowers xmat, ∀ p ∈ Hmat, z * p = p * z := fun z hz p hp =>
    commute_of_mem_zpowers (hxc p hp) hz
  have hx2 : xmat ^ 2 = 1 := by rw [← orderOf_xmat]; exact pow_orderOf_eq_one xmat
  set R := M ⊔ zpowers xmat with hRdef
  have hR : ∀ f ∈ Hmat, ∀ r ∈ R, f * r * f⁻¹ ∈ R := by
    intro f hf r hr
    have hle : R ≤ R.comap (MulAut.conj f).toMonoidHom := by
      refine sup_le (fun y hy => ?_) (fun z hz => ?_)
      · exact le_sup_left (a := M) (hM f hf y hy)
      · show f * z * f⁻¹ ∈ R
        rw [← hZ z hz f hf, mul_inv_cancel_right]
        exact le_sup_right (b := zpowers xmat) hz
    exact hle hr
  have hRQ : R ≤ Qmat := sup_le hMQ (zpowers_le.mpr xmat_mem_Qmat)
  rcases irreducible_Qmat visible_quotient_irreducible_action.1 R hR le_sup_right hRQ with h | h
  · left
    exact le_sup_left.trans h.le
  · right
    refine le_antisymm hMQ ?_
    have hxM : xmat ∈ M := by
      by_contra hxM
      have hMc : M ≤ centralizer (M : Set _) := by
        intro m₁ hm₁
        rw [mem_centralizer_iff]
        intro m₂ hm₂
        have hc := comm_Qmat m₂ (hMQ hm₂) m₁ (hMQ hm₁)
        have hcM : m₂ * m₁ * m₂⁻¹ * m₁⁻¹ ∈ M :=
          M.mul_mem (M.mul_mem (M.mul_mem hm₂ hm₁) (inv_mem hm₂)) (inv_mem hm₁)
        rcases eq_one_or_eq_of_mem_zpowers hx2 hc with h1 | h1
        · calc m₂ * m₁ = (m₂ * m₁ * m₂⁻¹ * m₁⁻¹) * (m₁ * m₂) := by group
            _ = m₁ * m₂ := by rw [h1, one_mul]
        · exact absurd (h1 ▸ hcM) hxM
      have hZc : zpowers xmat ≤ centralizer (M : Set _) := fun z hz => by
        rw [mem_centralizer_iff]
        intro m hm
        exact (hZ z hz m (Qmat_le_Hmat (hMQ hm))).symm
      have hZZ : zpowers xmat ≤ centralizer (zpowers xmat : Set _) := fun z hz => by
        rw [mem_centralizer_iff]
        intro w hw
        obtain ⟨a, rfl⟩ := mem_zpowers_iff.mp hz
        obtain ⟨c, rfl⟩ := mem_zpowers_iff.mp hw
        rw [← zpow_add, ← zpow_add, add_comm]
      have h1 : R ≤ centralizer (M : Set _) := sup_le hMc hZc
      have h2 : R ≤ centralizer (zpowers xmat : Set _) :=
        sup_le (le_centralizer_iff.mp hZc) hZZ
      have h3 : R ≤ centralizer (R : Set _) :=
        le_centralizer_iff.mpr (sup_le (le_centralizer_iff.mp h1) (le_centralizer_iff.mp h2))
      obtain ⟨q, hq, hqz⟩ := exists_Qmat_not_mem_zpowers
      apply hqz
      rw [← center_Qmat q hq]
      intro y hy
      have hyR : y ∈ R := by rw [h]; exact hy
      have hqR : q ∈ R := by rw [h]; exact hq
      exact (mem_centralizer_iff.mp (h3 hqR)) y hyR
    have hRM : R ≤ M := sup_le le_rfl (zpowers_le.mpr hxM)
    rw [← h]
    exact hRM

theorem natCard_Qmat : Nat.card Qmat = 2 ^ 25 := by
  rw [← natCard_rhoQvis]
  exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe rhoQ_le_Gvis).toEquiv).symm

theorem exists_four_dvd_orderOf_Qmat : ∃ y ∈ Qmat, 4 ∣ orderOf y := by
  by_contra hcon
  push Not at hcon
  have hsq : ∀ y ∈ Qmat, y ^ 2 = 1 := by
    intro y hy
    have hd : orderOf y ∣ 2 ^ 25 := by
      rw [← natCard_Qmat]
      exact Qmat.orderOf_dvd_natCard hy
    obtain ⟨m, hm, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
    have hm1 : m ≤ 1 := by
      by_contra hm2
      apply hcon y hy
      rw [he]
      exact (pow_dvd_pow 2 (by omega : 2 ≤ m) : 2 ^ 2 ∣ 2 ^ m)
    rw [← orderOf_dvd_iff_pow_eq_one, he]
    exact pow_dvd_pow 2 hm1
  obtain ⟨q, hq, hqz⟩ := exists_Qmat_not_mem_zpowers
  apply hqz
  rw [← center_Qmat q hq]
  intro x hx
  exact RankTwoSporadic.commute_of_sq_eq_one hsq hx hq

theorem yWitness_xmat
    {E : Subgroup (SpaceB ≃ₗ[ℚ] SpaceB)} (hEG : E ≤ Gmat) (hE : IsElemAbelian 2 E)
    (hE4 : 4 ≤ Nat.card E) (hx : xmat ∈ E) : YWitness Gmat E := by
  obtain ⟨b, hbE, hbz⟩ := exists_not_mem_zpowers_of_isElemAbelian hE4
    (by rw [← orderOf_xmat]; exact pow_orderOf_eq_one xmat)
  have hbx : b * xmat = xmat * b :=
    congrArg Subtype.val (hE.1.is_comm.comm ⟨b, hbE⟩ ⟨xmat, hx⟩)
  have hbH : b ∈ Hmat := by
    rw [← Gmat_inf_centralizer_xmat]
    exact ⟨hEG hbE, mem_centralizer_singleton_iff.mpr hbx⟩
  have hx1 : xmat ≠ 1 := fun h => by
    have := orderOf_xmat
    rw [h, orderOf_one] at this
    exact absurd this (by norm_num)
  have hxc : ∀ p ∈ Hmat, p * xmat = xmat * p := fun p hp => by
    rw [← Gmat_inf_centralizer_xmat] at hp
    exact mem_centralizer_singleton_iff.mp hp.2
  have hQn : ∀ p ∈ Hmat, ∀ q ∈ Qmat, p * q * p⁻¹ ∈ Qmat := by
    intro p hp q hq
    have h := (normal_Qmat_subgroupOf_Hmat).conj_mem ⟨q, Qmat_le_Hmat hq⟩
      (by rw [mem_subgroupOf]; exact hq) ⟨p, hp⟩
    rwa [mem_subgroupOf] at h
  have h4 : FourProp Hmat :=
    fourProp_of_constrained (Z := zpowers xmat) Qmat_le_Hmat hQn
      (fun z hz p hp => commute_of_mem_zpowers (hxc p hp) hz)
      (fun M hMQ hM => invariant_le_or_eq_Qmat hMQ hM)
      (fun f hf hc => faithful_Hmat f hf fun y hy => by
        have := hc y hy
        rwa [commutatorElement_def] at this)
      exists_four_dvd_orderOf_Qmat
  have hperf : ⁅Hmat, Hmat⁆ = Hmat := by
    have := (Hmat_perfect_and_inner_of_Co1_inner (Sporadic.Co1Schreier.full_automorphisms_inner_of_inputs
        Sporadic.Co2Schreier.CTUC_Co2_full_automorphisms_inner)).1
    exact Subgroup.commutator_eq_self
  refine yWitness_of_perfect hx hx1 hbE (P := Hmat) centDer_xmat.ge hperf h4 (le_normalizer hbH)
    fun hbc => hbz ?_
  rw [← generated_group_Co1_local_recognition_hypotheses.2.2.2.2.2.2.2.2.2.2.1]
  exact ⟨hEG hbE, fun q hq => (mem_centralizer_iff.mp hbc) q (Qmat_le_Hmat hq)⟩

theorem yCensus_Gmat :
    YCensus (⊤ : Subgroup ↥Gmat) (fun _ => False) := by
  refine yCensus_of_classes (X := ⊤) inferInstance (fun t₀ => t₀ = xGmat ∨ t₀ = tGmat)
    (fun E hE hE4 => ?_) ?_
  · obtain ⟨t, htE, ht2⟩ := exists_orderOf_eq_two_of_isElemAbelian hE hE4
    rcases Census.generated_group_two_involution_classes t ht2 with h | h
    · exact ⟨t, htE, xGmat, Or.inl rfl, h⟩
    · exact ⟨t, htE, tGmat, Or.inr rfl, h⟩
  · rintro t₀ ht₀ E hE hE4 ht
    have hEG : E.map Gmat.subtype ≤ Gmat := by
      rintro _ ⟨y, -, rfl⟩
      exact y.2
    have hE' := isElemAbelian_map hE Gmat.subtype
    have hE4' : 4 ≤ Nat.card (E.map Gmat.subtype) := by
      rwa [card_map_of_injective Gmat.subtype_injective]
    rw [← yWitness_map_iff Gmat.subtype Gmat.subtype_injective, ← MonoidHom.range_eq_map,
      range_subtype]
    rcases ht₀ with rfl | rfl
    · exact yWitness_xmat hEG hE' hE4' ⟨_, ht, rfl⟩
    · exact yWitness_tStar hEG hE' hE4' ⟨_, ht, rfl⟩

theorem center_Gmat :
    center ↥Gmat = ⊥ := by
  obtain ⟨-, hs, ⟨g, h, hgh⟩, -⟩ := generated_group_Co1_local_recognition_hypotheses
  have := hs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center ↥Gmat) with hc | hc
  · exact hc
  · exact absurd (mem_center_iff.mp (hc ▸ mem_top g) h).symm hgh

theorem autModel_Gmat :
    AutModel ↥Gmat ↥Gmat ⊤ :=
  autModel_top center_Gmat CFSG.RankThree.PartOne.SPOR.allInner_Gmat

theorem sporadicCaseOdd_M
    (h32 : AS76b.Lemma32) (h33 : AS76b.Lemma33Three) : SporadicCaseOdd .M :=
  sporadicCaseOdd_of_yCensus_of_simple h32 h33 autModel_Gmat yCensus_Gmat
    fun _ _ hQ e => by
      have := hQ
      exact CFSG.RankThree.PartOne.SPOR.mulEquiv_Gmat_of_simple e

end CFSG.ComponentClassification.RankTwoSporadic.Monster
