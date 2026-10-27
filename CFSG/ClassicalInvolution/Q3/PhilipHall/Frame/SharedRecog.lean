module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Exits
public import CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge.SharedTarget
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FStarBasic
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TightFamily
import CFSG.Models.Transport

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.Q3T.MFS

section Transport

theorem lieModel_psp_three_two_of_mulEquiv {G G' : Type} [Group G] [Group G'] (e : G ≃* G')
    (h : Models.LieModel G .PSp 3 2 1) : Models.LieModel G' .PSp 3 2 1 :=
  CFSG.Models.LieModel.of_mulEquiv e h

theorem lieModel_pomegaPlus_four_two_of_mulEquiv {G G' : Type} [Group G] [Group G']
    (e : G ≃* G') (h : Models.LieModel G .POmegaPlus 4 2 1) :
    Models.LieModel G' .POmegaPlus 4 2 1 :=
  CFSG.Models.LieModel.of_mulEquiv e h

theorem genFittingFStar_eq_top_of_simple {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (hnab : ∃ a b : X, a * b ≠ b * a) : genFittingFStar X = ⊤ := by
  have : IsSimpleGroup ↥(⊤ : Subgroup X) := (Subgroup.topEquiv (G := X)).isSimpleGroup
  have hnab' : ∃ a b : ↥(⊤ : Subgroup X), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    exact ⟨⟨a, trivial⟩, ⟨b, trivial⟩, fun h => hab (congrArg Subtype.val h)⟩
  have hC : Subgroup.centralizer ((⊤ : Subgroup X) : Set X) = ⊥ := by
    rw [Subgroup.coe_top, Subgroup.centralizer_univ]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      have ha : a ∈ Subgroup.center X := by rw [h]; exact Subgroup.mem_top a
      exact hab (Subgroup.mem_center_iff.mp ha b).symm
  exact genFittingFStar_eq_of_normal_simple ⊤ hnab' hC

@[expose] def ExSpD4 (Y : Type) [Group Y] [Finite Y] : Prop :=
  Models.LieModel ↥(genFittingFStar Y) .PSp 3 2 1 ∨
    Models.LieModel ↥(genFittingFStar Y) .POmegaPlus 4 2 1

end Transport

section Targets

@[expose] def Q8TwinRecogLarge : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsSimpleGroup ↥(genFittingFStar Y) →
    (∃ a b : ↥(genFittingFStar Y), a * b ≠ b * a) → CIT3Below (Nat.card Y) →
    TightBelow (Nat.card Y) → ¬ TwoSubgroupsFourGenerated ↥(genFittingFStar Y) →
    ∀ (R : Subgroup Y) (S : Sylow 2 R) (t : Y), QuaternionBridge.Q8TwinDatum R S t →
      Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup 2) → TightSelfGen R →
      HypOmegaGen (CoreAssembly.conjClass (tightCore R)) →
      AEmpty (CoreAssembly.conjClass (tightCore R)) (tightCore R) →
      IsSubnormal (tightCore R) (Subgroup.centralizer ({t} : Set Y)) →
      (∃ K' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R),
        K' ≠ tightCore R) → TightHasLift R t ∨ ExSpD4 Y

theorem q8TwinRecogLarge_of_recogEx (h : QuaternionBridge.Q8TwinRecogEx ExSpD4) :
    Q8TwinRecogLarge :=
  fun Y _ _ hF hnab hB hTB _ R S t hd hq hg hΩ hA hs htw =>
    h Y hF hnab hB hTB R S t hd hq hg hΩ hA hs htw

@[expose] def FrameAEmpty : Prop :=
  ∀ (T : Type) [Group T] [Finite T] [IsSimpleGroup T], (∃ a b : T, a * b ≠ b * a) →
    CIT3Below (Nat.card T) → TightBelow (Nat.card T) → ¬ TwoSubgroupsFourGenerated T →
    ∀ (R : Subgroup T) (t : T), FrameTightDatum R t → AEmpty (CoreAssembly.conjClass R) R

@[expose] def FStarTwinMemberFreeLargeTB : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] [IsSimpleGroup (genFittingFStar Y)],
    (∃ a b : genFittingFStar Y, a * b ≠ b * a) → CIT3Below (Nat.card Y) →
    TightBelow (Nat.card Y) →
    ∀ (Ω : Set (Subgroup Y)) (K : Subgroup Y), HypOmegaModU (.sl2 3 1) Ω → K ∈ Ω →
      (∀ J ∈ Ω, ∃ g : Y, conjSub g K = J) → (⨆ J ∈ Ω, J) = ⊤ →
      (∃ K' ∈ twinSet Ω K, K' ≠ K) → genFittingFStar Y ⊔ K = ⊤ →
      (∀ (z' : genFittingFStar Y) (L' : Subgroup (genFittingFStar Y)),
        ¬ IsClassicalMember3 L' z') →
      memberIndex K (genFittingFStar Y) = 3 →
      ¬ TwoSubgroupsFourGenerated (genFittingFStar Y) → False

end Targets

section Datum

variable {T : Type} [Group T] [Finite T]

theorem mem_of_isUniqueInvolution_of_quat {R P : Subgroup T} {t : T}
    (hu : IsUniqueInvolution R t) (hPR : P ≤ R) (hP : Nonempty (↥P ≃* QuaternionGroup 2)) :
    t ∈ P := by
  obtain ⟨e⟩ := hP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card ↥P = 8 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥P) 2 (by rw [hcard]; norm_num)
  have hx2 : (x : T) * (x : T) = 1 := by
    have h1 : x ^ 2 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
    have h2 : ((x ^ 2 : ↥P) : T) = 1 := by rw [h1]; rfl
    simpa [pow_two] using h2
  have hx1 : (x : T) ≠ 1 := by
    intro h1
    have : x = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hx
    exact absurd hx (by norm_num)
  rcases hu.unique (x : T) (hPR x.2) hx2 with h | h
  · exact absurd h hx1
  · exact h ▸ x.2

theorem le_centralizer_of_isUniqueInvolution {R : Subgroup T} {t : T}
    (hu : IsUniqueInvolution R t) : R ≤ Subgroup.centralizer ({t} : Set T) := by
  intro k hk
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hmem : k * t * k⁻¹ ∈ R := R.mul_mem (R.mul_mem hk hu.mem) (R.inv_mem hk)
  have hsq : k * t * k⁻¹ * (k * t * k⁻¹) = 1 := by
    calc k * t * k⁻¹ * (k * t * k⁻¹) = k * (t * t) * k⁻¹ := by group
      _ = 1 := by rw [hu.sq]; group
  rcases hu.unique _ hmem hsq with h | h
  · exfalso
    apply hu.ne_one
    calc t = k⁻¹ * (k * t * k⁻¹) * k := by group
      _ = 1 := by rw [h]; group
  · calc k * t = k * t * k⁻¹ * k := by group
      _ = t * k := by rw [h]

theorem FrameTightDatum.q8TwinDatum {R : Subgroup T} {t : T} (hD : FrameTightDatum R t)
    (S : Sylow 2 R) :
    QuaternionBridge.Q8TwinDatum R S t ∧ Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup 2) := by
  have hPsyl : IsSylow2In ((S : Subgroup R).map R.subtype) R := Asc77.isSylow2In_map_subtype R S
  obtain ⟨e⟩ := hD.quat _ hPsyl
  have hq : Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup 2) :=
    ⟨(Subgroup.equivMapOfInjective (S : Subgroup R) R.subtype R.subtype_injective).trans e⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨⟨⟨3, le_rfl, hq⟩, mem_of_isUniqueInvolution_of_quat hD.unique hPsyl.1 ⟨e⟩,
    orderOf_eq_prime (by rw [pow_two]; exact hD.unique.sq) hD.unique.ne_one,
    le_centralizer_of_isUniqueInvolution hD.unique, hD.twoGroup⟩, hq⟩

end Datum

section Reduction

theorem fStarTwinMemberFreeLargeTB_of_recog (h : Q8TwinRecogLarge) (hA : FrameAEmpty)
    (hD4 : FrameExitD42) : FStarTwinMemberFreeLargeTB := by
  intro Y _ _ _ hnab hBelow hTB Ω K hΩ hK htrans hgen htwin hsup hfree h3 hlarge
  set T : Subgroup Y := genFittingFStar Y with hTdef
  have hTn : T.Normal := fstar_normal
  obtain ⟨hodd, h3T⟩ := odd_index_of_memberIndex_eq_three hsup h3
  obtain ⟨z, hz⟩ := hΩ.classical K hK
  have hD := frameTightDatum_of_frame hodd hΩ hK htrans hsup htwin hz
  have hTY : T ≠ ⊤ := by
    intro htop
    have : T.index = 1 := by rw [htop, Subgroup.index_top]
    rw [this] at h3T
    norm_num at h3T
  have hcard : Nat.card T < Nat.card Y := by
    rw [← Subgroup.card_top (G := Y)]
    exact Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hTY)
  have hBT : CIT3Below (Nat.card T) := CIT3Below.mono hcard.le hBelow
  have hTBT : TightBelow (Nat.card T) := QuaternionBridge.tightBelow_mono hcard.le hTB
  have hF0 : genFittingFStar ↥T = ⊤ := genFittingFStar_eq_top_of_simple hnab
  have hF : IsSimpleGroup ↥(genFittingFStar ↥T) := by
    rw [hF0]
    exact (Subgroup.topEquiv (G := ↥T)).isSimpleGroup
  have hnabF : ∃ a b : ↥(genFittingFStar ↥T), a * b ≠ b * a := by
    rw [hF0]
    obtain ⟨a, b, hab⟩ := hnab
    exact ⟨⟨a, trivial⟩, ⟨b, trivial⟩, fun h => hab (congrArg Subtype.val h)⟩
  have hlargeF : ¬ TwoSubgroupsFourGenerated ↥(genFittingFStar ↥T) := by
    rw [hF0]
    intro h4
    exact hlarge (twoSubgroupsFourGenerated_of_mulEquiv (Subgroup.topEquiv (G := ↥T)) h4)
  set R : Subgroup ↥T := (tightCore K).subgroupOf T with hR
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S⟩ : Nonempty (Sylow 2 ↥R) := inferInstance
  obtain ⟨hdat, hq⟩ := hD.q8TwinDatum S
  have hcore := hD.tightCore_eq
  have hAR := hA ↥T hnab hBT hTBT hlarge R _ hD
  have hsg : TightSelfGen R := by
    unfold TightSelfGen
    rw [hcore]
    exact hD.selfGen
  have hΩR : HypOmegaGen (CoreAssembly.conjClass (tightCore R)) := by
    rw [hcore]
    exact hD.hyp
  have hAR' : AEmpty (CoreAssembly.conjClass (tightCore R)) (tightCore R) := by
    rw [hcore]
    exact hAR
  have hsub : IsSubnormal (tightCore R) (Subgroup.centralizer
      ({(⟨z, tightCore_le_of_odd_index hodd K (mem_tightCore_of_member hz)⟩ : ↥T)} : Set ↥T)) := by
    rw [hcore]
    exact hD.subnormal
  have htw : ∃ K' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R),
      K' ≠ tightCore R := by
    rw [hcore]
    exact hD.twin
  rcases h ↥T hF hnabF hBT hTBT hlargeF R S _ hdat hq hsg hΩR hAR' hsub htw with hlift | hex
  · obtain ⟨L, -, hL⟩ := hlift
    exact hfree _ _ hL
  · rcases hex with hsp | hd4
    · rw [hF0] at hsp
      exact hTY (frameExitSp62_proved Y T hTn (centralizer_fstar_eq_bot hnab)
        (lieModel_psp_three_two_of_mulEquiv (Subgroup.topEquiv (G := ↥T)) hsp))
    · rw [hF0] at hd4
      exact hD4 Y hnab hBelow Ω K hΩ hK htrans hgen htwin hsup hfree h3
        (lieModel_pomegaPlus_four_two_of_mulEquiv (Subgroup.topEquiv (G := ↥T)) hd4)

end Reduction

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
