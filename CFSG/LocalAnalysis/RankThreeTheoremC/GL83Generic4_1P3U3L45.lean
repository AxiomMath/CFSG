module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3U3Basics
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3U3L45b
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.InvariantTwoWithin
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.LocalHallConfinement
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3R1L45c
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3R1L45d
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericCaseSetup
import CFSG.LocalAnalysis.RankThreeTheoremC.InvariantTwoConstrained

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G]

theorem u3l45_exists_within_not_le (hS : Setting G) (hU0 : FullCoreLocal G)
    (hK2 : KFactU3TwoSignalizer) (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G} {M : Subgroup G}
    (hM : IsCoreMaxLocal 3 P M) {x : G} (hgen : IsGenericPoint 3 P M x) {J : Subgroup G}
    (hJ : IsU3Normal M x J) (hxJ : x ∉ J) {U : Subgroup G} (hU : IsElemAbelian 3 U)
    (hUc : Nat.card U = 3 ^ 2) (hUP : U ≤ (P : Subgroup G)) (hxU : x ∈ U) (hUJ : U ⊓ J ≠ ⊥)
    (hUZ : ∀ u ∈ U ⊓ J, ∀ t ∈ (P : Subgroup G) ⊓ J, u * t = t * u) :
    ∃ A : Subgroup G, invariantTwoMaximalWithin U J A ∧ ¬ A ≤ M := by
  by_contra hno
  push Not at hno
  have hprime : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hprime⟩
  obtain ⟨hxP, ⟨-, hx1, hx3, -, -⟩, hsyl, hrk⟩ := hgen
  have hxo : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hall : ∀ S : Subgroup G, S ≤ J → IsPGroup 2 S → U ≤ normalizer (S : Set G) → S ≤ M := by
    intro S hSJ hS2 hUS
    obtain ⟨S₁, hSS₁, hS₁⟩ := exists_invariantTwoMaximalWithin_containing U J S hSJ hS2 hUS
    exact hSS₁.trans (hno S₁ hS₁)
  have hJC : J ≤ centralizer ({x} : Set G) := hJ.le_centralizer
  have hxJc : ∀ j ∈ J, x * j = j * x := fun j hj =>
    (mem_centralizer_singleton_iff.mp (hJC hj)).symm
  have hUN : U ≤ normalizer (J : Set G) := fun g hg =>
    hJ.centralizer_le (mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hU.1.is_comm.comm ⟨g, hg⟩ ⟨x, hxU⟩)))
  obtain ⟨⟨u, hu⟩, hu1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hUJ
  have hu1' : u ≠ 1 := fun h => hu1 (Subtype.ext h)
  have huU : u ∈ U := hu.1
  have huJ : u ∈ J := hu.2
  have huo : orderOf u = 3 := orderOf_eq_prime (hU.2 u huU) hu1'
  obtain ⟨Qt, instQ, ψ, hψ, hker, hQt⟩ := hJ.iso
  set O : Subgroup ↥J := ψ.ker
  have hOJ : rankThreePrimeCore 3 J ≤ J := CFSG.AGLEmbedding.glbPrimeCore_le 3 J
  have hOcop0 : Nat.Coprime 3 (Nat.card (rankThreePrimeCore 3 J)) :=
    CFSG.AGLEmbedding.glbPrimeCore_coprime 3 J
  have hOcop : Nat.Coprime 3 (Nat.card O) := by
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOJ).toEquiv]
    exact hOcop0
  have hOn : O.Normal := MonoidHom.normal_ker ψ
  have hKt : IsRankThreeU3 (↥J ⧸ O) :=
    isU3_of_mulEquiv (QuotientGroup.quotientKerEquivOfSurjective ψ hψ) hQt
  have hSylJ : IsSylowOf 3 ((P : Subgroup G) ⊓ J) J := by
    have h := hsyl.inf_of_le_normalizer hJC hJ.centralizer_le
    rwa [inf_assoc, inf_eq_right.mpr hJC] at h
  obtain ⟨T, hT⟩ := hSylJ.exists_sylow_eq_subgroupOf
  have hTP : ∀ R : Subgroup ↥J, R ≤ (T : Subgroup ↥J) → R.map J.subtype ≤ (P : Subgroup G) := by
    intro R hR
    refine (Subgroup.map_mono (hR.trans hT.le)).trans ?_
    rw [Subgroup.map_subgroupOf_eq_of_le inf_le_right]
    exact inf_le_left
  have huT : (⟨u, huJ⟩ : ↥J) ∈ (T : Subgroup ↥J) := by
    rw [hT]
    exact ⟨hUP huU, huJ⟩
  have huoJ : orderOf (⟨u, huJ⟩ : ↥J) = 3 := by
    rw [Subgroup.orderOf_mk]
    exact huo
  have huZ : ∀ t ∈ (T : Subgroup ↥J), (⟨u, huJ⟩ : ↥J) * t = t * (⟨u, huJ⟩ : ↥J) := by
    intro t ht
    rw [hT] at ht
    exact Subtype.ext (hUZ u hu t ht)
  have hOM : rankThreePrimeCore 3 J ≤ M := by
    have h1 : GLBPrimeCore 3 (centralizer ({x} : Set G)) ≤ M :=
      (glbPrimeCore_le_pPrimeCoreIn 3 _).trans (pPrimeCoreIn_centralizer_le hS hp hM hrk.ge)
    refine le_trans ?_ h1
    exact CFSG.AGLEmbedding.le_glbPrimeCore (hOJ.trans hJC)
      (hJ.centralizer_le.trans
        (CFSG.PreuniquenessRankFour.Helpers.primeCore_normalizer_normalizes 3 hprime J))
      hOcop0
  set A : Subgroup ↥J := M.subgroupOf J
  have hOA : O ≤ A := by
    intro g hg
    rw [hker] at hg
    exact hOM hg
  have hN : ∀ R : Subgroup ↥J, R ≤ (T : Subgroup ↥J) → R ≠ ⊥ → normalizer (R : Set ↥J) ≤ A :=
    fun R hR hR1 n hn =>
      m11l45_normalizer_le hS hU0 hp hM hxP hxo hxJc hxJ (hTP R hR) hR1 hn
  have hxu : x ∉ zpowers u := fun h => hxJ (zpowers_le.mpr huJ h)
  have hUxu : U ≤ zpowers x ⊔ zpowers u := by
    have hcard := CFSG.RankThree.PartOne.Planes.card_sup_zpowers hprime (zpowers u) hx3 hxu
      (fun e he => by
        obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp he
        exact (Commute.zpow_right (hxJc u huJ : Commute x u) m).eq.symm)
    rw [Nat.card_zpowers, huo] at hcard
    have hle : zpowers u ⊔ zpowers x ≤ U :=
      sup_le (zpowers_le.mpr huU) (zpowers_le.mpr hxU)
    have heq : zpowers u ⊔ zpowers x = U :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hUc, hcard]; norm_num)
    rw [sup_comm, heq]
  have hV : ∀ V : Subgroup (↥J ⧸ O), IsPGroup 2 V →
      QuotientGroup.mk' O ⟨u, huJ⟩ ∈ normalizer (V : Set (↥J ⧸ O)) →
        V ≤ A.map (QuotientGroup.mk' O) := by
    intro V hV2 hVu v hv
    obtain ⟨W, hW2, hUW, hWV⟩ := m11l45_exists_invariant_two_lift (J := J) (U := U) (x := x)
      (u := u) (P.isPGroup'.to_le hUP) huJ hUxu hxJc O hOcop V hV2 hVu
    obtain ⟨s, hs, hsW, hsv⟩ := hWV v hv
    have hWM : W ⊓ J ≤ M := hall (W ⊓ J) inf_le_right (hW2.to_le inf_le_left)
      (fun g hg => Subgroup.inf_normalizer_le_normalizer_inf ⟨hUW hg, hUN hg⟩)
    exact ⟨⟨s, hs⟩, Subgroup.mem_subgroupOf.mpr (hWM ⟨hsW, hs⟩), hsv⟩
  have htop : A = ⊤ := u3l45_eq_top hK2 O hOcop hKt T hOA huT huZ huoJ hN hV
  refine hJ.not_le fun g hg => ?_
  have : (⟨g, hg⟩ : ↥J) ∈ A := htop ▸ Subgroup.mem_top _
  exact Subgroup.mem_subgroupOf.mp this

theorem u3_exists_maximal_not_le_of_plane (hS : Setting G) (hU0 : FullCoreLocal G)
    (hK2 : KFactU3TwoSignalizer) (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G} {M : Subgroup G}
    (hM : IsCoreMaxLocal 3 P M) {x : G} (hgen : IsGenericPoint 3 P M x) {J : Subgroup G}
    (hJ : IsU3Normal M x J) (hxJ : x ∉ J) {U : Subgroup G} (hU : IsElemAbelian 3 U)
    (hUc : Nat.card U = 3 ^ 2) (hUP : U ≤ (P : Subgroup G)) (hxU : x ∈ U) (hUJ : U ⊓ J ≠ ⊥)
    (hUZ : ∀ u ∈ U ⊓ J, ∀ t ∈ (P : Subgroup G) ⊓ J, u * t = t * u) :
    ∃ S₁ : Subgroup G, rankTwoMaximalInvariantTwoSubgroup U S₁ ∧ ¬ S₁ ≤ M := by
  obtain ⟨A, hA, hAM⟩ := u3l45_exists_within_not_le hS hU0 hK2 hp hM hgen hJ hxJ hU hUc hUP hxU
    hUJ hUZ
  obtain ⟨S₁, hAS₁, hS₁⟩ := exists_maximal_invariant_two_subgroup_containing U A hA.2.1 hA.2.2.1
  exact ⟨S₁, hS₁, fun h => hAM (hAS₁.trans h)⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
