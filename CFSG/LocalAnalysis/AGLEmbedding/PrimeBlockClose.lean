module

public import CFSG.LocalAnalysis.AGLEmbedding.PrimeBlockGlue
public import CFSG.LocalAnalysis.AGLEmbedding.PrimeBlockTypes
import CFSG.LocalAnalysis.AGLEmbedding.BlockInnerNormalizer
import CFSG.LocalAnalysis.AGLEmbedding.GapROneBSAux
import CFSG.LocalAnalysis.AGLEmbedding.ResidualFiveOddCore

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbeddingD2 (NoXBlockFor)

section Close

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}

theorem TwoLocalPhaseThree.coprime_card_barM_normalizer_inf (h : TwoLocalPhaseThree M H)
    (hK : Open.IsKGroup ↥M) (h85 : Asc81bEightFive) (h93 : Asc81bNineThree) (hD2 : NoXBlockFor G)
    (hKP : KFactParabolicPrime) (hC3 : CitedBlockTransvectionPrime) (hK5 : KFactBlockAltSevenPrime)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L) {q : ℕ} (hq : q.Prime) (hq5 : 5 ≤ q)
    (hPq : ∀ V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M),
      V ≤ barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L) → ⁅V, V⁆ = V →
        q.Coprime (Nat.card V)) :
    q.Coprime (Nat.card (barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L))) := by
  have hn1 := h.nineThree_not_one hK h85 hD2 hL
  have hnS : ¬ IsSylowTwoOf (pCoreOf 2 H ⊓ L) L := h.not_isSylowTwoOf_inf hK h85 hD2 hL
  rcases h.nineThree hK h93 hL with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  · exact absurd h1 hn1.1
  · exact coprime_card_of_nineThreeTwo hKP hL.component h2 (hn1.2 h2) hq hq5 hPq
  · exact hC3 G M (pCoreOf 2 H) L q hK h.asc81bHyp hL hn1.1 hnS h3 hq hq5 hPq
  · exact coprime_card_of_nineThreeFour hq hq5 h4
  · exact hK5 G M (pCoreOf 2 H) L q hK h.asc81bHyp hL hn1.1 hnS h5 hq hq5 hPq
  · exact coprime_card_of_nineThreeSix hq hq5 hPq (Or.inl h6)
  · exact coprime_card_of_nineThreeSix hq hq5 hPq (Or.inr h7)
  · exact coprime_card_of_nineThreeEight hq hq5 hPq h8

theorem D1PhaseThree.coprime_card_barM_normalizer_inf (h : D1PhaseThree p P M H R)
    (h85 : Asc81bEightFive) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hKP : KFactParabolicPrime) (hC3 : CitedBlockTransvectionPrime)
    (hK5 : KFactBlockAltSevenPrime) {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    {q : ℕ} (hq : q.Prime) (hq5 : 5 ≤ q)
    (hPq : ∀ V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M),
      V ≤ barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L) → ⁅V, V⁆ = V →
        q.Coprime (Nat.card V)) :
    q.Coprime (Nat.card (barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L))) :=
  h.toTwoLocalPhaseThree.coprime_card_barM_normalizer_inf h.isKGroup.1 h85 h93 (hD2 G h.glob) hKP
    hC3 hK5 hL hq hq5 hPq

theorem TwoLocalPhaseThree.twoGenInner_hyp (h : TwoLocalPhaseThree M H) (hK : Open.IsKGroup ↥M)
    (h85 : Asc81bEightFive) (h93 : Asc81bNineThree) (hD2 : NoXBlockFor G) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) {q : ℕ}
    (hP : q.Coprime (Nat.card (barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L)))) :
    ¬ q ∣ Nat.card (barM M L) ∨ IsOrthogonalTwo ↥(barM M L) ∨
      (∃ m : ℕ, Nonempty (↥(barM M L) ≃* alternatingGroup (Fin m)) ∨
        Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* alternatingGroup (Fin m))) ∨
      (IsClassicalTwoOrG2 (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) ∧
        ∃ T : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), IsSylowTwoOf T (barM M L) ∧
          q.Coprime (Nat.card ↥(barM M L ⊓ Subgroup.normalizer (T : Set _)))) := by
  have hn1 := h.nineThree_not_one hK h85 hD2 hL
  rcases h.nineThree hK h93 hL with h1 | ⟨hcl, ⟨-, T, hT, hNT⟩, -⟩ | h3 | h4 | h5 | h6 | h7 | h8
  · exact absurd h1 hn1.1
  · exact Or.inr (Or.inr (Or.inr ⟨hcl, T, hT,
      Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hNT) hP⟩))
  · exact Or.inr (Or.inl h3.2.1)
  · exact Or.inr (Or.inr (Or.inl ⟨6, Or.inr h4.2.2.1⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨7, Or.inl h5.2.1⟩))
  · obtain ⟨-, n, he, -⟩ := h6
    exact Or.inr (Or.inr (Or.inl ⟨2 * n, Or.inr he⟩))
  · obtain ⟨-, n, he, -⟩ := h7
    exact Or.inr (Or.inr (Or.inl ⟨4 * n, Or.inl he⟩))
  · obtain ⟨-, N, r, -, -, -, -, -, he, -⟩ := h8
    exact Or.inr (Or.inr (Or.inl ⟨N, Or.inl he⟩))

theorem D1PhaseThree.twoGenInner_hyp (h : D1PhaseThree p P M H R) (h85 : Asc81bEightFive)
    (h93 : Asc81bNineThree) (hD2 : D1NoXBlock) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) {q : ℕ}
    (hP : q.Coprime (Nat.card (barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L)))) :
    ¬ q ∣ Nat.card (barM M L) ∨ IsOrthogonalTwo ↥(barM M L) ∨
      (∃ m : ℕ, Nonempty (↥(barM M L) ≃* alternatingGroup (Fin m)) ∨
        Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* alternatingGroup (Fin m))) ∨
      (IsClassicalTwoOrG2 (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) ∧
        ∃ T : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), IsSylowTwoOf T (barM M L) ∧
          q.Coprime (Nat.card ↥(barM M L ⊓ Subgroup.normalizer (T : Set _)))) :=
  h.toTwoLocalPhaseThree.twoGenInner_hyp h.isKGroup.1 h85 h93 (hD2 G h.glob) hL hP

omit [Finite G] in
theorem barM_zpowers_le_iff {M : Subgroup G} {z : G} (hzM : z ∈ M)
    {C : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} :
    barM M (Subgroup.zpowers z) ≤ C ↔ QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzM⟩ ∈ C := by
  constructor
  · intro hle
    exact hle ⟨⟨z, hzM⟩, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers z), rfl⟩
  · intro hx
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (Subgroup.mem_subgroupOf.mp hy)
    have hy' : y = ⟨z, hzM⟩ ^ n := Subtype.ext (by rw [← hn]; simp)
    rw [hy', map_zpow]
    exact C.zpow_mem hx n

theorem D1PhaseThree.le_centralizer_of_mem_nclIn (h : D1PhaseThree p P M H R)
    (h84 : Asc81bEightFour) (h85 : Asc81bEightFive) (h86 : Asc81bEightSix)
    (h93 : Asc81bNineThree) (hD2 : D1NoXBlock) (hKin : KFactTwoGenInner)
    (hKP : KFactParabolicPrime) (hC3 : CitedBlockTransvectionPrime)
    (hK5 : KFactBlockAltSevenPrime) {q : ℕ} (hq : q.Prime) (hq5 : 5 ≤ q) {z : G}
    (hzT : z ∈ nclIn M (pCoreOf 2 H)) (hzS : z ∈ Subgroup.normalizer (pCoreOf 2 H : Set G))
    {k : ℕ} (hzq : z ^ q ^ k = 1) {L : Subgroup G} (hL : IsTwoPrimeComponent M L)
    (hPq : ∀ V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M),
      V ≤ barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L) → ⁅V, V⁆ = V →
        q.Coprime (Nat.card V)) :
    barM M (Subgroup.zpowers z) ≤
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  set S := pCoreOf 2 H
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M)
  set Lb := barM M L
  have hzM : z ∈ M := nclIn_le_self M S hzT
  set x := mk ⟨z, hzM⟩
  rw [barM_zpowers_le_iff hzM]
  change x ∈ Subgroup.centralizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M))
  have hxT : x ∈ barM M (nclIn M S) :=
    ⟨⟨z, hzM⟩, Subgroup.mem_subgroupOf.mpr hzT, rfl⟩
  have hx2 : x ∈ Subgroup.closure
      {a | a ∈ Subgroup.normalizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∧ ∃ k : ℕ, a ^ 2 ^ k = 1} :=
    normalClosure_twoElems_le Lb hL.component (h.barM_nclIn_le_normalClosure h86 hxT)
  have hxq : x ^ q ^ k = 1 := by
    have : (⟨z, hzM⟩ : M) ^ q ^ k = 1 := Subtype.ext (by simpa using hzq)
    rw [← map_pow, this, map_one]
  have hxS : x ∈ Subgroup.normalizer (barM M S : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    mem_normalizer_barM hzM hzS
  have hMtop : M ≠ ⊤ := fun hM => h.not_le (hM ▸ le_top)
  have hcat : IsCatalogGroup (↥Lb ⧸ Subgroup.center ↥Lb) :=
    ((catalogSimpleSections_of_isKProper h.glob.kProper M hMtop).quotient
      _).isCatalogGroup_center_quotient hL.component
  by_cases hLS : L ≤ Subgroup.normalizer (S : Set G)
  ·
    have hPL : barM M (Subgroup.normalizer (S : Set G) ⊓ L) = Lb := by
      rw [inf_eq_right.mpr hLS]
    have hLp : ⁅Lb, Lb⁆ = Lb := by
      rw [show Lb = barM M L from rfl, barM, ← Subgroup.map_commutator]
      congr 1
      apply Subgroup.map_injective M.subtype_injective
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hL.le, hL.perfect]
    have hLq : q.Coprime (Nat.card Lb) := hPq Lb hPL.ge hLp
    have hin := hKin _ Lb hL.component hcat q hq hq5
      (Or.inl ((Nat.Prime.coprime_iff_not_dvd hq).mp hLq)) x hx2 ⟨k, hxq⟩
    have hLC : Lb ≤ Subgroup.normalizer
        ((Subgroup.centralizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M))) : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
      Subgroup.le_normalizer.trans
        ((Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).mp
          (Subgroup.normal_subgroupOf_centralizer_normalizer _))
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hLC] at hin
    obtain ⟨l, hl, c, hc, hlc⟩ := hin
    rw [← hlc] at hxq ⊢
    exact mul_mem_centralizer_of_coprime hl le_rfl hc hLq hxq
  ·
    have hW : IsWeakSBlock M S L := ⟨hL, hLS⟩
    have hP := h.coprime_card_barM_normalizer_inf h85 h93 hD2 hKP hC3 hK5 hW hq hq5 hPq
    have hin := hKin _ Lb hL.component hcat q hq hq5 (h.twoGenInner_hyp h85 h93 hD2 hW hP) x hx2
      ⟨k, hxq⟩
    exact h.mem_centralizer_of_mem_sup h84 h86 hD2 hW hP hin hxS hxq

theorem D1PhaseThree.exists_component_of_not_mem (h : D1PhaseThree p P M H R)
    (h84 : Asc81bEightFour) (h85 : Asc81bEightFive) (h86 : Asc81bEightSix)
    (h93 : Asc81bNineThree) (hD2 : D1NoXBlock) (hKin : KFactTwoGenInner)
    (hKP : KFactParabolicPrime) (hC3 : CitedBlockTransvectionPrime)
    (hK5 : KFactBlockAltSevenPrime) (hp5 : 5 ≤ p) {z : G}
    (hzT : z ∈ nclIn M (pCoreOf 2 H)) (hzS : z ∈ Subgroup.normalizer (pCoreOf 2 H : Set G))
    {k : ℕ} (hzp : z ^ p ^ k = 1) (hzY : z ∉ pCorePreimage p M) :
    ∃ L : Subgroup G, IsTwoPrimeComponent M L ∧
      ¬ barM M (Subgroup.zpowers z) ≤
        Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∧
      ∃ V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M),
        V ≤ barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L) ∧ ⁅V, V⁆ = V ∧
          p ∣ Nat.card V := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  by_contra hno
  push Not at hno
  apply hzY
  have hzM : z ∈ M := nclIn_le_self M (pCoreOf 2 H) hzT
  set A := barM M (Subgroup.zpowers z)
  have hA : IsPGroup p A := by
    have h1 : IsPGroup p (Subgroup.zpowers z) := by
      rintro ⟨x, hx⟩
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      refine ⟨k, Subtype.ext ?_⟩
      change (z ^ n) ^ p ^ k = 1
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hzp, one_zpow]
    exact (h1.comap_subtype).map _
  have hcomp : ∀ Lb : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), IsComponentOf Lb ⊤ →
      A ≤ Subgroup.centralizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    intro Lb hLb
    obtain ⟨L, hL, rfl⟩ := exists_isTwoPrimeComponent hLb
    by_contra hnc
    refine h.le_centralizer_of_mem_nclIn h84 h85 h86 h93 hD2 hKin hKP hC3 hK5 hp hp5 hzT hzS hzp
      hL (fun V hV hVp => ?_) |> hnc
    exact (Nat.Prime.coprime_iff_not_dvd hp).mpr (hno L hL hnc V hV hVp)
  have hcore : ∀ l : ℕ, l.Prime →
      A ≤ Subgroup.centralizer
        (CFSG.pCore l (↥M ⧸ CFSG.pCore 2 ↥M) : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    intro l hl
    by_cases hl2 : l = 2
    · rw [hl2, pCore_quotient_pCore_eq_bot']
      exact Subgroup.le_centralizer_iff.mp bot_le
    · refine le_trans ?_ (Subgroup.centralizer_le (pCore_le_pPrimeCore_two hl hl2))
      exact (barM_mono (Subgroup.zpowers_le.mpr hzT)).trans
        (h.barM_nclIn_le_centralizer_oddCore h84 hD2)
  have hle := le_pCore_of_le_centralizer_components hA hcomp hcore
  exact ⟨⟨z, hzM⟩, hle ⟨⟨z, hzM⟩, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers z), rfl⟩, rfl⟩

end Close

end CFSG.AGLEmbedding
