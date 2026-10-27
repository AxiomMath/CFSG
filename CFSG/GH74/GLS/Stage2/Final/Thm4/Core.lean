module

public import CFSG.GH74.GLS.Stage2.Final.Thm4.Elem
public import CFSG.LocalAnalysis.ComponentInitial.CyclicIndexTwoRank
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.GH74.GLS.Stage2.Final.Thm4.Cover
public import CFSG.GH74.GLS.Stage2.Local.Closed

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm4

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

theorem barIn_self_eq_top {G : Type} [Group G] (H : Subgroup G) : barIn H H = ⊤ := by
  unfold barIn
  rw [Subgroup.subgroupOf_self, Subgroup.map_top, QuotientGroup.range_mk']

theorem pRank_two_le_of_isDihedral {Y : Type} [Group Y] [Finite Y] (h : IsDihedral Y) :
    CFSG.pRank 2 Y ≤ 2 := by
  obtain ⟨m, k, rfl, hk, ⟨e⟩⟩ := h
  have : NeZero k := ⟨by omega⟩
  set R : Subgroup Y := zpowers (e.symm (DihedralGroup.r 1)) with hR
  have hRcard : Nat.card R = k := by
    rw [hR, Nat.card_zpowers, MulEquiv.orderOf_eq, DihedralGroup.orderOf_r_one]
  have hYcard : Nat.card Y = 2 * k := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have hind : R.index ≤ 2 := by
    have h1 := R.index_mul_card
    rw [hRcard, hYcard] at h1
    have hk0 : 0 < k := by omega
    exact (Nat.eq_of_mul_eq_mul_right hk0 (show R.index * k = 2 * k from h1)).le
  exact LocalAnalysis.ComponentInitial.cyclic_index_two_rank_bound (H := R) inferInstance hind

section Ctx

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S M : Subgroup G}

theorem three_le_pRank_S (h : Stage2Ctx G z k S) : 3 ≤ CFSG.pRank 2 ↥S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS := h.sylow_top
  rw [CFSG.ABGLocalTools.isSylowOf_iff] at hS
  obtain ⟨-, hP, hdvd⟩ := hS
  rw [Subgroup.relIndex_top_right] at hdvd
  let P : Sylow 2 G := hP.toSylow hdvd
  have hPS : (P : Subgroup G) = S := rfl
  have := (CFSG.SectionRank.pRank_sylow P).2
  rw [hPS] at this
  rw [this]
  exact h.std.rank.1

theorem not_isDihedral_S (h : Stage2Ctx G z k S) : ¬ IsDihedral ↥S := fun hd =>
  absurd (pRank_two_le_of_isDihedral hd) (by have := three_le_pRank_S h; omega)

theorem Ctx17.cases (h34 : Leaf_Prop34) (h : Ctx17 G z k S M) :
    M = Cen z ∨ ∃ (ε : Bool) (q : ℕ) (L₁ L₂ : Subgroup (CentralizerBar z)), k = Kind.l4 ε ∧
      Stage1L4 G z S ε q L₁ L₂ ∧ 3 < q ∧ IVK.IsPSp4 ↥(generalizedFitting (HBar M)) q ∧
      IsCoatom (barIn M (Cen z)) := by
  have hP34 := h34 G z k S h.ctx M h.cen_le h.ne_top
  rcases hP34 with hc | hd | ⟨ε, q, L₁, L₂, hk, hL4, -, hq3, hF, hcoat, -⟩
  · exact Or.inl (h.eq_of_oddCover hc)
  · exact absurd hd (not_isDihedral_S h.ctx)
  · exact Or.inr ⟨ε, q, L₁, L₂, hk, hL4, hq3, hF, hcoat⟩

end Ctx

theorem hasSL2Model_unique {X : Type} [Group X] {q q' : ℕ} (h : HasSL2Model X (fun r => r = q))
    (h' : HasSL2Model X (fun r => r = q')) : q = q' := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  obtain ⟨F', _, _, hF', ⟨e'⟩⟩ := h'
  have hcard : ∀ (K : Type) [Field K] [Finite K],
      Nat.card (StatedSL 2 K) = Nat.card K * (Nat.card K ^ 2 - 1) := fun K _ _ => by
    rw [← Nat.card_congr (specialLinearGroupEquivStatedSL 2 K).toEquiv]
    exact CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two K
  have hq : 2 ≤ q := hF ▸ Finite.one_lt_card
  have hq' : 2 ≤ q' := hF' ▸ Finite.one_lt_card
  have hEq : q * (q ^ 2 - 1) = q' * (q' ^ 2 - 1) := by
    have := Nat.card_congr (e.symm.trans e').toEquiv
    rw [hcard F, hcard F', hF, hF'] at this
    exact this
  have hq2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hq'2 : 1 ≤ q' ^ 2 := Nat.one_le_pow _ _ (by omega)
  rcases lt_trichotomy q q' with hlt | heq | hgt
  · exfalso
    have : q * (q ^ 2 - 1) < q' * (q' ^ 2 - 1) := by
      zify [hq2, hq'2] at hEq ⊢
      nlinarith [mul_pos (show (0 : ℤ) < q' - q by omega) (show (0 : ℤ) < q' + q by omega)]
    omega
  · exact heq
  · exfalso
    have : q' * (q' ^ 2 - 1) < q * (q ^ 2 - 1) := by
      zify [hq2, hq'2] at hEq ⊢
      nlinarith [mul_pos (show (0 : ℤ) < q - q' by omega) (show (0 : ℤ) < q + q' by omega)]
    omega

section Ctx2

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G}

theorem stage1L4_q_eq {ε ε' : Bool} {q q' : ℕ} {L₁ L₂ L₁' L₂' : Subgroup (CentralizerBar z)}
    (h : Stage1L4 G z S ε q L₁ L₂) (h' : Stage1L4 G z S ε' q' L₁' L₂') : q = q' := by
  have hc : IsComponent L₁' := by
    have : L₁' ∈ ({L₁', L₂'} : Set (Subgroup (CentralizerBar z))) := Set.mem_insert _ _
    rw [← h'.pair.comps] at this
    exact this
  have hmem : L₁' ∈ ({L₁, L₂} : Set (Subgroup (CentralizerBar z))) := by
    rw [← h.pair.comps]
    exact hc
  rcases hmem with rfl | hmem
  · exact hasSL2Model_unique h.pair.sl₁ h'.pair.sl₁
  · rw [Set.mem_singleton_iff] at hmem
    subst hmem
    exact hasSL2Model_unique h.pair.sl₂ h'.pair.sl₁

end Ctx2

section CaseC

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S M : Subgroup G}

theorem thm4Concl_of_case_c (hP : PSp4_oddCover) (h : Ctx17 G z k S M) {ε : Bool} {q : ℕ}
    {L₁ L₂ : Subgroup (CentralizerBar z)} (hk : k = Kind.l4 ε) (hL4 : Stage1L4 G z S ε q L₁ L₂)
    (hq3 : 3 < q) (hF : IVK.IsPSp4 ↥(generalizedFitting (HBar M)) q)
    (hcoat : IsCoatom (barIn M (Cen z))) : Thm4Concl z k S M := by
  obtain ⟨-, ha, hE⟩ := layer_of_PSp4 hP M hL4.pair.odd hq3 hF h.h17A
  refine ⟨ha, fun _ => ⟨Or.inr ⟨ε, hk⟩, ?_, ?_⟩, fun hMC => ?_⟩
  · intro q' L₁' L₂' hk' _
    rw [hk] at hk'
    exact absurd hk' (by simp)
  · intro ε' q' L₁' L₂' hk' hL4'
    rw [hk] at hk'
    obtain rfl : ε = ε' := Kind.l4.inj hk'
    obtain rfl : q = q' := stage1L4_q_eq hL4 hL4'
    exact hE
  · subst hMC
    exact absurd (barIn_self_eq_top (Cen z)) hcoat.1

end CaseC

theorem thm4 (h34 : Leaf_Prop34) (h19 : Prop19_1) (hP : PSp4_oddCover) : Ch4Thm4 := by
  intro G _ _ z k S hctx M hM hev
  have h : Ctx17 G z k S M := ⟨hctx, hM, hev⟩
  rcases h.cases h34 with hMC | ⟨ε, q, L₁, L₂, hk, hL4, hq3, hF, hcoat⟩
  · obtain ⟨ha, hc⟩ := h19 G z k S M h hMC
    exact ⟨ha, fun hlt => absurd hMC hlt.ne', hc⟩
  · exact thm4Concl_of_case_c hP h hk hL4 hq3 hF hcoat

theorem prop17_1 (h34 : Leaf_Prop34) (hP : PSp4_oddCover) : Prop17_1 := by
  intro G _ _ z k S M h hfail
  rcases h.cases h34 with hMC | ⟨ε, q, L₁, L₂, hk, hL4, hq3, hF, hcoat⟩
  · refine ⟨hMC, fun hO => hfail ?_⟩
    have hO' : pPrimeCore 2 ↥M = ⊥ := (pPrimeCoreOf_eq_bot_iff M).mp hO
    exact ⟨thm4a_of_oddCore_bot hO', fun hlt => absurd hMC hlt.ne', thm4c_of_oddCore_bot hO'⟩
  · exact absurd (thm4Concl_of_case_c hP h hk hL4 hq3 hF hcoat) hfail

end CFSG.GH74.GLS.Stage2.Final.Thm4
