module

public import CFSG.LocalAnalysis.GLTheoremA.S11.CounterD

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

structure Inputs111 (G : Type) [Group G] [Finite G] : Prop where
  i161a : I161aAt G
  i161b : I161bAt G
  i162 : I162At G
  i163 : I163At G
  i164 : I164At G
  i165 : I165At G
  i2315a : I2315aAt G
  i2315b : I2315bAt G
  i3013 : I3013At G
  e62 : E62At G
  i183 : Input18_3_4
  i1810 : Input18_10
  chev2 : ∀ p : ℕ, Chev2DownAt G p
  i1122 : ∀ p : ℕ, p.Prime → p ≠ 2 → I1122IsoAt G p
  idiag : InnDiagIndepAt G

structure Cor112Full (G : Type) [Group G] [Finite G] (m p : ℕ) (B : Subgroup G) (x : G) (L : Subgroup G) : Prop where
  indep : Cor112Indep G m p B x L
  e_eq : evenRank ↥L = m
  half : ∃ lab : GLALabel, LabelOf L lab ∧ List110 p lab (Subgroup.center ↥L = ⊥)
  not_E62 : ¬ LabelOf L ⟨.E6, 0, 1⟩

namespace S11

variable {G : Type} [Group G] [Finite G] {m p q : ℕ} {B : Subgroup G} {x : G} {L : Subgroup G}

theorem no_ce (hctx : ThmACtx G m) (hsf : StageFacts G m) (hin : Inputs111 G) (hce : CE G m p B x L q) : False := by
  obtain ⟨M, D, E, F, J, hR⟩ := redB hctx hsf hin.i161a hin.i165 hin.i2315a hce
  exact redC hctx hsf hin.i183 hin.i2315b hin.i3013 hin.i1810 (hin.chev2 p) (hin.i1122 p hce.hyp.prime hce.hyp.ne_two) hce.hyp hR hce.prime hce.odd

theorem nosplit_of_gt (hin : Inputs111 G) (hH : Hyp111 G m p B x L) (hm : 4 ≤ m) (hgt : m < evenRank ↥L) : NoSplit16 p L := by
  have hp := hH.prime
  have hBx : B ≤ Subgroup.centralizer ({x} : Set G) := fun b hb => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (isElemAbelian_commute hH.elem hb hH.mem).symm ▸ rfl
  have hrank : CFSG.Open.pRank p B = m := pRank_eq_of_card hp hH.elem hH.card_B
  refine hin.i164 p hp hH.ne_two (Subgroup.centralizer ({x} : Set G)) L B ⟨hH.comp.1, hH.comp.2.1, hH.qs⟩ hH.isChev2 hBx
    hH.elem hH.idiag (hrank ▸ hm) ⟨x, ⟨hH.mem, ?_⟩, hH.ne_one⟩ ?_ (hrank ▸ hgt)
  · show x ∈ Subgroup.centralizer (L : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.1 (hH.comp.1 hl)
  · rw [hrank]
    have h1 := twoLocalRank_le_top hp (Subgroup.centralizer ({x} : Set G))
    rw [hH.mu.2.1] at h1
    exact h1

theorem prop111_le (hctx : ThmACtx G m) (hsf : StageFacts G m) (hin : Inputs111 G) (hH : Hyp111 G m p B x L) :
    evenRank ↥L ≤ m := by
  by_contra hgt
  push Not at hgt
  have hm : 4 ≤ m := hctx.1.four_le
  have hns := nosplit_of_gt hin hH hm hgt
  obtain ⟨q, hq, hq2, hqL⟩ := exists_prime_eq_evenRank (L := L) (by omega)
  refine no_ce hctx hsf hin (q := q) ⟨hH, hns, hq, hq2, hqL, hgt.le, ?_, Or.inl hgt⟩
  intro hqmu
  have h1 := twoLocalRank_le_top hq L
  rw [hqL, hqmu.2.1] at h1
  omega

theorem prop111_half (hctx : ThmACtx G m) (hin : Inputs111 G) (hH : Hyp111 G m p B x L) (he : evenRank ↥L ≤ m) :
    HalfSplit16At p L := by
  have hm : 4 ≤ m := hctx.1.four_le
  refine hin.i162 p hH.prime hH.ne_two B L (m - 1) hH.elem hH.idiag (by omega) (by omega) ?_
  exact hH.pow_index_le (by omega)

theorem prop111 (hctx : ThmACtx G m) (hsf : StageFacts G m) (hin : Inputs111 G) (hH : Hyp111 G m p B x L) :
    evenRank ↥L ≤ m ∧ HalfSplit16At p L := by
  have he := prop111_le hctx hsf hin hH
  exact ⟨he, prop111_half hctx hin hH he⟩

theorem stage11_of_inputs (hctx : ThmACtx G m) (hsf : StageFacts G m) (hin : Inputs111 G) : Stage11 G m := by
  intro q hq B x L hB hxB hx1 hcomp hnorm hcent hqs hid
  have hH : Hyp111 G m q B x L := ⟨hq, hB, hxB, hx1, hcomp, hnorm, hcent, hqs, hid⟩
  obtain ⟨he, lab, hlab, hhalf⟩ := prop111 hctx hsf hin hH
  refine ⟨he, ?_⟩
  have h1 := hin.idiag B L (fun lab' _ _ _ _ _ => lab' = lab) hid hlab
  refine CFSG.StandardType.Canonical.largeEvenMarking_mono ?_ h1
  intro lab' R _ I F θ ⟨h2, h3, h4⟩
  subst h2
  exact ⟨hhalf, h3, h4⟩

theorem prop113 (hctx : ThmACtx G m) (hsf : StageFacts G m) (hin : Inputs111 G) (hR : RQuad G m p B x L)
    (hns : NoSplit16 p L) (he : evenRank ↥L = m) (hq : q.Prime) (hq2 : q ≠ 2) (hqL : GLATwoLocalRank q ↥L = m) :
    q ∈ Mu G m := by
  by_contra hbad
  exact no_ce hctx hsf hin (q := q) ⟨rquad_hyp hsf hR, hns, hq, hq2, by omega, he.ge, hbad, Or.inr hR⟩

theorem cor112_full (hctx : ThmACtx G m) (hsf : StageFacts G m) (hin : Inputs111 G) (hR : RQuad G m p B x L)
    (hns : NoSplit16 p L) : Cor112Full G m p B x L := by
  have hH := rquad_hyp hsf hR
  have hm : 4 ≤ m := hctx.1.four_le
  have hindep := cor112_indep hctx hsf hin.i161a hR hns
  have hrk := hindep.rank
  obtain ⟨he, hhalf⟩ := prop111 hctx hsf hin hH
  have hge : m - 1 ≤ evenRank ↥L := hrk ▸ twoLocalRank_le_evenRank hH.prime hH.ne_two L
  have hne : evenRank ↥L ≠ m - 1 := by
    intro heq
    obtain ⟨lab, hlab, hsp⟩ := hin.i163 p hH.prime hH.ne_two L hH.isChev2 (by omega) (by omega)
      (Or.inr ⟨B ⊓ L, inf_le_right, isElemAbelian_mono hH.elem inf_le_left, by rw [hrk]; exact card_inf_eq hH hindep.direct,
        hindep.comm⟩)
    exact hns lab hlab hsp
  have he_eq : evenRank ↥L = m := by omega
  refine ⟨hindep, he_eq, ?_, ?_⟩
  · obtain ⟨lab, hlab, hh⟩ := hhalf
    exact ⟨lab, hlab, hh, hns lab hlab⟩
  · intro hE62
    have h2 := hin.e62 p L hH.prime hH.ne_two hE62 hhalf hns
    rw [hrk] at h2
    omega

theorem noSplit_of_not_114 (hin : InnDiagIndepAt G)
    (hno : ¬ ∃ p ∈ Mu G m, ∃ (B : Subgroup G) (x : G) (L : Subgroup G), IsSStarMax p B x L ∧ SplitInnerDiagMarking16 p B L)
    (hR : RQuad G m p B x L) : NoSplit16 p L := by
  intro lab hlab hsp
  apply hno
  refine ⟨p, hR.1, B, x, L, hR.2.1, ?_⟩
  have h1 := hin B L (fun lab' _ _ _ _ _ => lab' = lab) hR.2.2 hlab
  refine CFSG.StandardType.Canonical.largeEvenMarking_mono ?_ h1
  intro lab' R _ I F θ ⟨h2, h3, h4⟩
  subst h2
  exact ⟨hsp, h3, h4⟩

end S11

end CFSG.LocalAnalysis.GLTheoremA
