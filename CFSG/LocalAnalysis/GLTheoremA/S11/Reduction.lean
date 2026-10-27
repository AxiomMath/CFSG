module

public import CFSG.LocalAnalysis.GLTheoremA.S11.Prop114
public import CFSG.LocalAnalysis.GLTheoremA.S11.Canonical

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.UniquenessMaximal

structure S11Inputs (G : Type) [Group G] [Finite G] : Prop where
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
  i166 : I166At G
  labUniq : LabelUniqAt G
  eTable : ETableAt G
  i61 : I61At G
  i1441 : I1441At G
  i14neg : I14NegAt G
  i1416 : I1416Chev2At G
  i142 : I142At G
  sch : CFSG.AGLEmbedding.KFactCatalogSchreier
  i25 : Input2_5
  rank3 : RankThreeLabelAt G
  ys08 : YS08
  u64types : U64TypesAt G
  u5rank : U5RankAt
  u5out : U5OutAt G
  u6struct : U6StructAt G
  u5case : U5CaseAt G
  u6case : U6CaseAt G
  centq : CentQuasiAt G

theorem S11Inputs.toInputs111 {G : Type} [Group G] [Finite G] (h : S11Inputs G) : Inputs111 G :=
  ⟨h.i161a, h.i161b, h.i162, h.i163, h.i164, h.i165, h.i2315a, h.i2315b, h.i3013, h.e62, h.i183, h.i1810, h.chev2, h.i1122, h.idiag⟩

theorem S11Inputs.toInputs114 {G : Type} [Group G] [Finite G] (h : S11Inputs G) : Inputs114 G :=
  { h.toInputs111 with
    i166 := h.i166, labUniq := h.labUniq, eTable := h.eTable, i61 := h.i61, i1441 := h.i1441, i14neg := h.i14neg,
    i1416 := h.i1416, i142 := h.i142, sch := h.sch, i25 := h.i25, rank3 := h.rank3, ys08 := h.ys08,
    u64types := h.u64types, u5rank := h.u5rank, u5out := h.u5out, u6struct := h.u6struct,
    u5case := h.u5case, u6case := h.u6case, centq := h.centq }

theorem ys10_of_inputs
    (hin : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m → S11Inputs G) : YS10 := by
  intro G _ _ m hctx hsf hne
  have hI := (hin G m hctx).toInputs114
  refine ⟨S11.stage11_of_inputs hctx hsf hI.toInputs111, ?_⟩
  obtain ⟨p, hp, B, x, L, hSS, hsp⟩ := S11.prop114 hctx hsf hI hne
  refine ⟨p, hp, B, x, L, hSS, ?_⟩
  have hID : InnerDiagMarking B L :=
    CFSG.StandardType.Canonical.largeEvenMarking_mono (fun lab R _ I F θ ⟨_, h2, h3⟩ => ⟨h2, h3⟩) hsp
  have hH := S11.rquad_hyp hsf ⟨hp, hSS, hID⟩
  have hm : 4 ≤ m := hctx.1.four_le
  have hpow : p ^ 3 * Nat.card ↥(B ⊓ centModSubgroup p L) ≤ Nat.card B :=
    (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hH.prime.pos (by omega : 3 ≤ m - 1))).trans
      (hH.pow_index_le (by omega))
  exact S11.splitInnerDiag_of_16
    (fun lab hlab => hI.rank3 p hH.prime hH.ne_two B L lab hH.elem hID hpow hlab) hsp

end CFSG.LocalAnalysis.GLTheoremA
