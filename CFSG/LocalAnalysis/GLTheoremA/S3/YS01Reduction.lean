module

public import CFSG.LocalAnalysis.GLTheoremA.S3.Prop32
public import CFSG.LocalAnalysis.GLTheoremA.S3.Prop33
public import CFSG.LocalAnalysis.GLTheoremA.S3.Lemma21
public import CFSG.LocalAnalysis.GLTheoremA.P55.Dihedral

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.UniquenessMaximal

structure S3Inputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  km : KMUsedAt
  lBalance : LBalanceAt G p
  input18_3_4 : Input18_3_4
  input18_3_12 : Input18_3_12
  i1135 : I1135At G p
  chevClosure : ChevClosureAt G p
  chevUnique : ChevUniqueAt G p
  chevInner : ChevInnerAt G p
  i65 : I65At G p
  i76 : I76At G p
  chevRank3 : ChevRank3At G p
  i112L227 : I112L227At G
  l227Data : L227DataAt G
  l227Pump : L227PumpAt G

variable {G : Type} [Group G] [Finite G]

theorem stage3_of_inputs {m : ℕ} (hctx : ThmACtx G m) {p : ℕ} (hp : p ∈ Mu G m)
    (hin : S3Inputs G p) : Stage3 G p := by
  have hc : S3Ctx G p := S3Ctx.of_ctx hctx hp
  refine ⟨fun B hB => prop32 hin.km P55.dihedralUsed hin.lBalance hc hB,
    fun B hB => lemma31_hyperplane hctx hp hB,
    fun B D N hB hDB hDnc hN hBN => lemma31 hctx hp hB hDB hDnc hN hBN,
    fun B hB hchev => prop33 hin.km P55.dihedralUsed hc hin.input18_3_4 hin.i1135 hin.chevClosure
      hin.chevUnique hin.chevInner hin.i65 hin.i76 hin.chevRank3 hB hchev, ?_⟩
  intro h3 B b L hB hb hb1 hL hL27
  subst h3
  exact lemma21 hc hin.i112L227 hin.l227Data hin.l227Pump hin.input18_3_12 hB hb hb1 hL hL27

theorem ys01_of_inputs (hin : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m →
    ∀ p ∈ Mu G m, S3Inputs G p) : YS01 :=
  fun G _ _ m hctx p hp => stage3_of_inputs hctx hp (hin G m hctx p hp)

end CFSG.LocalAnalysis.GLTheoremA
