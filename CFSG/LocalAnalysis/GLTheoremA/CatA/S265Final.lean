module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265NL
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265QUsed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265QStd
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265Used
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265Std

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10

theorem i265UsedAt_of_facts (hNL : QFactUNL) {G : Type} [Group G] [Finite G] (p : ℕ) (hp : p.Prime)
    (hp2 : p ≠ 2)
    (hK : ∀ y : G, y ≠ 1 → CFSG.Open.IsKGroup ↥(Subgroup.centralizer ({y} : Set G))) :
    I265UsedAt G p :=
  i265UsedAt_of_fact (factU_of_factUQ (qFactU_of_NL hNL)) p hp hp2 hK

theorem i265UsedAt_of_facts' (hNL : QFactUNL) {G : Type} [Group G] [Finite G] {m : ℕ} (hctx : ThmACtx G m)
    {p : ℕ} (hp : p ∈ Mu G m) : I265UsedAt G p :=
  i265UsedAt_of_facts hNL p hp.1.1 hp.1.2.1 fun y hy =>
    isKGroup_of_isKProper hctx.1.kProper (centralizer_ne_top_of_ne_one hctx.1.simple hctx.1.nonabelian hy)

theorem i265StdAt_of_facts (hNL : QFactSNL) {G : Type} [Group G] [Finite G] (p : ℕ) : I265StdAt G p :=
  i265StdAt_of_fact (factS_of_factSQ (qFactS_of_NL hNL)) p

theorem i265StdAt_of_facts' (hNL : QFactSNL) {G : Type} [Group G] [Finite G] {m : ℕ} (_hctx : ThmACtx G m)
    {p : ℕ} (_hp : p ∈ Mu G m) : I265StdAt G p :=
  i265StdAt_of_facts hNL p

end CFSG.LocalAnalysis.GLTheoremA.S265

end
