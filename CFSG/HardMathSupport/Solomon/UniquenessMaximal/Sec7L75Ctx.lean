module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Interface
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator

variable {G : Type} [Group G] [Finite G]

@[expose] def mkN (N : Subgroup G) (a : G) (ha : a ∈ N) : ↥N ⧸ GLAPPrimeCore 3 ↥N :=
  QuotientGroup.mk' (GLAPPrimeCore 3 ↥N) ⟨a, ha⟩

omit [Finite G] in
theorem mkN_one (N : Subgroup G) : mkN N 1 N.one_mem = 1 := map_one (QuotientGroup.mk' _)

structure Ctx75 (B N K : Subgroup G) (x : G) : Prop where
  stand : GLStanding G 4 3
  bone : IsBOneMax 3 B
  hf : IsProp68Facts B K
  hN : N ≠ ⊤
  hBN : B ≤ N
  cov : Covers3 N K
  hxB : x ∈ B
  hx1 : x ≠ 1
  hxK : GLAPComponent 3 (Subgroup.centralizer ({x} : Set G)) K

namespace Ctx75

variable {B N K : Subgroup G} {x : G}

theorem hxN (c : Ctx75 B N K x) : x ∈ N := c.hBN c.hxB

theorem AN (c : Ctx75 B N K x) {a : G} (ha : a ∈ centralizerQuot B K) : a ∈ N :=
  c.hBN ((Subgroup.closure_le B).2 (fun _ hb => hb.1) ha)

end Ctx75

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
