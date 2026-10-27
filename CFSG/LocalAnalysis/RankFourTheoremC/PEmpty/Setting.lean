module

public import CFSG.Yardstones.Md8ed6d263d89.Definitions
import CFSG.LocalAnalysis.RankFourTheoremC.Equivalence

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 Subgroup
open CFSG.Yardstones.Md8ed6d263d89 (TheoremCAt)
open CFSG.LocalAnalysis.RankFourTheoremC.PPointP (omegaCenter mem_omegaCenter)

structure Global (G : Type) [Group G] [Finite G] : Prop where
  d1Global : D1Global G
  d1 : D1For G
  d2 : D2For G
  fullCore : FullCoreLocality G
  thmC : ∀ (f : ℕ) (F : Sylow f G) (N : Subgroup G), D1Local f F N →
    (∃ y : G, IsPElement f N y) → TheoremCAt G f N

structure Situation (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M : Subgroup G) :
    Prop where
  toGlobal : Global G
  p_ge : 5 ≤ p
  larger : ∀ (q : ℕ) (Q : Sylow q G) (N : Subgroup G), p < q → D1Local q Q N → TheoremCAt G q N
  loc : D1Local p P M
  empty : ¬ ∃ y : G, IsPElement p M y

structure Point {G : Type} [Group G] {p : ℕ} (P : Sylow p G) (M : Subgroup G) (x : G) : Prop where
  mem : x ∈ (P : Subgroup G)
  order : orderOf x = p
  not_le : ¬ centralizer ({x} : Set G) ≤ M
  sylow : CFSG.ABGLocalTools.IsSylowOf p ((P : Subgroup G) ⊓ centralizer ({x} : Set G))
    (centralizer ({x} : Set G))

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G}

namespace Situation

theorem prime (hS : Situation G p P M) : p.Prime := hS.loc.beta.1

theorem ne_two (hS : Situation G p P M) : p ≠ 2 := hS.loc.beta.2.1

theorem simple (hS : Situation G p P M) : IsSimpleGroup G := hS.toGlobal.d1Global.simple

theorem nonab (hS : Situation G p P M) : ∃ a b : G, a * b ≠ b * a := hS.toGlobal.d1Global.nonab

theorem sylow_le (hS : Situation G p P M) : (P : Subgroup G) ≤ M := sylow_le_of_core hS.loc

theorem four_le_pRank (hS : Situation G p P M) : 4 ≤ Open.pRank p (P : Subgroup G) :=
  four_le_pRank_sylow hS.loc.beta P

theorem normalizer_le (hS : Situation G p P M) {S : Subgroup G} (hSp : IsPGroup p S) (hSM : S ≤ M)
    (hS2 : 2 ≤ Open.pRank p S) : normalizer (S : Set G) ≤ M :=
  normalizer_le_of_two_le_pRank hS.toGlobal.fullCore hS.loc hSp hSM hS2

theorem centralizer_le_of_pRank (hS : Situation G p P M) {y : G} (hy : y ∈ M)
    (hyp : orderOf y = p) (h3 : 3 ≤ Open.pRank p (M ⊓ centralizer ({y} : Set G))) :
    centralizer ({y} : Set G) ≤ M := by
  by_contra h
  exact hS.empty ⟨y, hy, hyp, h3, h⟩

theorem normalizer_zpowers_le (hS : Situation G p P M) {y : G} (hyP : y ∈ (P : Subgroup G))
    (hyp : orderOf y = p)
    (h3 : 3 ≤ Open.pRank p ((P : Subgroup G) ⊓ centralizer ({y} : Set G))) :
    normalizer ((zpowers y : Subgroup G) : Set G) ≤ M := by
  have hCM : centralizer ({y} : Set G) ≤ M :=
    hS.centralizer_le_of_pRank (hS.sylow_le hyP) hyp
      (h3.trans (CFSG.SectionRank.pRank_mono hS.prime.one_lt
        (inf_le_inf_right _ hS.sylow_le)))
  exact normalizer_zpowers_le_of_centralizer_le hS.toGlobal.fullCore hS.loc hCM (by omega)

end Situation

namespace Point

variable {x : G}

theorem pow_eq_one (hx : Point P M x) : x ^ p = 1 := by
  rw [← hx.order]
  exact pow_orderOf_eq_one x

theorem ne_one (hp : p.Prime) (hx : Point P M x) : x ≠ 1 := by
  intro h
  have := hx.order
  rw [h, orderOf_one] at this
  exact hp.one_lt.ne this

theorem mem_M (hS : Situation G p P M) (hx : Point P M x) : x ∈ M := hS.sylow_le hx.mem

theorem pRank_centralizer_le (hS : Situation G p P M) (hx : Point P M x) :
    Open.pRank p (centralizer ({x} : Set G)) ≤ 2 := by
  have hp := hS.prime
  have hMx : Open.pRank p (M ⊓ centralizer ({x} : Set G)) ≤ 2 := by
    by_contra h
    exact hS.empty ⟨x, hx.mem_M hS, hx.order, by omega, hx.not_le⟩
  rw [← pRank_eq_of_isSylowOf hp hx.sylow]
  exact (CFSG.SectionRank.pRank_mono hp.one_lt
    (inf_le_inf_right _ hS.sylow_le)).trans hMx

end Point

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
