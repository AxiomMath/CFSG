module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294Defs
public import CFSG.HardMathSupport.Lang.E6Descent.MaxClassRank
public import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank
public import CFSG.LocalAnalysis.PreuniquenessRankFour.Helpers
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

open CFSG CFSG.Open Subgroup

theorem card_eq_eightyOne_of_sylowLine {Y : Type} [Group Y] [Finite Y] {D : Subgroup Y} {x : Y}
    (hDe : CFSG.Open.IsElemAbelian 3 D) (hD : Nat.card D = 3 ^ 2) (hx : x ∈ D) (hx1 : x ≠ 1)
    (hS : CFSG.ABGLocalTools.IsSylowOf 3 D (centralizer ({x} : Set Y)))
    {P : Subgroup Y} (hP : IsPGroup 3 P) (hDP : D ≤ P) (hrk : CFSG.Open.pRank 3 P = 3) :
    Nat.card P = 81 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp3 : (3 : ℕ).Prime := Nat.prime_three
  have hxP : x ∈ P := hDP hx
  have hx3 : x ^ 3 = 1 := hDe.2 x hx
  have hxo : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hDC : D ≤ centralizer ({x} : Set Y) := fun d hd =>
    Subgroup.mem_centralizer_singleton_iff.2 (hDe.comm hd hx)
  let x' : P := ⟨x, hxP⟩
  have hx'o : orderOf x' = 3 := by rw [Subgroup.orderOf_mk]; exact hxo
  have hC : Subgroup.centralizer ({x'} : Set P) = D.subgroupOf P := by
    ext g
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf]
    constructor
    · intro hg
      have hgC : (g : Y) ∈ centralizer ({x} : Set Y) :=
        Subgroup.mem_centralizer_singleton_iff.2 (congrArg Subtype.val hg)
      have heq : P ⊓ centralizer ({x} : Set Y) = D :=
        hS.eq_of_le (le_inf hDP hDC) inf_le_right hP.to_inf_left
      rw [← heq]
      exact Subgroup.mem_inf.2 ⟨g.2, hgC⟩
    · intro hg
      exact Subtype.ext (hDe.comm hg hx)
  have hC9 : Nat.card (Subgroup.centralizer ({x'} : Set P)) = 3 ^ 2 := by
    rw [hC, ← hD]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDP).toEquiv
  have hmax : CFSG.Walter.W67.IsMaximalClass 3 P :=
    CFSG.Walter.W67.isMaximalClass_of_card_centralizer hP x' hx'o hC9
  obtain ⟨B, hBP, hBe, hBc⟩ := CFSG.PreuniquenessRankFour.Helpers.pRank_attained 3 hp3 P
  rw [hrk] at hBc
  have hBe' : IsElemAbelian 3 (B.subgroupOf P) := IsElemAbelian.comap hBe P.subtype_injective
  have hBc' : Nat.card (B.subgroupOf P) = 27 := by
    rw [show (27 : ℕ) = Nat.card B by rw [hBc]; norm_num]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBP).toEquiv
  exact CFSG.HardMathSupport.Lang.E6Descent.card_eq_81_of_maxClass_of_elemAbelian27 hP hmax
    (B.subgroupOf P) hBe' hBc'.ge

theorem I294Cfg.card_sylow_eq_eightyOne {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y}
    [L.Normal] {z g : Y} {D : Subgroup Y} (h : I294Cfg 3 L z g D) (P : Sylow 3 Y)
    (hDP : D ≤ (P : Subgroup Y)) : Nat.card P = 81 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hxD, hx1, hS⟩ := h.sylowLine
  have hrk : CFSG.Open.pRank 3 (P : Subgroup Y) = 3 :=
    (CFSG.SectionRank.pRank_sylow P).1.trans h.rank
  exact card_eq_eightyOne_of_sylowLine h.elem h.card hxD hx1 hS P.isPGroup' hDP hrk

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
