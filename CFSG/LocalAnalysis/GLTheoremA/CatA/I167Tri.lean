module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167TriAmb
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167Step0
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10

set_option linter.unusedSectionVars false


theorem false_of_triality {Ω : Type} [Group Ω] [Finite Ω] {p : ℕ} {B X D J : Subgroup Ω}
    (hp : p.Prime) (hp2 : p ≠ 2) (hB : IsElemAbelian p B) (hX : CFSG.Open.IsQuasisimple ↥X)
    (hchev : IsChevSimple 2 (PSimple p X)) (hBN : B ≤ Subgroup.normalizer (X : Set Ω))
    (hrank : GLATwoLocalRank p ↥(X ⊔ B) ≤ CFSG.Open.pRank p B)
    (hSC : ∀ g ∈ X ⊔ B, g ∈ Subgroup.centralizer (B : Set Ω) → orderOf g = p → g ∈ B)
    (hcard : Nat.card ↥(B ⊓ cs X) = p) (hD : IsE2 p B D) (hJ : GLAPComponent p (X ⊓ cs D) J)
    (hDJ : D = B ⊓ cs J) (htype : Type167J p J)
    (hsplit : HalfSplit16At p X ∨ ∃ d ∈ D, FieldOn p d X)
    {x : Ω} (hxD : x ∈ D)
    (hnf : ∀ d ∈ D, ¬ FieldOn p d X) (hnon : NonInnDiag p x X) (hp3 : p = 3)
    (htri : catalogIs (PSimple 3 X) isD4any ∨ IsTD4 3 X) : False := by
  subst hp3
  have hxB : x ∈ B := hD.1 hxD
  have hxN : x ∈ Subgroup.normalizer (X : Set Ω) := hBN hxB
  have hx3 : x ^ 3 = 1 := hB.2 x hxB
  have hself : GLAPComponent 3 X X := tri_glaPComponent_self hX hchev
  have hxc : x ∉ cs X := tri_not_mem_cs hself hchev hxN hnon.2
  have hDsup := eq_sup_zpowers_of_notMem_cs hp hD hcard (inf_cs_le_of_glaPComponent hJ hDJ) hxD hxc
  exact false_of_triality_amb hX hchev hxN hx3 (hnf x hxD) hnon.2
    (glaPComponent_inf_cx_of_eq_sup hDsup hJ) htype

theorem i167Tri_holds : I167Tri := by
  intro Ω _ _ p B X D J x hp hp2 hB hX hchev hBN hrank hSC hcard hD hJ hDJ htype hsplit hxD
    _ _ hnf hnon hp3 htri
  exact false_of_triality hp hp2 hB hX hchev hBN hrank hSC hcard hD hJ hDJ htype hsplit hxD hnf
    hnon hp3 htri

end CFSG.LocalAnalysis.GLTheoremA.I167

end
