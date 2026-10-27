module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167ExcSmall
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167ExcRk2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167ExcE6
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167Exc3Big
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167ExcPar

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10


theorem false_of_exc3 {Ω : Type} [Group Ω] [Finite Ω] {p : ℕ} {B X D J : Subgroup Ω}
    (hp : p.Prime) (hp2 : p ≠ 2) (hB : IsElemAbelian p B) (hX : CFSG.Open.IsQuasisimple ↥X)
    (hchev : IsChevSimple 2 (PSimple p X)) (hBN : B ≤ Subgroup.normalizer (X : Set Ω))
    (hrank : GLATwoLocalRank p ↥(X ⊔ B) ≤ CFSG.Open.pRank p B)
    (hSC : ∀ g ∈ X ⊔ B, g ∈ Subgroup.centralizer (B : Set Ω) → orderOf g = p → g ∈ B)
    (hcard : Nat.card ↥(B ⊓ cs X) = p) (hD : IsE2 p B D) (hJ : GLAPComponent p (X ⊓ cs D) J)
    (hDJ : D = B ⊓ cs J) (htype : Type167J p J)
    (hsplit : HalfSplit16At p X ∨ ∃ d ∈ D, FieldOn p d X)
    {x : Ω} (hxD : x ∈ D) (hxX : x ∉ cs X) (hDx : D = (B ⊓ cs X) ⊔ Subgroup.zpowers x)
    (hnf : ∀ d ∈ D, ¬ FieldOn p d X) (hhs : HalfSplit16At p X)
    (hinn : InnDiagOn p (Subgroup.zpowers x) X)
    (hexc : ¬ catalogIs (PSimple p X) K1419.I1419Classical2) (hp3 : p = 3) : False := by
  have H : ExcHyp p B X D J x :=
    ⟨hp, hp2, hB, hX, hchev, hBN, hrank, hSC, hcard, hD, hJ, hDJ, htype, hsplit, hxD, hxX, hDx, hnf, hhs,
      hinn, hexc⟩
  rcases exc_dispatch hchev hexc with hs | hr | h6 | hpar
  · exact false_of_exc_small H hs
  · exact false_of_exc_rk2 H hr
  · exact false_of_exc3_big H hp3 (catalogIs_imp (fun i hi => Or.inl hi) h6)
  · exact false_of_exc3_big H hp3 (catalogIs_imp (fun i hi => Or.inr hi) hpar)

theorem false_of_exc {Ω : Type} [Group Ω] [Finite Ω] {p : ℕ} {B X D J : Subgroup Ω}
    (hp : p.Prime) (hp2 : p ≠ 2) (hB : IsElemAbelian p B) (hX : CFSG.Open.IsQuasisimple ↥X)
    (hchev : IsChevSimple 2 (PSimple p X)) (hBN : B ≤ Subgroup.normalizer (X : Set Ω))
    (hrank : GLATwoLocalRank p ↥(X ⊔ B) ≤ CFSG.Open.pRank p B)
    (hSC : ∀ g ∈ X ⊔ B, g ∈ Subgroup.centralizer (B : Set Ω) → orderOf g = p → g ∈ B)
    (hcard : Nat.card ↥(B ⊓ cs X) = p) (hD : IsE2 p B D) (hJ : GLAPComponent p (X ⊓ cs D) J)
    (hDJ : D = B ⊓ cs J) (htype : Type167J p J)
    (hsplit : HalfSplit16At p X ∨ ∃ d ∈ D, FieldOn p d X)
    {x : Ω} (hxD : x ∈ D) (hxX : x ∉ cs X) (hDx : D = (B ⊓ cs X) ⊔ Subgroup.zpowers x)
    (hnf : ∀ d ∈ D, ¬ FieldOn p d X) (hhs : HalfSplit16At p X)
    (hinn : InnDiagOn p (Subgroup.zpowers x) X)
    (hexc : ¬ catalogIs (PSimple p X) K1419.I1419Classical2) (hp3 : p ≠ 3) : False := by
  have H : ExcHyp p B X D J x :=
    ⟨hp, hp2, hB, hX, hchev, hBN, hrank, hSC, hcard, hD, hJ, hDJ, htype, hsplit, hxD, hxX, hDx, hnf, hhs,
      hinn, hexc⟩
  rcases exc_dispatch hchev hexc with hs | hr | h6 | hpar
  · exact false_of_exc_small H hs
  · exact false_of_exc_rk2 H hr
  · exact false_of_exc_E6 H hp3 h6
  · exact false_of_exc_parabolic H hp3 hpar

end CFSG.LocalAnalysis.GLTheoremA.I167

end
