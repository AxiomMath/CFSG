module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167Exc3CoreDispBase
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167Exc3CoreOutD
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167Exc3CoreOutE
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167Exc3CoreRank
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167Exc3CoreWE6
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167Exc3CoreWE8
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcRDF4
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcRDE6
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcRDE7
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcRDE8

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.Assembly (LargeEvenInduces)
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Dickson.Sec6.Up34Exc


theorem exc3core_false_F4 {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] (SL : LangSetup Tag.F4 L 5)
    {a : Fin Tag.F4.rank → Lˣ} (i : KernelComponent (rootCharHom a)) {e f : ℕ}
    (hq : SL.D.q = 2 ^ e) (h3 : 3 ∣ 2 ^ e + 1) (hT : rootDiagUnit Tag.F4 a ∈ SL.D.torus)
    (hap : ∀ m, a m ^ 3 = 1) (ha1 : rootDiagUnit Tag.F4 a ≠ 1)
    (hqs : CFSG.IsQuasisimple ↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i))
    (hshape : catalogIs (↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i)) (T167Idx f)) : False := by
  refine exc3core_false_of_out hshape ?_
  obtain ⟨r6, r18⟩ := exc3core_rank_F4 SL hap i
  rcases rdValues_F4 L a hap i with h | h | h
  · exact exc3core_out_A25 SL hT hap ha1 i (Or.inl ⟨r6 h, h⟩) hqs
  · exact exc3core_out_F4_B3C3 SL hT hap ha1 i (r18 h) h
      (exc3core_inner_of_size SL hT i (Or.inr (Or.inl h)))
  · exact absurd (rootDiagUnit_eq_one_of_ncard i (by rw [h]; rfl)) ha1

theorem exc3core_false_E6 {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] (SL : LangSetup Tag.E6 L 5)
    {a : Fin Tag.E6.rank → Lˣ} (i : KernelComponent (rootCharHom a)) {e f : ℕ}
    (hq : SL.D.q = 2 ^ e) (h3 : 3 ∣ 2 ^ e + 1) (hT : rootDiagUnit Tag.E6 a ∈ SL.D.torus)
    (hap : ∀ m, a m ^ 3 = 1) (ha1 : rootDiagUnit Tag.E6 a ≠ 1)
    (hqs : CFSG.IsQuasisimple ↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i))
    (hshape : catalogIs (↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i)) (T167Idx f)) : False := by
  refine exc3core_false_of_out hshape ?_
  obtain ⟨r2, r6, r20, r24, r30, r40⟩ := exc3core_rank_E6 SL hap i
  rcases rdValues_E6 L a hap i with h | h | h | h | h | h | h
  · exact exc3core_out_A1 SL hT hap ha1 i (r2 h) h hqs
  · exact exc3core_out_A25 SL hT hap ha1 i (Or.inl ⟨r6 h, h⟩) hqs
  · obtain ⟨hobs, huniq⟩ := exc3core_wobs_E6 a hap i (Or.inl h)
    exact exc3core_out_typeA_suN SL hT hap ha1 i
      ⟨by have := r20 h; omega, by rw [r20 h]; omega⟩
      (exc3core_not_inner_of_wobs SL hq h3 hT hap i hobs huniq) hqs
  · exact exc3core_out_D4 SL hT hap ha1 i (r24 h) h
  · exact exc3core_out_A25 SL hT hap ha1 i (Or.inr ⟨r30 h, h⟩) hqs
  · obtain ⟨hobs, huniq⟩ := exc3core_wobs_E6 a hap i (Or.inr h)
    exact exc3core_out_twoD SL hT hap ha1 i (Or.inl ⟨r40 h, h⟩)
      (exc3core_not_inner_of_wobs SL hq h3 hT hap i hobs huniq)
  · exact absurd (rootDiagUnit_eq_one_of_ncard i (by rw [h]; rfl)) ha1

theorem exc3core_false_E7 {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] (SL : LangSetup Tag.E7 L 5)
    {a : Fin Tag.E7.rank → Lˣ} (i : KernelComponent (rootCharHom a))
    (w : WeylGroup Tag.E7) (hρ : ∀ γ, IsRoot Tag.E7 γ → SL.ρ γ = w • γ) {e f : ℕ}
    (hq : SL.D.q = 2 ^ e) (h3 : 3 ∣ 2 ^ e + 1) (hT : rootDiagUnit Tag.E7 a ∈ SL.D.torus)
    (hap : ∀ m, a m ^ 3 = 1) (ha1 : rootDiagUnit Tag.E7 a ≠ 1)
    (hqs : CFSG.IsQuasisimple ↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i))
    (hshape : catalogIs (↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i)) (T167Idx f)) : False := by
  refine exc3core_false_of_out hshape ?_
  obtain ⟨r2, r6, r30, r40, r42, r60, r72⟩ := exc3core_rank_E7 SL hap i
  rcases rdValues_E7 L a hap i with h | h | h | h | h | h | h | h
  · exact exc3core_out_A1 SL hT hap ha1 i (r2 h) h hqs
  · exact exc3core_out_A25 SL hT hap ha1 i (Or.inl ⟨r6 h, h⟩) hqs
  · exact exc3core_out_A25 SL hT hap ha1 i (Or.inr ⟨r30 h, h⟩) hqs
  · obtain ⟨hobs, huniq⟩ := exc3core_wobs_E7 a hap i (Or.inl h)
    exact exc3core_out_twoD SL hT hap ha1 i (Or.inl ⟨r40 h, h⟩)
      (exc3core_not_inner_of_wobs SL hq h3 hT hap i hobs huniq)
  · obtain ⟨hobs, huniq⟩ := exc3core_wobs_E7 a hap i (Or.inr (Or.inl h))
    exact exc3core_out_typeA_suN SL hT hap ha1 i
      ⟨by have := r42 h; omega, by rw [r42 h]; omega⟩
      (exc3core_not_inner_of_wobs SL hq h3 hT hap i hobs huniq) hqs
  · exact exc3core_out_D6_inner SL hT hap ha1 i (r60 h) h (exc3core_inner_D6 SL i w hρ hq h3 hT hap h)
  · obtain ⟨hobs, huniq⟩ := exc3core_wobs_E7 a hap i (Or.inr (Or.inr h))
    exact exc3core_out_E6 SL hT hap ha1 i (r72 h) h
      (exc3core_not_inner_of_wobs SL hq h3 hT hap i hobs huniq)
  · exact absurd (rootDiagUnit_eq_one_of_ncard i (by rw [h]; rfl)) ha1

theorem exc3core_false_E8 {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] (SL : LangSetup Tag.E8 L 5)
    {a : Fin Tag.E8.rank → Lˣ} (i : KernelComponent (rootCharHom a)) {e f : ℕ}
    (hq : SL.D.q = 2 ^ e) (h3 : 3 ∣ 2 ^ e + 1) (hT : rootDiagUnit Tag.E8 a ∈ SL.D.torus)
    (hap : ∀ m, a m ^ 3 = 1) (ha1 : rootDiagUnit Tag.E8 a ≠ 1)
    (hqs : CFSG.IsQuasisimple ↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i))
    (hshape : catalogIs (↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i)) (T167Idx f)) : False := by
  refine exc3core_false_of_out hshape ?_
  obtain ⟨r6, r72, r84, r126⟩ := exc3core_rank_E8 SL hap i
  rcases rdValues_E8 L a hap i with h | h | h | h | h
  · exact exc3core_out_A25 SL hT hap ha1 i (Or.inl ⟨r6 h, h⟩) hqs
  · obtain ⟨hobs, huniq⟩ := exc3core_wobs_E8 a hap i (Or.inl h)
    have hout := exc3core_not_inner_of_wobs SL hq h3 hT hap i hobs huniq
    rcases r72 h with hr | hr
    · exact exc3core_out_E6 SL hT hap ha1 i hr h hout
    · exact exc3core_out_typeA_suN SL hT hap ha1 i ⟨by omega, by rw [hr]; omega⟩ hout hqs
  · obtain ⟨hobs, huniq⟩ := exc3core_wobs_E8 a hap i (Or.inr h)
    exact exc3core_out_twoD SL hT hap ha1 i (Or.inr ⟨r84 h, h⟩)
      (exc3core_not_inner_of_wobs SL hq h3 hT hap i hobs huniq)
  · exact exc3core_out_E7 SL hT hap ha1 i (r126 h) h
      (exc3core_inner_of_size SL hT i (Or.inr (Or.inr h)))
  · exact absurd (rootDiagUnit_eq_one_of_ncard i (by rw [h]; rfl)) ha1


end CFSG.LocalAnalysis.GLTheoremA.I167

end
