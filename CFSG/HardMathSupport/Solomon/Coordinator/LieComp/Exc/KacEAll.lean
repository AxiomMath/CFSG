module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.KacE
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUE6
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUE7
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUE8

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.PartOne.KE CFSG.Timmesfeld
open scoped MatrixGroups Matrix

set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

@[expose] def e6ETreesRaw : List (List (Option (Fin 6))) :=
  [[none, some 4, some 1, some 3, some 2, some 0],
    [none, some 2, some 1, some 3, some 4, some 5],
    [some 0, some 1, some 2, some 3, some 4, some 5]]

@[expose] def e6ETrees : List (List (Option (Fin Tag.E6.rank))) := e6ETreesRaw

theorem e6_ecount_raw : ∀ c ∈ e6Conn, 6 ≤ c.length →
    kacCount Tag.E6 ![1, 2, 2, 3, 2, 1] (c.map (idxNode (r := Tag.E6.rank))).toFinset =
      eRootCount c.length → ∃ P ∈ e6ETrees, sameSet c (P.map nodeIdx) = true := by
  decide +kernel

theorem e6_ecount : ∀ c ∈ e6Conn, 6 ≤ c.length →
    kacCount Tag.E6 kacE6.θ (c.map (idxNode (r := Tag.E6.rank))).toFinset =
      eRootCount c.length → ∃ P ∈ e6ETrees, sameSet c (P.map nodeIdx) = true :=
  e6_ecount_raw

theorem e6_etrees_raw : ∀ P ∈ e6ETreesRaw, P.Nodup ∧ 6 ≤ P.length ∧
    (∀ c d : Fin P.length, c ≠ d → ¬ edgeE P.length c d → ¬ edgeE P.length d c →
      iform (e6ExtVec (P.get c)) (e6ExtVec (P.get d)) = 0) ∧
    ∀ c d : Fin P.length, edgeE P.length c d →
      (nodeIdx (P.get c), nodeIdx (P.get d)) ∈ e6EdgeIdx := by
  decide +kernel

theorem e6_etrees :
    ∀ P ∈ e6ETrees, P.Nodup ∧ 6 ≤ P.length ∧
      (∀ c d : Fin P.length, c ≠ d → ¬ edgeE P.length c d → ¬ edgeE P.length d c →
        iform (kacE6.extRoot (P.get c)) (kacE6.extRoot (P.get d)) = 0) ∧
      ∀ c d : Fin P.length, edgeE P.length c d →
        (nodeIdx (P.get c), nodeIdx (P.get d)) ∈ e6EdgeIdx := by
  rw [kacE6_extRoot]
  exact e6_etrees_raw

theorem e6_elen : ∀ P ∈ e6ETrees, P.length = 6 ∨ P.length = 7 ∨ P.length = 8 := by
  decide

section E6Rat


theorem rationalLieType_of_eClass_E6 {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ}
    (S : LangSetup Tag.E6 L p₀) (hp : p.Prime) (hpL : (p : L) ≠ 0)
    {a : Fin Tag.E6.rank → Lˣ} (hTor : rootDiagUnit Tag.E6 a ∈ S.D.torus)
    (hTp : rootDiagUnit Tag.E6 a ^ p = 1) (i : KernelComponent (rootCharHom a))
    (h6 : 6 ≤ compRank (componentRoots (rootCharHom a) i))
    (hn : (componentRoots (rootCharHom a) i).ncard =
      eRootCount (compRank (componentRoots (rootCharHom a) i)))
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    RationalLieType (ringChar L) (rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
  rationalLieType_of_eClass (Or.inr (Or.inl rfl)) kacE6 facts_E6 e6_tree e6_adj e6_check e6_lt
    e6_card e6_ecount e6_etrees e6_elen (fun {F} _ x y h => e6_frames x y h) S hp hpL hTor hTp i
    h6 hn hinner

end E6Rat

@[expose] def e7ETreesRaw : List (List (Option (Fin 7))) :=
  [[some 0, some 1, some 2, some 3, some 4, some 5],
    [some 5, some 1, some 4, some 3, some 2, some 0, none],
    [some 0, some 1, some 2, some 3, some 4, some 5, some 6]]

@[expose] def e7ETrees : List (List (Option (Fin Tag.E7.rank))) := e7ETreesRaw

theorem e7_ecount_raw : ∀ c ∈ e7Conn, 6 ≤ c.length →
    kacCount Tag.E7 ![2, 2, 3, 4, 3, 2, 1] (c.map (idxNode (r := Tag.E7.rank))).toFinset =
      eRootCount c.length → ∃ P ∈ e7ETrees, sameSet c (P.map nodeIdx) = true := by
  decide +kernel

theorem e7_ecount : ∀ c ∈ e7Conn, 6 ≤ c.length →
    kacCount Tag.E7 kacE7.θ (c.map (idxNode (r := Tag.E7.rank))).toFinset =
      eRootCount c.length → ∃ P ∈ e7ETrees, sameSet c (P.map nodeIdx) = true :=
  e7_ecount_raw

theorem e7_etrees_raw : ∀ P ∈ e7ETreesRaw, P.Nodup ∧ 6 ≤ P.length ∧
    (∀ c d : Fin P.length, c ≠ d → ¬ edgeE P.length c d → ¬ edgeE P.length d c →
      iform (e7ExtVec (P.get c)) (e7ExtVec (P.get d)) = 0) ∧
    ∀ c d : Fin P.length, edgeE P.length c d →
      (nodeIdx (P.get c), nodeIdx (P.get d)) ∈ e7EdgeIdx := by
  decide +kernel

theorem e7_etrees :
    ∀ P ∈ e7ETrees, P.Nodup ∧ 6 ≤ P.length ∧
      (∀ c d : Fin P.length, c ≠ d → ¬ edgeE P.length c d → ¬ edgeE P.length d c →
        iform (kacE7.extRoot (P.get c)) (kacE7.extRoot (P.get d)) = 0) ∧
      ∀ c d : Fin P.length, edgeE P.length c d →
        (nodeIdx (P.get c), nodeIdx (P.get d)) ∈ e7EdgeIdx := by
  rw [kacE7_extRoot]
  exact e7_etrees_raw

theorem e7_elen : ∀ P ∈ e7ETrees, P.length = 6 ∨ P.length = 7 ∨ P.length = 8 := by
  decide

section E7Rat


theorem rationalLieType_of_eClass_E7 {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ}
    (S : LangSetup Tag.E7 L p₀) (hp : p.Prime) (hpL : (p : L) ≠ 0)
    {a : Fin Tag.E7.rank → Lˣ} (hTor : rootDiagUnit Tag.E7 a ∈ S.D.torus)
    (hTp : rootDiagUnit Tag.E7 a ^ p = 1) (i : KernelComponent (rootCharHom a))
    (h6 : 6 ≤ compRank (componentRoots (rootCharHom a) i))
    (hn : (componentRoots (rootCharHom a) i).ncard =
      eRootCount (compRank (componentRoots (rootCharHom a) i)))
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E7.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    RationalLieType (ringChar L) (rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
  rationalLieType_of_eClass (Or.inr (Or.inr (Or.inl rfl))) kacE7 facts_E7 e7_tree e7_adj e7_check e7_lt
    e7_card e7_ecount e7_etrees e7_elen (fun {F} _ x y h => e7_frames x y h) S hp hpL hTor hTp i
    h6 hn hinner

end E7Rat

@[expose] def e8ETreesRaw : List (List (Option (Fin 8))) :=
  [[some 0, some 1, some 2, some 3, some 4, some 5],
    [some 0, some 1, some 2, some 3, some 4, some 5, some 6],
    [some 0, some 1, some 2, some 3, some 4, some 5, some 6, some 7]]

@[expose] def e8ETrees : List (List (Option (Fin Tag.E8.rank))) := e8ETreesRaw

theorem e8_ecount_raw : ∀ c ∈ e8Conn, 6 ≤ c.length →
    kacCount Tag.E8 ![2, 3, 4, 6, 5, 4, 3, 2] (c.map (idxNode (r := Tag.E8.rank))).toFinset =
      eRootCount c.length → ∃ P ∈ e8ETrees, sameSet c (P.map nodeIdx) = true := by
  decide +kernel

theorem e8_ecount : ∀ c ∈ e8Conn, 6 ≤ c.length →
    kacCount Tag.E8 kacE8.θ (c.map (idxNode (r := Tag.E8.rank))).toFinset =
      eRootCount c.length → ∃ P ∈ e8ETrees, sameSet c (P.map nodeIdx) = true :=
  e8_ecount_raw

theorem e8_etrees_raw : ∀ P ∈ e8ETreesRaw, P.Nodup ∧ 6 ≤ P.length ∧
    (∀ c d : Fin P.length, c ≠ d → ¬ edgeE P.length c d → ¬ edgeE P.length d c →
      iform (e8ExtVec (P.get c)) (e8ExtVec (P.get d)) = 0) ∧
    ∀ c d : Fin P.length, edgeE P.length c d →
      (nodeIdx (P.get c), nodeIdx (P.get d)) ∈ e8EdgeIdx := by
  decide +kernel

theorem e8_etrees :
    ∀ P ∈ e8ETrees, P.Nodup ∧ 6 ≤ P.length ∧
      (∀ c d : Fin P.length, c ≠ d → ¬ edgeE P.length c d → ¬ edgeE P.length d c →
        iform (kacE8.extRoot (P.get c)) (kacE8.extRoot (P.get d)) = 0) ∧
      ∀ c d : Fin P.length, edgeE P.length c d →
        (nodeIdx (P.get c), nodeIdx (P.get d)) ∈ e8EdgeIdx := by
  rw [kacE8_extRoot]
  exact e8_etrees_raw

theorem e8_elen : ∀ P ∈ e8ETrees, P.length = 6 ∨ P.length = 7 ∨ P.length = 8 := by
  decide

section E8Rat


theorem rationalLieType_of_eClass_E8 {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ}
    (S : LangSetup Tag.E8 L p₀) (hp : p.Prime) (hpL : (p : L) ≠ 0)
    {a : Fin Tag.E8.rank → Lˣ} (hTor : rootDiagUnit Tag.E8 a ∈ S.D.torus)
    (hTp : rootDiagUnit Tag.E8 a ^ p = 1) (i : KernelComponent (rootCharHom a))
    (h6 : 6 ≤ compRank (componentRoots (rootCharHom a) i))
    (hn : (componentRoots (rootCharHom a) i).ncard =
      eRootCount (compRank (componentRoots (rootCharHom a) i)))
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E8.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    RationalLieType (ringChar L) (rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
  rationalLieType_of_eClass (Or.inr (Or.inr (Or.inr rfl))) kacE8 facts_E8 e8_tree e8_adj e8_check e8_lt
    e8_card e8_ecount e8_etrees e8_elen (fun {F} _ x y h => e8_frames x y h) S hp hpL hTor hTp i
    h6 hn hinner

end E8Rat

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
