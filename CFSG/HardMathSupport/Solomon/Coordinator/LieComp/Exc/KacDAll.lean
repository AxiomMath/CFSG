module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.KacD
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUD4
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

@[expose] def d4DTreesRaw : List (List (Option (Fin 4))) :=
  [[none, some 2, some 0, some 1],
    [none, some 2, some 0, some 3],
    [none, some 2, some 1, some 3],
    [some 0, some 2, some 1, some 3]]

@[expose] def d4DTrees : List (List (Option (Fin Tag.D4.rank))) := d4DTreesRaw

theorem d4_dcount_raw : ∀ c ∈ d4Conn, 4 ≤ c.length →
    kacCount Tag.D4 ![1, 1, 2, 1] (c.map (idxNode (r := Tag.D4.rank))).toFinset =
      2 * c.length * (c.length - 1) → ∃ P ∈ d4DTrees, sameSet c (P.map nodeIdx) = true := by
  decide +kernel

theorem d4_dcount : ∀ c ∈ d4Conn, 4 ≤ c.length →
    kacCount Tag.D4 kacD4.θ (c.map (idxNode (r := Tag.D4.rank))).toFinset =
      2 * c.length * (c.length - 1) → ∃ P ∈ d4DTrees, sameSet c (P.map nodeIdx) = true :=
  d4_dcount_raw

theorem d4_dtrees_raw : ∀ P ∈ d4DTreesRaw, P.Nodup ∧ 4 ≤ P.length ∧
    (∀ c d : Fin P.length, c ≠ d → ¬ edgeD P.length c d → ¬ edgeD P.length d c →
      iform (d4ExtVec (P.get c)) (d4ExtVec (P.get d)) = 0) ∧
    ∀ c d : Fin P.length, edgeD P.length c d →
      (nodeIdx (P.get c), nodeIdx (P.get d)) ∈ d4EdgeIdx := by
  decide +kernel

theorem d4_dtrees :
    ∀ P ∈ d4DTrees, P.Nodup ∧ 4 ≤ P.length ∧
      (∀ c d : Fin P.length, c ≠ d → ¬ edgeD P.length c d → ¬ edgeD P.length d c →
        iform (kacD4.extRoot (P.get c)) (kacD4.extRoot (P.get d)) = 0) ∧
      ∀ c d : Fin P.length, edgeD P.length c d →
        (nodeIdx (P.get c), nodeIdx (P.get d)) ∈ d4EdgeIdx := by
  rw [kacD4_extRoot]
  exact d4_dtrees_raw

section D4Rat


theorem rationalLieType_of_dClass_D4 {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ}
    (S : LangSetup Tag.D4 L p₀) (hp : p.Prime) (hpL : (p : L) ≠ 0)
    {a : Fin Tag.D4.rank → Lˣ} (hTor : rootDiagUnit Tag.D4 a ∈ S.D.torus)
    (hTp : rootDiagUnit Tag.D4 a ^ p = 1) (i : KernelComponent (rootCharHom a))
    (h4 : 4 ≤ compRank (componentRoots (rootCharHom a) i))
    (hn : (componentRoots (rootCharHom a) i).ncard =
      2 * compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) - 1))
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.D4.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    RationalLieType (ringChar L) (rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
  rationalLieType_of_dClass (Or.inl rfl) kacD4 facts_D4 d4_tree d4_adj d4_check d4_lt
    d4_card d4_dcount d4_dtrees (fun {F} _ x y h => d4_frames x y h) S hp hpL hTor hTp i h4 hn
    hinner

end D4Rat

@[expose] def e6DTreesRaw : List (List (Option (Fin 6))) :=
  [[some 1, some 3, some 2, some 4],
    [none, some 1, some 3, some 2, some 4],
    [some 0, some 2, some 3, some 1, some 4],
    [some 5, some 4, some 3, some 1, some 2]]

@[expose] def e6DTrees : List (List (Option (Fin Tag.E6.rank))) := e6DTreesRaw

theorem e6_dcount_raw : ∀ c ∈ e6Conn, 4 ≤ c.length →
    kacCount Tag.E6 ![1, 2, 2, 3, 2, 1] (c.map (idxNode (r := Tag.E6.rank))).toFinset =
      2 * c.length * (c.length - 1) → ∃ P ∈ e6DTrees, sameSet c (P.map nodeIdx) = true := by
  decide +kernel

theorem e6_dcount : ∀ c ∈ e6Conn, 4 ≤ c.length →
    kacCount Tag.E6 kacE6.θ (c.map (idxNode (r := Tag.E6.rank))).toFinset =
      2 * c.length * (c.length - 1) → ∃ P ∈ e6DTrees, sameSet c (P.map nodeIdx) = true :=
  e6_dcount_raw

theorem e6_dtrees_raw : ∀ P ∈ e6DTreesRaw, P.Nodup ∧ 4 ≤ P.length ∧
    (∀ c d : Fin P.length, c ≠ d → ¬ edgeD P.length c d → ¬ edgeD P.length d c →
      iform (e6ExtVec (P.get c)) (e6ExtVec (P.get d)) = 0) ∧
    ∀ c d : Fin P.length, edgeD P.length c d →
      (nodeIdx (P.get c), nodeIdx (P.get d)) ∈ e6EdgeIdx := by
  decide +kernel

theorem e6_dtrees :
    ∀ P ∈ e6DTrees, P.Nodup ∧ 4 ≤ P.length ∧
      (∀ c d : Fin P.length, c ≠ d → ¬ edgeD P.length c d → ¬ edgeD P.length d c →
        iform (kacE6.extRoot (P.get c)) (kacE6.extRoot (P.get d)) = 0) ∧
      ∀ c d : Fin P.length, edgeD P.length c d →
        (nodeIdx (P.get c), nodeIdx (P.get d)) ∈ e6EdgeIdx := by
  rw [kacE6_extRoot]
  exact e6_dtrees_raw

section E6Rat


theorem rationalLieType_of_dClass_E6 {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ}
    (S : LangSetup Tag.E6 L p₀) (hp : p.Prime) (hpL : (p : L) ≠ 0)
    {a : Fin Tag.E6.rank → Lˣ} (hTor : rootDiagUnit Tag.E6 a ∈ S.D.torus)
    (hTp : rootDiagUnit Tag.E6 a ^ p = 1) (i : KernelComponent (rootCharHom a))
    (h4 : 4 ≤ compRank (componentRoots (rootCharHom a) i))
    (hn : (componentRoots (rootCharHom a) i).ncard =
      2 * compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) - 1))
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    RationalLieType (ringChar L) (rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
  rationalLieType_of_dClass (Or.inr (Or.inl rfl)) kacE6 facts_E6 e6_tree e6_adj e6_check e6_lt
    e6_card e6_dcount e6_dtrees (fun {F} _ x y h => e6_frames x y h) S hp hpL hTor hTp i h4 hn
    hinner

end E6Rat

@[expose] def e7DTreesRaw : List (List (Option (Fin 7))) :=
  [[some 1, some 3, some 2, some 4],
    [some 0, some 2, some 3, some 1, some 4],
    [none, some 0, some 2, some 3, some 1, some 4],
    [some 5, some 4, some 3, some 1, some 2],
    [some 6, some 5, some 4, some 3, some 1, some 2]]

@[expose] def e7DTrees : List (List (Option (Fin Tag.E7.rank))) := e7DTreesRaw

theorem e7_dcount_raw : ∀ c ∈ e7Conn, 4 ≤ c.length →
    kacCount Tag.E7 ![2, 2, 3, 4, 3, 2, 1] (c.map (idxNode (r := Tag.E7.rank))).toFinset =
      2 * c.length * (c.length - 1) → ∃ P ∈ e7DTrees, sameSet c (P.map nodeIdx) = true := by
  decide +kernel

theorem e7_dcount : ∀ c ∈ e7Conn, 4 ≤ c.length →
    kacCount Tag.E7 kacE7.θ (c.map (idxNode (r := Tag.E7.rank))).toFinset =
      2 * c.length * (c.length - 1) → ∃ P ∈ e7DTrees, sameSet c (P.map nodeIdx) = true :=
  e7_dcount_raw

theorem e7_dtrees_raw : ∀ P ∈ e7DTreesRaw, P.Nodup ∧ 4 ≤ P.length ∧
    (∀ c d : Fin P.length, c ≠ d → ¬ edgeD P.length c d → ¬ edgeD P.length d c →
      iform (e7ExtVec (P.get c)) (e7ExtVec (P.get d)) = 0) ∧
    ∀ c d : Fin P.length, edgeD P.length c d →
      (nodeIdx (P.get c), nodeIdx (P.get d)) ∈ e7EdgeIdx := by
  decide +kernel

theorem e7_dtrees :
    ∀ P ∈ e7DTrees, P.Nodup ∧ 4 ≤ P.length ∧
      (∀ c d : Fin P.length, c ≠ d → ¬ edgeD P.length c d → ¬ edgeD P.length d c →
        iform (kacE7.extRoot (P.get c)) (kacE7.extRoot (P.get d)) = 0) ∧
      ∀ c d : Fin P.length, edgeD P.length c d →
        (nodeIdx (P.get c), nodeIdx (P.get d)) ∈ e7EdgeIdx := by
  rw [kacE7_extRoot]
  exact e7_dtrees_raw

section E7Rat


theorem rationalLieType_of_dClass_E7 {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ}
    (S : LangSetup Tag.E7 L p₀) (hp : p.Prime) (hpL : (p : L) ≠ 0)
    {a : Fin Tag.E7.rank → Lˣ} (hTor : rootDiagUnit Tag.E7 a ∈ S.D.torus)
    (hTp : rootDiagUnit Tag.E7 a ^ p = 1) (i : KernelComponent (rootCharHom a))
    (h4 : 4 ≤ compRank (componentRoots (rootCharHom a) i))
    (hn : (componentRoots (rootCharHom a) i).ncard =
      2 * compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) - 1))
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E7.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    RationalLieType (ringChar L) (rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
  rationalLieType_of_dClass (Or.inr (Or.inr (Or.inl rfl))) kacE7 facts_E7 e7_tree e7_adj e7_check e7_lt
    e7_card e7_dcount e7_dtrees (fun {F} _ x y h => e7_frames x y h) S hp hpL hTor hTp i h4 hn
    hinner

end E7Rat

@[expose] def e8DTreesRaw : List (List (Option (Fin 8))) :=
  [[some 1, some 3, some 2, some 4],
    [some 0, some 2, some 3, some 1, some 4],
    [some 5, some 4, some 3, some 1, some 2],
    [some 6, some 5, some 4, some 3, some 1, some 2],
    [some 7, some 6, some 5, some 4, some 3, some 1, some 2],
    [none, some 7, some 6, some 5, some 4, some 3, some 1, some 2]]

@[expose] def e8DTrees : List (List (Option (Fin Tag.E8.rank))) := e8DTreesRaw

theorem e8_dcount_raw : ∀ c ∈ e8Conn, 4 ≤ c.length →
    kacCount Tag.E8 ![2, 3, 4, 6, 5, 4, 3, 2] (c.map (idxNode (r := Tag.E8.rank))).toFinset =
      2 * c.length * (c.length - 1) → ∃ P ∈ e8DTrees, sameSet c (P.map nodeIdx) = true := by
  decide +kernel

theorem e8_dcount : ∀ c ∈ e8Conn, 4 ≤ c.length →
    kacCount Tag.E8 kacE8.θ (c.map (idxNode (r := Tag.E8.rank))).toFinset =
      2 * c.length * (c.length - 1) → ∃ P ∈ e8DTrees, sameSet c (P.map nodeIdx) = true :=
  e8_dcount_raw

theorem e8_dtrees_raw : ∀ P ∈ e8DTreesRaw, P.Nodup ∧ 4 ≤ P.length ∧
    (∀ c d : Fin P.length, c ≠ d → ¬ edgeD P.length c d → ¬ edgeD P.length d c →
      iform (e8ExtVec (P.get c)) (e8ExtVec (P.get d)) = 0) ∧
    ∀ c d : Fin P.length, edgeD P.length c d →
      (nodeIdx (P.get c), nodeIdx (P.get d)) ∈ e8EdgeIdx := by
  decide +kernel

theorem e8_dtrees :
    ∀ P ∈ e8DTrees, P.Nodup ∧ 4 ≤ P.length ∧
      (∀ c d : Fin P.length, c ≠ d → ¬ edgeD P.length c d → ¬ edgeD P.length d c →
        iform (kacE8.extRoot (P.get c)) (kacE8.extRoot (P.get d)) = 0) ∧
      ∀ c d : Fin P.length, edgeD P.length c d →
        (nodeIdx (P.get c), nodeIdx (P.get d)) ∈ e8EdgeIdx := by
  rw [kacE8_extRoot]
  exact e8_dtrees_raw

section E8Rat


theorem rationalLieType_of_dClass_E8 {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ}
    (S : LangSetup Tag.E8 L p₀) (hp : p.Prime) (hpL : (p : L) ≠ 0)
    {a : Fin Tag.E8.rank → Lˣ} (hTor : rootDiagUnit Tag.E8 a ∈ S.D.torus)
    (hTp : rootDiagUnit Tag.E8 a ^ p = 1) (i : KernelComponent (rootCharHom a))
    (h4 : 4 ≤ compRank (componentRoots (rootCharHom a) i))
    (hn : (componentRoots (rootCharHom a) i).ncard =
      2 * compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) - 1))
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E8.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    RationalLieType (ringChar L) (rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
  rationalLieType_of_dClass (Or.inr (Or.inr (Or.inr rfl))) kacE8 facts_E8 e8_tree e8_adj e8_check e8_lt
    e8_card e8_dcount e8_dtrees (fun {F} _ x y h => e8_frames x y h) S hp hpL hTor hTp i h4 hn
    hinner

end E8Rat

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
