module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1OmCSub
public import CFSG.RankThree.PartOne.K159.RowFourType
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.RankThree.PartOne.KC.OrthogonalFixedBlock
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC

open QuadraticMap Module CFSG.ClassicalGroups.Orthogonal CFSG.Open CFSG.GroupTheory.WeirSylow
  CFSG.RankThree.PartOne.K159
open scoped commutatorElement

section TypeCalc

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}

theorem Q_eq_one_of_mem_planeSpan {p : V × V} (hp : MinusPair Q p.1 p.2) {x : V}
    (hx : x ∈ planeSpan p) (hx0 : x ≠ 0) : Q x = 1 := by
  obtain ⟨c, d, rfl⟩ := (mem_planeSpan_iff p x).1 hx
  have hcd : c ≠ 0 ∨ d ≠ 0 := by
    by_contra hno
    push Not at hno
    obtain ⟨rfl, rfl⟩ := hno
    exact hx0 (by simp)
  have key : ∀ c d : ZMod 2, (c ≠ 0 ∨ d ≠ 0) → c * c + d * d + c * d = 1 := by decide
  rw [QuadraticMap.map_add Q, QuadraticMap.map_smul, QuadraticMap.map_smul, polar_smul_left,
    polar_smul_right, hp.qa, hp.qb, hp.ab]
  simp only [smul_eq_mul, mul_one]
  exact key c d hcd

theorem nondeg_comp_subtype {S : Submodule (ZMod 2) V}
    (h : ∀ x ∈ S, (∀ y ∈ S, polar Q x y = 0) → x = 0) :
    (QuadraticMap.polarBilin (Q.comp S.subtype)).Nondegenerate := by
  have key : ∀ a b : S, polarBilin (Q.comp S.subtype) a b = polar Q (a : V) (b : V) := by
    intro a b
    rw [QuadraticMap.polarBilin_apply_apply]
    exact polar_comp_subtype S a b
  constructor
  · intro x hx
    refine Subtype.ext (h x x.2 (fun y hy => ?_))
    have := hx ⟨y, hy⟩
    rwa [key] at this
  · intro y hy
    refine Subtype.ext (h y y.2 (fun x hx => ?_))
    have := hy ⟨x, hx⟩
    rw [key] at this
    rw [polar_comm]
    exact this

theorem nondeg_planeSpan {p : V × V} (hp : MinusPair Q p.1 p.2) :
    (QuadraticMap.polarBilin (Q.comp (planeSpan p).subtype)).Nondegenerate :=
  nondeg_comp_subtype (fun x hx hxy => hp.eq_zero_of_mem_planeSpan_of_mem_perp hx
    ((mem_perpPlane_iff' p x).2 ⟨hxy _ (left_mem_planeSpan p), hxy _ (right_mem_planeSpan p)⟩))

theorem not_isPlusType_planeSpan {p : V × V} (hp : MinusPair Q p.1 p.2) :
    ¬ IsPlusType (Q.comp (planeSpan p).subtype) := by
  rintro ⟨W', hW', hQ⟩
  have h2 := hp.finrank_planeSpan
  have h1 : finrank (ZMod 2) W' = 1 := by omega
  have hne : W' ≠ ⊥ := by
    rintro rfl
    simp at h1
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have h0 := hQ w hw
  rw [QuadraticMap.comp_apply] at h0
  have h1 := Q_eq_one_of_mem_planeSpan hp w.2 (fun h => hw0 (Subtype.ext h))
  simp only [Submodule.subtype_apply] at h0
  rw [h0] at h1
  exact zero_ne_one h1

theorem isPlusType_sup_iff [FiniteDimensional (ZMod 2) V] {A B : Submodule (ZMod 2) V}
    (hdisj : Disjoint A B) (horth : ∀ a ∈ A, ∀ b ∈ B, polar Q a b = 0)
    (hA : (QuadraticMap.polarBilin (Q.comp A.subtype)).Nondegenerate)
    (hB : (QuadraticMap.polarBilin (Q.comp B.subtype)).Nondegenerate) {d₁ d₂ : ℕ}
    (hd₁ : 1 ≤ d₁) (hd₂ : 1 ≤ d₂) (h₁ : finrank (ZMod 2) A = 2 * d₁)
    (h₂ : finrank (ZMod 2) B = 2 * d₂) :
    IsPlusType (Q.comp (A ⊔ B).subtype) ↔
      (IsPlusType (Q.comp A.subtype) ↔ IsPlusType (Q.comp B.subtype)) := by
  rw [isPlusType_congr (isometryEquivSup Q A B hdisj horth)]
  exact isPlusType_prod_iff hA hB hd₁ hd₂ h₁ h₂

theorem polar_planeSpan_Wspan {p : V × V} {l : List (V × V)} (hperp : ∀ q ∈ l, PairPerp Q p q)
    {a b : V} (ha : a ∈ planeSpan p) (hb : b ∈ Wspan l) : polar Q a b = 0 := by
  obtain ⟨c, d, rfl⟩ := (mem_planeSpan_iff p a).1 ha
  obtain ⟨e1, e2⟩ := polar_Wspan_eq_zero hperp hb
  rw [polar_add_left, polar_smul_left, polar_smul_left, e1, e2]
  simp

theorem nondeg_Wspan {l : List (V × V)} (hl : IsFrame Q l) :
    (QuadraticMap.polarBilin (Q.comp (Wspan l).subtype)).Nondegenerate := by
  refine nondeg_comp_subtype (fun x hx hxy => hl.eq_zero_of_mem_Wspan_of_mem_perpL hx ?_)
  rw [mem_perpL_iff]
  intro q hq
  have h1 := hxy _ (planeSpan_le_Wspan hq (left_mem_planeSpan q))
  have h2 := hxy _ (planeSpan_le_Wspan hq (right_mem_planeSpan q))
  exact ⟨by rw [polar_comm]; exact h1, by rw [polar_comm]; exact h2⟩

theorem isPlusType_Wspan_iff [FiniteDimensional (ZMod 2) V] {l : List (V × V)}
    (hl : IsFrame Q l) : IsPlusType (Q.comp (Wspan l).subtype) ↔ Even l.length := by
  induction l with
  | nil =>
    haveI : Subsingleton (Wspan ([] : List (V × V))) := by
      rw [Wspan_nil]
      infer_instance
    exact iff_of_true (isPlusType_of_subsingleton _) (by simp)
  | cons p l ih =>
    obtain ⟨hp, hperp, hl'⟩ := isFrame_cons.1 hl
    rw [Wspan_cons]
    by_cases hnil : l = []
    · subst hnil
      rw [Wspan_nil, sup_bot_eq, isPlusType_congr (isometryOfEq Q (rfl : planeSpan p = planeSpan p))]
      exact iff_of_false (not_isPlusType_planeSpan hp) (by simp)
    · have hlen : 1 ≤ l.length := List.length_pos_iff.2 hnil
      rw [isPlusType_sup_iff (IsFrame.disjoint_planeSpan_Wspan hp hperp)
        (fun a ha b hb => polar_planeSpan_Wspan hperp ha hb) (nondeg_planeSpan hp)
        (nondeg_Wspan hl') (le_refl 1) hlen (by rw [hp.finrank_planeSpan]) hl'.finrank_Wspan,
        ih hl', List.length_cons, Nat.even_add_one]
      have hpl := not_isPlusType_planeSpan hp
      tauto

end TypeCalc

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC

end
