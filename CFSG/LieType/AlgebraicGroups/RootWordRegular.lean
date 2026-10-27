module

public import CFSG.LieType.AlgebraicGroups.GLCoordPoints
public import CFSG.LieType.AlgebraicGroups.ZariskiPoints
public import CFSG.LieType.AlgebraicGroups.TorusAffineDomain
public import CFSG.LieType.Chevalley.RootPairCommonField
public import CFSG.LieType.Chevalley.Canonical
public import CFSG.LieType.Steinberg.Adjoint.BaseChange
public import Mathlib.Algebra.Polynomial.AlgebraMap

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint WithConv

@[expose] def modGLPoint (τ : Tag) (k : Type) [Field k] :
    ModGL τ k ≃* WithConv (GLCoord k (Label τ) →ₐ[k] k) :=
  (modGLEquivGL τ k).trans glPointEquiv

variable {k : Type} [Field k]

theorem GLCoord.algHom_ext_of_entries {ι : Type} [Fintype ι] [DecidableEq ι] {A : Type}
    [CommRing A] [Algebra k A] {f g : GLCoord k ι →ₐ[k] A}
    (hx : ∀ i j, f (glEntry k ι i j) = g (glEntry k ι i j)) : f = g := by
  refine GLCoord.algHom_ext k ι hx ?_
  have hdet : f (glEntryMatrix k ι).det = g (glEntryMatrix k ι).det := by
    rw [GLCoord.map_det, GLCoord.map_det]
    simp only [hx]
  have hf := congrArg f (det_glEntryMatrix_mul_glDetInv k ι)
  have hg := congrArg g (det_glEntryMatrix_mul_glDetInv k ι)
  rw [map_mul, map_one] at hf hg
  rw [hdet] at hf
  calc f (glDetInv k ι) = f (glDetInv k ι) * (g (glEntryMatrix k ι).det * g (glDetInv k ι)) := by
        rw [hg, mul_one]
    _ = (g (glEntryMatrix k ι).det * f (glDetInv k ι)) * g (glDetInv k ι) := by ring
    _ = g (glDetInv k ι) := by rw [hf, one_mul]

variable {τ : Tag} {D : Type} [CommRing D] [Algebra k D]

variable (τ) in
@[expose] def endMatrix
    (A : Module.End D (RootModule τ D)) : Matrix (Label τ) (Label τ) D :=
  LinearMap.toMatrixAlgEquiv Finsupp.basisSingleOne A

theorem endMatrix_apply
    (A : Module.End D (RootModule τ D)) (a b : Label τ) :
    endMatrix τ A a b = A (Finsupp.single b 1) a := by
  simp [endMatrix, LinearMap.toMatrixAlgEquiv_apply]

theorem det_endMatrix_mul_inv (g : (Module.End D (RootModule τ D))ˣ) :
    (endMatrix τ (g : Module.End D (RootModule τ D))).det *
      (endMatrix τ ((g⁻¹ : (Module.End D (RootModule τ D))ˣ) :
        Module.End D (RootModule τ D))).det = 1 := by
  rw [← Matrix.det_mul]
  unfold endMatrix
  rw [← map_mul, Units.mul_inv, map_one, Matrix.det_one]

variable (k) in
@[expose] def unitCo
    (g : (Module.End D (RootModule τ D))ˣ) : GLCoord k (Label τ) →ₐ[k] D :=
  GLCoord.lift k (Label τ) (endMatrix τ (g : Module.End D (RootModule τ D))) _
    (det_endMatrix_mul_inv g)

theorem modGLPoint_apply_glEntry (g : ModGL τ k) (a b : Label τ) :
    (modGLPoint τ k g).ofConv (glEntry k (Label τ) a b) =
      (g : Module.End k (RootModule τ k)) (Finsupp.single b 1) a := by
  simp [modGLPoint]

theorem comp_unitCo_of_baseChange
    (z : D →ₐ[k] k) (g : (Module.End D (RootModule τ D))ˣ)
    (g' : ModGL τ k)
    (h : BaseChange (z : D →+* k) (g : Module.End D (RootModule τ D))
      (g' : Module.End k (RootModule τ k))) :
    z.comp (unitCo k g) = (modGLPoint τ k g').ofConv := by
  refine GLCoord.algHom_ext_of_entries fun a b => ?_
  rw [AlgHom.comp_apply, unitCo, GLCoord.lift_glEntry, endMatrix_apply, modGLPoint_apply_glEntry,
    ← h b, Finsupp.mapRange_apply]
  rfl

abbrev Letter (τ : Tag) : Type := Fin τ.rank × Bool

variable (τ) in
@[expose] def letterUnit
    (R : Type) [CommRing R] (l : Letter τ) (c : R) :
    (Module.End R (RootModule τ R))ˣ :=
  if l.2 then xUnit τ R l.1 c else yUnit τ R l.1 c

variable (τ) in
@[expose] def wordUnit
    (R : Type) [CommRing R] (w : List (Letter τ × R)) :
    (Module.End R (RootModule τ R))ˣ :=
  (w.map fun p => letterUnit τ R p.1 p.2).prod

section Words

variable {R S : Type} [CommRing R] [CommRing S]

theorem wordUnit_nil
    : wordUnit τ R [] = 1 :=
  rfl

theorem wordUnit_cons
    (p : Letter τ × R) (w : List (Letter τ × R)) :
    wordUnit τ R (p :: w) = letterUnit τ R p.1 p.2 * wordUnit τ R w := by
  simp [wordUnit]

theorem wordUnit_append
    (w w' : List (Letter τ × R)) :
    wordUnit τ R (w ++ w') = wordUnit τ R w * wordUnit τ R w' := by
  simp [wordUnit]

theorem wordUnit_flatten
    (L : List (List (Letter τ × R))) :
    wordUnit τ R L.flatten = (L.map (wordUnit τ R)).prod := by
  induction L with
  | nil => rfl
  | cons w L ih => rw [List.flatten_cons, wordUnit_append, ih, List.map_cons, List.prod_cons]

theorem letterUnit_zero
    (l : Letter τ) : letterUnit τ R l 0 = 1 := by
  unfold letterUnit
  split_ifs
  · exact Units.ext (by rw [coe_xUnit, Units.val_one]; exact xOp_zero _)
  · exact Units.ext (by rw [coe_yUnit, Units.val_one]; exact yOp_zero _)

theorem letterUnit_neg
    (l : Letter τ) (c : R) : letterUnit τ R l (-c) = (letterUnit τ R l c)⁻¹ := by
  unfold letterUnit
  split_ifs
  · exact Units.ext (by rw [coe_xUnit, coe_xUnit_inv])
  · exact Units.ext (by rw [coe_yUnit, coe_yUnit_inv])

@[expose] def mapWord (f : R →+* S) (w : List (Letter τ × R)) : List (Letter τ × S) :=
  w.map fun p => (p.1, f p.2)

theorem mapWord_cons (f : R →+* S) (p : Letter τ × R) (w : List (Letter τ × R)) :
    mapWord f (p :: w) = (p.1, f p.2) :: mapWord f w :=
  rfl

theorem mapWord_append (f : R →+* S) (w w' : List (Letter τ × R)) :
    mapWord f (w ++ w') = mapWord f w ++ mapWord f w' :=
  List.map_append

theorem mapWord_flatten (f : R →+* S) (L : List (List (Letter τ × R))) :
    mapWord f L.flatten = (L.map (mapWord f)).flatten :=
  List.map_flatten ..

theorem baseChange_letterUnit
    (f : R →+* S) (l : Letter τ) (c : R) :
    BaseChange f (letterUnit τ R l c : Module.End R (RootModule τ R))
      (letterUnit τ S l (f c) : Module.End S (RootModule τ S)) := by
  unfold letterUnit
  split_ifs
  · rw [coe_xUnit, coe_xUnit]
    exact BaseChange.xOp _ _
  · rw [coe_yUnit, coe_yUnit]
    exact BaseChange.yOp _ _

theorem baseChange_wordUnit
    (f : R →+* S) (w : List (Letter τ × R)) :
    BaseChange f (wordUnit τ R w : Module.End R (RootModule τ R))
      (wordUnit τ S (mapWord f w) : Module.End S (RootModule τ S)) := by
  induction w with
  | nil => exact BaseChange.one
  | cons p w ih =>
    rw [mapWord, List.map_cons, ← mapWord, wordUnit_cons, wordUnit_cons, Units.val_mul,
      Units.val_mul]
    exact (baseChange_letterUnit f p.1 p.2).mul ih

variable (τ R) in
@[expose] def weylWord (i : Fin τ.rank) : List (Letter τ × R) :=
  [((i, true), 1), ((i, false), -1), ((i, true), 1)]

variable (τ R) in
@[expose] def weylInvWord (i : Fin τ.rank) : List (Letter τ × R) :=
  [((i, true), -1), ((i, false), 1), ((i, true), -1)]

variable (τ R) in
@[expose] def torusWord (i : Fin τ.rank) (u : Rˣ) : List (Letter τ × R) :=
  [((i, true), (u : R)), ((i, false), -((u⁻¹ : Rˣ) : R)), ((i, true), (u : R)),
    ((i, true), -1), ((i, false), 1), ((i, true), -1)]

variable (τ R) in
@[expose] def pinnedWord
    (α : Fin τ.rank → ℤ) (c : R) : List (Letter τ × R) :=
  ((pinnedData τ α).2.1.reverse.map fun i => weylWord τ R (τ.idx i)).flatten ++
    [(((pinnedData τ α).1, true), (pinnedData τ α).2.2 • c)] ++
    ((pinnedData τ α).2.1.map fun i => weylInvWord τ R (τ.idx i)).flatten

variable (τ R) in
@[expose] def canonicalWord
    (w : WeylGroup τ) : List (Letter τ × R) :=
  (((coxeterSystem τ).exists_isReduced w).choose.map (weylWord τ R)).flatten

theorem wordUnit_weylWord
    (i : Fin τ.rank) : wordUnit τ R (weylWord τ R i) = weylElt τ R i 1 := by
  refine Units.ext ?_
  simp [wordUnit, weylWord, letterUnit, coe_weylElt, coe_xUnit, coe_yUnit, mul_assoc]

theorem wordUnit_weylInvWord
    (i : Fin τ.rank) :
    wordUnit τ R (weylInvWord τ R i) = (weylElt τ R i 1)⁻¹ := by
  refine Units.ext ?_
  simp [wordUnit, weylInvWord, letterUnit, coe_weylElt_inv, coe_xUnit, coe_yUnit, mul_assoc]

theorem wordUnit_torusWord
    (i : Fin τ.rank) (u : Rˣ) :
    wordUnit τ R (torusWord τ R i u) = torusElt τ R i u := by
  refine Units.ext ?_
  simp [wordUnit, torusWord, letterUnit, coe_torusElt, coe_weylElt, coe_xUnit, coe_yUnit,
    mul_assoc]

theorem wordUnit_pinnedWord
    (α : Fin τ.rank → ℤ) (c : R) :
    wordUnit τ R (pinnedWord τ R α c) = pinnedX τ R α c := by
  rw [pinnedWord, wordUnit_append, wordUnit_append, wordUnit_flatten, wordUnit_flatten,
    List.map_map, List.map_map, pinnedX, pinnedWeyl]
  have h1 : ((pinnedData τ α).2.1.reverse.map (wordUnit τ R ∘ fun i => weylWord τ R (τ.idx i))) =
      ((pinnedData τ α).2.1.map fun i => weylElt τ R (τ.idx i) 1).reverse := by
    rw [List.map_reverse]
    congr 1
    exact List.map_congr_left fun i _ => wordUnit_weylWord _
  have h2 : ((pinnedData τ α).2.1.map (wordUnit τ R ∘ fun i => weylInvWord τ R (τ.idx i))).prod =
      ((((pinnedData τ α).2.1.map fun i => weylElt τ R (τ.idx i) 1).reverse).prod)⁻¹ := by
    rw [List.prod_inv_reverse, List.map_reverse, List.reverse_reverse, List.map_map]
    congr 1
    exact List.map_congr_left fun i _ => wordUnit_weylInvWord _
  rw [h1, h2]
  congr 2

theorem wordUnit_canonicalWord
    (w : WeylGroup τ) :
    wordUnit τ R (canonicalWord τ R w) = canonicalRep (coxeterSystem τ) R w := by
  obtain ⟨hred, hw⟩ := ((coxeterSystem τ).exists_isReduced w).choose_spec
  rw [canonicalWord, wordUnit_flatten, List.map_map]
  conv_rhs => rw [hw]
  rw [canonicalRep_wordProd hred]
  congr 1
  exact List.map_congr_left fun i _ => wordUnit_weylWord i

theorem mapWord_weylWord (f : R →+* S) (i : Fin τ.rank) :
    mapWord f (weylWord τ R i) = weylWord τ S i := by
  simp [mapWord, weylWord]

theorem mapWord_weylInvWord (f : R →+* S) (i : Fin τ.rank) :
    mapWord f (weylInvWord τ R i) = weylInvWord τ S i := by
  simp [mapWord, weylInvWord]

theorem mapWord_torusWord (f : R →+* S) (i : Fin τ.rank) (u : Rˣ) :
    mapWord f (torusWord τ R i u) = torusWord τ S i (Units.map f.toMonoidHom u) := by
  simp [mapWord, torusWord]

theorem mapWord_pinnedWord
    (f : R →+* S) (α : Fin τ.rank → ℤ) (c : R) :
    mapWord f (pinnedWord τ R α c) = pinnedWord τ S α (f c) := by
  simp only [pinnedWord, mapWord_append, mapWord_flatten, List.map_map, Function.comp_def,
    mapWord_weylWord, mapWord_weylInvWord]
  simp [mapWord]

theorem mapWord_canonicalWord
    (f : R →+* S) (w : WeylGroup τ) :
    mapWord f (canonicalWord τ R w) = canonicalWord τ S w := by
  simp only [canonicalWord, mapWord_flatten, List.map_map]
  congr 1
  exact List.map_congr_left fun i _ => mapWord_weylWord f i

end Words

variable (τ) in
@[expose] def letterElt
    (l : Letter τ) (c : k) : adjointGroup τ k :=
  if l.2 then ⟨xUnit τ k l.1 c, xUnit_mem_adjointGroup l.1 c⟩
  else ⟨yUnit τ k l.1 c, yUnit_mem_adjointGroup l.1 c⟩

variable (τ) in
@[expose] def wordElt
    (w : List (Letter τ × k)) : adjointGroup τ k :=
  (w.map fun p => letterElt τ p.1 p.2).prod

theorem coe_letterElt
    (l : Letter τ) (c : k) :
    (letterElt τ l c : ModGL τ k) = letterUnit τ k l c := by
  unfold letterElt letterUnit
  split_ifs <;> rfl

theorem coe_wordElt
    (w : List (Letter τ × k)) : (wordElt τ w : ModGL τ k) = wordUnit τ k w := by
  induction w with
  | nil => rfl
  | cons p w ih =>
    rw [wordElt, List.map_cons, List.prod_cons, Subgroup.coe_mul, ← wordElt, ih, coe_letterElt,
      wordUnit_cons]

theorem wordElt_cons
    (p : Letter τ × k) (w : List (Letter τ × k)) :
    wordElt τ (p :: w) = letterElt τ p.1 p.2 * wordElt τ w := by
  rw [wordElt, List.map_cons, List.prod_cons, ← wordElt]

theorem letterElt_true
    (i : Fin τ.rank) (c : k) : letterElt τ (i, true) c = adjX τ k i c :=
  rfl

theorem letterElt_false
    (i : Fin τ.rank) (c : k) : letterElt τ (i, false) c = adjY τ k i c :=
  rfl

section Psi

variable {M : ℕ}

@[expose] def letterCo (φx φy : Fin τ.rank → (GLCoord k (Fin M) →ₐ[k] Polynomial k))
    (l : Letter τ) : GLCoord k (Fin M) →ₐ[k] Polynomial k :=
  if l.2 then φx l.1 else φy l.1

@[expose] def psiWordCo (φx φy : Fin τ.rank → (GLCoord k (Fin M) →ₐ[k] Polynomial k))
    (w : List (Letter τ × D)) : WithConv (GLCoord k (Fin M) →ₐ[k] D) :=
  (w.map fun p => toConv ((Polynomial.aeval p.2).comp (letterCo φx φy p.1))).prod

theorem comp_convOne {C : Type} [CommRing C] [Bialgebra k C] (z : D →ₐ[k] k) :
    toConv (z.comp (1 : WithConv (C →ₐ[k] D)).ofConv) = 1 := by
  rw [← TauCeti.AlgHom.mapValue_apply, map_one]

theorem point_psiWordCo
    (ψ : adjointGroup τ k →* Matrix.GeneralLinearGroup (Fin M) k)
    (φx φy : Fin τ.rank → (GLCoord k (Fin M) →ₐ[k] Polynomial k))
    (hx : ∀ i c, toConv ((Polynomial.aeval c).comp (φx i)) = glPointEquiv (ψ (adjX τ k i c)))
    (hy : ∀ i c, toConv ((Polynomial.aeval c).comp (φy i)) = glPointEquiv (ψ (adjY τ k i c)))
    (z : D →ₐ[k] k) (w : List (Letter τ × D)) :
    toConv (z.comp (psiWordCo φx φy w).ofConv) =
      glPointEquiv (ψ (wordElt τ (mapWord (z : D →+* k) w))) := by
  induction w with
  | nil =>
    rw [psiWordCo, List.map_nil, List.prod_nil, comp_convOne]
    simp [mapWord, wordElt]
  | cons p w ih =>
    rw [psiWordCo, List.map_cons, List.prod_cons, AlgHom.comp_convMul_distrib, toConv_ofConv,
      ← psiWordCo, ih, mapWord_cons, wordElt_cons, map_mul, map_mul]
    congr 1
    rw [ofConv_toConv, ← AlgHom.comp_assoc, ← Polynomial.aeval_algHom]
    rcases p with ⟨⟨i, b⟩, f⟩
    cases b
    · exact hy i (z f)
    · exact hx i (z f)

end Psi

end CFSG.LieType.AlgebraicGroups
