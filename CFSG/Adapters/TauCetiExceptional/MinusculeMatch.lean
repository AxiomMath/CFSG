module

public import CFSG.LieType.Steinberg.Minuscule.Group
public import TauCeti.Algebra.Lie.Presentation.MinusculeWeightTable.Basic
public import TauCeti.LinearAlgebra.Basis.DiagonalTorus.Basic

public noncomputable section

namespace CFSG.TauCetiBridge.Minuscule

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule

section Units

variable {τ : Tag} {D : MinData τ} (hV : D.Valid) (A : Type*) [CommRing A]

@[expose] def rootUnit
    (γ : Fin τ.rank → ℤ) (c : A) : (Module.End A (Fin D.d →₀ A))ˣ where
  val := 1 + c • D.rootOp A γ
  inv := 1 - c • D.rootOp A γ
  val_inv := one_add_mul_one_sub (by rw [smul_mul_smul_comm, hV.rootOp_mul_self, smul_zero])
  inv_val := one_sub_mul_one_add (by rw [smul_mul_smul_comm, hV.rootOp_mul_self, smul_zero])

theorem coe_rootUnit
    (γ : Fin τ.rank → ℤ) (c : A) :
    (rootUnit hV A γ c : Module.End A (Fin D.d →₀ A)) = 1 + c • D.rootOp A γ :=
  rfl

theorem rootUnit_eq_xu
    (k : Type*) [Field k] (γ : Fin τ.rank → ℤ) (c : k) :
    rootUnit hV k γ c = hV.xu k γ c :=
  rfl

theorem rootUnit_add
    (γ : Fin τ.rank → ℤ) (c c' : A) :
    rootUnit hV A γ (c + c') = rootUnit hV A γ c * rootUnit hV A γ c' := by
  ext1
  simp only [Units.val_mul, coe_rootUnit]
  rw [add_mul, one_mul, mul_add, mul_one, smul_mul_smul_comm, hV.rootOp_mul_self, smul_zero,
    add_zero, add_smul]
  abel

theorem rootUnit_zero
    (γ : Fin τ.rank → ℤ) : rootUnit hV A γ 0 = 1 := by
  ext1
  rw [coe_rootUnit, zero_smul, add_zero, Units.val_one]

variable {A} in
@[expose] def diagUnit
    {d : ℕ} (f : Fin d → Aˣ) : (Module.End A (Fin d →₀ A))ˣ where
  val := Finsupp.linearCombination A fun a => ((f a : Aˣ) : A) • Finsupp.single a 1
  inv := Finsupp.linearCombination A fun a => (((f a)⁻¹ : Aˣ) : A) • Finsupp.single a 1
  val_inv := ext_single fun a => by simp
  inv_val := ext_single fun a => by simp

variable {A} in
theorem diagUnit_single
    {d : ℕ} (f : Fin d → Aˣ) (a : Fin d) :
    (diagUnit f : Module.End A (Fin d →₀ A)) (Finsupp.single a 1) =
      ((f a : Aˣ) : A) • Finsupp.single a 1 := by
  simp [diagUnit]

variable {A} in
theorem diagUnit_mul
    {d : ℕ} (f g : Fin d → Aˣ) : diagUnit (f * g) = diagUnit f * diagUnit g := by
  refine Units.ext (ext_single fun a => ?_)
  rw [Units.val_mul, Module.End.mul_apply, diagUnit_single, diagUnit_single, map_smul,
    diagUnit_single, smul_smul, Pi.mul_apply, Units.val_mul, mul_comm]

theorem coe_diagUnit_eq_diagOp
    {k : Type*} [Field k] {d : ℕ} (f : Fin d → kˣ) :
    (diagUnit f : Module.End k (Fin d →₀ k)) = diagOp fun a => ((f a : kˣ) : k) :=
  ext_single fun a => by rw [diagUnit_single, diagOp_single]

end Units

section Field

variable {τ : Tag} {D : MinData τ} (hV : D.Valid) (k : Type*) [Field k]

theorem minGroup_le_of_simple
    {P : Subgroup (Module.End k (Fin D.d →₀ k))ˣ}
    (hP : ∀ (i : Fin τ.rank) (c : k),
      hV.xu k (Pi.single i 1) c ∈ P ∧ hV.xu k (-Pi.single i 1) c ∈ P) :
    hV.minGroup k ≤ P := by
  have hn : ∀ i, ((hV.nm k i : hV.minGroup k) : (Module.End k (Fin D.d →₀ k))ˣ) ∈ P := fun i =>
    mul_mem (mul_mem (hP i _).1 (hP i _).2) (hP i _).1
  have hx : ∀ γ, IsRoot τ γ → ∀ c : k, hV.xu k γ c ∈ P := by
    intro γ hγ
    induction hγ with
    | basis j => exact fun c => (hP j c).1
    | @reflect i v hv ih =>
      intro c
      obtain ⟨σ, hσ, h⟩ := hV.nm_conj_xm k hv i
      have e : hV.xm k (reflect τ i v) c =
          hV.nm k i * hV.xm k v (σ * c) * (hV.nm k i)⁻¹ := by
        rw [h, ← mul_assoc, hσ.mul_self, one_mul]
      have e' := congrArg (fun g : hV.minGroup k => (g : (Module.End k (Fin D.d →₀ k))ˣ)) e
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at e'
      change hV.xu k (reflect τ i v) c = _ at e'
      rw [e']
      exact mul_mem (mul_mem (hn i) (ih _)) (inv_mem (hn i))
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨γ, hγ, c, rfl⟩
  exact hx γ hγ c

@[expose] def torusElt
    (s : Fin τ.rank → kˣ) : hV.minGroup k :=
  ((List.finRange τ.rank).map fun i => hV.hm k i (s i)).prod

theorem coe_torusElt
    (s : Fin τ.rank → kˣ) :
    ((torusElt hV k s : hV.minGroup k) : (Module.End k (Fin D.d →₀ k))ˣ) =
      diagUnit fun a => TauCeti.torusCharacter s (D.wt a) := by
  have key : ∀ l : List (Fin τ.rank),
      ((((l.map fun i => hV.hm k i (s i)).prod : hV.minGroup k) :
        (Module.End k (Fin D.d →₀ k))ˣ)) =
        diagUnit fun a => (l.map fun i => s i ^ D.wt a i).prod := by
    intro l
    induction l with
    | nil =>
      refine Units.ext (ext_single fun a => ?_)
      simp [diagUnit_single]
    | cons i l ih =>
      simp only [List.map_cons, List.prod_cons, Subgroup.coe_mul, ih]
      have hh : (((hV.hm k i (s i) : hV.minGroup k) : (Module.End k (Fin D.d →₀ k))ˣ) :
          Module.End k (Fin D.d →₀ k)) = D.hDiag k i (s i) := hV.endo_hm k i (s i)
      refine Units.ext (ext_single fun a => ?_)
      rw [Units.val_mul, Module.End.mul_apply, diagUnit_single, map_smul, hh,
        MinData.hDiag_single, smul_smul, diagUnit_single, Units.val_mul, mul_comm]
  rw [torusElt, key]
  simp only [Fin.prod_univ_def, TauCeti.torusCharacter_def]

end Field

section Matrix

variable {n d : ℕ} (lab : Fin n ≃ Fin d) (A : Type*) [CommRing A]

@[expose] def labBasis : Module.Basis (Fin n) A (Fin d →₀ A) :=
  Finsupp.basisSingleOne.reindex lab.symm

@[expose] def toMat : (Module.End A (Fin d →₀ A))ˣ ≃* Matrix.GeneralLinearGroup (Fin n) A :=
  Units.mapEquiv (LinearMap.toMatrixAlgEquiv (labBasis lab A)).toMulEquiv

theorem toMat_apply (g : (Module.End A (Fin d →₀ A))ˣ) (r s : Fin n) :
    ((toMat lab A g : Matrix.GeneralLinearGroup (Fin n) A) : Matrix (Fin n) (Fin n) A) r s =
      (g : Module.End A (Fin d →₀ A)) (Finsupp.single (lab s) 1) (lab r) := by
  simp only [toMat, Units.coe_mapEquiv, MulEquiv.coe_mk, AlgEquiv.toEquiv_eq_coe,
    EquivLike.coe_coe, LinearMap.toMatrixAlgEquiv_apply, labBasis, Module.Basis.reindex_apply,
    Module.Basis.repr_reindex_apply, Finsupp.coe_basisSingleOne, Finsupp.basisSingleOne_repr,
    LinearEquiv.refl_apply, Equiv.symm_symm]

theorem coe_toMat_diagUnit
    (f : Fin d → Aˣ) :
    ((toMat lab A (diagUnit f) : Matrix.GeneralLinearGroup (Fin n) A) :
        Matrix (Fin n) (Fin n) A) = Matrix.diagonal fun a => ((f (lab a) : Aˣ) : A) := by
  ext r s
  rw [toMat_apply, diagUnit_single, Matrix.diagonal_apply, Finsupp.smul_apply, smul_eq_mul,
    Finsupp.single_apply]
  by_cases h : s = r
  · subst h
    simp
  · simp [Ne.symm h, lab.injective.ne h]

theorem toMat_mem_of_simple
    {τ : Tag} {D : MinData τ} (hV : D.Valid) (lab : Fin n ≃ Fin D.d)
    (k : Type*) [Field k] {P : Subgroup (Matrix.GeneralLinearGroup (Fin n) k)}
    (hP : ∀ (i : Fin τ.rank) (c : k), toMat lab k (hV.xu k (Pi.single i 1) c) ∈ P ∧
      toMat lab k (hV.xu k (-Pi.single i 1) c) ∈ P)
    (g : hV.minGroup k) : toMat lab k g ∈ P :=
  minGroup_le_of_simple hV k (P := P.comap (toMat lab k).toMonoidHom) hP g.2

end Matrix

structure WeightMatch {τ : Tag} (D : MinData τ) {B : Type*} {n : ℕ}
    (W : TauCeti.MinusculeWeightTable B (Fin n)) where
  node : B ≃ Fin τ.rank
  lab : Fin n ≃ Fin D.d
  wt_lab : ∀ a i, D.wt (lab a) (node i) = W.weight a i
  cartan : ∀ i j, W.cartanMatrix i j = τ.cartan (node i) (node j)

namespace WeightMatch

variable {τ : Tag} {D : MinData τ} {B : Type*} {n : ℕ} {W : TauCeti.MinusculeWeightTable B (Fin n)}
  (M : WeightMatch D W) (hV : D.Valid) (A : Type*) [CommRing A]

omit M in
include hV in
theorem nonempty
    (ν : B ≃ Fin τ.rank) (hcart : ∀ i j, W.cartanMatrix i j = τ.cartan (ν i) (ν j))
    (hcard : n = D.d) {a₀ : Fin n} {b₀ : Fin D.d} (h₀ : ∀ i, D.wt b₀ (ν i) = W.weight a₀ i)
    (hreach : ∀ a, ∃ l : List B, l.foldl (fun b i => W.reflection i b) a₀ = a) :
    Nonempty (WeightMatch D W) := by
  have hex : ∀ a, ∃ b : Fin D.d, ∀ i, D.wt b (ν i) = W.weight a i := by
    intro a
    obtain ⟨l, rfl⟩ := hreach a
    clear hreach
    induction l generalizing a₀ b₀ with
    | nil => exact ⟨b₀, h₀⟩
    | cons i l ih =>
      rw [List.foldl_cons]
      refine ih (a₀ := W.reflection i a₀) (b₀ := hV.sRefl (ν i) b₀) (fun j => ?_)
      rw [hV.wt_sRefl, W.weight_reflection, MinData.reflectWeight, Pi.sub_apply, Pi.smul_apply,
        smul_eq_mul, MinData.toWeight_single, h₀, h₀, hcart]
  choose f hf using hex
  have hinj : Function.Injective f := fun a a' h => W.weight_injective (funext fun i => by
    rw [← hf a i, ← hf a' i, h])
  have hbij : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨hinj, by simp [hcard]⟩
  exact ⟨⟨ν, Equiv.ofBijective f hbij, hf, hcart⟩⟩

theorem lab_reflection
    (i : B) (a : Fin n) :
    M.lab (W.reflection i a) = hV.sRefl (M.node i) (M.lab a) := by
  apply hV.wt_injective
  funext j
  obtain ⟨j, rfl⟩ := M.node.surjective j
  change D.wt (M.lab (W.reflection i a)) (M.node j) = D.wt (hV.sRefl (M.node i) (M.lab a)) _
  rw [hV.wt_sRefl, M.wt_lab, W.weight_reflection, MinData.reflectWeight, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul, MinData.toWeight_single, M.wt_lab, M.wt_lab, M.cartan]

include hV in
theorem raisingMatrix_apply
    (i : B) (r s : Fin n) :
    ((W.raisingMatrix i r s : ℤ) : A) =
      D.rootOp A (Pi.single (M.node i) 1) (Finsupp.single (M.lab s) 1) (M.lab r) := by
  rw [W.raisingMatrix_apply, hV.rootOp_single_apply, M.wt_lab, ← M.lab_reflection hV]
  by_cases h : W.weight s i = -1
  · by_cases hr : r = W.reflection i s
    · subst hr
      simp [h]
    · simp [h, hr]
  · simp [h]

include hV in
theorem loweringMatrix_apply
    (i : B) (r s : Fin n) :
    ((W.loweringMatrix i r s : ℤ) : A) =
      D.rootOp A (-Pi.single (M.node i) 1) (Finsupp.single (M.lab s) 1) (M.lab r) := by
  rw [W.loweringMatrix_apply, hV.rootOp_neg_single_apply, M.wt_lab, ← M.lab_reflection hV]
  by_cases h : W.weight s i = 1
  · by_cases hr : r = W.reflection i s
    · subst hr
      simp [h]
    · simp [h, hr]
  · simp [h]

theorem toMat_one_add_smul {g : (Module.End A (Fin D.d →₀ A))ˣ} {X : Module.End A (Fin D.d →₀ A)}
    {c : A} (hg : (g : Module.End A (Fin D.d →₀ A)) = 1 + c • X) {E : Matrix (Fin n) (Fin n) ℤ}
    (hE : ∀ r s, ((E r s : ℤ) : A) = X (Finsupp.single (M.lab s) 1) (M.lab r)) :
    ((toMat M.lab A g : Matrix.GeneralLinearGroup (Fin n) A) : Matrix (Fin n) (Fin n) A) =
      1 + c • E.map (Int.cast : ℤ → A) := by
  ext r s
  rw [toMat_apply, hg, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
    Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, ← hE, Matrix.add_apply, Matrix.one_apply,
    Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, Finsupp.single_apply]
  by_cases h : s = r
  · subst h
    simp
  · simp [Ne.symm h, M.lab.injective.ne h]

theorem toMat_rootUnit_single
    (i : B) (c : A) :
    ((toMat M.lab A (rootUnit hV A (Pi.single (M.node i) 1) c) :
        Matrix.GeneralLinearGroup (Fin n) A) : Matrix (Fin n) (Fin n) A) =
      1 + c • (W.raisingMatrix i).map (Int.cast : ℤ → A) :=
  M.toMat_one_add_smul A (coe_rootUnit hV A _ c) (M.raisingMatrix_apply hV A i)

theorem toMat_rootUnit_neg_single
    (i : B) (c : A) :
    ((toMat M.lab A (rootUnit hV A (-Pi.single (M.node i) 1) c) :
        Matrix.GeneralLinearGroup (Fin n) A) : Matrix (Fin n) (Fin n) A) =
      1 + c • (W.loweringMatrix i).map (Int.cast : ℤ → A) :=
  M.toMat_one_add_smul A (coe_rootUnit hV A _ c) (M.loweringMatrix_apply hV A i)

theorem torusCharacter_wt_lab [Fintype B] (s : B → Aˣ) (a : Fin n) :
    TauCeti.torusCharacter (s ∘ M.node.symm) (D.wt (M.lab a)) =
      TauCeti.torusCharacter s (W.weight a) := by
  rw [TauCeti.torusCharacter_def, TauCeti.torusCharacter_def,
    ← M.node.prod_comp (fun j => (s ∘ M.node.symm) j ^ D.wt (M.lab a) j)]
  simp only [Function.comp_apply, Equiv.symm_apply_apply, M.wt_lab]

theorem coe_toMat_diagUnit_torusCharacter
    [Fintype B] (s : B → Aˣ) :
    ((toMat M.lab A (diagUnit fun a => TauCeti.torusCharacter (s ∘ M.node.symm) (D.wt a)) :
        Matrix.GeneralLinearGroup (Fin n) A) : Matrix (Fin n) (Fin n) A) =
      Matrix.diagonal fun a => ((TauCeti.torusCharacter s (W.weight a) : Aˣ) : A) := by
  rw [coe_toMat_diagUnit]
  simp only [M.torusCharacter_wt_lab]

theorem coe_toMat_torusElt
    [Fintype B] (k : Type*) [Field k] (s : B → kˣ) :
    ((toMat M.lab k (torusElt hV k (s ∘ M.node.symm) : hV.minGroup k) :
        Matrix.GeneralLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) =
      Matrix.diagonal fun a => ((TauCeti.torusCharacter s (W.weight a) : kˣ) : k) := by
  rw [coe_torusElt]
  exact M.coe_toMat_diagUnit_torusCharacter k s

end WeightMatch

end CFSG.TauCetiBridge.Minuscule
