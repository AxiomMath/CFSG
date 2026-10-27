module

public import CFSG.CharacterTheory.SteinbergBYNortonCriterion
public import CFSG.CharacterTheory.SteinbergBYBrauerSimpleBound
public import Mathlib.RepresentationTheory.Character
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.Algebra.CharP.Two
public import Mathlib.LinearAlgebra.Basis.VectorSpace

public section

namespace CFSG.CharacterTheory.SteinbergBY

open Module
open scoped Matrix TensorProduct

section Definitions

variable {L k G M V V' : Type*} [Field L] [Field k] [Group G] [AddCommGroup M] [Module L M]
  [AddCommGroup V] [Module k V] [AddCommGroup V'] [Module k V']

@[expose] def restrictScalarsRep (F : Type*) [CommSemiring F] [Algebra F L] [Module F M]
    [IsScalarTower F L M] (τ : Representation L G M) : Representation F G M where
  toFun g := (τ g).restrictScalars F
  map_one' := by ext; simp
  map_mul' g h := by ext; simp

@[expose] def transportRep (e : V ≃ₗ[k] V') (ρ : Representation k G V) :
    Representation k G V' where
  toFun g := e.toLinearMap ∘ₗ ρ g ∘ₗ e.symm.toLinearMap
  map_one' := by ext; simp
  map_mul' g h := by ext; simp

@[expose] def transportRepEquiv (e : V ≃ₗ[k] V') (ρ : Representation k G V) :
    ρ.Equiv (transportRep e ρ) :=
  Representation.Equiv.mk e fun g => by ext v; simp [transportRep]

end Definitions

section Irreducible

variable {k G V W : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V] [AddCommGroup W]
  [Module k W]

theorem isIrreducible_of_equiv {ρ : Representation k G V} {σ : Representation k G W}
    (φ : ρ.Equiv σ) (h : ρ.IsIrreducible) : σ.IsIrreducible := by
  rw [Representation.irreducible_iff_isSimpleModule_asModule] at h ⊢
  let f := Representation.IntertwiningMap.equivLinearMapAsModule σ ρ φ.symm.toIntertwiningMap
  have hf : Function.Bijective f := φ.symm.bijective
  exact IsSimpleModule.congr (LinearEquiv.ofBijective f hf)

theorem isEmpty_equiv_of_finrank_ne {ρ : Representation k G V} {σ : Representation k G W}
    (h : finrank k V ≠ finrank k W) : IsEmpty (ρ.Equiv σ) :=
  ⟨fun e => h e.toLinearEquiv.finrank_eq⟩

theorem isEmpty_equiv_of_trace_ne {ρ : Representation k G V} {σ : Representation k G W} (g : G)
    (h : LinearMap.trace k V (ρ g) ≠ LinearMap.trace k W (σ g)) : IsEmpty (ρ.Equiv σ) :=
  ⟨fun e => h (congrFun (Representation.char_iso e) g)⟩

theorem nontrivial_of_isIrreducible (ρ : Representation k G V) [ρ.IsIrreducible] :
    Nontrivial V := by
  by_contra hV
  rw [not_nontrivial_iff_subsingleton] at hV
  apply (bot_ne_top : (⊥ : Subrepresentation ρ) ≠ ⊤)
  ext v
  rw [Subsingleton.elim v 0]
  exact ⟨fun _ => Submodule.zero_mem _, fun _ => Submodule.zero_mem _⟩

theorem finiteDimensional_of_isIrreducible [Finite G] (ρ : Representation k G V)
    [ρ.IsIrreducible] : FiniteDimensional k V := by
  classical
  have := nontrivial_of_isIrreducible ρ
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hle : Submodule.span k (Set.range fun g => ρ g v) ≤
      ⨅ h : G, (Submodule.span k (Set.range fun g => ρ g v)).comap (ρ h) := by
    refine le_iInf fun h => ?_
    rw [Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    exact Submodule.subset_span ⟨h * g, by simp [map_mul]⟩
  let U : Subrepresentation ρ :=
    ⟨Submodule.span k (Set.range fun g => ρ g v), fun h _ hx => Submodule.mem_iInf _ |>.mp
      (hle hx) h⟩
  have hU : U ≠ ⊥ := by
    intro h0
    apply hv
    have hv1 : v ∈ U := Submodule.subset_span ⟨1, by simp⟩
    rw [h0] at hv1
    exact (Submodule.mem_bot k).mp hv1
  have hUtop : U = ⊤ := (eq_bot_or_eq_top U).resolve_left hU
  have hspan : Submodule.span k (Set.range fun g => ρ g v) = ⊤ := by
    have := congrArg Subrepresentation.toSubmodule hUtop
    exact this
  have : Fintype G := Fintype.ofFinite G
  refine ⟨⟨Finset.univ.image fun g => ρ g v, ?_⟩⟩
  rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, hspan]

theorem exists_isIrreducible_subrepresentation [FiniteDimensional k V] [Nontrivial V]
    (ρ : Representation k G V) :
    ∃ U : Subrepresentation ρ, U ≠ ⊥ ∧ U.toRepresentation.IsIrreducible := by
  classical
  have htop : (⊤ : Subrepresentation ρ) ≠ ⊥ := by
    intro h
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have hvtop : v ∈ (⊤ : Subrepresentation ρ) := Submodule.mem_top
    rw [h] at hvtop
    exact hv ((Submodule.mem_bot k).mp hvtop)
  have hex : ∃ n, ∃ U : Subrepresentation ρ, U ≠ ⊥ ∧ finrank k U.toSubmodule = n :=
    ⟨_, ⊤, htop, rfl⟩
  obtain ⟨U, hU, hUn⟩ := Nat.find_spec hex
  have hmin : ∀ U' : Subrepresentation ρ, U' ≤ U → U' ≠ ⊥ → U' = U := by
    intro U' hle hne
    have h1 : Nat.find hex ≤ finrank k U'.toSubmodule := Nat.find_min' hex ⟨U', hne, rfl⟩
    exact Subrepresentation.toSubmodule_injective
      (Submodule.eq_of_le_of_finrank_le hle (hUn ▸ h1))
  obtain ⟨u, huU, hu0⟩ : ∃ u ∈ U, u ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hU
    ext x
    exact ⟨fun hx => (Submodule.mem_bot k).mpr (hcon x hx),
      fun hx => (Submodule.mem_bot k).mp hx ▸ Submodule.zero_mem _⟩
  refine ⟨U, hU, ?_⟩
  let img : Subrepresentation U.toRepresentation → Subrepresentation ρ := fun W' =>
    ⟨W'.toSubmodule.map U.toSubmodule.subtype, by
      rintro g _ ⟨y, hy, rfl⟩
      exact ⟨U.toRepresentation g y, W'.apply_mem_toSubmodule g hy, rfl⟩⟩
  have himg_le : ∀ W', img W' ≤ U := by
    rintro W' _ ⟨y, -, rfl⟩
    exact y.2
  have hbt : (⊥ : Subrepresentation U.toRepresentation) ≠ ⊤ := by
    intro h
    have hmem : (⟨u, huU⟩ : U.toSubmodule) ∈ (⊤ : Subrepresentation U.toRepresentation) :=
      Submodule.mem_top
    rw [← h] at hmem
    exact hu0 (congrArg Subtype.val ((Submodule.mem_bot k).mp hmem))
  have : Nontrivial (Subrepresentation U.toRepresentation) := ⟨⟨⊥, ⊤, hbt⟩⟩
  refine ⟨fun W' => ?_⟩
  by_cases hW : img W' = ⊥
  · left
    ext y
    refine ⟨fun hy => ?_, fun hy => (Submodule.mem_bot k).mp hy ▸ Submodule.zero_mem _⟩
    have hy' : (y : V) ∈ img W' := ⟨y, hy, rfl⟩
    rw [hW] at hy'
    exact (Submodule.mem_bot k).mpr (Subtype.ext ((Submodule.mem_bot k).mp hy'))
  · right
    have heq := hmin (img W') (himg_le W') hW
    ext y
    refine ⟨fun _ => Submodule.mem_top, fun _ => ?_⟩
    have hy : (y : V) ∈ img W' := by rw [heq]; exact y.2
    obtain ⟨y', hy', hyy'⟩ := hy
    have : y' = y := Subtype.ext hyy'
    rw [← this]
    exact hy'

end Irreducible

section Completeness

variable {k G : Type*} [Field k] [Group G]

theorem exists_equiv_of_card_pRegularClass_le_of_univ [IsAlgClosed k] [Finite G] (p : ℕ)
    [Fact p.Prime] [CharP k p] {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)] [∀ i, FiniteDimensional k (V i)]
    (ρ : ∀ i, Representation k G (V i)) [∀ i, (ρ i).IsIrreducible]
    (hne : ∀ i j, i ≠ j → IsEmpty ((ρ i).Equiv (ρ j)))
    (hcard : Fintype.card (PRegularClass p G) ≤ Fintype.card ι)
    (W : Type*) [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (σ : Representation k G W) [σ.IsIrreducible]
    (huniv : ∀ i, Nonempty (V i ≃ₗ[k] (Fin (finrank k (V i)) → k)))
    (hW : Nonempty (W ≃ₗ[k] (Fin (finrank k W) → k))) :
    ∃ i, Nonempty (σ.Equiv (ρ i)) := by
  classical
  by_contra hcon
  push Not at hcon
  let d : Option ι → ℕ := fun o => Option.elim o (finrank k W) fun i => finrank k (V i)
  let e : ∀ i, V i ≃ₗ[k] (Fin (finrank k (V i)) → k) := fun i => (huniv i).some
  let eW : W ≃ₗ[k] (Fin (finrank k W) → k) := hW.some
  let ρ' : ∀ o : Option ι, Representation k G (Fin (d o) → k) := fun o =>
    match o with
    | none => transportRep eW σ
    | some i => transportRep (e i) (ρ i)
  have hirr : ∀ o, (ρ' o).IsIrreducible := by
    intro o
    cases o with
    | none => exact isIrreducible_of_equiv (transportRepEquiv eW σ) inferInstance
    | some i => exact isIrreducible_of_equiv (transportRepEquiv (e i) (ρ i)) inferInstance
  have hne' : ∀ o o', o ≠ o' → IsEmpty ((ρ' o).Equiv (ρ' o')) := by
    intro o o' hoo'
    refine ⟨fun φ => ?_⟩
    cases o with
    | none =>
      cases o' with
      | none => exact hoo' rfl
      | some j =>
        exact (hcon j).false (((transportRepEquiv eW σ).trans φ).trans
          (transportRepEquiv (e j) (ρ j)).symm)
    | some i =>
      cases o' with
      | none =>
        exact (hcon i).false ((((transportRepEquiv (e i) (ρ i)).trans φ).trans
          (transportRepEquiv eW σ).symm).symm)
      | some j =>
        have hij : i ≠ j := fun h => hoo' (h ▸ rfl)
        exact (hne i j hij).false (((transportRepEquiv (e i) (ρ i)).trans φ).trans
          (transportRepEquiv (e j) (ρ j)).symm)
  have h := card_le_card_pRegularClass (k := k) p ρ' hne'
  rw [Fintype.card_option] at h
  omega

theorem exists_equiv_of_card_pRegularClass_le [IsAlgClosed k] [Finite G] (p : ℕ)
    [Fact p.Prime] [CharP k p] {ι : Type} [Fintype ι] [DecidableEq ι] (d : ι → ℕ)
    (ρ : ∀ i, Representation k G (Fin (d i) → k)) [∀ i, (ρ i).IsIrreducible]
    (hne : ∀ i j, i ≠ j → IsEmpty ((ρ i).Equiv (ρ j)))
    (hcard : Fintype.card (PRegularClass p G) ≤ Fintype.card ι)
    (W : Type*) [AddCommGroup W] [Module k W] (σ : Representation k G W) [σ.IsIrreducible] :
    FiniteDimensional k W ∧ ∃ i, Nonempty (σ.Equiv (ρ i)) := by
  have hfin := finiteDimensional_of_isIrreducible σ
  refine ⟨hfin, ?_⟩
  let eW : W ≃ₗ[k] (Fin (finrank k W) → k) := (Module.finBasis k W).equivFun
  let σ' := transportRep eW σ
  have : σ'.IsIrreducible := isIrreducible_of_equiv (transportRepEquiv eW σ) inferInstance
  obtain ⟨i, ⟨φ⟩⟩ := exists_equiv_of_card_pRegularClass_le_of_univ p ρ hne hcard
    (Fin (finrank k W) → k) σ'
    (fun i => ⟨(Module.finBasis k (Fin (d i) → k)).equivFun⟩)
    ⟨(Module.finBasis k (Fin (finrank k W) → k)).equivFun⟩
  exact ⟨i, ⟨(transportRepEquiv eW σ).trans φ⟩⟩

end Completeness

section Matrices

variable {F K G : Type*} [Field F] [Field K] [Group G] {n m : ℕ}

theorem trace_matrixBaseChange (φ : F →+* K) (M : G →* Matrix (Fin n) (Fin n) F) (g : G) :
    LinearMap.trace K (Fin n → K) (matrixBaseChange φ M g) = φ (Matrix.trace (M g)) := by
  change LinearMap.trace K (Fin n → K) (Matrix.toLin' ((M g).map φ)) = _
  rw [Matrix.trace_toLin'_eq, AddMonoidHom.map_trace]

@[expose] noncomputable def repMatrix (ρ : Representation F G (Fin n → F)) :
    G →* Matrix (Fin n) (Fin n) F :=
  (LinearMap.toMatrixAlgEquiv' : Module.End F (Fin n → F) ≃ₐ[F] Matrix (Fin n) (Fin n) F)
    |>.toMonoidHom.comp ρ

theorem matrixBaseChange_repMatrix (ρ : Representation F G (Fin n → F)) :
    matrixBaseChange (RingHom.id F) (repMatrix ρ) = ρ := by
  refine MonoidHom.ext fun g => LinearMap.ext fun x => ?_
  rw [matrixBaseChange_apply]
  change (LinearMap.toMatrix' (ρ g)).map (RingHom.id F) *ᵥ x = _
  rw [RingHom.coe_id, Matrix.map_id, LinearMap.toMatrix'_mulVec]

theorem toMatrix'_mul_map_eq (φ : F →+* K) (M : G →* Matrix (Fin n) (Fin n) F)
    (N : G →* Matrix (Fin m) (Fin m) F)
    (f : (matrixBaseChange φ M).IntertwiningMap (matrixBaseChange φ N)) (g : G) :
    LinearMap.toMatrix' f.toLinearMap * (M g).map φ =
      (N g).map φ * LinearMap.toMatrix' f.toLinearMap := by
  have h := f.isIntertwining' g
  have h2 := congrArg LinearMap.toMatrix' h
  change LinearMap.toMatrix' (f.toLinearMap ∘ₗ Matrix.toLin' ((M g).map φ)) =
    LinearMap.toMatrix' (Matrix.toLin' ((N g).map φ) ∘ₗ f.toLinearMap) at h2
  simp only [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin'] at h2
  exact h2

@[expose] noncomputable def intertwiningMapOfMatrix (φ : F →+* K)
    (M : G →* Matrix (Fin n) (Fin n) F) (N : G →* Matrix (Fin m) (Fin m) F)
    (T : Matrix (Fin m) (Fin n) F) (hT : ∀ g, T * M g = N g * T) :
    (matrixBaseChange φ M).IntertwiningMap (matrixBaseChange φ N) where
  toLinearMap := Matrix.toLin' (T.map φ)
  isIntertwining' g := by
    apply LinearMap.toMatrix'.injective
    change LinearMap.toMatrix' (Matrix.toLin' (T.map φ) ∘ₗ Matrix.toLin' ((M g).map φ)) =
      LinearMap.toMatrix' (Matrix.toLin' ((N g).map φ) ∘ₗ Matrix.toLin' (T.map φ))
    simp only [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin']
    rw [← Matrix.map_mul, ← Matrix.map_mul, hT]

theorem intertwiningMapOfMatrix_ne_zero (φ : F →+* K)
    (M : G →* Matrix (Fin n) (Fin n) F) (N : G →* Matrix (Fin m) (Fin m) F)
    (T : Matrix (Fin m) (Fin n) F) (hT : ∀ g, T * M g = N g * T) (h0 : T ≠ 0) :
    intertwiningMapOfMatrix φ M N T hT ≠ 0 := by
  intro h
  apply h0
  have h1 := congrArg (fun f : (matrixBaseChange φ M).IntertwiningMap (matrixBaseChange φ N) =>
    LinearMap.toMatrix' f.toLinearMap) h
  change LinearMap.toMatrix' (Matrix.toLin' (T.map φ)) = LinearMap.toMatrix' 0 at h1
  rw [LinearMap.toMatrix'_toLin', map_zero] at h1
  ext i j
  have h2 := congrFun (congrFun h1 i) j
  rw [Matrix.map_apply, Matrix.zero_apply] at h2
  rw [Matrix.zero_apply]
  exact (map_eq_zero φ).mp h2

omit [Group G] in
theorem exists_ne_zero_mul_eq_mul_of_map {ι κ : Type*} [Fintype ι] [Fintype κ] (φ : F →+* K)
    (A : G → Matrix ι ι F) (B : G → Matrix κ κ F) (T : Matrix κ ι K) (hT0 : T ≠ 0)
    (hT : ∀ g, T * (A g).map φ = (B g).map φ * T) :
    ∃ T' : Matrix κ ι F, T' ≠ 0 ∧ ∀ g, T' * A g = B g * T' := by
  classical
  let _ : Algebra F K := φ.toAlgebra
  set b := Module.Basis.ofVectorSpace F K with hb
  have hcoord : ∀ (t : K) (a : F) (idx : Module.Basis.ofVectorSpaceIndex F K),
      b.repr (t * φ a) idx = b.repr t idx * a := by
    intro t a idx
    have h1 : t * φ a = a • t := by
      rw [Algebra.smul_def, mul_comm]
      rfl
    rw [h1, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm]
  have hcoord' : ∀ (t : K) (a : F) (idx : Module.Basis.ofVectorSpaceIndex F K),
      b.repr (φ a * t) idx = a * b.repr t idx := by
    intro t a idx
    rw [mul_comm, hcoord, mul_comm]
  obtain ⟨x, y, hxy⟩ : ∃ x y, T x y ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hT0 (Matrix.ext hcon)
  obtain ⟨idx, hidx⟩ : ∃ idx, b.repr (T x y) idx ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hxy (b.repr.injective (Finsupp.ext fun i => by rw [hcon i, map_zero,
      Finsupp.zero_apply]))
  refine ⟨Matrix.of fun x y => b.repr (T x y) idx, fun h => hidx ?_, fun g => ?_⟩
  · have := congrFun (congrFun h x) y
    simpa using this
  · ext u v
    have h1 := congrFun (congrFun (hT g) u) v
    rw [Matrix.mul_apply, Matrix.mul_apply] at h1
    have h2 := congrArg (fun t => b.repr t idx) h1
    simp only [map_sum, Finsupp.finsetSum_apply, Matrix.map_apply, hcoord, hcoord'] at h2
    rw [Matrix.mul_apply, Matrix.mul_apply]
    simpa only [Matrix.of_apply] using h2

end Matrices

section Schur

variable {k G V W : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V] [AddCommGroup W]
  [Module k W]

theorem nonempty_equiv_of_ne_zero {ρ : Representation k G V} {σ : Representation k G W}
    [ρ.IsIrreducible] [σ.IsIrreducible] (f : ρ.IntertwiningMap σ) (hf : f ≠ 0) :
    Nonempty (ρ.Equiv σ) :=
  ⟨f.ofBijective ((Representation.IsIrreducible.bijective_or_eq_zero f).resolve_right hf)⟩

end Schur

end CFSG.CharacterTheory.SteinbergBY
