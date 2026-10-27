module

public import CFSG.ClassicalGroups.Alternating.Transvections
public import Mathlib.LinearAlgebra.Center
public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open LinearMap (BilinForm)
open CFSG.ClassicalGroups.Alternating
open scoped commutatorElement

variable {k A W : Type*} [Field k] [AddCommGroup A] [Module k A] [AddCommGroup W] [Module k W]

@[expose] noncomputable def orthoSumForm (BA : BilinForm k A) (BW : BilinForm k W) :
    BilinForm k (A × W) :=
  BA.compl₁₂ (LinearMap.fst k A W) (LinearMap.fst k A W) +
    BW.compl₁₂ (LinearMap.snd k A W) (LinearMap.snd k A W)

theorem orthoSumForm_apply (BA : BilinForm k A) (BW : BilinForm k W) (x y : A × W) :
    orthoSumForm BA BW x y = BA x.1 y.1 + BW x.2 y.2 := rfl

theorem summand_gl_ext {V : Type*} [AddCommGroup V] [Module k V]
    {g h : LinearMap.GeneralLinearGroup k V} (H : ∀ x, (g : V →ₗ[k] V) x = (h : V →ₗ[k] V) x) :
    g = h :=
  Units.ext (LinearMap.ext H)

theorem summand_gl_inv_apply {V : Type*} [AddCommGroup V] [Module k V]
    (g : LinearMap.GeneralLinearGroup k V) (x : V) :
    (g : V →ₗ[k] V) (((g⁻¹ : LinearMap.GeneralLinearGroup k V) : V →ₗ[k] V) x) = x := by
  rw [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Module.End.one_apply]

theorem summand_gl_apply_inv {V : Type*} [AddCommGroup V] [Module k V]
    (g : LinearMap.GeneralLinearGroup k V) (x : V) :
    ((g⁻¹ : LinearMap.GeneralLinearGroup k V) : V →ₗ[k] V) ((g : V →ₗ[k] V) x) = x := by
  rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Module.End.one_apply]

variable (W) in
@[expose] noncomputable def oddSummandGL : LinearMap.GeneralLinearGroup k A →*
    LinearMap.GeneralLinearGroup k (A × W) where
  toFun g := ⟨(g : A →ₗ[k] A).prodMap LinearMap.id, (g⁻¹ : LinearMap.GeneralLinearGroup k A).val
      |>.prodMap LinearMap.id, LinearMap.ext fun x => Prod.ext (summand_gl_inv_apply g x.1) rfl,
    LinearMap.ext fun x => Prod.ext (summand_gl_apply_inv g x.1) rfl⟩
  map_one' := Units.ext (LinearMap.ext fun x => by simp)
  map_mul' g h := Units.ext (LinearMap.ext fun x => by simp)

theorem oddSummandGL_apply (g : LinearMap.GeneralLinearGroup k A) (x : A × W) :
    ((oddSummandGL W g : LinearMap.GeneralLinearGroup k (A × W)) : A × W →ₗ[k] A × W) x =
      ((g : A →ₗ[k] A) x.1, x.2) := rfl

variable (W) in
@[expose] noncomputable def symplecticSummand (BA : BilinForm k A) :
    Subgroup (LinearMap.GeneralLinearGroup k (A × W)) :=
  (bilinIsometryGroup BA).map (oddSummandGL W)

theorem symplecticSummand_apply_comm {BA : BilinForm k A}
    {g : LinearMap.GeneralLinearGroup k (A × W)}
    (hg : g ∈ Subgroup.centralizer (symplecticSummand W BA : Set _))
    {h : LinearMap.GeneralLinearGroup k A} (hh : h ∈ bilinIsometryGroup BA) (x : A × W) :
    (g : A × W →ₗ[k] A × W) ((h : A →ₗ[k] A) x.1, x.2) =
      (((h : A →ₗ[k] A) ((g : A × W →ₗ[k] A × W) x).1), ((g : A × W →ₗ[k] A × W) x).2) := by
  have := congrArg (fun u : LinearMap.GeneralLinearGroup k (A × W) =>
    (u : A × W →ₗ[k] A × W) x) (Subgroup.mem_centralizer_iff.mp hg _ ⟨h, hh, rfl⟩)
  simpa [oddSummandGL_apply] using this.symm

theorem neg_one_mem_bilinIsometryGroup (BA : BilinForm k A) :
    (-1 : LinearMap.GeneralLinearGroup k A) ∈ bilinIsometryGroup BA := by
  intro x y
  simp

theorem apply_prod_of_comm_neg (hk : ringChar k ≠ 2) {BA : BilinForm k A}
    {g : LinearMap.GeneralLinearGroup k (A × W)}
    (hg : g ∈ Subgroup.centralizer (symplecticSummand W BA : Set _)) (a : A) (w : W) :
    ((g : A × W →ₗ[k] A × W) (a, 0)).2 = 0 ∧ ((g : A × W →ₗ[k] A × W) (0, w)).1 = 0 := by
  have h2 : (2 : k) ≠ 0 := Ring.two_ne_zero hk
  have hneg := symplecticSummand_apply_comm hg (neg_one_mem_bilinIsometryGroup BA)
  constructor
  · have h := hneg (a, 0)
    have h' : (g : A × W →ₗ[k] A × W) (-a, 0) = -(g : A × W →ₗ[k] A × W) (a, 0) := by
      rw [← map_neg, Prod.neg_mk, neg_zero]
    simp only [Units.val_neg, Units.val_one, LinearMap.neg_apply, Module.End.one_apply] at h
    rw [h'] at h
    have h3 := congrArg Prod.snd h
    simp only [Prod.snd_neg] at h3
    have h4 : (2 : k) • ((g : A × W →ₗ[k] A × W) (a, 0)).2 = 0 := by
      rw [two_smul]
      nth_rewrite 1 [← h3]
      rw [neg_add_cancel]
    exact (smul_eq_zero.1 h4).resolve_left h2
  · have h := hneg (0, w)
    simp only [Units.val_neg, Units.val_one, LinearMap.neg_apply, Module.End.one_apply,
      neg_zero] at h
    have h3 := congrArg Prod.fst h
    have h4 : (2 : k) • ((g : A × W →ₗ[k] A × W) (0, w)).1 = 0 := by
      rw [two_smul]
      nth_rewrite 1 [h3]
      rw [neg_add_cancel]
    exact (smul_eq_zero.1 h4).resolve_left h2

theorem exists_eq_smul_of_comm_isometry {BA : BilinForm k A} [Module.Free k A]
    (hBA : BA.IsAlt) (hBAn : BA.Nondegenerate) {f : A →ₗ[k] A}
    (hf : ∀ h ∈ bilinIsometryGroup BA, ∀ x, f ((h : A →ₗ[k] A) x) = (h : A →ₗ[k] A) (f x)) :
    ∃ c : k, f = c • 1 := by
  refine LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent fun a => ?_
  by_cases ha : a = 0
  · rw [ha]
    exact fun h => (h.ne_zero 0) rfl
  obtain ⟨y, hy⟩ : ∃ y, BA y a ≠ 0 := by
    by_contra! hz
    exact ha (hBAn.2 a hz)
  set x := (BA y a)⁻¹ • y with hx
  have hxa : BA x a = 1 := by rw [hx, map_smul, LinearMap.smul_apply, smul_eq_mul,
    inv_mul_cancel₀ hy]
  have hT := hf _ (symplecticTransvection_mem_bilinIsometryGroup hBA a 1) x
  rw [symplecticTransvection_apply, symplecticTransvection_apply, hxa, one_mul, one_smul,
    map_add, add_right_inj, one_mul] at hT
  intro hli
  have h0 := (LinearIndependent.pair_iff.1 hli (BA (f x) a) (-1)
    (by rw [neg_one_smul, ← hT, add_neg_cancel])).2
  exact one_ne_zero (neg_eq_zero.1 h0)

theorem natural_odd_symplectic_summand_centralizer [Finite k] (hk : ringChar k ≠ 2)
    [FiniteDimensional k A] [FiniteDimensional k W] {BA : BilinForm k A} {BW : BilinForm k W}
    (hBA : BA.IsAlt) (hBAn : BA.Nondegenerate) (_hBW : BW.IsAlt) (_hBWn : BW.Nondegenerate)
    (hdim : 2 ≤ Module.finrank k A) :
    symplecticSummand W BA ≤ bilinIsometryGroup (orthoSumForm BA BW) ∧
    {x : A × W | ∀ d ∈ symplecticSummand W BA, (d : A × W →ₗ[k] A × W) x = x} =
      Set.range (LinearMap.inr k A W) ∧
    (∀ g : LinearMap.GeneralLinearGroup k (A × W),
      g ∈ bilinIsometryGroup (orthoSumForm BA BW) ⊓
          Subgroup.centralizer (symplecticSummand W BA : Set _) ↔
        ∃ ε : k, (ε = 1 ∨ ε = -1) ∧ ∃ gW ∈ bilinIsometryGroup BW, ∀ (a : A) (w : W),
          (g : A × W →ₗ[k] A × W) (a, w) = (ε • a, (gW : W →ₗ[k] W) w)) ∧
    ∀ R : Subgroup (LinearMap.GeneralLinearGroup k (A × W)),
      R ≤ bilinIsometryGroup (orthoSumForm BA BW) ⊓
          Subgroup.centralizer (symplecticSummand W BA : Set _) →
        Group.IsPerfect R → ∀ g ∈ R, ∀ a : A, (g : A × W →ₗ[k] A × W) (a, 0) = (a, 0) := by
  classical
  have h2 : (2 : k) ≠ 0 := Ring.two_ne_zero hk
  have hApos : 0 < Module.finrank k A := by omega
  obtain ⟨a₀, ha₀⟩ : ∃ a : A, a ≠ 0 := by
    have : Nontrivial A := Module.nontrivial_of_finrank_pos hApos
    exact exists_ne 0
  obtain ⟨b₀, hb₀⟩ : ∃ b, BA b a₀ ≠ 0 := by
    by_contra! hz
    exact ha₀ (hBAn.2 a₀ hz)
  have hblock : ∀ g : LinearMap.GeneralLinearGroup k (A × W),
      g ∈ Subgroup.centralizer (symplecticSummand W BA : Set _) → ∀ (a : A) (w : W),
      (g : A × W →ₗ[k] A × W) (a, w) =
        (((g : A × W →ₗ[k] A × W) (a, 0)).1, ((g : A × W →ₗ[k] A × W) (0, w)).2) := by
    intro g hg a w
    obtain ⟨h1, -⟩ := apply_prod_of_comm_neg hk hg a w
    obtain ⟨-, h2'⟩ := apply_prod_of_comm_neg hk hg a w
    have : (a, w) = (a, (0 : W)) + ((0 : A), w) := by simp
    rw [this, map_add]
    ext
    · simp [h2']
    · simp [h1]
  have hscalar : ∀ g : LinearMap.GeneralLinearGroup k (A × W),
      g ∈ Subgroup.centralizer (symplecticSummand W BA : Set _) → ∃ c : k, ∀ a : A, ((g : A × W →ₗ[k] A × W) (a, 0)).1 = c • a := by
    intro g hg
    let f : A →ₗ[k] A := (LinearMap.fst k A W).comp ((g : A × W →ₗ[k] A × W).comp
      (LinearMap.inl k A W))
    obtain ⟨c, hc⟩ := exists_eq_smul_of_comm_isometry hBA hBAn (f := f) fun h hh x => by
      have := symplecticSummand_apply_comm hg hh (x, 0)
      exact congrArg Prod.fst this
    exact ⟨c, fun a => by simpa [f] using LinearMap.congr_fun hc a⟩
  refine ⟨?_, ?_, fun g => ?_, ?_⟩
  ·
    rintro _ ⟨h, hh, rfl⟩ x y
    rw [oddSummandGL_apply, oddSummandGL_apply, orthoSumForm_apply, orthoSumForm_apply, hh]
  ·
    ext ⟨a, w⟩
    constructor
    · intro hx
      have h := congrArg Prod.fst (hx _ ⟨-1, neg_one_mem_bilinIsometryGroup BA, rfl⟩)
      simp only [oddSummandGL_apply, Units.val_neg, Units.val_one, LinearMap.neg_apply,
        Module.End.one_apply] at h
      have ha : a = 0 := by
        have h4 : (2 : k) • a = 0 := by
          rw [two_smul]
          nth_rewrite 1 [← h]
          rw [neg_add_cancel]
        exact (smul_eq_zero.1 h4).resolve_left h2
      exact ⟨w, by rw [ha]; rfl⟩
    · rintro ⟨w', hw'⟩ _ ⟨h, -, rfl⟩
      rw [← hw', oddSummandGL_apply]
      simp
  ·
    constructor
    · rintro ⟨hgS, hgC⟩
      obtain ⟨c, hc⟩ := hscalar g hgC
      have hA0 : ∀ a : A, (g : A × W →ₗ[k] A × W) (a, 0) = (c • a, 0) := fun a =>
        Prod.ext (hc a) (apply_prod_of_comm_neg hk hgC a 0).1
      have hc2 : c * c = 1 := by
        have h := hgS (b₀, 0) (a₀, 0)
        rw [hA0, hA0] at h
        simp only [orthoSumForm_apply, map_zero, add_zero, map_smul, LinearMap.smul_apply,
          smul_eq_mul] at h
        have h' : (c * c - 1) * BA b₀ a₀ = 0 := by linear_combination h
        exact sub_eq_zero.1 ((mul_eq_zero.1 h').resolve_right hb₀)
      have hε : c = 1 ∨ c = -1 := by
        have : (c - 1) * (c + 1) = 0 := by linear_combination hc2
        rcases mul_eq_zero.1 this with h | h
        · exact Or.inl (sub_eq_zero.1 h)
        · exact Or.inr (eq_neg_of_add_eq_zero_left h)
      have hgi : g⁻¹ ∈ Subgroup.centralizer (symplecticSummand W BA : Set _) := inv_mem hgC
      let gW : W →ₗ[k] W := (LinearMap.snd k A W).comp ((g : A × W →ₗ[k] A × W).comp
        (LinearMap.inr k A W))
      let gW' : W →ₗ[k] W := (LinearMap.snd k A W).comp
        (((g⁻¹ : LinearMap.GeneralLinearGroup k (A × W)) : A × W →ₗ[k] A × W).comp
        (LinearMap.inr k A W))
      have hgW : ∀ w, (g : A × W →ₗ[k] A × W) (0, w) = (0, gW w) := fun w => by
        ext
        · exact (apply_prod_of_comm_neg hk hgC 0 w).2
        · rfl
      have hgW' : ∀ w, ((g⁻¹ : LinearMap.GeneralLinearGroup k (A × W)) : A × W →ₗ[k] A × W)
          (0, w) = (0, gW' w) := fun w => by
        ext
        · exact (apply_prod_of_comm_neg hk hgi 0 w).2
        · rfl
      have h1 : ∀ w, gW (gW' w) = w := fun w => by
        have := summand_gl_inv_apply g (0, w)
        rw [hgW', hgW] at this
        exact congrArg Prod.snd this
      have h1' : ∀ w, gW' (gW w) = w := fun w => by
        have := summand_gl_apply_inv g (0, w)
        rw [hgW, hgW'] at this
        exact congrArg Prod.snd this
      let gWu : LinearMap.GeneralLinearGroup k W :=
        ⟨gW, gW', LinearMap.ext h1, LinearMap.ext h1'⟩
      refine ⟨c, hε, gWu, fun w w' => ?_, fun a w => ?_⟩
      · have h := hgS (0, w) (0, w')
        rw [hgW, hgW] at h
        simpa [orthoSumForm_apply] using h
      · rw [hblock g hgC a w, hc]
        rfl
    · rintro ⟨ε, hε, gW, hgW, hg⟩
      refine ⟨fun x y => ?_, Subgroup.mem_centralizer_iff.2 ?_⟩
      · obtain ⟨a, w⟩ := x
        obtain ⟨a', w'⟩ := y
        rw [hg, hg, orthoSumForm_apply, orthoSumForm_apply, hgW]
        have hεε : ε * ε = 1 := by rcases hε with rfl | rfl <;> simp
        simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, ← mul_assoc, hεε, one_mul]
      · rintro _ ⟨h, -, rfl⟩
        refine summand_gl_ext fun x => ?_
        obtain ⟨a, w⟩ := x
        change (oddSummandGL W h : A × W →ₗ[k] A × W) ((g : A × W →ₗ[k] A × W) (a, w)) =
          (g : A × W →ₗ[k] A × W) ((oddSummandGL W h : A × W →ₗ[k] A × W) (a, w))
        rw [oddSummandGL_apply, hg, oddSummandGL_apply, hg, map_smul]
  ·
    intro R hR hRp
    have hsign : ∀ g ∈ R, ∃ c : k, ∀ a : A, (g : A × W →ₗ[k] A × W) (a, 0) = (c • a, 0) := by
      intro g hg
      obtain ⟨c, hc⟩ := hscalar g (hR hg).2
      exact ⟨c, fun a => Prod.ext (hc a) (apply_prod_of_comm_neg hk (hR hg).2 a 0).1⟩
    let F : Subgroup (LinearMap.GeneralLinearGroup k (A × W)) :=
      { carrier := {g | ∀ a : A, (g : A × W →ₗ[k] A × W) (a, 0) = (a, 0)}
        one_mem' := fun a => rfl
        mul_mem' := fun {g h} hg hh a => by
          change (g : A × W →ₗ[k] A × W) ((h : A × W →ₗ[k] A × W) (a, 0)) = (a, 0)
          rw [hh, hg]
        inv_mem' := fun {g} hg a => by
          have := summand_gl_apply_inv g (a, 0)
          rw [hg] at this
          exact this }
    have hRF : ⁅R, R⁆ ≤ F := by
      rw [Subgroup.commutator_le]
      intro x hx y hy a
      obtain ⟨cx, hcx⟩ := hsign x hx
      obtain ⟨cy, hcy⟩ := hsign y hy
      obtain ⟨cx', hcx'⟩ := hsign _ (inv_mem hx)
      obtain ⟨cy', hcy'⟩ := hsign _ (inv_mem hy)
      have hxx : ∀ a : A, (cx * cx') • a = a := fun a => by
        have := summand_gl_inv_apply x (a, 0)
        rw [hcx', hcx, smul_smul] at this
        exact congrArg Prod.fst this
      have hyy : ∀ a : A, (cy * cy') • a = a := fun a => by
        have := summand_gl_inv_apply y (a, 0)
        rw [hcy', hcy, smul_smul] at this
        exact congrArg Prod.fst this
      change ((x * y * x⁻¹ * y⁻¹ : LinearMap.GeneralLinearGroup k (A × W)) :
        A × W →ₗ[k] A × W) (a, 0) = (a, 0)
      simp only [Units.val_mul, Module.End.mul_apply, hcy', hcx', hcy, hcx, smul_smul]
      ext
      · simp only
        rw [show cx * (cy * (cx' * cy')) = (cx * cx') * (cy * cy') by ring, ← smul_smul, hyy,
          hxx]
      · rfl
    intro g hg a
    rw [← Subgroup.isPerfect_iff.1 hRp] at hg
    exact hRF hg a

end CFSG.LocalAnalysis.ComponentInitial
