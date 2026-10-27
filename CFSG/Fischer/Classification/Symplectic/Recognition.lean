module

public import CFSG.Fischer.Classification.Symplectic.Module
public import CFSG.Fischer.Classification.Symplectic.Stars
public import CFSG.Fischer.Classification.Symplectic.OrthoGen
public import CFSG.Fischer.Classification.Symplectic.OrthoGenSymplectic
import TauCeti.LinearAlgebra.BilinearForm.Orthogonal
import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis

public noncomputable section

namespace CFSG.Fischer.Classification

open CFSG.Blueprint.Fischer CFSG.Fischer CFSG.Open Matrix

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {X : Type} [Group X] {E : Set X}

namespace Symplectic

section Config

theorem bar_ne_zero (hP : Pair X E) (hZ : Subgroup.center X = ⊥)
    (hS : IsSimpleGroup (commutator X)) (hsymp : IsSymplecticType E) (e : E) : bar e ≠ 0 := by
  intro h
  apply Pair.ne_one hP e.2
  apply rho_injective hP hZ hS hsymp
  rw [map_one]
  refine LinearEquiv.ext fun v => ?_
  rw [rho_apply_eq hP hsymp, h, smul_zero, add_zero]
  rfl

theorem rho_mem_range_bar_iff (hP : Pair X E) (g : X) (v : SympModule E) :
    rho hP g v ∈ Set.range (bar (E := E)) ↔ v ∈ Set.range (bar (E := E)) := by
  constructor
  · rintro ⟨e, he⟩
    refine ⟨Pair.conjPerm hP g⁻¹ e, ?_⟩
    rw [← rho_bar, he, ← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl
  · rintro ⟨e, rfl⟩
    exact ⟨Pair.conjPerm hP g e, (rho_bar hP g e).symm⟩

theorem eq_range_bar_of_closed (hP : Pair X E) (hsymp : IsSymplecticType E)
    (ℓ : Set (SympModule E)) (hℓ : ℓ ⊆ Set.range bar) (hne : ℓ.Nonempty)
    (hcl : ∀ d ∈ Set.range (bar (E := E)), ∀ p ∈ ℓ, p + sympForm E p d • d ∈ ℓ) :
    ℓ = Set.range bar := by
  refine Set.Subset.antisymm hℓ ?_
  have hgen : ∀ d e : E, bar e ∈ ℓ → bar (Pair.conjPerm hP d e) ∈ ℓ := by
    intro d e he
    rw [← rho_bar, rho_apply_eq hP hsymp]
    exact hcl _ ⟨d, rfl⟩ _ he
  have hall : ∀ g : X, ∀ e : E, bar e ∈ ℓ ↔ bar (Pair.conjPerm hP g e) ∈ ℓ := by
    intro g
    have hg : g ∈ Subgroup.closure E := by rw [Pair.closure_eq hP]; trivial
    induction hg using Subgroup.closure_induction with
    | mem d hd =>
      intro e
      refine ⟨hgen ⟨d, hd⟩ e, fun h => ?_⟩
      have := hgen ⟨d, hd⟩ _ h
      rwa [← Equiv.Perm.mul_apply, ← map_mul, Pair.mul_self hP hd, map_one,
        Equiv.Perm.one_apply] at this
    | one =>
      intro e
      rw [map_one, Equiv.Perm.one_apply]
    | mul g h _ _ hg hh =>
      intro e
      rw [map_mul, Equiv.Perm.mul_apply, ← hg, ← hh]
    | inv g _ hg =>
      intro e
      rw [hg (Pair.conjPerm hP g⁻¹ e), ← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel,
        map_one, Equiv.Perm.one_apply]
  obtain ⟨p, hp⟩ := hne
  obtain ⟨e₀, rfl⟩ := hℓ hp
  rintro _ ⟨e, rfl⟩
  obtain ⟨g, hg⟩ := isConj_iff.1 (Pair.isConj hP e₀.2 e.2)
  have heq : Pair.conjPerm hP g e₀ = e := Subtype.ext (by rw [Pair.conjPerm_apply, hg])
  rw [← heq]
  exact (hall g e₀).1 hp

@[expose] def sympConfig (hP : Pair X E) (hZ : Subgroup.center X = ⊥)
    (hS : IsSimpleGroup (commutator X)) (hsymp : IsSymplecticType E)
    (htrans : ∀ a ∈ E, ∀ b ∈ E, ∀ c ∈ E, ∀ e ∈ E, a ≠ b → a * b = b * a → c ≠ e →
      c * e = e * c → ∃ g : X, g * a * g⁻¹ = c ∧ g * b * g⁻¹ = e) :
    SympConfig (SympModule E) where
  b := sympForm E
  D := Set.range bar
  self_eq_zero := sympForm_self E
  comm := sympForm_comm E
  nondeg := sympForm_nondegenerate E
  zero_notMem := by
    rintro ⟨e, he⟩
    exact bar_ne_zero hP hZ hS hsymp e he
  span_eq := span_range_bar E
  add_mem := by
    rintro _ ⟨d, rfl⟩ _ ⟨e, rfl⟩ h
    refine ⟨Pair.conjPerm hP e d, ?_⟩
    rw [← rho_bar, rho_apply_eq hP hsymp, h, one_smul]
  eq_of_closed := eq_range_bar_of_closed hP hsymp
  trans := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ _ ⟨c, rfl⟩ _ ⟨e, rfl⟩ hab hb hce hb'
    rw [sympForm_bar, ncomm_eq_zero_iff] at hb hb'
    obtain ⟨g, hga, hgb⟩ := htrans a a.2 b b.2 c c.2 e e.2
      (fun h => hab (congrArg bar (Subtype.ext h))) hb (fun h => hce (congrArg bar (Subtype.ext h)))
      hb'
    refine ⟨(rho hP g : SympModule E →ₗ[ZMod 2] SympModule E), sympForm_rho hP g, ?_, ?_, ?_⟩
    · rintro _ ⟨f, rfl⟩
      exact ⟨Pair.conjPerm hP g f, (rho_bar hP g f).symm⟩
    · change rho hP g (bar a) = bar c
      rw [rho_bar]
      exact congrArg bar (Subtype.ext (by rw [Pair.conjPerm_apply, hga]))
    · change rho hP g (bar b) = bar e
      rw [rho_bar]
      exact congrArg bar (Subtype.ext (by rw [Pair.conjPerm_apply, hgb]))

end Config

section Matrices

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {n : ℕ}

@[expose] def conjAut (e : V ≃ₗ[ZMod 2] (Fin n → ZMod 2)) :
    (V ≃ₗ[ZMod 2] V) ≃* ((Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n → ZMod 2)) where
  toFun f := e.symm.trans (f.trans e)
  invFun f := e.trans (f.trans e.symm)
  left_inv f := LinearEquiv.ext fun v => by simp
  right_inv f := LinearEquiv.ext fun v => by simp
  map_mul' f g := LinearEquiv.ext fun v => by simp [LinearEquiv.mul_apply]

@[expose] def toGL (e : V ≃ₗ[ZMod 2] (Fin n → ZMod 2)) :
    (V ≃ₗ[ZMod 2] V) ≃* GL (Fin n) (ZMod 2) :=
  (conjAut e).trans ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2)
    (Fin n → ZMod 2)).symm.trans Matrix.GeneralLinearGroup.toLin.symm)

theorem toGL_mulVec (e : V ≃ₗ[ZMod 2] (Fin n → ZMod 2)) (f : V ≃ₗ[ZMod 2] V)
    (x : Fin n → ZMod 2) :
    ((toGL e f : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x =
      e (f (e.symm x)) := by
  rw [← Matrix.mulVecLin_apply, ← Matrix.GeneralLinearGroup.coe_toLin, toGL, MulEquiv.trans_apply,
    MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  rfl

theorem gl_ext {g h : GL (Fin n) (ZMod 2)}
    (H : ∀ x, (g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x =
      (h : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x) :
    g = h :=
  Units.ext (Matrix.toLin'.injective (LinearMap.ext fun x => by
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, H]))

theorem fischerLinearModel_of_image {G : Type} [Group G] {D : Set G}
    (hcl : Subgroup.closure D = ⊤) (ρ : G →* GL (Fin n) (ZMod 2)) (hinj : Function.Injective ρ)
    {T : Set (GL (Fin n) (ZMod 2))} (hT : ρ '' D = T) :
    fischerLinearModel D (Subgroup.closure T) T := by
  have hrange : ρ.range = Subgroup.closure T := by
    rw [MonoidHom.range_eq_map, ← hcl, MonoidHom.map_closure, hT]
  refine ⟨(MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange), fun g => ?_⟩
  rw [MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply, MonoidHom.ofInjective_apply]
  constructor
  · intro hg
    exact hT ▸ ⟨g, hg, rfl⟩
  · intro hg
    rw [← hT] at hg
    obtain ⟨d, hd, hdg⟩ := hg
    rwa [← hinj hdg]

end Matrices

theorem SympConfig.two_le_of_orth {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (C : SympConfig V) {m : ℕ}
    (hm : Module.finrank (ZMod 2) V = 2 * m) {x y : V} (hx : x ∈ C.D) (hy : y ∈ C.D)
    (hxy : x ≠ y) (hb : C.b x y = 0) : 2 ≤ m := by
  have hnd : C.b.Nondegenerate :=
    ⟨fun u hu => C.nondeg u hu, fun u hu => C.nondeg u fun v => by rw [C.comm]; exact hu v⟩
  have hli : LinearIndependent (ZMod 2) ![x, y] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    rcases zmod_two_cases s with rfl | rfl <;> rcases zmod_two_cases t with rfl | rfl
    · exact ⟨rfl, rfl⟩
    · rw [zero_smul, one_smul, zero_add] at hst
      exact absurd hst (C.ne_zero_of_mem hy)
    · rw [zero_smul, one_smul, add_zero] at hst
      exact absurd hst (C.ne_zero_of_mem hx)
    · rw [one_smul, one_smul] at hst
      exact absurd (zmod_two_eq_of_add_eq_zero hst) hxy
  have hW : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) {x, y}) = 2 := by
    rw [← Matrix.range_cons_cons_empty x y ![], finrank_span_eq_card hli, Fintype.card_fin]
  have hiso : Submodule.span (ZMod 2) {x, y} ≤
      C.b.orthogonal (Submodule.span (ZMod 2) {x, y}) := by
    rw [Submodule.span_le]
    intro z hz
    rw [SetLike.mem_coe, LinearMap.BilinForm.mem_orthogonal_span_pair_iff]
    rcases hz with rfl | hz
    · exact ⟨C.self_eq_zero z, by rw [C.comm]; exact hb⟩
    · rw [Set.mem_singleton_iff] at hz
      subst hz
      exact ⟨hb, C.self_eq_zero _⟩
  have h1 := Submodule.finrank_mono hiso
  rw [LinearMap.BilinForm.finrank_orthogonal hnd, hW, hm] at h1
  omega

section Cases

theorem injective_toGL_comp_rho (hP : Pair X E) (hZ : Subgroup.center X = ⊥)
    (hS : IsSimpleGroup (commutator X)) (hsymp : IsSymplecticType E) {n : ℕ}
    (e : SympModule E ≃ₗ[ZMod 2] (Fin n → ZMod 2)) :
    Function.Injective ((toGL e).toMonoidHom.comp (rho hP)) :=
  (toGL e).injective.comp (rho_injective hP hZ hS hsymp)

theorem image_eq_fischerTransvections (hP : Pair X E) (hsymp : IsSymplecticType E) {n : ℕ}
    (e : SympModule E ≃ₗ[ZMod 2] (Fin n → ZMod 2))
    (P : (Fin n → ZMod 2) → Prop) (hPD : ∀ v, P v ↔ e.symm v ∈ Set.range (bar (E := E)))
    (β : (Fin n → ZMod 2) → (Fin n → ZMod 2) → ZMod 2)
    (hβ : ∀ x y, β x y = sympForm E (e.symm x) (e.symm y)) :
    ((toGL e).toMonoidHom.comp (rho hP)) '' E = fischerTransvections β P := by
  have hρ : ∀ d : E, ∀ x, (((toGL e).toMonoidHom.comp (rho hP) d : GL (Fin n) (ZMod 2)) :
      Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x = x + β x (e (bar d)) • e (bar d) := by
    intro d x
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, toGL_mulVec, rho_apply_eq hP hsymp,
      map_add, map_smul, LinearEquiv.apply_symm_apply, hβ, LinearEquiv.symm_apply_apply]
  ext g
  constructor
  · rintro ⟨d, hd, rfl⟩
    exact ⟨e (bar ⟨d, hd⟩), (hPD _).2 ⟨⟨d, hd⟩, by rw [LinearEquiv.symm_apply_apply]⟩,
      hρ ⟨d, hd⟩⟩
  · rintro ⟨v, hv, hgv⟩
    obtain ⟨d, hd⟩ := (hPD v).1 hv
    have hdv : e (bar d) = v := by rw [hd, LinearEquiv.apply_symm_apply]
    refine ⟨d, d.2, gl_ext fun x => ?_⟩
    rw [hρ d x, hgv, hdv]

theorem exists_finrank_eq (hP : Pair X E) :
    ∃ m : ℕ, Module.finrank (ZMod 2) (SympModule E) = 2 * m := by
  have := Pair.finite hP
  have hnd : (sympForm E).Nondegenerate :=
    ⟨fun u hu => sympForm_nondegenerate E u hu,
      fun u hu => sympForm_nondegenerate E u fun v => by rw [sympForm_comm]; exact hu v⟩
  obtain ⟨m, hm⟩ := LinearMap.BilinForm.IsAlt.even_finrank (sympForm_self E) hnd
  exact ⟨m, by omega⟩

variable (hP : Pair X E) (hZ : Subgroup.center X = ⊥) (hS : IsSimpleGroup (commutator X))
  (hsymp : IsSymplecticType E)
  (htrans : ∀ a ∈ E, ∀ b ∈ E, ∀ c ∈ E, ∀ e ∈ E, a ≠ b → a * b = b * a → c ≠ e →
    c * e = e * c → ∃ g : X, g * a * g⁻¹ = c ∧ g * b * g⁻¹ = e)

theorem classicalConclusion_sp
    (hall : ∀ v, v ∈ (sympConfig hP hZ hS hsymp htrans).D ↔ v ≠ 0)
    (hpair : ∃ x ∈ (sympConfig hP hZ hS hsymp htrans).D, ∃ y ∈ (sympConfig hP hZ hS hsymp htrans).D,
      x ≠ y ∧ (sympConfig hP hZ hS hsymp htrans).b x y = 0) :
    ∃ m : ℕ, 2 ≤ m ∧ ∃ b : LinearMap.BilinForm (ZMod 2) (Fin (2 * m) → ZMod 2),
      (∀ x, b x x = 0) ∧ (∀ x, (∀ y, b x y = 0) → x = 0) ∧
      fischerLinearModel E
        (fischerMatrixGroup fun A => ∀ x y, b (A *ᵥ x) (A *ᵥ y) = b x y)
        (fischerTransvections (fun x y => b x y) fun v => v ≠ 0) := by
  have := Pair.finite hP
  obtain ⟨m, hm⟩ := exists_finrank_eq hP
  obtain ⟨x, hx, y, hy, hxy, hb⟩ := hpair
  have h2 := (sympConfig hP hZ hS hsymp htrans).two_le_of_orth hm hx hy hxy hb
  let e := (Module.finBasisOfFinrankEq (ZMod 2) (SympModule E) hm).equivFun
  let b' := LinearMap.BilinForm.congr e (sympForm E)
  have hb' : ∀ x y, b' x y = sympForm E (e.symm x) (e.symm y) := fun x y =>
    LinearMap.BilinForm.congr_apply e _ x y
  have halt : ∀ x, b' x x = 0 := fun x => by rw [hb', sympForm_self]
  have hnd : ∀ x, (∀ y, b' x y = 0) → x = 0 := fun x hx => by
    have : e.symm x = 0 := sympForm_nondegenerate E _ fun w => by
      have := hx (e w)
      rwa [hb', LinearEquiv.symm_apply_apply] at this
    simpa using congrArg e this
  refine ⟨m, h2, b', halt, hnd, ?_⟩
  rw [fischerMatrixGroup_symplectic_eq_closure m b' halt hnd]
  refine fischerLinearModel_of_image (Pair.closure_eq hP) _
    (injective_toGL_comp_rho hP hZ hS hsymp e)
    (image_eq_fischerTransvections hP hsymp e _ (fun v => ?_) (fun x y => b' x y) hb')
  rw [show (e.symm v ∈ Set.range (bar (E := E))) = (e.symm v ∈
    (sympConfig hP hZ hS hsymp htrans).D) from rfl, hall]
  simp

theorem classicalConclusion_o {Q : QuadraticForm (ZMod 2) (SympModule E)}
    (hpol : ∀ u v, QuadraticMap.polar Q u v = (sympConfig hP hZ hS hsymp htrans).b u v)
    (hQ : ∀ v, v ∈ (sympConfig hP hZ hS hsymp htrans).D ↔ Q v = 1)
    (hpair : ∃ x ∈ (sympConfig hP hZ hS hsymp htrans).D, ∃ y ∈ (sympConfig hP hZ hS hsymp htrans).D,
      x ≠ y ∧ (sympConfig hP hZ hS hsymp htrans).b x y = 0) :
    ∃ m : ℕ, 2 ≤ m ∧ ∃ Q : QuadraticForm (ZMod 2) (Fin (2 * m) → ZMod 2),
      (∀ x, (∀ y, QuadraticMap.polar Q x y = 0) → x = 0) ∧
      (m = 2 → ¬ ∃ W : Submodule (ZMod 2) (Fin (2 * m) → ZMod 2),
        Module.finrank (ZMod 2) W = 2 ∧ ∀ w ∈ W, Q w = 0) ∧
      fischerLinearModel E
        (fischerMatrixGroup fun A => ∀ x, Q (A *ᵥ x) = Q x)
        (fischerTransvections (QuadraticMap.polar Q) fun v => Q v = 1) := by
  have := Pair.finite hP
  obtain ⟨m, hm⟩ := exists_finrank_eq hP
  obtain ⟨x, hx, y, hy, hxy, hb⟩ := hpair
  have h2 := (sympConfig hP hZ hS hsymp htrans).two_le_of_orth hm hx hy hxy hb
  let e := (Module.finBasisOfFinrankEq (ZMod 2) (SympModule E) hm).equivFun
  let Q' := Q.comp (e.symm : (Fin (2 * m) → ZMod 2) →ₗ[ZMod 2] SympModule E)
  have hQ' : ∀ x, Q' x = Q (e.symm x) := fun x => QuadraticMap.comp_apply Q _ x
  have hpol' : ∀ x y, QuadraticMap.polar Q' x y = sympForm E (e.symm x) (e.symm y) := by
    intro x y
    rw [QuadraticMap.polar, hQ', hQ', hQ', map_add, ← QuadraticMap.polar]
    exact hpol _ _
  have hnd : ∀ x, (∀ y, QuadraticMap.polar Q' x y = 0) → x = 0 := fun x hx => by
    have : e.symm x = 0 := sympForm_nondegenerate E _ fun w => by
      have := hx (e w)
      rwa [hpol', LinearEquiv.symm_apply_apply] at this
    simpa using congrArg e this
  have hplus : m = 2 → ¬ ∃ W : Submodule (ZMod 2) (Fin (2 * m) → ZMod 2),
      Module.finrank (ZMod 2) W = 2 ∧ ∀ w ∈ W, Q' w = 0 := by
    rintro hm2 ⟨W, hW, hWQ⟩
    refine (sympConfig hP hZ hS hsymp htrans).not_exists_totallySingular (by rw [hm, hm2]) hpol
      hQ ⟨W.map (e.symm : (Fin (2 * m) → ZMod 2) →ₗ[ZMod 2] SympModule E), ?_, ?_⟩
    · exact (LinearEquiv.finrank_map_eq e.symm W).trans hW
    · rintro _ ⟨w, hw, rfl⟩
      show Q (e.symm w) = 0
      rw [← hQ']
      exact hWQ w hw
  refine ⟨m, h2, Q', hnd, hplus, ?_⟩
  rw [fischerMatrixGroup_orthogonal_eq_closure m h2 Q' hnd hplus]
  refine fischerLinearModel_of_image (Pair.closure_eq hP) _
    (injective_toGL_comp_rho hP hZ hS hsymp e)
    (image_eq_fischerTransvections hP hsymp e _ (fun v => ?_) _ hpol')
  rw [hQ', ← hQ]
  rfl

theorem classicalConclusion_sym (hTN : (sympConfig hP hZ hS hsymp htrans).TN) :
    ∃ m : ℕ, (m = 3 ∨ 5 ≤ m) ∧
      ∃ φ : X ≃* Equiv.Perm (Fin m), ∀ g : X, g ∈ E ↔ (φ g).IsSwap := by
  have := Pair.finite hP
  have : Finite (SympModule E) := Module.finite_of_finite (ZMod 2)
  obtain ⟨e₀, he₀⟩ := Pair.nonempty hP
  exact (sympConfig hP hZ hS hsymp htrans).exists_mulEquiv_perm hTN (rho hP)
    (rho_injective hP hZ hS hsymp) (sympForm_rho hP) (rho_mem_range_bar_iff hP) E bar
    (fun d => ⟨d, rfl⟩) (rho_apply_eq hP hsymp) (fun v hv => hv) ⟨bar ⟨e₀, he₀⟩, ⟨e₀, he₀⟩, rfl⟩

end Cases

end Symplectic

open Symplectic

theorem classicalConclusion_of_symplecticType (hP : Pair X E) (hZ : Subgroup.center X = ⊥)
    (hS : IsSimpleGroup (commutator X)) (hsymp : IsSymplecticType E)
    (htrans : ∀ a ∈ E, ∀ b ∈ E, ∀ c ∈ E, ∀ e ∈ E, a ≠ b → a * b = b * a → c ≠ e →
      c * e = e * c → ∃ g : X, g * a * g⁻¹ = c ∧ g * b * g⁻¹ = e) :
    ClassicalConclusion X E := by
  rcases (sympConfig hP hZ hS hsymp htrans).trichotomy with
    ⟨hall, hpair⟩ | ⟨⟨Q, hpol, hQ⟩, hpair⟩ | hTN
  · exact Or.inr (Or.inl (classicalConclusion_sp hP hZ hS hsymp htrans hall hpair))
  · exact Or.inr (Or.inr (Or.inl (classicalConclusion_o hP hZ hS hsymp htrans hpol hQ hpair)))
  · exact Or.inl (classicalConclusion_sym hP hZ hS hsymp htrans hTN)

end CFSG.Fischer.Classification
