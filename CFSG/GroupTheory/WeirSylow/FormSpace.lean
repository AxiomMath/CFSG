module

public import CFSG.GroupTheory.WeirSylow.Defs
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

public section

namespace CFSG.GroupTheory.WeirSylow

open Module

section Isometry

variable (K : Type*) [Semiring K] {V : Type*} [AddCommMonoid V] [Module K V] {R : Type*}

@[expose] def formIsometryGroup (F : V → V → R) : Subgroup (V ≃ₗ[K] V) where
  carrier := {g | ∀ x y, F (g x) (g y) = F x y}
  one_mem' _ _ := rfl
  mul_mem' {a b} ha hb x y := (ha (b x) (b y)).trans (hb x y)
  inv_mem' {g} hg x y := by
    have h := hg (g.symm x) (g.symm y)
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h
    exact h.symm

variable {K}

theorem mem_formIsometryGroup {F : V → V → R} {g : V ≃ₗ[K] V} :
    g ∈ formIsometryGroup K F ↔ ∀ x y, F (g x) (g y) = F x y :=
  Iff.rfl

@[expose] def formIsometryGroupCongr {V' : Type*} [AddCommMonoid V'] [Module K V']
    {F : V → V → R} {F' : V' → V' → R} (e : V ≃ₗ[K] V')
    (he : ∀ x y, F' (e x) (e y) = F x y) :
    formIsometryGroup K F ≃* formIsometryGroup K F' where
  toFun g := ⟨e.symm.trans (g.1.trans e), fun x y => by
    change F' (e (g.1 (e.symm x))) (e (g.1 (e.symm y))) = F' x y
    rw [he, g.2, ← he, e.apply_symm_apply, e.apply_symm_apply]⟩
  invFun g := ⟨e.trans (g.1.trans e.symm), fun x y => by
    change F (e.symm (g.1 (e x))) (e.symm (g.1 (e y))) = F x y
    rw [← he, e.apply_symm_apply, e.apply_symm_apply, g.2, he]⟩
  left_inv g := Subtype.ext (LinearEquiv.ext fun x => by
    change e.symm (e (g.1 (e.symm (e x)))) = g.1 x
    rw [e.symm_apply_apply, e.symm_apply_apply])
  right_inv g := Subtype.ext (LinearEquiv.ext fun x => by
    change e (e.symm (g.1 (e (e.symm x)))) = g.1 x
    rw [e.apply_symm_apply, e.apply_symm_apply])
  map_mul' g h := Subtype.ext (LinearEquiv.ext fun x => by
    change e (g.1 (h.1 (e.symm x))) = e (g.1 (e.symm (e (h.1 (e.symm x)))))
    rw [e.symm_apply_apply])

theorem formIsometryGroupCongr_apply {V' : Type*} [AddCommMonoid V'] [Module K V']
    {F : V → V → R} {F' : V' → V' → R} (e : V ≃ₗ[K] V')
    (he : ∀ x y, F' (e x) (e y) = F x y) (g : formIsometryGroup K F) (x : V') :
    (formIsometryGroupCongr e he g).1 x = e (g.1 (e.symm x)) :=
  rfl

end Isometry

section Sums

variable (K : Type*) [Semiring K] {R : Type*}

@[expose] def prodForm [Add R] {V₁ V₂ : Type*} (F₁ : V₁ → V₁ → R) (F₂ : V₂ → V₂ → R)
    (x y : V₁ × V₂) : R :=
  F₁ x.1 y.1 + F₂ x.2 y.2

@[expose] def piForm [AddCommMonoid R] {ι : Type*} [Fintype ι] {V : ι → Type*}
    (F : ∀ i, V i → V i → R) (x y : ∀ i, V i) : R :=
  ∑ i, F i (x i) (y i)

variable {V₁ V₂ : Type*} [AddCommMonoid V₁] [Module K V₁] [AddCommMonoid V₂] [Module K V₂]

@[expose] def prodIsometryHom [Add R] (F₁ : V₁ → V₁ → R) (F₂ : V₂ → V₂ → R) :
    formIsometryGroup K F₁ × formIsometryGroup K F₂ →* formIsometryGroup K (prodForm F₁ F₂) where
  toFun g := ⟨g.1.1.prodCongr g.2.1, fun (x y : V₁ × V₂) => by
    change F₁ (g.1.1 x.1) (g.1.1 y.1) + F₂ (g.2.1 x.2) (g.2.1 y.2) = F₁ x.1 y.1 + F₂ x.2 y.2
    rw [g.1.2, g.2.2]⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem prodIsometryHom_injective [Add R] (F₁ : V₁ → V₁ → R) (F₂ : V₂ → V₂ → R) :
    Function.Injective (prodIsometryHom K F₁ F₂) := by
  intro g h hgh
  have h' : ∀ x : V₁ × V₂, (g.1.1 x.1, g.2.1 x.2) = (h.1.1 x.1, h.2.1 x.2) := fun x =>
    LinearEquiv.congr_fun (congrArg Subtype.val hgh) x
  refine Prod.ext (Subtype.ext (LinearEquiv.ext fun x => ?_))
    (Subtype.ext (LinearEquiv.ext fun x => ?_))
  · exact congrArg Prod.fst (h' (x, 0))
  · exact congrArg Prod.snd (h' (0, x))

variable {ι : Type*} [Fintype ι] {V : ι → Type*} [∀ i, AddCommMonoid (V i)] [∀ i, Module K (V i)]

@[expose] def piIsometryHom [AddCommMonoid R] (F : ∀ i, V i → V i → R) :
    (∀ i, formIsometryGroup K (F i)) →* formIsometryGroup K (piForm F) where
  toFun g := ⟨LinearEquiv.piCongrRight fun i => (g i).1, fun x y => by
    change ∑ i, F i ((g i).1 (x i)) ((g i).1 (y i)) = ∑ i, F i (x i) (y i)
    exact Finset.sum_congr rfl fun i _ => (g i).2 _ _⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem piIsometryHom_injective [AddCommMonoid R] [DecidableEq ι] (F : ∀ i, V i → V i → R) :
    Function.Injective (piIsometryHom K F) := by
  intro g h hgh
  funext i
  refine Subtype.ext (LinearEquiv.ext fun v => ?_)
  have := LinearEquiv.congr_fun (congrArg Subtype.val hgh) (Pi.single i v)
  have hi := congrFun this i
  change (g i).1 (Pi.single i v i) = (h i).1 (Pi.single i v i) at hi
  rwa [Pi.single_eq_same] at hi

end Sums

section Wreath

variable (K : Type*) [Semiring K] {V : Type*} [AddCommMonoid V] [Module K V] {R : Type*}
  {D C : Type*} [Group D] [Group C]

@[expose] def wreathLinearEquiv {F : V → V → R} (ρ : D →* formIsometryGroup K F)
    (w : D ≀ᵣ C) : (C → V) ≃ₗ[K] (C → V) :=
  (LinearEquiv.funCongrLeft K V (Equiv.mulLeft w.right⁻¹)).trans
    (LinearEquiv.piCongrRight fun x => (ρ (w.left x)).1)

theorem wreathLinearEquiv_apply {F : V → V → R} (ρ : D →* formIsometryGroup K F)
    (w : D ≀ᵣ C) (v : C → V) (x : C) :
    wreathLinearEquiv K ρ w v x = (ρ (w.left x)).1 (v (w.right⁻¹ * x)) :=
  rfl

variable [AddCommMonoid R] [Fintype C]

@[expose] def wreathIsometryHom {F : V → V → R} (ρ : D →* formIsometryGroup K F) :
    D ≀ᵣ C →* formIsometryGroup K (piForm fun _ : C => F) where
  toFun w := ⟨wreathLinearEquiv K ρ w, fun v v' => by
    change ∑ x, F ((ρ (w.left x)).1 (v (w.right⁻¹ * x))) ((ρ (w.left x)).1 (v' (w.right⁻¹ * x)))
      = ∑ x, F (v x) (v' x)
    calc _ = ∑ x, F (v (w.right⁻¹ * x)) (v' (w.right⁻¹ * x)) :=
          Finset.sum_congr rfl fun x _ => (ρ (w.left x)).2 _ _
      _ = ∑ x, F (v x) (v' x) := Fintype.sum_equiv (Equiv.mulLeft w.right⁻¹) _ _ fun x => rfl⟩
  map_one' := by
    refine Subtype.ext (LinearEquiv.ext fun v => funext fun x => ?_)
    change (ρ 1).1 (v (1⁻¹ * x)) = v x
    rw [map_one, inv_one, one_mul]
    rfl
  map_mul' w w' := by
    refine Subtype.ext (LinearEquiv.ext fun v => funext fun x => ?_)
    change (ρ ((w * w').left x)).1 (v ((w * w').right⁻¹ * x)) =
      (ρ (w.left x)).1 ((ρ (w'.left (w.right⁻¹ * x))).1 (v (w'.right⁻¹ * (w.right⁻¹ * x))))
    rw [RegularWreathProduct.mul_def]
    change (ρ (w.left x * w'.left (w.right⁻¹ * x))).1 (v ((w.right * w'.right)⁻¹ * x)) = _
    rw [map_mul, mul_inv_rev, mul_assoc]
    rfl

theorem coe_wreathIsometryHom {F : V → V → R} (ρ : D →* formIsometryGroup K F) (w : D ≀ᵣ C) :
    (wreathIsometryHom K ρ w).1 = wreathLinearEquiv K ρ w :=
  rfl

theorem wreathIsometryHom_injective [DecidableEq C] [Nontrivial V] {F : V → V → R}
    {ρ : D →* formIsometryGroup K F} (hρ : Function.Injective ρ) :
    Function.Injective (wreathIsometryHom K (C := C) ρ) := by
  intro w w' h
  have h' : ∀ (v : C → V) (x : C), (ρ (w.left x)).1 (v (w.right⁻¹ * x)) =
      (ρ (w'.left x)).1 (v (w'.right⁻¹ * x)) := fun v x => by
    have := congrFun (LinearEquiv.congr_fun (congrArg Subtype.val h) v) x
    rwa [coe_wreathIsometryHom, coe_wreathIsometryHom, wreathLinearEquiv_apply,
      wreathLinearEquiv_apply] at this
  obtain ⟨u, hu⟩ := exists_ne (0 : V)
  have hright : w.right = w'.right := by
    by_contra hne
    have h1 := h' (Pi.single 1 u) w.right
    rw [inv_mul_cancel, Pi.single_eq_same,
      Pi.single_eq_of_ne (fun heq => hne (inv_mul_eq_one.1 heq).symm), map_zero] at h1
    exact hu ((ρ (w.left w.right)).1.injective (h1.trans (map_zero _).symm))
  have hleft : ∀ x, w.left x = w'.left x := fun x =>
    hρ (Subtype.ext (LinearEquiv.ext fun u => by
      have h1 := h' (fun _ => u) x
      exact h1))
  exact RegularWreathProduct.ext (funext hleft) hright

end Wreath

structure FormSpace (K : Type) [Field K] (R : Type) where
  V : Type
  [instAddCommGroup : AddCommGroup V]
  [instModule : Module K V]
  [instFiniteDimensional : FiniteDimensional K V]
  F : V → V → R

attribute [instance] FormSpace.instAddCommGroup FormSpace.instModule
  FormSpace.instFiniteDimensional

namespace FormSpace

variable {K : Type} [Field K] {R : Type}

abbrev isom (S : FormSpace K R) : Subgroup (S.V ≃ₗ[K] S.V) :=
  formIsometryGroup K S.F

abbrev pi [AddCommMonoid R] {ι : Type} [Fintype ι] (S : ι → FormSpace K R) :
    FormSpace K R where
  V := ∀ i, (S i).V
  F := piForm fun i => (S i).F

abbrev prod [Add R] (S T : FormSpace K R) : FormSpace K R where
  V := S.V × T.V
  F := prodForm S.F T.F

theorem finrank_pi [AddCommMonoid R] {ι : Type} [Fintype ι] (S : ι → FormSpace K R) :
    finrank K (pi S).V = ∑ i, finrank K (S i).V :=
  Module.finrank_pi_fintype K

theorem finrank_prod [Add R] (S T : FormSpace K R) :
    finrank K (prod S T).V = finrank K S.V + finrank K T.V :=
  Module.finrank_prod

end FormSpace

section Towers

variable {K : Type} [Field K] {R : Type} [AddCommMonoid R]

theorem sum_getElem_mul_pow (p : ℕ) :
    ∀ L : List ℕ, ∑ i : Fin L.length, L[i] * p ^ (i : ℕ) = Nat.ofDigits p L
  | [] => by simp
  | d :: L => by
    rw [Nat.ofDigits_cons, ← sum_getElem_mul_pow p L, Finset.mul_sum]
    change ∑ i : Fin (L.length + 1), (d :: L)[i] * p ^ (i : ℕ) = _
    rw [Fin.sum_univ_succ]
    simp only [Fin.getElem_fin, Fin.val_zero, pow_zero, mul_one, Fin.val_succ,
      List.getElem_cons_succ, List.getElem_cons_zero, pow_succ]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    ring

theorem exists_wreathTower_rep (p : ℕ) [NeZero p] (P : FormSpace K R → Prop)
    (hP : ∀ (ι : Type) [Fintype ι] (S : ι → FormSpace K R), (∀ i, P (S i)) → P (FormSpace.pi S))
    {T : Type} [Group T] (S₀ : FormSpace K R) (h₀ : P S₀) (hS₀ : Nontrivial S₀.V)
    (ρ : T →* S₀.isom) (hρ : Function.Injective ρ) :
    ∀ i : ℕ, ∃ S : FormSpace K R, P S ∧ Nontrivial S.V ∧
      finrank K S.V = finrank K S₀.V * p ^ i ∧
      ∃ φ : wreathTower p T i →* S.isom, Function.Injective φ
  | 0 => ⟨S₀, h₀, hS₀, by rw [pow_zero, mul_one], ρ, hρ⟩
  | i + 1 => by
    obtain ⟨S, hPS, hS, hdim, φ, hφ⟩ := exists_wreathTower_rep p P hP S₀ h₀ hS₀ ρ hρ i
    classical
    let ψ : wreathTower p T i ≀ᵣ Multiplicative (ZMod p) →*
        (FormSpace.pi fun _ : Multiplicative (ZMod p) => S).isom :=
      wreathIsometryHom K (C := Multiplicative (ZMod p)) φ
    refine ⟨FormSpace.pi fun _ : Multiplicative (ZMod p) => S, hP _ _ fun _ => hPS, ?_, ?_,
      ψ, wreathIsometryHom_injective K (C := Multiplicative (ZMod p)) hφ⟩
    · change Nontrivial (Multiplicative (ZMod p) → S.V)
      infer_instance
    · rw [FormSpace.finrank_pi, Finset.sum_const, Finset.card_univ, Fintype.card_multiplicative,
        ZMod.card, hdim, smul_eq_mul, pow_succ]
      ring

theorem exists_sigmaModel_rep (p : ℕ) [NeZero p] (P : FormSpace K R → Prop)
    (hP : ∀ (ι : Type) [Fintype ι] (S : ι → FormSpace K R), (∀ i, P (S i)) → P (FormSpace.pi S))
    {a : ℕ} (S₀ : FormSpace K R) (h₀ : P S₀) (hS₀ : Nontrivial S₀.V)
    (ρ : Multiplicative (ZMod (p ^ a)) →* S₀.isom) (hρ : Function.Injective ρ) (e N : ℕ) :
    ∃ S : FormSpace K R, P S ∧ finrank K S.V = finrank K S₀.V * (N / e) ∧
      ∃ φ : sigmaModel p e a N →* S.isom, Function.Injective φ := by
  classical
  choose S hPS hnt hdim φ hφ using exists_wreathTower_rep p P hP S₀ h₀ hS₀ ρ hρ
  let S' : Fin (Nat.digits p (N / e)).length → FormSpace K R := fun i =>
    FormSpace.pi fun _ : Fin (Nat.digits p (N / e))[i] => S i
  refine ⟨FormSpace.pi S', hP _ _ fun i => hP _ _ fun _ => hPS i, ?_,
    (piIsometryHom K (fun i => (S' i).F)).comp
      (MonoidHom.piMap fun i =>
        (piIsometryHom K (fun _ : Fin (Nat.digits p (N / e))[i] => (S i).F)).comp
          (MonoidHom.piMap fun _ => φ i)), ?_⟩
  · rw [FormSpace.finrank_pi]
    simp only [S', Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul, hdim]
    calc ∑ x : Fin (Nat.digits p (N / e)).length,
          (Nat.digits p (N / e))[x] * (finrank K S₀.V * p ^ (x : ℕ))
        = finrank K S₀.V * ∑ x : Fin (Nat.digits p (N / e)).length,
            (Nat.digits p (N / e))[x] * p ^ (x : ℕ) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ = finrank K S₀.V * (N / e) := by rw [sum_getElem_mul_pow, Nat.ofDigits_digits]
  · refine (piIsometryHom_injective K _).comp fun g h hgh => funext fun i => ?_
    exact funext fun j => hφ i (congrFun ((piIsometryHom_injective K _) (congrFun hgh i)) j)

theorem exists_rep_prod {G : Type} [Group G] (S T : FormSpace K R) (φ : G →* S.isom)
    (hφ : Function.Injective φ) :
    ∃ ψ : G →* (FormSpace.prod S T).isom, Function.Injective ψ :=
  ⟨(prodIsometryHom K S.F T.F).comp (φ.prod 1),
    (prodIsometryHom_injective K S.F T.F).comp fun _ _ hgh => hφ (congrArg Prod.fst hgh)⟩

end Towers

end CFSG.GroupTheory.WeirSylow
