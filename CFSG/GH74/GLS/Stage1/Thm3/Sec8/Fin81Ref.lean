module

public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.GroupTheory.Sylow
public import Mathlib.Tactic.DeriveFintype

public section

open Equiv

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8.Fin81

abbrev V4 := ZMod 4 × ZMod 4

@[expose] def pt (v : V4) : Fin 4 → ZMod 4 := ![0, v.1, v.2, -v.1 - v.2]

@[expose] def actV (π : Perm (Fin 4)) (v : V4) : V4 :=
  ((pt v (π.symm 1) - pt v (π.symm 0)), (pt v (π.symm 2) - pt v (π.symm 0)))

theorem actV_add : ∀ (π : Perm (Fin 4)) (v w : V4), actV π (v + w) = actV π v + actV π w := by
  decide

theorem actV_one : ∀ v : V4, actV 1 v = v := by decide

theorem actV_mul : ∀ (π σ : Perm (Fin 4)) (v : V4), actV (π * σ) v = actV π (actV σ v) := by
  decide

@[expose] def refAut (π : Perm (Fin 4)) : MulAut (Multiplicative V4) where
  toFun x := Multiplicative.ofAdd (actV π (Multiplicative.toAdd x))
  invFun x := Multiplicative.ofAdd (actV π⁻¹ (Multiplicative.toAdd x))
  left_inv x := by
    simp only [toAdd_ofAdd]
    rw [← actV_mul, inv_mul_cancel, actV_one]; rfl
  right_inv x := by
    simp only [toAdd_ofAdd]
    rw [← actV_mul, mul_inv_cancel, actV_one]; rfl
  map_mul' x y := by
    simp only [toAdd_mul]
    rw [actV_add]; rfl

theorem refAut_apply (π : Perm (Fin 4)) (v : V4) :
    refAut π (Multiplicative.ofAdd v) = Multiplicative.ofAdd (actV π v) := rfl

@[expose] def refAct : Perm (Fin 4) →* MulAut (Multiplicative V4) where
  toFun := refAut
  map_one' := by
    refine MulEquiv.ext fun x => ?_
    show Multiplicative.ofAdd (actV 1 (Multiplicative.toAdd x)) = x
    rw [actV_one]; rfl
  map_mul' π σ := by
    refine MulEquiv.ext fun x => ?_
    show Multiplicative.ofAdd (actV (π * σ) (Multiplicative.toAdd x)) =
      Multiplicative.ofAdd (actV π (actV σ (Multiplicative.toAdd x)))
    rw [actV_mul]

@[expose] def inR0 (π : Perm (Fin 4)) : Prop :=
  ∀ i j : Fin 4, (i.val / 2 = j.val / 2) ↔ ((π i).val / 2 = (π j).val / 2)

instance : DecidablePred inR0 := fun π => by unfold inR0; infer_instance

theorem inR0_one : inR0 1 := by decide
theorem inR0_mul : ∀ π σ : Perm (Fin 4), inR0 π → inR0 σ → inR0 (π * σ) := by decide
theorem inR0_inv : ∀ π : Perm (Fin 4), inR0 π → inR0 π⁻¹ := by decide

@[expose] def R0 : Subgroup (Perm (Fin 4)) where
  carrier := {π | inR0 π}
  one_mem' := inR0_one
  mul_mem' := fun {a b} ha hb => inR0_mul a b ha hb
  inv_mem' := fun {a} ha => inR0_inv a ha

instance : DecidablePred (· ∈ R0) := fun π => (inferInstance : Decidable (inR0 π))

instance : Fintype R0 := Subtype.fintype _

theorem card_R0 : Nat.card R0 = 8 := by
  rw [Nat.card_eq_fintype_card]; decide

@[expose] def ψ : R0 →* MulAut (Multiplicative V4) := refAct.comp R0.subtype

abbrev M128 := Multiplicative V4 ⋊[ψ] R0

instance : Fintype M128 := Fintype.ofEquiv _ SemidirectProduct.equivProd.symm

theorem card_M128 : Nat.card M128 = 128 := by
  rw [SemidirectProduct.card, Nat.card_eq_fintype_card (α := Multiplicative V4), card_R0]
  decide +kernel

structure Mt where
  a : ZMod 4
  b : ZMod 4
  c : ZMod 4
  d : ZMod 4
deriving DecidableEq, Fintype

namespace Mt

@[expose] def mul (x y : Mt) : Mt :=
  ⟨x.a * y.a + x.b * y.c, x.a * y.b + x.b * y.d, x.c * y.a + x.d * y.c, x.c * y.b + x.d * y.d⟩

instance : Mul Mt := ⟨mul⟩

@[expose] def one : Mt := ⟨1, 0, 0, 1⟩

instance : One Mt := ⟨one⟩

@[expose] def det (x : Mt) : ZMod 4 := x.a * x.d - x.b * x.c

@[expose] def IsU (x : Mt) : Prop := x.det = 1 ∨ x.det = 3

instance : DecidablePred IsU := fun x => by unfold IsU; infer_instance

end Mt


@[expose] def M0 (π : Perm (Fin 4)) : Mt :=
  ⟨(actV π (1, 0)).1, (actV π (0, 1)).1, (actV π (1, 0)).2, (actV π (0, 1)).2⟩

@[expose] def ga : Perm (Fin 4) := swap 0 1
@[expose] def gb : Perm (Fin 4) := finRotate 4


theorem mt_class : ∀ α : Mt, α.IsU → ∀ β : Mt, β.IsU → α * α = 1 → β * β * β * β = 1 →
    (α * β) * (α * β) * (α * β) = 1 → α * (β * β) * α * (β * β) ≠ 1 →
    ∃ g : Mt, g.IsU ∧ ∃ π : Perm (Fin 4), g * α = M0 (π * ga * π⁻¹) * g ∧
      g * β = M0 (π * gb * π⁻¹) * g := by
  decide +kernel

@[expose] def e1 : V4 := (1, 0)
@[expose] def e2 : V4 := (0, 1)

theorem v4_eq (v : V4) : v = v.1.val • e1 + v.2.val • e2 := by
  ext <;> simp [e1, e2]

@[expose] def autMt (σ : MulAut (Multiplicative V4)) : Mt :=
  ⟨(Multiplicative.toAdd (σ (Multiplicative.ofAdd e1))).1,
    (Multiplicative.toAdd (σ (Multiplicative.ofAdd e2))).1,
    (Multiplicative.toAdd (σ (Multiplicative.ofAdd e1))).2,
    (Multiplicative.toAdd (σ (Multiplicative.ofAdd e2))).2⟩

theorem autMt_apply (σ : MulAut (Multiplicative V4)) (v : V4) :
    Multiplicative.toAdd (σ (Multiplicative.ofAdd v)) =
      ((autMt σ).a * v.1 + (autMt σ).b * v.2, (autMt σ).c * v.1 + (autMt σ).d * v.2) := by
  have h1 : Multiplicative.ofAdd v =
      Multiplicative.ofAdd e1 ^ v.1.val * Multiplicative.ofAdd e2 ^ v.2.val := by
    rw [← ofAdd_nsmul, ← ofAdd_nsmul, ← ofAdd_add, ← v4_eq]
  rw [h1, map_mul, map_pow, map_pow]
  simp only [toAdd_mul, toAdd_pow, autMt]
  ext <;> simp [nsmul_eq_mul]
  all_goals ring



theorem autMt_mul (σ τ : MulAut (Multiplicative V4)) : autMt (σ * τ) = autMt σ * autMt τ := by
  have h1 : Multiplicative.toAdd ((σ * τ) (Multiplicative.ofAdd e1)) =
      ((autMt σ).a * (autMt τ).a + (autMt σ).b * (autMt τ).c,
        (autMt σ).c * (autMt τ).a + (autMt σ).d * (autMt τ).c) := by
    rw [MulAut.mul_apply]
    have : τ (Multiplicative.ofAdd e1) = Multiplicative.ofAdd ((autMt τ).a, (autMt τ).c) := rfl
    rw [this, autMt_apply]
  have h2 : Multiplicative.toAdd ((σ * τ) (Multiplicative.ofAdd e2)) =
      ((autMt σ).a * (autMt τ).b + (autMt σ).b * (autMt τ).d,
        (autMt σ).c * (autMt τ).b + (autMt σ).d * (autMt τ).d) := by
    rw [MulAut.mul_apply]
    have : τ (Multiplicative.ofAdd e2) = Multiplicative.ofAdd ((autMt τ).b, (autMt τ).d) := rfl
    rw [this, autMt_apply]
  show Mt.mk (Multiplicative.toAdd ((σ * τ) (Multiplicative.ofAdd e1))).1
      (Multiplicative.toAdd ((σ * τ) (Multiplicative.ofAdd e2))).1
      (Multiplicative.toAdd ((σ * τ) (Multiplicative.ofAdd e1))).2
      (Multiplicative.toAdd ((σ * τ) (Multiplicative.ofAdd e2))).2 = Mt.mul _ _
  rw [h1, h2]
  rfl

theorem autMt_one : autMt (1 : MulAut (Multiplicative V4)) = 1 := rfl

theorem autMt_injective : Function.Injective autMt := by
  intro σ τ h
  refine MulEquiv.ext fun x => ?_
  have hx : x = Multiplicative.ofAdd (Multiplicative.toAdd x) := rfl
  rw [hx]
  apply Multiplicative.toAdd.injective
  rw [autMt_apply, autMt_apply, h]

theorem mt_isU_of_mul : ∀ x y : Mt, x * y = 1 → x.IsU := by decide +kernel

theorem autMt_isU (σ : MulAut (Multiplicative V4)) : (autMt σ).IsU := by
  apply mt_isU_of_mul (autMt σ) (autMt σ⁻¹)
  rw [← autMt_mul, mul_inv_cancel, autMt_one]


@[expose] def Mt.inv (x : Mt) : Mt := ⟨x.det * x.d, -(x.det * x.b), -(x.det * x.c), x.det * x.a⟩

theorem Mt.mul_inv_cancel' : ∀ x : Mt, x.IsU → x * x.inv = 1 ∧ x.inv * x = 1 := by decide +kernel

@[expose] def Mt.app (x : Mt) (v : V4) : V4 := (x.a * v.1 + x.b * v.2, x.c * v.1 + x.d * v.2)

theorem Mt.app_inv : ∀ x : Mt, x.IsU → ∀ v : V4, x.inv.app (x.app v) = v := by decide +kernel
theorem Mt.inv_app : ∀ x : Mt, x.IsU → ∀ v : V4, x.app (x.inv.app v) = v := by decide +kernel

theorem Mt.app_add (x : Mt) (v w : V4) : x.app (v + w) = x.app v + x.app w := by
  ext <;> simp [Mt.app] <;> ring

theorem Mt.inv_isU : ∀ x : Mt, x.IsU → x.inv.IsU := by decide +kernel

@[expose] def mtAut (g : Mt) (hg : g.IsU) : MulAut (Multiplicative V4) where
  toFun x := Multiplicative.ofAdd (g.app (Multiplicative.toAdd x))
  invFun x := Multiplicative.ofAdd (g.inv.app (Multiplicative.toAdd x))
  left_inv x := by
    simp only [toAdd_ofAdd]
    rw [Mt.app_inv g hg]; rfl
  right_inv x := by
    simp only [toAdd_ofAdd]
    rw [Mt.inv_app g hg]; rfl
  map_mul' x y := by
    simp only [toAdd_mul]
    rw [Mt.app_add]; rfl

theorem autMt_mtAut (g : Mt) (hg : g.IsU) : autMt (mtAut g hg) = g := by
  obtain ⟨a, b, c, d⟩ := g
  show Mt.mk _ _ _ _ = _
  simp [mtAut, Mt.app, e1, e2]

theorem M0_eq (π : Perm (Fin 4)) : M0 π = autMt (refAut π) := rfl

theorem ga_sq : ga * ga = 1 := by decide
theorem gb_pow : gb * gb * gb * gb = 1 := by decide
theorem gab_cube : (ga * gb) * (ga * gb) * (ga * gb) = 1 := by decide
theorem gword_ne : ga * (gb * gb) * ga * (gb * gb) ≠ 1 := by decide

theorem closure_ga_gb : Subgroup.closure ({ga, gb} : Set (Perm (Fin 4))) = ⊤ := by
  have h := Equiv.Perm.closure_cycle_adjacent_swap (σ := finRotate 4) (isCycle_finRotate (n := 2))
    (support_finRotate (n := 2)) 0
  have e : (swap 0 ((finRotate 4) 0) : Perm (Fin 4)) = ga := by decide
  have e' : finRotate 4 = gb := rfl
  rw [e, e', Set.pair_comm] at h
  exact h

theorem exists_conj_refAct (ρ : Perm (Fin 4) →* MulAut (Multiplicative V4))
    (hρ : Function.Injective ρ) :
    ∃ (β : MulAut (Multiplicative V4)) (π : Perm (Fin 4)),
      ∀ x, β * ρ x * β⁻¹ = refAct (π * x * π⁻¹) := by
  let ρM : Perm (Fin 4) → Mt := fun x => autMt (ρ x)
  have ρM_mul : ∀ x y, ρM (x * y) = ρM x * ρM y := fun x y => by
    show autMt (ρ (x * y)) = autMt (ρ x) * autMt (ρ y)
    rw [map_mul, autMt_mul]
  have ρM_one : ρM 1 = 1 := by
    show autMt (ρ 1) = 1
    rw [map_one, autMt_one]
  have hα : ρM ga * ρM ga = 1 := by rw [← ρM_mul, ga_sq, ρM_one]
  have hβ : ρM gb * ρM gb * ρM gb * ρM gb = 1 := by
    simp only [← ρM_mul, gb_pow, ρM_one]
  have hαβ : (ρM ga * ρM gb) * (ρM ga * ρM gb) * (ρM ga * ρM gb) = 1 := by
    simp only [← ρM_mul, gab_cube, ρM_one]
  have hnt : ρM ga * (ρM gb * ρM gb) * ρM ga * (ρM gb * ρM gb) ≠ 1 := by
    intro h
    apply gword_ne
    apply hρ
    apply autMt_injective
    show ρM _ = ρM 1
    rw [ρM_one, ← h]
    simp only [ρM_mul]
  obtain ⟨g, hg, π, h1, h2⟩ := mt_class _ (autMt_isU _) _ (autMt_isU _) hα hβ hαβ hnt
  have c1 : mtAut g hg * ρ ga = refAct (π * ga * π⁻¹) * mtAut g hg := by
    apply autMt_injective
    rw [autMt_mul, autMt_mul, autMt_mtAut]
    exact h1
  have c2 : mtAut g hg * ρ gb = refAct (π * gb * π⁻¹) * mtAut g hg := by
    apply autMt_injective
    rw [autMt_mul, autMt_mul, autMt_mtAut]
    exact h2
  refine ⟨mtAut g hg, π, ?_⟩
  let f₁ : Perm (Fin 4) →* MulAut (Multiplicative V4) :=
    (MulAut.conj (mtAut g hg)).toMonoidHom.comp ρ
  let f₂ : Perm (Fin 4) →* MulAut (Multiplicative V4) :=
    refAct.comp (MulAut.conj π).toMonoidHom
  have hf : f₁ = f₂ := by
    refine MonoidHom.eq_of_eqOn_dense closure_ga_gb ?_
    intro x hx
    rcases hx with rfl | hx
    · show mtAut g hg * ρ ga * (mtAut g hg)⁻¹ = refAct (π * ga * π⁻¹)
      rw [c1, mul_assoc, mul_inv_cancel, mul_one]
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      show mtAut g hg * ρ gb * (mtAut g hg)⁻¹ = refAct (π * gb * π⁻¹)
      rw [c2, mul_assoc, mul_inv_cancel, mul_one]
  intro x
  exact congrArg (fun f => f x) hf


theorem nonempty_mulEquiv_M128 {S : Type*} [Group S]
    (fn : Multiplicative V4 →* S) (fg : R0 →* S)
    (hfg : Function.Injective fg)
    (hcompat : ∀ (r : R0) (v : Multiplicative V4), fg r * fn v * (fg r)⁻¹ = fn (ψ r v))
    (hdisj : ∀ (v : Multiplicative V4) (r : R0), fn v = fg r → v = 1)
    (hcard : Nat.card S = 128) : Nonempty (M128 ≃* S) := by
  have : Finite S := Nat.finite_of_card_ne_zero (by omega)
  have h : ∀ r : R0, fn.comp (ψ r).toMonoidHom = (MulAut.conj (fg r)).toMonoidHom.comp fn := by
    intro r
    refine MonoidHom.ext fun v => ?_
    show fn (ψ r v) = fg r * fn v * (fg r)⁻¹
    exact (hcompat r v).symm
  let Ψ : M128 →* S := SemidirectProduct.lift fn fg h
  have hinj : Function.Injective Ψ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx' : fn x.left * fg x.right = 1 := hx
    have h1 : fn x.left = (fg x.right)⁻¹ := eq_inv_of_mul_eq_one_left hx'
    have h3 : x.left = 1 := hdisj x.left x.right⁻¹ (by rw [h1, map_inv])
    have h4 : fg x.right = 1 := by
      rw [h3, map_one] at hx'
      simpa using hx'
    have h5 : x.right = 1 := by
      apply hfg
      rw [h4, map_one]
    exact SemidirectProduct.ext h3 h5
  have hcard' : Nat.card M128 = Nat.card S := by rw [card_M128, hcard]
  exact ⟨MulEquiv.ofBijective Ψ ((Nat.bijective_iff_injective_and_card Ψ).mpr ⟨hinj, hcard'⟩)⟩


theorem card_perm_fin4 : Nat.card (Perm (Fin 4)) = 24 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm]; decide

theorem not_two_dvd_index (P : Subgroup (Perm (Fin 4))) (hP : Nat.card P = 8) : ¬ 2 ∣ P.index := by
  have h := P.card_mul_index
  rw [hP, card_perm_fin4] at h
  omega

theorem exists_conj_R0 (R : Subgroup (Perm (Fin 4))) (hR : Nat.card R = 8) :
    ∃ τ : Perm (Fin 4), ∀ x ∈ R, τ * x * τ⁻¹ ∈ R0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : ∀ P : Subgroup (Perm (Fin 4)), Nat.card P = 8 → IsPGroup 2 P := fun P hP =>
    IsPGroup.of_card (n := 3) (by rw [hP]; norm_num)
  obtain ⟨τ, hτ⟩ := MulAction.exists_smul_eq (Perm (Fin 4))
    ((h2 R hR).toSylow (not_two_dvd_index R hR))
    ((h2 R0 card_R0).toSylow (not_two_dvd_index R0 card_R0))
  refine ⟨τ, fun x hx => ?_⟩
  have h1 : ((τ • (h2 R hR).toSylow (not_two_dvd_index R hR) : Sylow 2 (Perm (Fin 4))) :
      Set (Perm (Fin 4))) = ((h2 R0 card_R0).toSylow (not_two_dvd_index R0 card_R0) : Set (Perm (Fin 4))) :=
    congrArg (fun P : Sylow 2 (Perm (Fin 4)) => (P : Set (Perm (Fin 4)))) hτ
  rw [Sylow.coe_smul] at h1
  have hx' : x ∈ (((h2 R hR).toSylow (not_two_dvd_index R hR) : Sylow 2 (Perm (Fin 4))) :
      Set (Perm (Fin 4))) := by
    exact hx
  have := Set.smul_mem_smul_set (a := MulAut.conj τ) hx'
  rw [h1] at this
  exact this

end CFSG.GH74.GLS.Stage1.Thm3.Sec8.Fin81
