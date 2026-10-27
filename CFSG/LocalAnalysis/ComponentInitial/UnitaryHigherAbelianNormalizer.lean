module

public import CFSG.LocalAnalysis.ComponentInitial.IrreducibleOperatorField
public import Mathlib.GroupTheory.SemidirectProduct

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open Module

@[expose] def ringAutUnits (R : Type*) [Semiring R] : RingAut R →* MulAut Rˣ where
  toFun σ := Units.mapEquiv σ.toMulEquiv
  map_one' := MulEquiv.ext fun _ => Units.ext rfl
  map_mul' _ _ := MulEquiv.ext fun _ => Units.ext rfl

theorem coe_ringAutUnits_apply {R : Type*} [Semiring R] (σ : RingAut R) (u : Rˣ) :
    ((ringAutUnits R σ u : Rˣ) : R) = σ u :=
  rfl

variable {p : ℕ} [Fact p.Prime] {Q : Type*} [AddCommGroup Q] [Module (ZMod p) Q]
  {T : Subgroup (LinearMap.GeneralLinearGroup (ZMod p) Q)}

theorem gl_inv_apply_apply (g : LinearMap.GeneralLinearGroup (ZMod p) Q) (q : Q) :
    (↑g⁻¹ : Module.End (ZMod p) Q) ((g : Module.End (ZMod p) Q) q) = q := by
  rw [← Module.End.mul_apply, Units.inv_mul, Module.End.one_apply]

theorem conj_mem_of_subgroupOf_normal {U : Subgroup (LinearMap.GeneralLinearGroup (ZMod p) Q)}
    (hTU : T ≤ U) (hTn : (T.subgroupOf U).Normal) : ∀ u ∈ U, ∀ t ∈ T, u * t * u⁻¹ ∈ T :=
  fun u hu t ht =>
    Subgroup.mem_subgroupOf.mp (hTn.conj_mem ⟨t, hTU ht⟩ (Subgroup.mem_subgroupOf.mpr ht) ⟨u, hu⟩)

theorem conj_mem_operatorAlgebra {g : LinearMap.GeneralLinearGroup (ZMod p) Q}
    (hg : ∀ t ∈ T, g * t * g⁻¹ ∈ T) {a : Module.End (ZMod p) Q} (ha : a ∈ operatorAlgebra T) :
    (g : Module.End (ZMod p) Q) * a * ↑g⁻¹ ∈ operatorAlgebra T := by
  induction ha using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨t, ht, rfl⟩ := hx
    rw [← Units.val_mul, ← Units.val_mul]
    exact Algebra.subset_adjoin ⟨_, hg t ht, rfl⟩
  | algebraMap r =>
    rw [← Algebra.commutes, mul_assoc, Units.mul_inv, mul_one]
    exact Subalgebra.algebraMap_mem _ r
  | add x y _ _ hx hy =>
    rw [mul_add, add_mul]
    exact add_mem hx hy
  | mul x y _ _ hx hy =>
    have he : (g : Module.End (ZMod p) Q) * (x * y) * ↑g⁻¹ =
        ((g : Module.End (ZMod p) Q) * x * ↑g⁻¹) * ((g : Module.End (ZMod p) Q) * y * ↑g⁻¹) := by
      simp only [mul_assoc, Units.inv_mul_cancel_left]
    rw [he]
    exact mul_mem hx hy

variable (T) in
@[expose] noncomputable def operatorConjAut {g : LinearMap.GeneralLinearGroup (ZMod p) Q}
    (hg : ∀ t ∈ T, g * t * g⁻¹ ∈ T) (hg' : ∀ t ∈ T, g⁻¹ * t * g⁻¹⁻¹ ∈ T) :
    RingAut (operatorAlgebra T) where
  toFun a := ⟨(g : Module.End (ZMod p) Q) * a * ↑g⁻¹, conj_mem_operatorAlgebra hg a.2⟩
  invFun a := ⟨(↑g⁻¹ : Module.End (ZMod p) Q) * a * ↑g⁻¹⁻¹, conj_mem_operatorAlgebra hg' a.2⟩
  left_inv a := Subtype.ext (by
    change (↑g⁻¹ : Module.End (ZMod p) Q) * ((g : Module.End (ZMod p) Q) * a * ↑g⁻¹) * ↑g⁻¹⁻¹ =
      a
    simp only [inv_inv, mul_assoc, Units.inv_mul_cancel_left, Units.inv_mul, mul_one])
  right_inv a := Subtype.ext (by
    change (g : Module.End (ZMod p) Q) * ((↑g⁻¹ : Module.End (ZMod p) Q) * a * ↑g⁻¹⁻¹) * ↑g⁻¹ =
      a
    simp only [inv_inv, mul_assoc, Units.mul_inv_cancel_left, Units.mul_inv, mul_one])
  map_mul' a b := Subtype.ext (by
    change (g : Module.End (ZMod p) Q) * ((a : Module.End (ZMod p) Q) * b) * ↑g⁻¹ =
      ((g : Module.End (ZMod p) Q) * a * ↑g⁻¹) * ((g : Module.End (ZMod p) Q) * b * ↑g⁻¹)
    simp only [mul_assoc, Units.inv_mul_cancel_left])
  map_add' a b := Subtype.ext (by
    change (g : Module.End (ZMod p) Q) * ((a : Module.End (ZMod p) Q) + b) * ↑g⁻¹ =
      (g : Module.End (ZMod p) Q) * a * ↑g⁻¹ + (g : Module.End (ZMod p) Q) * b * ↑g⁻¹
    rw [mul_add, add_mul])

@[expose] noncomputable def operatorConjHom
    {U : Subgroup (LinearMap.GeneralLinearGroup (ZMod p) Q)}
    (hTn : ∀ u ∈ U, ∀ t ∈ T, u * t * u⁻¹ ∈ T) : U →* RingAut (operatorAlgebra T) where
  toFun u := operatorConjAut T (hTn u u.2) (hTn _ (inv_mem u.2))
  map_one' := RingEquiv.ext fun a => Subtype.ext (by
    change (((1 : LinearMap.GeneralLinearGroup (ZMod p) Q) : Module.End (ZMod p) Q)) * a *
      ↑(1 : LinearMap.GeneralLinearGroup (ZMod p) Q)⁻¹ = a
    rw [inv_one, Units.val_one, one_mul, mul_one])
  map_mul' u v := RingEquiv.ext fun a => Subtype.ext (by
    change ((((u * v : U) : LinearMap.GeneralLinearGroup (ZMod p) Q)) : Module.End (ZMod p) Q) *
      a * ↑((u * v : U) : LinearMap.GeneralLinearGroup (ZMod p) Q)⁻¹ =
      ((u : LinearMap.GeneralLinearGroup (ZMod p) Q) : Module.End (ZMod p) Q) *
        (((v : LinearMap.GeneralLinearGroup (ZMod p) Q) : Module.End (ZMod p) Q) * a *
          ↑(v : LinearMap.GeneralLinearGroup (ZMod p) Q)⁻¹) *
        ↑(u : LinearMap.GeneralLinearGroup (ZMod p) Q)⁻¹
    simp only [Subgroup.coe_mul, mul_inv_rev, Units.val_mul, mul_assoc])

theorem coe_operatorConjHom_apply {U : Subgroup (LinearMap.GeneralLinearGroup (ZMod p) Q)}
    (hTn : ∀ u ∈ U, ∀ t ∈ T, u * t * u⁻¹ ∈ T) (u : U) (a : operatorAlgebra T) :
    ((operatorConjHom hTn u a : operatorAlgebra T) : Module.End (ZMod p) Q) =
      ((u : LinearMap.GeneralLinearGroup (ZMod p) Q) : Module.End (ZMod p) Q) * a *
        ↑(u : LinearMap.GeneralLinearGroup (ZMod p) Q)⁻¹ :=
  rfl

theorem operatorConjHom_apply_apply {U : Subgroup (LinearMap.GeneralLinearGroup (ZMod p) Q)}
    (hTn : ∀ u ∈ U, ∀ t ∈ T, u * t * u⁻¹ ∈ T) (u : U) (a : operatorAlgebra T) (q : Q) :
    ((u : LinearMap.GeneralLinearGroup (ZMod p) Q) : Module.End (ZMod p) Q)
        ((a : Module.End (ZMod p) Q) q) =
      ((operatorConjHom hTn u a : operatorAlgebra T) : Module.End (ZMod p) Q)
        (((u : LinearMap.GeneralLinearGroup (ZMod p) Q) : Module.End (ZMod p) Q) q) := by
  rw [coe_operatorConjHom_apply, Module.End.mul_apply, Module.End.mul_apply, gl_inv_apply_apply]

theorem operatorConjHom_eq_one_iff {U : Subgroup (LinearMap.GeneralLinearGroup (ZMod p) Q)}
    (hTn : ∀ u ∈ U, ∀ t ∈ T, u * t * u⁻¹ ∈ T) (hcomm : ∀ g ∈ T, ∀ h ∈ T, g * h = h * g)
    {s : Q} (hev : Function.Bijective fun a : operatorAlgebra T => (a : Module.End (ZMod p) Q) s)
    (u : U) : operatorConjHom hTn u = 1 ↔
      ((u : LinearMap.GeneralLinearGroup (ZMod p) Q) : Module.End (ZMod p) Q) ∈
        operatorAlgebra T := by
  constructor
  · intro h1
    have hc : ∀ a : operatorAlgebra T,
        ((u : LinearMap.GeneralLinearGroup (ZMod p) Q) : Module.End (ZMod p) Q) * a =
          a * (u : LinearMap.GeneralLinearGroup (ZMod p) Q) := fun a => by
      have h2 := congrArg (fun σ : RingAut (operatorAlgebra T) =>
        ((σ a : operatorAlgebra T) : Module.End (ZMod p) Q)) h1
      change ((u : LinearMap.GeneralLinearGroup (ZMod p) Q) : Module.End (ZMod p) Q) * a *
        ↑(u : LinearMap.GeneralLinearGroup (ZMod p) Q)⁻¹ = a at h2
      calc ((u : LinearMap.GeneralLinearGroup (ZMod p) Q) : Module.End (ZMod p) Q) * a =
            ((u : LinearMap.GeneralLinearGroup (ZMod p) Q) : Module.End (ZMod p) Q) * a *
              ↑(u : LinearMap.GeneralLinearGroup (ZMod p) Q)⁻¹ *
              (u : LinearMap.GeneralLinearGroup (ZMod p) Q) := by
            rw [mul_assoc _ (↑(u : LinearMap.GeneralLinearGroup (ZMod p) Q)⁻¹ :
              Module.End (ZMod p) Q), Units.inv_mul, mul_one]
        _ = a * (u : LinearMap.GeneralLinearGroup (ZMod p) Q) := by rw [h2]
    obtain ⟨b, hb⟩ := hev.2 (((u : LinearMap.GeneralLinearGroup (ZMod p) Q) :
      Module.End (ZMod p) Q) s)
    have hub : ((u : LinearMap.GeneralLinearGroup (ZMod p) Q) : Module.End (ZMod p) Q) =
        (b : Module.End (ZMod p) Q) := by
      refine LinearMap.ext fun q => ?_
      obtain ⟨a, rfl⟩ := hev.2 q
      change ((u : LinearMap.GeneralLinearGroup (ZMod p) Q) : Module.End (ZMod p) Q)
          ((a : Module.End (ZMod p) Q) s) = (b : Module.End (ZMod p) Q)
          ((a : Module.End (ZMod p) Q) s)
      change (b : Module.End (ZMod p) Q) s =
        ((u : LinearMap.GeneralLinearGroup (ZMod p) Q) : Module.End (ZMod p) Q) s at hb
      rw [← Module.End.mul_apply, hc a, Module.End.mul_apply, ← hb, ← Module.End.mul_apply,
        ← Module.End.mul_apply, mul_comm_of_mem_operatorAlgebra hcomm a.2 b.2]
    rw [hub]
    exact b.2
  · intro hu
    refine RingEquiv.ext fun a => Subtype.ext ?_
    change ((u : LinearMap.GeneralLinearGroup (ZMod p) Q) : Module.End (ZMod p) Q) * a *
      ↑(u : LinearMap.GeneralLinearGroup (ZMod p) Q)⁻¹ = a
    rw [mul_comm_of_mem_operatorAlgebra hcomm hu a.2, mul_assoc, Units.mul_inv, mul_one]

theorem eq_of_operatorConjHom_eq {U : Subgroup (LinearMap.GeneralLinearGroup (ZMod p) Q)}
    (hTn : ∀ u ∈ U, ∀ t ∈ T, u * t * u⁻¹ ∈ T) (hcomm : ∀ g ∈ T, ∀ h ∈ T, g * h = h * g)
    {s : Q} (hev : Function.Bijective fun a : operatorAlgebra T => (a : Module.End (ZMod p) Q) s)
    {u v : U} (hσ : operatorConjHom hTn u = operatorConjHom hTn v)
    (huv : ((u : LinearMap.GeneralLinearGroup (ZMod p) Q) : Module.End (ZMod p) Q) s =
      ((v : LinearMap.GeneralLinearGroup (ZMod p) Q) : Module.End (ZMod p) Q) s) : u = v := by
  have h1 : operatorConjHom hTn (u⁻¹ * v) = 1 := by
    rw [map_mul, map_inv, hσ, inv_mul_cancel]
  have hw := (operatorConjHom_eq_one_iff hTn hcomm hev _).mp h1
  have hws : (((u⁻¹ * v : U) : LinearMap.GeneralLinearGroup (ZMod p) Q) :
      Module.End (ZMod p) Q) s = s := by
    change (↑(u : LinearMap.GeneralLinearGroup (ZMod p) Q)⁻¹ : Module.End (ZMod p) Q)
      (((v : LinearMap.GeneralLinearGroup (ZMod p) Q) : Module.End (ZMod p) Q) s) = s
    rw [← huv, gl_inv_apply_apply]
  have h2 : (⟨_, hw⟩ : operatorAlgebra T) = 1 := hev.1 hws
  have h3 : ((u⁻¹ * v : U) : LinearMap.GeneralLinearGroup (ZMod p) Q) = 1 :=
    Units.ext (congrArg Subtype.val h2)
  exact inv_mul_eq_one.mp (Subtype.ext h3)

theorem abelian_irreducible_normalizer_semilinear [FiniteDimensional (ZMod p) Q] {n : ℕ}
    (hn : 1 ≤ n) (hdim : finrank (ZMod p) Q = n)
    {U : Subgroup (LinearMap.GeneralLinearGroup (ZMod p) Q)} (hTU : T ≤ U)
    (hTn : (T.subgroupOf U).Normal) (hcomm : ∀ g ∈ T, ∀ h ∈ T, g * h = h * g)
    (hirr : ∀ W : Submodule (ZMod p) Q,
      (∀ g ∈ T, ∀ w ∈ W, (g : Module.End (ZMod p) Q) w ∈ W) → W = ⊥ ∨ W = ⊤) :
    IsField (operatorAlgebra T) ∧ Nat.card (operatorAlgebra T) = p ^ n ∧
    (∀ s : Q, s ≠ 0 →
      Function.Bijective fun a : operatorAlgebra T => (a : Module.End (ZMod p) Q) s) ∧
    (∀ (u : U) (a : operatorAlgebra T),
      ((operatorConjHom (conj_mem_of_subgroupOf_normal hTU hTn) u a : operatorAlgebra T) :
        Module.End (ZMod p) Q) =
        ((u : LinearMap.GeneralLinearGroup (ZMod p) Q) : Module.End (ZMod p) Q) * a *
          ↑(u : LinearMap.GeneralLinearGroup (ZMod p) Q)⁻¹) ∧
    (∀ (u : U) (a : operatorAlgebra T) (q : Q),
      ((u : LinearMap.GeneralLinearGroup (ZMod p) Q) : Module.End (ZMod p) Q)
          ((a : Module.End (ZMod p) Q) q) =
        ((operatorConjHom (conj_mem_of_subgroupOf_normal hTU hTn) u a : operatorAlgebra T) :
          Module.End (ZMod p) Q)
          (((u : LinearMap.GeneralLinearGroup (ZMod p) Q) : Module.End (ZMod p) Q) q)) ∧
    (∀ u : U, operatorConjHom (conj_mem_of_subgroupOf_normal hTU hTn) u = 1 ↔
      ((u : LinearMap.GeneralLinearGroup (ZMod p) Q) : Module.End (ZMod p) Q) ∈
        operatorAlgebra T) ∧
    (∀ s : Q, s ≠ 0 → ∀ u v : U,
      ((u : LinearMap.GeneralLinearGroup (ZMod p) Q) : Module.End (ZMod p) Q) s = s →
      ((v : LinearMap.GeneralLinearGroup (ZMod p) Q) : Module.End (ZMod p) Q) s = s →
      operatorConjHom (conj_mem_of_subgroupOf_normal hTU hTn) u =
        operatorConjHom (conj_mem_of_subgroupOf_normal hTU hTn) v → u = v) ∧
    (∀ s : Q, s ≠ 0 → ∃ ι : U →* (operatorAlgebra T)ˣ ⋊[ringAutUnits (operatorAlgebra T)]
        RingAut (operatorAlgebra T), Function.Injective ι ∧ ∀ u : U,
        (ι u).right = operatorConjHom (conj_mem_of_subgroupOf_normal hTU hTn) u ∧
        ((((ι u).left : (operatorAlgebra T)ˣ) : operatorAlgebra T) : Module.End (ZMod p) Q) s =
          ((u : LinearMap.GeneralLinearGroup (ZMod p) Q) : Module.End (ZMod p) Q) s) := by
  obtain ⟨hF, hcard, -, hev'⟩ := irreducible_abelian_operator_algebra_field hn hdim hcomm hirr
  have hev : ∀ s : Q, s ≠ 0 →
      Function.Bijective fun a : operatorAlgebra T => (a : Module.End (ZMod p) Q) s := by
    intro s hs
    obtain ⟨e, he⟩ := hev' s hs
    have hfe : (fun a : operatorAlgebra T => (a : Module.End (ZMod p) Q) s) = e :=
      funext fun a => (he a).symm
    rw [hfe]
    exact e.bijective
  have hTn' := conj_mem_of_subgroupOf_normal hTU hTn
  have : Nontrivial Q := Module.nontrivial_of_finrank_pos (R := ZMod p) (by omega)
  obtain ⟨s₀, hs₀⟩ := exists_ne (0 : Q)
  have hcF : ∀ a b : operatorAlgebra T, a * b = b * a := fun a b =>
    Subtype.ext (mul_comm_of_mem_operatorAlgebra hcomm a.2 b.2)
  refine ⟨hF, hcard, hev, fun u a => rfl, operatorConjHom_apply_apply hTn',
    operatorConjHom_eq_one_iff hTn' hcomm (hev s₀ hs₀),
    fun s hs u v hu hv hσ => eq_of_operatorConjHom_eq hTn' hcomm (hev s hs) hσ (hu.trans hv.symm),
    fun s hs => ?_⟩
  obtain ⟨ev, hevdef⟩ : ∃ ev : operatorAlgebra T ≃ Q,
      ev = Equiv.ofBijective _ (hev s hs) := ⟨_, rfl⟩
  have hev_apply : ∀ a : operatorAlgebra T, ev a = (a : Module.End (ZMod p) Q) s := fun a => by
    rw [hevdef, Equiv.ofBijective_apply]
  have hus : ∀ u : U,
      ((u : LinearMap.GeneralLinearGroup (ZMod p) Q) : Module.End (ZMod p) Q) s ≠ 0 :=
    fun u h0 => hs (by
      have h1 := gl_inv_apply_apply (u : LinearMap.GeneralLinearGroup (ZMod p) Q) s
      rw [h0, map_zero] at h1
      exact h1.symm)
  have ha0 : ∀ u : U, ev.symm
      (((u : LinearMap.GeneralLinearGroup (ZMod p) Q) : Module.End (ZMod p) Q) s) ≠ 0 :=
    fun u h0 => hus u (by
      have h1 := ev.apply_symm_apply
        (((u : LinearMap.GeneralLinearGroup (ZMod p) Q) : Module.End (ZMod p) Q) s)
      rw [h0, hev_apply] at h1
      rw [← h1]
      rfl)
  choose binv hbinv using fun u : U => hF.mul_inv_cancel (ha0 u)
  obtain ⟨A, hAdef⟩ : ∃ A : U → (operatorAlgebra T)ˣ, A = fun u =>
      ⟨ev.symm (((u : LinearMap.GeneralLinearGroup (ZMod p) Q) : Module.End (ZMod p) Q) s),
        binv u, hbinv u, (hcF _ _).trans (hbinv u)⟩ := ⟨_, rfl⟩
  have hA : ∀ u : U, ev ((A u : (operatorAlgebra T)ˣ) : operatorAlgebra T) =
      ((u : LinearMap.GeneralLinearGroup (ZMod p) Q) : Module.End (ZMod p) Q) s := fun u => by
    rw [hAdef]
    exact ev.apply_symm_apply _
  have hA' : ∀ u : U,
      ((((A u : (operatorAlgebra T)ˣ) : operatorAlgebra T)) : Module.End (ZMod p) Q) s =
        ((u : LinearMap.GeneralLinearGroup (ZMod p) Q) : Module.End (ZMod p) Q) s := fun u => by
    rw [← hev_apply, hA]
  have hAmul : ∀ u v : U, ((A (u * v) : (operatorAlgebra T)ˣ) : operatorAlgebra T) =
      (A u : operatorAlgebra T) * operatorConjHom hTn' u (A v : operatorAlgebra T) := by
    intro u v
    apply ev.injective
    rw [hA, hev_apply, hcF]
    change _ = ((operatorConjHom hTn' u (A v : operatorAlgebra T) : operatorAlgebra T) :
      Module.End (ZMod p) Q)
        ((((A u : (operatorAlgebra T)ˣ) : operatorAlgebra T) : Module.End (ZMod p) Q) s)
    rw [hA', ← operatorConjHom_apply_apply, hA']
    rfl
  refine ⟨{ toFun := fun u => ⟨A u, operatorConjHom hTn' u⟩
            map_one' := ?_
            map_mul' := ?_ }, ?_, fun u => ⟨rfl, hA' u⟩⟩
  · refine SemidirectProduct.ext (Units.ext (ev.injective ?_)) (map_one _)
    change ev ((A 1 : (operatorAlgebra T)ˣ) : operatorAlgebra T) = ev 1
    rw [hA, hev_apply]
    rfl
  · intro u v
    refine SemidirectProduct.ext (Units.ext ?_) (map_mul _ u v)
    change ((A (u * v) : (operatorAlgebra T)ˣ) : operatorAlgebra T) =
      (A u : operatorAlgebra T) * operatorConjHom hTn' u (A v : operatorAlgebra T)
    exact hAmul u v
  · intro u v huv
    have h1 := congrArg SemidirectProduct.right huv
    have h2 := congrArg (fun x : (operatorAlgebra T)ˣ ⋊[ringAutUnits (operatorAlgebra T)]
      RingAut (operatorAlgebra T) => ev ((x.left : (operatorAlgebra T)ˣ) : operatorAlgebra T)) huv
    change operatorConjHom hTn' u = operatorConjHom hTn' v at h1
    change ev ((A u : (operatorAlgebra T)ˣ) : operatorAlgebra T) =
      ev ((A v : (operatorAlgebra T)ˣ) : operatorAlgebra T) at h2
    rw [hA, hA] at h2
    exact eq_of_operatorConjHom_eq hTn' hcomm (hev s hs) h1 h2

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
