module

public import CFSG.CGT.PushingUpLit.CGT6.EmbModule.M2One
public import CFSG.CGT.PushingUpLit.CGT6.EmbModule.DualNat

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.CGT.PushingUpLit.CGT6.EmbModule

variable {n : ℕ} {V : Type} [CommGroup V] {G : Subgroup (MulAut V)} (S : NatSec n G)
  (ρ : Representation (ZMod 2) ↥G (Fin 2 → GaloisField 2 n))
  (hρ : ∀ (g : ↥G) (w : Fin 2 → GaloisField 2 n),
    ρ g w = (S.θ g : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec w)
  (s : Multiplicative (Fin 2 → GaloisField 2 n) →* ↥(commV G))
  (hs : ∀ x, S.β (s x) = x)

omit S hρ s hs in
theorem rho_apply_inv (g : ↥G) (w : Fin 2 → GaloisField 2 n) : ρ g (ρ g⁻¹ w) = w := by
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

omit S hρ s hs in
theorem rho_inv_apply (g : ↥G) (w : Fin 2 → GaloisField 2 n) : ρ g⁻¹ (ρ g w) = w := by
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

omit hρ hs in
@[expose] noncomputable def kappaU (g : ↥G) (x : Multiplicative (Fin 2 → GaloisField 2 n)) :
    ↥(commV G) :=
  ⟨(g : MulAut V) (s (Multiplicative.ofAdd (ρ g⁻¹ (Multiplicative.toAdd x))) : V),
    commV_apply_mem g.2 (s _).2⟩ * (s x)⁻¹

include hρ hs in
theorem kappaU_beta (g : ↥G) (x : Multiplicative (Fin 2 → GaloisField 2 n)) :
    S.β (kappaU ρ s g x) = 1 := by
  set m : Multiplicative (Fin 2 → GaloisField 2 n) :=
    Multiplicative.ofAdd (ρ g⁻¹ (Multiplicative.toAdd x)) with hm
  have hp := commV_apply_mem g.2 (s m).2
  have e := S.equiv g (s m) hp
  rw [hs] at e
  have hm' : ρ g (Multiplicative.toAdd m) = Multiplicative.toAdd x := by
    rw [hm, toAdd_ofAdd]
    exact rho_apply_inv ρ g _
  have e' : S.β ⟨(g : MulAut V) (s m : V), hp⟩ = x := by
    rw [e, ← hρ, hm']
    rfl
  show S.β (⟨(g : MulAut V) (s m : V), commV_apply_mem g.2 (s m).2⟩ * (s x)⁻¹) = 1
  rw [map_mul, map_inv, hs, e', mul_inv_cancel]

omit hρ hs in
theorem kappaU_one (g : ↥G) : kappaU ρ s g 1 = 1 := by
  apply Subtype.ext
  simp [kappaU]

omit hρ hs in
theorem kappaU_mul (g : ↥G) (x y : Multiplicative (Fin 2 → GaloisField 2 n)) :
    kappaU ρ s g (x * y) = kappaU ρ s g x * kappaU ρ s g y := by
  apply Subtype.ext
  simp only [kappaU, Subgroup.coe_mul, Subgroup.coe_inv, toAdd_mul, map_add, ofAdd_add, map_mul,
    mul_inv]
  exact mul_mul_mul_comm _ _ _ _

omit hρ hs in
theorem kappaU_mul_left (g h : ↥G) (x : Multiplicative (Fin 2 → GaloisField 2 n)) :
    kappaU ρ s (g * h) x =
      ⟨(g : MulAut V) (kappaU ρ s h (Multiplicative.ofAdd (ρ g⁻¹ (Multiplicative.toAdd x))) : V),
        commV_apply_mem g.2 (kappaU ρ s h _).2⟩ * kappaU ρ s g x := by
  apply Subtype.ext
  simp only [kappaU, Subgroup.coe_mul, Subgroup.coe_inv, toAdd_ofAdd, mul_inv_rev, map_mul,
    map_inv, MulAut.mul_apply, Module.End.mul_apply]
  rw [mul_assoc, inv_mul_cancel_left]

include hρ hs in
theorem kappaU_mem (g : ↥G) (x : Multiplicative (Fin 2 → GaloisField 2 n)) :
    ((kappaU ρ s g x : ↥(commV G)) : V) ∈ commV G ⊓ fixV G := by
  have h : kappaU ρ s g x ∈ S.β.ker := kappaU_beta S ρ hρ s hs g x
  rw [S.ker, Subgroup.mem_subgroupOf] at h
  exact h

@[expose] noncomputable def kappaC (g : ↥G) (x : Multiplicative (Fin 2 → GaloisField 2 n)) :
    ↥(commV G ⊓ fixV G) :=
  ⟨(kappaU ρ s g x : V), kappaU_mem S ρ hρ s hs g x⟩

theorem kappaC_one (g : ↥G) : kappaC S ρ hρ s hs g 1 = 1 :=
  Subtype.ext (congrArg (fun u : ↥(commV G) => (u : V)) (kappaU_one ρ s g))

theorem kappaC_mul (g : ↥G) (x y : Multiplicative (Fin 2 → GaloisField 2 n)) :
    kappaC S ρ hρ s hs g (x * y) = kappaC S ρ hρ s hs g x * kappaC S ρ hρ s hs g y :=
  Subtype.ext (congrArg (fun u : ↥(commV G) => (u : V)) (kappaU_mul ρ s g x y))

theorem kappaC_mul_left (g h : ↥G) (x : Multiplicative (Fin 2 → GaloisField 2 n)) :
    kappaC S ρ hρ s hs (g * h) x =
      kappaC S ρ hρ s hs h (Multiplicative.ofAdd (ρ g⁻¹ (Multiplicative.toAdd x))) *
        kappaC S ρ hρ s hs g x := by
  apply Subtype.ext
  have hfix : (g : MulAut V) (kappaU ρ s h
      (Multiplicative.ofAdd (ρ g⁻¹ (Multiplicative.toAdd x))) : V) =
      (kappaU ρ s h (Multiplicative.ofAdd (ρ g⁻¹ (Multiplicative.toAdd x))) : V) :=
    mem_fixV.1 (kappaU_mem S ρ hρ s hs h _).2 g g.2
  have h1 := congrArg (fun u : ↥(commV G) => (u : V)) (kappaU_mul_left ρ s g h x)
  change (kappaU ρ s (g * h) x : V) = _
  rw [h1]
  change (g : MulAut V) (kappaU ρ s h
      (Multiplicative.ofAdd (ρ g⁻¹ (Multiplicative.toAdd x))) : V) * _ = _
  rw [hfix]
  rfl

section Dual

@[expose] noncomputable def cfun (f : Additive ↥(commV G ⊓ fixV G) →+ ZMod 2)
    (g : ↥G) : Module.Dual (ZMod 2) (Fin 2 → GaloisField 2 n) :=
  zmod2Dual
    (AddMonoidHom.mk' (fun w => f (Additive.ofMul (kappaC S ρ hρ s hs g (Multiplicative.ofAdd w))))
      fun a b => by
        simp only [ofAdd_add, kappaC_mul S ρ hρ s hs g, ofMul_mul, map_add])

theorem cfun_apply (f : Additive ↥(commV G ⊓ fixV G) →+ ZMod 2) (g : ↥G)
    (w : Fin 2 → GaloisField 2 n) :
    cfun S ρ hρ s hs f g w = f (Additive.ofMul (kappaC S ρ hρ s hs g (Multiplicative.ofAdd w))) :=
  rfl

theorem cfun_cocycle (f : Additive ↥(commV G ⊓ fixV G) →+ ZMod 2) :
    ∀ g h : ↥G, cfun S ρ hρ s hs f (g * h) =
      cfun S ρ hρ s hs f g + (ρ.dual g) (cfun S ρ hρ s hs f h) := by
  intro g h
  apply LinearMap.ext
  intro w
  rw [Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.add_apply, cfun_apply,
    cfun_apply, LinearMap.comp_apply, cfun_apply, kappaC_mul_left S ρ hρ s hs g h, ofMul_mul,
    map_add, add_comm]
  rfl

end Dual

section Inj

omit hρ in
@[expose] noncomputable def ccHom : ↥(commV G) →* ↥(commV G ⊓ fixV G) where
  toFun u := ⟨(u : V) * ((s (S.β u) : ↥(commV G)) : V)⁻¹, by
    have h : u * (s (S.β u))⁻¹ ∈ S.β.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hs, mul_inv_cancel]
    rw [S.ker, Subgroup.mem_subgroupOf] at h
    exact h⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' u u' := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, map_mul, mul_inv]
    exact mul_mul_mul_comm _ _ _ _

omit hρ in
theorem ccHom_val (u : ↥(commV G)) :
    ((ccHom S s hs u : ↥(commV G ⊓ fixV G)) : V) = (u : V) * ((s (S.β u) : ↥(commV G)) : V)⁻¹ :=
  rfl

include hρ hs in
theorem ccHom_apply_g (g : ↥G) (u : ↥(commV G)) :
    ccHom S s hs ⟨(g : MulAut V) (u : V), commV_apply_mem g.2 u.2⟩ =
      ccHom S s hs u * kappaC S ρ hρ s hs g
        (Multiplicative.ofAdd (ρ g (Multiplicative.toAdd (S.β u)))) := by
  have hp := commV_apply_mem g.2 u.2
  have e : S.β ⟨(g : MulAut V) (u : V), hp⟩ =
      Multiplicative.ofAdd (ρ g (Multiplicative.toAdd (S.β u))) := by
    rw [S.equiv g u hp, hρ]
  have hfix : (g : MulAut V) ((ccHom S s hs u : ↥(commV G ⊓ fixV G)) : V) =
      ((ccHom S s hs u : ↥(commV G ⊓ fixV G)) : V) :=
    mem_fixV.1 (ccHom S s hs u).2.2 g g.2
  rw [ccHom_val, map_mul, map_inv] at hfix
  apply Subtype.ext
  change ((ccHom S s hs ⟨(g : MulAut V) (u : V), hp⟩ : ↥(commV G ⊓ fixV G)) : V) =
    ((ccHom S s hs u : ↥(commV G ⊓ fixV G)) : V) * (kappaU ρ s g _ : V)
  rw [ccHom_val, ccHom_val]
  change (g : MulAut V) (u : V) * ((s (S.β ⟨(g : MulAut V) (u : V), hp⟩) : ↥(commV G)) : V)⁻¹ =
    ((u : V) * ((s (S.β u) : ↥(commV G)) : V)⁻¹) *
      ((g : MulAut V) ((s (Multiplicative.ofAdd (ρ g⁻¹ (Multiplicative.toAdd
        (Multiplicative.ofAdd (ρ g (Multiplicative.toAdd (S.β u)))))))) : V) *
        ((s (Multiplicative.ofAdd (ρ g (Multiplicative.toAdd (S.β u)))) : ↥(commV G)) : V)⁻¹)
  rw [e, toAdd_ofAdd, rho_inv_apply ρ g, ofAdd_toAdd, ← hfix]
  group

@[expose] noncomputable def thetaA (f : Additive ↥(commV G ⊓ fixV G) →+ ZMod 2)
    (φ : Module.Dual (ZMod 2) (Fin 2 → GaloisField 2 n)) (u : ↥(commV G)) : ZMod 2 :=
  f (Additive.ofMul (ccHom S s hs u)) + φ (Multiplicative.toAdd (S.β u))

omit hρ in
theorem thetaA_mul (f : Additive ↥(commV G ⊓ fixV G) →+ ZMod 2)
    (φ : Module.Dual (ZMod 2) (Fin 2 → GaloisField 2 n)) (u u' : ↥(commV G)) :
    thetaA S s hs f φ (u * u') = thetaA S s hs f φ u + thetaA S s hs f φ u' := by
  simp only [thetaA, map_mul, ofMul_mul, toAdd_mul, map_add]
  abel

omit hρ in
theorem thetaA_one (f : Additive ↥(commV G ⊓ fixV G) →+ ZMod 2)
    (φ : Module.Dual (ZMod 2) (Fin 2 → GaloisField 2 n)) : thetaA S s hs f φ 1 = 0 := by
  simp [thetaA]

include hρ hs in
theorem thetaA_g (f : Additive ↥(commV G ⊓ fixV G) →+ ZMod 2)
    (φ : Module.Dual (ZMod 2) (Fin 2 → GaloisField 2 n))
    (hφ : ∀ (g : ↥G) (w : Fin 2 → GaloisField 2 n),
      cfun S ρ hρ s hs f g w = φ (ρ g⁻¹ w) - φ w)
    (g : ↥G) (u : ↥(commV G)) :
    thetaA S s hs f φ ⟨(g : MulAut V) (u : V), commV_apply_mem g.2 u.2⟩ =
      thetaA S s hs f φ u := by
  have hp := commV_apply_mem g.2 u.2
  have e : S.β ⟨(g : MulAut V) (u : V), hp⟩ =
      Multiplicative.ofAdd (ρ g (Multiplicative.toAdd (S.β u))) := by
    rw [S.equiv g u hp, hρ]
  have h1 := hφ g (ρ g (Multiplicative.toAdd (S.β u)))
  rw [cfun_apply, rho_inv_apply ρ g] at h1
  unfold thetaA
  rw [ccHom_apply_g S ρ hρ s hs g u, e, toAdd_ofAdd, ofMul_mul, map_add, h1]
  abel

include hρ hs in
theorem thetaA_eq_zero (hn : 2 ≤ n) (f : Additive ↥(commV G ⊓ fixV G) →+ ZMod 2)
    (φ : Module.Dual (ZMod 2) (Fin 2 → GaloisField 2 n))
    (hφ : ∀ (g : ↥G) (w : Fin 2 → GaloisField 2 n),
      cfun S ρ hρ s hs f g w = φ (ρ g⁻¹ w) - φ w) (u : ↥(commV G)) :
    thetaA S s hs f φ u = 0 := by
  have := S.isPerfect hn
  have hgen : ∀ (g : ↥G) (v : V), thetaA S s hs f φ (commEl g v) = 0 := by
    intro g v
    let η : ↥G →* Multiplicative (ZMod 2) :=
      { toFun := fun g => Multiplicative.ofAdd (thetaA S s hs f φ (commEl g v))
        map_one' := by
          have : commEl (1 : ↥G) v = 1 := Subtype.ext (by simp [commEl_val])
          simp [this, thetaA_one]
        map_mul' := fun g h => by
          rw [commEl_mul_left, thetaA_mul, thetaA_g S ρ hρ s hs f φ hφ g (commEl h v),
            add_comm, ofAdd_add] }
    exact Multiplicative.ofAdd.injective (eq_one_of_perfect η g)
  obtain ⟨u, hu⟩ := u
  induction hu using Subgroup.closure_induction with
  | mem w hw =>
    obtain ⟨y, hy, v, rfl⟩ := hw
    exact hgen ⟨y, hy⟩ v
  | one => exact thetaA_one S s hs f φ
  | mul x y hx hy ihx ihy =>
    have h1 : (⟨x * y, Subgroup.mul_mem _ hx hy⟩ : ↥(commV G)) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
    rw [h1, thetaA_mul, ihx, ihy, add_zero]
  | inv x hx ih =>
    have h1 : (⟨x⁻¹, Subgroup.inv_mem _ hx⟩ : ↥(commV G)) * ⟨x, hx⟩ = 1 :=
      Subtype.ext (inv_mul_cancel x)
    have h2 := thetaA_mul S s hs f φ ⟨x⁻¹, Subgroup.inv_mem _ hx⟩ ⟨x, hx⟩
    rw [h1, thetaA_one, ih, add_zero] at h2
    exact h2.symm

include hρ hs in
theorem NatSec.dual_inj (hn : 2 ≤ n) (f : Additive ↥(commV G ⊓ fixV G) →+ ZMod 2)
    (φ : Module.Dual (ZMod 2) (Fin 2 → GaloisField 2 n))
    (hφ' : ∀ (g : ↥G) (w : Fin 2 → GaloisField 2 n),
      cfun S ρ hρ s hs f g w = φ (ρ g⁻¹ w) - φ w) : f = 0 := by
  apply AddMonoidHom.ext
  intro x
  obtain ⟨c, hcx⟩ : ∃ c : ↥(commV G ⊓ fixV G), x = Additive.ofMul c := ⟨Additive.toMul x, rfl⟩
  rw [hcx]
  have hc : (c : V) ∈ commV G := c.2.1
  have hβc : S.β ⟨c, hc⟩ = 1 := by
    have : (⟨c, hc⟩ : ↥(commV G)) ∈ S.β.ker := by
      rw [S.ker, Subgroup.mem_subgroupOf]
      exact c.2
    exact this
  have h0 := thetaA_eq_zero S ρ hρ s hs hn f φ hφ' ⟨c, hc⟩
  have hcc : ccHom S s hs ⟨c, hc⟩ = c := by
    apply Subtype.ext
    rw [ccHom_val, hβc, map_one]
    simp
  unfold thetaA at h0
  rw [hcc, hβc, toAdd_one, map_zero, add_zero] at h0
  simpa using h0

section Claim2

omit s hs in
theorem cfun_zero (s : Multiplicative (Fin 2 → GaloisField 2 n) →* ↥(commV G))
    (hs : ∀ x, S.β (s x) = x) (g : ↥G) : cfun S ρ hρ s hs 0 g = 0 :=
  LinearMap.ext fun _ => rfl

theorem cfun_add (f f' : Additive ↥(commV G ⊓ fixV G) →+ ZMod 2) (g : ↥G) :
    cfun S ρ hρ s hs (f + f') g = cfun S ρ hρ s hs f g + cfun S ρ hρ s hs f' g :=
  LinearMap.ext fun _ => rfl

variable (Φ : (Fin 2 → GaloisField 2 n) ≃+ Module.Dual (ZMod 2) (Fin 2 → GaloisField 2 n))
  (hΦ : ∀ (g : ↥G) (w : Fin 2 → GaloisField 2 n), Φ (ρ g w) = ρ.dual g (Φ w))

include hΦ in
theorem Phi_symm_dual (g : ↥G) (ψ : Module.Dual (ZMod 2) (Fin 2 → GaloisField 2 n)) :
    Φ.symm (ρ.dual g ψ) = ρ g (Φ.symm ψ) := by
  have := hΦ g (Φ.symm ψ)
  rw [AddEquiv.apply_symm_apply] at this
  rw [← this, AddEquiv.symm_apply_apply]

include hρ hΦ in
theorem cW_mem_Z1 (f : Additive ↥(commV G ⊓ fixV G) →+ ZMod 2) :
    (fun g => Φ.symm (cfun S ρ hρ s hs f g)) ∈ Z1 ρ := by
  intro g h
  change Φ.symm (cfun S ρ hρ s hs f (g * h)) = Φ.symm (cfun S ρ hρ s hs f g) +
    ρ g (Φ.symm (cfun S ρ hρ s hs f h))
  rw [cfun_cocycle S ρ hρ s hs f g h, map_add, Phi_symm_dual ρ Φ hΦ]

include hρ hs hΦ in
theorem NatSec.cW_inj (hn : 2 ≤ n) (g : Additive ↥(commV G ⊓ fixV G) →+ ZMod 2)
    (hg : (fun x => Φ.symm (cfun S ρ hρ s hs g x)) ∈ B1 ρ) : g = 0 := by
  obtain ⟨z, hz⟩ := hg
  refine S.dual_inj ρ hρ s hs hn g (Φ z) fun x w => ?_
  have h2 : ρ x z - z = Φ.symm (cfun S ρ hρ s hs g x) := congrFun hz x
  have h3 : ρ x z = Φ.symm (cfun S ρ hρ s hs g x) + z := by rw [← h2]; abel
  have h4 : ρ.dual x (Φ z) = cfun S ρ hρ s hs g x + Φ z := by
    rw [← hΦ, h3, map_add, AddEquiv.apply_symm_apply]
  have h5 := congrArg (fun k : Module.Dual (ZMod 2) (Fin 2 → GaloisField 2 n) => k w) h4
  simp only [Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply,
    LinearMap.add_apply] at h5
  exact eq_sub_of_add_eq h5.symm

include hρ hs hΦ in
theorem NatSec.claim2 [Finite V] (hn : 2 ≤ n) (hV : ∀ v : V, v ^ 2 = 1)
    (hH : Nat.card (H1 ρ) ≤ 2 ^ n) : Nat.card ↥(commV G ⊓ fixV G) ≤ 2 ^ n := by
  have hG : Finite ↥G := Finite.of_equiv _ S.θ.toEquiv.symm
  have hZ : Finite ↥(Z1 ρ) := Subtype.finite
  have hHf : Finite (H1 ρ) := Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)
  let Ψ : (Additive ↥(commV G ⊓ fixV G) →+ ZMod 2) →+ H1 ρ :=
    { toFun := fun f => (Submodule.Quotient.mk
        (⟨fun g => Φ.symm (cfun S ρ hρ s hs f g), cW_mem_Z1 S ρ hρ s hs Φ hΦ f⟩ : Z1 ρ) : H1 ρ)
      map_zero' := by
        have : (⟨fun g => Φ.symm (cfun S ρ hρ s hs 0 g), cW_mem_Z1 S ρ hρ s hs Φ hΦ 0⟩ : Z1 ρ) =
            0 := Subtype.ext (funext fun g => by simp [cfun_zero])
        simp only [this]
        exact Submodule.Quotient.mk_zero _
      map_add' := fun f f' => by
        have : (⟨fun g => Φ.symm (cfun S ρ hρ s hs (f + f') g),
            cW_mem_Z1 S ρ hρ s hs Φ hΦ (f + f')⟩ : Z1 ρ) =
            ⟨fun g => Φ.symm (cfun S ρ hρ s hs f g), cW_mem_Z1 S ρ hρ s hs Φ hΦ f⟩ +
              ⟨fun g => Φ.symm (cfun S ρ hρ s hs f' g), cW_mem_Z1 S ρ hρ s hs Φ hΦ f'⟩ :=
          Subtype.ext (funext fun g => by simp [cfun_add])
        simp only [this]
        exact Submodule.Quotient.mk_add _ }
  have hdbl : ∀ x : H1 ρ, x + x = 0 := fun x => by
    rw [← two_smul (ZMod 2) x]
    have h2 : (2 : ZMod 2) = 0 := by decide
    rw [h2, zero_smul]
  have hinj : Function.Injective Ψ := by
    intro f f' h
    have h1 : Ψ (f + f') = 0 := by rw [map_add, ← h]; exact hdbl _
    have hmem := (Submodule.Quotient.mk_eq_zero ((B1 ρ).comap (Z1 ρ).subtype)).1 h1
    have h2 : f + f' = 0 := S.cW_inj ρ hρ s hs Φ hΦ hn (f + f') hmem
    apply AddMonoidHom.ext
    intro x
    have h3 := DFunLike.congr_fun h2 x
    simp only [AddMonoidHom.add_apply, AddMonoidHom.zero_apply] at h3
    revert h3
    generalize f x = a
    generalize f' x = b
    revert a b
    decide
  have h1 := Nat.card_le_card_of_injective Ψ hinj
  have hC : ∀ c : ↥(commV G ⊓ fixV G), c ^ 2 = 1 := fun c => Subtype.ext (hV c)
  have h2 := card_hom_zmod2 hC
  calc Nat.card ↥(commV G ⊓ fixV G) = Nat.card (Additive ↥(commV G ⊓ fixV G) →+ ZMod 2) :=
        h2.symm
    _ ≤ Nat.card (H1 ρ) := h1
    _ ≤ 2 ^ n := hH

end Claim2

end Inj

end CFSG.CGT.PushingUpLit.CGT6
