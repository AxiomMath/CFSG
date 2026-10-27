module

public import CFSG.Quasithin.Background.G6Natural
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.CGT.PushingUpLit.SYMB

open CFSG.Quasithin

namespace Split5

def sg : Fin 4 → Equiv.Perm (Fin 5) :=
  ![1, Equiv.swap 0 1 * Equiv.swap 2 3, Equiv.swap 0 2 * Equiv.swap 1 3,
    Equiv.swap 0 3 * Equiv.swap 1 2]

theorem sg_zero : sg 0 = 1 := by decide +kernel

theorem sg_injective : Function.Injective sg := by decide +kernel

theorem sg_mul : ∀ k j : Fin 4, ∃ m, sg k * sg j = sg m := by decide +kernel

theorem sg_inv : ∀ k : Fin 4, ∃ m, (sg k)⁻¹ = sg m := by decide +kernel

theorem sg_alt : ∀ k : Fin 4, sg k ∈ alternatingGroup (Fin 5) := by
  intro k
  rw [Equiv.Perm.mem_alternatingGroup]
  revert k
  decide +kernel

def klein : Subgroup (Equiv.Perm (Fin 5)) where
  carrier := Set.range sg
  one_mem' := ⟨0, sg_zero⟩
  mul_mem' := by
    rintro _ _ ⟨k, rfl⟩ ⟨j, rfl⟩
    obtain ⟨m, hm⟩ := sg_mul k j
    exact ⟨m, hm.symm⟩
  inv_mem' := by
    rintro _ ⟨k, rfl⟩
    obtain ⟨m, hm⟩ := sg_inv k
    exact ⟨m, hm.symm⟩

theorem klein_le_alt : klein ≤ alternatingGroup (Fin 5) := by
  rintro _ ⟨k, rfl⟩
  exact sg_alt k

theorem card_klein : Nat.card klein = 4 := by
  have h : Nat.card (Set.range sg) = Nat.card (Fin 4) := Nat.card_range_of_injective sg_injective
  rw [Nat.card_eq_fintype_card (α := Fin 4), Fintype.card_fin] at h
  exact h

theorem index_klein : klein.index = 30 := by
  have h := Subgroup.card_mul_index klein
  rw [card_klein] at h
  have h2 : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]
    simp [Nat.factorial]
  omega

theorem relIndex_klein : klein.relIndex (alternatingGroup (Fin 5)) = 15 := by
  have h := Subgroup.relIndex_mul_index klein_le_alt
  rw [index_klein, alternatingGroup.index_eq_two] at h
  omega

theorem index_comap_klein {E : Type*} [Group E] (η : E →* Equiv.Perm (Fin 5))
    (hA : ∀ e, η e ∈ alternatingGroup (Fin 5))
    (hs : ∀ σ ∈ alternatingGroup (Fin 5), ∃ e, η e = σ) : (klein.comap η).index = 15 := by
  have hr : η.range = alternatingGroup (Fin 5) := by
    ext σ
    constructor
    · rintro ⟨e, rfl⟩
      exact hA e
    · intro hσ
      exact hs σ hσ
  rw [Subgroup.index_comap, hr, relIndex_klein]

section Vectors

local instance instDecidablePredMemCore : DecidablePred (· ∈ G6.coreMod 5) :=
  fun x => decidable_of_iff (∑ i, Multiplicative.toAdd x i = 0) G6.mem_coreMod.symm

def delta : G6.coreMod 5 :=
  ⟨Multiplicative.ofAdd (fun i => if i = 0 ∨ i = 4 then (1 : ZMod 2) else 0), by
    rw [G6.mem_coreMod]
    decide +kernel⟩

def vv (k : Fin 4) : G6.coreMod 5 := G6.coreAct 5 (sg k) delta

def crd (w : G6.coreMod 5) (k : Fin 4) : ZMod 2 :=
  Multiplicative.toAdd (w : G6.PermMod 5) (Fin.castSucc k)

set_option synthInstance.maxSize 2000 in
theorem vv_basis : ∀ w : G6.coreMod 5, ∏ k : Fin 4, vv k ^ (crd w k).val = w := by
  decide +kernel

theorem crd_vv : ∀ j k : Fin 4, (crd (vv j) k).val = if k = j then 1 else 0 := by
  decide +kernel

theorem core_sq : ∀ w : G6.coreMod 5, w * w = 1 := by decide +kernel

end Vectors

section BasisHom

variable {X : Type*} [CommGroup X]

theorem pow_val_add (u : X) (hu : u * u = 1) (a b : ZMod 2) :
    u ^ (a + b).val = u ^ a.val * u ^ b.val := by
  have hmod : ∀ n : ℕ, u ^ (n % 2) = u ^ n := by
    intro n
    conv_rhs => rw [← Nat.mod_add_div n 2, pow_add, pow_mul, sq, hu, one_pow, mul_one]
  rw [ZMod.val_add, hmod, pow_add]

def secOf (hX : ∀ x : X, x * x = 1) (u : Fin 4 → X) : G6.coreMod 5 →* X where
  toFun w := ∏ k : Fin 4, u k ^ (crd w k).val
  map_one' := by simp [crd]
  map_mul' w₁ w₂ := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← pow_val_add (u k) (hX _)]
    rfl

theorem secOf_vv (hX : ∀ x : X, x * x = 1) (u : Fin 4 → X) (j : Fin 4) :
    secOf hX u (vv j) = u j := by
  show ∏ k : Fin 4, u k ^ (crd (vv j) k).val = u j
  rw [Finset.prod_eq_single j]
  · simp [crd_vv]
  · intro k _ hk
    simp [crd_vv, hk]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem hom_eq_of_basis (F₁ F₂ : G6.coreMod 5 →* X) (h : ∀ k : Fin 4, F₁ (vv k) = F₂ (vv k)) :
    F₁ = F₂ := by
  ext w
  rw [← vv_basis w, map_prod, map_prod]
  exact Finset.prod_congr rfl fun k _ => by rw [map_pow, map_pow, h]

end BasisHom

section Avg

variable {E : Type*} [Group E] {X Y : Type*} [CommGroup X] [Monoid Y]

theorem twist_mul_right (H : Subgroup E) (act : E →* MulAut X) (actY : E →* MulAut Y)
    (f : Y →* X) (hf : ∀ h ∈ H, ∀ y, f (actY h y) = act h (f y)) (g : E) {h : E} (hh : h ∈ H)
    (y : Y) : act (g * h) (f (actY (g * h)⁻¹ y)) = act g (f (actY g⁻¹ y)) := by
  have hz : ∀ z, act h (f (actY h⁻¹ z)) = f z := fun z => by
    rw [← hf h hh, ← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  rw [map_mul act, MulAut.mul_apply, mul_inv_rev, map_mul actY, MulAut.mul_apply, hz]

theorem twist_congr (H : Subgroup E) (act : E →* MulAut X) (actY : E →* MulAut Y)
    (f : Y →* X) (hf : ∀ h ∈ H, ∀ y, f (actY h y) = act h (f y)) {g g' : E}
    (hg : g⁻¹ * g' ∈ H) (y : Y) :
    act g (f (actY g⁻¹ y)) = act g' (f (actY g'⁻¹ y)) := by
  have h := twist_mul_right H act actY f hf g hg y
  rw [mul_inv_cancel_left] at h
  exact h.symm

theorem out_inv_mul_mem (H : Subgroup E) (g : E) (x : E ⧸ H) :
    (g • x).out⁻¹ * (g * x.out) ∈ H := by
  have h : ((g • x).out : E ⧸ H) = ((g * x.out : E) : E ⧸ H) := by
    rw [QuotientGroup.out_eq']
    conv_rhs => rw [← smul_eq_mul, ← MulAction.Quotient.smul_mk, QuotientGroup.out_eq']
  exact QuotientGroup.eq.mp h

noncomputable def avg (H : Subgroup E) [Fintype (E ⧸ H)] (act : E →* MulAut X)
    (actY : E →* MulAut Y) (f : Y →* X) : Y →* X where
  toFun y := ∏ q : E ⧸ H, act q.out (f (actY q.out⁻¹ y))
  map_one' := by simp
  map_mul' y y' := by simp [Finset.prod_mul_distrib]

theorem avg_act (H : Subgroup E) [Fintype (E ⧸ H)] (act : E →* MulAut X) (actY : E →* MulAut Y)
    (f : Y →* X) (hf : ∀ h ∈ H, ∀ y, f (actY h y) = act h (f y)) (e : E) (y : Y) :
    avg H act actY f (actY e y) = act e (avg H act actY f y) := by
  show ∏ q : E ⧸ H, act q.out (f (actY q.out⁻¹ (actY e y))) =
    act e (∏ q : E ⧸ H, act q.out (f (actY q.out⁻¹ y)))
  rw [map_prod, ← Equiv.prod_comp (MulAction.toPerm e)]
  refine Finset.prod_congr rfl fun q _ => ?_
  have hy : actY e⁻¹ (actY e y) = y := by
    rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl
  rw [MulAction.toPerm_apply, twist_congr H act actY f hf (out_inv_mul_mem H e q)]
  simp only [map_mul, MulAut.mul_apply, mul_inv_rev, hy]

theorem avg_section (H : Subgroup E) [Fintype (E ⧸ H)] (act : E →* MulAut X)
    (actY : E →* MulAut Y) (f : Y →* X) (ψ : X →* Y) (hψ : ∀ e x, ψ (act e x) = actY e (ψ x))
    (hf : ∀ y, ψ (f y) = y) (hY : ∀ y : Y, y * y = 1) (hodd : Odd (Nat.card (E ⧸ H))) (y : Y) :
    ψ (avg H act actY f y) = y := by
  have h1 : ∀ q : E ⧸ H, ψ (act q.out (f (actY q.out⁻¹ y))) = y := fun q => by
    rw [hψ, hf, ← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  have h2 : ∀ s : Finset (E ⧸ H),
      ψ (∏ q ∈ s, act q.out (f (actY q.out⁻¹ y))) = y ^ s.card := by
    classical
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, map_mul, h1, ih, Finset.card_insert_of_notMem ha, pow_succ']
  show ψ (∏ q : E ⧸ H, act q.out (f (actY q.out⁻¹ y))) = y
  rw [h2, Finset.card_univ, Fintype.card_eq_nat_card]
  obtain ⟨k, hk⟩ := hodd
  rw [hk, pow_succ, pow_mul, sq, hY, one_pow, one_mul]

end Avg

end Split5

theorem exists_equivariant_section {E : Type*} [Group E] [Finite E]
    (η : E →* Equiv.Perm (Fin 5))
    (hA : ∀ e, η e ∈ alternatingGroup (Fin 5))
    (hs : ∀ σ ∈ alternatingGroup (Fin 5), ∃ e, η e = σ)
    {X : Type*} [CommGroup X] [Finite X] (hX : ∀ x : X, x * x = 1)
    (act : E →* MulAut X) (hker : ∀ e, η e = 1 → ∀ x, act e x = x)
    (ψ : X →* G6.coreMod 5) (hψs : Function.Surjective ψ)
    (hψ : ∀ e x, ψ (act e x) = G6.coreAct 5 (η e) (ψ x)) :
    ∃ s : G6.coreMod 5 →* X, (∀ w, ψ (s w) = w) ∧
      ∀ e w, act e (s w) = s (G6.coreAct 5 (η e) w) := by
  have hact : ∀ a b : E, η a = η b → ∀ x, act a x = act b x := by
    intro a b hab x
    have h1 : η (b⁻¹ * a) = 1 := by rw [map_mul, map_inv, hab, inv_mul_cancel]
    calc act a x = act (b * (b⁻¹ * a)) x := by rw [mul_inv_cancel_left]
      _ = act b (act (b⁻¹ * a) x) := by rw [map_mul, MulAut.mul_apply]
      _ = act b x := by rw [hker _ h1]
  choose g hg using fun k => hs (Split5.sg k) (Split5.sg_alt k)
  obtain ⟨x₀, hx₀⟩ := hψs Split5.delta
  let u : Fin 4 → X := fun k => act (g k) x₀
  have hu : ∀ k, ψ (u k) = Split5.vv k := fun k => by
    show ψ (act (g k) x₀) = _
    rw [hψ, hg, hx₀]
    rfl
  have hsH : ∀ w, ψ (Split5.secOf hX u w) = w := by
    intro w
    show ψ (∏ k : Fin 4, u k ^ (Split5.crd w k).val) = w
    simp only [map_prod, map_pow, hu]
    exact Split5.vv_basis w
  have hH : ∀ h ∈ Split5.klein.comap η, ∀ w,
      Split5.secOf hX u (G6.coreAct 5 (η h) w) = act h (Split5.secOf hX u w) := by
    intro h hh w
    obtain ⟨k, hk⟩ := hh
    have hbasis := Split5.hom_eq_of_basis
      ((act h).toMonoidHom.comp (Split5.secOf hX u))
      ((Split5.secOf hX u).comp (G6.coreAct 5 (η h)).toMonoidHom) (fun j => by
        obtain ⟨m, hm⟩ := Split5.sg_mul k j
        have h1 : act h (u j) = u m := by
          show act h (act (g j) x₀) = act (g m) x₀
          rw [← MulAut.mul_apply, ← map_mul]
          exact hact _ _ (by rw [map_mul, hg, hg, ← hk, hm]) x₀
        have h2 : G6.coreAct 5 (η h) (Split5.vv j) = Split5.vv m := by
          rw [← hk]
          show G6.coreAct 5 (Split5.sg k) (G6.coreAct 5 (Split5.sg j) Split5.delta) =
            G6.coreAct 5 (Split5.sg m) Split5.delta
          rw [← MulAut.mul_apply, ← map_mul, hm]
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Split5.secOf_vv, h1, h2])
    exact (DFunLike.congr_fun hbasis w).symm
  let _ : Fintype (E ⧸ Split5.klein.comap η) := Fintype.ofFinite _
  have hcard : Nat.card (E ⧸ Split5.klein.comap η) = 15 := by
    rw [← Subgroup.index_eq_card]
    exact Split5.index_comap_klein η hA hs
  let actY : E →* MulAut (G6.coreMod 5) := (G6.coreAct 5).comp η
  let s : G6.coreMod 5 →* X :=
    Split5.avg (Split5.klein.comap η) act actY (Split5.secOf hX u)
  refine ⟨s, ?_, ?_⟩
  · exact Split5.avg_section (Split5.klein.comap η) act actY (Split5.secOf hX u) ψ hψ hsH
      Split5.core_sq (by rw [hcard]; decide)
  · intro e w
    exact (Split5.avg_act (Split5.klein.comap η) act actY (Split5.secOf hX u) hH e w).symm

end CFSG.CGT.PushingUpLit.SYMB
