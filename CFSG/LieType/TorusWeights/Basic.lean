module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Basic
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.RepresentationTheory.Basic

public section

namespace CFSG.LieType.TorusWeights

open Finset

attribute [local instance] Fintype.ofFinite Classical.propDecidable

variable {n : ℕ} {G : Type*} [Group G] {K : Type*} [Field K] [Finite K] [CharP K 2]
  {X : Type*} [AddCommGroup X] [Module K X]
  (h : (Fin n → Kˣ) →* G) (ρ : Representation K G X)

@[expose] def castW (N : ℕ) (α : Fin n → ℤ) : Fin n → ZMod N := fun k => (α k : ZMod N)

@[expose] noncomputable def wtChar (a : Fin n → ZMod (Nat.card Kˣ)) : (Fin n → Kˣ) →* Kˣ where
  toFun t := ∏ k, t k ^ (a k).val
  map_one' := by simp
  map_mul' s t := by simp only [Pi.mul_apply, mul_pow, Finset.prod_mul_distrib]

omit [Finite K] [CharP K 2] in
theorem wtChar_apply (a : Fin n → ZMod (Nat.card Kˣ)) (t : Fin n → Kˣ) :
    wtChar a t = ∏ k, t k ^ (a k).val := rfl

omit [Finite K] [CharP K 2] in
theorem wtChar_zero (t : Fin n → Kˣ) : wtChar (0 : Fin n → ZMod (Nat.card Kˣ)) t = 1 := by
  simp [wtChar]

omit [CharP K 2] in
theorem wtChar_add (a b : Fin n → ZMod (Nat.card Kˣ)) (t : Fin n → Kˣ) :
    wtChar (a + b) t = wtChar a t * wtChar b t := by
  simp only [wtChar_apply, Pi.add_apply]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← pow_add]
  conv_rhs => rw [pow_eq_pow_mod (a := t k) (n := Nat.card Kˣ) _ pow_card_eq_one']
  rw [ZMod.val_add]

omit [CharP K 2] in
theorem wtChar_neg (a : Fin n → ZMod (Nat.card Kˣ)) (t : Fin n → Kˣ) :
    wtChar (-a) t = (wtChar a t)⁻¹ := by
  have h := wtChar_add a (-a) t
  rw [add_neg_cancel, wtChar_zero] at h
  exact eq_inv_of_mul_eq_one_right h.symm

omit [CharP K 2] in
theorem wtChar_sub (a b : Fin n → ZMod (Nat.card Kˣ)) (t : Fin n → Kˣ) :
    wtChar (a - b) t = wtChar a t / wtChar b t := by
  rw [sub_eq_add_neg, wtChar_add, wtChar_neg, div_eq_mul_inv]

omit [CharP K 2] in
private theorem units_pow_val_intCast (x : Kˣ) (m : ℤ) :
    x ^ ((m : ZMod (Nat.card Kˣ)).val) = x ^ m := by
  have hdec : ((m : ZMod (Nat.card Kˣ)).val : ℤ) + (Nat.card Kˣ : ℤ) *
      (m / (Nat.card Kˣ : ℤ)) = m := by
    rw [show ((m : ZMod (Nat.card Kˣ)).val : ℤ) = m % (Nat.card Kˣ : ℤ) from
      ZMod.val_intCast m]
    exact Int.emod_add_mul_ediv m (Nat.card Kˣ)
  rw [← zpow_natCast]
  conv_rhs => rw [← hdec]
  rw [zpow_add, zpow_mul, show x ^ (Nat.card Kˣ : ℤ) = 1 from by
    rw [zpow_natCast, pow_card_eq_one'], one_zpow, mul_one]

omit [CharP K 2] in
private theorem units_pow_val_natCast (x : Kˣ) (m : ℕ) :
    x ^ ((m : ZMod (Nat.card Kˣ)).val) = x ^ m := by
  simp

omit [CharP K 2] in
theorem wtChar_castW (α : Fin n → ℤ) (t : Fin n → Kˣ) :
    wtChar (castW (Nat.card Kˣ) α) t = ∏ k, t k ^ α k := by
  rw [wtChar_apply]
  exact Finset.prod_congr rfl fun k _ => units_pow_val_intCast (t k) (α k)

omit [CharP K 2] in
theorem wtChar_natCast_smul (k : ℕ) (a : Fin n → ZMod (Nat.card Kˣ)) (t : Fin n → Kˣ) :
    wtChar ((k : ZMod (Nat.card Kˣ)) • a) t = wtChar a t ^ k := by
  rw [wtChar_apply, wtChar_apply, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hcast : (((k : ZMod (Nat.card Kˣ)) • a) i) =
      ((k * (a i).val : ℕ) : ZMod (Nat.card Kˣ)) := by
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← ZMod.natCast_zmod_val (a i), Nat.cast_mul]
    norm_num
  rw [hcast, units_pow_val_natCast (t i) (k * (a i).val), mul_comm, pow_mul]

@[expose] def wtSpace (a : Fin n → ZMod (Nat.card Kˣ)) : Submodule K X where
  carrier := {x | ∀ t : Fin n → Kˣ, ρ (h t) x = (wtChar a t : K) • x}
  add_mem' := by
    intro x y hx hy t
    rw [map_add, hx t, hy t, smul_add]
  zero_mem' := by
    intro t
    rw [map_zero, smul_zero]
  smul_mem' := by
    intro c x hx t
    rw [map_smul, hx t, smul_comm]

omit [Finite K] [CharP K 2] in
theorem mem_wtSpace {a : Fin n → ZMod (Nat.card Kˣ)} {x : X} :
    x ∈ wtSpace h ρ a ↔ ∀ t : Fin n → Kˣ, ρ (h t) x = (wtChar a t : K) • x :=
  Iff.rfl

@[expose] noncomputable def wtProj (a : Fin n → ZMod (Nat.card Kˣ)) : Module.End K X :=
  ∑ t : Fin n → Kˣ, ((wtChar a t)⁻¹ : K) • ρ (h t)

omit [CharP K 2] in
theorem wtProj_apply (a : Fin n → ZMod (Nat.card Kˣ)) (x : X) :
    wtProj h ρ a x = ∑ t : Fin n → Kˣ, ((wtChar a t)⁻¹ : K) • ρ (h t) x := by
  rw [wtProj]
  exact LinearMap.sum_apply _ _ x

theorem natCard_units_cast_eq_one : ((Nat.card Kˣ : ℕ) : K) = 1 := by
  classical
  have hq : ((Nat.card K : ℕ) : K) = 0 := by
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.cast_card_eq_zero K
  have h1 : 1 ≤ Nat.card K := Nat.one_le_iff_ne_zero.mpr Nat.card_pos.ne'
  rw [Nat.card_units, Nat.cast_sub h1, hq, zero_sub, CharTwo.neg_eq, Nat.cast_one]

omit [Finite K] [CharP K 2] in
private theorem prod_ite_eq_one {α : Type*} [DecidableEq α] (f : Fin n → α) (z : α) :
    (∏ k, if f k = z then (1 : K) else 0) = if f = fun _ => z then 1 else 0 := by
  classical
  by_cases hf : f = fun _ => z
  · rw [hf]
    simp
  · have hex : ∃ k, f k ≠ z := by
      by_contra h
      push Not at h
      exact hf (funext h)
    obtain ⟨k, hk⟩ := hex
    rw [if_neg hf, Finset.prod_eq_zero (Finset.mem_univ k)]
    simp [hk]

theorem sum_units_pow (i : ℕ) :
    (∑ x : Kˣ, (x : K) ^ i) = if Nat.card Kˣ ∣ i then 1 else 0 := by
  classical
  have h := FiniteField.sum_pow_units (K := K) i
  have hq : Fintype.card K - 1 = Nat.card Kˣ := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units]
  rw [hq, show (-1 : K) = 1 from CharTwo.neg_eq 1] at h
  exact h

private theorem sum_zmod_pow_val (u : Kˣ) :
    (∑ e : ZMod (Nat.card Kˣ), (u : K) ^ e.val) = if u = 1 then 1 else 0 := by
  classical
  have hreindex : (∑ e : ZMod (Nat.card Kˣ), (u : K) ^ e.val) =
      ∑ e : Fin (Nat.card Kˣ), (u : K) ^ (e : ℕ) := by
    refine Fintype.sum_bijective (fun e : ZMod (Nat.card Kˣ) =>
      (⟨e.val, ZMod.val_lt e⟩ : Fin (Nat.card Kˣ))) ?_ _ _ fun e => rfl
    refine ⟨fun a b hab => ZMod.val_injective _ ?_, fun b => ⟨(b : ZMod (Nat.card Kˣ)), ?_⟩⟩
    · simpa using congrArg Fin.val hab
    · apply Fin.ext
      change ((b : ZMod (Nat.card Kˣ)).val) = b.val
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt b.isLt]
  rw [hreindex]
  by_cases hu : u = 1
  · subst u
    have hsum : (∑ e : Fin (Nat.card Kˣ), ((1 : Kˣ) : K) ^ (e : ℕ)) =
        ((Nat.card Kˣ : ℕ) : K) := by simp
    rw [hsum, natCard_units_cast_eq_one]
    simp
  · have hN : (u : K) ^ Nat.card Kˣ = 1 := by
      rw [← Units.val_pow_eq_pow_val, pow_card_eq_one', Units.val_one]
    have hgeom : (∑ e : Fin (Nat.card Kˣ), (u : K) ^ (e : ℕ)) * ((u : K) - 1) = 0 := by
      rw [Fin.sum_univ_eq_sum_range (fun e => (u : K) ^ e) (Nat.card Kˣ), geom_sum_mul, hN,
        sub_self]
    rcases mul_eq_zero.mp hgeom with h' | h'
    · rw [h', if_neg hu]
    · exact absurd (Units.ext (sub_eq_zero.mp h')) hu

theorem sum_wtChar (a : Fin n → ZMod (Nat.card Kˣ)) :
    (∑ t : Fin n → Kˣ, (wtChar a t : K)) = if a = 0 then 1 else 0 := by
  classical
  have hprod : (∑ t : Fin n → Kˣ, (wtChar a t : K)) =
      ∏ k, ∑ u : Kˣ, (u : K) ^ (a k).val := by
    rw [← Finset.sum_prod_piFinset (s := (Finset.univ : Finset Kˣ))
      (g := fun k u => (u : K) ^ (a k).val)]
    simp [wtChar_apply]
  have hdvd : ∀ k : Fin n, Nat.card Kˣ ∣ (a k).val ↔ a k = 0 := by
    intro k
    constructor
    · intro h
      rw [← ZMod.natCast_zmod_val (a k)]
      exact (ZMod.natCast_eq_zero_iff _ _).mpr h
    · intro h
      rw [h, ZMod.val_zero]
      exact dvd_zero _
  rw [hprod]
  simp only [sum_units_pow, hdvd, prod_ite_eq_one]
  rfl

theorem sum_wtChar' (t : Fin n → Kˣ) :
    (∑ a : Fin n → ZMod (Nat.card Kˣ), (wtChar a t : K)) = if t = 1 then 1 else 0 := by
  classical
  have hprod : (∑ a : Fin n → ZMod (Nat.card Kˣ), (wtChar a t : K)) =
      ∏ k, ∑ e : ZMod (Nat.card Kˣ), (t k : K) ^ e.val := by
    rw [← Finset.sum_prod_piFinset (s := (Finset.univ : Finset (ZMod (Nat.card Kˣ))))
      (g := fun k e => (t k : K) ^ e.val)]
    simp [wtChar_apply]
  rw [hprod]
  simp only [sum_zmod_pow_val, prod_ite_eq_one]
  rfl

omit [CharP K 2] in
theorem wtProj_mem (a : Fin n → ZMod (Nat.card Kˣ)) (x : X) :
    wtProj h ρ a x ∈ wtSpace h ρ a := by
  rw [mem_wtSpace]
  intro s
  rw [wtProj_apply, map_sum]
  have hterm : ∀ t : Fin n → Kˣ, ρ (h s) (((wtChar a t)⁻¹ : K) • ρ (h t) x) =
      ((wtChar a t)⁻¹ : K) • ρ (h (s * t)) x := by
    intro t
    rw [map_smul]
    congr 1
    rw [← Module.End.mul_apply, ← map_mul, map_mul (f := h)]
  simp only [hterm]
  have h1 : (∑ t : Fin n → Kˣ, ((wtChar a t)⁻¹ : K) • ρ (h (s * t)) x) =
      ∑ u : Fin n → Kˣ, ((wtChar a (s⁻¹ * u))⁻¹ : K) • ρ (h u) x := by
    rw [← Equiv.sum_comp (Equiv.mulLeft s)
      (fun u : Fin n → Kˣ => ((wtChar a (s⁻¹ * u))⁻¹ : K) • ρ (h u) x)]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Equiv.coe_mulLeft, ← mul_assoc, inv_mul_cancel, one_mul]
  have h2 : ∀ u : Fin n → Kˣ, ((wtChar a (s⁻¹ * u))⁻¹ : K) • ρ (h u) x =
      (wtChar a s : K) • (((wtChar a u)⁻¹ : K) • ρ (h u) x) := by
    intro u
    have hc : ((wtChar a (s⁻¹ * u) : K))⁻¹ =
        (wtChar a s : K) * ((wtChar a u : K))⁻¹ := by
      rw [← Units.val_inv_eq_inv_val,
        show (wtChar a (s⁻¹ * u))⁻¹ = wtChar a s * (wtChar a u)⁻¹ from by
          rw [map_mul, map_inv, mul_inv_rev, inv_inv, mul_comm],
        Units.val_mul, Units.val_inv_eq_inv_val]
    rw [hc, mul_smul]
  rw [h1, Finset.smul_sum]
  exact Finset.sum_congr rfl fun u _ => h2 u

theorem wtProj_of_mem {a b : Fin n → ZMod (Nat.card Kˣ)} {x : X}
    (hx : x ∈ wtSpace h ρ b) : wtProj h ρ a x = if a = b then x else 0 := by
  rw [wtProj_apply]
  have hsub : ∀ t : Fin n → Kˣ,
      ((wtChar a t)⁻¹ : K) * (wtChar b t : K) = (wtChar (b - a) t : K) := by
    intro t
    rw [wtChar_sub, div_eq_mul_inv, Units.val_mul, Units.val_inv_eq_inv_val]
    ring
  have hterm : ∀ t : Fin n → Kˣ, ((wtChar a t)⁻¹ : K) • ρ (h t) x =
      (wtChar (b - a) t : K) • x := by
    intro t
    have hxt : ρ (h t) x = (wtChar b t : K) • x :=
      (mem_wtSpace (h := h) (ρ := ρ)).mp hx t
    rw [hxt, ← mul_smul, hsub]
  simp only [hterm, ← Finset.sum_smul, sum_wtChar]
  have hcond : b - a = 0 ↔ a = b := by rw [sub_eq_zero, eq_comm]
  by_cases hab : a = b
  · rw [if_pos (hcond.mpr hab), if_pos hab, one_smul]
  · rw [if_neg (fun h => hab (hcond.mp h)), if_neg hab, zero_smul]

theorem sum_wtProj (x : X) :
    (∑ a : Fin n → ZMod (Nat.card Kˣ), wtProj h ρ a x) = x := by
  simp only [wtProj_apply]
  rw [Finset.sum_comm]
  have hinner : ∀ t : Fin n → Kˣ,
      (∑ a : Fin n → ZMod (Nat.card Kˣ), ((wtChar a t)⁻¹ : K)) =
        if t = 1 then 1 else 0 := by
    intro t
    have hneg : (∑ a : Fin n → ZMod (Nat.card Kˣ), ((wtChar a t)⁻¹ : K)) =
        ∑ a : Fin n → ZMod (Nat.card Kˣ), (wtChar a t : K) := by
      rw [← Equiv.sum_comp (Equiv.neg (Fin n → ZMod (Nat.card Kˣ)))
        (fun a => (wtChar a t : K))]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Equiv.neg_apply, wtChar_neg, Units.val_inv_eq_inv_val]
    rw [hneg]
    exact sum_wtChar' t
  simp only [← Finset.sum_smul, hinner]
  rw [Finset.sum_eq_single (1 : Fin n → Kˣ)]
  · simp
  · intro t _ ht
    simp [ht]
  · intro h
    exact absurd (Finset.mem_univ (1 : Fin n → Kˣ)) h

omit [CharP K 2] in
theorem wtProj_comm_h (a : Fin n → ZMod (Nat.card Kˣ)) (t : Fin n → Kˣ) :
    ρ (h t) ∘ₗ wtProj h ρ a = wtProj h ρ a ∘ₗ ρ (h t) := by
  ext x
  simp only [LinearMap.comp_apply, wtProj_apply, map_sum, map_smul]
  refine Finset.sum_congr rfl fun u _ => ?_
  congr 1
  rw [← Module.End.mul_apply, ← Module.End.mul_apply]
  rw [show ρ (h t) * ρ (h u) = ρ (h u) * ρ (h t) from by
    calc ρ (h t) * ρ (h u) = ρ (h t * h u) := (map_mul ρ _ _).symm
      _ = ρ (h (t * u)) := congrArg (fun z => ρ z) (map_mul h t u).symm
      _ = ρ (h (u * t)) := by rw [mul_comm t u]
      _ = ρ (h u * h t) := congrArg (fun z => ρ z) (map_mul h u t)
      _ = ρ (h u) * ρ (h t) := map_mul ρ _ _]

theorem iSup_wtSpace : ⨆ a, wtSpace h ρ a = ⊤ := by
  refine le_antisymm le_top ?_
  intro x _
  rw [show x = ∑ a, wtProj h ρ a x from (sum_wtProj h ρ x).symm]
  exact Submodule.sum_mem _ fun a _ => Submodule.mem_iSup_of_mem a (wtProj_mem h ρ a x)

theorem iSupIndep_wtSpace : iSupIndep (wtSpace h ρ) := by
  rw [iSupIndep_def]
  intro a
  rw [disjoint_iff_inf_le]
  rintro x ⟨hxa, hxsup⟩
  have hker : (⨆ (b) (_ : b ≠ a), wtSpace h ρ b) ≤ LinearMap.ker (wtProj h ρ a) := by
    refine iSup_le fun b => iSup_le fun hb => ?_
    intro y hy
    rw [LinearMap.mem_ker, wtProj_of_mem h ρ hy]
    simp [Ne.symm hb]
  have hx0 : wtProj h ρ a x = 0 := hker hxsup
  have hx1 : wtProj h ρ a x = x := by
    rw [wtProj_of_mem h ρ hxa]
    simp
  have hxeq : x = 0 := by rw [← hx1, hx0]
  rw [hxeq]
  exact Submodule.zero_mem _

theorem finrank_eq_sum_finrank_wtSpace [FiniteDimensional K X] :
    Module.finrank K X = ∑ a, Module.finrank K (wtSpace h ρ a) := by
  have h := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (iSupIndep_wtSpace h ρ) (iSup_wtSpace h ρ)
  rw [← (LinearEquiv.ofBijective (DirectSum.coeLinearMap _) h).finrank_eq,
    Module.finrank_directSum]

theorem odd_natCard_units : Odd (Nat.card Kˣ) := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨f, -, hq⟩ := FiniteField.card K 2
  rw [Nat.card_units, Nat.card_eq_fintype_card, hq]
  obtain ⟨j, hj⟩ : ∃ j : ℕ, (f : ℕ) = j + 1 := ⟨(f : ℕ) - 1, by have := f.pos; omega⟩
  rw [hj, pow_succ]
  have hp : 1 ≤ 2 ^ j := Nat.one_le_two_pow
  exact ⟨2 ^ j - 1, by omega⟩

omit [CharP K 2] in
theorem wtChar_eq_one_iff {a : Fin n → ZMod (Nat.card Kˣ)} :
    (∀ t, wtChar a t = 1) ↔ a = 0 := by
  constructor
  · intro ha
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
    have hord : orderOf g = Nat.card Kˣ := orderOf_eq_card_of_forall_mem_zpowers hg
    funext i
    have ht : wtChar a (Function.update (1 : Fin n → Kˣ) i g) = 1 := ha _
    have hprod : (∏ k, Function.update (1 : Fin n → Kˣ) i g k ^ (a k).val) =
        g ^ (a i).val := by
      rw [Finset.prod_eq_single i]
      · simp
      · intro k _ hk
        simp [Function.update_of_ne hk]
      · intro hi
        exact absurd (Finset.mem_univ i) hi
    rw [wtChar_apply, hprod] at ht
    have hdvd' : orderOf g ∣ (a i).val := orderOf_dvd_of_pow_eq_one ht
    have hdvd : Nat.card Kˣ ∣ (a i).val := by
      rwa [hord] at hdvd'
    have hval : (a i).val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (ZMod.val_lt (a i))
    rw [← ZMod.natCast_zmod_val (a i), hval, Nat.cast_zero]
    simp
  · rintro rfl t
    exact wtChar_zero t

theorem ext_of_wtSpace {f g : Module.End K X}
    (hfg : ∀ a, ∀ x ∈ wtSpace h ρ a, f x = g x) : f = g := by
  ext x
  rw [← sum_wtProj h ρ x, map_sum, map_sum]
  exact Finset.sum_congr rfl fun a _ => hfg a _ (wtProj_mem h ρ a x)

omit [Finite K] [CharP K 2] in
theorem map_mem_wtSpace {m : G} {τ : (Fin n → Kˣ) → (Fin n → Kˣ)}
    (hm : ∀ t, m⁻¹ * h t * m = h (τ t)) {a b : Fin n → ZMod (Nat.card Kˣ)}
    (hab : ∀ t, wtChar a (τ t) = wtChar b t) {x : X} (hx : x ∈ wtSpace h ρ a) :
    ρ m x ∈ wtSpace h ρ b := by
  rw [mem_wtSpace] at hx ⊢
  intro t
  have hconj : ρ m⁻¹ * ρ (h t) * ρ m = ρ (h (τ t)) := by
    rw [← map_mul, ← map_mul]
    exact congrArg ρ (hm t)
  have h1 : ρ m⁻¹ (ρ (h t) (ρ m x)) = (wtChar a (τ t) : K) • x := by
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, hconj, hx (τ t)]
  have hcancel : ∀ v : X, ρ m (ρ m⁻¹ v) = v := by
    intro v
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  calc ρ (h t) (ρ m x)
      = ρ m (ρ m⁻¹ (ρ (h t) (ρ m x))) := (hcancel _).symm
    _ = ρ m ((wtChar a (τ t) : K) • x) := by rw [h1]
    _ = (wtChar a (τ t) : K) • ρ m x := by rw [map_smul]
    _ = (wtChar b t : K) • ρ m x := by rw [hab t]

omit [Finite K] [CharP K 2] in
theorem finrank_wtSpace_le_of_conj [FiniteDimensional K X] {m : G}
    {τ : (Fin n → Kˣ) → (Fin n → Kˣ)} (hm : ∀ t, m⁻¹ * h t * m = h (τ t))
    {a b : Fin n → ZMod (Nat.card Kˣ)} (hab : ∀ t, wtChar a (τ t) = wtChar b t) :
    Module.finrank K (wtSpace h ρ a) ≤ Module.finrank K (wtSpace h ρ b) := by
  have hle : (wtSpace h ρ a).map (ρ m) ≤ wtSpace h ρ b := by
    rintro _ ⟨x, hx, rfl⟩
    exact map_mem_wtSpace h ρ hm hab hx
  calc Module.finrank K (wtSpace h ρ a)
      = Module.finrank K ((wtSpace h ρ a).map (ρ m)) :=
        (LinearEquiv.finrank_map_eq (LinearEquiv.ofBijective (ρ m) (ρ.apply_bijective m)) _).symm
    _ ≤ Module.finrank K (wtSpace h ρ b) := Submodule.finrank_mono hle

omit [Finite K] [CharP K 2] in
theorem wtChar_comp_perm (σ : Equiv.Perm (Fin n)) (a : Fin n → ZMod (Nat.card Kˣ))
    (t : Fin n → Kˣ) : wtChar a (t ∘ σ) = wtChar (a ∘ σ.symm) t := by
  rw [wtChar_apply, wtChar_apply]
  set f : Fin n → Kˣ := fun j => t j ^ (a (σ.symm j)).val with hf
  calc (∏ k, (t ∘ σ) k ^ (a k).val)
      = ∏ k, f (σ k) := by simp [f]
    _ = ∏ k, f k := Equiv.prod_comp σ f
    _ = ∏ k, t k ^ ((a ∘ σ.symm) k).val := by simp [f]

omit [CharP K 2] in
theorem wtChar_update_inv (i : Fin n) (a : Fin n → ZMod (Nat.card Kˣ))
    (t : Fin n → Kˣ) :
    wtChar a (Function.update t i (t i)⁻¹) =
      wtChar (Function.update a i (-a i)) t := by
  rw [wtChar_apply, wtChar_apply]
  refine Finset.prod_congr rfl fun k _ => ?_
  by_cases hk : k = i
  · subst k
    rw [Function.update_self, Function.update_self]
    have hcast : (((-(a i).val : ℤ) : ZMod (Nat.card Kˣ))) = -a i := by
      push_cast
      rw [ZMod.natCast_zmod_val]
    have hx : (t i) ^ ((-a i).val) = (t i) ^ (-(a i).val : ℤ) := by
      conv_lhs => rw [← hcast]
      exact units_pow_val_intCast (t i) (-(a i).val)
    rw [hx, zpow_neg, zpow_natCast, inv_pow]
  · rw [Function.update_of_ne hk, Function.update_of_ne hk]

omit [CharP K 2] in
theorem bilin_eq_zero_of_mem_wtSpace {B : LinearMap.BilinForm K X}
    (hB : ∀ g u v, B (ρ g u) (ρ g v) = B u v) {a b : Fin n → ZMod (Nat.card Kˣ)}
    (hab : a + b ≠ 0) {u v : X} (hu : u ∈ wtSpace h ρ a) (hv : v ∈ wtSpace h ρ b) :
    B u v = 0 := by
  have hne : ∃ t : Fin n → Kˣ, wtChar (a + b) t ≠ 1 := by
    by_contra h
    push Not at h
    exact hab ((wtChar_eq_one_iff (K := K) (n := n)).mp h)
  obtain ⟨t, ht⟩ := hne
  have hua := (mem_wtSpace h ρ).mp hu t
  have hvb := (mem_wtSpace h ρ).mp hv t
  have hBinv := hB (h t) u v
  rw [hua, hvb, LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right] at hBinv
  have hcoef : (wtChar (a + b) t : K) = (wtChar a t : K) * (wtChar b t : K) := by
    rw [wtChar_add, Units.val_mul]
  have hc : (wtChar (a + b) t : K) ≠ 1 := by
    intro h
    exact ht (Units.ext h)
  have hEq : (wtChar (a + b) t : K) * B u v = B u v := by
    calc (wtChar (a + b) t : K) * B u v
        = ((wtChar a t : K) * (wtChar b t : K)) * B u v := by rw [hcoef]
      _ = (wtChar a t : K) * ((wtChar b t : K) * B u v) := by ring
      _ = B u v := hBinv
  have hmul : ((1 : K) - (wtChar (a + b) t : K)) * B u v = 0 := by
    rw [sub_mul, one_mul, hEq, sub_self]
  exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr (Ne.symm hc))

theorem quad_eq_zero_of_mem_wtSpace {Q : QuadraticForm K X}
    (hQ : ∀ g v, Q (ρ g v) = Q v) {a : Fin n → ZMod (Nat.card Kˣ)} (ha : a ≠ 0)
    {v : X} (hv : v ∈ wtSpace h ρ a) : Q v = 0 := by
  have haa : a + a ≠ 0 := by
    intro h
    apply ha
    funext i
    have hi : a i + a i = 0 := by
      simpa using congrFun h i
    exact (ZMod.add_self_eq_zero_iff_eq_zero (n := Nat.card Kˣ)
      (odd_natCard_units (K := K))).mp hi
  have hne : ∃ t : Fin n → Kˣ, wtChar (a + a) t ≠ 1 := by
    by_contra h
    push Not at h
    exact haa ((wtChar_eq_one_iff (K := K) (n := n)).mp h)
  obtain ⟨t, ht⟩ := hne
  have hv' := (mem_wtSpace h ρ).mp hv t
  have hQinv := hQ (h t) v
  rw [hv', QuadraticMap.map_smul] at hQinv
  have hcoef : (wtChar a t : K) * (wtChar a t : K) = (wtChar (a + a) t : K) := by
    rw [wtChar_add, Units.val_mul]
  rw [hcoef, smul_eq_mul] at hQinv
  have hc : (wtChar (a + a) t : K) ≠ 1 := by
    intro h
    exact ht (Units.ext h)
  have hmul : ((1 : K) - (wtChar (a + a) t : K)) * Q v = 0 := by
    rw [sub_mul, one_mul, hQinv, sub_self]
  exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr (Ne.symm hc))

end CFSG.LieType.TorusWeights
