module

public import CFSG.LieType.D4Small.Datum
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RepresentationTheory.Basic

public section

namespace CFSG.LieType.D4Small.D4Datum

open Finset

attribute [local instance] Fintype.ofFinite Classical.propDecidable

variable {G : Type*} [Group G] {K : Type*} [Field K] [Finite K] [CharP K 2]
  {X : Type*} [AddCommGroup X] [Module K X] (D : D4Datum G K) (ρ : Representation K G X)

@[expose] noncomputable def wtChar (a : Fin 4 → ZMod (Nat.card Kˣ)) : (Fin 4 → Kˣ) →* Kˣ where
  toFun t := ∏ k, t k ^ (a k).val
  map_one' := by simp
  map_mul' s t := by simp only [Pi.mul_apply, mul_pow, Finset.prod_mul_distrib]

theorem wtChar_apply (a : Fin 4 → ZMod (Nat.card Kˣ)) (t : Fin 4 → Kˣ) :
    wtChar a t = ∏ k, t k ^ (a k).val := rfl

theorem wtChar_zero (t : Fin 4 → Kˣ) : wtChar (0 : Fin 4 → ZMod (Nat.card Kˣ)) t = 1 := by
  simp [wtChar]

theorem wtChar_add (a b : Fin 4 → ZMod (Nat.card Kˣ)) (t : Fin 4 → Kˣ) :
    wtChar (a + b) t = wtChar a t * wtChar b t := by
  simp only [wtChar_apply, Pi.add_apply]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← pow_add]
  conv_rhs => rw [pow_eq_pow_mod (a := t k) (n := Nat.card Kˣ) _ pow_card_eq_one']
  rw [ZMod.val_add]

theorem wtChar_neg (a : Fin 4 → ZMod (Nat.card Kˣ)) (t : Fin 4 → Kˣ) :
    wtChar (-a) t = (wtChar a t)⁻¹ := by
  have h := wtChar_add a (-a) t
  rw [add_neg_cancel, wtChar_zero] at h
  exact eq_inv_of_mul_eq_one_right h.symm

theorem wtChar_sub (a b : Fin 4 → ZMod (Nat.card Kˣ)) (t : Fin 4 → Kˣ) :
    wtChar (a - b) t = wtChar a t / wtChar b t := by
  rw [sub_eq_add_neg, wtChar_add, wtChar_neg, div_eq_mul_inv]

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

theorem wtChar_castW_units (α : Fin 4 → ℤ) (t : Fin 4 → Kˣ) :
    wtChar (castW (Nat.card Kˣ) α) t = torusChar α t := by
  rw [wtChar_apply, torusChar_apply]
  refine Finset.prod_congr rfl fun k _ => ?_
  exact units_pow_val_intCast (t k) (α k)

theorem wtChar_castW (α : Fin 4 → ℤ) (t : Fin 4 → Kˣ) :
    (wtChar (castW (Nat.card Kˣ) α) t : K) = ((torusChar α t : Kˣ) : K) :=
  congrArg ((↑) : Kˣ → K) (wtChar_castW_units α t)

theorem wtChar_nsmul_castW_units (k : ℕ) (α : Fin 4 → ℤ) (t : Fin 4 → Kˣ) :
    wtChar ((k : ZMod (Nat.card Kˣ)) • castW (Nat.card Kˣ) α) t = (torusChar α t) ^ k := by
  rw [wtChar_apply, torusChar_apply, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hcast : ((k : ZMod (Nat.card Kˣ)) • castW (Nat.card Kˣ) α) i =
      ((α i * (k : ℤ) : ℤ) : ZMod (Nat.card Kˣ)) := by
    simp only [castW, Pi.smul_apply, smul_eq_mul]
    push_cast
    ring
  rw [hcast, units_pow_val_intCast, zpow_mul, zpow_natCast]

theorem wtChar_nsmul_castW (k : ℕ) (α : Fin 4 → ℤ) (t : Fin 4 → Kˣ) :
    (wtChar ((k : ZMod (Nat.card Kˣ)) • castW (Nat.card Kˣ) α) t : K) =
      ((torusChar α t : Kˣ) : K) ^ k := by
  rw [← Units.val_pow_eq_pow_val]
  exact congrArg ((↑) : Kˣ → K) (wtChar_nsmul_castW_units k α t)

@[expose] def wtSpace (a : Fin 4 → ZMod (Nat.card Kˣ)) : Submodule K X where
  carrier := {x | ∀ t : Fin 4 → Kˣ, ρ (D.h t) x = (wtChar a t : K) • x}
  add_mem' := by
    intro x y hx hy t
    rw [map_add, hx t, hy t, smul_add]
  zero_mem' := by
    intro t
    rw [map_zero, smul_zero]
  smul_mem' := by
    intro c x hx t
    rw [map_smul, hx t, smul_comm]

theorem mem_wtSpace {a : Fin 4 → ZMod (Nat.card Kˣ)} {x : X} :
    x ∈ wtSpace D ρ a ↔ ∀ t : Fin 4 → Kˣ, ρ (D.h t) x = (wtChar a t : K) • x :=
  Iff.rfl

@[expose] noncomputable def wtProj (a : Fin 4 → ZMod (Nat.card Kˣ)) : Module.End K X :=
  ∑ t : Fin 4 → Kˣ, ((wtChar a t)⁻¹ : K) • ρ (D.h t)

theorem wtProj_apply (a : Fin 4 → ZMod (Nat.card Kˣ)) (x : X) :
    wtProj D ρ a x = ∑ t : Fin 4 → Kˣ, ((wtChar a t)⁻¹ : K) • ρ (D.h t) x := by
  rw [wtProj]
  exact LinearMap.sum_apply _ _ x

theorem natCard_units_cast_eq_one : ((Nat.card Kˣ : ℕ) : K) = 1 := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  have hq : ((Nat.card K : ℕ) : K) = 0 := by
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.cast_card_eq_zero K
  have h1 : 1 ≤ Nat.card K := Nat.one_le_iff_ne_zero.mpr Nat.card_pos.ne'
  rw [Nat.card_units, Nat.cast_sub h1, hq, zero_sub, CharTwo.neg_eq, Nat.cast_one]

private theorem prod_ite_eq_one {α : Type*} [DecidableEq α] (f : Fin 4 → α) (z : α) :
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
  letI : Fintype K := Fintype.ofFinite K
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

theorem sum_wtChar (a : Fin 4 → ZMod (Nat.card Kˣ)) :
    (∑ t : Fin 4 → Kˣ, (wtChar a t : K)) = if a = 0 then 1 else 0 := by
  classical
  have hprod : (∑ t : Fin 4 → Kˣ, (wtChar a t : K)) =
      ∏ k, ∑ u : Kˣ, (u : K) ^ (a k).val := by
    rw [← Finset.sum_prod_piFinset (s := (Finset.univ : Finset Kˣ))
      (g := fun k u => (u : K) ^ (a k).val)]
    simp [wtChar_apply]
  have hdvd : ∀ k : Fin 4, Nat.card Kˣ ∣ (a k).val ↔ a k = 0 := by
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

theorem sum_wtChar' (t : Fin 4 → Kˣ) :
    (∑ a : Fin 4 → ZMod (Nat.card Kˣ), (wtChar a t : K)) = if t = 1 then 1 else 0 := by
  classical
  have hprod : (∑ a : Fin 4 → ZMod (Nat.card Kˣ), (wtChar a t : K)) =
      ∏ k, ∑ e : ZMod (Nat.card Kˣ), (t k : K) ^ e.val := by
    rw [← Finset.sum_prod_piFinset (s := (Finset.univ : Finset (ZMod (Nat.card Kˣ))))
      (g := fun k e => (t k : K) ^ e.val)]
    simp [wtChar_apply]
  rw [hprod]
  simp only [sum_zmod_pow_val, prod_ite_eq_one]
  rfl

theorem wtProj_mem (a : Fin 4 → ZMod (Nat.card Kˣ)) (x : X) :
    wtProj D ρ a x ∈ wtSpace D ρ a := by
  rw [mem_wtSpace]
  intro s
  rw [wtProj_apply, map_sum]
  have hterm : ∀ t : Fin 4 → Kˣ, ρ (D.h s) (((wtChar a t)⁻¹ : K) • ρ (D.h t) x) =
      ((wtChar a t)⁻¹ : K) • ρ (D.h (s * t)) x := by
    intro t
    rw [map_smul]
    congr 1
    rw [← Module.End.mul_apply, ← map_mul, map_mul (f := D.h)]
  simp only [hterm]
  have h1 : (∑ t : Fin 4 → Kˣ, ((wtChar a t)⁻¹ : K) • ρ (D.h (s * t)) x) =
      ∑ u : Fin 4 → Kˣ, ((wtChar a (s⁻¹ * u))⁻¹ : K) • ρ (D.h u) x := by
    rw [← Equiv.sum_comp (Equiv.mulLeft s)
      (fun u : Fin 4 → Kˣ => ((wtChar a (s⁻¹ * u))⁻¹ : K) • ρ (D.h u) x)]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Equiv.coe_mulLeft, ← mul_assoc, inv_mul_cancel, one_mul]
  have h2 : ∀ u : Fin 4 → Kˣ, ((wtChar a (s⁻¹ * u))⁻¹ : K) • ρ (D.h u) x =
      (wtChar a s : K) • (((wtChar a u)⁻¹ : K) • ρ (D.h u) x) := by
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

theorem wtProj_of_mem {a b : Fin 4 → ZMod (Nat.card Kˣ)} {x : X}
    (hx : x ∈ wtSpace D ρ b) : wtProj D ρ a x = if a = b then x else 0 := by
  rw [wtProj_apply]
  have hsub : ∀ t : Fin 4 → Kˣ,
      ((wtChar a t)⁻¹ : K) * (wtChar b t : K) = (wtChar (b - a) t : K) := by
    intro t
    rw [wtChar_sub, div_eq_mul_inv, Units.val_mul, Units.val_inv_eq_inv_val]
    ring
  have hterm : ∀ t : Fin 4 → Kˣ, ((wtChar a t)⁻¹ : K) • ρ (D.h t) x =
      (wtChar (b - a) t : K) • x := by
    intro t
    have hxt : ρ (D.h t) x = (wtChar b t : K) • x :=
      (mem_wtSpace (D := D) (ρ := ρ)).mp hx t
    rw [hxt, ← mul_smul, hsub]
  simp only [hterm, ← Finset.sum_smul, sum_wtChar]
  have hcond : b - a = 0 ↔ a = b := by rw [sub_eq_zero, eq_comm]
  by_cases hab : a = b
  · rw [if_pos (hcond.mpr hab), if_pos hab, one_smul]
  · rw [if_neg (fun h => hab (hcond.mp h)), if_neg hab, zero_smul]

theorem sum_wtProj (x : X) :
    (∑ a : Fin 4 → ZMod (Nat.card Kˣ), wtProj D ρ a x) = x := by
  simp only [wtProj_apply]
  rw [Finset.sum_comm]
  have hinner : ∀ t : Fin 4 → Kˣ,
      (∑ a : Fin 4 → ZMod (Nat.card Kˣ), ((wtChar a t)⁻¹ : K)) =
        if t = 1 then 1 else 0 := by
    intro t
    have hneg : (∑ a : Fin 4 → ZMod (Nat.card Kˣ), ((wtChar a t)⁻¹ : K)) =
        ∑ a : Fin 4 → ZMod (Nat.card Kˣ), (wtChar a t : K) := by
      rw [← Equiv.sum_comp (Equiv.neg (Fin 4 → ZMod (Nat.card Kˣ)))
        (fun a => (wtChar a t : K))]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Equiv.neg_apply, wtChar_neg, Units.val_inv_eq_inv_val]
    rw [hneg]
    exact sum_wtChar' t
  simp only [← Finset.sum_smul, hinner]
  rw [Finset.sum_eq_single (1 : Fin 4 → Kˣ)]
  · simp
  · intro t _ ht
    simp [ht]
  · intro h
    exact absurd (Finset.mem_univ (1 : Fin 4 → Kˣ)) h

theorem sum_wtProj_eq_one : (∑ a : Fin 4 → ZMod (Nat.card Kˣ), wtProj D ρ a) = 1 := by
  ext x
  simpa using sum_wtProj D ρ x

theorem wtProj_comm_h (a : Fin 4 → ZMod (Nat.card Kˣ)) (t : Fin 4 → Kˣ) :
    ρ (D.h t) ∘ₗ wtProj D ρ a = wtProj D ρ a ∘ₗ ρ (D.h t) := by
  ext x
  simp only [LinearMap.comp_apply, wtProj_apply, map_sum, map_smul]
  refine Finset.sum_congr rfl fun u _ => ?_
  congr 1
  rw [← Module.End.mul_apply, ← Module.End.mul_apply]
  rw [show ρ (D.h t) * ρ (D.h u) = ρ (D.h u) * ρ (D.h t) from by
    calc ρ (D.h t) * ρ (D.h u) = ρ (D.h t * D.h u) := (map_mul ρ _ _).symm
      _ = ρ (D.h (t * u)) := congrArg (fun z => ρ z) (map_mul D.h t u).symm
      _ = ρ (D.h (u * t)) := by rw [mul_comm t u]
      _ = ρ (D.h u * D.h t) := congrArg (fun z => ρ z) (map_mul D.h u t)
      _ = ρ (D.h u) * ρ (D.h t) := map_mul ρ _ _]

theorem iSup_wtSpace : ⨆ a, wtSpace D ρ a = ⊤ := by
  refine le_antisymm le_top ?_
  intro x _
  rw [show x = ∑ a, wtProj D ρ a x from (sum_wtProj D ρ x).symm]
  exact Submodule.sum_mem _ fun a _ => Submodule.mem_iSup_of_mem a (wtProj_mem D ρ a x)

theorem iSupIndep_wtSpace : iSupIndep (wtSpace D ρ) := by
  rw [iSupIndep_def]
  intro a
  rw [disjoint_iff_inf_le]
  rintro x ⟨hxa, hxsup⟩
  have hker : (⨆ (b) (_ : b ≠ a), wtSpace D ρ b) ≤ LinearMap.ker (wtProj D ρ a) := by
    refine iSup_le fun b => iSup_le fun hb => ?_
    intro y hy
    rw [LinearMap.mem_ker, wtProj_of_mem D ρ hy]
    simp [Ne.symm hb]
  have hx0 : wtProj D ρ a x = 0 := hker hxsup
  have hx1 : wtProj D ρ a x = x := by
    rw [wtProj_of_mem D ρ hxa]
    simp
  have hxeq : x = 0 := by rw [← hx1, hx0]
  rw [hxeq]
  exact Submodule.zero_mem _

theorem finrank_eq_sum_finrank_wtSpace [FiniteDimensional K X] :
    Module.finrank K X = ∑ a, Module.finrank K (wtSpace D ρ a) := by
  have h := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (iSupIndep_wtSpace D ρ) (iSup_wtSpace D ρ)
  rw [← (LinearEquiv.ofBijective (DirectSum.coeLinearMap _) h).finrank_eq,
    Module.finrank_directSum]

theorem mem_iSup_wtSpace_finset {A : Finset (Fin 4 → ZMod (Nat.card Kˣ))} {x : X} :
    x ∈ ⨆ a ∈ A, wtSpace D ρ a ↔ ∀ b ∉ A, wtProj D ρ b x = 0 := by
  constructor
  · intro hx b hb
    have hle : (⨆ a ∈ A, wtSpace D ρ a) ≤ LinearMap.ker (wtProj D ρ b) := by
      refine iSup_le fun a => iSup_le fun ha => ?_
      intro y hy
      rw [LinearMap.mem_ker, wtProj_of_mem D ρ hy]
      simp [show b ≠ a from fun h => hb (h ▸ ha)]
    exact hle hx
  · intro h
    have hsum : (∑ a : Fin 4 → ZMod (Nat.card Kˣ), wtProj D ρ a x) =
        ∑ a ∈ A, wtProj D ρ a x := by
      refine (Finset.sum_subset (Finset.subset_univ A) ?_).symm
      intro b _ hb
      exact h b hb
    rw [← sum_wtProj D ρ x, hsum]
    exact Submodule.sum_mem _ fun a ha =>
      Submodule.mem_iSup_of_mem a (Submodule.mem_iSup_of_mem ha (wtProj_mem D ρ a x))

theorem dotProduct_castW {N : ℕ} (v w : Fin 4 → ℤ) :
    castW N v ⬝ᵥ castW N w = ((v ⬝ᵥ w : ℤ) : ZMod N) := by
  simp only [dotProduct, castW]
  push_cast
  rfl

private theorem prod_fin_four_zpow {M : Type*} [CommGroup M] (x : M) (m : Fin 4 → ℤ) :
    (∏ k, x ^ m k) = x ^ (∑ k, m k) := by
  rw [Fin.prod_univ_four, Fin.sum_univ_four, zpow_add, zpow_add, zpow_add]

theorem reflW_reflW {N : ℕ} (β : Fin 4 → ℤ) (hβ : IsD4Root β)
    (a : Fin 4 → ZMod N) : reflW β (reflW β a) = a := by
  have hβ2 : castW N β ⬝ᵥ castW N β = (2 : ZMod N) := by
    rw [dotProduct_castW, hβ]
    norm_num
  have hdot : (reflW β a) ⬝ᵥ castW N β = -(a ⬝ᵥ castW N β) := by
    rw [reflW, sub_dotProduct, smul_dotProduct, hβ2]
    ring
  calc reflW β (reflW β a)
      = reflW β a - ((reflW β a) ⬝ᵥ castW N β) • castW N β := rfl
    _ = reflW β a - (-(a ⬝ᵥ castW N β)) • castW N β := by rw [hdot]
    _ = (a - (a ⬝ᵥ castW N β) • castW N β) - (-(a ⬝ᵥ castW N β)) • castW N β := rfl
    _ = a := by rw [neg_smul, sub_neg_eq_add, sub_add_cancel]

private theorem zpow_mul_neg_two {M : Type*} [CommGroup M] (c : M) : c * c ^ (-2 : ℤ) = c⁻¹ := by
  calc c * c ^ (-2 : ℤ) = c ^ (1 : ℤ) * c ^ (-2 : ℤ) := by rw [zpow_one]
    _ = c ^ ((1 : ℤ) + (-2 : ℤ)) := by rw [← zpow_add]
    _ = c ^ (-1 : ℤ) := by norm_num
    _ = c⁻¹ := zpow_neg_one c

theorem torusChar_reflTorus {M : Type*} [CommGroup M] (β : Fin 4 → ℤ) (hβ : IsD4Root β)
    (t : Fin 4 → M) : torusChar β (reflTorus β t) = (torusChar β t)⁻¹ := by
  have hβ2 : (∑ k : Fin 4, β k * β k) = 2 := by
    rw [← dotProduct]
    exact hβ
  have hterm : ∀ k : Fin 4, (reflTorus β t k) ^ β k =
      t k ^ β k * (torusChar β t) ^ (-β k * β k) := by
    intro k
    rw [reflTorus, mul_zpow, ← zpow_mul]
  rw [torusChar_apply, Finset.prod_congr rfl fun k _ => hterm k, Finset.prod_mul_distrib,
    prod_fin_four_zpow]
  have hsum : (∑ k : Fin 4, -β k * β k) = -2 := by
    rw [← hβ2, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hsum, ← torusChar_apply]
  exact zpow_mul_neg_two (torusChar β t)

theorem reflTorus_reflTorus {M : Type*} [CommGroup M] (β : Fin 4 → ℤ) (hβ : IsD4Root β)
    (t : Fin 4 → M) : reflTorus β (reflTorus β t) = t := by
  funext k
  rw [reflTorus, torusChar_reflTorus β hβ, reflTorus, inv_zpow', neg_neg, mul_assoc,
    ← zpow_add, neg_add_cancel, zpow_zero, mul_one]

theorem wtChar_reflTorus (β : Fin 4 → ℤ) (hβ : IsD4Root β)
    (a : Fin 4 → ZMod (Nat.card Kˣ)) (t : Fin 4 → Kˣ) :
    wtChar a (reflTorus β t) = wtChar (reflW β a) t := by
  set e : Fin 4 → ℤ := fun k => ((a k).val : ℤ) with he
  set S : ℤ := ∑ k, e k * β k with hS
  have ha : a = castW (Nat.card Kˣ) (fun k => e k) := by
    funext k
    simp only [castW, he, Int.cast_natCast, ZMod.natCast_zmod_val]
  have hdot : a ⬝ᵥ castW (Nat.card Kˣ) β = (S : ZMod (Nat.card Kˣ)) := by
    rw [ha, dotProduct_castW, hS]
    rfl
  have hreflW : ∀ k, reflW β a k = ((e k - S * β k : ℤ) : ZMod (Nat.card Kˣ)) := by
    intro k
    rw [reflW, hdot]
    simp only [ha, castW, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    ring
  have hprod : (∏ k : Fin 4, (torusChar β t) ^ (-β k * e k)) =
      (torusChar β t) ^ (-S) := by
    rw [prod_fin_four_zpow, hS, ← Finset.sum_neg_distrib]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by ring
  have hL : wtChar a (reflTorus β t) = wtChar a t * (torusChar β t) ^ (-S) := by
    rw [wtChar_apply]
    have hterm : ∀ k, (reflTorus β t k) ^ (a k).val =
        t k ^ (a k).val * (torusChar β t) ^ (-β k * e k) := by
      intro k
      rw [reflTorus, mul_pow]
      simp only [← zpow_natCast, ← zpow_mul]
      congr 1
    rw [Finset.prod_congr rfl fun k _ => hterm k, Finset.prod_mul_distrib, hprod]
    rw [← wtChar_apply]
  have hprod2 : (∏ k : Fin 4, t k ^ (-S * β k)) = (torusChar β t) ^ (-S) := by
    rw [torusChar_apply, ← Finset.prod_zpow]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← zpow_mul]
    congr 1
    ring
  have hR : wtChar (reflW β a) t = wtChar a t * (torusChar β t) ^ (-S) := by
    rw [wtChar_apply]
    have hterm : ∀ k, t k ^ ((reflW β a k).val) =
        t k ^ (e k) * t k ^ (-S * β k) := by
      intro k
      rw [hreflW k, units_pow_val_intCast,
        show e k - S * β k = e k + (-S * β k) from by ring, zpow_add, zpow_natCast]
    rw [Finset.prod_congr rfl fun k _ => hterm k, Finset.prod_mul_distrib, hprod2]
    congr 1
  rw [hL, hR]

theorem map_mul_wtSpace (β : Fin 4 → ℤ) (hβ : IsD4Root β) (m : G)
    (hm : ∀ t : Fin 4 → Kˣ, m⁻¹ * D.h t * m = D.h (reflTorus β t))
    (a : Fin 4 → ZMod (Nat.card Kˣ)) :
    (wtSpace D ρ a).map (ρ m) ≤ wtSpace D ρ (reflW β a) := by
  rintro _ ⟨x, hx, rfl⟩
  have hx' := (mem_wtSpace (D := D) (ρ := ρ)).mp hx
  change ∀ t : Fin 4 → Kˣ, ρ (D.h t) (ρ m x) = (wtChar (reflW β a) t : K) • ρ m x
  intro t
  have hconj : ρ m⁻¹ * ρ (D.h t) * ρ m = ρ (D.h (reflTorus β t)) := by
    rw [← map_mul, ← map_mul]
    exact congrArg ρ (hm t)
  have h1 : ρ m⁻¹ (ρ (D.h t) (ρ m x)) = (wtChar a (reflTorus β t) : K) • x := by
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, hconj, hx' (reflTorus β t)]
  have hcancel : ∀ v : X, ρ m (ρ m⁻¹ v) = v := by
    intro v
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  calc ρ (D.h t) (ρ m x)
      = ρ m (ρ m⁻¹ (ρ (D.h t) (ρ m x))) := (hcancel _).symm
    _ = ρ m ((wtChar a (reflTorus β t) : K) • x) := by rw [h1]
    _ = (wtChar a (reflTorus β t) : K) • ρ m x := by rw [map_smul]
    _ = (wtChar (reflW β a) t : K) • ρ m x := by rw [wtChar_reflTorus β hβ a t]

theorem map_n_wtSpace (β : Fin 4 → ℤ) (hβ : IsD4Root β)
    (a : Fin 4 → ZMod (Nat.card Kˣ)) :
    (wtSpace D ρ a).map (ρ (D.n β)) = wtSpace D ρ (reflW β a) := by
  have hm₁ : ∀ t : Fin 4 → Kˣ, (D.n β)⁻¹ * D.h t * D.n β = D.h (reflTorus β t) := by
    intro t
    have h := D.n_conj (β := β) hβ (reflTorus β t)
    rw [reflTorus_reflTorus β hβ t] at h
    calc (D.n β)⁻¹ * D.h t * D.n β
        = (D.n β)⁻¹ * (D.n β * D.h (reflTorus β t) * (D.n β)⁻¹) * D.n β := by
          rw [← h]
      _ = D.h (reflTorus β t) := by group
  have hm₂ : ∀ t : Fin 4 → Kˣ, ((D.n β)⁻¹)⁻¹ * D.h t * (D.n β)⁻¹ = D.h (reflTorus β t) := by
    intro t
    rw [inv_inv]
    exact D.n_conj (β := β) hβ t
  refine le_antisymm (map_mul_wtSpace D ρ β hβ (D.n β) hm₁ a) ?_
  intro y hy
  have hy' : ρ (D.n β)⁻¹ y ∈ wtSpace D ρ a := by
    have h := map_mul_wtSpace D ρ β hβ ((D.n β)⁻¹) hm₂ (reflW β a) ⟨y, hy, rfl⟩
    rwa [reflW_reflW β hβ a] at h
  exact ⟨ρ (D.n β)⁻¹ y, hy', by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]⟩

theorem finrank_wtSpace_reflW [FiniteDimensional K X] (β : Fin 4 → ℤ) (hβ : IsD4Root β)
    (a : Fin 4 → ZMod (Nat.card Kˣ)) :
    Module.finrank K (wtSpace D ρ (reflW β a)) = Module.finrank K (wtSpace D ρ a) := by
  rw [← map_n_wtSpace D ρ β hβ a]
  exact LinearEquiv.finrank_map_eq
    (LinearEquiv.ofBijective (ρ (D.n β)) (ρ.apply_bijective (D.n β))) (wtSpace D ρ a)

@[expose] noncomputable def rootCoeff (k : ℕ) (d : K) : K :=
  if k = 0 then (if d = 0 then 1 else 0)
  else if k < Nat.card Kˣ then (if d = 0 then 0 else (d ^ k)⁻¹)
  else if k = Nat.card Kˣ then 1 else 0

@[expose] noncomputable def rootOp (α : Fin 4 → ℤ) (k : ℕ) : Module.End K X :=
  ∑ d : K, rootCoeff k d • ρ (D.x α d)

theorem rootOp_apply (α : Fin 4 → ℤ) (k : ℕ) (x : X) :
    rootOp D ρ α k x = ∑ d : K, rootCoeff k d • ρ (D.x α d) x := by
  rw [rootOp]
  exact LinearMap.sum_apply _ _ x

theorem rootCoeff_zero (d : K) : rootCoeff 0 d = if d = 0 then 1 else 0 := by
  simp [rootCoeff]

theorem rootCoeff_of_pos_of_lt {k : ℕ} (hk0 : 0 < k) (hkN : k < Nat.card Kˣ) (d : K) :
    rootCoeff k d = if d = 0 then 0 else (d ^ k)⁻¹ := by
  rw [rootCoeff, if_neg hk0.ne', if_pos hkN]

theorem rootCoeff_card (d : K) : rootCoeff (Nat.card Kˣ) d = 1 := by
  have hN : Nat.card Kˣ ≠ 0 := Nat.card_pos.ne'
  rw [rootCoeff, if_neg hN, if_neg (lt_irrefl (Nat.card Kˣ)), if_pos rfl]

theorem rootCoeff_of_lt {k : ℕ} (hk : Nat.card Kˣ < k) (d : K) : rootCoeff k d = 0 := by
  have hN : Nat.card Kˣ ≠ 0 := Nat.card_pos.ne'
  have hk0 : k ≠ 0 := by omega
  have hnk : ¬ k < Nat.card Kˣ := by omega
  have hne : k ≠ Nat.card Kˣ := by omega
  rw [rootCoeff, if_neg hk0, if_neg hnk, if_neg hne]

private theorem sum_K_eq_zero_add {M : Type*} [AddCommMonoid M] (f : K → M) :
    (∑ d : K, f d) = f 0 + ∑ u : Kˣ, f (u : K) := by
  classical
  rw [← Finset.add_sum_erase (Finset.univ : Finset K) f (Finset.mem_univ 0)]
  congr 1
  refine Finset.sum_bij (fun d hd => Units.mk0 d (Finset.ne_of_mem_erase hd)) ?_ ?_ ?_ ?_
  · intro d _
    exact Finset.mem_univ _
  · intro d₁ h₁ d₂ h₂ hd
    simpa using congrArg Units.val hd
  · intro u _
    exact ⟨(u : K), Finset.mem_erase.mpr ⟨u.ne_zero, Finset.mem_univ _⟩, Units.ext rfl⟩
  · intro d _
    rfl

private theorem sum_units_zpow (n : ℤ) :
    (∑ u : Kˣ, (u : K) ^ n) = if (Nat.card Kˣ : ℤ) ∣ n then 1 else 0 := by
  rcases le_or_gt 0 n with hn | hn
  · have hn' : n = (n.toNat : ℤ) := (Int.toNat_of_nonneg hn).symm
    rw [hn']
    simp only [zpow_natCast, sum_units_pow, Int.natCast_dvd_natCast]
  · have hm : 0 ≤ -n := by omega
    set m : ℕ := (-n).toNat with hmdef
    have hn' : n = -(m : ℤ) := by
      rw [hmdef, Int.toNat_of_nonneg hm]
      omega
    have h1 : (∑ u : Kˣ, (u : K) ^ n) = ∑ u : Kˣ, (u : K) ^ m := by
      rw [hn']
      simp only [zpow_neg, zpow_natCast]
      refine Fintype.sum_bijective (fun u : Kˣ => u⁻¹)
        ⟨fun a b h => ?_, fun b => ⟨b⁻¹, by simp⟩⟩
        (fun u : Kˣ => ((u : K) ^ m)⁻¹) (fun u : Kˣ => (u : K) ^ m) fun u => ?_
      · simpa using congrArg Inv.inv h
      · rw [Units.val_inv_eq_inv_val, inv_pow]
    have hiff : ((Nat.card Kˣ : ℤ) ∣ n) ↔ Nat.card Kˣ ∣ m := by
      rw [hn', Int.dvd_neg, Int.natCast_dvd_natCast]
    rw [h1, sum_units_pow]
    by_cases h : Nat.card Kˣ ∣ m
    · rw [if_pos h, if_pos (hiff.mpr h)]
    · rw [if_neg h, if_neg (fun hh => h (hiff.mp hh))]

private theorem rootCoeff_sum_mul_zero {m : ℕ} (hm : m ≤ Nat.card Kˣ) :
    (∑ d : K, rootCoeff 0 d * d ^ m) = if 0 = m then 1 else 0 := by
  rw [Finset.sum_eq_single (0 : K)]
  · rw [rootCoeff_zero, if_pos rfl, one_mul]
    by_cases hm0 : m = 0
    · subst hm0
      simp
    · rw [zero_pow hm0, if_neg (Ne.symm hm0)]
  · intro d _ hd
    rw [rootCoeff_zero, if_neg hd, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ (0 : K)) h

private theorem rootCoeff_sum_mul_card {m : ℕ} (hm : m ≤ Nat.card Kˣ) :
    (∑ d : K, rootCoeff (Nat.card Kˣ) d * d ^ m) =
      if Nat.card Kˣ = m then 1 else 0 := by
  rw [sum_K_eq_zero_add]
  have h0 : rootCoeff (Nat.card Kˣ) (0 : K) * (0 : K) ^ m = if m = 0 then 1 else 0 := by
    rw [rootCoeff_card, one_mul]
    by_cases hm0 : m = 0
    · subst hm0
      simp
    · rw [zero_pow hm0, if_neg hm0]
  rw [h0]
  have h1 : ∀ u : Kˣ, rootCoeff (Nat.card Kˣ) (u : K) * (u : K) ^ m = (u : K) ^ m := by
    intro u
    rw [rootCoeff_card, one_mul]
  simp only [h1]
  rw [sum_units_pow]
  have hN : Nat.card Kˣ ≠ 0 := Nat.card_pos.ne'
  by_cases hm0 : m = 0
  · subst hm0
    rw [if_pos rfl, if_pos (dvd_zero _), if_neg hN]
    exact CharTwo.add_self_eq_zero 1
  · have hdvd : Nat.card Kˣ ∣ m ↔ m = Nat.card Kˣ := by
      constructor
      · intro hd
        exact Nat.le_antisymm hm (Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) hd)
      · intro h
        rw [h]
    rw [if_neg hm0]
    by_cases h : Nat.card Kˣ ∣ m
    · rw [if_pos h, if_pos (hdvd.mp h).symm, zero_add]
    · rw [if_neg h, if_neg (fun hnm => h (hdvd.mpr hnm.symm)), zero_add]

private theorem rootCoeff_sum_mul_pos {k m : ℕ} (hk0 : 0 < k) (hkN : k < Nat.card Kˣ)
    (hm : m ≤ Nat.card Kˣ) :
    (∑ d : K, rootCoeff k d * d ^ m) = if k = m then 1 else 0 := by
  rw [sum_K_eq_zero_add]
  have h0 : rootCoeff k (0 : K) * (0 : K) ^ m = 0 := by
    rw [rootCoeff_of_pos_of_lt hk0 hkN, if_pos rfl, zero_mul]
  rw [h0, zero_add]
  have hterm : ∀ u : Kˣ, rootCoeff k (u : K) * (u : K) ^ m =
      ((u ^ ((m : ℤ) - k) : Kˣ) : K) := by
    intro u
    rw [rootCoeff_of_pos_of_lt hk0 hkN, if_neg (by exact u.ne_zero)]
    rw [Units.val_zpow_eq_zpow_val, zpow_sub₀ (by exact u.ne_zero), div_eq_mul_inv,
      mul_comm]
    simp only [zpow_natCast]
  rw [Finset.sum_congr rfl fun u _ => hterm u]
  simp only [Units.val_zpow_eq_zpow_val]
  rw [sum_units_zpow]
  have hiff : ((Nat.card Kˣ : ℤ) ∣ ((m : ℤ) - k)) ↔ k = m := by
    by_cases hkm : k ≤ m
    · have h1 : (m : ℤ) - k = ((m - k : ℕ) : ℤ) := by omega
      rw [h1, Int.natCast_dvd_natCast]
      constructor
      · intro hd
        rcases Nat.eq_zero_or_pos (m - k) with h2 | h2
        · omega
        · exact absurd (Nat.le_of_dvd h2 hd) (by omega)
      · intro h
        subst h
        simp
    · have hkm' : m < k := by omega
      have h1 : (m : ℤ) - k = -((k - m : ℕ) : ℤ) := by omega
      rw [h1, Int.dvd_neg, Int.natCast_dvd_natCast]
      constructor
      · intro hd
        exact absurd (Nat.le_of_dvd (by omega : 0 < k - m) hd) (by omega)
      · intro h
        omega
  by_cases hkm : k = m
  · rw [if_pos (hiff.mpr hkm), if_pos hkm]
  · rw [if_neg (fun h => hkm (hiff.mp h)), if_neg hkm]

theorem rootCoeff_sum_mul {k m : ℕ} (hk : k ≤ Nat.card Kˣ) (hm : m ≤ Nat.card Kˣ) :
    (∑ d : K, rootCoeff k d * d ^ m) = if k = m then 1 else 0 := by
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · exact rootCoeff_sum_mul_zero hm
  · rcases eq_or_lt_of_le hk with hk' | hk'
    · obtain rfl : k = Nat.card Kˣ := hk'
      exact rootCoeff_sum_mul_card hm
    · exact rootCoeff_sum_mul_pos hkpos hk' hm

private theorem sum_range_pow_succ (u : K) :
    (∑ k ∈ Finset.range (Nat.card Kˣ), u ^ (k + 1)) = if u = 1 then 1 else 0 := by
  have hN : Nat.card Kˣ ≠ 0 := Nat.card_pos.ne'
  by_cases hu : u = 0
  · rw [if_neg (by rw [hu]; exact zero_ne_one), hu]
    simp
  · have huN : u ^ Nat.card Kˣ = 1 := by
      have h := congrArg ((↑) : Kˣ → K) (pow_card_eq_one' (x := Units.mk0 u hu))
      rwa [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one] at h
    have hgeom : (∑ k ∈ Finset.range (Nat.card Kˣ), u ^ k) * (u - 1) = 0 := by
      rw [geom_sum_mul, huN, sub_self]
    rw [show (∑ k ∈ Finset.range (Nat.card Kˣ), u ^ (k + 1)) =
        u * ∑ k ∈ Finset.range (Nat.card Kˣ), u ^ k from by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by rw [pow_succ']]
    by_cases hu1 : u = 1
    · subst hu1
      rw [if_pos rfl, one_mul]
      rw [Finset.sum_congr rfl fun k _ => one_pow k, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul, mul_one]
      exact natCard_units_cast_eq_one
    · rw [if_neg hu1]
      rcases mul_eq_zero.mp hgeom with h | h
      · rw [h, mul_zero]
      · exact absurd (sub_eq_zero.mp h) hu1

private theorem sum_range_rootCoeff_zero (c : K) :
    (∑ k ∈ Finset.range (Nat.card Kˣ),
      c ^ (k + 1) * rootCoeff (k + 1) (0 : K)) = c ^ Nat.card Kˣ := by
  have hN : Nat.card Kˣ ≠ 0 := Nat.card_pos.ne'
  conv_lhs => rw [show Nat.card Kˣ = (Nat.card Kˣ - 1) + 1 from
    (Nat.sub_one_add_one hN).symm]
  rw [Finset.sum_range_succ]
  have hlast : c ^ (Nat.card Kˣ - 1 + 1) * rootCoeff (Nat.card Kˣ - 1 + 1) (0 : K) =
      c ^ Nat.card Kˣ := by
    rw [Nat.sub_one_add_one hN, rootCoeff_card, mul_one]
  rw [hlast]
  have hzero : (∑ k ∈ Finset.range (Nat.card Kˣ - 1),
      c ^ (k + 1) * rootCoeff (k + 1) (0 : K)) = 0 := by
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [rootCoeff_of_pos_of_lt (Nat.succ_pos k) (by
      have := Finset.mem_range.mp hk
      omega), if_pos rfl, mul_zero]
  rw [hzero, zero_add]

private theorem rootOp_interpolation_zero (c : K) :
    (∑ j ∈ Finset.range (Nat.card Kˣ + 1), c ^ j * rootCoeff j (0 : K)) =
      if c = 0 then 1 else 0 := by
  have hN : Nat.card Kˣ ≠ 0 := Nat.card_pos.ne'
  rw [Finset.sum_range_succ']
  have h0 : c ^ 0 * rootCoeff 0 (0 : K) = 1 := by
    rw [rootCoeff_zero, if_pos rfl, mul_one, pow_zero]
  rw [sum_range_rootCoeff_zero, h0]
  by_cases hc : c = 0
  · subst hc
    rw [zero_pow hN, zero_add, if_pos rfl]
  · rw [if_neg hc]
    have hcN : c ^ Nat.card Kˣ = 1 := by
      have h := congrArg ((↑) : Kˣ → K) (pow_card_eq_one' (x := Units.mk0 c hc))
      rwa [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one] at h
    rw [hcN]
    exact CharTwo.add_self_eq_zero 1

private theorem rootCoeff_pow_of_ne_zero {c d : K} (hd : d ≠ 0) {j : ℕ}
    (hj1 : 1 ≤ j) (hjN : j ≤ Nat.card Kˣ) :
    c ^ j * rootCoeff j d = (c * d⁻¹) ^ j := by
  rcases eq_or_lt_of_le hjN with hj | hj
  · rw [hj, rootCoeff_card, mul_one, mul_pow, inv_pow,
      show d ^ Nat.card Kˣ = 1 from by
        have h := congrArg ((↑) : Kˣ → K) (pow_card_eq_one' (x := Units.mk0 d hd))
        rwa [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one] at h,
      inv_one, mul_one]
  · rw [rootCoeff_of_pos_of_lt (by omega) hj, if_neg hd, ← inv_pow, ← mul_pow]

private theorem rootOp_interpolation_ne_zero {c d : K} (hd : d ≠ 0) :
    (∑ j ∈ Finset.range (Nat.card Kˣ + 1), c ^ j * rootCoeff j d) =
      if c = d then 1 else 0 := by
  have huval : c * d⁻¹ = 1 ↔ c = d := by
    constructor
    · intro h
      calc c = c * d⁻¹ * d := by rw [mul_assoc, inv_mul_cancel₀ hd, mul_one]
        _ = 1 * d := by rw [h]
        _ = d := one_mul d
    · intro h
      rw [h, mul_inv_cancel₀ hd]
  have hsum : (∑ j ∈ Finset.range (Nat.card Kˣ + 1), c ^ j * rootCoeff j d) =
      ∑ k ∈ Finset.range (Nat.card Kˣ), (c * d⁻¹) ^ (k + 1) := by
    rw [Finset.sum_range_succ']
    have h0 : c ^ 0 * rootCoeff 0 d = 0 := by
      rw [rootCoeff_zero, if_neg hd, mul_zero]
    rw [h0]
    simp only [zero_add, add_zero]
    exact Finset.sum_congr rfl fun k hk =>
      rootCoeff_pow_of_ne_zero hd (Nat.succ_pos k)
        (Nat.succ_le_of_lt (Finset.mem_range.mp hk))
  rw [hsum, sum_range_pow_succ]
  by_cases hcd : c = d
  · rw [if_pos hcd, if_pos (huval.mpr hcd)]
  · rw [if_neg hcd, if_neg (fun h => hcd (huval.mp h))]

theorem rootOp_interpolation (c d : K) :
    (∑ j ∈ Finset.range (Nat.card Kˣ + 1), c ^ j * rootCoeff j d) =
      if c = d then 1 else 0 := by
  by_cases hd : d = 0
  · subst hd
    exact rootOp_interpolation_zero c
  · exact rootOp_interpolation_ne_zero hd

theorem rho_x_eq_sum (α : Fin 4 → ℤ) (hα : IsD4Root α) (c : K) :
    ρ (D.x α c) = ∑ k ∈ Finset.range (Nat.card Kˣ + 1), c ^ k • rootOp D ρ α k := by
  ext x
  rw [LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, rootOp_apply, Finset.smul_sum]
  rw [Finset.sum_comm]
  have hinner : ∀ d : K, (∑ k ∈ Finset.range (Nat.card Kˣ + 1),
      c ^ k • (rootCoeff k d • ρ (D.x α d) x)) =
      (if c = d then (1 : K) else 0) • ρ (D.x α d) x := by
    intro d
    rw [show (∑ k ∈ Finset.range (Nat.card Kˣ + 1),
        c ^ k • (rootCoeff k d • ρ (D.x α d) x)) =
        ∑ k ∈ Finset.range (Nat.card Kˣ + 1),
          (c ^ k * rootCoeff k d) • ρ (D.x α d) x from
      Finset.sum_congr rfl fun k _ => (mul_smul _ _ _).symm]
    have h := rootOp_interpolation (K := K) c d
    rw [← Finset.sum_smul]
    exact congrArg (fun z : K => z • ρ (D.x α d) x) h
  simp only [hinner]
  rw [Finset.sum_eq_single c]
  · rw [if_pos rfl, one_smul]
  · intro d _ hd
    rw [if_neg (Ne.symm hd), zero_smul]
  · intro h
    exact absurd (Finset.mem_univ c) h

theorem rootOp_zero (α : Fin 4 → ℤ) (hα : IsD4Root α) : rootOp D ρ α 0 = 1 := by
  ext x
  rw [rootOp_apply, Finset.sum_eq_single (0 : K)]
  · rw [rootCoeff_zero, if_pos rfl, one_smul, D.x_zero hα, map_one, Module.End.one_apply]
  · intro d _ hd
    rw [rootCoeff_zero, if_neg hd, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ (0 : K)) h

theorem rootOp_of_lt (α : Fin 4 → ℤ) {k : ℕ} (hk : Nat.card Kˣ < k) :
    rootOp D ρ α k = 0 := by
  ext x
  rw [rootOp_apply]
  simp only [rootCoeff_of_lt hk, zero_smul, Finset.sum_const_zero, LinearMap.zero_apply]

theorem rootCoeff_inv_mul (k : ℕ) {lam : K} (hlam : lam ≠ 0) (d : K) :
    rootCoeff k (lam⁻¹ * d) = lam ^ k * rootCoeff k d := by
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · rw [rootCoeff_zero, rootCoeff_zero, pow_zero, one_mul]
    by_cases hd : d = 0
    · rw [hd, mul_zero, if_pos rfl]
    · rw [if_neg hd, if_neg (mul_ne_zero (inv_ne_zero hlam) hd)]
  · rcases lt_or_ge k (Nat.card Kˣ) with hkN | hkN
    · rw [rootCoeff_of_pos_of_lt hkpos hkN, rootCoeff_of_pos_of_lt hkpos hkN]
      by_cases hd : d = 0
      · rw [hd, mul_zero, if_pos rfl, mul_zero]
      · rw [if_neg (mul_ne_zero (inv_ne_zero hlam) hd), if_neg hd, mul_pow, mul_inv_rev,
          inv_pow, inv_inv, mul_comm]
    · rcases eq_or_lt_of_le hkN with hk | hk
      · rw [← hk, rootCoeff_card, rootCoeff_card,
          show lam ^ Nat.card Kˣ = 1 from by
            have h := congrArg ((↑) : Kˣ → K) (pow_card_eq_one' (x := Units.mk0 lam hlam))
            rwa [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one] at h,
          one_mul]
      · rw [rootCoeff_of_lt hk, rootCoeff_of_lt hk, mul_zero]

theorem rootOp_conj (α : Fin 4 → ℤ) (hα : IsD4Root α) (t : Fin 4 → Kˣ) (k : ℕ) :
    ρ (D.h t) * rootOp D ρ α k =
      (((torusChar α t : Kˣ) : K)) ^ k • (rootOp D ρ α k * ρ (D.h t)) := by
  set lam : K := ((torusChar α t : Kˣ) : K) with hlamdef
  have hlam : lam ≠ 0 := by
    rw [hlamdef]
    exact_mod_cast (torusChar α t).ne_zero
  ext x
  rw [Module.End.mul_apply, LinearMap.smul_apply, Module.End.mul_apply, rootOp_apply,
    rootOp_apply, map_sum]
  have hterm : ∀ d : K, ρ (D.h t) (rootCoeff k d • ρ (D.x α d) x) =
      rootCoeff k d • ρ (D.x α (lam * d)) (ρ (D.h t) x) := by
    intro d
    rw [map_smul]
    congr 1
    rw [← Module.End.mul_apply, ← Module.End.mul_apply]
    rw [show ρ (D.h t) * ρ (D.x α d) = ρ (D.x α (lam * d)) * ρ (D.h t) from by
      rw [← map_mul, ← map_mul]
      congr 1
      have h := D.h_conj α hα t d
      calc D.h t * D.x α d = D.h t * D.x α d * (D.h t)⁻¹ * D.h t := by group
        _ = D.x α (lam * d) * D.h t := by rw [h]]
  rw [Finset.sum_congr rfl fun d _ => hterm d]
  have hreindex : (∑ d : K, rootCoeff k d • ρ (D.x α (lam * d)) (ρ (D.h t) x)) =
      ∑ d : K, rootCoeff k (lam⁻¹ * d) • ρ (D.x α d) (ρ (D.h t) x) := by
    refine Fintype.sum_bijective (fun d : K => lam * d) ⟨?_, ?_⟩ _ _ ?_
    · intro a b hab
      exact mul_left_cancel₀ hlam hab
    · intro b
      exact ⟨lam⁻¹ * b, by
        show lam * (lam⁻¹ * b) = b
        rw [← mul_assoc, mul_inv_cancel₀ hlam, one_mul]⟩
    · intro d
      congr 2
      show d = lam⁻¹ * (lam * d)
      rw [← mul_assoc, inv_mul_cancel₀ hlam, one_mul]
  rw [hreindex]
  have hhom : ∀ d : K, rootCoeff k (lam⁻¹ * d) • ρ (D.x α d) (ρ (D.h t) x) =
      lam ^ k • (rootCoeff k d • ρ (D.x α d) (ρ (D.h t) x)) := by
    intro d
    rw [rootCoeff_inv_mul k hlam, mul_smul]
  simp only [hhom, Finset.smul_sum]

theorem rootOp_mem_wtSpace (α : Fin 4 → ℤ) (hα : IsD4Root α)
    (a : Fin 4 → ZMod (Nat.card Kˣ)) {x : X} (hx : x ∈ wtSpace D ρ a) (k : ℕ) :
    rootOp D ρ α k x ∈ wtSpace D ρ (a + (k : ZMod (Nat.card Kˣ)) • castW (Nat.card Kˣ) α) := by
  rw [mem_wtSpace] at hx ⊢
  intro t
  have h := congrArg (fun f : Module.End K X => f x) (rootOp_conj D ρ α hα t k)
  simp only [Module.End.mul_apply, LinearMap.smul_apply] at h
  rw [h, hx t, map_smul, smul_smul, wtChar_add, Units.val_mul, wtChar_nsmul_castW,
    mul_comm]

private theorem rootCoeff_sum_mul' {i r : ℕ} (hr : r ≤ Nat.card Kˣ) :
    (∑ c : K, rootCoeff i c * c ^ r) = if i = r then 1 else 0 := by
  by_cases hi : i ≤ Nat.card Kˣ
  · exact rootCoeff_sum_mul hi hr
  · have hir : i ≠ r := by omega
    rw [if_neg hir]
    exact Finset.sum_eq_zero fun c _ => by rw [rootCoeff_of_lt (by omega), zero_mul]

private theorem rootCoeff_mul_binomial_expand {i j k : ℕ} :
    (∑ c : K, ∑ d : K, rootCoeff i c * rootCoeff j d * (c + d) ^ k) =
      ∑ r ∈ Finset.range (k + 1), (k.choose r : K) *
        (∑ c : K, rootCoeff i c * c ^ r) *
        (∑ d : K, rootCoeff j d * d ^ (k - r)) := by
  calc (∑ c : K, ∑ d : K, rootCoeff i c * rootCoeff j d * (c + d) ^ k)
      = ∑ c : K, ∑ d : K, ∑ r ∈ Finset.range (k + 1),
          (rootCoeff i c * c ^ r) * (rootCoeff j d * d ^ (k - r)) *
            (k.choose r : K) := by
        refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
        rw [add_pow, Finset.mul_sum]
        refine Finset.sum_congr rfl fun r _ => ?_
        ring
    _ = ∑ r ∈ Finset.range (k + 1), ∑ c : K, ∑ d : K,
          (rootCoeff i c * c ^ r) * (rootCoeff j d * d ^ (k - r)) *
            (k.choose r : K) := by
        rw [Finset.sum_congr rfl fun c _ => Finset.sum_comm]
        rw [Finset.sum_comm]
    _ = ∑ r ∈ Finset.range (k + 1), (k.choose r : K) *
          (∑ c : K, rootCoeff i c * c ^ r) *
          (∑ d : K, rootCoeff j d * d ^ (k - r)) := by
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun d _ => by ring

private theorem rootCoeff_mul_binomial_sum {i j k : ℕ} (hk : k ≤ Nat.card Kˣ) :
    (∑ r ∈ Finset.range (k + 1), (k.choose r : K) *
        (∑ c : K, rootCoeff i c * c ^ r) *
        (∑ d : K, rootCoeff j d * d ^ (k - r))) =
      if k = i + j then ((k.choose i : ℕ) : K) else 0 := by
  have hsum : ∀ r ∈ Finset.range (k + 1),
      (k.choose r : K) * (∑ c : K, rootCoeff i c * c ^ r) *
          (∑ d : K, rootCoeff j d * d ^ (k - r)) =
      (k.choose r : K) * (if i = r then 1 else 0) * (if j = k - r then 1 else 0) := by
    intro r hr
    have hrk : r ≤ k := by
      have := Finset.mem_range.mp hr
      omega
    rw [rootCoeff_sum_mul' (by omega : r ≤ Nat.card Kˣ),
      rootCoeff_sum_mul' (by omega : k - r ≤ Nat.card Kˣ)]
  rw [Finset.sum_congr rfl hsum]
  by_cases h : k = i + j
  · rw [if_pos h]
    have hi : i ∈ Finset.range (k + 1) := Finset.mem_range.mpr (by omega)
    rw [Finset.sum_eq_single i]
    · rw [if_pos rfl, if_pos (by omega : j = k - i)]
      ring
    · intro r _ hr
      rw [if_neg (fun hri : i = r => hr hri.symm)]
      ring
    · intro hnot
      exact absurd hi hnot
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun r hr => ?_
    by_cases hri : i = r
    · have hrk : r ≤ k := by
        have := Finset.mem_range.mp hr
        omega
      rw [if_pos hri]
      rw [if_neg (fun hjk : j = k - r => h (by omega))]
      ring
    · rw [if_neg hri]
      ring

private theorem rootCoeff_mul_binomial {i j k : ℕ} (hk : k ≤ Nat.card Kˣ) :
    (∑ c : K, ∑ d : K, rootCoeff i c * rootCoeff j d * (c + d) ^ k) =
      if k = i + j then ((k.choose i : ℕ) : K) else 0 :=
  (rootCoeff_mul_binomial_expand).trans (rootCoeff_mul_binomial_sum hk)

private theorem rootOp_mul_expand (α : Fin 4 → ℤ) (hα : IsD4Root α) (i j : ℕ) (x : X) :
    (rootOp D ρ α i * rootOp D ρ α j) x =
      ∑ c : K, ∑ d : K,
        (rootCoeff i c * rootCoeff j d) • ρ (D.x α (c + d)) x := by
  rw [Module.End.mul_apply]
  simp only [rootOp_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [map_smul, smul_smul, ← Module.End.mul_apply, ← map_mul, ← D.x_add α hα c d]

private theorem rootOp_mul_expand' (α : Fin 4 → ℤ) (hα : IsD4Root α) (i j : ℕ) (x : X) :
    (∑ c : K, ∑ d : K, (rootCoeff i c * rootCoeff j d) • ρ (D.x α (c + d)) x) =
      ∑ k ∈ Finset.range (Nat.card Kˣ + 1),
        (∑ c : K, ∑ d : K, rootCoeff i c * rootCoeff j d * (c + d) ^ k) •
          rootOp D ρ α k x := by
  have hpoint : ∀ c : K, ρ (D.x α c) x =
      ∑ k ∈ Finset.range (Nat.card Kˣ + 1), c ^ k • rootOp D ρ α k x := by
    intro c
    rw [rho_x_eq_sum D ρ α hα c]
    exact LinearMap.sum_apply _ _ x
  simp only [hpoint, Finset.smul_sum]
  calc (∑ c : K, ∑ d : K, ∑ k ∈ Finset.range (Nat.card Kˣ + 1),
        (rootCoeff i c * rootCoeff j d) • ((c + d) ^ k • rootOp D ρ α k x))
      = ∑ k ∈ Finset.range (Nat.card Kˣ + 1), ∑ c : K, ∑ d : K,
          (rootCoeff i c * rootCoeff j d) • ((c + d) ^ k • rootOp D ρ α k x) := by
        rw [Finset.sum_congr rfl fun c _ => Finset.sum_comm]
        rw [Finset.sum_comm]
    _ = ∑ k ∈ Finset.range (Nat.card Kˣ + 1),
          (∑ c : K, ∑ d : K, rootCoeff i c * rootCoeff j d * (c + d) ^ k) •
            rootOp D ρ α k x := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [show (∑ c : K, ∑ d : K,
            (rootCoeff i c * rootCoeff j d) • ((c + d) ^ k • rootOp D ρ α k x)) =
            ∑ c : K, (∑ d : K, rootCoeff i c * rootCoeff j d * (c + d) ^ k) •
              rootOp D ρ α k x from by
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [show (∑ d : K, (rootCoeff i c * rootCoeff j d) •
              ((c + d) ^ k • rootOp D ρ α k x)) =
              ∑ d : K, (rootCoeff i c * rootCoeff j d * (c + d) ^ k) •
                rootOp D ρ α k x from
            Finset.sum_congr rfl fun d _ => smul_smul _ _ _]
          rw [← Finset.sum_smul]]
        rw [← Finset.sum_smul]

private theorem rootOp_mul_apply (α : Fin 4 → ℤ) (hα : IsD4Root α) (i j : ℕ) (x : X) :
    (rootOp D ρ α i * rootOp D ρ α j) x =
      (if i + j ≤ Nat.card Kˣ then (((i + j).choose i : ℕ) : K) else 0) •
        rootOp D ρ α (i + j) x := by
  rw [rootOp_mul_expand D ρ α hα i j x, rootOp_mul_expand' D ρ α hα i j x]
  have h3 : (∑ k ∈ Finset.range (Nat.card Kˣ + 1),
        (∑ c : K, ∑ d : K, rootCoeff i c * rootCoeff j d * (c + d) ^ k) •
          rootOp D ρ α k x) =
      ∑ k ∈ Finset.range (Nat.card Kˣ + 1),
        (if k = i + j then (((k.choose i : ℕ) : K)) else 0) • rootOp D ρ α k x := by
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [rootCoeff_mul_binomial (by
      have := Finset.mem_range.mp hk
      omega)]
  rw [h3]
  by_cases hij : i + j ≤ Nat.card Kˣ
  · rw [if_pos hij]
    rw [Finset.sum_eq_single (i + j)]
    · rw [if_pos rfl]
    · intro k _ hk
      rw [if_neg hk, zero_smul]
    · intro hnot
      exact absurd (Finset.mem_range.mpr (by omega)) hnot
  · rw [if_neg hij, zero_smul]
    refine Finset.sum_eq_zero fun k hk => ?_
    have hk' : k ≤ Nat.card Kˣ := by
      have := Finset.mem_range.mp hk
      omega
    rw [if_neg (fun h => absurd h (by omega)), zero_smul]

theorem rootOp_mul (α : Fin 4 → ℤ) (hα : IsD4Root α) (i j : ℕ) :
    rootOp D ρ α i * rootOp D ρ α j =
      (if i + j ≤ Nat.card Kˣ then (((i + j).choose i : ℕ) : K) else 0) •
        rootOp D ρ α (i + j) := by
  ext x
  exact rootOp_mul_apply D ρ α hα i j x

end CFSG.LieType.D4Small.D4Datum
