module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact2025Core

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KF2025

open CFSG Equiv
open scoped commutatorElement

universe u v

section Gam

variable {k : Type u} [Field k] {V : Type v} [AddCommGroup V] [Module k V]

theorem gam_aux (h2 : (2 : k) ≠ 0) {X : Module.End k V} (hX : X * X = -1) :
    (1 + X) * (algebraMap k (Module.End k V) 2⁻¹ * (1 - X)) = 1 ∧
      (algebraMap k (Module.End k V) 2⁻¹ * (1 - X)) * (1 + X) = 1 := by
  have h22 : algebraMap k (Module.End k V) 2⁻¹ * 2 = 1 := by
    rw [← map_ofNat (algebraMap k (Module.End k V)) 2, ← map_mul, inv_mul_cancel₀ h2, map_one]
  have e1 : (1 + X) * (1 - X) = 2 := by
    calc (1 + X) * (1 - X) = 1 - X * X := by noncomm_ring
      _ = 2 := by rw [hX]; norm_num
  have e2 : (1 - X) * (1 + X) = 2 := by
    calc (1 - X) * (1 + X) = 1 - X * X := by noncomm_ring
      _ = 2 := by rw [hX]; norm_num
  constructor
  · calc (1 + X) * (algebraMap k (Module.End k V) 2⁻¹ * (1 - X))
        = ((1 + X) * algebraMap k (Module.End k V) 2⁻¹) * (1 - X) := (mul_assoc _ _ _).symm
      _ = (algebraMap k (Module.End k V) 2⁻¹ * (1 + X)) * (1 - X) := by
          rw [← Algebra.commutes 2⁻¹ (1 + X)]
      _ = algebraMap k (Module.End k V) 2⁻¹ * ((1 + X) * (1 - X)) := mul_assoc _ _ _
      _ = 1 := by rw [e1, h22]
  · calc (algebraMap k (Module.End k V) 2⁻¹ * (1 - X)) * (1 + X)
        = algebraMap k (Module.End k V) 2⁻¹ * ((1 - X) * (1 + X)) := mul_assoc _ _ _
      _ = 1 := by rw [e2, h22]

@[expose] noncomputable def gam (h2 : (2 : k) ≠ 0) (x : (Module.End k V)ˣ) (hx : x * x = -1) :
    (Module.End k V)ˣ where
  val := 1 + (x : Module.End k V)
  inv := algebraMap k (Module.End k V) 2⁻¹ * (1 - (x : Module.End k V))
  val_inv := (gam_aux h2 (by simpa using congrArg Units.val hx)).1
  inv_val := (gam_aux h2 (by simpa using congrArg Units.val hx)).2

theorem gam_val (h2 : (2 : k) ≠ 0) (x : (Module.End k V)ˣ) (hx : x * x = -1) :
    ((gam h2 x hx : (Module.End k V)ˣ) : Module.End k V) = 1 + (x : Module.End k V) := rfl

theorem gam_inv_val (h2 : (2 : k) ≠ 0) (x : (Module.End k V)ˣ) (hx : x * x = -1) :
    (((gam h2 x hx)⁻¹ : (Module.End k V)ˣ) : Module.End k V) =
      algebraMap k (Module.End k V) 2⁻¹ * (1 - (x : Module.End k V)) := rfl

theorem gam_conj_comm (h2 : (2 : k) ≠ 0) {x : (Module.End k V)ˣ} (hx : x * x = -1)
    {y : (Module.End k V)ˣ} (hy : y * x = x * y) :
    gam h2 x hx * y * (gam h2 x hx)⁻¹ = y := by
  have hX : (x : Module.End k V) * x = -1 := by simpa using congrArg Units.val hx
  have hY : (y : Module.End k V) * x = x * y := by simpa using congrArg Units.val hy
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, gam_val, gam_inv_val]
  have hc : (1 + (x : Module.End k V)) * y = y * (1 + x) := by
    rw [add_mul, mul_add, one_mul, mul_one, hY.symm]
  calc (1 + (x : Module.End k V)) * y * (algebraMap k (Module.End k V) 2⁻¹ * (1 - x))
      = y * ((1 + (x : Module.End k V)) * (algebraMap k (Module.End k V) 2⁻¹ * (1 - x))) := by
        rw [hc, mul_assoc]
    _ = y := by rw [(gam_aux h2 hX).1, mul_one]

theorem gam_conj_anti (h2 : (2 : k) ≠ 0) {x : (Module.End k V)ˣ} (hx : x * x = -1)
    {y : (Module.End k V)ˣ} (hy : y * x = -(x * y)) :
    gam h2 x hx * y * (gam h2 x hx)⁻¹ = x * y := by
  have hX : (x : Module.End k V) * x = -1 := by simpa using congrArg Units.val hx
  have hY : (y : Module.End k V) * x = -(x * y) := by simpa using congrArg Units.val hy
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, gam_val, gam_inv_val]
  set c := algebraMap k (Module.End k V) 2⁻¹ with hcdef
  have hc2 : c * 2 = 1 := by
    rw [hcdef, ← map_ofNat (algebraMap k (Module.End k V)) 2, ← map_mul, inv_mul_cancel₀ h2,
      map_one]
  have key : (y : Module.End k V) * (1 - x) = (1 + x) * y := by
    rw [mul_sub, mul_one, hY, add_mul, one_mul, sub_neg_eq_add, add_comm]
  have hsq : (1 + (x : Module.End k V)) * (1 + x) = 2 * x := by
    calc (1 + (x : Module.End k V)) * (1 + x) = 1 + 2 * x + x * x := by noncomm_ring
      _ = 2 * x := by rw [hX]; noncomm_ring
  calc (1 + (x : Module.End k V)) * y * (c * (1 - x))
      = (((1 + (x : Module.End k V)) * y) * c) * (1 - x) := by rw [mul_assoc _ c]
    _ = (c * ((1 + (x : Module.End k V)) * y)) * (1 - x) := by
        rw [← Algebra.commutes 2⁻¹ ((1 + (x : Module.End k V)) * y)]
    _ = c * ((1 + (x : Module.End k V)) * (y * (1 - x))) := by
        rw [mul_assoc, mul_assoc]
    _ = c * ((1 + (x : Module.End k V)) * ((1 + x) * y)) := by rw [key]
    _ = c * (((1 + (x : Module.End k V)) * (1 + x)) * y) := by rw [mul_assoc]
    _ = c * ((2 * x) * y) := by rw [hsq]
    _ = (c * 2) * (x * y) := by noncomm_ring
    _ = x * y := by rw [hc2, one_mul]

end Gam


section PermSet

variable {k : Type u} [Field k] {V : Type v} [AddCommGroup V] [Module k V]
variable {R : Subgroup (Module.End k V)ˣ} {u : (Module.End k V)ˣ}
  {t : Fin 5 → (Module.End k V)ˣ}

theorem Pent.eq_of_eq_pm (h : Min32 R u) (ht : Pent R u t) {i j : Fin 5}
    (hij : t i = t j ∨ t i = -(t j)) : i = j := by
  by_contra hne
  have ha := ht.anti i j hne
  have hs := ht.sq j
  rcases hij with h1 | h1
  · rw [h1] at ha
    exact h.eq_neg_self_false ha
  · rw [h1, neg_mul, mul_neg, neg_neg, hs] at ha
    exact h.neg_one_ne_one ha

theorem pm_trans {x a b : (Module.End k V)ˣ} (h1 : x = a ∨ x = -a) (h2 : x = b ∨ x = -b) :
    a = b ∨ a = -b := by
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact Or.inl (h1.symm.trans h2)
  · exact Or.inr (h1.symm.trans h2)
  · exact Or.inr (eq_neg_symm (h2.symm.trans h1))
  · exact Or.inl (neg_injective (h1.symm.trans h2))

@[expose] def PermRel (t : Fin 5 → (Module.End k V)ˣ) (w : (Module.End k V)ˣ) (σ : Perm (Fin 5)) :
    Prop :=
  ∀ i, w * t i * w⁻¹ = t (σ i) ∨ w * t i * w⁻¹ = -(t (σ i))

theorem PermRel.one : PermRel t 1 1 := fun i => Or.inl (by simp)

theorem PermRel.mul {w₁ w₂ : (Module.End k V)ˣ} {σ₁ σ₂ : Perm (Fin 5)} (h₁ : PermRel t w₁ σ₁)
    (h₂ : PermRel t w₂ σ₂) : PermRel t (w₁ * w₂) (σ₁ * σ₂) := by
  intro i
  have e : w₁ * w₂ * t i * (w₁ * w₂)⁻¹ = w₁ * (w₂ * t i * w₂⁻¹) * w₁⁻¹ := by group
  rw [e]
  rcases h₂ i with h | h
  · rw [h]; exact h₁ (σ₂ i)
  · rw [h, mul_neg, neg_mul]
    rcases h₁ (σ₂ i) with h' | h'
    · right; rw [h']; rfl
    · left; rw [h', neg_neg]; rfl

theorem PermRel.inv {w : (Module.End k V)ˣ} {σ : Perm (Fin 5)} (hw : PermRel t w σ) :
    PermRel t w⁻¹ σ⁻¹ := by
  intro i
  have := hw (σ⁻¹ i)
  have hσ : σ (σ⁻¹ i) = i := by simp
  rw [hσ] at this
  rcases this with h | h
  · left
    rw [inv_inv, ← h]; group
  · right
    have h' : t i = -(w * t (σ⁻¹ i) * w⁻¹) := by rw [h, neg_neg]
    rw [inv_inv, h', mul_neg, neg_mul]
    congr 1
    group

@[expose] def permSet (t : Fin 5 → (Module.End k V)ˣ) : Subgroup (Module.End k V)ˣ where
  carrier := {w | ∃ σ, PermRel t w σ}
  one_mem' := ⟨1, PermRel.one⟩
  mul_mem' := by
    rintro w₁ w₂ ⟨σ₁, h₁⟩ ⟨σ₂, h₂⟩
    exact ⟨σ₁ * σ₂, h₁.mul h₂⟩
  inv_mem' := by
    rintro w ⟨σ, hσ⟩
    exact ⟨σ⁻¹, hσ.inv⟩

theorem PermRel.unique (h : Min32 R u) (ht : Pent R u t) {w : (Module.End k V)ˣ}
    {σ σ' : Perm (Fin 5)} (h₁ : PermRel t w σ) (h₂ : PermRel t w σ') : σ = σ' := by
  ext i
  exact congrArg Fin.val (ht.eq_of_eq_pm h (pm_trans (h₁ i) (h₂ i)))

@[expose] noncomputable def permOf (h : Min32 R u) (ht : Pent R u t) :
    permSet t →* Perm (Fin 5) where
  toFun w := Classical.choose w.2
  map_one' := PermRel.unique h ht (Classical.choose_spec (1 : permSet t).2) PermRel.one
  map_mul' := fun w₁ w₂ => PermRel.unique h ht (Classical.choose_spec (w₁ * w₂ : permSet t).2)
    ((Classical.choose_spec w₁.2).mul (Classical.choose_spec w₂.2))

theorem permOf_spec (h : Min32 R u) (ht : Pent R u t) (w : permSet t) :
    PermRel t w (permOf h ht w) := Classical.choose_spec w.2

theorem permOf_eq (h : Min32 R u) (ht : Pent R u t) {w : permSet t} {σ : Perm (Fin 5)}
    (hw : PermRel t w σ) : permOf h ht w = σ :=
  PermRel.unique h ht (permOf_spec h ht w) hw

end PermSet


section Specific

variable {k : Type u} [Field k] {V : Type v} [AddCommGroup V] [Module k V]
variable {R : Subgroup (Module.End k V)ˣ} {u : (Module.End k V)ˣ}
  {t : Fin 5 → (Module.End k V)ˣ}

@[expose] noncomputable def half (h2 : (2 : k) ≠ 0) : (Module.End k V)ˣ where
  val := algebraMap k (Module.End k V) 2⁻¹
  inv := algebraMap k (Module.End k V) 2
  val_inv := by rw [← map_mul, inv_mul_cancel₀ h2, map_one]
  inv_val := by rw [← map_mul, mul_inv_cancel₀ h2, map_one]

theorem half_comm (h2 : (2 : k) ≠ 0) (g : (Module.End k V)ˣ) : half h2 * g = g * half h2 :=
  Units.ext (Algebra.commutes (2⁻¹ : k) (g : Module.End k V))

theorem permRel_half (h2 : (2 : k) ≠ 0) : PermRel t (half h2) 1 := fun i => Or.inl (by
  rw [half_comm h2 (t i), mul_inv_cancel_right]; rfl)

theorem permRel_central {y : (Module.End k V)ˣ} (hy : ∀ g, y * g = g * y) : PermRel t y 1 :=
  fun i => Or.inl (by rw [hy (t i), mul_inv_cancel_right]; rfl)

theorem permRel_u (hu : ∀ i, u * t i * u⁻¹ = t (i + 1)) : PermRel t u (finRotate 5) :=
  fun i => Or.inl (by rw [finRotate_succ_apply]; exact hu i)

theorem gam_pair_rel (h2 : (2 : k) ≠ 0) (ht : Pent R u t) {i j : Fin 5} (hij : i ≠ j) :
    ∃ hx : t i * t j * (t i * t j) = -1, PermRel t (gam h2 (t i * t j) hx) (swap i j) := by
  have hx : (t i * t j) * (t i * t j) = -1 :=
    sq2_anti _ _ (ht.sq i) (ht.sq j) (ht.anti j i (Ne.symm hij))
  refine ⟨hx, fun k => ?_⟩
  by_cases hki : k = i
  · rw [hki]
    have h1 := (pair_pattern ht hij i).2 (Or.inl rfl)
    have hanti : t i * (t i * t j) = -((t i * t j) * t i) := eq_neg_symm h1
    rw [gam_conj_anti h2 hx hanti, swap_apply_left]
    right
    rw [h1, ← mul_assoc, ht.sq i, one_mul]
  · by_cases hkj : k = j
    · rw [hkj]
      have h1 := (pair_pattern ht hij j).2 (Or.inr rfl)
      have hanti : t j * (t i * t j) = -((t i * t j) * t j) := eq_neg_symm h1
      rw [gam_conj_anti h2 hx hanti, swap_apply_right]
      left
      rw [mul_assoc, ht.sq j, mul_one]
    · have hcomm : t k * (t i * t j) = (t i * t j) * t k :=
        ((pair_pattern ht hij k).1 hki hkj).symm
      rw [gam_conj_comm h2 hx hcomm, swap_apply_of_ne_of_ne hki hkj]
      left
      rfl

theorem permSet_le_normalizer (ht : Pent R u t) (hm1 : (-1 : (Module.End k V)ˣ) ∈ R) :
    permSet t ≤ Subgroup.normalizer (R : Set (Module.End k V)ˣ) := by
  have key : ∀ w ∈ permSet t, ∀ r ∈ R, w * r * w⁻¹ ∈ R := by
    rintro w ⟨σ, hσ⟩ r hr
    have hall : ∀ x ∈ Subgroup.closure (insert (-1 : (Module.End k V)ˣ) (Set.range t)),
        w * x * w⁻¹ ∈ R := by
      intro x hx
      induction hx using Subgroup.closure_induction with
      | mem x hx =>
        rcases hx with rfl | ⟨i, rfl⟩
        · rw [mul_neg_one, neg_mul, mul_inv_cancel]; exact hm1
        · rcases hσ i with h | h
          · rw [h]; exact ht.mem _
          · rw [h]
            have : -(t (σ i)) = (-1) * t (σ i) := (neg_one_mul _).symm
            rw [this]
            exact R.mul_mem hm1 (ht.mem _)
      | one => simp
      | mul x y _ _ hx hy => rw [conj_mul]; exact R.mul_mem hx hy
      | inv x _ hx =>
        have : w * x⁻¹ * w⁻¹ = (w * x * w⁻¹)⁻¹ := by group
        rw [this]; exact R.inv_mem hx
    exact hall r (ht.gen r hr)
  intro w hw
  refine Subgroup.mem_normalizer_iff.mpr fun r => ⟨fun hr => key w hw r hr, fun hr => ?_⟩
  have := key w⁻¹ (inv_mem hw) _ hr
  have e : w⁻¹ * (w * r * w⁻¹) * w⁻¹⁻¹ = r := by group
  rwa [e] at this

end Specific


section AltGen

theorem closure_five_three_eq_alt :
    Subgroup.closure ({finRotate 5, swap 0 1 * swap 1 2} : Set (Perm (Fin 5))) =
      alternatingGroup (Fin 5) := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · rw [SetLike.mem_coe, Equiv.Perm.mem_alternatingGroup, sign_finRotate]
      norm_num
    · rw [SetLike.mem_coe, Equiv.Perm.mem_alternatingGroup, Perm.sign_mul,
        Perm.sign_swap (by decide), Perm.sign_swap (by decide)]
      norm_num
  · set P := Subgroup.closure ({finRotate 5, swap 0 1 * swap 1 2} : Set (Perm (Fin 5))) with hP
    have hc5 : finRotate 5 ∈ P := Subgroup.subset_closure (by simp)
    have hc3 : swap 0 1 * swap 1 2 ∈ P := Subgroup.subset_closure (by simp)
    haveI : MulAction.IsPretransitive P (Fin 5) := by
      refine ⟨fun x y => ?_⟩
      have hx : finRotate 5 x ≠ x := by revert x; decide
      have hy : finRotate 5 y ≠ y := by revert y; decide
      obtain ⟨i, hi⟩ := (isCycle_finRotate_of_le (by norm_num : 2 ≤ 5)).exists_pow_eq hx hy
      exact ⟨⟨finRotate 5 ^ i, Subgroup.pow_mem _ hc5 i⟩, hi⟩
    haveI : MulAction.IsPreprimitive P (Fin 5) :=
      MulAction.IsPreprimitive.of_prime_card (by
        rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
    have h3 : (swap 0 1 * swap 1 2 : Perm (Fin 5)).IsThreeCycle := by
      rw [swap_comm 0 1]
      exact Perm.isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)
    exact Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem this h3 hc3

end AltGen


section AltSection

variable {k : Type u} [Field k] {V : Type v} [AddCommGroup V] [Module k V]
variable {R : Subgroup (Module.End k V)ˣ} {u : (Module.End k V)ˣ}
  {t : Fin 5 → (Module.End k V)ˣ}

theorem alt_section (h2 : (2 : k) ≠ 0) (h : Min32 R u) (ht : Pent R u t) :
    ∃ (x x' : (Module.End k V)ˣ) (hx : x * x = -1) (hx' : x' * x' = -1), x ∈ R ∧
      x' = u * x * u⁻¹ ∧
      ∃ w : (Module.End k V)ˣ, w = half h2 * gam h2 x hx * gam h2 x' hx' ∧
      ∃ (hu : u ∈ Subgroup.closure ({u, w} : Set (Module.End k V)ˣ))
        (ψ : Subgroup.closure ({u, w} : Set (Module.End k V)ˣ) →* alternatingGroup (Fin 5)),
        Function.Surjective ψ ∧
        (∀ y ∈ Subgroup.closure ({u, w} : Set (Module.End k V)ˣ),
          y ∈ Subgroup.normalizer (R : Set (Module.End k V)ˣ)) ∧
        (∀ (y : (Module.End k V)ˣ) (hy : y ∈ Subgroup.closure
          ({u, w} : Set (Module.End k V)ˣ)), (∀ g, y * g = g * y) → ψ ⟨y, hy⟩ = 1) ∧
        ψ ⟨u, hu⟩ ≠ 1 := by
  obtain ⟨hx, hrel1⟩ := gam_pair_rel h2 ht (i := 0) (j := 1) (by decide)
  obtain ⟨hx', hrel2⟩ := gam_pair_rel h2 ht (i := 1) (j := 2) (by decide)
  have hm1 : (-1 : (Module.End k V)ˣ) ∈ R := h.facts.1
  have hxu : t 1 * t 2 = u * (t 0 * t 1) * u⁻¹ := by
    rw [conj_mul, ht.conj 0, ht.conj 1]; rfl
  refine ⟨t 0 * t 1, t 1 * t 2, hx, hx', R.mul_mem (ht.mem 0) (ht.mem 1), hxu, ?_⟩
  obtain ⟨w, hw⟩ : ∃ w : (Module.End k V)ˣ,
      w = half h2 * gam h2 (t 0 * t 1) hx * gam h2 (t 1 * t 2) hx' := ⟨_, rfl⟩
  refine ⟨w, hw, ?_⟩
  have hwrel : PermRel t w (swap 0 1 * swap 1 2) := by
    rw [hw]
    have := ((permRel_half h2 (t := t)).mul hrel1).mul hrel2
    simpa using this
  have hurel : PermRel t u (finRotate 5) := permRel_u ht.conj
  have huS : u ∈ permSet t := ⟨_, hurel⟩
  have hwS : w ∈ permSet t := ⟨_, hwrel⟩
  have hY : Subgroup.closure ({u, w} : Set (Module.End k V)ˣ) ≤ permSet t := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact huS
    · exact hwS
  have huY : u ∈ Subgroup.closure ({u, w} : Set (Module.End k V)ˣ) :=
    Subgroup.subset_closure (by simp)
  have hwY : w ∈ Subgroup.closure ({u, w} : Set (Module.End k V)ˣ) :=
    Subgroup.subset_closure (by simp)
  obtain ⟨φ, hφ⟩ : ∃ φ : Subgroup.closure ({u, w} : Set (Module.End k V)ˣ) →* Perm (Fin 5),
      ∀ (y : (Module.End k V)ˣ) (hy : y ∈ Subgroup.closure ({u, w} : Set (Module.End k V)ˣ)),
        φ ⟨y, hy⟩ = permOf h ht ⟨y, hY hy⟩ :=
    ⟨(permOf h ht).comp (Subgroup.inclusion hY), fun _ _ => rfl⟩
  have hφu : φ ⟨u, huY⟩ = finRotate 5 := by
    rw [hφ]
    exact permOf_eq h ht (w := ⟨u, huS⟩) hurel
  have hφw : φ ⟨w, hwY⟩ = swap 0 1 * swap 1 2 := by
    rw [hφ]
    exact permOf_eq h ht (w := ⟨w, hwS⟩) hwrel
  have hAlt : ∀ y : Subgroup.closure ({u, w} : Set (Module.End k V)ˣ),
      φ y ∈ alternatingGroup (Fin 5) := by
    rintro ⟨y, hy⟩
    induction hy using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · rw [hφu, ← closure_five_three_eq_alt]
        exact Subgroup.subset_closure (by simp)
      · rw [hφw, ← closure_five_three_eq_alt]
        exact Subgroup.subset_closure (by simp)
    | one =>
      have e : φ ⟨1, one_mem _⟩ = 1 := map_one φ
      rw [e]
      exact one_mem _
    | mul x y hx hy hx' hy' =>
      have e : φ ⟨x * y, mul_mem hx hy⟩ = φ ⟨x, hx⟩ * φ ⟨y, hy⟩ := map_mul φ ⟨x, hx⟩ ⟨y, hy⟩
      rw [e]
      exact mul_mem hx' hy'
    | inv x hx hx' =>
      have e : φ ⟨x⁻¹, inv_mem hx⟩ = (φ ⟨x, hx⟩)⁻¹ := map_inv φ ⟨x, hx⟩
      rw [e]
      exact inv_mem hx'
  refine ⟨huY, φ.codRestrict (alternatingGroup (Fin 5)) hAlt, ?_, ?_, ?_, ?_⟩
  ·
    rintro ⟨a, ha⟩
    rw [← closure_five_three_eq_alt] at ha
    have hrange : Subgroup.closure ({finRotate 5, swap 0 1 * swap 1 2} : Set (Perm (Fin 5))) ≤
        φ.range := by
      rw [Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact ⟨⟨u, huY⟩, hφu⟩
      · exact ⟨⟨w, hwY⟩, hφw⟩
    obtain ⟨y, hy⟩ := hrange ha
    exact ⟨y, Subtype.ext hy⟩
  · intro y hy
    exact permSet_le_normalizer ht hm1 (hY hy)
  · intro y hy hc
    apply Subtype.ext
    have : φ ⟨y, hy⟩ = 1 := by
      rw [hφ]
      exact permOf_eq h ht (w := ⟨y, hY hy⟩) (permRel_central hc)
    simpa using this
  · intro h1
    have h2' : φ ⟨u, huY⟩ = 1 := congrArg Subtype.val h1
    rw [hφu] at h2'
    have := congrArg (fun σ : Perm (Fin 5) => σ 0) h2'
    revert this
    decide

end AltSection

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KF2025
