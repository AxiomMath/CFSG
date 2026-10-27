module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainZ4

public section

namespace CFSG.EvenSmallLie.OmegaEight.Chain

open Subgroup Matrix Stage1 CFSG.EvenSmallLie.UnitarySix.YamadaPar

variable {G : Type*} [Group G]

structure Coord4 (A : Subgroup G) (ψ : V6 → G) (Φ : (Fin 6 → ZMod 4) → G) : Prop where
  mem : ∀ v, Φ v ∈ A
  add : ∀ v w, Φ (v + w) = Φ v * Φ w
  surj : ∀ x ∈ A, ∃ v, Φ v = x
  inj : ∀ v, Φ v = 1 → v = 0
  sq : ∀ v, Φ v * Φ v = ψ fun j => red4 (v j)

namespace Coord4

variable {A : Subgroup G} {ψ : V6 → G} {Φ : (Fin 6 → ZMod 4) → G} (hΦ : Coord4 A ψ Φ)
include hΦ

theorem zero : Φ 0 = 1 := by
  have h := hΦ.add 0 0
  rw [add_zero] at h
  exact left_eq_mul.1 h

theorem neg (v : Fin 6 → ZMod 4) : Φ (-v) = (Φ v)⁻¹ := by
  have h := hΦ.add (-v) v
  rw [neg_add_cancel, hΦ.zero] at h
  exact eq_inv_of_mul_eq_one_left h.symm

theorem injective : Function.Injective Φ := by
  intro v w h
  have : Φ (v - w) = 1 := by
    rw [sub_eq_add_neg, hΦ.add, hΦ.neg, h, mul_inv_cancel]
  exact sub_eq_zero.1 (hΦ.inj _ this)

end Coord4

@[expose] def liftV (u : V6) : Fin 6 → ZMod 4 := fun j => ((u j).val : ZMod 4)

theorem red_liftV (u : V6) : (fun j => red4 (liftV u j)) = u := funext fun j => red4_val (u j)

theorem pow_val_cases {B : Type*} [Monoid B] {x : B} (hx : x * x = 1) (c : ZMod 4) :
    x ^ c.val = if red4 c = 1 then x else 1 := by
  rcases (show ∀ c : ZMod 4, c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 by decide) c with h | h | h | h <;>
    subst h
  · simp [show red4 0 = 0 by decide, show (0 : ZMod 4).val = 0 from rfl]
  · simp [show red4 1 = 1 by decide, show (1 : ZMod 4).val = 1 from rfl]
  · simp [show red4 2 = 0 by decide, show (2 : ZMod 4).val = 2 from rfl, sq, hx]
  · simp [show red4 3 = 1 by decide, show (3 : ZMod 4).val = 3 from rfl, pow_succ, hx]

theorem exists_coord4 {A Q : Subgroup G} {ψ : V6 → G}
    (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (h4 : ∀ x ∈ A, x ^ 4 = 1)
    (hsqQ : ∀ x ∈ A, x * x ∈ Q) (hmemQ : ∀ x ∈ A, x * x = 1 → x ∈ Q) (hQA : Q ≤ A)
    (honto : ∀ q ∈ Q, ∃ x ∈ A, x * x = q) (hcard : Nat.card A = 4096)
    (ψ_add : ∀ v w, ψ (v + w) = ψ v * ψ w) (ψ_mem : ∀ v, ψ v ∈ Q)
    (mem_ψ : ∀ x ∈ Q, ∃ v, ψ v = x) : ∃ Φ, Coord4 A ψ Φ := by
  classical
  choose b hbA hb using fun j : Fin 6 => honto _ (ψ_mem (Pi.single j 1))
  let _ : CommGroup A :=
    { (inferInstance : Group A) with mul_comm := fun x y => Subtype.ext (hcomm x x.2 y y.2) }
  have hψ0 : ψ 0 = 1 := by
    have := ψ_add 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  have hψA : ∀ u : V6, ψ u ∈ A := fun u => hQA (ψ_mem u)
  let ψ' : Multiplicative V6 →* A :=
    { toFun := fun u => ⟨ψ (Multiplicative.toAdd u), hψA _⟩
      map_one' := Subtype.ext (by simp [hψ0])
      map_mul' := fun u w => Subtype.ext (by simp [ψ_add]) }
  have hψ'apply : ∀ u : V6, ((ψ' (Multiplicative.ofAdd u) : A) : G) = ψ u := fun u => rfl
  let b' : Fin 6 → A := fun j => ⟨b j, hbA j⟩
  have hb4 : ∀ j, b' j ^ 4 = 1 := fun j => Subtype.ext (by simpa using h4 _ (hbA j))
  have hbb : ∀ j, b' j * b' j = ψ' (Multiplicative.ofAdd (Pi.single j 1)) :=
    fun j => Subtype.ext (hb j)
  let Φ' : (Fin 6 → ZMod 4) → A := fun v => ∏ j, b' j ^ (v j).val
  have hadd : ∀ v w, Φ' (v + w) = Φ' v * Φ' w := by
    intro v w
    simp only [Φ', ← Finset.prod_mul_distrib, Pi.add_apply]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [ZMod.val_add, ← pow_eq_pow_mod _ (hb4 j), pow_add]
  have hψsum : ∀ u : V6,
      ψ' (Multiplicative.ofAdd u) = ∏ j, ψ' (Multiplicative.ofAdd (Pi.single j (u j))) := by
    intro u
    rw [← map_prod, ← ofAdd_sum, Finset.univ_sum_single]
  have hsq : ∀ v, Φ' v * Φ' v = ψ' (Multiplicative.ofAdd fun j => red4 (v j)) := by
    intro v
    rw [hψsum, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [← mul_pow, hbb]
    have hx : ψ' (Multiplicative.ofAdd (Pi.single j 1)) *
        ψ' (Multiplicative.ofAdd (Pi.single j 1)) = 1 := by
      rw [← map_mul, ← ofAdd_add, ← Pi.single_add, CharTwo.add_self_eq_zero, Pi.single_zero,
        ofAdd_zero, map_one]
    rw [pow_val_cases hx]
    split_ifs with h
    · rw [h]
    · have h0 : red4 (v j) = 0 := by
        rcases (show ∀ c : ZMod 2, c = 0 ∨ c = 1 by decide) (red4 (v j)) with h' | h'
        · exact h'
        · exact absurd h' h
      rw [h0, Pi.single_zero, ofAdd_zero, map_one]
  have hsqG : ∀ v, ((Φ' v : A) : G) * (Φ' v : A) = ψ fun j => red4 (v j) := fun v => by
    rw [← Subgroup.coe_mul, hsq, hψ'apply]
  have hsurj : ∀ x ∈ A, ∃ v, ((Φ' v : A) : G) = x := by
    intro x hx
    obtain ⟨u, hu⟩ := mem_ψ _ (hsqQ x hx)
    set y := x * ((Φ' (liftV u) : A) : G)⁻¹ with hy
    have hyA : y ∈ A := mul_mem hx (inv_mem (Φ' (liftV u)).2)
    have hy2 : y * y = 1 := by
      have h1 := hsqG (liftV u)
      rw [red_liftV] at h1
      have hc := hcomm _ (inv_mem (Φ' (liftV u)).2) x hx
      calc y * y = x * (((Φ' (liftV u) : A) : G)⁻¹ * x) * ((Φ' (liftV u) : A) : G)⁻¹ := by
            simp only [hy]; group
        _ = x * x * (((Φ' (liftV u) : A) : G) * ((Φ' (liftV u) : A) : G))⁻¹ := by
            rw [hc]; group
        _ = 1 := by rw [h1, hu, mul_inv_cancel]
    obtain ⟨u', hu'⟩ := mem_ψ _ (hmemQ y hyA hy2)
    refine ⟨liftV u' + liftV u' + liftV u, ?_⟩
    rw [hadd, hadd, Subgroup.coe_mul, Subgroup.coe_mul, hsqG, red_liftV, hu', hy,
      inv_mul_cancel_right]
  have hfin : Finite A := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hbij : Function.Bijective Φ' := by
    refine Function.Surjective.bijective_of_nat_card_le (fun x => ?_) ?_
    · obtain ⟨v, hv⟩ := hsurj x x.2
      exact ⟨v, Subtype.ext hv⟩
    · rw [hcard]; simp
  have hΦ0 : Φ' 0 = 1 := by simp [Φ']
  refine ⟨fun v => (Φ' v : G), ⟨fun v => (Φ' v).2, fun v w => by rw [hadd, Subgroup.coe_mul],
    hsurj, fun v hv => hbij.1 (by rw [hΦ0]; exact Subtype.ext hv), hsqG⟩⟩

@[expose] def Rep (Φ : (Fin 6 → ZMod 4) → G) (g : G) (F : Matrix (Fin 6) (Fin 6) (ZMod 4)) :
    Prop :=
  ∀ v, g * Φ v * g⁻¹ = Φ (F *ᵥ v)

theorem additive_eq_mulVec4 {f : (Fin 6 → ZMod 4) → (Fin 6 → ZMod 4)}
    (hadd : ∀ v w, f (v + w) = f v + f w) (v : Fin 6 → ZMod 4) :
    f v = (Matrix.of fun i j => f (Pi.single j 1) i) *ᵥ v := by
  let F : (Fin 6 → ZMod 4) →+ (Fin 6 → ZMod 4) := AddMonoidHom.mk' f hadd
  have hsingle : ∀ (j : Fin 6) (c : ZMod 4), f (Pi.single j c) = c • f (Pi.single j 1) := by
    intro j c
    have h1 : Pi.single j c = c.val • (Pi.single j 1 : Fin 6 → ZMod 4) := by
      rw [← Pi.single_smul, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
    have h2 : f (c.val • Pi.single j 1) = c.val • f (Pi.single j 1) := map_nsmul F _ _
    rw [h1, h2, ← Nat.cast_smul_eq_nsmul (ZMod 4), ZMod.natCast_zmod_val]
  conv_lhs => rw [← Finset.univ_sum_single v]
  have : f (∑ j, Pi.single j (v j)) = ∑ j, f (Pi.single j (v j)) := map_sum F _ _
  rw [this]
  ext i
  rw [Finset.sum_apply]
  simp only [mulVec, dotProduct, Matrix.of_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hsingle j (v j), Pi.smul_apply, smul_eq_mul, mul_comm]

theorem map_red4_mulVec (F : Matrix (Fin 6) (Fin 6) (ZMod 4)) (v : Fin 6 → ZMod 4) :
    (fun j => red4 ((F *ᵥ v) j)) = F.map red4 *ᵥ fun j => red4 (v j) := by
  ext i
  exact RingHom.map_mulVec red4 F v i

theorem exists_two (y : ZMod 4) :
    ∃ d : ZMod 2, y = ((red4 y).val : ZMod 4) + 2 * (d.val : ZMod 4) := by
  revert y; decide

theorem eq_lift4_add (F : Matrix (Fin 6) (Fin 6) (ZMod 4)) :
    ∃ D, F = lift4 (F.map red4) + (2 : ZMod 4) • lift4 D := by
  choose d hd using fun i j => exists_two (F i j)
  refine ⟨Matrix.of d, ?_⟩
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, lift4, map_apply, of_apply]
  exact hd i j

namespace Coord4

variable {A : Subgroup G} {ψ : V6 → G} {Φ : (Fin 6 → ZMod 4) → G} (hΦ : Coord4 A ψ Φ)
include hΦ

theorem exists_rep {g : G} (hg : ∀ x ∈ A, g * x * g⁻¹ ∈ A) : ∃ F, Rep Φ g F := by
  choose f hf using fun v => hΦ.surj _ (hg _ (hΦ.mem v))
  have hadd : ∀ v w, f (v + w) = f v + f w := by
    intro v w
    refine hΦ.injective ?_
    rw [hf, hΦ.add, hΦ.add, hf, hf]
    group
  exact ⟨_, fun v => by rw [← hf v, additive_eq_mulVec4 hadd v]⟩

theorem rep_unique {g : G} {F F' : Matrix (Fin 6) (Fin 6) (ZMod 4)} (hF : Rep Φ g F)
    (hF' : Rep Φ g F') : F = F' :=
  Matrix.ext_iff_mulVec.2 fun v => hΦ.injective (by rw [← hF v, ← hF' v])

omit hΦ in
theorem rep_mul {g h : G} {F F' : Matrix (Fin 6) (Fin 6) (ZMod 4)} (hF : Rep Φ g F)
    (hF' : Rep Φ h F') : Rep Φ (g * h) (F * F') := fun v => by
  rw [← mulVec_mulVec, ← hF, ← hF']
  group

omit hΦ in
theorem rep_one : Rep Φ 1 1 := fun v => by rw [one_mulVec]; group

theorem rep_of_mem_A (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) {x : G} (hx : x ∈ A) :
    Rep Φ x 1 := fun v => by
  rw [one_mulVec, hcomm x hx _ (hΦ.mem v), mul_inv_cancel_right]

theorem map_red4_of_rep {g : G} {F : Matrix (Fin 6) (Fin 6) (ZMod 4)} (hF : Rep Φ g F)
    (ψ_inj : Function.Injective ψ) {M : Matrix (Fin 6) (Fin 6) (ZMod 2)}
    (hM : ∀ u, g * ψ u * g⁻¹ = ψ (M *ᵥ u)) : F.map red4 = M := by
  have key : ∀ v, (fun j => red4 ((F *ᵥ v) j)) = M *ᵥ fun j => red4 (v j) := by
    intro v
    apply ψ_inj
    have h1 := hΦ.sq (F *ᵥ v)
    have h2 := hΦ.sq v
    rw [← h1, ← hM, ← h2, ← hF v]
    group
  refine Matrix.ext_iff_mulVec.2 fun u => ?_
  have := key (liftV u)
  rwa [red_liftV, map_red4_mulVec, red_liftV] at this

end Coord4

theorem sq_one_add_two (X : Mat6) :
    (1 + (2 : ZMod 4) • lift4 X) * (1 + (2 : ZMod 4) • lift4 X) = 1 := by
  simp only [add_mul, mul_add, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [show (2 : ZMod 4) * 2 = 0 by decide, zero_smul, add_zero, add_assoc, ← add_smul,
    show (2 : ZMod 4) + 2 = 0 by decide, zero_smul, add_zero]

theorem map_red4_one_add_two (X : Mat6) : (1 + (2 : ZMod 4) • lift4 X).map red4 = 1 := by
  ext i j
  simp only [map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul,
    show red4 2 = 0 by decide, zero_mul, add_zero]
  by_cases h : i = j
  · subst h; simp
  · simp [h]

theorem conj_two (X M C : Mat6) :
    (1 + (2 : ZMod 4) • lift4 X) * (lift4 M + (2 : ZMod 4) • lift4 C) *
        (1 + (2 : ZMod 4) • lift4 X) =
      lift4 M + (2 : ZMod 4) • lift4 (C + X * M + M * X) := by
  have e : (1 + (2 : ZMod 4) • lift4 X) * (lift4 M + (2 : ZMod 4) • lift4 C) *
        (1 + (2 : ZMod 4) • lift4 X) =
      lift4 M + ((2 : ZMod 4) • lift4 C + (2 : ZMod 4) • (lift4 X * lift4 M) +
        (2 : ZMod 4) • (lift4 M * lift4 X)) := by
    simp only [add_mul, mul_add, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [show (2 : ZMod 4) * 2 = 0 by decide]
    simp only [zero_smul, add_zero, mul_zero]
    generalize lift4 M = m
    generalize (2 : ZMod 4) • lift4 C = c
    generalize (2 : ZMod 4) • (lift4 X * m) = x
    generalize (2 : ZMod 4) • (m * lift4 X) = y
    abel
  rw [e, two_smul_eq_lift4 (lift4 X * lift4 M), two_smul_eq_lift4 (lift4 M * lift4 X),
    Matrix.map_mul, Matrix.map_mul, map_red4_lift4, map_red4_lift4, ← two_smul_lift4_add,
    ← two_smul_lift4_add]

namespace Coord4

variable {A : Subgroup G} {ψ : V6 → G} {Φ : (Fin 6 → ZMod 4) → G} (hΦ : Coord4 A ψ Φ)
include hΦ

theorem change (X : Mat6) : Coord4 A ψ fun v => Φ ((1 + (2 : ZMod 4) • lift4 X) *ᵥ v) where
  mem v := hΦ.mem _
  add v w := by rw [mulVec_add, hΦ.add]
  surj x hx := by
    obtain ⟨v, rfl⟩ := hΦ.surj x hx
    refine ⟨(1 + (2 : ZMod 4) • lift4 X) *ᵥ v, ?_⟩
    rw [mulVec_mulVec, sq_one_add_two, one_mulVec]
  inj v hv := by
    have h := hΦ.inj _ hv
    have := congrArg (fun w => (1 + (2 : ZMod 4) • lift4 X) *ᵥ w) h
    simp only [mulVec_mulVec, sq_one_add_two, one_mulVec, mulVec_zero] at this
    exact this
  sq v := by
    rw [hΦ.sq, map_red4_mulVec, map_red4_one_add_two, one_mulVec]

omit hΦ in
theorem rep_change (X : Mat6) {g : G} {F : Matrix (Fin 6) (Fin 6) (ZMod 4)} (hF : Rep Φ g F) :
    Rep (fun v => Φ ((1 + (2 : ZMod 4) • lift4 X) *ᵥ v)) g
      ((1 + (2 : ZMod 4) • lift4 X) * F * (1 + (2 : ZMod 4) • lift4 X)) := fun v => by
  simp only
  rw [hF, mulVec_mulVec, mulVec_mulVec, ← mul_assoc, ← mul_assoc, sq_one_add_two, one_mul]

end Coord4

end CFSG.EvenSmallLie.OmegaEight.Chain
