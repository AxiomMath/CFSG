module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10K5S2

public section

namespace CFSG.OddStandard.SmallF3.Omega.K5

open Subgroup

structure SL23Pair (K : Type) [Group K] (A B : Subgroup K) : Prop where
  comm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a
  top : A ⊔ B = ⊤
  isoA : Nonempty (↥A ≃* SL23)
  isoB : Nonempty (↥B ≃* SL23)

namespace SL23Pair

variable {K : Type} [Group K] {A B : Subgroup K} (h : SL23Pair K A B)

include h

theorem exists_mul (k : K) : ∃ a ∈ A, ∃ b ∈ B, k = a * b := by
  let S : Subgroup K :=
    { carrier := {x | ∃ a ∈ A, ∃ b ∈ B, x = a * b}
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', mul_mem ha ha', b * b', mul_mem hb hb', ?_⟩
        calc a * b * (a' * b') = a * (b * a') * b' := by group
          _ = a * (a' * b) * b' := by rw [h.comm a' ha' b hb]
          _ = a * a' * (b * b') := by group
      one_mem' := ⟨1, one_mem _, 1, one_mem _, by simp⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, inv_mem ha, b⁻¹, inv_mem hb, ?_⟩
        rw [mul_inv_rev, ← h.comm a⁻¹ (inv_mem ha) b⁻¹ (inv_mem hb)] }
  have hle : A ⊔ B ≤ S := sup_le (fun a ha => ⟨a, ha, 1, one_mem _, by simp⟩)
    (fun b hb => ⟨1, one_mem _, b, hb, by simp⟩)
  have hk : k ∈ A ⊔ B := by
    rw [h.top]
    exact mem_top k
  exact hle hk

@[expose] noncomputable def eA : ↥A ≃* SL23 := h.isoA.some

@[expose] noncomputable def eB : ↥B ≃* SL23 := h.isoB.some

theorem card_B : Nat.card ↥B = 24 := by
  rw [Nat.card_congr h.eB.toEquiv, Nat.card_eq_fintype_card]
  decide

theorem inf_central {z : K} (hz : z ∈ A ⊓ B) (k : K) : z * k = k * z := by
  obtain ⟨a, ha, b, hb, rfl⟩ := h.exists_mul k
  have h1 : a * z = z * a := h.comm a ha z hz.2
  have h2 : z * b = b * z := h.comm z hz.1 b hb
  calc z * (a * b) = (z * a) * b := by group
    _ = (a * z) * b := by rw [h1]
    _ = a * (z * b) := by group
    _ = a * (b * z) := by rw [h2]
    _ = a * b * z := by group

theorem inf_sq {z : K} (hz : z ∈ A ⊓ B) : z * z = 1 := by
  have hc : ∀ t : SL23, h.eA ⟨z, hz.1⟩ * t = t * h.eA ⟨z, hz.1⟩ := by
    intro t
    have h1 : (⟨z, hz.1⟩ : ↥A) * h.eA.symm t = h.eA.symm t * ⟨z, hz.1⟩ :=
      Subtype.ext (h.inf_central hz _)
    have h2 := congrArg h.eA h1
    simpa using h2
  have h3 := sq_of_central hc
  have h4 : h.eA ((⟨z, hz.1⟩ : ↥A) * ⟨z, hz.1⟩) = h.eA 1 := by
    rw [map_mul, map_one]
    exact h3
  have h5 : (⟨z, hz.1⟩ : ↥A) * ⟨z, hz.1⟩ = 1 := h.eA.injective h4
  simpa using congrArg Subtype.val h5

@[expose] noncomputable def gen : Fin 4 ⊕ Fin 4 → K :=
  Sum.elim (fun i => ((h.eA.symm (k5g i) : ↥A) : K)) (fun i => ((h.eB.symm (k5g i) : ↥B) : K))

theorem gen_mem_A (i : Fin 4) : h.gen (Sum.inl i) ∈ A :=
  (h.eA.symm (k5g i)).2

theorem gen_mem_B (i : Fin 4) : h.gen (Sum.inr i) ∈ B :=
  (h.eB.symm (k5g i)).2

theorem gen_pow_three (p : Fin 4 ⊕ Fin 4) : h.gen p ^ 3 = 1 := by
  rcases p with i | i
  · have h1 : (h.eA.symm (k5g i)) ^ 3 = 1 := by
      rw [← map_pow, k5g_pow_three, map_one]
    simpa [gen] using congrArg Subtype.val h1
  · have h1 : (h.eB.symm (k5g i)) ^ 3 = 1 := by
      rw [← map_pow, k5g_pow_three, map_one]
    simpa [gen] using congrArg Subtype.val h1

theorem gen_ne_one (p : Fin 4 ⊕ Fin 4) : h.gen p ≠ 1 := by
  rcases p with i | i
  · intro h1
    apply k5g_ne_one i
    have h2 : h.eA.symm (k5g i) = 1 := Subtype.ext (by simpa [gen] using h1)
    simpa using congrArg h.eA h2
  · intro h1
    apply k5g_ne_one i
    have h2 : h.eB.symm (k5g i) = 1 := Subtype.ext (by simpa [gen] using h1)
    simpa using congrArg h.eB h2

theorem exists_gen_of_pow_three {x : K} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) (hx : x ∈ A ∨ x ∈ B) :
    ∃ p, x = h.gen p ∨ x = (h.gen p)⁻¹ := by
  rcases hx with hxA | hxB
  · have h3 : (h.eA ⟨x, hxA⟩) ^ 3 = 1 := by
      rw [← map_pow]
      have : (⟨x, hxA⟩ : ↥A) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
      rw [this, map_one]
    have h1 : h.eA ⟨x, hxA⟩ ≠ 1 := by
      intro h1
      apply hx1
      have : (⟨x, hxA⟩ : ↥A) = 1 := h.eA.injective (by simpa using h1)
      simpa using congrArg Subtype.val this
    obtain ⟨i, hi⟩ := exists_k5g_of_pow_three h3 h1
    refine ⟨Sum.inl i, ?_⟩
    rcases hi with hi | hi
    · left
      have : (⟨x, hxA⟩ : ↥A) = h.eA.symm (k5g i) := by rw [← hi]; simp
      simpa [gen] using congrArg Subtype.val this
    · right
      have : (⟨x, hxA⟩ : ↥A) = (h.eA.symm (k5g i))⁻¹ := by
        rw [← map_inv, ← hi]; simp
      simpa [gen] using congrArg Subtype.val this
  · have h3 : (h.eB ⟨x, hxB⟩) ^ 3 = 1 := by
      rw [← map_pow]
      have : (⟨x, hxB⟩ : ↥B) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
      rw [this, map_one]
    have h1 : h.eB ⟨x, hxB⟩ ≠ 1 := by
      intro h1
      apply hx1
      have : (⟨x, hxB⟩ : ↥B) = 1 := h.eB.injective (by simpa using h1)
      simpa using congrArg Subtype.val this
    obtain ⟨i, hi⟩ := exists_k5g_of_pow_three h3 h1
    refine ⟨Sum.inr i, ?_⟩
    rcases hi with hi | hi
    · left
      have : (⟨x, hxB⟩ : ↥B) = h.eB.symm (k5g i) := by rw [← hi]; simp
      simpa [gen] using congrArg Subtype.val this
    · right
      have : (⟨x, hxB⟩ : ↥B) = (h.eB.symm (k5g i))⁻¹ := by
        rw [← map_inv, ← hi]; simp
      simpa [gen] using congrArg Subtype.val this

theorem gen_eq_of {p q : Fin 4 ⊕ Fin 4} (hpq : h.gen p = h.gen q ∨ h.gen p = (h.gen q)⁻¹) :
    p = q := by
  have comm_of : ∀ x y : K, (x = y ∨ x = y⁻¹) → x * y = y * x := by
    intro x y hxy
    rcases hxy with e | e
    · rw [e]
    · rw [e]; group
  have mixed : ∀ x y : K, (x = y ∨ x = y⁻¹) → x ∈ A → y ∈ B → x ^ 3 = 1 → x ≠ 1 → False := by
    intro x y hxy hxA hyB hx3 hx1
    have hxB : x ∈ B := by
      rcases hxy with e | e
      · rw [e]; exact hyB
      · rw [e]; exact inv_mem hyB
    have hsq := h.inf_sq (show x ∈ A ⊓ B from ⟨hxA, hxB⟩)
    apply hx1
    have h1 : x ^ 3 = x * (x * x) := pow_three x
    rw [hsq, mul_one, hx3] at h1
    exact h1.symm
  rcases p with i | i <;> rcases q with j | j
  · have hc := comm_of _ _ hpq
    have h1 : (h.eA.symm (k5g i)) * (h.eA.symm (k5g j)) =
        (h.eA.symm (k5g j)) * (h.eA.symm (k5g i)) := Subtype.ext hc
    have h2 : k5g i * k5g j = k5g j * k5g i := by simpa using congrArg h.eA h1
    exact congrArg Sum.inl (comm_k5g h2)
  · exact (mixed _ _ hpq (h.gen_mem_A i) (h.gen_mem_B j) (h.gen_pow_three _)
      (h.gen_ne_one _)).elim
  · have hpq' : h.gen (Sum.inr i) ∈ A ∧ True := by
      refine ⟨?_, trivial⟩
      rcases hpq with e | e
      · rw [e]; exact h.gen_mem_A j
      · rw [e]; exact inv_mem (h.gen_mem_A j)
    have hsq := h.inf_sq (show h.gen (Sum.inr i) ∈ A ⊓ B from ⟨hpq'.1, h.gen_mem_B i⟩)
    have h1 : h.gen (Sum.inr i) ^ 3 =
        h.gen (Sum.inr i) * (h.gen (Sum.inr i) * h.gen (Sum.inr i)) := pow_three _
    rw [hsq, mul_one, h.gen_pow_three] at h1
    exact (h.gen_ne_one _ h1.symm).elim
  · have hc := comm_of _ _ hpq
    have h1 : (h.eB.symm (k5g i)) * (h.eB.symm (k5g j)) =
        (h.eB.symm (k5g j)) * (h.eB.symm (k5g i)) := Subtype.ext hc
    have h2 : k5g i * k5g j = k5g j * k5g i := by simpa using congrArg h.eB h1
    exact congrArg Sum.inr (comm_k5g h2)

theorem exists_decomp_pow_three {x : K} (hx : x ^ 3 = 1) :
    ∃ a ∈ A, ∃ b ∈ B, x = a * b ∧ a ^ 3 = 1 ∧ b ^ 3 = 1 := by
  obtain ⟨a0, ha0, b0, hb0, rfl⟩ := h.exists_mul x
  have hcomm : Commute a0 b0 := h.comm a0 ha0 b0 hb0
  have hab : a0 ^ 3 * b0 ^ 3 = 1 := by rw [← hcomm.mul_pow]; exact hx
  obtain ⟨ζ, hζ⟩ : ∃ ζ, ζ = a0 ^ 3 := ⟨_, rfl⟩
  have hζA : ζ ∈ A := hζ ▸ pow_mem ha0 3
  have hζb : ζ = (b0 ^ 3)⁻¹ := by rw [hζ]; exact eq_inv_of_mul_eq_one_left hab
  have hζB : ζ ∈ B := hζb ▸ inv_mem (pow_mem hb0 3)
  have hζ' : ζ ∈ A ⊓ B := ⟨hζA, hζB⟩
  have hsq : ζ * ζ = 1 := h.inf_sq hζ'
  have hcen : ∀ k : K, ζ * k = k * ζ := h.inf_central hζ'
  have hinv : ζ⁻¹ = ζ := inv_eq_of_mul_eq_one_right hsq
  refine ⟨a0 * ζ, mul_mem ha0 hζA, b0 * ζ, mul_mem hb0 hζB, ?_, ?_, ?_⟩
  · calc a0 * b0 = a0 * b0 * (ζ * ζ) := by rw [hsq, mul_one]
      _ = a0 * (b0 * ζ) * ζ := by group
      _ = a0 * (ζ * b0) * ζ := by rw [← hcen b0]
      _ = a0 * ζ * (b0 * ζ) := by group
  · have hc : Commute a0 ζ := by rw [hζ]; exact Commute.pow_right (Commute.refl a0) 3
    rw [hc.mul_pow, ← hζ]
    calc ζ * ζ ^ 3 = (ζ * ζ) * (ζ * ζ) := by rw [pow_three]; group
      _ = 1 := by rw [hsq, one_mul]
  · have hc : Commute b0 ζ := (hcen b0).symm
    rw [hc.mul_pow]
    have hb3 : b0 ^ 3 = ζ := by
      have : b0 ^ 3 = ζ⁻¹ := by rw [hζb, inv_inv]
      rw [this, hinv]
    rw [hb3]
    calc ζ * ζ ^ 3 = (ζ * ζ) * (ζ * ζ) := by rw [pow_three]; group
      _ = 1 := by rw [hsq, one_mul]

@[expose] noncomputable def embA : SL23 →* K := A.subtype.comp h.eA.symm.toMonoidHom

@[expose] noncomputable def embB : SL23 →* K := B.subtype.comp h.eB.symm.toMonoidHom

theorem embA_injective : Function.Injective h.embA :=
  Subtype.val_injective.comp h.eA.symm.injective

theorem embB_injective : Function.Injective h.embB :=
  Subtype.val_injective.comp h.eB.symm.injective

theorem embA_k5g (i : Fin 4) : h.embA (k5g i) = h.gen (Sum.inl i) := rfl

theorem embB_k5g (i : Fin 4) : h.embB (k5g i) = h.gen (Sum.inr i) := rfl

theorem embA_mem (s : SL23) : h.embA s ∈ A := (h.eA.symm s).2

theorem embB_mem (s : SL23) : h.embB s ∈ B := (h.eB.symm s).2

theorem exists_embA {a : K} (ha : a ∈ A) : ∃ s, h.embA s = a :=
  ⟨h.eA ⟨a, ha⟩, by simp [embA]⟩

theorem exists_embB {b : K} (hb : b ∈ B) : ∃ s, h.embB s = b :=
  ⟨h.eB ⟨b, hb⟩, by simp [embB]⟩

end SL23Pair

end CFSG.OddStandard.SmallF3.Omega.K5
