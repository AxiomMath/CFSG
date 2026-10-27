module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitAutL34Model

public section

namespace CFSG.ComponentClassification.HSFLit.AutL34

open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.ComponentClassification.GrSLit.L34Facts Subgroup

theorem card_le_two_mul {M : Type*} [Group M] [Finite M] {A C : Subgroup M}
    (h : ∀ a ∈ A, ∀ b ∈ A, a ∉ C → b ∉ C → a⁻¹ * b ∈ C) : Nat.card A ≤ 2 * Nat.card ↥(A ⊓ C) := by
  classical
  by_cases hA : ∃ a₀ ∈ A, a₀ ∉ C
  · obtain ⟨a₀, ha₀, ha₀C⟩ := hA
    let f : A → Bool × ↥(A ⊓ C) := fun a =>
      if ha : (a : M) ∈ C then (true, ⟨a, mem_inf.2 ⟨a.2, ha⟩⟩)
      else (false, ⟨a₀⁻¹ * a, mem_inf.2 ⟨A.mul_mem (A.inv_mem ha₀) a.2, h _ ha₀ _ a.2 ha₀C ha⟩⟩)
    have hf : Function.Injective f := by
      intro a b hab
      simp only [f] at hab
      by_cases ha : (a : M) ∈ C <;> by_cases hb : (b : M) ∈ C <;>
        simp only [ha, hb, dite_true, dite_false, Prod.mk.injEq, Bool.true_eq_false,
          Bool.false_eq_true, false_and] at hab
      · exact Subtype.ext (congrArg (fun x : ↥(A ⊓ C) => (x : M)) hab.2)
      · exact Subtype.ext (by simpa using congrArg (fun x : ↥(A ⊓ C) => (x : M)) hab.2)
    have := Nat.card_le_card_of_injective f hf
    rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at this
  · push Not at hA
    have : A ⊓ C = A := inf_eq_left.2 fun a ha => hA a ha
    rw [this]
    omega

theorem eq_of_card_eq_two {M : Type*} [Group M] {A : Subgroup M} (hA : Nat.card A = 2) {a b : M}
    (ha : a ∈ A) (hb : b ∈ A) (ha1 : a ≠ 1) (hb1 : b ≠ 1) : a = b := by
  have : Finite A := Nat.finite_of_card_ne_zero (by omega)
  by_contra hab
  let f : Fin 3 → A := ![1, ⟨a, ha⟩, ⟨b, hb⟩]
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [f, Subtype.ext_iff] at hij ⊢ <;>
      first | exact absurd hij.symm ha1 | exact absurd hij.symm hb1 | exact absurd hij ha1 |
        exact absurd hij hb1 | exact absurd hij hab | exact absurd hij.symm hab
  have := Nat.card_le_card_of_injective f hf
  rw [Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin] at this
  omega


theorem card_le_256 {X : Subgroup (Equiv.Perm (Fin 42))} (hXR : X ≤ R) (hX : IsPGroup 2 X) :
    Nat.card X ≤ 256 := by
  obtain ⟨c, -, hc⟩ := exists_conj_mem_TR hXR hX
  rw [← card_TR]
  exact Nat.card_le_card_of_injective (fun x : X => (⟨c * x * c⁻¹, hc x x.2⟩ : TR))
    fun x y h => Subtype.ext (by simpa using congrArg Subtype.val h)

theorem mem_center_of_half {X X₁ : Subgroup (Equiv.Perm (Fin 42))} (hXR : X ≤ R)
    (hX : IsPGroup 2 X) (hXS : Nat.card ↥(X ⊓ S) = 64) {y : Equiv.Perm (Fin 42)} (hy : y ∈ X)
    (hX₁ : X₁ ≤ X) (hcard : Nat.card X ≤ 2 * Nat.card X₁) (hX₁y : ∀ s ∈ X₁, s * y = y * s) :
    y ∈ S ∧ ∀ s ∈ X ⊓ S, y * s = s * y := by
  obtain ⟨c, -, hc, hiff, -⟩ := exists_std hXR hX hXS
  have hrel : X₁.relIndex X ≤ 2 := by
    have h := relIndex_mul_card X₁ X
    rw [inf_eq_left.2 hX₁] at h
    have hpos : 0 < Nat.card X₁ := Nat.card_pos
    nlinarith
  have hne : X₁.relIndex X ≠ 0 := by
    intro h0
    have h := relIndex_mul_card X₁ X
    rw [h0, zero_mul] at h
    exact Nat.card_pos.ne' h.symm
  have hrel' : X₁.relIndex (X ⊓ S) ≤ 2 := (relIndex_le_of_le_right inf_le_left hne).trans hrel
  have h32 : 32 ≤ Nat.card ↥(X₁ ⊓ (X ⊓ S)) := by
    have h := relIndex_mul_card X₁ (X ⊓ S)
    rw [hXS] at h
    nlinarith
  have hcnt : 32 ≤ Nat.card {t // t ∈ T0 ∧ t * (c * y * c⁻¹) = c * y * c⁻¹ * t} := by
    refine h32.trans (Nat.card_le_card_of_injective (fun s : ↥(X₁ ⊓ (X ⊓ S)) =>
      (⟨c * s * c⁻¹, (hiff s (mem_inf.1 (mem_inf.1 s.2).2).1).1 (mem_inf.1 (mem_inf.1 s.2).2).2,
        by rw [show c * s * c⁻¹ * (c * y * c⁻¹) = c * (s * y) * c⁻¹ by group,
          hX₁y _ (mem_inf.1 s.2).1]; group⟩ :
        {t // t ∈ T0 ∧ t * (c * y * c⁻¹) = c * y * c⁻¹ * t})) fun s s' h => ?_)
    exact Subtype.ext (by simpa using congrArg Subtype.val h)
  obtain ⟨hyT, hyc⟩ := mem_center_of_le_card (hc y hy) hcnt
  refine ⟨(hiff y hy).2 hyT, fun s hs => ?_⟩
  have h1 := hyc _ ((hiff s (mem_inf.1 hs).1).1 (mem_inf.1 hs).2)
  rw [show c * y * c⁻¹ * (c * s * c⁻¹) = c * (y * s) * c⁻¹ by group,
    show c * s * c⁻¹ * (c * y * c⁻¹) = c * (s * y) * c⁻¹ by group] at h1
  simpa using h1

theorem mem_of_center {X E : Subgroup (Equiv.Perm (Fin 42))} (hXR : X ≤ R) (hX : IsPGroup 2 X)
    (hXS : Nat.card ↥(X ⊓ S) = 64) (hEX : E ≤ X)
    (hEn : X ≤ normalizer (E : Set (Equiv.Perm (Fin 42))))
    (hE2 : ∀ e ∈ E, e * e = 1) (h8 : 8 ≤ Nat.card E)
    {z : Equiv.Perm (Fin 42)} (hz : z ∈ X ⊓ S) (hzc : ∀ s ∈ X ⊓ S, z * s = s * z) : z ∈ E := by
  obtain ⟨c, hcR, hc, hiff, hsurj⟩ := exists_std hXR hX hXS
  have hconjE : ∀ s ∈ X, ∀ e ∈ E, s * e * s⁻¹ ∈ E := fun s hs e he =>
    (mem_normalizer_iff.1 (hEn hs) e).1 he
  have hzT : c * z * c⁻¹ ∈ T0 := (hiff z (mem_inf.1 hz).1).1 (mem_inf.1 hz).2
  have hzc' : ∀ t ∈ T0, c * z * c⁻¹ * t = t * (c * z * c⁻¹) := by
    intro t ht
    obtain ⟨s, hs, rfl⟩ := hsurj t ht
    rw [show c * z * c⁻¹ * (c * s * c⁻¹) = c * (z * s) * c⁻¹ by group, hzc s hs]
    group
  by_contra hzE
  by_cases hA : ∃ e ∈ E, e ∈ S ∧ ¬ ∀ t ∈ T0, c * e * c⁻¹ * t = t * (c * e * c⁻¹)
  · obtain ⟨e, he, heS, hne⟩ := hA
    have heT : c * e * c⁻¹ ∈ T0 := (hiff e (hEX he)).1 heS
    have he2 : c * e * c⁻¹ * (c * e * c⁻¹) = 1 := by
      rw [show c * e * c⁻¹ * (c * e * c⁻¹) = c * (e * e) * c⁻¹ by group, hE2 e he]
      group
    obtain ⟨t, ht, hte⟩ := exists_mul_eq_mul heT he2 hne hzT hzc'
    obtain ⟨s, hs, rfl⟩ := hsurj t ht
    have h1 : s * e = e * z * s := by
      have := hte
      rw [show c * s * c⁻¹ * (c * e * c⁻¹) = c * (s * e) * c⁻¹ by group,
        show c * e * c⁻¹ * (c * z * c⁻¹) * (c * s * c⁻¹) = c * (e * z * s) * c⁻¹ by group]
        at this
      simpa using this
    apply hzE
    have : z = e⁻¹ * (s * e * s⁻¹) := by
      rw [show s * e = e * z * s from h1]
      group
    rw [this]
    exact E.mul_mem (E.inv_mem he) (hconjE s (mem_inf.1 hs).1 e he)
  · push Not at hA
    have hES : Nat.card ↥(E ⊓ S) ≤ 2 := by
      have hinj : Nat.card (↥(E ⊓ S) ⊕ Unit) ≤
          Nat.card {t // t ∈ T0 ∧ ∀ s ∈ T0, t * s = s * t} := by
        refine Nat.card_le_card_of_injective (fun x => match x with
          | Sum.inl e => ⟨c * e * c⁻¹, (hiff e (hEX (mem_inf.1 e.2).1)).1 (mem_inf.1 e.2).2,
              hA e (mem_inf.1 e.2).1 (mem_inf.1 e.2).2⟩
          | Sum.inr _ => ⟨c * z * c⁻¹, hzT, hzc'⟩) ?_
        rintro (e | u) (e' | u') h <;> simp only [Subtype.mk.injEq] at h
        · exact congrArg Sum.inl (Subtype.ext (by simpa using h))
        · exact absurd (by simpa using h : (e : Equiv.Perm (Fin 42)) = z) fun h' =>
            hzE (h' ▸ (mem_inf.1 e.2).1)
        · exact absurd (by simpa using h : z = (e' : Equiv.Perm (Fin 42))) fun h' =>
            hzE (h' ▸ (mem_inf.1 e'.2).1)
        · rfl
      have hu : Nat.card Unit = 1 := Nat.card_unique
      rw [Nat.card_sum, card_center_T0, hu] at hinj
      have hp : IsPGroup 2 ↥(E ⊓ S) := (hX.to_le hEX).to_le inf_le_left
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨k, hk⟩ := hp.exists_card_eq
      rw [hk] at hinj ⊢
      have hk1 : k ≤ 1 := by
        by_contra hk1
        have : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      interval_cases k <;> norm_num
    have hE4 : Nat.card E ≤ 4 * Nat.card ↥(E ⊓ S) := by
      have h1 := relIndex_mul_card S E
      have h2 := relIndex_mul_card S X
      rw [inf_comm] at h1 h2
      rw [hXS] at h2
      have hne : S.relIndex X ≠ 0 := by
        intro h0
        rw [h0, zero_mul] at h2
        exact Nat.card_pos.ne' h2.symm
      have h3 := relIndex_le_of_le_right hEX hne
      have h4 := card_le_256 hXR hX
      have h5 : S.relIndex X ≤ 4 := by nlinarith
      rw [← h1]
      calc S.relIndex E * Nat.card ↥(E ⊓ S) ≤ 4 * Nat.card ↥(E ⊓ S) :=
            Nat.mul_le_mul_right _ (h3.trans h5)
        _ = 4 * Nat.card ↥(E ⊓ S) := rfl
    have hES2 : Nat.card ↥(E ⊓ S) = 2 := by omega
    obtain ⟨e, he, heS⟩ : ∃ e ∈ E, e ∉ S := by
      by_contra hall
      push Not at hall
      have : E ⊓ S = E := inf_eq_left.2 hall
      rw [this] at hES2
      omega
    have hcomm : ∀ s ∈ X ⊓ S, e⁻¹ * (s * e * s⁻¹) ∈ E ⊓ S := by
      intro s hs
      refine mem_inf.2 ⟨E.mul_mem (E.inv_mem he) (hconjE s (mem_inf.1 hs).1 e he), ?_⟩
      have heR : e⁻¹ ∈ R := R.inv_mem (hXR (hEX he))
      have h1 : e⁻¹ * s * e⁻¹⁻¹ ∈ S := conj_mem_S heR (mem_inf.1 hs).2
      rw [show e⁻¹ * (s * e * s⁻¹) = e⁻¹ * s * e⁻¹⁻¹ * s⁻¹ by group]
      exact S.mul_mem h1 (S.inv_mem (mem_inf.1 hs).2)
    have hhalf := card_le_two_mul (A := X ⊓ S) (C := centralizer {e}) fun a ha b hb haC hbC => by
      rw [mem_centralizer_singleton_iff] at haC hbC ⊢
      have hua : e⁻¹ * (a * e * a⁻¹) ≠ 1 := fun h1 => haC (by
        rw [inv_mul_eq_one] at h1
        calc a * e = a * e * a⁻¹ * a := by group
          _ = e * a := by rw [← h1])
      have hub : e⁻¹ * (b * e * b⁻¹) ≠ 1 := fun h1 => hbC (by
        rw [inv_mul_eq_one] at h1
        calc b * e = b * e * b⁻¹ * b := by group
          _ = e * b := by rw [← h1])
      have heq := eq_of_card_eq_two hES2 (hcomm a ha) (hcomm b hb) hua hub
      have heq' : a * e * a⁻¹ = b * e * b⁻¹ := by simpa using heq
      calc a⁻¹ * b * e = a⁻¹ * (b * e * b⁻¹) * b := by group
        _ = a⁻¹ * (a * e * a⁻¹) * b := by rw [heq']
        _ = e * (a⁻¹ * b) := by group
    rw [hXS] at hhalf
    have hcnt : 32 ≤ Nat.card {t // t ∈ T0 ∧ t * (c * e * c⁻¹) = c * e * c⁻¹ * t} := by
      refine le_trans (by omega) (Nat.card_le_card_of_injective
        (fun s : ↥(X ⊓ S ⊓ centralizer {e}) =>
          (⟨c * s * c⁻¹, (hiff s (mem_inf.1 (mem_inf.1 s.2).1).1).1
            (mem_inf.1 (mem_inf.1 s.2).1).2, by
            rw [show c * s * c⁻¹ * (c * e * c⁻¹) = c * (s * e) * c⁻¹ by group,
              mem_centralizer_singleton_iff.1 (mem_inf.1 s.2).2]
            group⟩ : {t // t ∈ T0 ∧ t * (c * e * c⁻¹) = c * e * c⁻¹ * t}))
        fun s s' h => Subtype.ext (by simpa using congrArg Subtype.val h))
    exact heS ((hiff e (hEX he)).2 (mem_center_of_le_card (hc e (hEX he)) hcnt).1)

theorem card_le_two_of_normal {X D : Subgroup (Equiv.Perm (Fin 42))} (hXR : X ≤ R)
    (hX : IsPGroup 2 X) (hXS : Nat.card ↥(X ⊓ S) = 64) (hDX : D ≤ X)
    (hDn : X ≤ normalizer (D : Set (Equiv.Perm (Fin 42))))
    (hD : ∀ d ∈ D, ∀ e ∈ D, d * d = 1 → e * e = 1 → d = 1 ∨ e = 1 ∨ d = e) :
    Nat.card D ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra h2
  push Not at h2
  obtain ⟨d, hd, hd2⟩ : ∃ d ∈ D, d * d ≠ 1 := by
    by_contra hall
    push Not at hall
    by_cases h1 : ∃ d₀ ∈ D, d₀ ≠ 1
    · obtain ⟨d₀, hd₀, hd₀1⟩ := h1
      have hmem : ∀ d : D, (d : Equiv.Perm (Fin 42)) = 1 ∨ (d : Equiv.Perm (Fin 42)) = d₀ := by
        intro d
        rcases hD d d.2 d₀ hd₀ (hall d d.2) (hall d₀ hd₀) with h | h | h
        · exact Or.inl h
        · exact absurd h hd₀1
        · exact Or.inr h
      have hinj := Nat.card_le_card_of_injective
        (fun d : D => decide ((d : Equiv.Perm (Fin 42)) = 1)) fun a b hab => by
          apply Subtype.ext
          rcases hmem a with ha | ha <;> rcases hmem b with hb | hb
          · rw [ha, hb]
          · exfalso
            simp [ha, hb, hd₀1] at hab
          · exfalso
            simp [ha, hb, hd₀1] at hab
          · rw [ha, hb]
      rw [Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at hinj
      omega
    · push Not at h1
      have : D = ⊥ := (eq_bot_iff_forall D).2 h1
      rw [this, card_bot] at h2
      omega
  have hD2 : IsPGroup 2 D := hX.to_le hDX
  obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.1 hD2) ⟨d, hd⟩
  rw [orderOf_mk] at hm
  have hm2 : 2 ≤ m := by
    by_contra hm2
    apply hd2
    have h2' : d ^ 2 = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one, hm]
      exact (Nat.pow_dvd_pow 2 (by omega : m ≤ 1)).trans (by norm_num)
    rwa [pow_two] at h2'
  have h4 : 4 ∣ orderOf d := by
    rw [hm]
    exact (Nat.pow_dvd_pow 2 hm2)
  have hne : orderOf d ≠ 0 := by rw [hm]; positivity
  set y := d ^ (orderOf d / 4) with hy
  have hyo : orderOf y = 4 := orderOf_pow_orderOf_div hne h4
  have hyD : y ∈ D := D.pow_mem hd _
  have hy4 : y * y * (y * y) = 1 := by
    rw [← pow_two, ← pow_two, ← pow_mul, show 2 * 2 = orderOf y by rw [hyo]]
    exact pow_orderOf_eq_one y
  have hy2 : y * y ≠ 1 := by
    intro h
    have := orderOf_dvd_of_pow_eq_one (show y ^ 2 = 1 by rw [pow_two]; exact h)
    rw [hyo] at this
    omega
  obtain ⟨c, -, hc, -, hsurj⟩ := exists_std hXR hX hXS
  have hconj : ∀ s ∈ X, s * y * s⁻¹ ∈ D := fun s hs => (mem_normalizer_iff.1 (hDn hs) y).1 hyD
  have hy4' : c * y * c⁻¹ * (c * y * c⁻¹) * (c * y * c⁻¹ * (c * y * c⁻¹)) = 1 := by
    rw [show c * y * c⁻¹ * (c * y * c⁻¹) * (c * y * c⁻¹ * (c * y * c⁻¹)) =
      c * (y * y * (y * y)) * c⁻¹ by group, hy4]
    group
  have hy2' : c * y * c⁻¹ * (c * y * c⁻¹) ≠ 1 := by
    rw [show c * y * c⁻¹ * (c * y * c⁻¹) = c * (y * y) * c⁻¹ by group]
    intro h
    apply hy2
    have := congrArg (fun g => c⁻¹ * g * c) h
    simpa [mul_assoc] using this
  obtain ⟨w, hw, hw2, hw1, hwy⟩ := exists_other_involution (hc y (hDX hyD)) hy4' hy2'
  have hwD : c⁻¹ * w * c ∈ D := by
    rcases hw with ⟨t, ht, rfl⟩ | ⟨t, ht, t', ht', rfl⟩
    · obtain ⟨s, hs, rfl⟩ := hsurj t ht
      rw [show c⁻¹ * (c * y * c⁻¹ * (c * s * c⁻¹ * (c * y * c⁻¹) * (c * s * c⁻¹)⁻¹)) * c =
        y * (s * y * s⁻¹) by group]
      exact D.mul_mem hyD (hconj s (mem_inf.1 hs).1)
    · obtain ⟨s, hs, rfl⟩ := hsurj t ht
      obtain ⟨s', hs', rfl⟩ := hsurj t' ht'
      rw [show c⁻¹ * (c * y * c⁻¹ * (c * s * c⁻¹ * (c * y * c⁻¹) * (c * s * c⁻¹)⁻¹) *
        (c * s' * c⁻¹ * (c * y * c⁻¹) * (c * s' * c⁻¹)⁻¹)) * c =
        y * (s * y * s⁻¹) * (s' * y * s'⁻¹) by group]
      exact D.mul_mem (D.mul_mem hyD (hconj s (mem_inf.1 hs).1)) (hconj s' (mem_inf.1 hs').1)
  have hw2' : c⁻¹ * w * c * (c⁻¹ * w * c) = 1 := by
    rw [show c⁻¹ * w * c * (c⁻¹ * w * c) = c⁻¹ * (w * w) * c by group, hw2]
    group
  rcases hD _ hwD _ (D.mul_mem hyD hyD) hw2' hy4 with h | h | h
  · apply hw1
    have := congrArg (fun g => c * g * c⁻¹) h
    simpa [mul_assoc] using this
  · exact hy2 h
  · apply hwy
    have := congrArg (fun g => c * g * c⁻¹) h
    simp only [mul_assoc, mul_inv_cancel, mul_one, mul_inv_cancel_left] at this
    rw [this]
    group

end CFSG.ComponentClassification.HSFLit.AutL34
