module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QOGen

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P51Q

open CFSG Subgroup Matrix

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

omit [Fintype ι] in
theorem eq_zero_of_smul_one_add_smul [Nonempty ι] {A : Matrix ι ι K}
    (hA : ∀ c : K, A ≠ c • 1) {α β : K} (h : α • (1 : Matrix ι ι K) + β • A = 0) :
    α = 0 ∧ β = 0 := by
  by_cases hβ : β = 0
  · subst hβ
    rw [zero_smul, add_zero] at h
    obtain ⟨i⟩ := ‹Nonempty ι›
    have e := congrFun (congrFun h i) i
    simpa using e
  · exfalso
    apply hA (-α / β)
    have e : β • A = -(α • (1 : Matrix ι ι K)) := eq_neg_of_add_eq_zero_right h
    calc A = β⁻¹ • (β • A) := by rw [smul_smul, inv_mul_cancel₀ hβ, one_smul]
      _ = (-α / β) • 1 := by rw [e, smul_neg, smul_smul, ← neg_smul]; congr 1; ring

theorem rot_mul_rot {A : Matrix ι ι K} (hA : A * A = -1) (x y x' y' : K) :
    (x • (1 : Matrix ι ι K) + y • A) * (x' • 1 + y' • A) =
      (x * x' - y * y') • 1 + (x * y' + y * x') • A := by
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one, hA]
  module

theorem anti_mul_rot {A N : Matrix ι ι K} (hN : N * A = -(A * N)) (x y : K) :
    N * (x • (1 : Matrix ι ι K) + y • A) = (x • 1 + (-y) • A) * N := by
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one, hN, neg_smul, smul_neg, Matrix.neg_mul]

theorem famF_concl_skew [Nonempty ι] (h2 : (2 : K) ≠ 0) {S : Subgroup (GL ι K)} {X : Type}
    [Group X] [Finite X] (π : S →* X) (hπ : Function.Surjective π)
    (hker : ∀ s, π s = 1 → ((s : GL ι K) : Matrix ι ι K) = 1 ∨ ((s : GL ι K) : Matrix ι ι K) = -1)
    {a : S} (ha : ((a : GL ι K) : Matrix ι ι K) * ((a : GL ι K) : Matrix ι ι K) = -1)
    (hans : ∀ c : K, ((a : GL ι K) : Matrix ι ι K) ≠ c • 1) (hz2 : π a * π a = 1)
    {T : Subgroup S}
    (hTU : ∀ s ∈ T, ((s : GL ι K) : Matrix ι ι K) * ((a : GL ι K) : Matrix ι ι K) =
        ((a : GL ι K) : Matrix ι ι K) * ((s : GL ι K) : Matrix ι ι K) →
      ∃ x y : K, x ^ 2 + y ^ 2 = 1 ∧
        ((s : GL ι K) : Matrix ι ι K) = x • 1 + y • ((a : GL ι K) : Matrix ι ι K))
    {P : Subgroup X} (h8 : Nat.card P = 8) (hPC : P ≤ centralizer ({π a} : Set X))
    (hPT : ∀ g ∈ P, ∀ s, π s = g → s ∈ T) :
    ¬ ((∃ u ∈ P, ∃ v ∈ P, u * v ≠ v * u) ∧ ∀ q ∈ P, q * q = 1 → q = 1 ∨ q = π a) ∧
      ¬ ∀ q ∈ P, q * q = 1 := by
  classical
  set Ma := ((a : GL ι K) : Matrix ι ι K) with hMa
  have hinj : Function.Injective (fun s : S => ((s : GL ι K) : Matrix ι ι K)) :=
    fun s t h => Subtype.ext (Units.ext h)
  have hcoe_mul : ∀ s t : S, ((s * t : S) : GL ι K) = (s : GL ι K) * t := fun _ _ => rfl
  have hMa0 : Ma ≠ 0 := by
    intro h0
    obtain ⟨i⟩ := ‹Nonempty ι›
    have e := congrFun (congrFun ha i) i
    rw [h0, Matrix.zero_mul] at e
    simp at e
  have hcancel : ∀ (s : S) (U V : Matrix ι ι K), U * ((s : GL ι K) : Matrix ι ι K) =
      V * ((s : GL ι K) : Matrix ι ι K) → U = V := by
    intro s U V h
    exact (Units.isUnit ((s : S) : GL ι K)).mul_left_inj.1 h
  have haa : ((((a * a : S) : GL ι K)) : Matrix ι ι K) = -1 := ha
  have hπaa : π (a * a) = 1 := by rw [map_mul, hz2]
  set ℓ := Function.surjInv hπ with hℓdef
  have hℓ : ∀ g, π (ℓ g) = g := Function.surjInv_eq hπ
  have hsign : ∀ g ∈ P, ∀ s : S, π s = g →
      ((s : GL ι K) : Matrix ι ι K) * Ma = Ma * ((s : GL ι K) : Matrix ι ι K) ∨
        ((s : GL ι K) : Matrix ι ι K) * Ma = -(Ma * ((s : GL ι K) : Matrix ι ι K)) := by
    intro g hg s hs
    have hc : π (s * a * s⁻¹ * a⁻¹) = 1 := by
      have hga := mem_centralizer_singleton_iff.1 (hPC hg)
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hs, hga]
      group
    have e3 : ((s : GL ι K) : Matrix ι ι K) * Ma =
        ((((s * a * s⁻¹ * a⁻¹ : S) : GL ι K)) : Matrix ι ι K) *
          (Ma * ((s : GL ι K) : Matrix ι ι K)) := by
      have e2 : (s * a * s⁻¹ * a⁻¹) * (a * s) = s * a := by group
      calc ((s : GL ι K) : Matrix ι ι K) * Ma = ((((s * a : S) : GL ι K)) : Matrix ι ι K) := rfl
        _ = (((((s * a * s⁻¹ * a⁻¹) * (a * s) : S) : GL ι K)) : Matrix ι ι K) := by rw [e2]
        _ = _ := rfl
    rcases hker _ hc with h | h
    · left
      rw [e3, h, Matrix.one_mul]
    · right
      rw [e3, h, Matrix.neg_mul, Matrix.one_mul]
  have hnot : ∀ s : S, (π s = 1 ∨ π s = π a) →
      ((s : GL ι K) : Matrix ι ι K) * Ma = -(Ma * ((s : GL ι K) : Matrix ι ι K)) → False := by
    intro s hs hanti
    have hcomm : ((s : GL ι K) : Matrix ι ι K) * Ma = Ma * ((s : GL ι K) : Matrix ι ι K) := by
      have hk : ∀ t : S, π t = 1 → ((t : GL ι K) : Matrix ι ι K) * Ma =
          Ma * ((t : GL ι K) : Matrix ι ι K) := by
        intro t ht
        rcases hker t ht with h | h <;> rw [h] <;> simp
      rcases hs with hs | hs
      · exact hk s hs
      · have h1 : π (s * a⁻¹) = 1 := by rw [map_mul, map_inv, hs, mul_inv_cancel]
        have e : s = (s * a⁻¹) * a := by group
        have h3 := hk _ h1
        rw [e, hcoe_mul, Units.val_mul, ← Matrix.mul_assoc Ma, ← h3]
    have h0 : (2 : K) • (Ma * ((s : GL ι K) : Matrix ι ι K)) = 0 := by
      rw [two_smul]
      nth_rewrite 1 [← hcomm]
      rw [hanti, neg_add_cancel]
    have h0' : Ma * ((s : GL ι K) : Matrix ι ι K) = 0 := (smul_eq_zero.1 h0).resolve_left h2
    exact hMa0 (hcancel s Ma 0 (by rw [h0', Matrix.zero_mul]))
  have hsqA : ∀ s ∈ T, ((s : GL ι K) : Matrix ι ι K) * Ma = -(Ma * ((s : GL ι K) : Matrix ι ι K)) →
      π (s * s) = 1 := by
    intro s hs hanti
    have hss : ((((s * s : S) : GL ι K)) : Matrix ι ι K) * Ma =
        Ma * ((((s * s : S) : GL ι K)) : Matrix ι ι K) := by
      rw [hcoe_mul, Units.val_mul, Matrix.mul_assoc, hanti, Matrix.mul_neg, ← Matrix.mul_assoc,
        hanti, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
    obtain ⟨x, y, hxy, hxy'⟩ := hTU _ (mul_mem hs hs) hss
    have e1 : ((s : GL ι K) : Matrix ι ι K) * ((((s * s : S) : GL ι K)) : Matrix ι ι K) =
        ((((s * s : S) : GL ι K)) : Matrix ι ι K) * ((s : GL ι K) : Matrix ι ι K) := by
      rw [hcoe_mul, Units.val_mul, Matrix.mul_assoc]
    rw [hxy', anti_mul_rot hanti] at e1
    have e2 : (x • (1 : Matrix ι ι K) + (-y) • Ma) = x • 1 + y • Ma :=
      hcancel s _ _ e1
    have e3 : (-y) • Ma = y • Ma := add_left_cancel e2
    have e4 : (2 * y) • Ma = 0 := by
      rw [show (2 * y) • Ma = y • Ma - (-y) • Ma by rw [neg_smul, sub_neg_eq_add, ← add_smul,
        two_mul], e3, sub_self]
    have hy : y = 0 := by
      rcases smul_eq_zero.1 e4 with h | h
      · exact (mul_eq_zero.1 h).resolve_left h2
      · exact absurd h hMa0
    rw [hy, zero_smul, add_zero] at hxy'
    rw [hy, zero_pow two_ne_zero, add_zero] at hxy
    rcases mul_self_eq_one_iff.1 (show x * x = 1 by rw [← sq]; exact hxy) with hx | hx
    · have : s * s = 1 := hinj (by
        change ((((s * s : S) : GL ι K)) : Matrix ι ι K) = (((1 : S) : GL ι K) : Matrix ι ι K)
        rw [hxy', hx, one_smul]
        rfl)
      rw [this, map_one]
    · have : s * s = a * a := hinj (by
        change ((((s * s : S) : GL ι K)) : Matrix ι ι K) = ((((a * a : S) : GL ι K)) : Matrix ι ι K)
        rw [hxy', hx, haa, neg_one_smul])
      rw [this, hπaa]
  have hcoef : ∀ α β ε : K, α • (1 : Matrix ι ι K) + β • Ma = ε • 1 → α = ε ∧ β = 0 := by
    intro α β ε h
    have h' : (α - ε) • (1 : Matrix ι ι K) + β • Ma = 0 := by
      rw [sub_smul, show α • (1 : Matrix ι ι K) - ε • 1 + β • Ma = (α • 1 + β • Ma) - ε • 1 by
        abel, h, sub_self]
    obtain ⟨h1, h2'⟩ := eq_zero_of_smul_one_add_smul hans h'
    exact ⟨sub_eq_zero.1 h1, h2'⟩
  refine ⟨fun ⟨⟨u, hu, v, hv, huv⟩, huniq⟩ => ?_, fun hall => ?_⟩
  ·
    have hanti_false : ∀ t ∈ P, ((ℓ t : GL ι K) : Matrix ι ι K) * Ma =
        -(Ma * ((ℓ t : GL ι K) : Matrix ι ι K)) → False := by
      intro t ht hanti
      have h1 := hsqA (ℓ t) (hPT t ht _ (hℓ t)) hanti
      rw [map_mul, hℓ] at h1
      exact hnot (ℓ t) (by rw [hℓ]; exact huniq t ht h1) hanti
    rcases hsign u hu (ℓ u) (hℓ u) with hcu | hcu
    · rcases hsign v hv (ℓ v) (hℓ v) with hcv | hcv
      · obtain ⟨x, y, -, hu'⟩ := hTU _ (hPT u hu _ (hℓ u)) hcu
        obtain ⟨x', y', -, hv'⟩ := hTU _ (hPT v hv _ (hℓ v)) hcv
        apply huv
        rw [← hℓ u, ← hℓ v, ← map_mul, ← map_mul]
        congr 1
        apply hinj
        change ((ℓ u : GL ι K) : Matrix ι ι K) * ((ℓ v : GL ι K) : Matrix ι ι K) =
          ((ℓ v : GL ι K) : Matrix ι ι K) * ((ℓ u : GL ι K) : Matrix ι ι K)
        rw [hu', hv', rot_mul_rot ha, rot_mul_rot ha]
        module
      · exact hanti_false v hv hcv
    · exact hanti_false u hu hcu
  ·
    have hsq : ∀ g ∈ P, ∀ s : S, π s = g → π (s * s) = 1 := fun g hg s hs => by
      rw [map_mul, hs, hall g hg]
    have hrot : ∀ g ∈ P, ∀ s : S, π s = g →
        ((s : GL ι K) : Matrix ι ι K) * Ma = Ma * ((s : GL ι K) : Matrix ι ι K) →
          ((s : GL ι K) : Matrix ι ι K) = 1 ∨ ((s : GL ι K) : Matrix ι ι K) = -1 ∨
            ((s : GL ι K) : Matrix ι ι K) = Ma ∨ ((s : GL ι K) : Matrix ι ι K) = -Ma := by
      intro g hg s hs hc
      obtain ⟨x, y, hxy, hs'⟩ := hTU s (hPT g hg s hs) hc
      have hss : ((((s * s : S) : GL ι K)) : Matrix ι ι K) =
          (x * x - y * y) • 1 + (x * y + y * x) • Ma := by
        rw [hcoe_mul, Units.val_mul, hs', rot_mul_rot ha]
      have hxy0 : x * y + y * x = 0 := by
        rcases hker _ (hsq g hg s hs) with h | h
        · rw [hss] at h
          exact (hcoef _ _ 1 (by rw [h, one_smul])).2
        · rw [hss] at h
          exact (hcoef _ _ (-1) (by rw [h, neg_one_smul])).2
      have hxy1 : x * y = 0 := by
        have : (2 : K) * (x * y) = 0 := by linear_combination hxy0
        exact (mul_eq_zero.1 this).resolve_left h2
      rcases mul_eq_zero.1 hxy1 with hx | hy
      · rw [hx, zero_pow two_ne_zero, zero_add] at hxy
        rcases mul_self_eq_one_iff.1 (show y * y = 1 by rw [← sq]; exact hxy) with h | h
        · right; right; left
          rw [hs', hx, h, zero_smul, zero_add, one_smul]
        · right; right; right
          rw [hs', hx, h, zero_smul, zero_add, neg_one_smul]
      · rw [hy, zero_pow two_ne_zero, add_zero] at hxy
        rcases mul_self_eq_one_iff.1 (show x * x = 1 by rw [← sq]; exact hxy) with h | h
        · left
          rw [hs', hy, h, zero_smul, add_zero, one_smul]
        · right; left
          rw [hs', hy, h, zero_smul, add_zero, neg_one_smul]
    obtain ⟨s₀, hs₀⟩ : ∃ s₀ : S, ∀ g ∈ P, ∀ s : S, π s = g →
        ((s : GL ι K) : Matrix ι ι K) * Ma = -(Ma * ((s : GL ι K) : Matrix ι ι K)) →
          ((s : GL ι K) : Matrix ι ι K) = ((s₀ : GL ι K) : Matrix ι ι K) ∨
            ((s : GL ι K) : Matrix ι ι K) = -((s₀ : GL ι K) : Matrix ι ι K) ∨
              ((s : GL ι K) : Matrix ι ι K) = Ma * ((s₀ : GL ι K) : Matrix ι ι K) ∨
                ((s : GL ι K) : Matrix ι ι K) = -(Ma * ((s₀ : GL ι K) : Matrix ι ι K)) := by
      by_cases hB : ∃ g₀ ∈ P, ∃ s₀ : S, π s₀ = g₀ ∧
          ((s₀ : GL ι K) : Matrix ι ι K) * Ma = -(Ma * ((s₀ : GL ι K) : Matrix ι ι K))
      · obtain ⟨g₀, hg₀, s₀, hs₀π, hs₀a⟩ := hB
        refine ⟨s₀, fun g hg s hs hanti => ?_⟩
        have hwc : ((((s * s₀ : S) : GL ι K)) : Matrix ι ι K) * Ma =
            Ma * ((((s * s₀ : S) : GL ι K)) : Matrix ι ι K) := by
          rw [hcoe_mul, Units.val_mul, Matrix.mul_assoc, hs₀a, Matrix.mul_neg, ← Matrix.mul_assoc,
            hanti, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
        have hw := hrot (g * g₀) (mul_mem hg hg₀) (s * s₀) (by rw [map_mul, hs, hs₀π]) hwc
        have hw' : ((((s * s₀ : S) : GL ι K)) : Matrix ι ι K) * ((s₀ : GL ι K) : Matrix ι ι K) =
            ((s : GL ι K) : Matrix ι ι K) * ((((s₀ * s₀ : S) : GL ι K)) : Matrix ι ι K) := by
          rw [hcoe_mul, Units.val_mul, hcoe_mul, Units.val_mul, Matrix.mul_assoc]
        rcases hker _ (hsq g₀ hg₀ s₀ hs₀π) with h0 | h0
        · rw [h0, Matrix.mul_one] at hw'
          rcases hw with h | h | h | h <;> rw [h] at hw' <;> rw [← hw'] <;> simp
        · rw [h0, Matrix.mul_neg, Matrix.mul_one] at hw'
          have hs' : ((s : GL ι K) : Matrix ι ι K) =
              -(((((s * s₀ : S) : GL ι K)) : Matrix ι ι K) * ((s₀ : GL ι K) : Matrix ι ι K)) := by
            rw [hw', neg_neg]
          rcases hw with h | h | h | h <;> rw [h] at hs' <;> rw [hs'] <;> simp
      · exact ⟨1, fun g hg s hs hanti => absurd ⟨g, hg, s, hs, hanti⟩ hB⟩
    set T₄ : Finset (Matrix ι ι K) := {1, Ma, ((s₀ : GL ι K) : Matrix ι ι K),
      Ma * ((s₀ : GL ι K) : Matrix ι ι K)} with hT₄
    have hmem : ∀ g ∈ P, ∃ s : S, π s = g ∧ ((s : GL ι K) : Matrix ι ι K) ∈ T₄ := by
      intro g hg
      have hcases : ((ℓ g : GL ι K) : Matrix ι ι K) ∈ T₄ ∨
          -((ℓ g : GL ι K) : Matrix ι ι K) ∈ T₄ := by
        rcases hsign g hg (ℓ g) (hℓ g) with hc | hc
        · rcases hrot g hg _ (hℓ g) hc with h | h | h | h <;> simp [hT₄, h]
        · rcases hs₀ g hg _ (hℓ g) hc with h | h | h | h <;> simp [hT₄, h]
      rcases hcases with h | h
      · exact ⟨ℓ g, hℓ g, h⟩
      · refine ⟨a * a * ℓ g, by rw [map_mul, hπaa, one_mul, hℓ], ?_⟩
        have e : ((((a * a * ℓ g : S) : GL ι K)) : Matrix ι ι K) =
            -((ℓ g : GL ι K) : Matrix ι ι K) := by
          rw [hcoe_mul, Units.val_mul, haa, neg_one_mul]
        rw [e]
        exact h
    have hcard := card_le_of_forall_lift_mem π hinj T₄ hmem
    have h4 : T₄.card ≤ 4 := by
      have e1 := Finset.card_insert_le (1 : Matrix ι ι K)
        ({Ma, ((s₀ : GL ι K) : Matrix ι ι K), Ma * ((s₀ : GL ι K) : Matrix ι ι K)} : Finset _)
      have e2 := Finset.card_insert_le Ma
        ({((s₀ : GL ι K) : Matrix ι ι K), Ma * ((s₀ : GL ι K) : Matrix ι ι K)} : Finset _)
      have e3 := Finset.card_insert_le ((s₀ : GL ι K) : Matrix ι ι K)
        ({Ma * ((s₀ : GL ι K) : Matrix ι ι K)} : Finset _)
      rw [Finset.card_singleton] at e3
      rw [hT₄]
      omega
    omega

end CFSG.ComponentClassification.HarrisLit.T1.P51Q
