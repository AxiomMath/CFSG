module

public import CFSG.LieType.Steinberg.CentralExt.SUOddFieldThreeRadical
public import CFSG.LieType.Steinberg.CentralExt.FiniteFieldPairing

public section

namespace CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras

variable {F : Type} [Field F] {σ : F ≃+* F} {hσ : ∀ c, σ (σ c) = c} {m : ℕ}

section General

theorem inv_mul_mem_center0 {x y : SU σ (m + 2)} (hx : x ∈ radical σ hσ) (hy : y ∈ radical σ hσ)
    (h : qθ σ x = qθ σ y) : x⁻¹ * y ∈ center0 σ hσ :=
  ⟨mul_mem (inv_mem hx) hy, by rw [qθ_mul (inv_mem hx) hy, qθ_inv hx, h, neg_add_cancel]⟩

theorem conj_sq_mem {d : SU σ (m + 2)} (hdQ : ∀ x ∈ radical σ hσ, d * x * d⁻¹ ∈ radical σ hσ)
    {x : SU σ (m + 2)} (hx : x ∈ radical σ hσ) : d ^ 2 * x * (d ^ 2)⁻¹ ∈ radical σ hσ := by
  have h : d ^ 2 * x * (d ^ 2)⁻¹ = d * (d * x * d⁻¹) * d⁻¹ := by
    rw [sq, _root_.mul_inv_rev]
    simp only [mul_assoc]
  rw [h]
  exact hdQ _ (hdQ x hx)

theorem qθ_conj_sq {d : SU σ (m + 2)} (hdQ : ∀ x ∈ radical σ hσ, d * x * d⁻¹ ∈ radical σ hσ)
    {μ : F} (hdθ : ∀ x ∈ radical σ hσ, qθ σ (d * x * d⁻¹) = μ • qθ σ x) {x : SU σ (m + 2)}
    (hx : x ∈ radical σ hσ) : qθ σ (d ^ 2 * x * (d ^ 2)⁻¹) = μ ^ 2 • qθ σ x := by
  have h : d ^ 2 * x * (d ^ 2)⁻¹ = d * (d * x * d⁻¹) * d⁻¹ := by
    rw [sq, _root_.mul_inv_rev]
    simp only [mul_assoc]
  rw [h, hdθ _ (hdQ x hx), hdθ x hx, smul_smul, sq]

theorem conj_sq_center0 {d : SU σ (m + 2)}
    (hdZ : ∀ z ∈ center0 σ hσ, d * z * d⁻¹ = z⁻¹) {z : SU σ (m + 2)} (hz : z ∈ center0 σ hσ) :
    d ^ 2 * z * (d ^ 2)⁻¹ = z := by
  have h : d ^ 2 * z * (d ^ 2)⁻¹ = d * (d * z * d⁻¹) * d⁻¹ := by
    rw [sq, _root_.mul_inv_rev]
    simp only [mul_assoc]
  rw [h, hdZ z hz, show d * z⁻¹ * d⁻¹ = (d * z * d⁻¹)⁻¹ by group, hdZ z hz, inv_inv]

theorem hfix_radical {d : SU σ (m + 2)} (hdQ : ∀ x ∈ radical σ hσ, d * x * d⁻¹ ∈ radical σ hσ)
    {μ : F} (hdθ : ∀ x ∈ radical σ hσ, qθ σ (d * x * d⁻¹) = μ • qθ σ x) (hμ : μ ≠ 1)
    {x : SU σ (m + 2)} (hx : x ∈ radical σ hσ) (h : (d * x * d⁻¹)⁻¹ * x ∈ center0 σ hσ) :
    x ∈ center0 σ hσ := by
  refine ⟨hx, ?_⟩
  have h1 := h.2
  rw [qθ_mul (inv_mem (hdQ x hx)) hx, qθ_inv (hdQ x hx), hdθ x hx] at h1
  have h2 : (1 - μ) • qθ σ x = 0 := by
    rw [sub_smul, one_smul, sub_eq_neg_add]
    exact h1
  exact (smul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 (Ne.symm hμ))

theorem hbil_center0_center0 (hZ3 : Nat.card (center0 σ hσ (m := m)) = 3)
    (b : SU σ (m + 2) → SU σ (m + 2) → ZMod 3)
    (h₂ : ∀ x ∈ center0 σ hσ, ∀ y ∈ center0 σ hσ, ∀ y' ∈ center0 σ hσ,
      b x (y * y') = b x y + b x y')
    (h₃ : ∀ y ∈ center0 σ hσ, b 1 y = 0) (halt : ∀ x ∈ center0 σ hσ, b x x = 0) :
    ∀ x ∈ center0 σ hσ, ∀ y ∈ center0 σ hσ, b x y = 0 := by
  intro x hx y hy
  by_cases h1 : x = 1
  · rw [h1]
    exact h₃ y hy
  have hne : (⟨x, hx⟩ : center0 σ hσ) ≠ 1 := fun h => h1 (congrArg Subtype.val h)
  have hb1 : b x 1 = 0 := by
    have h := h₂ x hx 1 (one_mem _) 1 (one_mem _)
    rw [mul_one] at h
    exact add_eq_left.1 h.symm
  have hpow : ∀ n : ℕ, b x (x ^ n) = 0 := by
    intro n
    induction n with
    | zero => rw [pow_zero]; exact hb1
    | succ n ih => rw [pow_succ, h₂ x hx _ (pow_mem hx n) x hx, ih, halt x hx, add_zero]
  obtain ⟨n, hn⟩ := Submonoid.mem_powers_iff _ _ |>.1
    (mem_powers_of_prime_card hZ3 hne (g' := ⟨y, hy⟩))
  have hn' : x ^ n = y := by simpa using congrArg Subtype.val hn
  rw [← hn']
  exact hpow n

theorem pairing_inv_right {S₂ : Subgroup (SU σ (m + 2))}
    {b : SU σ (m + 2) → SU σ (m + 2) → ZMod 3} {x : SU σ (m + 2)}
    (h₂ : ∀ y ∈ S₂, ∀ y' ∈ S₂, b x (y * y') = b x y + b x y') (h1 : b x 1 = 0)
    {w : SU σ (m + 2)} (hw : w ∈ S₂) : b x w⁻¹ = -b x w := by
  have h := h₂ w hw w⁻¹ (inv_mem hw)
  rw [mul_inv_cancel, h1] at h
  exact eq_neg_of_add_eq_zero_right h.symm

theorem pairing_inv_left {S₁ : Subgroup (SU σ (m + 2))}
    {b : SU σ (m + 2) → SU σ (m + 2) → ZMod 3} {y : SU σ (m + 2)}
    (h₁ : ∀ x ∈ S₁, ∀ x' ∈ S₁, b (x * x') y = b x y + b x' y) (h1 : b 1 y = 0)
    {w : SU σ (m + 2)} (hw : w ∈ S₁) : b w⁻¹ y = -b w y := by
  have h := h₁ w hw w⁻¹ (inv_mem hw)
  rw [mul_inv_cancel, h1] at h
  exact eq_neg_of_add_eq_zero_right h.symm

end General

section CharThree

variable [CharP F 3]

theorem exists_mem_center0_of_ne_one {g : SU σ (m + 2)}
    (hgQ : ∀ x ∈ radical σ hσ, g * x * g⁻¹ ∈ radical σ hσ) {ν : F}
    (hgθ : ∀ x ∈ radical σ hσ, qθ σ (g * x * g⁻¹) = ν • qθ σ x) (hν : ν ≠ 1) {x : SU σ (m + 2)}
    (hx : x ∈ radical σ hσ) :
    ∃ w ∈ radical σ hσ, (g * w * g⁻¹ * w⁻¹)⁻¹ * x ∈ center0 σ hσ := by
  have hν' : ν - 1 ≠ 0 := sub_ne_zero.2 hν
  refine ⟨lift hσ ((ν - 1)⁻¹ • qθ σ x), lift_mem hσ _, inv_mul_mem_center0
    (mul_mem (hgQ _ (lift_mem hσ _)) (inv_mem (lift_mem hσ _))) hx ?_⟩
  rw [qθ_mul (hgQ _ (lift_mem hσ _)) (inv_mem (lift_mem hσ _)), qθ_inv (lift_mem hσ _),
    hgθ _ (lift_mem hσ _), qθ_lift, smul_smul, ← sub_eq_add_neg, ← sub_smul,
    ← sub_one_mul, mul_inv_cancel₀ hν', one_smul]

theorem hfix_center0 {d : SU σ (m + 2)} (hdZ : ∀ z ∈ center0 σ hσ, d * z * d⁻¹ = z⁻¹)
    {z : SU σ (m + 2)} (hz : z ∈ center0 σ hσ) (h : (d * z * d⁻¹)⁻¹ * z = 1) : z = 1 := by
  rw [hdZ z hz, inv_inv, ← sq] at h
  have h3 := pow_three_eq_one hσ hz
  rw [pow_succ, h, one_mul] at h3
  exact h3

theorem hbil_center0_radical {d : SU σ (m + 2)}
    (hdQ : ∀ x ∈ radical σ hσ, d * x * d⁻¹ ∈ radical σ hσ) {μ : F}
    (hdθ : ∀ x ∈ radical σ hσ, qθ σ (d * x * d⁻¹) = μ • qθ σ x)
    (hdZ : ∀ z ∈ center0 σ hσ, d * z * d⁻¹ = z⁻¹) (hμ : μ ^ 2 ≠ 1)
    (b : SU σ (m + 2) → SU σ (m + 2) → ZMod 3)
    (h₂ : ∀ x ∈ center0 σ hσ, ∀ y ∈ radical σ hσ, ∀ y' ∈ radical σ hσ,
      b x (y * y') = b x y + b x y')
    (h₄ : ∀ x ∈ center0 σ hσ, ∀ y ∈ center0 σ hσ, b x y = 0)
    (h₅ : ∀ x ∈ center0 σ hσ, ∀ y ∈ radical σ hσ,
      b (d ^ 2 * x * (d ^ 2)⁻¹) (d ^ 2 * y * (d ^ 2)⁻¹) = b x y) :
    ∀ x ∈ center0 σ hσ, ∀ y ∈ radical σ hσ, b x y = 0 := by
  intro x hx y hy
  obtain ⟨w, hw, hz⟩ := exists_mem_center0_of_ne_one (fun _ hx => conj_sq_mem hdQ hx)
    (fun _ hx => qθ_conj_sq hdQ hdθ hx) hμ hy
  have hw2 := conj_sq_mem hdQ hw
  have h6 : b x (d ^ 2 * w * (d ^ 2)⁻¹) = b x w := by
    have h := h₅ x hx w hw
    rwa [conj_sq_center0 hdZ hx] at h
  rw [show y = (d ^ 2 * w * (d ^ 2)⁻¹ * w⁻¹) * ((d ^ 2 * w * (d ^ 2)⁻¹ * w⁻¹)⁻¹ * y) by group,
    h₂ x hx _ (mul_mem hw2 (inv_mem hw)) _ hz.1, h₄ x hx _ hz, add_zero,
    h₂ x hx _ hw2 _ (inv_mem hw), h6,
    pairing_inv_right (h₂ x hx) (h₄ x hx 1 (one_mem _)) hw]
  exact add_neg_cancel _

theorem hbil_radical_center0 {d : SU σ (m + 2)}
    (hdQ : ∀ x ∈ radical σ hσ, d * x * d⁻¹ ∈ radical σ hσ) {μ : F}
    (hdθ : ∀ x ∈ radical σ hσ, qθ σ (d * x * d⁻¹) = μ • qθ σ x)
    (hdZ : ∀ z ∈ center0 σ hσ, d * z * d⁻¹ = z⁻¹) (hμ : μ ^ 2 ≠ 1)
    (b : SU σ (m + 2) → SU σ (m + 2) → ZMod 3)
    (h₁ : ∀ x ∈ radical σ hσ, ∀ x' ∈ radical σ hσ, ∀ y ∈ center0 σ hσ,
      b (x * x') y = b x y + b x' y)
    (h₃ : ∀ x ∈ center0 σ hσ, ∀ y ∈ center0 σ hσ, b x y = 0)
    (h₅ : ∀ x ∈ radical σ hσ, ∀ y ∈ center0 σ hσ,
      b (d ^ 2 * x * (d ^ 2)⁻¹) (d ^ 2 * y * (d ^ 2)⁻¹) = b x y) :
    ∀ x ∈ radical σ hσ, ∀ y ∈ center0 σ hσ, b x y = 0 := by
  intro x hx y hy
  obtain ⟨w, hw, hz⟩ := exists_mem_center0_of_ne_one (fun _ hx => conj_sq_mem hdQ hx)
    (fun _ hx => qθ_conj_sq hdQ hdθ hx) hμ hx
  have hw2 := conj_sq_mem hdQ hw
  have h6 : b (d ^ 2 * w * (d ^ 2)⁻¹) y = b w y := by
    have h := h₅ w hw y hy
    rwa [conj_sq_center0 hdZ hy] at h
  rw [show x = (d ^ 2 * w * (d ^ 2)⁻¹ * w⁻¹) * ((d ^ 2 * w * (d ^ 2)⁻¹ * w⁻¹)⁻¹ * x) by group,
    h₁ _ (mul_mem hw2 (inv_mem hw)) _ hz.1 y hy, h₃ _ hz y hy, add_zero,
    h₁ _ hw2 _ (inv_mem hw) y hy, h6,
    pairing_inv_left (fun a ha a' ha' => h₁ a ha a' ha' y hy) (h₃ 1 (one_mem _) y hy) hw]
  exact add_neg_cancel _

theorem hbil_radical_radical [Finite F] (hF9 : Nat.card F = 3 ^ 2) {d : SU σ (m + 2)}
    (hdQ : ∀ x ∈ radical σ hσ, d * x * d⁻¹ ∈ radical σ hσ) {μ : Fˣ}
    (hdθ : ∀ x ∈ radical σ hσ, qθ σ (d * x * d⁻¹) = (μ : F) • qθ σ x)
    (hμ : ∀ t : Fˣ, ∃ n : ℕ, μ ^ n = t) (b : SU σ (m + 2) → SU σ (m + 2) → ZMod 3)
    (h₁ : ∀ x ∈ radical σ hσ, ∀ x' ∈ radical σ hσ, ∀ y ∈ radical σ hσ,
      b (x * x') y = b x y + b x' y)
    (h₂ : ∀ x ∈ radical σ hσ, ∀ y ∈ radical σ hσ, ∀ y' ∈ radical σ hσ,
      b x (y * y') = b x y + b x y')
    (h₃ : ∀ x ∈ center0 σ hσ, ∀ y ∈ radical σ hσ, b x y = 0)
    (h₄ : ∀ x ∈ radical σ hσ, ∀ y ∈ center0 σ hσ, b x y = 0)
    (h₅ : ∀ x ∈ radical σ hσ, ∀ y ∈ radical σ hσ, b (d * x * d⁻¹) (d * y * d⁻¹) = b x y) :
    ∀ x ∈ radical σ hσ, ∀ y ∈ radical σ hσ, b x y = 0 := by
  have hθ1 : ∀ x ∈ radical σ hσ, ∀ x' ∈ radical σ hσ, qθ σ x = qθ σ x' →
      ∀ y ∈ radical σ hσ, b x y = b x' y := by
    intro x hx x' hx' h y hy
    have hz := inv_mul_mem_center0 hx hx' h
    rw [show x' = x * (x⁻¹ * x') by group, h₁ x hx _ hz.1 y hy, h₃ _ hz y hy, add_zero]
  have hθ2 : ∀ x ∈ radical σ hσ, ∀ y ∈ radical σ hσ, ∀ y' ∈ radical σ hσ, qθ σ y = qθ σ y' →
      b x y = b x y' := by
    intro x hx y hy y' hy' h
    have hz := inv_mul_mem_center0 hy hy' h
    rw [show y' = y * (y⁻¹ * y') by group, h₂ x hx y hy _ hz.1, h₄ x hx _ hz, add_zero]
  let B : (Fin m → F) → (Fin m → F) → ZMod 3 := fun w w' => b (lift hσ w) (lift hσ w')
  have hB : ∀ x ∈ radical σ hσ, ∀ y ∈ radical σ hσ, b x y = B (qθ σ x) (qθ σ y) :=
    fun x hx y hy => by
      rw [hθ1 x hx _ (lift_mem hσ _) (qθ_lift hσ _).symm y hy,
        hθ2 _ (lift_mem hσ _) y hy _ (lift_mem hσ _) (qθ_lift hσ _).symm]
  have hB1 : ∀ w w' v, B (w + w') v = B w v + B w' v := fun w w' v => by
    have h := hB _ (mul_mem (lift_mem hσ w) (lift_mem hσ w')) _ (lift_mem hσ v)
    rw [qθ_mul (lift_mem hσ w) (lift_mem hσ w'), qθ_lift, qθ_lift, qθ_lift] at h
    rw [← h, h₁ _ (lift_mem hσ w) _ (lift_mem hσ w') _ (lift_mem hσ v)]
  have hB2 : ∀ w v v', B w (v + v') = B w v + B w v' := fun w v v' => by
    have h := hB _ (lift_mem hσ w) _ (mul_mem (lift_mem hσ v) (lift_mem hσ v'))
    rw [qθ_mul (lift_mem hσ v) (lift_mem hσ v'), qθ_lift, qθ_lift, qθ_lift] at h
    rw [← h, h₂ _ (lift_mem hσ w) _ (lift_mem hσ v) _ (lift_mem hσ v')]
  have hBμ : ∀ w v, B ((μ : F) • w) ((μ : F) • v) = B w v := fun w v => by
    have h := hB _ (hdQ _ (lift_mem hσ w)) _ (hdQ _ (lift_mem hσ v))
    rw [hdθ _ (lift_mem hσ w), hdθ _ (lift_mem hσ v), qθ_lift, qθ_lift,
      h₅ _ (lift_mem hσ w) _ (lift_mem hσ v)] at h
    exact h.symm
  have hBt : ∀ t : Fˣ, ∀ w v, B ((t : F) • w) ((t : F) • v) = B w v := by
    intro t w v
    obtain ⟨n, rfl⟩ := hμ t
    induction n generalizing w v with
    | zero => simp
    | succ n ih => rw [pow_succ', Units.val_mul, mul_smul, mul_smul, hBμ, ih]
  have hcoord : ∀ j l : Fin m, ∀ c c' : F, B (Pi.single j c) (Pi.single l c') = 0 := by
    intro j l
    refine CFSG.LieType.Steinberg.CentralExt.zpow_form_eq_zero (K := F) (p := 3) (f := 2)
      (by norm_num) hF9 (e₁ := 1) (e₂ := 1) ?_ (fun c c' => B (Pi.single j c) (Pi.single l c'))
      (fun c₁ c₂ c' => by simp only [Pi.single_add, hB1])
      (fun c c₁ c₂ => by simp only [Pi.single_add, hB2]) (fun t c c' => ?_)
    · intro i i' hi hi'
      interval_cases i <;> interval_cases i' <;> decide
    · simp only [zpow_one]
      rw [← smul_eq_mul, ← smul_eq_mul, Pi.single_smul, Pi.single_smul, hBt]
  have hBzero : ∀ w v, B w v = 0 := by
    intro w v
    let φ₁ : (Fin m → F) →+ ZMod 3 := AddMonoidHom.mk' (fun w => B w v) fun w w' => hB1 w w' v
    have e1 : B w v = ∑ j, B (Pi.single j (w j)) v := by
      conv_lhs => rw [← Finset.univ_sum_single w]
      exact map_sum φ₁ _ _
    rw [e1]
    refine Finset.sum_eq_zero fun j _ => ?_
    let φ₂ : (Fin m → F) →+ ZMod 3 :=
      AddMonoidHom.mk' (fun v => B (Pi.single j (w j)) v) fun v v' => hB2 _ v v'
    have e2 : B (Pi.single j (w j)) v = ∑ l, B (Pi.single j (w j)) (Pi.single l (v l)) := by
      conv_lhs => rw [← Finset.univ_sum_single v]
      exact map_sum φ₂ _ _
    rw [e2]
    exact Finset.sum_eq_zero fun l _ => hcoord j l _ _
  intro x hx y hy
  rw [hB x hx y hy, hBzero]

theorem eq_one_of_invariant {E : Type*} [Group E] {d : SU σ (m + 2)}
    (hdQ : ∀ x ∈ radical σ hσ, d * x * d⁻¹ ∈ radical σ hσ) {μ : F}
    (hdθ : ∀ x ∈ radical σ hσ, qθ σ (d * x * d⁻¹) = μ • qθ σ x)
    (hdZ : ∀ z ∈ center0 σ hσ, d * z * d⁻¹ = z⁻¹) (hμ : μ ≠ 1) (φ : SU σ (m + 2) → E)
    (hmul : ∀ x ∈ radical σ hσ, ∀ y ∈ radical σ hσ, φ (x * y) = φ x * φ y)
    (hinv : ∀ x ∈ radical σ hσ, φ (d * x * d⁻¹) = φ x) : ∀ x ∈ radical σ hσ, φ x = 1 := by
  have h1 : φ 1 = 1 := by
    have h := hmul 1 (one_mem _) 1 (one_mem _)
    rw [mul_one] at h
    exact mul_eq_left.1 h.symm
  have hφinv : ∀ x ∈ radical σ hσ, φ x⁻¹ = (φ x)⁻¹ := fun x hx => by
    have h := hmul x hx x⁻¹ (inv_mem hx)
    rw [mul_inv_cancel, h1] at h
    exact eq_inv_of_mul_eq_one_right h.symm
  have hZ : ∀ z ∈ center0 σ hσ, φ z = 1 := fun z hz => by
    have h2 : φ z = (φ z)⁻¹ := by rw [← hφinv z hz.1, ← hdZ z hz, hinv z hz.1]
    have hz3 : z * z * z = 1 := by
      have h := pow_three_eq_one hσ hz
      rwa [pow_succ, sq] at h
    have h3 : φ z * φ z * φ z = 1 := by
      rw [← hmul z hz.1 z hz.1, ← hmul _ (mul_mem hz.1 hz.1) z hz.1, hz3, h1]
    have h4 : φ z * φ z = 1 := by
      nth_rewrite 2 [h2]
      exact mul_inv_cancel _
    calc φ z = φ z * φ z * φ z * (φ z * φ z)⁻¹ := by group
      _ = 1 := by rw [h3, h4, inv_one, mul_one]
  intro x hx
  obtain ⟨w, hw, hz⟩ := exists_mem_center0_of_ne_one hdQ hdθ hμ hx
  have hv : d * w * d⁻¹ * w⁻¹ ∈ radical σ hσ := mul_mem (hdQ w hw) (inv_mem hw)
  rw [show x = (d * w * d⁻¹ * w⁻¹) * ((d * w * d⁻¹ * w⁻¹)⁻¹ * x) by group, hmul _ hv _ hz.1,
    hZ _ hz, mul_one, hmul _ (hdQ w hw) _ (inv_mem hw), hinv w hw, hφinv w hw, mul_inv_cancel]

end CharThree

end CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree
