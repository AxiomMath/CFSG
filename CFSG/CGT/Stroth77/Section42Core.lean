module

public import CFSG.CGT.Stroth77.Arch76Frame
public import CFSG.CGT.Stroth77.TorusNormalForm

public section

namespace CFSG.CGT.Stroth77

open Matrix

namespace Stroth42Core

theorem zmod_even_or_odd {m : ℕ} (x : ZMod (2 ^ m)) : Even x ∨ Odd x := by
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective x
  rcases Int.even_or_odd z with h | h
  · exact Or.inl (by simpa using h.map (Int.castRingHom (ZMod (2 ^ m))))
  · exact Or.inr (by simpa using h.map (Int.castRingHom (ZMod (2 ^ m))))

theorem zmod_not_even_of_odd {m : ℕ} (hm : 1 ≤ m) {x : ZMod (2 ^ m)} (h : Odd x) : ¬ Even x := by
  have h2 : (2 : ℕ) ∣ 2 ^ m := dvd_pow_self 2 (by omega)
  intro he
  obtain ⟨r, hr⟩ := he.map (ZMod.castHom h2 (ZMod 2))
  obtain ⟨s, hs⟩ := h.map (ZMod.castHom h2 (ZMod 2))
  have key : ∀ r s : ZMod 2, r + r ≠ 2 * s + 1 := by decide
  exact key r s (hr.symm.trans hs)

theorem zmod_not_even_iff_odd {m : ℕ} (hm : 1 ≤ m) {x : ZMod (2 ^ m)} : ¬ Even x ↔ Odd x :=
  ⟨fun h => (zmod_even_or_odd x).resolve_left h, zmod_not_even_of_odd hm⟩

theorem even_intCast_iff {m : ℕ} (hm : 1 ≤ m) (z : ℤ) : Even ((z : ZMod (2 ^ m))) ↔ Even z := by
  constructor
  · intro h
    by_contra hz
    have ho : Odd ((z : ZMod (2 ^ m))) := by
      simpa using (Int.not_even_iff_odd.mp hz).map (Int.castRingHom (ZMod (2 ^ m)))
    exact zmod_not_even_of_odd hm ho h
  · intro h
    simpa using h.map (Int.castRingHom (ZMod (2 ^ m)))

theorem even_matAct_zero_iff {k : Fin 3 → ℕ} (hk : 1 ≤ k 0) (M : IntMat) (hM : Compat k M)
    (h00 : Odd (M 0 0)) (h01 : Even (M 0 1)) (h02 : Even (M 0 2)) (v : Torus k) :
    Even ((matAct k M hM v) 0) ↔ Even (v 0) := by
  obtain ⟨x, rfl⟩ := Torus.exists_ofInt v
  rw [matAct_ofInt, Torus.ofInt_apply, Torus.ofInt_apply, even_intCast_iff hk,
    even_intCast_iff hk]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  have h00' : ¬ Even (M 0 0) := Int.not_even_iff_odd.mpr h00
  simp [Int.even_add, Int.even_mul, h00', h01, h02]

theorem ofInt_mul_two_pow_pred_eq_iff {k : Fin 3 → ℕ} (hk : ∀ i, 1 ≤ k i) (x y : Fin 3 → ℤ) :
    Torus.ofInt k (fun i => x i * 2 ^ (k i - 1)) = Torus.ofInt k (fun i => y i * 2 ^ (k i - 1)) ↔
      ∀ i, x i ≡ y i [ZMOD 2] := by
  rw [Torus.ofInt_eq_ofInt_iff]
  refine forall_congr' fun i => ?_
  have hpow : (2 : ℤ) ^ k i = 2 * 2 ^ (k i - 1) := by
    rw [← pow_succ']; congr 1; have := hk i; omega
  have hne : (2 : ℤ) ^ (k i - 1) ≠ 0 := pow_ne_zero _ two_ne_zero
  rw [Int.modEq_iff_dvd, Int.modEq_iff_dvd, hpow, ← sub_mul]
  exact mul_dvd_mul_iff_right hne

variable {G : Type*} [Group G]

theorem natCard_le_of_subset_range {α : Type*} [Finite α] {E : Subgroup G} (f : α → G)
    (h : ∀ e ∈ E, ∃ x, f x = e) : Nat.card E ≤ Nat.card α := by
  have h1 : (E : Set G) ⊆ Set.range f := fun e he => h e he
  calc Nat.card E = Nat.card (E : Set G) := rfl
    _ ≤ Nat.card (Set.range f) := Nat.card_mono (Set.finite_range f) h1
    _ ≤ Nat.card α := Nat.card_le_card_of_surjective _ Set.rangeFactorization_surjective

theorem pow_two_pow_eq_mul_self (y : G) {l : ℕ} (hl : 1 ≤ l) :
    y ^ 2 ^ l = (y * y) ^ 2 ^ (l - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
  rw [Nat.add_sub_cancel, pow_succ', pow_mul, sq]

theorem two_pow_dvd_four {n : ℕ} (hn : 2 ≤ n) {A : ℤ} (h : (2 : ℤ) ^ n ∣ A) : 4 ∣ A := by
  have h4 : (4 : ℤ) ∣ 2 ^ n := by
    rw [show (4 : ℤ) = 2 ^ 2 by norm_num]
    exact pow_dvd_pow 2 hn
  exact h4.trans h

theorem four_dvd_of_two_pow_dvd_mul {n e : ℕ} (he : e + 2 = n) {A : ℤ}
    (h : (2 : ℤ) ^ n ∣ 2 ^ e * A) : 4 ∣ A := by
  have h4 : (2 : ℤ) ^ n = 2 ^ e * 4 := by
    rw [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_add, he]
  rw [h4] at h
  exact (mul_dvd_mul_iff_left (pow_ne_zero _ two_ne_zero)).mp h

theorem bool_toNat_cast_eq {z : ℤ} (hz : z = 0 ∨ z = 1) : ((decide (z = 1)).toNat : ℤ) = z := by
  rcases hz with rfl | rfl <;> simp

theorem not_two_pow_dvd_aux {n : ℕ} (hn : 2 ≤ n) (r : ℤ) :
    ¬ (2 : ℤ) ^ n ∣ 1 * 2 ^ (n - 1) - 2 ^ (n - 1 - 1) * (r + r + (r + r)) := by
  intro h
  have h4 : (2 : ℤ) ^ (n - 1 - 1) * (r + r + (r + r)) = 2 ^ n * r := by
    have : (2 : ℤ) ^ n = 2 ^ (n - 1 - 1) * 4 := by
      rw [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_add]
      congr 1
      omega
    rw [this]
    ring
  rw [h4, one_mul] at h
  have h' : (2 : ℤ) ^ n ∣ 2 ^ (n - 1) := by
    have := dvd_add h (dvd_mul_right ((2 : ℤ) ^ n) r)
    simpa using this
  have hlt : (2 : ℤ) ^ (n - 1) < 2 ^ n := pow_lt_pow_right₀ (by norm_num) (by omega)
  have hpos : (0 : ℤ) < 2 ^ (n - 1) := by positivity
  exact absurd (Int.le_of_dvd hpos h') (not_le.mpr hlt)

@[expose] def bpow (x : G) (b : Bool) : G := if b then x else 1

theorem bpow_mul_bpow {x : G} (hx : x * x = 1) (a b : Bool) :
    bpow x a * bpow x b = bpow x (xor a b) := by
  cases a <;> cases b <;> simp [bpow, hx]

theorem bpow_commute {x z : G} (h : x * z = z * x) (a b : Bool) :
    Commute (bpow x a) (bpow z b) := by
  cases a <;> cases b <;> simp [bpow, Commute, SemiconjBy, h]

theorem bpow_commute_left {x y : G} (h : x * y = y * x) (a : Bool) : Commute (bpow x a) y := by
  cases a <;> simp [bpow, Commute, SemiconjBy, h]

theorem bpow_two_mul {x z : G} (hx : x * x = 1) (hz : z * z = 1) (h : x * z = z * x)
    (a b a' b' : Bool) :
    bpow x a * bpow z b * (bpow x a' * bpow z b') = bpow x (xor a a') * bpow z (xor b b') := by
  rw [mul_assoc, ← mul_assoc (bpow z b), (bpow_commute h.symm b a').eq, mul_assoc, ← mul_assoc,
    bpow_mul_bpow hx, bpow_mul_bpow hz]

@[expose] def prod4 (x₁ x₂ y₃ y₄ : G) (w : (Bool × Bool) × (Bool × Bool)) : G :=
  bpow x₁ w.1.1 * bpow x₂ w.1.2 * (bpow y₃ w.2.1 * bpow y₄ w.2.2)

@[expose] def xor4 (w w' : (Bool × Bool) × (Bool × Bool)) : (Bool × Bool) × (Bool × Bool) :=
  ((xor w.1.1 w'.1.1, xor w.1.2 w'.1.2), (xor w.2.1 w'.2.1, xor w.2.2 w'.2.2))

theorem prod4_mul_prod4 {x₁ x₂ y₃ y₄ : G}
    (h₁ : x₁ * x₁ = 1) (h₂ : x₂ * x₂ = 1) (h₃ : y₃ * y₃ = 1) (h₄ : y₄ * y₄ = 1)
    (h₁₂ : x₁ * x₂ = x₂ * x₁) (h₁₃ : x₁ * y₃ = y₃ * x₁) (h₁₄ : x₁ * y₄ = y₄ * x₁)
    (h₂₃ : x₂ * y₃ = y₃ * x₂) (h₂₄ : x₂ * y₄ = y₄ * x₂) (h₃₄ : y₃ * y₄ = y₄ * y₃)
    (w w' : (Bool × Bool) × (Bool × Bool)) :
    prod4 x₁ x₂ y₃ y₄ w * prod4 x₁ x₂ y₃ y₄ w' = prod4 x₁ x₂ y₃ y₄ (xor4 w w') := by
  obtain ⟨⟨a, b⟩, ⟨c, d⟩⟩ := w
  obtain ⟨⟨a', b'⟩, ⟨c', d'⟩⟩ := w'
  simp only [prod4, xor4]
  have hQP : Commute (bpow y₃ c * bpow y₄ d) (bpow x₁ a' * bpow x₂ b') :=
    Commute.mul_left
      (Commute.mul_right (bpow_commute h₁₃.symm c a') (bpow_commute h₂₃.symm c b'))
      (Commute.mul_right (bpow_commute h₁₄.symm d a') (bpow_commute h₂₄.symm d b'))
  calc bpow x₁ a * bpow x₂ b * (bpow y₃ c * bpow y₄ d) *
        (bpow x₁ a' * bpow x₂ b' * (bpow y₃ c' * bpow y₄ d'))
      = bpow x₁ a * bpow x₂ b * ((bpow y₃ c * bpow y₄ d) * (bpow x₁ a' * bpow x₂ b')) *
          (bpow y₃ c' * bpow y₄ d') := by simp only [mul_assoc]
    _ = bpow x₁ a * bpow x₂ b * ((bpow x₁ a' * bpow x₂ b') * (bpow y₃ c * bpow y₄ d)) *
          (bpow y₃ c' * bpow y₄ d') := by rw [hQP.eq]
    _ = (bpow x₁ a * bpow x₂ b * (bpow x₁ a' * bpow x₂ b')) *
          (bpow y₃ c * bpow y₄ d * (bpow y₃ c' * bpow y₄ d')) := by simp only [mul_assoc]
    _ = _ := by rw [bpow_two_mul h₁ h₂ h₁₂, bpow_two_mul h₃ h₄ h₃₄]

theorem prod4_zero (x₁ x₂ y₃ y₄ : G) :
    prod4 x₁ x₂ y₃ y₄ ((false, false), (false, false)) = 1 := by
  simp [prod4, bpow]

theorem xor4_self (w : (Bool × Bool) × (Bool × Bool)) :
    xor4 w w = ((false, false), (false, false)) := by
  simp [xor4]

theorem exists_E16 {H : Subgroup G} {x₁ x₂ y₃ y₄ y : G} (hx₁ : x₁ ∈ H) (hx₂ : x₂ ∈ H)
    (h₁ : x₁ * x₁ = 1) (h₂ : x₂ * x₂ = 1) (h₃ : y₃ * y₃ = 1) (h₄ : y₄ * y₄ = 1)
    (h₁₂ : x₁ * x₂ = x₂ * x₁) (h₁₃ : x₁ * y₃ = y₃ * x₁) (h₁₄ : x₁ * y₄ = y₄ * x₁)
    (h₂₃ : x₂ * y₃ = y₃ * x₂) (h₂₄ : x₂ * y₄ = y₄ * x₂) (h₃₄ : y₃ * y₄ = y₄ * y₃)
    (hx₁1 : x₁ ≠ 1) (hx₂1 : x₂ ≠ 1) (hx₁₂ : x₁ ≠ x₂)
    (hy₃ : y₃ ∉ H) (hy₄ : y₄ ∉ H) (hy₃₄ : y₃ * y₄ ∉ H)
    (hc₁ : x₁ * y = y * x₁) (hc₂ : x₂ * y = y * x₂) (hc₃ : y₃ * y = y * y₃)
    (hc₄ : y₄ * y = y * y₄) :
    ∃ E : Subgroup G, E ≤ Subgroup.centralizer {y} ∧ (∀ e ∈ E, e * e = 1) ∧ Nat.card E = 16 := by
  have hmul := prod4_mul_prod4 h₁ h₂ h₃ h₄ h₁₂ h₁₃ h₁₄ h₂₃ h₂₄ h₃₄
  have hsq : ∀ w, prod4 x₁ x₂ y₃ y₄ w * prod4 x₁ x₂ y₃ y₄ w = 1 := fun w => by
    rw [hmul, xor4_self, prod4_zero]
  have hind : ∀ w, prod4 x₁ x₂ y₃ y₄ w = 1 → w = ((false, false), (false, false)) := by
    rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩ h
    simp only [prod4] at h
    have hPH : bpow x₁ a * bpow x₂ b ∈ H := by
      cases a <;> cases b <;> simp [bpow, hx₁, hx₂, mul_mem]
    have hQ : bpow y₃ c * bpow y₄ d ∈ H := by
      rw [eq_inv_of_mul_eq_one_right h]
      exact inv_mem hPH
    have hcd : c = false ∧ d = false := by
      cases c <;> cases d
      · exact ⟨rfl, rfl⟩
      · exact absurd (by simpa [bpow] using hQ) hy₄
      · exact absurd (by simpa [bpow] using hQ) hy₃
      · exact absurd (by simpa [bpow] using hQ) hy₃₄
    obtain ⟨rfl, rfl⟩ := hcd
    have h' : bpow x₁ a * bpow x₂ b = 1 := by simpa [bpow] using h
    have hab : a = false ∧ b = false := by
      cases a <;> cases b
      · exact ⟨rfl, rfl⟩
      · exact absurd (by simpa [bpow] using h') hx₂1
      · exact absurd (by simpa [bpow] using h') hx₁1
      · have h12 : x₁ * x₂ = 1 := by simpa [bpow] using h'
        exact absurd ((eq_inv_of_mul_eq_one_left h12).trans (inv_eq_of_mul_eq_one_right h₂))
          hx₁₂
    obtain ⟨rfl, rfl⟩ := hab
    rfl
  have hinj : Function.Injective (prod4 x₁ x₂ y₃ y₄) := by
    intro w w' h
    have h1 : prod4 x₁ x₂ y₃ y₄ (xor4 w w') = 1 := by rw [← hmul, h, hsq]
    have h2 := hind _ h1
    obtain ⟨⟨a, b⟩, ⟨c, d⟩⟩ := w
    obtain ⟨⟨a', b'⟩, ⟨c', d'⟩⟩ := w'
    simp only [xor4, Prod.mk.injEq] at h2
    obtain ⟨⟨ha, hb⟩, ⟨hc, hd⟩⟩ := h2
    revert ha hb hc hd
    cases a <;> cases a' <;> cases b <;> cases b' <;> cases c <;> cases c' <;> cases d <;>
      cases d' <;> decide
  let E : Subgroup G :=
    { carrier := Set.range (prod4 x₁ x₂ y₃ y₄)
      mul_mem' := by
        rintro _ _ ⟨w, rfl⟩ ⟨w', rfl⟩
        exact ⟨_, (hmul w w').symm⟩
      one_mem' := ⟨_, prod4_zero x₁ x₂ y₃ y₄⟩
      inv_mem' := by
        rintro _ ⟨w, rfl⟩
        exact ⟨w, (inv_eq_of_mul_eq_one_right (hsq w)).symm⟩ }
  refine ⟨E, ?_, ?_, ?_⟩
  · rintro _ ⟨⟨⟨a, b⟩, ⟨c, d⟩⟩, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    have hcomm : Commute (prod4 x₁ x₂ y₃ y₄ ((a, b), (c, d))) z :=
      Commute.mul_left (Commute.mul_left (bpow_commute_left hc₁ a) (bpow_commute_left hc₂ b))
        (Commute.mul_left (bpow_commute_left hc₃ c) (bpow_commute_left hc₄ d))
    exact hcomm.eq.symm
  · rintro _ ⟨w, rfl⟩
    exact hsq w
  · change Nat.card (Set.range (prod4 x₁ x₂ y₃ y₄)) = 16
    rw [Nat.card_range_of_injective hinj]
    simp

end Stroth42Core

namespace SigmaFourAction

variable {k : Fin 3 → ℕ} (A : SigmaFourAction k)

@[expose] def d8Act (i j l : Bool) : Torus k →+ Torus k :=
  (if i then A.φuv else AddMonoidHom.id _).comp
    ((if j then A.φt else AddMonoidHom.id _).comp (if l then A.φu else AddMonoidHom.id _))

theorem even_d8Act_zero_iff (huv : ∀ v, Even ((A.φuv v) 0) ↔ Even (v 0))
    (ht : ∀ v, Even ((A.φt v) 0) ↔ Even (v 0)) (hu : ∀ v, Even ((A.φu v) 0) ↔ Even (v 0))
    (i j l : Bool) (v : Torus k) : Even ((A.d8Act i j l v) 0) ↔ Even (v 0) := by
  cases i <;> cases j <;> cases l <;> simp [d8Act, huv, ht, hu]

end SigmaFourAction

namespace StrothWeakTypeData

variable {G : Type*} [Group G] {D : Subgroup G} {τ : StrothTypeIndex}
  (dD : StrothWeakTypeData D τ)

theorem uv_inv : dD.uv⁻¹ = dD.uv := inv_eq_of_mul_eq_one_right dD.uv_sq

theorem t_inv : dD.t⁻¹ = dD.t := inv_eq_of_mul_eq_one_right dD.t_sq

theorem u_inv : dD.u⁻¹ = dD.u := inv_eq_of_mul_eq_one_right dD.u_sq

theorem uv_mul_uv (x : G) : dD.uv * (dD.uv * x) = x := by rw [← mul_assoc, dD.uv_sq, one_mul]

theorem t_mul_t (x : G) : dD.t * (dD.t * x) = x := by rw [← mul_assoc, dD.t_sq, one_mul]

theorem u_mul_u (x : G) : dD.u * (dD.u * x) = x := by rw [← mul_assoc, dD.u_sq, one_mul]

theorem t_mul_uv (x : G) : dD.t * (dD.uv * x) = dD.uv * (dD.t * x) := by
  rw [← mul_assoc, ← dD.uv_comm_t, mul_assoc]

theorem u_mul_uv (x : G) : dD.u * (dD.uv * x) = dD.uv * (dD.u * x) := by
  rw [← mul_assoc, ← dD.uv_comm_u, mul_assoc]

theorem u_mul_t_eq : dD.u * dD.t = dD.uv * dD.t * dD.u := by
  have h1 : dD.u * (dD.t * dD.u) * dD.u = dD.u * (dD.u * dD.uv * dD.t) * dD.u := by
    rw [dD.t_u]
  rw [← mul_assoc, ← mul_assoc, ← mul_assoc, dD.u_sq, one_mul, mul_assoc, dD.u_sq,
    mul_one] at h1
  rw [h1]

theorem u_mul_t (x : G) : dD.u * (dD.t * x) = dD.uv * (dD.t * (dD.u * x)) := by
  rw [← mul_assoc, dD.u_mul_t_eq, mul_assoc, mul_assoc]

@[expose] def d8 (i j l : Bool) : G :=
  (if i then dD.uv else 1) * ((if j then dD.t else 1) * (if l then dD.u else 1))

theorem d8_fff : dD.d8 false false false = 1 := by simp [d8]

theorem d8_tff : dD.d8 true false false = dD.uv := by simp [d8]

theorem d8_ftf : dD.d8 false true false = dD.t := by simp [d8]

theorem d8_fft : dD.d8 false false true = dD.u := by simp [d8]

theorem d8_ttf : dD.d8 true true false = dD.uv * dD.t := by simp [d8]

theorem d8_tft : dD.d8 true false true = dD.uv * dD.u := by simp [d8]

theorem d8_ftt : dD.d8 false true true = dD.t * dD.u := by simp [d8]

theorem d8_ttt : dD.d8 true true true = dD.uv * (dD.t * dD.u) := by simp [d8]

theorem d8_mem (i j l : Bool) : dD.d8 i j l ∈ Subgroup.closure ({dD.uv, dD.t, dD.u} : Set G) := by
  have huv : dD.uv ∈ Subgroup.closure ({dD.uv, dD.t, dD.u} : Set G) :=
    Subgroup.subset_closure (by simp)
  have ht : dD.t ∈ Subgroup.closure ({dD.uv, dD.t, dD.u} : Set G) :=
    Subgroup.subset_closure (by simp)
  have hu : dD.u ∈ Subgroup.closure ({dD.uv, dD.t, dD.u} : Set G) :=
    Subgroup.subset_closure (by simp)
  cases i <;> cases j <;> cases l <;> simp [d8, huv, ht, hu, mul_mem]

theorem uv_mul_d8 (i j l : Bool) : dD.uv * dD.d8 i j l = dD.d8 (!i) j l := by
  cases i <;> cases j <;> cases l <;> simp [d8, dD.uv_mul_uv, dD.uv_sq]

theorem t_mul_d8 (i j l : Bool) : dD.t * dD.d8 i j l = dD.d8 i (!j) l := by
  have h : dD.t * dD.uv = dD.uv * dD.t := dD.uv_comm_t.symm
  cases i <;> cases j <;> cases l <;> simp [d8, dD.t_mul_uv, dD.t_mul_t, dD.t_sq, h]

theorem u_mul_d8 (i j l : Bool) : dD.u * dD.d8 i j l = dD.d8 (xor i j) j (!l) := by
  have h : dD.u * dD.uv = dD.uv * dD.u := dD.uv_comm_u.symm
  have h' : dD.u * dD.t = dD.uv * (dD.t * dD.u) := by rw [dD.u_mul_t_eq, mul_assoc]
  cases i <;> cases j <;> cases l <;>
    simp [d8, dD.u_mul_uv, dD.u_mul_t, dD.u_mul_u, dD.u_sq, dD.uv_mul_uv, dD.uv_sq, h, h']

theorem mem_closure_iff_d8 {x : G} :
    x ∈ Subgroup.closure ({dD.uv, dD.t, dD.u} : Set G) ↔ ∃ i j l, x = dD.d8 i j l := by
  constructor
  · intro hx
    induction hx using Subgroup.closure_induction_left with
    | one => exact ⟨false, false, false, dD.d8_fff.symm⟩
    | mul_left x hx y _ ih =>
      obtain ⟨i, j, l, rfl⟩ := ih
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact ⟨!i, j, l, dD.uv_mul_d8 i j l⟩
      · exact ⟨i, !j, l, dD.t_mul_d8 i j l⟩
      · exact ⟨xor i j, j, !l, dD.u_mul_d8 i j l⟩
    | inv_mul_cancel x hx y _ ih =>
      obtain ⟨i, j, l, rfl⟩ := ih
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact ⟨!i, j, l, by rw [dD.uv_inv]; exact dD.uv_mul_d8 i j l⟩
      · exact ⟨i, !j, l, by rw [dD.t_inv]; exact dD.t_mul_d8 i j l⟩
      · exact ⟨xor i j, j, !l, by rw [dD.u_inv]; exact dD.u_mul_d8 i j l⟩
  · rintro ⟨i, j, l, rfl⟩
    exact dD.d8_mem i j l

theorem d8_mul (i j l : Bool) (x : G) :
    dD.d8 i j l * x =
      (if i then dD.uv else 1) * ((if j then dD.t else 1) * ((if l then dD.u else 1) * x)) := by
  simp only [d8, mul_assoc]

theorem d8_mul_d8 (i j l i' j' l' : Bool) :
    dD.d8 i j l * dD.d8 i' j' l' = dD.d8 (xor i (xor i' (l && j'))) (xor j j') (xor l l') := by
  rw [d8_mul]
  cases i <;> cases j <;> cases l <;> simp [uv_mul_d8, t_mul_d8, u_mul_d8]

theorem d8_mul_self (i j l : Bool) : dD.d8 i j l * dD.d8 i j l = dD.d8 (l && j) false false := by
  rw [d8_mul_d8]
  cases i <;> cases j <;> cases l <;> rfl

theorem d8_inv (i j l : Bool) : (dD.d8 i j l)⁻¹ = dD.d8 (xor i (l && j)) j l := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [d8_mul_d8, ← dD.d8_fff]
  cases i <;> cases j <;> cases l <;> rfl

theorem ofTorus_inj : Function.Injective dD.ofTorus := by
  intro v w h
  have h1 : (Additive.toMul (dD.e.symm v) : D) = Additive.toMul (dD.e.symm w) := Subtype.ext h
  exact dD.e.symm.injective (Additive.toMul.injective h1)

theorem exists_ofTorus {x : G} (hx : x ∈ D) : ∃ v, x = dD.ofTorus v :=
  ⟨dD.e (Additive.ofMul ⟨x, hx⟩), (dD.ofTorus_e ⟨x, hx⟩).symm⟩

theorem ofTorus_comm (v w : Torus τ.k) :
    dD.ofTorus v * dD.ofTorus w = dD.ofTorus w * dD.ofTorus v := by
  rw [← dD.ofTorus_add, ← dD.ofTorus_add, add_comm]

theorem ofTorus_eq_one_iff {v : Torus τ.k} : dD.ofTorus v = 1 ↔ v = 0 := by
  rw [← dD.ofTorus_zero]
  exact dD.ofTorus_inj.eq_iff

theorem ofTorus_mul_self (v : Torus τ.k) : dD.ofTorus v * dD.ofTorus v = dD.ofTorus (v + v) :=
  (dD.ofTorus_add v v).symm

theorem uv_mul_ofTorus (v : Torus τ.k) :
    dD.uv * dD.ofTorus v = dD.ofTorus (τ.action.φuv v) * dD.uv := by
  have h := dD.conj_ofTorus dD.uv_mem dD.uv_conj v
  rw [dD.uv_inv] at h
  rw [← h, mul_assoc, dD.uv_sq, mul_one]

theorem t_mul_ofTorus (v : Torus τ.k) :
    dD.t * dD.ofTorus v = dD.ofTorus (τ.action.φt v) * dD.t := by
  have h := dD.conj_ofTorus dD.t_mem dD.t_conj v
  rw [dD.t_inv] at h
  rw [← h, mul_assoc, dD.t_sq, mul_one]

theorem u_mul_ofTorus (v : Torus τ.k) :
    dD.u * dD.ofTorus v = dD.ofTorus (τ.action.φu v) * dD.u := by
  have h := dD.conj_ofTorus dD.u_mem dD.u_conj v
  rw [dD.u_inv] at h
  rw [← h, mul_assoc, dD.u_sq, mul_one]

theorem uv_mul_ofTorus_mul (v : Torus τ.k) (x : G) :
    dD.uv * (dD.ofTorus v * x) = dD.ofTorus (τ.action.φuv v) * (dD.uv * x) := by
  rw [← mul_assoc, uv_mul_ofTorus, mul_assoc]

theorem t_mul_ofTorus_mul (v : Torus τ.k) (x : G) :
    dD.t * (dD.ofTorus v * x) = dD.ofTorus (τ.action.φt v) * (dD.t * x) := by
  rw [← mul_assoc, t_mul_ofTorus, mul_assoc]

theorem u_mul_ofTorus_mul (v : Torus τ.k) (x : G) :
    dD.u * (dD.ofTorus v * x) = dD.ofTorus (τ.action.φu v) * (dD.u * x) := by
  rw [← mul_assoc, u_mul_ofTorus, mul_assoc]

theorem d8_mul_ofTorus (i j l : Bool) (v : Torus τ.k) :
    dD.d8 i j l * dD.ofTorus v = dD.ofTorus (τ.action.d8Act i j l v) * dD.d8 i j l := by
  cases i <;> cases j <;> cases l <;>
    simp [d8, SigmaFourAction.d8Act, mul_assoc, uv_mul_ofTorus, t_mul_ofTorus, u_mul_ofTorus,
      uv_mul_ofTorus_mul, t_mul_ofTorus_mul, u_mul_ofTorus_mul]

theorem nf_commute_iff (v w : Torus τ.k) (i j l : Bool) :
    dD.ofTorus v * dD.d8 i j l * dD.ofTorus w = dD.ofTorus w * (dD.ofTorus v * dD.d8 i j l) ↔
      τ.action.d8Act i j l w = w := by
  rw [mul_assoc, dD.d8_mul_ofTorus, ← mul_assoc, ← mul_assoc, ← dD.ofTorus_add,
    ← dD.ofTorus_add, mul_left_inj, dD.ofTorus_inj.eq_iff, add_comm w v, add_right_inj]

theorem closure_le_normalizer :
    Subgroup.closure ({dD.uv, dD.t, dD.u} : Set G) ≤ Subgroup.normalizer (D : Set G) := by
  rw [Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  exacts [dD.uv_mem, dD.t_mem, dD.u_mem]

theorem mem_sup_iff {y : G} :
    y ∈ D ⊔ Subgroup.closure ({dD.uv, dD.t, dD.u} : Set G) ↔
      ∃ (v : Torus τ.k) (i j l : Bool), y = dD.ofTorus v * dD.d8 i j l := by
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left D _ dD.closure_le_normalizer,
    Set.mem_mul]
  constructor
  · rintro ⟨x, hx, w, hw, rfl⟩
    obtain ⟨v, rfl⟩ := dD.exists_ofTorus hx
    obtain ⟨i, j, l, rfl⟩ := dD.mem_closure_iff_d8.mp hw
    exact ⟨v, i, j, l, rfl⟩
  · rintro ⟨v, i, j, l, rfl⟩
    exact ⟨_, dD.ofTorus_mem v, _, dD.d8_mem i j l, rfl⟩

theorem nf_mem (v : Torus τ.k) (i j l : Bool) :
    dD.ofTorus v * dD.d8 i j l ∈ D ⊔ Subgroup.closure ({dD.uv, dD.t, dD.u} : Set G) :=
  dD.mem_sup_iff.mpr ⟨v, i, j, l, rfl⟩

theorem nf_mul_nf (v v' : Torus τ.k) (i j l i' j' l' : Bool) :
    dD.ofTorus v * dD.d8 i j l * (dD.ofTorus v' * dD.d8 i' j' l') =
      dD.ofTorus (v + τ.action.d8Act i j l v') *
        dD.d8 (xor i (xor i' (l && j'))) (xor j j') (xor l l') := by
  rw [mul_assoc, ← mul_assoc (dD.d8 i j l), dD.d8_mul_ofTorus, mul_assoc, dD.d8_mul_d8,
    ← mul_assoc, ← dD.ofTorus_add]

theorem nf_mul_self (v : Torus τ.k) (i j l : Bool) :
    dD.ofTorus v * dD.d8 i j l * (dD.ofTorus v * dD.d8 i j l) =
      dD.ofTorus (v + τ.action.d8Act i j l v) * dD.d8 (l && j) false false := by
  rw [nf_mul_nf]
  cases i <;> cases j <;> cases l <;> rfl

theorem mul_self_mem_or :
    ∀ y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u}, y * y ∈ D ∨ y * y * dD.uv ∈ D := by
  intro y hy
  obtain ⟨v, i, j, l, rfl⟩ := dD.mem_sup_iff.mp hy
  rw [nf_mul_self]
  cases l && j
  · left
    rw [d8_fff, mul_one]
    exact dD.ofTorus_mem _
  · right
    rw [d8_tff, mul_assoc, dD.uv_sq, mul_one]
    exact dD.ofTorus_mem _

theorem nf_u_mul_inv_mem (v v' : Torus τ.k) :
    dD.ofTorus v' * dD.d8 false false true * (dD.ofTorus v * dD.d8 false false true)⁻¹ ∈ D := by
  rw [mul_inv_rev, ← mul_assoc, mul_assoc (dD.ofTorus v'), mul_inv_cancel, mul_one]
  exact mul_mem (dD.ofTorus_mem _) (inv_mem (dD.ofTorus_mem _))

theorem d8_eq_of_mem
    (hF : ∀ i j l, (∀ v, τ.action.d8Act i j l v = v) → i = false ∧ j = false ∧ l = false)
    {i j l : Bool} (h : dD.d8 i j l ∈ D) : i = false ∧ j = false ∧ l = false := by
  apply hF
  intro v
  obtain ⟨w, hw⟩ := dD.exists_ofTorus h
  have hc : dD.d8 i j l * dD.ofTorus v = dD.ofTorus v * dD.d8 i j l := by
    rw [hw, ofTorus_comm]
  rw [dD.d8_mul_ofTorus] at hc
  exact dD.ofTorus_inj (mul_right_cancel hc)

theorem nf_inj
    (hF : ∀ i j l, (∀ v, τ.action.d8Act i j l v = v) → i = false ∧ j = false ∧ l = false)
    {v v' : Torus τ.k} {i j l i' j' l' : Bool}
    (h : dD.ofTorus v * dD.d8 i j l = dD.ofTorus v' * dD.d8 i' j' l') :
    v = v' ∧ i = i' ∧ j = j' ∧ l = l' := by
  have hmem : dD.d8 i' j' l' * (dD.d8 i j l)⁻¹ ∈ D := by
    have : dD.d8 i' j' l' * (dD.d8 i j l)⁻¹ = (dD.ofTorus v')⁻¹ * dD.ofTorus v := by
      rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, ← h, mul_assoc, mul_inv_cancel, mul_one]
    rw [this]
    exact mul_mem (inv_mem (dD.ofTorus_mem _)) (dD.ofTorus_mem _)
  rw [d8_inv, d8_mul_d8] at hmem
  obtain ⟨h1, h2, h3⟩ := dD.d8_eq_of_mem hF hmem
  have hijl : i = i' ∧ j = j' ∧ l = l' := by
    revert h1 h2 h3
    cases i <;> cases j <;> cases l <;> cases i' <;> cases j' <;> cases l' <;> decide
  obtain ⟨rfl, rfl, rfl⟩ := hijl
  exact ⟨dD.ofTorus_inj (mul_right_cancel h), rfl, rfl, rfl⟩

theorem d8_not_mem
    (hF : ∀ i j l, (∀ v, τ.action.d8Act i j l v = v) → i = false ∧ j = false ∧ l = false)
    {i j l : Bool} (h : ¬ (i = false ∧ j = false ∧ l = false)) (v : Torus τ.k) :
    dD.ofTorus v * dD.d8 i j l ∉ D := by
  intro hm
  apply h
  apply dD.d8_eq_of_mem hF
  have : dD.d8 i j l = (dD.ofTorus v)⁻¹ * (dD.ofTorus v * dD.d8 i j l) := by group
  rw [this]
  exact mul_mem (inv_mem (dD.ofTorus_mem v)) hm

theorem mem_S₁_iff (hk0 : 1 ≤ τ.k 0)
    (hP : ∀ i j l (v : Torus τ.k), Even ((τ.action.d8Act i j l v) 0) ↔ Even (v 0)) {y : G} :
    y ∈ Subgroup.closure
        ({(dD.c : G) ^ 2, (dD.a : G), (dD.b : G), dD.uv, dD.t, dD.u} : Set G) ↔
      ∃ (v : Torus τ.k) (i j l : Bool), Even (v 0) ∧ y = dD.ofTorus v * dD.d8 i j l := by
  constructor
  · intro hy
    induction hy using Subgroup.closure_induction with
    | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · refine ⟨Torus.c + Torus.c, false, false, false, ⟨Torus.c 0, rfl⟩, ?_⟩
        rw [d8_fff, mul_one, ofTorus_add, ← c_eq, sq]
      · refine ⟨Torus.a, false, false, false, ⟨0, by simp [gen]⟩, ?_⟩
        rw [d8_fff, mul_one, ← a_eq]
      · refine ⟨Torus.b, false, false, false, ⟨0, by simp [gen]⟩, ?_⟩
        rw [d8_fff, mul_one, ← b_eq]
      · exact ⟨0, true, false, false, ⟨0, by simp⟩, by rw [d8_tff, ofTorus_zero, one_mul]⟩
      · exact ⟨0, false, true, false, ⟨0, by simp⟩, by rw [d8_ftf, ofTorus_zero, one_mul]⟩
      · exact ⟨0, false, false, true, ⟨0, by simp⟩, by rw [d8_fft, ofTorus_zero, one_mul]⟩
    | one => exact ⟨0, false, false, false, ⟨0, by simp⟩, by rw [d8_fff, ofTorus_zero, one_mul]⟩
    | mul x y _ _ hx hy =>
      obtain ⟨v, i, j, l, hv, rfl⟩ := hx
      obtain ⟨v', i', j', l', hv', rfl⟩ := hy
      exact ⟨_, _, _, _, hv.add ((hP i j l v').mpr hv'), dD.nf_mul_nf v v' i j l i' j' l'⟩
    | inv x _ hx =>
      obtain ⟨v, i, j, l, hv, rfl⟩ := hx
      refine ⟨τ.action.d8Act (xor i (l && j)) j l (-v), xor i (l && j), j, l, ?_, ?_⟩
      · rw [hP]
        simpa using hv.neg
      · rw [mul_inv_rev, dD.d8_inv, ← dD.ofTorus_neg, dD.d8_mul_ofTorus]
  · rintro ⟨v, i, j, l, hv, rfl⟩
    have hgen : ∀ x ∈ ({(dD.c : G) ^ 2, (dD.a : G), (dD.b : G), dD.uv, dD.t, dD.u} : Set G),
        x ∈ Subgroup.closure
          ({(dD.c : G) ^ 2, (dD.a : G), (dD.b : G), dD.uv, dD.t, dD.u} : Set G) :=
      fun x hx => Subgroup.subset_closure hx
    refine mul_mem ?_ ?_
    · obtain ⟨x, rfl⟩ := Torus.exists_ofInt v
      rw [Torus.ofInt_apply, Stroth42Core.even_intCast_iff hk0] at hv
      obtain ⟨r, hr⟩ := hv
      have hdec : Torus.ofInt τ.k x =
          r • (Torus.c + Torus.c) + x 1 • Torus.a + x 2 • Torus.b := by
        rw [Torus.ofInt_eq_zsmul_gens, hr, add_zsmul, smul_add]
      rw [hdec, ofTorus_add, ofTorus_add]
      have hz : ∀ (z : ℤ) (w : Torus τ.k), dD.ofTorus (z • w) = dD.ofTorus w ^ z := by
        intro z w
        rcases z with z | z
        · rw [Int.ofNat_eq_coe, natCast_zsmul, ofTorus_nsmul, zpow_natCast]
        · rw [Int.negSucc_eq, neg_zsmul, ofTorus_neg, zpow_neg]
          congr 1
          rw [← Int.natCast_succ, natCast_zsmul, ofTorus_nsmul, zpow_natCast]
      rw [hz, hz, hz, ofTorus_add, ← c_eq, ← a_eq, ← b_eq, ← sq]
      exact mul_mem (mul_mem (zpow_mem (hgen _ (by simp)) _) (zpow_mem (hgen _ (by simp)) _))
        (zpow_mem (hgen _ (by simp)) _)
    · have hle : Subgroup.closure ({dD.uv, dD.t, dD.u} : Set G) ≤ Subgroup.closure
          ({(dD.c : G) ^ 2, (dD.a : G), (dD.b : G), dD.uv, dD.t, dD.u} : Set G) := by
        rw [Subgroup.closure_le]
        intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl | rfl <;> exact hgen _ (by simp)
      exact hle (dD.d8_mem i j l)

theorem c_not_mem_S₁ (hk0 : 1 ≤ τ.k 0)
    (hF : ∀ i j l, (∀ v, τ.action.d8Act i j l v = v) → i = false ∧ j = false ∧ l = false)
    (hP : ∀ i j l (v : Torus τ.k), Even ((τ.action.d8Act i j l v) 0) ↔ Even (v 0)) :
    (dD.c : G) ∉
      Subgroup.closure {(dD.c : G) ^ 2, (dD.a : G), (dD.b : G), dD.uv, dD.t, dD.u} := by
  intro h
  obtain ⟨v, i, j, l, hv, he⟩ := (dD.mem_S₁_iff hk0 hP).mp h
  rw [c_eq, ← mul_one (dD.ofTorus Torus.c), ← dD.d8_fff] at he
  obtain ⟨rfl, -, -, -⟩ := dD.nf_inj hF he
  have h1 : Odd ((Torus.c : Torus τ.k) 0) := ⟨0, by simp [gen]⟩
  exact Stroth42Core.zmod_not_even_of_odd hk0 h1 hv

theorem relIndex_S₁ (hk0 : 1 ≤ τ.k 0)
    (hF : ∀ i j l, (∀ v, τ.action.d8Act i j l v = v) → i = false ∧ j = false ∧ l = false)
    (hP : ∀ i j l (v : Torus τ.k), Even ((τ.action.d8Act i j l v) 0) ↔ Even (v 0)) :
    (Subgroup.closure {(dD.c : G) ^ 2, (dD.a : G), (dD.b : G), dD.uv, dD.t, dD.u}).relIndex
      (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u}) = 2 := by
  rw [Subgroup.relIndex_eq_two_iff]
  refine ⟨dD.c, Subgroup.mem_sup_left dD.c.2, fun y hy => ?_⟩
  obtain ⟨v, i, j, l, rfl⟩ := dD.mem_sup_iff.mp hy
  have hS₁ : ∀ x : G, x ∈ Subgroup.closure
        ({(dD.c : G) ^ 2, (dD.a : G), (dD.b : G), dD.uv, dD.t, dD.u} : Set G) ↔
      ∃ (v : Torus τ.k) (i j l : Bool), Even (v 0) ∧ x = dD.ofTorus v * dD.d8 i j l :=
    fun x => dD.mem_S₁_iff hk0 hP
  rcases Stroth42Core.zmod_even_or_odd (v 0) with hv | hv
  · have hy1 := (hS₁ _).mpr ⟨v, i, j, l, hv, rfl⟩
    refine Or.inr ⟨hy1, fun h => dD.c_not_mem_S₁ hk0 hF hP ?_⟩
    have := mul_mem (inv_mem hy1) h
    rwa [inv_mul_cancel_left] at this
  · refine Or.inl ⟨?_, fun h => ?_⟩
    · rw [c_eq, mul_assoc, dD.d8_mul_ofTorus, ← mul_assoc, ← dD.ofTorus_add]
      refine (hS₁ _).mpr ⟨_, i, j, l, ?_, rfl⟩
      have hc : Odd ((τ.action.d8Act i j l Torus.c) 0) := by
        rw [← Stroth42Core.zmod_not_even_iff_odd hk0, hP,
          Stroth42Core.zmod_not_even_iff_odd hk0]
        exact ⟨0, by simp [gen]⟩
      exact hv.add_odd hc
    · obtain ⟨v', i', j', l', hv', he⟩ := (hS₁ _).mp h
      obtain ⟨rfl, -, -, -⟩ := dD.nf_inj hF he
      exact Stroth42Core.zmod_not_even_of_odd hk0 hv hv'

end StrothWeakTypeData

end CFSG.CGT.Stroth77
