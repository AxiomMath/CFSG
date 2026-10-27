module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7Prod
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7TwoWTr
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8Phi

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL

namespace F7K

open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.F94
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.F7E
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.F7J

section Act

variable {Q : Type} [Group Q] {X : Type*} [MulAction Q X]

theorem cover3A {w : X} {q₁ q₂ : Q}
    (hcov : ∀ q : Q, q • w = w ∨ q • w = q₁ • w ∨
      q • w = q₂ • w)
    {g₁ g₂ : Q} (hg1 : g₁ • w ≠ w) (hg2 : g₂ • w ≠ w)
    (hg12 : g₁ • w ≠ g₂ • w) (q : Q) :
    q • w = w ∨ q • w = g₁ • w ∨ q • w = g₂ • w :=
  pigeon (Or.inl rfl) (hcov g₁) (hcov g₂) (hcov q) hg1.symm hg2.symm hg12

theorem block3A {w : X} {q₁ q₂ : Q}
    (hcov : ∀ q : Q, q • w = w ∨ q • w = q₁ • w ∨
      q • w = q₂ • w)
    (h01 : q₁ • w ≠ w) (h02 : q₂ • w ≠ w) (h12 : q₁ • w ≠ q₂ • w)
    (R : Q → Q → Prop) (hRs : ∀ {x y : Q}, R x y → R y x)
    (hRt : ∀ {x y w : Q}, R x y → R y w → R x w)
    (hRc : ∀ (c : Q) {x y : Q}, R x y → R (c * x * c⁻¹) (c * y * c⁻¹)) {y₀ : Q}
    (hR : ∀ q d : Q, q • w = d • w → R (q * y₀ * q⁻¹) (d * y₀ * d⁻¹))
    {g : Q} (hg : g • w ≠ w) (hgy : R (g * y₀ * g⁻¹) y₀) (d : Q) :
    R (d * y₀ * d⁻¹) y₀ := by
  have hone : (1 : Q) * y₀ * 1⁻¹ = y₀ := by group
  have h1 : ∀ q : Q, q • w = w → R (q * y₀ * q⁻¹) y₀ := by
    intro q h
    have := hR q 1 (by rw [one_smul]; exact h)
    rwa [hone] at this
  by_cases hd0 : d • w = w
  · exact h1 d hd0
  by_cases hdg : d • w = g • w
  · exact hRt (hR d g hdg) hgy
  have hdg' : (d * g) • w ≠ d • w := by
    rw [mul_smul]
    exact fun h => hg ((MulAction.injective d) h)
  have hR' : R (d * y₀ * d⁻¹) ((d * g) * y₀ * (d * g)⁻¹) := by
    have := hRs (hRc d hgy)
    have e : d * (g * y₀ * g⁻¹) * d⁻¹ = (d * g) * y₀ * (d * g)⁻¹ := by group
    rwa [e] at this
  rcases cover3A hcov hg hd0 (Ne.symm hdg) (d * g) with h | h | h
  · exact hRt hR' (h1 _ h)
  · exact hRt hR' (hRt (hR _ _ h) hgy)
  · exact absurd h hdg'

theorem exists_three_cycleA {w : X} {q₁ q₂ : Q}
    (hcov : ∀ q : Q, q • w = w ∨ q • w = q₁ • w ∨
      q • w = q₂ • w)
    (h01 : q₁ • w ≠ w) (h02 : q₂ • w ≠ w) (h12 : q₁ • w ≠ q₂ • w) :
    ∃ c : Q, c • w ≠ w ∧ (c * c) • w ≠ w ∧ (c * c * c) • w = w := by
  obtain ⟨c, hc1, hc2⟩ : ∃ c : Q, c • w ≠ w ∧ (c * c) • w ≠ w := by
    by_cases hq1 : (q₁ * q₁) • w = w
    swap
    · exact ⟨q₁, h01, hq1⟩
    by_cases hq2 : (q₂ * q₂) • w = w
    swap
    · exact ⟨q₂, h02, hq2⟩
    have hq1' : q₁ • q₁ • w = w := by rw [← mul_smul]; exact hq1
    have hq2' : q₂ • q₂ • w = w := by rw [← mul_smul]; exact hq2
    have hc : (q₁ * q₂) • w = q₂ • w := by
      rcases hcov (q₁ * q₂) with h | h | h
      · exfalso
        apply h12
        apply MulAction.injective q₁
        dsimp only
        rw [hq1', ← mul_smul, h]
      · exfalso
        apply h02
        apply MulAction.injective q₁
        dsimp only
        rw [← mul_smul, h]
      · exact h
    refine ⟨q₁ * q₂, by rw [hc]; exact h02, ?_⟩
    rw [mul_smul, hc, mul_smul, hq2']
    exact h01
  have hc12 : c • w ≠ (c * c) • w := by
    rw [mul_smul c c]
    intro h
    exact hc1 ((MulAction.injective c) h).symm
  refine ⟨c, hc1, hc2, ?_⟩
  rcases cover3A hcov hc1 hc2 hc12 (c * c * c) with h | h | h
  · exact h
  · exfalso
    apply hc2
    apply MulAction.injective c
    dsimp only
    rw [← mul_smul, ← mul_assoc]
    exact h
  · exfalso
    apply hc12
    apply MulAction.injective c
    dsimp only
    rw [← mul_smul, ← mul_smul, ← mul_assoc]
    exact h.symm

theorem exists_odd_moveA [Finite Q] {w : X} {q₁ q₂ : Q}
    (hcov : ∀ q : Q, q • w = w ∨ q • w = q₁ • w ∨
      q • w = q₂ • w)
    (h01 : q₁ • w ≠ w) (h02 : q₂ • w ≠ w) (h12 : q₁ • w ≠ q₂ • w) :
    ∃ x : Q, ∃ m : ℕ, Odd m ∧ x ^ m = 1 ∧ x • w ≠ w := by
  obtain ⟨c, hc1, hc2, hc3⟩ := exists_three_cycleA hcov h01 h02 h12
  obtain ⟨α, m, hm, hcm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos c).ne'
  refine ⟨c ^ (2 ^ α), m, hm, by rw [← pow_mul, ← hcm, pow_orderOf_eq_one], ?_⟩
  have h3 : ∀ j : ℕ, (c ^ (3 * j)) • w = w := by
    intro j
    induction j with
    | zero => rw [Nat.mul_zero, pow_zero, one_smul]
    | succ j ih => rw [mul_add, mul_one, pow_add, mul_smul, pow_three', hc3, ih]
  have hmod : ∀ N : ℕ, (c ^ N) • w = (c ^ (N % 3)) • w := by
    intro N
    conv_lhs => rw [← Nat.mod_add_div N 3, pow_add, mul_smul, h3]
  have h2 : 2 ^ α % 3 = 1 ∨ 2 ^ α % 3 = 2 := by
    have hn : ¬ 3 ∣ 2 ^ α := fun h => by
      have := Nat.prime_three.dvd_of_dvd_pow h
      omega
    generalize 2 ^ α = N at hn ⊢
    omega
  rw [hmod]
  rcases h2 with h | h <;> rw [h]
  · rwa [pow_one]
  · rwa [pow_two]

theorem prod_coreA [Finite Q] {A B : Subgroup Q} {z : Q} (hz : ∀ q : Q, q * z = z * q)
    (hsA : IsUniqueInvolution A z) (hsB : IsUniqueInvolution B z) (h8A : Nat.card A = 8)
    (h8B : Nat.card B = 8) (hnabA : ∃ x ∈ A, ∃ y ∈ A, x * y ≠ y * x)
    (hnabB : ∃ x ∈ B, ∃ y ∈ B, x * y ≠ y * x) (hcomm : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x)
    (hperm : ∀ q : Q, (conjSub q A = A ∧ conjSub q B = B) ∨ (conjSub q A = B ∧ conjSub q B = A))
    {a b : Q} (ha : a ∈ A) (hb : b ∈ B) (ha1 : a ≠ 1) (haz : a ≠ z) (hb1 : b ≠ 1) (hbz : b ≠ z)
    {s : Q} (hsAB : conjSub s A = B) (hsBA : conjSub s B = A)
    (hsp : ModZ z (s * (a * b) * s⁻¹) (a * b))
    {eb : Q} (heA : ∀ x ∈ A, eb * x = x * eb) (heB : ∀ x ∈ B, eb * x = x * eb)
    (hMB : ∀ m : Q, (∀ x ∈ A, m * x = x * m) → (∀ x ∈ B, m * x = x * m) → m * eb = eb * m)
    (he2 : eb * eb = 1) (heb1 : eb ≠ 1) (hebz : eb ≠ z) {w : X}
    (hWp : ∀ q d : Q, q • w = d • w →
      ModZ z (q * (a * b) * q⁻¹) (d * (a * b) * d⁻¹))
    (hWe : ∀ q d : Q, q • w = d • w → q * eb * q⁻¹ = d * eb * d⁻¹)
    (hM1 : ∃ r₁ r₂ : Q, ∀ q : Q, ∃ d : Q, (d = 1 ∨ d = r₁ ∨ d = r₂) ∧
      q • w = d • w)
    {q₁ q₂ : Q} (h01 : q₁ • w ≠ w) (h02 : q₂ • w ≠ w)
    (h12 : q₁ • w ≠ q₂ • w)
    (hCen : (∀ q : Q, q * (eb * (q₁ * eb * q₁⁻¹) * (q₂ * eb * q₂⁻¹)) =
        (eb * (q₁ * eb * q₁⁻¹) * (q₂ * eb * q₂⁻¹)) * q) →
      (eb * (q₁ * eb * q₁⁻¹) * (q₂ * eb * q₂⁻¹)) * (eb * (q₁ * eb * q₁⁻¹) * (q₂ * eb * q₂⁻¹)) = 1 →
      eb * (q₁ * eb * q₁⁻¹) * (q₂ * eb * q₂⁻¹) = 1 ∨ eb * (q₁ * eb * q₁⁻¹) * (q₂ * eb * q₂⁻¹) = z)
    (hnc : ¬ ∀ d : Q, d * eb * d⁻¹ = eb) :
    a * b * eb * (q₁ * (a * b * eb) * q₁⁻¹) * (q₂ * (a * b * eb) * q₂⁻¹) = 1 ∨
      a * b * eb * (q₁ * (a * b * eb) * q₁⁻¹) * (q₂ * (a * b * eb) * q₂⁻¹) = z := by
  have hz2 := hsA.sq
  have hinf : ∀ w ∈ A, w ∈ B → w = 1 ∨ w = z := fun w hwA hwB =>
    mem_inf_q8 hz hsA h8A hnabA hcomm hwA hwB
  have hmem : ∀ (g : Q) (M N : Subgroup Q), conjSub g M = N → ∀ m ∈ M, g * m * g⁻¹ ∈ N :=
    fun g M N h m hm => h ▸ conj_mem_conjSub hm
  have hone : ∀ y : Q, (1 : Q) * y * 1⁻¹ = y := fun y => by group
  obtain ⟨r₁, r₂, hr⟩ := hM1
  have hcov : ∀ q : Q, q • w = w ∨ q • w = q₁ • w ∨
      q • w = q₂ • w := by
    have hlab : ∀ q : Q, q • w = w ∨ q • w = r₁ • w ∨
        q • w = r₂ • w := by
      intro q
      obtain ⟨d, hd, h⟩ := hr q
      rcases hd with rfl | rfl | rfl
      · left; rw [h, one_smul]
      · right; left; exact h
      · right; right; exact h
    intro q
    exact pigeon (Or.inl rfl) (hlab q₁) (hlab q₂) (hlab q) (Ne.symm h01) (Ne.symm h02) h12
  have hW1 : ∀ q : Q, q • w = w → q • w = (1 : Q) • w := fun q h => by
    rw [one_smul]; exact h
  have hEc : ∀ ρ x : Q, (x ∈ A ∨ x ∈ B) → (ρ * eb * ρ⁻¹) * x = x * (ρ * eb * ρ⁻¹) := by
    intro ρ x hx
    have hx' : ρ⁻¹ * x * ρ ∈ A ∨ ρ⁻¹ * x * ρ ∈ B := by
      have e : ρ⁻¹ * x * ρ = ρ⁻¹ * x * ρ⁻¹⁻¹ := by rw [inv_inv]
      rw [e]
      rcases hx with hx | hx <;> rcases hperm ρ⁻¹ with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl (hmem _ _ _ h1 _ hx)
      · exact Or.inr (hmem _ _ _ h1 _ hx)
      · exact Or.inr (hmem _ _ _ h2 _ hx)
      · exact Or.inl (hmem _ _ _ h2 _ hx)
    have h1 : eb * (ρ⁻¹ * x * ρ) = (ρ⁻¹ * x * ρ) * eb := by
      rcases hx' with h | h
      · exact heA _ h
      · exact heB _ h
    calc ρ * eb * ρ⁻¹ * x = ρ * (eb * (ρ⁻¹ * x * ρ)) * ρ⁻¹ := by group
      _ = ρ * ((ρ⁻¹ * x * ρ) * eb) * ρ⁻¹ := by rw [h1]
      _ = x * (ρ * eb * ρ⁻¹) := by group
  have hEE : ∀ γ δ : Q, (γ * eb * γ⁻¹) * (δ * eb * δ⁻¹) = (δ * eb * δ⁻¹) * (γ * eb * γ⁻¹) :=
    F7I.conj_comm_of_cent hperm heA heB hMB
  have horb : ∀ q : Q, ∃ d : Q, (d = 1 ∨ d = q₁ ∨ d = q₂) ∧
      ModZ z (q * (a * b) * q⁻¹) (d * (a * b) * d⁻¹) := by
    intro q
    rcases hcov q with h | h | h
    · exact ⟨1, Or.inl rfl, hWp q 1 (hW1 q h)⟩
    · exact ⟨q₁, Or.inr (Or.inl rfl), hWp q q₁ h⟩
    · exact ⟨q₂, Or.inr (Or.inr rfl), hWp q q₂ h⟩
  have hPP : ∀ γ δ : Q, (γ * (a * b) * γ⁻¹) * (δ * (a * b) * δ⁻¹) =
      (δ * (a * b) * δ⁻¹) * (γ * (a * b) * γ⁻¹) := by
    intro γ δ
    have h := comm_conj_of_orbit hz hsA hsB h8A h8B hnabA hnabB hcomm hinf hperm ha hb ha1 haz
      hb1 hbz hsAB hsBA hsp horb (γ⁻¹ * δ)
    have h' := (conj_comm_iff γ ((γ⁻¹ * δ) * (a * b) * (γ⁻¹ * δ)⁻¹) (a * b)).mpr h
    have e : γ * ((γ⁻¹ * δ) * (a * b) * (γ⁻¹ * δ)⁻¹) * γ⁻¹ = δ * (a * b) * δ⁻¹ := by group
    rw [e] at h'
    exact h'.symm
  have hEP : ∀ γ δ : Q, (γ * eb * γ⁻¹) * (δ * (a * b) * δ⁻¹) =
      (δ * (a * b) * δ⁻¹) * (γ * eb * γ⁻¹) := by
    intro γ δ
    have hδa : δ * a * δ⁻¹ ∈ A ∨ δ * a * δ⁻¹ ∈ B := by
      rcases hperm δ with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact Or.inl (hmem δ A A h1 a ha)
      · exact Or.inr (hmem δ A B h1 a ha)
    have hδb : δ * b * δ⁻¹ ∈ A ∨ δ * b * δ⁻¹ ∈ B := by
      rcases hperm δ with ⟨-, h2⟩ | ⟨-, h2⟩
      · exact Or.inr (hmem δ B B h2 b hb)
      · exact Or.inl (hmem δ B A h2 b hb)
    have e : δ * (a * b) * δ⁻¹ = (δ * a * δ⁻¹) * (δ * b * δ⁻¹) := by group
    rw [e]
    calc (γ * eb * γ⁻¹) * ((δ * a * δ⁻¹) * (δ * b * δ⁻¹))
        = ((γ * eb * γ⁻¹) * (δ * a * δ⁻¹)) * (δ * b * δ⁻¹) := (mul_assoc _ _ _).symm
      _ = ((δ * a * δ⁻¹) * (γ * eb * γ⁻¹)) * (δ * b * δ⁻¹) := by rw [hEc γ _ hδa]
      _ = (δ * a * δ⁻¹) * ((γ * eb * γ⁻¹) * (δ * b * δ⁻¹)) := mul_assoc _ _ _
      _ = (δ * a * δ⁻¹) * ((δ * b * δ⁻¹) * (γ * eb * γ⁻¹)) := by rw [hEc γ _ hδb]
      _ = ((δ * a * δ⁻¹) * (δ * b * δ⁻¹)) * (γ * eb * γ⁻¹) := (mul_assoc _ _ _).symm
  have hX : a * b * eb * (q₁ * (a * b * eb) * q₁⁻¹) * (q₂ * (a * b * eb) * q₂⁻¹) =
      ((a * b) * (q₁ * (a * b) * q₁⁻¹) * (q₂ * (a * b) * q₂⁻¹)) *
        (eb * (q₁ * eb * q₁⁻¹) * (q₂ * eb * q₂⁻¹)) := by
    have e1 : ∀ q : Q, q * (a * b * eb) * q⁻¹ = (q * (a * b) * q⁻¹) * (q * eb * q⁻¹) :=
      fun q => by group
    rw [e1 q₁, e1 q₂]
    refine rearr ?_ (hEP q₁ q₂) ?_
    · have := hEP 1 q₁; rwa [hone] at this
    · have := hEP 1 q₂; rwa [hone] at this
  have k01 := hEE 1 q₁
  have k02 := hEE 1 q₂
  have k12 := hEE q₁ q₂
  rw [hone] at k01 k02
  have hf2 : (eb * (q₁ * eb * q₁⁻¹) * (q₂ * eb * q₂⁻¹)) *
      (eb * (q₁ * eb * q₁⁻¹) * (q₂ * eb * q₂⁻¹)) = 1 := by
    have hc : ∀ γ : Q, (γ * eb * γ⁻¹) * (γ * eb * γ⁻¹) = 1 := fun γ => by
      calc (γ * eb * γ⁻¹) * (γ * eb * γ⁻¹) = γ * (eb * eb) * γ⁻¹ := by group
        _ = 1 := by rw [he2]; group
    exact sq3 k01 k02 k12 he2 (hc q₁) (hc q₂)
  have hcov1 : ∀ q : Q, q • w = (1 : Q) • w ∨ q • w = q₁ • w ∨
      q • w = q₂ • w := by
    intro q
    rcases hcov q with h | h | h
    · exact Or.inl (hW1 q h)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have hfc : ∀ c : Q, c * (eb * (q₁ * eb * q₁⁻¹) * (q₂ * eb * q₂⁻¹)) =
      (eb * (q₁ * eb * q₁⁻¹) * (q₂ * eb * q₂⁻¹)) * c := by
    intro c
    refine (comm_of_conj_eq' ?_).symm
    have e : c * (eb * (q₁ * eb * q₁⁻¹) * (q₂ * eb * q₂⁻¹)) * c⁻¹ =
        (c * eb * c⁻¹) * ((c * q₁) * eb * (c * q₁)⁻¹) * ((c * q₂) * eb * (c * q₂)⁻¹) := by group
    rw [e]
    have d01 : c • w ≠ (c * q₁) • w := by
      rw [mul_smul]; exact fun h => h01 ((MulAction.injective c) h).symm
    have d02 : c • w ≠ (c * q₂) • w := by
      rw [mul_smul]; exact fun h => h02 ((MulAction.injective c) h).symm
    have d12 : (c * q₁) • w ≠ (c * q₂) • w := by
      rw [mul_smul, mul_smul]; exact fun h => h12 ((MulAction.injective c) h)
    have P := perm3 k01 k02 k12
    rcases hcov1 c with h0 | h0 | h0 <;> rcases hcov1 (c * q₁) with h1 | h1 | h1 <;>
      rcases hcov1 (c * q₂) with h2 | h2 | h2 <;>
      first
      | exact absurd (h0.trans h1.symm) d01
      | exact absurd (h0.trans h2.symm) d02
      | exact absurd (h1.trans h2.symm) d12
      | (rw [hWe _ _ h0, hWe _ _ h1, hWe _ _ h2, hone] <;>
         first
         | rfl
         | exact P.1
         | exact P.2.1
         | exact P.2.2.1
         | exact P.2.2.2.1
         | exact P.2.2.2.2)
  have hfz := hCen hfc hf2
  by_cases hB : ModZ z (q₁ * (a * b) * q₁⁻¹) (a * b) ∨ ModZ z (q₂ * (a * b) * q₂⁻¹) (a * b) ∨
      ModZ z (q₁ * (a * b) * q₁⁻¹) (q₂ * (a * b) * q₂⁻¹)
  · exfalso
    obtain ⟨g, hg, hgp⟩ : ∃ g : Q, g • w ≠ w ∧ ModZ z (g * (a * b) * g⁻¹) (a * b) := by
      rcases hB with h | h | h
      · exact ⟨q₁, h01, h⟩
      · exact ⟨q₂, h02, h⟩
      · refine ⟨q₁⁻¹ * q₂, ?_, ?_⟩
        · intro h'
          apply h12
          calc q₁ • w = q₁ • (q₁⁻¹ * q₂) • w := by rw [h']
            _ = q₂ • w := by rw [← mul_smul, mul_inv_cancel_left]
        · have := ModZ.symm hz2 (ModZ.conj hz h q₁⁻¹)
          have e1 : q₁⁻¹ * (q₁ * (a * b) * q₁⁻¹) * q₁⁻¹⁻¹ = a * b := by group
          have e2 : q₁⁻¹ * (q₂ * (a * b) * q₂⁻¹) * q₁⁻¹⁻¹ =
              (q₁⁻¹ * q₂) * (a * b) * (q₁⁻¹ * q₂)⁻¹ := by group
          rwa [e1, e2] at this
    have hall : ∀ d : Q, ModZ z (d * (a * b) * d⁻¹) (a * b) :=
      block3A hcov h01 h02 h12 (ModZ z) (fun h => ModZ.symm hz2 h)
        (fun h₁ h₂ => ModZ.trans hz2 h₁ h₂) (fun c {_ _} h => ModZ.conj hz h c) hWp hg hgp
    obtain ⟨x, m, hm, hxm, hxW⟩ := exists_odd_moveA hcov h01 h02 h12
    have hAB : A ≠ B := by
      intro h
      obtain ⟨x, hx, y, hy, hxy⟩ := hnabA
      exact hxy (hcomm x hx y (by rw [← h]; exact hy))
    have hxA : conjSub x A = A := fix_of_odd hAB hm hxm (hperm x)
    have hxB : conjSub x B = B := by
      rcases hperm x with ⟨-, h⟩ | ⟨h, -⟩
      · exact h
      · exact absurd (hxA.symm.trans h) hAB
    have hxa : x * a * x⁻¹ ∈ A := hmem x A A hxA a ha
    have hxb : x * b * x⁻¹ ∈ B := hmem x B B hxB b hb
    have hdx : ModZ z ((x * a * x⁻¹) * (x * b * x⁻¹)) (a * b) := by
      have e : (x * a * x⁻¹) * (x * b * x⁻¹) = x * (a * b) * x⁻¹ := by group
      rw [e]
      exact hall x
    obtain ⟨hma, hmb⟩ := dec_of_modZ hz hz2 hsB.mem hinf ha hxa hb hxb hdx
    have hcA := cent_of_odd_q8 hz hsA h8A hnabA hxm hm (hmem x A A hxA) ha ha1 haz hma
    have hcB := cent_of_odd_q8 hz hsB h8B hnabB hxm hm (hmem x B B hxB) hb hb1 hbz hmb
    have hxe : x * eb * x⁻¹ = eb := by
      have h := hMB x (fun w hw => (comm_of_conj_eq' (hcA w hw)).symm)
        (fun w hw => (comm_of_conj_eq' (hcB w hw)).symm)
      rw [h, mul_inv_cancel_right]
    have hebc : ∀ d : Q, d * eb * d⁻¹ = eb :=
      block3A hcov h01 h02 h12 (· = ·) Eq.symm Eq.trans (fun c {_ _} h => by rw [h]) hWe hxW hxe
    exact hnc hebc
  rw [not_or, not_or] at hB
  obtain ⟨n1, n2, n12⟩ := hB
  have hnt : ∀ (g x : Q), x ≠ 1 → x ≠ z → g * x * g⁻¹ ≠ 1 ∧ g * x * g⁻¹ ≠ z := by
    intro g x h1 h2
    constructor
    · intro h
      apply h1
      calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group
    · intro h
      apply h2
      calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
        _ = g⁻¹ * (z * g) := by rw [h]; group
        _ = g⁻¹ * (g * z) := by rw [hz g]
        _ = z := by group
  have hdecomp : ∀ g : Q, ∃ a' ∈ A, ∃ b' ∈ B, a' ≠ 1 ∧ a' ≠ z ∧ b' ≠ 1 ∧ b' ≠ z ∧
      g * (a * b) * g⁻¹ = a' * b' := by
    intro g
    obtain ⟨hga1, hgaz⟩ := hnt g a ha1 haz
    obtain ⟨hgb1, hgbz⟩ := hnt g b hb1 hbz
    rcases hperm g with ⟨hA, hB⟩ | ⟨hA, hB⟩
    · exact ⟨_, hmem g A A hA a ha, _, hmem g B B hB b hb, hga1, hgaz, hgb1, hgbz, by group⟩
    · refine ⟨_, hmem g B A hB b hb, _, hmem g A B hA a ha, hgb1, hgbz, hga1, hgaz, ?_⟩
      calc g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
        _ = (g * b * g⁻¹) * (g * a * g⁻¹) :=
          (hcomm _ (hmem g B A hB b hb) _ (hmem g A B hA a ha)).symm
  obtain ⟨α₁, hα₁, β₁, hβ₁, hα₁1, hα₁z, hβ₁1, hβ₁z, hP1⟩ := hdecomp q₁
  obtain ⟨α₂, hα₂, β₂, hβ₂, hα₂1, hα₂z, hβ₂1, hβ₂z, hP2⟩ := hdecomp q₂
  have hPP0 : ∀ δ : Q, (a * b) * (δ * (a * b) * δ⁻¹) = (δ * (a * b) * δ⁻¹) * (a * b) := by
    intro δ
    have := hPP 1 δ
    rwa [hone] at this
  rw [hP1] at n1
  rw [hP2] at n2
  rw [hP1, hP2] at n12
  have hc01 : (a * b) * (α₁ * β₁) = (α₁ * β₁) * (a * b) := by rw [← hP1]; exact hPP0 q₁
  have hc02 : (a * b) * (α₂ * β₂) = (α₂ * β₂) * (a * b) := by rw [← hP2]; exact hPP0 q₂
  have hc21 : (α₂ * β₂) * (α₁ * β₁) = (α₁ * β₁) * (α₂ * β₂) := by
    rw [← hP1, ← hP2]; exact hPP q₂ q₁
  obtain ⟨na01, nb01⟩ := noncomm_of_not_modZ hz hsA hsB h8A h8B hnabA hnabB hcomm ha hα₁ hb hβ₁
    ha1 haz hα₁1 hα₁z hb1 hbz hβ₁1 hβ₁z hc01 n1
  obtain ⟨na02, nb02⟩ := noncomm_of_not_modZ hz hsA hsB h8A h8B hnabA hnabB hcomm ha hα₂ hb hβ₂
    ha1 haz hα₂1 hα₂z hb1 hbz hβ₂1 hβ₂z hc02 n2
  obtain ⟨na21, nb21⟩ := noncomm_of_not_modZ hz hsA hsB h8A h8B hnabA hnabB hcomm hα₂ hα₁ hβ₂
    hβ₁ hα₂1 hα₂z hα₁1 hα₁z hβ₂1 hβ₂z hβ₁1 hβ₁z hc21 n12
  have tA := triple_q8 hz hsA h8A hnabA ha hα₁ hα₂ na01 na02 (fun h => na21 h.symm)
  have tB := triple_q8 hz hsB h8B hnabB hb hβ₁ hβ₂ nb01 nb02 (fun h => nb21 h.symm)
  have hsplit : a * b * (α₁ * β₁) * (α₂ * β₂) = (a * α₁ * α₂) * (b * β₁ * β₂) := by
    calc a * b * (α₁ * β₁) * (α₂ * β₂) = a * (b * α₁) * β₁ * α₂ * β₂ := by group
      _ = a * (α₁ * b) * β₁ * α₂ * β₂ := by rw [← hcomm α₁ hα₁ b hb]
      _ = a * α₁ * (b * β₁ * α₂) * β₂ := by group
      _ = a * α₁ * (α₂ * (b * β₁)) * β₂ := by rw [← hcomm α₂ hα₂ (b * β₁) (B.mul_mem hb hβ₁)]
      _ = a * α₁ * α₂ * (b * β₁ * β₂) := by group
  rw [hX, hP1, hP2, hsplit]
  rcases tA with h | h <;> rcases tB with h' | h' <;> rcases hfz with h'' | h'' <;>
    rw [h, h', h''] <;> simp [hz2]

end Act

section Index

variable {Q : Type} [Group Q] [Finite Q]

abbrev zSub {A : Subgroup Q} {z : Q} (hs : IsUniqueInvolution A z) : Subgroup ↥A :=
  Subgroup.zpowers ⟨z, hs.mem⟩

theorem zSub_normal {A : Subgroup Q} {z : Q} (hz : ∀ q : Q, q * z = z * q)
    (hs : IsUniqueInvolution A z) : (zSub hs).Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
  have hc : Commute g (⟨z, hs.mem⟩ : ↥A) := Subtype.ext (hz g)
  rw [(hc.zpow_right k).eq, mul_inv_cancel_right]
  exact Subgroup.zpow_mem_zpowers _ k

theorem mem_zSub {A : Subgroup Q} {z : Q} (hs : IsUniqueInvolution A z) {w : ↥A}
    (hw : w ∈ zSub hs) : w = 1 ∨ w = ⟨z, hs.mem⟩ := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  have h2 : (⟨z, hs.mem⟩ : ↥A) * ⟨z, hs.mem⟩ = 1 := Subtype.ext hs.sq
  have hk : (⟨z, hs.mem⟩ : ↥A) ^ k = ⟨z, hs.mem⟩ ^ (k % 2) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv k 2, zpow_add, zpow_mul]
    rw [zpow_two, h2, one_zpow, mul_one]
  rw [hk]
  rcases Int.emod_two_eq_zero_or_one k with h | h <;> rw [h]
  · left; exact zpow_zero _
  · right; rw [zpow_one]

theorem aut_fix_z {A : Subgroup Q} {z : Q} (hs : IsUniqueInvolution A z) (φ : MulAut ↥A) :
    φ ⟨z, hs.mem⟩ = ⟨z, hs.mem⟩ := by
  have h2 : φ ⟨z, hs.mem⟩ * φ ⟨z, hs.mem⟩ = 1 := by
    rw [← map_mul, show (⟨z, hs.mem⟩ : ↥A) * ⟨z, hs.mem⟩ = 1 from Subtype.ext hs.sq, map_one]
  rcases hs.unique _ (φ ⟨z, hs.mem⟩).2 (congrArg Subtype.val h2) with h | h
  · exfalso
    apply hs.ne_one
    have h1 : φ ⟨z, hs.mem⟩ = φ 1 := by rw [map_one]; exact Subtype.ext h
    exact congrArg Subtype.val (φ.injective h1)
  · exact Subtype.ext h

theorem aut_map_zSub {A : Subgroup Q} {z : Q} (hs : IsUniqueInvolution A z) (φ : MulAut ↥A) :
    (zSub hs).map (φ : ↥A ≃* ↥A).toMonoidHom = zSub hs := by
  rw [MonoidHom.map_zpowers]
  congr 1
  exact aut_fix_z hs φ

noncomputable def autQuot {A : Subgroup Q} {z : Q} (hs : IsUniqueInvolution A z)
    [(zSub hs).Normal] : MulAut ↥A →* Equiv.Perm (↥A ⧸ zSub hs) where
  toFun φ := (QuotientGroup.congr (zSub hs) (zSub hs) φ (aut_map_zSub hs φ)).toEquiv
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl
  map_mul' φ ψ := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl

theorem autQuot_ker_sq {A : Subgroup Q} {z : Q} (hs : IsUniqueInvolution A z)
    [(zSub hs).Normal] {φ : MulAut ↥A} (hφ : φ ∈ (autQuot hs).ker) : φ * φ = 1 := by
  have hz' := aut_fix_z hs φ
  have h2 : (⟨z, hs.mem⟩ : ↥A) * ⟨z, hs.mem⟩ = 1 := Subtype.ext hs.sq
  have hfix : ∀ a : ↥A, φ a = a ∨ φ a = a * ⟨z, hs.mem⟩ := by
    intro a
    have h := congrArg (fun σ : Equiv.Perm (↥A ⧸ zSub hs) => σ (a : ↥A ⧸ zSub hs))
      ((autQuot hs).mem_ker.mp hφ)
    change ((φ a : ↥A) : ↥A ⧸ zSub hs) = (a : ↥A ⧸ zSub hs) at h
    rcases mem_zSub hs (QuotientGroup.eq.mp h.symm) with h' | h'
    · left
      calc φ a = a * (a⁻¹ * φ a) := by group
        _ = a := by rw [h', mul_one]
    · right
      calc φ a = a * (a⁻¹ * φ a) := by group
        _ = a * ⟨z, hs.mem⟩ := by rw [h']
  refine MulEquiv.ext fun a => ?_
  change φ (φ a) = a
  rcases hfix a with h | h
  · rw [h, h]
  · rw [h, map_mul, hz', h, mul_assoc, h2, mul_one]

theorem card_autQuot_ker {A : Subgroup Q} {z : Q} (hs : IsUniqueInvolution A z)
    [(zSub hs).Normal] : ∃ k : ℕ, Nat.card (autQuot hs).ker = 2 ^ k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (MulAut ↥A) :=
    Finite.of_injective (fun φ : MulAut ↥A => (φ : ↥A → ↥A)) fun _ _ h => MulEquiv.ext (congrFun h)
  have hp : IsPGroup 2 (autQuot hs).ker := by
    intro g
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one, Subgroup.coe_pow, pow_two, Subgroup.coe_one]
    exact autQuot_ker_sq hs g.2
  exact IsPGroup.iff_card.mp hp

theorem card_aut_dvd {A : Subgroup Q} {z : Q} (hz : ∀ q : Q, q * z = z * q)
    (hs : IsUniqueInvolution A z) (h8 : Nat.card A = 8) :
    ∃ k : ℕ, Nat.card (MulAut ↥A) ∣ 2 ^ k * 24 := by
  haveI := zSub_normal hz hs
  obtain ⟨k, hk⟩ := card_autQuot_ker hs
  refine ⟨k, ?_⟩
  rw [← Subgroup.card_ker_mul_card_range (autQuot hs), hk]
  refine Nat.mul_dvd_mul_left _ ?_
  have hz2 : orderOf (⟨z, hs.mem⟩ : ↥A) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [pow_two]; exact Subtype.ext hs.sq)
      (fun h => hs.ne_one (congrArg Subtype.val h))
  have hq : Nat.card (↥A ⧸ zSub hs) = 4 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (zSub hs)
    rw [Nat.card_zpowers, hz2, h8] at h
    omega
  have h24 : Nat.card (Equiv.Perm (↥A ⧸ zSub hs)) = 24 := by
    rw [Nat.card_perm, hq]; rfl
  rw [← h24]
  exact Subgroup.card_subgroup_dvd_card _

theorem mem_normalizer_of_conjSub_eq' {A : Subgroup Q} {q : Q} (h : conjSub q A = A) :
    q ∈ Subgroup.normalizer (A : Set Q) := by
  refine Subgroup.mem_normalizer_iff.mpr fun w => ⟨fun hw => ?_, fun hw => ?_⟩
  · rw [← h]; exact conj_mem_conjSub hw
  · have h' : conjSub q⁻¹ A = A := by
      conv_lhs => rw [← h]
      exact conjSub_inv_conjSub q A
    have h1 := conj_mem_conjSub (n := q⁻¹) hw
    rw [h'] at h1
    convert h1 using 1
    group

theorem index_dvd_nine {A B : Subgroup Q} {z : Q} (hz : ∀ q : Q, q * z = z * q)
    (hsA : IsUniqueInvolution A z) (hsB : IsUniqueInvolution B z) (h8A : Nat.card A = 8)
    (h8B : Nat.card B = 8)
    (hperm : ∀ q : Q, (conjSub q A = A ∧ conjSub q B = B) ∨ (conjSub q A = B ∧ conjSub q B = A))
    {s : Q} (hsAB : conjSub s A = B) (hsBA : conjSub s B = A) {H : Subgroup Q}
    (hMH : ∀ m : Q, (∀ x ∈ A, m * x = x * m) → (∀ x ∈ B, m * x = x * m) → m ∈ H)
    (hodd : Odd H.index) : H.index ∣ 9 := by
  set N₀ := Subgroup.normalizer (A : Set Q) ⊓ Subgroup.normalizer (B : Set Q) with hN₀
  have hN2 : N₀.index ∣ 2 := by
    refine Subgroup.index_dvd_two_iff.mpr ⟨s, fun b => ?_⟩
    rcases hperm b with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inr ⟨mem_normalizer_of_conjSub_eq' h1, mem_normalizer_of_conjSub_eq' h2⟩
    · left
      refine ⟨mem_normalizer_of_conjSub_eq' ?_, mem_normalizer_of_conjSub_eq' ?_⟩
      · rw [conjSub_mul, hsAB, h2]
      · rw [conjSub_mul, hsBA, h1]
  let ρ : ↥N₀ →* MulAut ↥A × MulAut ↥B :=
    (A.normalizerMonoidHom.comp (Subgroup.inclusion inf_le_left)).prod
      (B.normalizerMonoidHom.comp (Subgroup.inclusion inf_le_right))
  have hker : ρ.ker ≤ H.subgroupOf N₀ := by
    intro n hn
    rw [MonoidHom.mem_ker, Prod.ext_iff] at hn
    obtain ⟨hnA, hnB⟩ := hn
    refine Subgroup.mem_subgroupOf.mpr (hMH _ (fun x hx => ?_) (fun x hx => ?_))
    · have h1 := congrArg (fun φ : MulAut ↥A => ((φ ⟨x, hx⟩ : ↥A) : Q)) hnA
      simp only [ρ, MonoidHom.prod_apply, MonoidHom.comp_apply, Prod.fst_one,
        Subgroup.normalizerMonoidHom_apply_apply_coe, Subgroup.coe_inclusion,
        MulAut.one_apply] at h1
      exact (comm_of_conj_eq' h1).symm
    · have h1 := congrArg (fun φ : MulAut ↥B => ((φ ⟨x, hx⟩ : ↥B) : Q)) hnB
      simp only [ρ, MonoidHom.prod_apply, MonoidHom.comp_apply, Prod.snd_one,
        Subgroup.normalizerMonoidHom_apply_apply_coe, Subgroup.coe_inclusion,
        MulAut.one_apply] at h1
      exact (comm_of_conj_eq' h1).symm
  obtain ⟨kA, hkA⟩ := card_aut_dvd hz hsA h8A
  obtain ⟨kB, hkB⟩ := card_aut_dvd hz hsB h8B
  have hrel : (H.subgroupOf N₀).index ∣ 2 ^ kA * 24 * (2 ^ kB * 24) := by
    refine (Subgroup.index_dvd_of_le hker).trans ?_
    rw [Subgroup.index_ker]
    refine (Subgroup.card_subgroup_dvd_card _).trans ?_
    rw [Nat.card_prod]
    exact Nat.mul_dvd_mul hkA hkB
  have hH : H.index ∣ (H.subgroupOf N₀).index * N₀.index := by
    have e := Subgroup.relIndex_mul_index (H := H ⊓ N₀) (K := N₀) inf_le_right
    rw [Subgroup.inf_relIndex_right] at e
    change (H.subgroupOf N₀).index * N₀.index = (H ⊓ N₀).index at e
    rw [e]
    exact Subgroup.index_dvd_of_le inf_le_left
  have hall : H.index ∣ 9 * 2 ^ (kA + kB + 7) := by
    refine hH.trans ((Nat.mul_dvd_mul hrel hN2).trans ?_)
    refine ⟨1, ?_⟩
    rw [pow_add, pow_add]
    ring
  exact (Nat.Coprime.pow_right _ (hodd.coprime_two_right)).dvd_of_dvd_mul_right hall

end Index

section Stab

variable {Q : Type} [Group Q]

@[expose] def stabMod (e z x : Q) : Subgroup Q where
  carrier := {q | q * e * q⁻¹ = e ∧ q * z * q⁻¹ = z ∧ x⁻¹ * (q * x * q⁻¹) ∈ Subgroup.zpowers z}
  one_mem' := by
    refine ⟨by group, by group, ?_⟩
    rw [one_mul, inv_one, mul_one, inv_mul_cancel]
    exact Subgroup.one_mem _
  mul_mem' := by
    rintro a b ⟨ha1, ha2, ha3⟩ ⟨hb1, hb2, hb3⟩
    have hca : ∀ w ∈ Subgroup.zpowers z, a * w * a⁻¹ = w := by
      intro w hw
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      rw [← conj_zpow, ha2]
    refine ⟨?_, ?_, ?_⟩
    · calc a * b * e * (a * b)⁻¹ = a * (b * e * b⁻¹) * a⁻¹ := by group
        _ = e := by rw [hb1, ha1]
    · calc a * b * z * (a * b)⁻¹ = a * (b * z * b⁻¹) * a⁻¹ := by group
        _ = z := by rw [hb2, ha2]
    · have e1 : x⁻¹ * (a * b * x * (a * b)⁻¹) =
          (x⁻¹ * (a * x * a⁻¹)) * (a * (x⁻¹ * (b * x * b⁻¹)) * a⁻¹) := by group
      rw [e1, hca _ hb3]
      exact Subgroup.mul_mem _ ha3 hb3
  inv_mem' := by
    rintro a ⟨ha1, ha2, ha3⟩
    have ha2' : a⁻¹ * z * a⁻¹⁻¹ = z := by
      calc a⁻¹ * z * a⁻¹⁻¹ = a⁻¹ * (a * z * a⁻¹) * a⁻¹⁻¹ := by rw [ha2]
        _ = z := by group
    have hca : ∀ w ∈ Subgroup.zpowers z, a⁻¹ * w * a⁻¹⁻¹ = w := by
      intro w hw
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      rw [← conj_zpow, ha2']
    refine ⟨?_, ha2', ?_⟩
    · calc a⁻¹ * e * a⁻¹⁻¹ = a⁻¹ * (a * e * a⁻¹) * a⁻¹⁻¹ := by rw [ha1]
        _ = e := by group
    · have e1 : x⁻¹ * (a⁻¹ * x * a⁻¹⁻¹) = a⁻¹ * (x⁻¹ * (a * x * a⁻¹))⁻¹ * a⁻¹⁻¹ := by group
      rw [e1, hca _ (Subgroup.inv_mem _ ha3)]
      exact Subgroup.inv_mem _ ha3

theorem zpow_cases {z : Q} (hz2 : z * z = 1) (k : ℤ) : z ^ k = 1 ∨ z ^ k = z := by
  have hk : z ^ k = z ^ (k % 2) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv k 2, zpow_add, zpow_mul]
    rw [zpow_two, hz2, one_zpow, mul_one]
  rw [hk]
  rcases Int.emod_two_eq_zero_or_one k with h | h <;> rw [h]
  · left; exact zpow_zero _
  · right; rw [zpow_one]

theorem modZ_of_mem_stabMod {e z x q : Q} (hz2 : z * z = 1) (hq : q ∈ stabMod e z x) :
    q * e * q⁻¹ = e ∧ ModZ z (q * x * q⁻¹) x := by
  obtain ⟨h1, -, h3⟩ := hq
  refine ⟨h1, ?_⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h3
  rcases zpow_cases hz2 k with h | h <;> rw [h] at hk
  · left
    calc q * x * q⁻¹ = x * (x⁻¹ * (q * x * q⁻¹)) := by group
      _ = x := by rw [← hk, mul_one]
  · right
    calc q * x * q⁻¹ = x * (x⁻¹ * (q * x * q⁻¹)) := by group
      _ = x * z := by rw [← hk]

theorem mem_stabMod_of_modZ {e z x q : Q} (hz : q * z = z * q) (h1 : q * e * q⁻¹ = e)
    (h2 : ModZ z (q * x * q⁻¹) x) : q ∈ stabMod e z x := by
  refine ⟨h1, by rw [hz, mul_inv_cancel_right], ?_⟩
  rcases h2 with h | h
  · rw [h, inv_mul_cancel]; exact Subgroup.one_mem _
  · rw [h, ← mul_assoc, inv_mul_cancel, one_mul]; exact Subgroup.mem_zpowers _

theorem conjSub_eq_of_mem_normalizer' {K : Subgroup Q} {q : Q}
    (hq : q ∈ Subgroup.normalizer (K : Set Q)) : conjSub q K = K := by
  ext x
  rw [mem_conjSub_iff, Subgroup.mem_normalizer_iff.mp hq (q⁻¹ * x * q)]
  simp only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one]

theorem cover_of_index_le_three [Finite Q] {H : Subgroup Q} (hle : H.index ≤ 3) :
    ∃ r₁ r₂ : Q, ∀ q : Q, ∃ d : Q, (d = 1 ∨ d = r₁ ∨ d = r₂) ∧
      q • ((1 : Q) : Q ⧸ H) = d • ((1 : Q) : Q ⧸ H) := by
  have hsm : ∀ q : Q, q • ((1 : Q) : Q ⧸ H) = (q : Q ⧸ H) := fun q => by
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
  simp only [hsm]
  by_cases h1 : ∃ r₁ : Q, (r₁ : Q ⧸ H) ≠ ((1 : Q) : Q ⧸ H)
  · obtain ⟨r₁, hr₁⟩ := h1
    by_cases h2 : ∃ r₂ : Q, (r₂ : Q ⧸ H) ≠ ((1 : Q) : Q ⧸ H) ∧ (r₂ : Q ⧸ H) ≠ r₁
    · obtain ⟨r₂, hr₂, hr₂₁⟩ := h2
      refine ⟨r₁, r₂, fun q => ?_⟩
      by_contra hne
      push Not at hne
      have hq1 := hne 1 (Or.inl rfl)
      have hq2 := hne r₁ (Or.inr (Or.inl rfl))
      have hq3 := hne r₂ (Or.inr (Or.inr rfl))
      let f : Fin 4 → Q ⧸ H := ![((1 : Q) : Q ⧸ H), (r₁ : Q ⧸ H), (r₂ : Q ⧸ H), (q : Q ⧸ H)]
      have hf : Function.Injective f := by
        intro i j hij
        fin_cases i <;> fin_cases j <;>
          simp_all [f, eq_comm]
      have h4 := Nat.card_le_card_of_injective f hf
      rw [Nat.card_eq_fintype_card, Fintype.card_fin] at h4
      have : H.index = Nat.card (Q ⧸ H) := rfl
      omega
    · push Not at h2
      refine ⟨r₁, r₁, fun q => ?_⟩
      by_cases hq : (q : Q ⧸ H) = ((1 : Q) : Q ⧸ H)
      · exact ⟨1, Or.inl rfl, hq⟩
      · exact ⟨r₁, Or.inr (Or.inl rfl), h2 q hq⟩
  · push Not at h1
    exact ⟨1, 1, fun q => ⟨1, Or.inl rfl, h1 q⟩⟩

end Stab

end F7K

section E7Odd

variable {n : ℕ}

@[expose] def P23E7Odd (n : ℕ) : Prop :=
  CIT3Below n → TL4.TightBelowRPlus 3 n →
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
    (u e g : Y), P23Cfg n Y R S t K' W u e g → ¬ SecNoExit R e → ECase1 R W e →
      u * e ∈ zStarOf (Subgroup.centralizer ({u} : Set Y)) →
      Odd (Subgroup.normalizer (((W.subgroupOf (Subgroup.centralizer ({t} : Set Y))).map
        (F7I.piC (Subgroup.centralizer ({t} : Set Y))) :
          Subgroup (↥(Subgroup.centralizer ({t} : Set Y)) ⧸
            classicalInvolutionOddCore ↥(Subgroup.centralizer ({t} : Set Y)))) :
        Set (↥(Subgroup.centralizer ({t} : Set Y)) ⧸
          classicalInvolutionOddCore ↥(Subgroup.centralizer ({t} : Set Y))))).index

@[expose] def P23E7Not9 (n : ℕ) : Prop :=
  CIT3Below n → TL4.TightBelowRPlus 3 n →
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
    (u e g : Y), P23Cfg n Y R S t K' W u e g → ¬ SecNoExit R e → ECase1 R W e →
      u * e ∈ zStarOf (Subgroup.centralizer ({u} : Set Y)) →
      ∀ xe xt xu : ↥(Subgroup.centralizer ({t} : Set Y)), (xe : Y) = e → (xt : Y) = t →
        (xu : Y) = u →
        (F7K.stabMod (F7I.piC (Subgroup.centralizer ({t} : Set Y)) xe)
          (F7I.piC (Subgroup.centralizer ({t} : Set Y)) xt)
          (F7I.piC (Subgroup.centralizer ({t} : Set Y)) xu)).index ≠ 9

@[expose] def P23E7NC (n : ℕ) : Prop :=
  CIT3Below n → TL4.TightBelowRPlus 3 n →
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
    (u e g : Y), P23Cfg n Y R S t K' W u e g → ¬ SecNoExit R e → ECase1 R W e →
      u * e ∈ zStarOf (Subgroup.centralizer ({u} : Set Y)) →
      ∀ xe : ↥(Subgroup.centralizer ({t} : Set Y)), (xe : Y) = e →
        ¬ ∀ q : ↥(Subgroup.centralizer ({t} : Set Y)) ⧸
            classicalInvolutionOddCore ↥(Subgroup.centralizer ({t} : Set Y)),
          q * F7I.piC (Subgroup.centralizer ({t} : Set Y)) xe =
            F7I.piC (Subgroup.centralizer ({t} : Set Y)) xe * q

@[expose] def P23E7Cen3 (n : ℕ) : Prop :=
  CIT3Below n → TL4.TightBelowRPlus 3 n →
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
    (u e g : Y), P23Cfg n Y R S t K' W u e g → ¬ SecNoExit R e → ECase1 R W e →
      u * e ∈ zStarOf (Subgroup.centralizer ({u} : Set Y)) →
      ∀ xe xt xu : ↥(Subgroup.centralizer ({t} : Set Y)), (xe : Y) = e → (xt : Y) = t →
        (xu : Y) = u →
      ∀ q₁ q₂ : ↥(Subgroup.centralizer ({t} : Set Y)) ⧸
          classicalInvolutionOddCore ↥(Subgroup.centralizer ({t} : Set Y)),
        q₁ ∉ F7K.stabMod (F7I.piC _ xe) (F7I.piC _ xt) (F7I.piC _ xu) →
        q₂ ∉ F7K.stabMod (F7I.piC _ xe) (F7I.piC _ xt) (F7I.piC _ xu) →
        q₁⁻¹ * q₂ ∉ F7K.stabMod (F7I.piC _ xe) (F7I.piC _ xt) (F7I.piC _ xu) →
        (∀ q, q * (F7I.piC _ xe * (q₁ * F7I.piC _ xe * q₁⁻¹) * (q₂ * F7I.piC _ xe * q₂⁻¹)) =
          (F7I.piC _ xe * (q₁ * F7I.piC _ xe * q₁⁻¹) * (q₂ * F7I.piC _ xe * q₂⁻¹)) * q) →
        (F7I.piC _ xe * (q₁ * F7I.piC _ xe * q₁⁻¹) * (q₂ * F7I.piC _ xe * q₂⁻¹)) *
            (F7I.piC _ xe * (q₁ * F7I.piC _ xe * q₁⁻¹) * (q₂ * F7I.piC _ xe * q₂⁻¹)) = 1 →
        F7I.piC _ xe * (q₁ * F7I.piC _ xe * q₁⁻¹) * (q₂ * F7I.piC _ xe * q₂⁻¹) = 1 ∨
          F7I.piC _ xe * (q₁ * F7I.piC _ xe * q₁⁻¹) * (q₂ * F7I.piC _ xe * q₂⁻¹) = F7I.piC _ xt

theorem p23E7E8_of_nc (hOdd : P23E7Odd n) (hN9 : P23E7Not9 n) (hNC : P23E7NC n)
    (hC3 : P23E7Cen3 n) : P23E7E8 n := by
  intro hcit hP Y _ _ R S t K' W u e g hc hno hE hZ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := Q3CL.Thompson.commutes_of_mem_WSet hΩ hd.hW
  have heW : e ∈ W := (T7K.e_mem_inf hd).1
  have hNe := normalizer_le_centralizer_e hd
  have hW2 : IsPGroup 2 W := Asc77.Thompson.isPGroup_of_mem_WSet hd.hW
  set C := Subgroup.centralizer ({t} : Set Y) with hCdef
  have hWt : W ≤ C := fun w hw =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hWab w hw t hd.hzW)
  have htC : t ∈ C := hWt hd.hzW
  have heC : e ∈ C := hWt heW
  have huC : u ∈ C := hWt hd.huW
  have hueC : u * e ∈ C := C.mul_mem huC heC
  have htc : ∀ c ∈ C, c * t = t * c := fun c hc => Subgroup.mem_centralizer_singleton_iff.mp hc
  obtain ⟨qA, qB, h8A, h8B, nA, nB, hcomm, heA, heB, b₁, b', hub, ha, hb, ha1, haz, hb1, hbz⟩ :=
    p23_twin_q8 hc hCdef htC heC
  have hz : ∀ q : ↥C ⧸ classicalInvolutionOddCore ↥C,
      q * F7I.piC C ⟨t, htC⟩ = F7I.piC C ⟨t, htC⟩ * q := by
    intro q
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective (classicalInvolutionOddCore ↥C) q
    change F7I.piC C c * _ = _ * F7I.piC C c
    rw [← map_mul, ← map_mul]
    exact congrArg _ (Subtype.ext (htc _ c.2))
  have hz2 : F7I.piC C ⟨t, htC⟩ * F7I.piC C ⟨t, htC⟩ = 1 := qA.sq
  have hperm : ∀ q : ↥C ⧸ classicalInvolutionOddCore ↥C,
      (conjSub q (((tightCore R).subgroupOf C).map (F7I.piC C)) =
          ((tightCore R).subgroupOf C).map (F7I.piC C) ∧
        conjSub q ((K'.subgroupOf C).map (F7I.piC C)) = (K'.subgroupOf C).map (F7I.piC C)) ∨
      (conjSub q (((tightCore R).subgroupOf C).map (F7I.piC C)) =
          (K'.subgroupOf C).map (F7I.piC C) ∧
        conjSub q ((K'.subgroupOf C).map (F7I.piC C)) =
          ((tightCore R).subgroupOf C).map (F7I.piC C)) := by
    intro q
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective (classicalInvolutionOddCore ↥C) q
    change (conjSub (F7I.piC C c) _ = _ ∧ conjSub (F7I.piC C c) _ = _) ∨
      (conjSub (F7I.piC C c) _ = _ ∧ conjSub (F7I.piC C c) _ = _)
    rw [F7I.conjSub_map_piC, F7I.conjSub_map_piC]
    rcases p23_conj_twins hc c.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; rw [h1, h2]; exact ⟨rfl, rfl⟩
    · right; rw [h1, h2]; exact ⟨rfl, rfl⟩
  have hxmod : ∀ x n : ↥C, ((n : Y) * x * (n : Y)⁻¹ = x ∨ (n : Y) * x * (n : Y)⁻¹ = x * t) →
      F7E.ModZ (F7I.piC C ⟨t, htC⟩) (F7I.piC C n * F7I.piC C x * (F7I.piC C n)⁻¹)
        (F7I.piC C x) := by
    intro x n h
    rw [← map_inv, ← map_mul, ← map_mul]
    rcases h with h | h
    · left; exact congrArg _ (Subtype.ext h)
    · right; rw [← map_mul]; exact congrArg _ (Subtype.ext h)
  have hNu : ∀ n ∈ C, n ∈ Subgroup.normalizer (W : Set Y) →
      n * u * n⁻¹ = u ∨ n * u * n⁻¹ = u * t := fun n hn hnN => conj_u_cases hc hnN hn
  have hNue : ∀ n ∈ C, n ∈ Subgroup.normalizer (W : Set Y) →
      n * (u * e) * n⁻¹ = u * e ∨ n * (u * e) * n⁻¹ = u * e * t := by
    intro n hn hnN
    have hne : n * e * n⁻¹ = e := by
      rw [Subgroup.mem_centralizer_singleton_iff.mp (hNe hnN)]; group
    have e1 : n * (u * e) * n⁻¹ = (n * u * n⁻¹) * (n * e * n⁻¹) := by group
    rw [e1, hne]
    rcases hNu n hn hnN with h | h
    · left; rw [h]
    · right; rw [h, mul_assoc, ← htc e heC, ← mul_assoc]
  have hu' : (⟨u, huC⟩ : ↥C) = b₁ * b' := Subtype.ext hub.symm
  have hg' : (⟨u * e, hueC⟩ : ↥C) = b₁ * b' * ⟨e, heC⟩ :=
    Subtype.ext (by show u * e = (b₁ : Y) * b' * e; rw [hub])
  have hgb : F7I.piC C ⟨u * e, hueC⟩ =
      F7I.piC C b₁ * F7I.piC C b' * F7I.piC C ⟨e, heC⟩ := by
    rw [hg', map_mul, map_mul]
  obtain ⟨s, hsC, hsN, hsK⟩ := p23_exists_swap hc
  have hsAB : conjSub (F7I.piC C ⟨s, hsC⟩) (((tightCore R).subgroupOf C).map (F7I.piC C)) =
      (K'.subgroupOf C).map (F7I.piC C) := by
    rw [F7I.conjSub_map_piC]
    change ((conjSub s (tightCore R)).subgroupOf C).map _ = _
    rw [hsK]
  have hsBA : conjSub (F7I.piC C ⟨s, hsC⟩) ((K'.subgroupOf C).map (F7I.piC C)) =
      ((tightCore R).subgroupOf C).map (F7I.piC C) := by
    rw [F7I.conjSub_map_piC]
    change ((conjSub s K').subgroupOf C).map _ = _
    rw [p23_swap_conj hc hsC hsK]
  have hsp : F7E.ModZ (F7I.piC C ⟨t, htC⟩)
      (F7I.piC C ⟨s, hsC⟩ * (F7I.piC C b₁ * F7I.piC C b') * (F7I.piC C ⟨s, hsC⟩)⁻¹)
      (F7I.piC C b₁ * F7I.piC C b') := by
    rw [← map_mul, ← hu']
    exact hxmod _ _ (conj_u_cases hc hsN hsC)
  have hMB' := p23E7MBar_proved hcit hP Y R S t K' W u e g hc hno hE hZ ⟨e, heC⟩ rfl
  have he2 : F7I.piC C ⟨e, heC⟩ * F7I.piC C ⟨e, heC⟩ = 1 := by
    rw [← map_mul, ← map_one (F7I.piC C)]
    exact congrArg _ (Subtype.ext hd.he2)
  have hz' : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have heb1 : F7I.piC C ⟨e, heC⟩ ≠ 1 := by
    intro h
    rw [← map_one (F7I.piC C)] at h
    exact hd.he1 (congrArg Subtype.val (F7I.piC_inj hW2 heW W.one_mem h))
  have hebz : F7I.piC C ⟨e, heC⟩ ≠ F7I.piC C ⟨t, htC⟩ := by
    intro h
    have h' : e = t := congrArg Subtype.val (F7I.piC_inj hW2 heW hd.hzW h)
    exact e_not_mem_sup hc (by rw [h']; exact Subgroup.mem_sup_left hz'.mem)
  have hone : ∀ x : ↥C ⧸ classicalInvolutionOddCore ↥C, (1 : ↥C ⧸ _) * x * 1⁻¹ = x := by
    intro x; group
  have hmodu := F7I.modZ_of_conjSub_eq hWt hW2 htC htc (x := ⟨u, huC⟩) hNu
  have hNe' : ∀ n ∈ C, n ∈ Subgroup.normalizer (W : Set Y) → n * e * n⁻¹ = e := by
    intro n _ hnN
    rw [Subgroup.mem_centralizer_singleton_iff.mp (hNe hnN)]; group
  have hmode := F7J.conj_eq_of_conjSub_eq hWt hW2 (x := ⟨e, heC⟩) hNe'
  set H := F7K.stabMod (F7I.piC C ⟨e, heC⟩) (F7I.piC C ⟨t, htC⟩) (F7I.piC C ⟨u, huC⟩) with hHdef
  have hNH : Subgroup.normalizer (((W.subgroupOf C).map (F7I.piC C) :
      Subgroup (↥C ⧸ classicalInvolutionOddCore ↥C)) : Set (↥C ⧸ classicalInvolutionOddCore ↥C)) ≤
      H := by
    intro q hq
    have hq' := F7K.conjSub_eq_of_mem_normalizer' hq
    have h1 := hmode q 1 (by rw [conjSub_one]; exact hq')
    have h2 := hmodu q 1 (by rw [conjSub_one]; exact hq')
    rw [hone] at h1 h2
    exact F7K.mem_stabMod_of_modZ (hz q) h1 h2
  have hpb : F7I.piC C ⟨u, huC⟩ = F7I.piC C b₁ * F7I.piC C b' := by rw [hu', map_mul]
  have hMH : ∀ m : ↥C ⧸ classicalInvolutionOddCore ↥C,
      (∀ x ∈ ((tightCore R).subgroupOf C).map (F7I.piC C), m * x = x * m) →
      (∀ x ∈ (K'.subgroupOf C).map (F7I.piC C), m * x = x * m) → m ∈ H := by
    intro m hmA hmB
    refine F7K.mem_stabMod_of_modZ (hz m) (by rw [hMB' m hmA hmB, mul_inv_cancel_right]) (Or.inl ?_)
    rw [hpb]
    calc m * (F7I.piC C b₁ * F7I.piC C b') * m⁻¹ = (m * F7I.piC C b₁) * F7I.piC C b' * m⁻¹ := by
          group
      _ = (F7I.piC C b₁ * m) * F7I.piC C b' * m⁻¹ := by rw [hmA _ ha]
      _ = F7I.piC C b₁ * (m * F7I.piC C b') * m⁻¹ := by group
      _ = F7I.piC C b₁ * (F7I.piC C b' * m) * m⁻¹ := by rw [hmB _ hb]
      _ = F7I.piC C b₁ * F7I.piC C b' := by group
  have hodd : Odd H.index :=
    (hOdd hcit hP Y R S t K' W u e g hc hno hE hZ).of_dvd_nat (Subgroup.index_dvd_of_le hNH)
  have h9 := F7K.index_dvd_nine hz qA qB h8A h8B hperm hsAB hsBA hMH hodd
  have hn9 := hN9 hcit hP Y R S t K' W u e g hc hno hE hZ ⟨e, heC⟩ ⟨t, htC⟩ ⟨u, huC⟩ rfl rfl rfl
  have hle : H.index ≤ 3 := by
    obtain ⟨i, hi, hie⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (show H.index ∣ 3 ^ 2 from h9)
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl
    · rw [hie]; norm_num
    · rw [hie]; norm_num
    · exact absurd (by rw [hie]; norm_num) hn9
  set w₀ : (↥C ⧸ classicalInvolutionOddCore ↥C) ⧸ H := ((1 : ↥C ⧸ classicalInvolutionOddCore ↥C) :
    (↥C ⧸ classicalInvolutionOddCore ↥C) ⧸ H) with hw₀
  have hlab : ∀ q d : ↥C ⧸ classicalInvolutionOddCore ↥C, q • w₀ = d • w₀ → d⁻¹ * q ∈ H := by
    intro q d h
    rw [hw₀, MulAction.Quotient.smul_mk, MulAction.Quotient.smul_mk, smul_eq_mul, smul_eq_mul,
      mul_one, mul_one] at h
    exact QuotientGroup.eq.mp h.symm
  have hconj : ∀ q d x : ↥C ⧸ classicalInvolutionOddCore ↥C,
      (d⁻¹ * q) * x * (d⁻¹ * q)⁻¹ = x → q * x * q⁻¹ = d * x * d⁻¹ := by
    intro q d x h
    calc q * x * q⁻¹ = d * ((d⁻¹ * q) * x * (d⁻¹ * q)⁻¹) * d⁻¹ := by group
      _ = d * x * d⁻¹ := by rw [h]
  have hmode' : ∀ q d : ↥C ⧸ classicalInvolutionOddCore ↥C, q • w₀ = d • w₀ →
      q * F7I.piC C ⟨e, heC⟩ * q⁻¹ = d * F7I.piC C ⟨e, heC⟩ * d⁻¹ := fun q d h =>
    hconj q d _ (F7K.modZ_of_mem_stabMod hz2 (hlab q d h)).1
  have hmodu' : ∀ q d : ↥C ⧸ classicalInvolutionOddCore ↥C, q • w₀ = d • w₀ →
      F7E.ModZ (F7I.piC C ⟨t, htC⟩) (q * (F7I.piC C b₁ * F7I.piC C b') * q⁻¹)
        (d * (F7I.piC C b₁ * F7I.piC C b') * d⁻¹) := by
    intro q d h
    have h2 := F7E.ModZ.conj hz (F7K.modZ_of_mem_stabMod hz2 (hlab q d h)).2 d
    rw [← hpb]
    have e1 : d * ((d⁻¹ * q) * F7I.piC C ⟨u, huC⟩ * (d⁻¹ * q)⁻¹) * d⁻¹ =
        q * F7I.piC C ⟨u, huC⟩ * q⁻¹ := by group
    rwa [e1] at h2
  set gb := F7I.piC C b₁ * F7I.piC C b' * F7I.piC C ⟨e, heC⟩ with hgbdef
  have hmodg : ∀ q d : ↥C ⧸ classicalInvolutionOddCore ↥C, q • w₀ = d • w₀ →
      F7E.ModZ (F7I.piC C ⟨t, htC⟩) (q * gb * q⁻¹) (d * gb * d⁻¹) := by
    intro q d h
    have h1 := F7J.modZ_mul hz hz2 (hmodu' q d h)
      (Or.inl (hmode' q d h) : F7E.ModZ (F7I.piC C ⟨t, htC⟩) (q * F7I.piC C ⟨e, heC⟩ * q⁻¹)
        (d * F7I.piC C ⟨e, heC⟩ * d⁻¹))
    have e1 : ∀ r : ↥C ⧸ classicalInvolutionOddCore ↥C, r * gb * r⁻¹ =
        r * (F7I.piC C b₁ * F7I.piC C b') * r⁻¹ * (r * F7I.piC C ⟨e, heC⟩ * r⁻¹) := fun r => by
      rw [hgbdef]; group
    rw [e1 q, e1 d]
    exact h1
  obtain ⟨q₁, q₂, hq⟩ := F7K.cover_of_index_le_three hle
  have horb : ∀ q : ↥C ⧸ classicalInvolutionOddCore ↥C, ∃ d, (d = 1 ∨ d = q₁ ∨ d = q₂) ∧
      F7E.ModZ (F7I.piC C ⟨t, htC⟩) (q * (F7I.piC C b₁ * F7I.piC C b') * q⁻¹)
        (d * (F7I.piC C b₁ * F7I.piC C b') * d⁻¹) := by
    intro q
    obtain ⟨d, hd', heq⟩ := hq q
    exact ⟨d, hd', hmodu' q d heq⟩
  have hmod1 : ∀ q : ↥C ⧸ classicalInvolutionOddCore ↥C, q • w₀ = w₀ →
      F7E.ModZ (F7I.piC C ⟨t, htC⟩) (q * gb * q⁻¹) gb := by
    intro q h
    have := hmodg q 1 (by rw [one_smul]; exact h)
    rwa [hone] at this
  have hcov3 : ∀ γ, F7E.ModZ (F7I.piC C ⟨t, htC⟩) (γ * gb * γ⁻¹) gb ∨
      F7E.ModZ (F7I.piC C ⟨t, htC⟩) (γ * gb * γ⁻¹) (q₁ * gb * q₁⁻¹) ∨
      F7E.ModZ (F7I.piC C ⟨t, htC⟩) (γ * gb * γ⁻¹) (q₂ * gb * q₂⁻¹) := by
    intro γ
    obtain ⟨d, hd', heq⟩ := hq γ
    have h := hmodg γ d heq
    rcases hd' with rfl | rfl | rfl
    · left; rwa [hone] at h
    · right; left; exact h
    · right; right; exact h
  have hdich : ∃ r g₂, (∀ γ, F7E.ModZ (F7I.piC C ⟨t, htC⟩) (γ * gb * γ⁻¹) gb ∨
      F7E.ModZ (F7I.piC C ⟨t, htC⟩) (γ * gb * γ⁻¹) (r * gb * r⁻¹) ∨
      F7E.ModZ (F7I.piC C ⟨t, htC⟩) (γ * gb * γ⁻¹) g₂) ∧
      (F7E.ModZ (F7I.piC C ⟨t, htC⟩) (gb * (r * gb * r⁻¹) * g₂) 1 ∨
        g₂ = gb * (r * gb * r⁻¹)) := by
    have htr : ∀ {x y w : ↥C ⧸ classicalInvolutionOddCore ↥C},
        F7E.ModZ (F7I.piC C ⟨t, htC⟩) x y → F7E.ModZ (F7I.piC C ⟨t, htC⟩) y w →
          F7E.ModZ (F7I.piC C ⟨t, htC⟩) x w := fun h₁ h₂ => F7E.ModZ.trans hz2 h₁ h₂
    by_cases h01 : q₁ • w₀ = w₀
    · refine ⟨q₂, gb * (q₂ * gb * q₂⁻¹), fun γ => ?_, Or.inr rfl⟩
      rcases hcov3 γ with h | h | h
      · exact Or.inl h
      · exact Or.inl (htr h (hmod1 q₁ h01))
      · exact Or.inr (Or.inl h)
    by_cases h02 : q₂ • w₀ = w₀
    · refine ⟨q₁, gb * (q₁ * gb * q₁⁻¹), fun γ => ?_, Or.inr rfl⟩
      rcases hcov3 γ with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inl (htr h (hmod1 q₂ h02))
    by_cases h12 : q₁ • w₀ = q₂ • w₀
    · refine ⟨q₁, gb * (q₁ * gb * q₁⁻¹), fun γ => ?_, Or.inr rfl⟩
      rcases hcov3 γ with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inl (htr h (hmodg q₂ q₁ h12.symm)))
    refine ⟨q₁, q₂ * gb * q₂⁻¹, hcov3, Or.inl ?_⟩
    have hlab' : ∀ q d : ↥C ⧸ classicalInvolutionOddCore ↥C, d⁻¹ * q ∈ H → q • w₀ = d • w₀ := by
      intro q d h
      rw [hw₀, MulAction.Quotient.smul_mk, MulAction.Quotient.smul_mk, smul_eq_mul, smul_eq_mul,
        mul_one, mul_one]
      exact (QuotientGroup.eq.mpr h).symm
    have hC3' := hC3 hcit hP Y R S t K' W u e g hc hno hE hZ ⟨e, heC⟩ ⟨t, htC⟩ ⟨u, huC⟩ rfl rfl rfl
      q₁ q₂ (fun h => h01 (by simpa using hlab' q₁ 1 (by rwa [inv_one, one_mul])))
      (fun h => h02 (by simpa using hlab' q₂ 1 (by rwa [inv_one, one_mul])))
      (fun h => h12 (hlab' q₂ q₁ h).symm)
    have hnc' : ¬ ∀ d : ↥C ⧸ classicalInvolutionOddCore ↥C,
        d * F7I.piC C ⟨e, heC⟩ * d⁻¹ = F7I.piC C ⟨e, heC⟩ := by
      intro h
      refine hNC hcit hP Y R S t K' W u e g hc hno hE hZ ⟨e, heC⟩ rfl fun q => ?_
      calc q * F7I.piC C ⟨e, heC⟩ = (q * F7I.piC C ⟨e, heC⟩ * q⁻¹) * q := by group
        _ = F7I.piC C ⟨e, heC⟩ * q := by rw [h q]
    rcases F7K.prod_coreA hz qA qB h8A h8B nA nB hcomm hperm ha hb ha1 haz hb1 hbz hsAB hsBA hsp
      heA heB hMB' he2 heb1 hebz hmodu' hmode' ⟨q₁, q₂, hq⟩ h01 h02 h12 hC3' hnc' with h | h
    · left; exact h
    · right; rw [one_mul]; exact h
  obtain ⟨r, g₂, hcov, hprod⟩ := hdich
  obtain ⟨hexp, hcard⟩ := F7I.elem_card hz qA qB h8A h8B nA nB hcomm hperm ha hb ha1 haz hb1 hbz
    hsAB hsBA hsp horb he2 heA heB hMB' hcov hprod
  have hA : p23ABar t u e = Subgroup.closure {q | ∃ γ : ↥C ⧸ classicalInvolutionOddCore ↥C,
      q = γ * gb * γ⁻¹} := by
    unfold p23ABar
    congr 1
    ext q
    constructor
    · rintro ⟨x, ⟨c, hcC, hx⟩, rfl⟩
      refine ⟨F7I.piC C ⟨c, hcC⟩, ?_⟩
      have e1 : x = ⟨c, hcC⟩ * ⟨u * e, hueC⟩ * ⟨c, hcC⟩⁻¹ := Subtype.ext hx
      change F7I.piC C x = _
      rw [e1, map_mul, map_mul, map_inv, hgb]
    · rintro ⟨γ, rfl⟩
      obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective (classicalInvolutionOddCore ↥C) γ
      refine ⟨c * ⟨u * e, hueC⟩ * c⁻¹, ⟨c, c.2, rfl⟩, ?_⟩
      change _ = F7I.piC C (c * ⟨u * e, hueC⟩ * c⁻¹)
      rw [map_mul, map_mul, map_inv, hgb]
  rw [hA]
  exact ⟨hexp, hcard⟩

theorem p23_exists_sylow_normW {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R}
    {t : Y} {K' W : Subgroup Y} {u e g : Y} (hc : P23Cfg n Y R S t K' W u e g) :
    ∃ S₂ : Subgroup Y, IsSylow2In S₂ (Subgroup.centralizer ({t} : Set Y)) ∧
      S₂ ≤ Subgroup.normalizer (W : Set Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hPG : Q3CL.PartIHypG (Om R) := hC.partIHypG
  have hd := hc.data
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hz' : IsUniqueInvolution K' t := isUniqueInvolution_of_mem_twinSet hz hc.std.hK'
  have htr : ∀ K₁ ∈ Om R, ∀ J ∈ Om R, ∃ a : Y, conjSub a K₁ = J := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    exact ⟨b * a⁻¹, by rw [conjSub_mul, conjSub_inv_conjSub]⟩
  have hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := Q3CL.Thompson.commutes_of_mem_WSet hΩ hd.hW
  obtain ⟨S₀, hWS₀, hwc, -⟩ := exists_weaklyClosed_conj_of_muIsoS4 hPG htr hd.hW hd.hS4
  have hW2 : IsPGroup 2 W := Asc77.Thompson.isPGroup_of_mem_WSet hd.hW
  have hWt : W ≤ Subgroup.centralizer ({t} : Set Y) := fun w hw =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hWab w hw t hd.hzW)
  obtain ⟨S₂, hS₂, hWS₂⟩ := IsSylow2In.exists_ge hW2 hWt
  obtain ⟨S₁, hSS₁⟩ := hS₂.2.1.exists_le_sylow
  obtain ⟨a, ha⟩ := exists_conjSub_eq_of_sylow S₀ S₁
  have e2 : conjSub a⁻¹ W = W := hwc a⁻¹ (by
    rw [conjSub_le_iff, inv_inv, ha]
    exact hWS₂.trans hSS₁)
  have e3 : conjSub a W = W := by
    conv_lhs => rw [← e2]
    exact conjSub_conjSub_inv a W
  have hS₂N : S₂ ≤ Subgroup.normalizer (W : Set Y) := by
    intro s hs
    have hs₀ : a⁻¹ * s * a ∈ (S₀ : Subgroup Y) := by
      have := hSS₁ hs
      rw [← ha] at this
      exact mem_conjSub_iff.mp this
    have e4 : conjSub (a⁻¹ * s * a) W = W :=
      hwc _ ((conjSub_mono hWS₀).trans (conjSub_eq_self_of_mem hs₀).le)
    have e5 : conjSub s W = W := by
      have : s = a * (a⁻¹ * s * a) * a⁻¹ := by group
      conv_lhs => rw [this]
      rw [conjSub_mul, conjSub_mul, e2, e4, e3]
    exact mem_normalizer_iff_conjSub_eq.mpr e5
  exact ⟨S₂, hS₂, hS₂N⟩

theorem p23E7Odd_proved : P23E7Odd n := by
  intro _ _ Y _ _ R S t K' W u e g hc _ _ _
  obtain ⟨S₂, hS₂, hS₂N⟩ := p23_exists_sylow_normW hc
  set C := Subgroup.centralizer ({t} : Set Y) with hCdef
  set N := Subgroup.normalizer ((((W.subgroupOf C).map (F7I.piC C)) :
    Subgroup (↥C ⧸ classicalInvolutionOddCore ↥C)) : Set (↥C ⧸ classicalInvolutionOddCore ↥C))
    with hN
  have hsurj : Function.Surjective (F7I.piC C) := QuotientGroup.mk'_surjective _
  have hle : S₂.subgroupOf C ≤ N.comap (F7I.piC C) := by
    intro c hcS
    rw [Subgroup.mem_comap]
    have hcN : (c : Y) ∈ Subgroup.normalizer (W : Set Y) := hS₂N (Subgroup.mem_subgroupOf.mp hcS)
    apply mem_normalizer_iff_conjSub_eq.mpr
    rw [F7I.conjSub_map_piC, mem_normalizer_iff_conjSub_eq.mp hcN]
  have hidx : N.index ∣ S₂.relIndex C := by
    rw [← Subgroup.index_comap_of_surjective N hsurj]
    exact Subgroup.index_dvd_of_le hle
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnd : ¬ 2 ∣ S₂.relIndex C := by
    obtain ⟨P, hP⟩ := (hS₂.2.1.comap_subtype : IsPGroup 2 (S₂.subgroupOf C)).exists_le_sylow
    have hPm : (P : Subgroup ↥C).map C.subtype = S₂ := by
      refine hS₂.2.2 _ (Subgroup.map_subtype_le _) (P.isPGroup'.map _) fun x hx => ?_
      exact ⟨⟨x, hS₂.1 hx⟩, hP (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
    have hPe : (P : Subgroup ↥C) = S₂.subgroupOf C := by
      ext x
      rw [Subgroup.mem_subgroupOf, ← hPm]
      constructor
      · intro hx; exact ⟨x, hx, rfl⟩
      · rintro ⟨y, hy, hyx⟩
        rwa [Subtype.ext hyx] at hy
    have := P.not_dvd_index
    rwa [hPe] at this
  exact Nat.not_even_iff_odd.mp fun h => hnd ((even_iff_two_dvd.mp h).trans hidx)

end E7Odd

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
