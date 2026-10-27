module

public import CFSG.LocalAnalysis.ComponentClassification.Sol78F514Basic
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12b.Dihedral

public noncomputable section

namespace CFSG.ComponentClassification.Sol78.F514

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.GH74.GLS.Stage1.Thm6.Sec12b

theorem conj_inv_zpow {G : Type} [Group G] (g x : G) (i : ℤ) :
    (g⁻¹ * x * g) ^ i = g⁻¹ * x ^ i * g := by
  have := conj_zpow (a := g⁻¹) (b := x) (i := i)
  simpa using this

theorem conj_conj_eq_of_mul_self {G : Type} [Group G] {y : G} (hy2 : y * y = 1) (x : G) :
    y * (y * x * y⁻¹) * y⁻¹ = x := by
  calc y * (y * x * y⁻¹) * y⁻¹ = (y * y) * x * (y * y)⁻¹ := by group
    _ = x := by rw [hy2]; group

theorem commute_of_conj_eq {G : Type} [Group G] {x y : G} (hx : y * x * y⁻¹ = x) :
    x * y = y * x := by
  calc x * y = (y * x * y⁻¹) * y := by rw [hx]
    _ = y * x := by group

section Dih

variable {G : Type} [Group G] {D : Subgroup G} {ρ b : G} {j : ℕ}

theorem refl_ne_zpow (h : DihData D ρ b j) (i k : ℤ) : b * ρ ^ i ≠ ρ ^ k := by
  intro e
  have hb : b = ρ ^ (k - i) := by rw [zpow_sub, ← e]; group
  apply h.ρ_sq_ne_one
  have h1 := h.s_conj
  rw [hb] at h1
  have h2 : ρ = ρ⁻¹ := by
    rw [← h1]; group
  calc ρ * ρ = ρ * ρ⁻¹ := by rw [← h2]
    _ = 1 := mul_inv_cancel ρ

theorem not_mem_zpowers (h : DihData D ρ b j) : b ∉ zpowers ρ := by
  intro hb
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hb
  exact refl_ne_zpow h 0 k (by rw [zpow_zero, mul_one, hk])

theorem card_eq_two_mul [Finite G] (h : DihData D ρ b j) : Nat.card D = 2 * orderOf ρ := by
  have hzρ : zpowers ρ ≤ D := zpowers_le_of_mem h.ρ_mem
  let φ : zpowers ρ ⊕ zpowers ρ → D := fun x => match x with
    | Sum.inl r => ⟨r, hzρ r.2⟩
    | Sum.inr r => ⟨b * r, D.mul_mem h.s_mem (hzρ r.2)⟩
  have hφi : Function.Injective φ := by
    intro x y hxy
    have h' := congrArg Subtype.val hxy
    rcases x with r | r <;> rcases y with r' | r'
    · exact congrArg Sum.inl (Subtype.ext h')
    · exfalso
      have h'' : (r : G) = b * r' := h'
      apply not_mem_zpowers h
      rw [show b = (r : G) * (r' : G)⁻¹ by rw [h'']; group]
      exact mul_mem r.2 (inv_mem r'.2)
    · exfalso
      have h'' : b * (r : G) = r' := h'
      apply not_mem_zpowers h
      rw [show b = (r' : G) * (r : G)⁻¹ by rw [← h'']; group]
      exact mul_mem r'.2 (inv_mem r.2)
    · have h'' : b * (r : G) = b * r' := h'
      exact congrArg Sum.inr (Subtype.ext (mul_left_cancel h''))
  have hφs : Function.Surjective φ := by
    rintro ⟨x, hx⟩
    obtain ⟨i, hi | hi⟩ := h.elem x hx
    · exact ⟨Sum.inl ⟨ρ ^ i, zpow_mem_zpowers ρ i⟩, Subtype.ext hi.symm⟩
    · exact ⟨Sum.inr ⟨ρ ^ i, zpow_mem_zpowers ρ i⟩, Subtype.ext hi.symm⟩
  rw [← Nat.card_congr (Equiv.ofBijective φ ⟨hφi, hφs⟩), Nat.card_sum, Nat.card_zpowers,
    two_mul]

theorem zpow_mul_refl (h : DihData D ρ b j) (k i : ℤ) :
    ρ ^ k * (b * ρ ^ i) * (ρ ^ k)⁻¹ = b * ρ ^ (i - 2 * k) := by
  calc ρ ^ k * (b * ρ ^ i) * (ρ ^ k)⁻¹ = (ρ ^ k * b) * ρ ^ i * ρ ^ (-k) := by
        rw [zpow_neg]; group
    _ = (b * ρ ^ (-k)) * ρ ^ i * ρ ^ (-k) := by rw [h.zpow_s]
    _ = b * ρ ^ (i - 2 * k) := by
        rw [mul_assoc b, mul_assoc b, ← zpow_add, ← zpow_add]; congr 2; ring

theorem refl_of_mem (h : DihData D ρ b j) {x : G} (hx : x ∈ D) (hx2 : x * x = 1) (hx1 : x ≠ 1)
    (hxc : x ≠ ρ ^ DihData.zc j) : ∃ i : ℤ, x = b * ρ ^ i := by
  rcases h.inv_cases x hx hx2 with e | e | e
  · exact absurd e hx1
  · exact absurd e hxc
  · exact e

variable (h : DihData D ρ b j) {y : G} (hy2 : y * y = 1) (hyD : ∀ d, d ∈ D ↔ y * d * y⁻¹ ∈ D)
  (hfix : ∀ d ∈ D, d * y = y * d → d = 1 ∨ d = ρ ^ DihData.zc j)
include h hy2 hyD hfix

theorem conj_ρ_eq_inv : y * ρ * y⁻¹ = ρ⁻¹ := by
  obtain ⟨u, c, -, hρu, hbc⟩ := h.act hyD
  have hcz : ∀ k : ℤ, y * ρ ^ k * y⁻¹ = ρ ^ (u * k) := fun k => by
    rw [← conj_zpow, hρu, ← zpow_mul]
  have huu : ρ ^ (u * u) = ρ := by
    have h1 := conj_conj_eq_of_mul_self hy2 ρ
    rw [hρu, hcz] at h1
    exact h1
  have hq : ρ ^ (1 + u) * y = y * ρ ^ (1 + u) := by
    apply commute_of_conj_eq
    rw [hcz, show u * (1 + u) = u + u * u by ring, zpow_add, huu, ← zpow_add_one, add_comm]
  rcases hfix _ (zpow_mem h.ρ_mem _) hq with h1 | h1
  · rw [hρu]
    calc ρ ^ u = ρ ^ (1 + u) * ρ⁻¹ := by rw [zpow_add, zpow_one]; group
      _ = ρ⁻¹ := by rw [h1, one_mul]
  · exfalso
    rcases Nat.eq_zero_or_pos j with hj | hj
    ·
      subst hj
      have h2 : ρ ^ u = ρ := by
        have h3 : ρ ^ (1 + u) = ρ ^ (2 : ℤ) := by rw [h1]; rfl
        calc ρ ^ u = ρ ^ (1 + u) * ρ⁻¹ := by rw [zpow_add, zpow_one]; group
          _ = ρ ^ (2 : ℤ) * ρ⁻¹ := by rw [h3]
          _ = ρ := by rw [zpow_two]; group
      have h3 : ρ * y = y * ρ := commute_of_conj_eq (by rw [hρu, h2])
      rcases hfix ρ h.ρ_mem h3 with h4 | h4
      · exact h.ρ_sq_ne_one (by rw [h4, one_mul])
      · have h5 : ρ ^ (1 : ℤ) = ρ ^ DihData.zc 0 := by rw [zpow_one]; exact h4
        rw [h.zpow_eq_iff] at h5
        obtain ⟨k, hk⟩ := h5
        unfold DihData.zc at hk
        push_cast at hk
        omega
    ·
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      have hcs := cs_lemma' hy2 hbc
      rw [hρu, ← zpow_mul, ← zpow_add, h.zpow_eq_one_iff] at hcs
      have h1' := (h.zpow_eq_iff _ _).mp h1
      obtain ⟨k₀, hk₀⟩ := h1'
      obtain ⟨k₁, hk₁⟩ := hcs
      unfold DihData.zc at hk₀
      push_cast at hk₀ hk₁
      have hceven : ∃ l : ℤ, c = 2 * l := by
        have hu : u = 2 * 2 ^ (j' + 1) - 1 + 4 * 2 ^ (j' + 1) * k₀ := by linarith
        rw [hu] at hk₁
        have h2 : c * (2 * 2 ^ (j' + 1)) = 4 * 2 ^ (j' + 1) * (k₁ - c * k₀) := by linarith
        have h3 : (2 : ℤ) ^ (j' + 1) ≠ 0 := by positivity
        have h4 : c = 2 * (k₁ - c * k₀) := by
          have : (2 * 2 ^ (j' + 1)) * c = (2 * 2 ^ (j' + 1)) * (2 * (k₁ - c * k₀)) := by
            linarith
          exact mul_left_cancel₀ (by positivity) this
        exact ⟨k₁ - c * k₀, h4⟩
      obtain ⟨l, rfl⟩ := hceven
      set i : ℤ := l * (2 ^ (j' + 1) + 1) with hi
      have hw : y * (b * ρ ^ i) * y⁻¹ = b * ρ ^ i := by
        have h2 : y * (b * ρ ^ i) * y⁻¹ = b * ρ ^ (2 * l + u * i) := by
          calc y * (b * ρ ^ i) * y⁻¹ = (y * b * y⁻¹) * (y * ρ ^ i * y⁻¹) := by group
            _ = b * ρ ^ (2 * l) * ρ ^ (u * i) := by rw [hbc, hcz]
            _ = b * ρ ^ (2 * l + u * i) := by rw [mul_assoc, ← zpow_add]
        rw [h2]
        congr 1
        rw [h.zpow_eq_iff]
        have hu : u = 2 * 2 ^ (j' + 1) - 1 + 4 * 2 ^ (j' + 1) * k₀ := by linarith
        refine ⟨2 ^ j' * l + k₀ * i, ?_⟩
        push_cast
        rw [hu, hi, pow_succ]
        ring
      have hc := hfix _ (mul_mem h.s_mem (zpow_mem h.ρ_mem i))
        (commute_of_conj_eq hw)
      rcases hc with hc | hc
      · exact refl_ne_zpow h i 0 (by rw [hc, zpow_zero])
      · exact refl_ne_zpow h i _ hc

theorem false_of_four {x : G} (hx : ∃ i : ℤ, x = b * ρ ^ i)
    (hρx : ρ * x * ρ⁻¹ = x ∨ ρ * x * ρ⁻¹ = x * ρ ^ DihData.zc j)
    (hyx : y * x * y⁻¹ = x ∨ y * x * y⁻¹ = x * ρ ^ DihData.zc j) : False := by
  obtain ⟨i, rfl⟩ := hx
  have hρx' : ρ * (b * ρ ^ i) * ρ⁻¹ = b * ρ ^ (i - 2) := by
    have := zpow_mul_refl h 1 i
    rw [zpow_one] at this
    rw [this, mul_one]
  rw [hρx'] at hρx
  have hj : j = 0 := by
    rcases hρx with e | e
    · have e' : ρ ^ (i - 2) = ρ ^ i := mul_left_cancel e
      rw [h.zpow_eq_iff] at e'
      obtain ⟨k, hk⟩ := e'
      push_cast at hk
      have h2 : (0 : ℤ) < 2 ^ j := by positivity
      have h3 : (4 * 2 ^ j : ℤ) * k = -2 := by linarith
      rcases lt_trichotomy k 0 with hk0 | hk0 | hk0
      · nlinarith
      · rw [hk0] at h3; simp at h3
      · nlinarith
    · have e' : ρ ^ (i - 2) = ρ ^ (i + DihData.zc j) := by
        rw [zpow_add]; exact mul_left_cancel (e.trans (by rw [mul_assoc]))
      rw [h.zpow_eq_iff] at e'
      obtain ⟨k, hk⟩ := e'
      unfold DihData.zc at hk
      push_cast at hk
      by_contra hj
      have h2 : (2 : ℤ) ≤ 2 ^ j := by
        calc (2 : ℤ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) (by omega)
      have h3 : (4 * 2 ^ j : ℤ) * k = -2 - 2 * 2 ^ j := by linarith
      rcases lt_trichotomy k 0 with hk0 | hk0 | hk0
      · have : k ≤ -1 := by omega
        nlinarith
      · rw [hk0] at h3; nlinarith
      · nlinarith
  subst hj
  have hzc : ρ ^ DihData.zc 0 = ρ ^ (2 : ℤ) := rfl
  rcases hyx with e | e
  · rcases hfix _ (mul_mem h.s_mem (zpow_mem h.ρ_mem i)) (commute_of_conj_eq e)
      with e' | e'
    · exact refl_ne_zpow h i 0 (by rw [e', zpow_zero])
    · exact refl_ne_zpow h i _ e'
  · have hinv := conj_ρ_eq_inv h hy2 hyD hfix
    have h2 : y * (b * ρ ^ (i + 1)) * y⁻¹ = b * ρ ^ (i + 1) := by
      calc y * (b * ρ ^ (i + 1)) * y⁻¹ = (y * (b * ρ ^ i) * y⁻¹) * (y * ρ * y⁻¹) := by
            rw [zpow_add_one]; group
        _ = b * ρ ^ i * ρ ^ (2 : ℤ) * ρ⁻¹ := by rw [e, hinv, hzc]
        _ = b * ρ ^ (i + 1) := by group
    rcases hfix _ (mul_mem h.s_mem (zpow_mem h.ρ_mem _)) (commute_of_conj_eq h2)
      with e' | e'
    · exact refl_ne_zpow h _ 0 (by rw [e', zpow_zero])
    · exact refl_ne_zpow h _ _ e'

theorem false_of_elemAbelian {x : G} (hxD : x ∈ D) (hx2 : x * x = 1) (hx1 : x ≠ 1)
    (hxc : x ≠ ρ ^ DihData.zc j) (hρx : x * (ρ * x * ρ⁻¹) * (x * (ρ * x * ρ⁻¹)) = 1)
    (hyx : x * (y * x * y⁻¹) * (x * (y * x * y⁻¹)) = 1) : False := by
  obtain ⟨i, rfl⟩ := refl_of_mem h hxD hx2 hx1 hxc
  have hbinv : b⁻¹ = b := h.s_inv
  have hbb : ∀ k : ℤ, b * ρ ^ i * (b * ρ ^ k) = ρ ^ (k - i) := fun k => by
    calc b * ρ ^ i * (b * ρ ^ k) = (b * ρ ^ i * b⁻¹) * ρ ^ k := by rw [hbinv]; group
      _ = ρ ^ (-i) * ρ ^ k := by rw [h.s_zpow]
      _ = ρ ^ (k - i) := by rw [← zpow_add]; congr 1; ring
  have hρx' : ρ * (b * ρ ^ i) * ρ⁻¹ = b * ρ ^ (i - 2) := by
    have := zpow_mul_refl h 1 i
    rw [zpow_one] at this
    rw [this, mul_one]
  rw [hρx', hbb, ← zpow_add, h.zpow_eq_one_iff] at hρx
  obtain ⟨k, hk⟩ := hρx
  have hj : j = 0 := by
    by_contra hj
    have h2 : (2 : ℤ) ≤ 2 ^ j := by
      calc (2 : ℤ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) (by omega)
    push_cast at hk
    have h3 : (4 * 2 ^ j : ℤ) * k = -4 := by linarith
    rcases lt_trichotomy k 0 with hk0 | hk0 | hk0
    · have : k ≤ -1 := by omega
      nlinarith
    · rw [hk0] at h3; simp at h3
    · nlinarith
  subst hj
  have hzc : DihData.zc 0 = 2 := rfl
  have hinv := conj_ρ_eq_inv h hy2 hyD hfix
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  have hρc : ρ * (b * ρ ^ i) * ρ⁻¹ = b * ρ ^ i * ρ ^ DihData.zc 0 := by
    rw [hρx', mul_assoc, ← zpow_add, hzc]
    congr 1
    rw [h.zpow_eq_iff]
    exact ⟨-1, by push_cast; ring⟩
  have hyxD : y * (b * ρ ^ i) * y⁻¹ ∈ D := (hyD _).mp hxD
  have hyx2 : y * (b * ρ ^ i) * y⁻¹ * (y * (b * ρ ^ i) * y⁻¹) = 1 := by
    rw [show y * (b * ρ ^ i) * y⁻¹ * (y * (b * ρ ^ i) * y⁻¹) =
      y * (b * ρ ^ i * (b * ρ ^ i)) * y⁻¹ by group, hx2]; group
  have hyx1 : y * (b * ρ ^ i) * y⁻¹ ≠ 1 := fun e => hx1 (by
    calc b * ρ ^ i = y⁻¹ * (y * (b * ρ ^ i) * y⁻¹) * y := by group
      _ = 1 := by rw [e]; group)
  have hyxc : y * (b * ρ ^ i) * y⁻¹ ≠ ρ ^ DihData.zc 0 := fun e => by
    apply hxc
    have h1 : y⁻¹ * ρ ^ DihData.zc 0 * y = ρ ^ DihData.zc 0 := by
      have h2 : y * ρ ^ DihData.zc 0 * y⁻¹ = ρ ^ DihData.zc 0 := by
        rw [← conj_zpow, hinv, inv_zpow, ← zpow_neg, h.z0_inv]
      rw [hyinv] at h2 ⊢
      exact h2
    calc b * ρ ^ i = y⁻¹ * (y * (b * ρ ^ i) * y⁻¹) * y := by group
      _ = ρ ^ DihData.zc 0 := by rw [e, h1]
  obtain ⟨m, hm⟩ := refl_of_mem h hyxD hyx2 hyx1 hyxc
  rw [hm, hbb, ← zpow_add, h.zpow_eq_one_iff] at hyx
  obtain ⟨k', hk'⟩ := hyx
  push_cast at hk'
  have hyc : y * (b * ρ ^ i) * y⁻¹ = b * ρ ^ i ∨
      y * (b * ρ ^ i) * y⁻¹ = b * ρ ^ i * ρ ^ DihData.zc 0 := by
    rw [hm, mul_assoc, ← zpow_add, hzc]
    rcases Int.even_or_odd k' with ⟨l, hl⟩ | ⟨l, hl⟩
    · left
      congr 1
      rw [h.zpow_eq_iff]
      exact ⟨l, by push_cast; linarith⟩
    · right
      congr 1
      rw [h.zpow_eq_iff]
      exact ⟨l, by push_cast; linarith⟩
  exact false_of_four h hy2 hyD hfix ⟨i, rfl⟩ (Or.inr hρc) hyc

theorem exists_conj_refl {x : G} (hx : ∃ i : ℤ, x = b * ρ ^ i) :
    ∃ g ∈ D, g * x * g⁻¹ = b ∨ g * (y * x * y⁻¹) * g⁻¹ = b := by
  obtain ⟨i, rfl⟩ := hx
  obtain ⟨u, c, -, -, hbc⟩ := h.act hyD
  have hinv := conj_ρ_eq_inv h hy2 hyD hfix
  have hcz : ∀ k : ℤ, y * ρ ^ k * y⁻¹ = ρ ^ (-k) := fun k => by
    rw [← conj_zpow, hinv, inv_zpow, zpow_neg]
  have hcodd : Odd c := by
    by_contra hc
    obtain ⟨l, hl⟩ := Int.not_odd_iff_even.mp hc
    have hw : y * (b * ρ ^ l) * y⁻¹ = b * ρ ^ l := by
      calc y * (b * ρ ^ l) * y⁻¹ = (y * b * y⁻¹) * (y * ρ ^ l * y⁻¹) := by group
        _ = b * ρ ^ c * ρ ^ (-l) := by rw [hbc, hcz]
        _ = b * ρ ^ l := by rw [mul_assoc, ← zpow_add, hl]; congr 2; ring
    rcases hfix _ (mul_mem h.s_mem (zpow_mem h.ρ_mem l)) (commute_of_conj_eq hw)
      with e | e
    · exact refl_ne_zpow h l 0 (by rw [e, zpow_zero])
    · exact refl_ne_zpow h l _ e
  rcases Int.even_or_odd i with ⟨m, hm⟩ | ⟨m, hm⟩
  · refine ⟨ρ ^ m, zpow_mem h.ρ_mem m, Or.inl ?_⟩
    rw [zpow_mul_refl h, hm, show m + m - 2 * m = 0 by ring, zpow_zero, mul_one]
  · obtain ⟨c', hc'⟩ := hcodd
    have hyx : y * (b * ρ ^ i) * y⁻¹ = b * ρ ^ (c - i) := by
      calc y * (b * ρ ^ i) * y⁻¹ = (y * b * y⁻¹) * (y * ρ ^ i * y⁻¹) := by group
        _ = b * ρ ^ c * ρ ^ (-i) := by rw [hbc, hcz]
        _ = b * ρ ^ (c - i) := by group
    refine ⟨ρ ^ (c' - m), zpow_mem h.ρ_mem _, Or.inr ?_⟩
    rw [hyx, zpow_mul_refl h, hc', hm, show 2 * c' + 1 - (2 * m + 1) - 2 * (c' - m) = 0 by ring,
      zpow_zero, mul_one]

end Dih

theorem dihData_conjugate {G : Type} [Group G] {D : Subgroup G} {ρ b : G} {j : ℕ}
    (h : DihData D ρ b j) (g : G) :
    DihData (conjugate D g) (g⁻¹ * ρ * g) (g⁻¹ * b * g) j where
  ρ_mem := conj_inv_mem_conjugate h.ρ_mem
  s_mem := conj_inv_mem_conjugate h.s_mem
  s_sq := by
    rw [show g⁻¹ * b * g * (g⁻¹ * b * g) = g⁻¹ * (b * b) * g by group, h.s_sq]; group
  s_conj := by
    rw [show g⁻¹ * b * g * (g⁻¹ * ρ * g) * (g⁻¹ * b * g)⁻¹ = g⁻¹ * (b * ρ * b⁻¹) * g by group,
      h.s_conj]; group
  elem := by
    intro d hd
    obtain ⟨i, e | e⟩ := h.elem _ (mem_conjugate_iff.mp hd)
    · refine ⟨i, Or.inl ?_⟩
      rw [conj_inv_zpow, ← e]; group
    · refine ⟨i, Or.inr ?_⟩
      rw [conj_inv_zpow, show g⁻¹ * b * g * (g⁻¹ * ρ ^ i * g) = g⁻¹ * (b * ρ ^ i) * g by group,
        ← e]
      group
  ord := by
    have := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) ρ
    rw [MulAut.conj_apply, inv_inv] at this
    rw [this, h.ord]

end CFSG.ComponentClassification.Sol78.F514
