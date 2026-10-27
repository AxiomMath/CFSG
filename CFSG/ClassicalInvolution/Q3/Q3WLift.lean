module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.Group

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open scoped commutatorElement

variable {Y X : Type*} [Group Y] [Group X]

theorem commutatorElement_mul_central_left {k : Y} (hk : k ∈ Subgroup.center Y) (a b : Y) :
    ⁅a * k, b⁆ = ⁅a, b⁆ := by
  have h : k * b * k⁻¹ = b := by
    rw [mul_inv_eq_iff_eq_mul]
    exact (Subgroup.mem_center_iff.mp hk b).symm
  calc ⁅a * k, b⁆ = a * (k * b * k⁻¹) * a⁻¹ * b⁻¹ := by
        simp only [commutatorElement_def]; group
    _ = ⁅a, b⁆ := by rw [h]; rfl

theorem commutatorElement_mul_central_right {k : Y} (hk : k ∈ Subgroup.center Y) (a b : Y) :
    ⁅a, b * k⁆ = ⁅a, b⁆ := by
  have h : k * a⁻¹ * k⁻¹ = a⁻¹ := by
    rw [mul_inv_eq_iff_eq_mul]
    exact (Subgroup.mem_center_iff.mp hk a⁻¹).symm
  calc ⁅a, b * k⁆ = a * b * (k * a⁻¹ * k⁻¹) * b⁻¹ := by
        simp only [commutatorElement_def]; group
    _ = ⁅a, b⁆ := by rw [h]; rfl

theorem commutator_le_center_of_map_commute (π : Y →* X) (hker : π.ker ≤ Subgroup.center Y)
    {A B : Subgroup Y} (hc : ∀ a ∈ A, ∀ b ∈ B, π a * π b = π b * π a) :
    ⁅A, B⁆ ≤ Subgroup.center Y := by
  refine le_trans ?_ hker
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [MonoidHom.mem_ker, commutatorElement_def]
  simp only [map_mul, map_inv]
  rw [hc a ha b hb]
  group

theorem commutes_derived_left {A B : Subgroup Y} (h : ⁅A, B⁆ ≤ Subgroup.center Y) :
    ∀ α ∈ ⁅A, A⁆, ∀ w ∈ B, w * α = α * w := by
  have h1 : ⁅⁅A, B⁆, A⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    (h.trans (Subgroup.center_le_centralizer _))
  have h2 : ⁅⁅B, A⁆, A⁆ = ⊥ := by
    rw [Subgroup.commutator_comm B A]; exact h1
  have h3 : ⁅⁅A, A⁆, B⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
  intro α hα w hw
  exact Subgroup.mem_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h3 hα)
    w hw

theorem commutes_of_perfect_image (π : Y →* X) (hker : π.ker ≤ Subgroup.center Y)
    {A B : Subgroup Y} (hB : ⁅B.map π, B.map π⁆ = B.map π)
    (hc : ∀ a ∈ A, ∀ b ∈ B, π a * π b = π b * π a) :
    ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := by
  have hAB : ⁅A, B⁆ ≤ Subgroup.center Y := commutator_le_center_of_map_commute π hker hc
  have hBA : ⁅B, A⁆ ≤ Subgroup.center Y := by rwa [Subgroup.commutator_comm]
  intro a ha b hb
  have hbm : π b ∈ ⁅B.map π, B.map π⁆ := by rw [hB]; exact ⟨b, hb, rfl⟩
  rw [← Subgroup.map_commutator] at hbm
  obtain ⟨b', hb', hbb'⟩ := hbm
  have hn : b'⁻¹ * b ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul π b'⁻¹ b, map_inv, hbb', inv_mul_cancel]
  have hnc := Subgroup.mem_center_iff.mp (hker hn)
  have hab' : a * b' = b' * a := commutes_derived_left hBA b' hb' a ha
  have hb_eq : b = b' * (b'⁻¹ * b) := by group
  calc a * b = a * (b' * (b'⁻¹ * b)) := by rw [← hb_eq]
    _ = (a * b') * (b'⁻¹ * b) := by simp only [mul_assoc]
    _ = (b' * a) * (b'⁻¹ * b) := by rw [hab']
    _ = b' * ((b'⁻¹ * b) * a) := by rw [mul_assoc, hnc a]
    _ = (b' * (b'⁻¹ * b)) * a := by simp only [mul_assoc]
    _ = b * a := by rw [← hb_eq]

theorem commutes_of_map_le_perfect (π : Y →* X) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center Y) {M : Subgroup X} (hM : ⁅M, M⁆ = M) {A L : Subgroup Y}
    (hA : ∀ a ∈ A, ∀ m ∈ M, π a * m = m * π a) (hL : ∀ l ∈ L, π l ∈ M) :
    ∀ a ∈ A, ∀ l ∈ L, a * l = l * a := by
  have hNM : (M.comap π).map π = M := Subgroup.map_comap_eq_self_of_surjective hπ M
  have hBM : ⁅M.comap π, M.comap π⁆.map π = M := by
    rw [Subgroup.map_commutator, hNM, hM]
  have hc : ∀ a ∈ A, ∀ b ∈ ⁅M.comap π, M.comap π⁆, π a * π b = π b * π a := fun a ha b hb =>
    hA a ha (π b) (hBM ▸ ⟨b, hb, rfl⟩)
  have key := commutes_of_perfect_image π hker (A := A) (B := ⁅M.comap π, M.comap π⁆)
    (by rw [hBM]; exact hM) hc
  intro a ha l hl
  have hlM : π l ∈ ⁅M.comap π, M.comap π⁆.map π := by rw [hBM]; exact hL l hl
  obtain ⟨b, hb, hbl⟩ := hlM
  have hn : b⁻¹ * l ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul π b⁻¹ l, map_inv, hbl, inv_mul_cancel]
  have hnc := Subgroup.mem_center_iff.mp (hker hn)
  have hab := key a ha b hb
  calc a * l = a * (b * (b⁻¹ * l)) := by group
    _ = (a * b) * (b⁻¹ * l) := by simp only [mul_assoc]
    _ = (b * a) * (b⁻¹ * l) := by rw [hab]
    _ = b * ((b⁻¹ * l) * a) := by rw [mul_assoc, hnc a]
    _ = (b * (b⁻¹ * l)) * a := by simp only [mul_assoc]
    _ = l * a := by group

theorem commutator_pow_of_central' {x y : Y} (hc : ∀ k : ℕ, ⁅x ^ k, y⁆ ∈ Subgroup.center Y)
    (n : ℕ) : ⁅x ^ n, y⁆ = ⁅x, y⁆ ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : ⁅x ^ n * x, y⁆ = x ^ n * ⁅x, y⁆ * (x ^ n)⁻¹ * ⁅x ^ n, y⁆ := by
      simp only [commutatorElement_def]
      group
    have hx : ⁅x, y⁆ ∈ Subgroup.center Y := by simpa using hc 1
    have h2 : x ^ n * ⁅x, y⁆ * (x ^ n)⁻¹ = ⁅x, y⁆ := by
      rw [Subgroup.mem_center_iff.mp hx (x ^ n)]
      group
    rw [pow_succ, h1, h2, ih, pow_succ']

theorem commutes_of_map_commute_exponent3 (π : Y →* X) (hker : π.ker ≤ Subgroup.center Y)
    (hcop : ∀ n ∈ π.ker, ¬ 3 ∣ orderOf n) {A L : Subgroup Y}
    (hL : ∀ l ∈ L, l ^ 3 ∈ ⁅L, L⁆) (hc : ∀ a ∈ A, ∀ l ∈ L, π a * π l = π l * π a) :
    ∀ a ∈ A, ∀ l ∈ L, a * l = l * a := by
  have hAL : ⁅A, L⁆ ≤ Subgroup.center Y := commutator_le_center_of_map_commute π hker hc
  have hLA : ⁅L, A⁆ ≤ Subgroup.center Y := by rwa [Subgroup.commutator_comm]
  have hα := commutes_derived_left hLA
  intro a ha l hl
  have hcl : ∀ k : ℕ, ⁅l ^ k, a⁆ ∈ Subgroup.center Y := fun k =>
    hLA (Subgroup.commutator_mem_commutator (L.pow_mem hl k) ha)
  have hmem : ⁅l, a⁆ ∈ π.ker := by
    rw [MonoidHom.mem_ker, commutatorElement_def]
    simp only [map_mul, map_inv]
    rw [(hc a ha l hl).symm]
    group
  have hpow : ⁅l, a⁆ ^ 3 = 1 := by
    rw [← commutator_pow_of_central' hcl 3, commutatorElement_eq_one_iff_mul_comm]
    exact (hα (l ^ 3) (hL l hl) a ha).symm
  have hord : orderOf ⁅l, a⁆ ∣ 3 := orderOf_dvd_of_pow_eq_one hpow
  have h1 : orderOf ⁅l, a⁆ = 1 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hord with h | h
    · exact h
    · exact (hcop _ hmem (dvd_of_eq h.symm)).elim
  exact (commutatorElement_eq_one_iff_mul_comm.mp (orderOf_eq_one_iff.mp h1)).symm

theorem commutes_of_swap (π : Y →* X) (hker : π.ker ≤ Subgroup.center Y)
    (hodd : ∀ n ∈ π.ker, Odd (orderOf n)) {A B : Subgroup Y} {x y : Y} (hx : x ∈ A)
    (hy : y ∈ B) (hA : ∀ a ∈ A, ∃ (i : ℤ) (α : Y), α ∈ ⁅A, A⁆ ∧ a = x ^ i * α)
    (hB : ∀ b ∈ B, ∃ (j : ℤ) (β : Y), β ∈ ⁅B, B⁆ ∧ b = y ^ j * β)
    (hc : ∀ a ∈ A, ∀ b ∈ B, π a * π b = π b * π a) {g : Y}
    (hgx : π (g * x * g⁻¹) = π y) (hgy : π (g * y * g⁻¹) = π x) :
    ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := by
  have hAB : ⁅A, B⁆ ≤ Subgroup.center Y := commutator_le_center_of_map_commute π hker hc
  have hBA : ⁅B, A⁆ ≤ Subgroup.center Y := by rwa [Subgroup.commutator_comm]
  have hAA : ⁅A, A⁆ ≤ A := by
    rw [Subgroup.commutator_le]
    intro g₁ h₁ g₂ h₂
    rw [commutatorElement_def]
    exact A.mul_mem (A.mul_mem (A.mul_mem h₁ h₂) (A.inv_mem h₁)) (A.inv_mem h₂)
  have hα : ∀ α ∈ ⁅A, A⁆, ∀ w ∈ B, w * α = α * w := commutes_derived_left hAB
  have hβ : ∀ β ∈ ⁅B, B⁆, ∀ w ∈ A, w * β = β * w := commutes_derived_left hBA
  have hxy : x * y = y * x := by
    have hcker : ⁅x, y⁆ ∈ π.ker := by
      rw [MonoidHom.mem_ker, commutatorElement_def]
      simp only [map_mul, map_inv]
      rw [hc x hx y hy]
      group
    have hccen := hker hcker
    have hk1 : y⁻¹ * (g * x * g⁻¹) ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul π y⁻¹ (g * x * g⁻¹), map_inv, hgx, inv_mul_cancel]
    have hk2 : x⁻¹ * (g * y * g⁻¹) ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul π x⁻¹ (g * y * g⁻¹), map_inv, hgy, inv_mul_cancel]
    have hconj : ⁅g * x * g⁻¹, g * y * g⁻¹⁆ = ⁅x, y⁆ := by
      have h1 : ⁅g * x * g⁻¹, g * y * g⁻¹⁆ = g * ⁅x, y⁆ * g⁻¹ := by
        simp only [commutatorElement_def]; group
      have h2 := Subgroup.mem_center_iff.mp hccen g
      rw [h1, h2]
      group
    have hx' : g * x * g⁻¹ = y * (y⁻¹ * (g * x * g⁻¹)) := (mul_inv_cancel_left y _).symm
    have hy' : g * y * g⁻¹ = x * (x⁻¹ * (g * y * g⁻¹)) := (mul_inv_cancel_left x _).symm
    have hinv : ⁅g * x * g⁻¹, g * y * g⁻¹⁆ = ⁅x, y⁆⁻¹ := by
      rw [hx', hy', commutatorElement_mul_central_left (hker hk1),
        commutatorElement_mul_central_right (hker hk2), commutatorElement_inv]
    have hsq : ⁅x, y⁆ * ⁅x, y⁆ = 1 := by
      have : ⁅x, y⁆ = ⁅x, y⁆⁻¹ := hconj.symm.trans hinv
      exact mul_eq_one_iff_eq_inv.mpr this
    have hord : orderOf ⁅x, y⁆ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hsq)
    have h1 : orderOf ⁅x, y⁆ = 1 := by
      have hodd' := hodd _ hcker
      rcases (Nat.dvd_prime Nat.prime_two).mp hord with h | h
      · exact h
      · rw [h] at hodd'
        exact absurd hodd' (by decide)
    exact commutatorElement_eq_one_iff_mul_comm.mp (orderOf_eq_one_iff.mp h1)
  intro a ha b hb
  obtain ⟨i, α, hαm, rfl⟩ := hA a ha
  obtain ⟨j, β, hβm, rfl⟩ := hB b hb
  have hxyz : x ^ i * y ^ j = y ^ j * x ^ i := (Commute.zpow_zpow hxy i j).eq
  calc x ^ i * α * (y ^ j * β) = x ^ i * (α * y ^ j) * β := by simp only [mul_assoc]
    _ = x ^ i * (y ^ j * α) * β := by rw [← hα α hαm (y ^ j) (B.zpow_mem hy j)]
    _ = (x ^ i * y ^ j) * (α * β) := by simp only [mul_assoc]
    _ = (y ^ j * x ^ i) * (β * α) := by rw [hxyz, hβ β hβm α (hAA hαm)]
    _ = y ^ j * (x ^ i * β) * α := by simp only [mul_assoc]
    _ = y ^ j * (β * x ^ i) * α := by rw [hβ β hβm (x ^ i) (A.zpow_mem hx i)]
    _ = y ^ j * β * (x ^ i * α) := by simp only [mul_assoc]

theorem orderOf_coprime_six {O : Subgroup Y} (hodd : Odd (Nat.card O)) (h3 : ¬ 3 ∣ Nat.card O)
    {n : Y} (hn : n ∈ O) : Nat.Coprime (orderOf n) 6 := by
  have h2 : Nat.Coprime (Nat.card O) 2 := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
    exact fun h => (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h)
  have h3' : Nat.Coprime (Nat.card O) 3 := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    exact h3
  have hc6 : Nat.Coprime (Nat.card O) 6 := by
    simpa using Nat.Coprime.mul_right h2 h3'
  exact Nat.Coprime.coprime_dvd_left (Subgroup.orderOf_dvd_natCard O hn) hc6

theorem le_of_map_le_of_exponent (π : Y →* X) (hker : π.ker ≤ Subgroup.center Y)
    (hcop : ∀ n ∈ π.ker, Nat.Coprime (orderOf n) 6) {L₁ L₂ : Subgroup Y}
    (h₁ : ∀ l ∈ L₁, l ^ 12 = 1) (h₂ : ∀ l ∈ L₂, l ^ 12 = 1)
    (h : ∀ l ∈ L₁, π l ∈ L₂.map π) : L₁ ≤ L₂ := by
  intro l hl
  obtain ⟨l₂, hl₂, hll₂⟩ := h l hl
  have hn : l₂⁻¹ * l ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul π l₂⁻¹ l, map_inv, hll₂, inv_mul_cancel]
  have hnc := Subgroup.mem_center_iff.mp (hker hn)
  have hcomm : Commute l₂⁻¹ l := by
    show l₂⁻¹ * l = l * l₂⁻¹
    have h1 : l * l₂⁻¹ = l₂ * ((l₂⁻¹ * l) * l₂⁻¹) := by group
    rw [h1, ← hnc l₂⁻¹]
    group
  have hpow : (l₂⁻¹ * l) ^ 12 = 1 := by
    rw [hcomm.mul_pow, inv_pow, h₂ l₂ hl₂, h₁ l hl]
    simp
  have hord : orderOf (l₂⁻¹ * l) ∣ 6 * 2 := orderOf_dvd_of_pow_eq_one hpow
  have hone : orderOf (l₂⁻¹ * l) = 1 := by
    have hc6 := hcop _ hn
    have h2 : orderOf (l₂⁻¹ * l) ∣ 2 := (Nat.Coprime.dvd_mul_left hc6).mp hord
    have hc2 : Nat.Coprime (orderOf (l₂⁻¹ * l)) 2 :=
      Nat.Coprime.coprime_dvd_right (by norm_num) hc6
    exact Nat.Coprime.eq_one_of_dvd hc2 h2
  have hn1 : l₂⁻¹ * l = 1 := orderOf_eq_one_iff.mp hone
  have : l = l₂ := by
    have := congrArg (l₂ * ·) hn1
    simpa using this
  rw [this]
  exact hl₂

end CFSG.ClassicalInvolution.Q3.Q3W
