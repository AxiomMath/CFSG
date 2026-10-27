module

public import CFSG.GH74.GLS.IVK.Proofs2.GHInvAltInv
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvAltCent

public section

namespace CFSG.GH74.GLS.IVK.GHInv

open Equiv Equiv.Perm

section Main

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

omit [Fintype Ω] [DecidableEq Ω] in
theorem mul_self_eq_one_of_commute {a b : Perm Ω} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) : (a * b) * (a * b) = 1 := by
  calc (a * b) * (a * b) = a * (b * a) * b := by group
    _ = a * (a * b) * b := by rw [hab]
    _ = (a * a) * (b * b) := by group
    _ = 1 := by rw [ha, hb, mul_one]

@[expose] def Terminal (N K : Subgroup (Perm Ω)) : Prop :=
  ∀ y ∈ N, y * y = 1 → y ≠ 1 → (∀ k ∈ K, y * k = k * y) →
    ∀ F : Finset Ω, 5 ≤ F.card → (∀ x ∈ F, y x = x) → K ≤ altOn F → K ≠ ⊥ → K = altOn F

theorem exists_altOn_eq (hΩ : Fintype.card Ω ≤ 11) {N K Q : Subgroup (Perm Ω)} {a b : Perm Ω}
    (hKA : K ≤ alternatingGroup Ω) (hKp : Group.IsPerfect K) (hK1 : K ≠ ⊥)
    (hQN : Q ≤ N) (hQK : ∀ q ∈ Q, ∀ k ∈ K, q * k = k * q)
    (ha : a ∈ Q) (hb : b ∈ Q) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab1 : a ≠ b)
    (ha2 : a * a = 1) (hb2 : b * b = 1) (habc : a * b = b * a)
    (hterm : Terminal N K) :
    ∃ F : Finset Ω, K = altOn F ∧ 5 ≤ F.card := by
  have hab' : a * b ≠ 1 := by
    intro h
    apply hab1
    have : a⁻¹ = b := (mul_eq_one_iff_inv_eq.1 h)
    rw [← this]
    exact (inv_eq_of_mul_eq_one_right ha2).symm
  have hex : ∃ y ∈ Q, y * y = 1 ∧ y ≠ 1 ∧ y.cycleType.card ≤ 4 := by
    rcases exists_cycleType_card_le_four hΩ ha2 hb2 habc with h | h | h
    · exact ⟨a, ha, ha2, ha1, h⟩
    · exact ⟨b, hb, hb2, hb1, h⟩
    · exact ⟨a * b, Q.mul_mem ha hb, mul_self_eq_one_of_commute ha2 hb2 habc, hab', h⟩
  obtain ⟨y, hyQ, hy2, hy1, hyc⟩ := hex
  let F : Finset Ω := y.supportᶜ
  have hF : ∀ x, x ∈ F ↔ y x = x := by
    intro x
    simp [F, Equiv.Perm.mem_support]
  have hKsym : K ≤ symOn F := by
    intro k hk x hx
    have hyx : y x ≠ x := fun h => hx ((hF x).2 h)
    exact perfect_fixes_support hy2 hyc hKp (fun x hx => (hQK y hyQ x hx).symm) k hk x hyx
  have hF5 : 5 ≤ F.card := by
    by_contra hlt
    exact hK1 (eq_bot_of_perfect_le_symOn (by omega) hKp hKsym)
  refine ⟨F, hterm y (hQN hyQ) hy2 hy1 (hQK y hyQ) F hF5 (fun x hx => (hF x).1 hx) ?_ hK1, hF5⟩
  intro k hk
  exact Subgroup.mem_inf.2 ⟨hKsym hk, hKA hk⟩




theorem moves_outside {N K : Subgroup (Perm Ω)} {F : Finset Ω}
    (hF5 : 5 ≤ F.card) (hKF : K = altOn F) (hK1 : K ≠ ⊥) (hterm : Terminal N K)
    {y : Perm Ω} (hyN : y ∈ N) (hy2 : y * y = 1) (hy1 : y ≠ 1)
    (hyK : ∀ k ∈ K, y * k = k * y) : ∀ x, x ∉ F → y x ≠ x := by
  intro x hx hyx
  have hyF : ∀ z ∈ F, y z = z := fun z hz =>
    fixes_of_commute_altOn hF5 (fun k hk => hyK k (hKF ▸ hk)) hz
  have hcard : (insert x F).card = F.card + 1 := Finset.card_insert_of_notMem hx
  have hle : K ≤ altOn (insert x F) := hKF ▸ altOn_mono (Finset.subset_insert x F)
  have heq : K = altOn (insert x F) :=
    hterm y hyN hy2 hy1 hyK (insert x F) (by omega) (by
      intro z hz
      rcases Finset.mem_insert.1 hz with rfl | hz
      · exact hyx
      · exact hyF z hz) hle hK1
  obtain ⟨h, hh, hhx⟩ := exists_mem_altOn_moves (F := insert x F) (by omega)
    (Finset.mem_insert_self x F)
  have hhK : h ∈ altOn F := hKF ▸ heq ▸ hh
  exact hhx ((mem_altOn.1 hhK).1 x hx)

theorem card_le_card_compl {Q : Subgroup (Perm Ω)} (hQ2 : IsPGroup 2 Q) {F : Finset Ω}
    (hfix : ∀ q ∈ Q, ∀ x ∈ F, q x = x)
    (hinv : ∀ q ∈ Q, q * q = 1 → q ≠ 1 → ∀ x, x ∉ F → q x ≠ x) {x₀ : Ω} (hx₀ : x₀ ∉ F) :
    Nat.card Q ≤ Fᶜ.card := by
  have hfree : ∀ q ∈ Q, q x₀ = x₀ → q = 1 := by
    intro q hq hqx
    by_contra hq1
    obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.1 hQ2) ⟨q, hq⟩
    have hj' : orderOf q = 2 ^ j := by rwa [Subgroup.orderOf_mk] at hj
    have hpos : 0 < orderOf q := orderOf_pos q
    have h2 : 2 ∣ orderOf q := by
      rcases j with _ | j
      · rw [pow_zero, orderOf_eq_one_iff] at hj'
        exact absurd hj' hq1
      · rw [hj', pow_succ]
        exact Dvd.intro_left _ rfl
    have hq0 := orderOf_pow_orderOf_div (x := q) hpos.ne' h2
    have hq0Q : q ^ (orderOf q / 2) ∈ Q := Q.pow_mem hq _
    have hsq : (q ^ (orderOf q / 2)) * (q ^ (orderOf q / 2)) = 1 := by
      rw [← sq, ← orderOf_dvd_iff_pow_eq_one]
      exact hq0.symm ▸ dvd_rfl
    have hne : q ^ (orderOf q / 2) ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hq0
      omega
    have hfixq : (q ^ (orderOf q / 2)) x₀ = x₀ :=
      Equiv.Perm.pow_apply_eq_self_of_apply_eq_self hqx _
    exact hinv _ hq0Q hsq hne x₀ hx₀ hfixq
  let f : Q → {x // x ∈ Fᶜ} := fun q => ⟨(q : Perm Ω) x₀, by
    rw [Finset.mem_compl]
    intro h
    have h1 := hfix q q.2 _ h
    have := (q : Perm Ω).injective h1
    exact hx₀ (this ▸ h)⟩
  have hf : Function.Injective f := by
    intro q₁ q₂ h
    have h1 : (q₁ : Perm Ω) x₀ = (q₂ : Perm Ω) x₀ := congrArg Subtype.val h
    have h2 : ((q₂⁻¹ * q₁ : Q) : Perm Ω) x₀ = x₀ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Perm.mul_apply]
      rw [h1]
      simp
    have := hfree _ (q₂⁻¹ * q₁).2 h2
    have h3 : (q₂⁻¹ * q₁ : Q) = 1 := Subtype.ext this
    exact (inv_mul_eq_one.1 h3).symm
  calc Nat.card Q ≤ Nat.card {x // x ∈ Fᶜ} := Nat.card_le_card_of_injective f hf
    _ = Fᶜ.card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]


theorem support_eq_compl {F : Finset Ω} {y : Perm Ω}
    (hfix : ∀ x ∈ F, y x = x) (hmov : ∀ x, x ∉ F → y x ≠ x) : y.support = Fᶜ := by
  ext x
  rw [Equiv.Perm.mem_support, Finset.mem_compl]
  constructor
  · intro h hx
    exact h (hfix x hx)
  · intro h
    exact hmov x h

theorem four_dvd_card_compl {F : Finset Ω} {a b : Perm Ω}
    (ha2 : a * a = 1) (hb2 : b * b = 1) (hab : a * b = b * a)
    (hsa : a.support = Fᶜ) (hsb : b.support = Fᶜ) (hsab : (a * b).support = Fᶜ) :
    4 ∣ Fᶜ.card := by
  obtain ⟨ha1, ha3⟩ := involution_cycle_data ha2
  obtain ⟨hb1, hb3⟩ := involution_cycle_data hb2
  obtain ⟨hc1, hc3⟩ := involution_cycle_data (mul_self_eq_one_of_commute ha2 hb2 hab)
  rw [hsa] at ha1
  rw [hsb] at hb1
  rw [hsab] at hc1
  have e1 : a.cycleType.card = (a * b).cycleType.card := by omega
  have e2 : b.cycleType.card = (a * b).cycleType.card := by omega
  rw [e1] at ha3
  rw [e2] at hb3
  have hs := Equiv.Perm.sign_mul a b
  rw [ha3, hb3, hc3] at hs
  have h1 : ((-1 : ℤˣ) ^ (a * b).cycleType.card) = 1 := by
    have := hs
    rw [← pow_add] at this
    have h2 : ((-1 : ℤˣ) ^ ((a * b).cycleType.card)) *
        ((-1 : ℤˣ) ^ ((a * b).cycleType.card)) =
        ((-1 : ℤˣ) ^ ((a * b).cycleType.card)) * 1 := by
      rw [mul_one, ← pow_add]
      exact this.symm
    exact (mul_left_cancel h2)
  rw [neg_one_pow_eq_one_iff_even (by decide)] at h1
  obtain ⟨r, hr⟩ := h1
  exact ⟨r, by omega⟩

theorem le_alternatingGroup_of_card {N K : Subgroup (Perm Ω)} {F : Finset Ω}
    (hNA : alternatingGroup Ω ≤ N) (hF5 : 5 ≤ F.card) (hKF : K = altOn F) (hK1 : K ≠ ⊥)
    (hterm : Terminal N K) (hc : 3 ≤ Fᶜ.card) : N ≤ alternatingGroup Ω := by
  intro g hgN
  by_contra hg
  have hsg : sign g = -1 := by
    rcases Int.units_eq_one_or (sign g) with h | h
    · exact absurd (Equiv.Perm.mem_alternatingGroup.2 h) hg
    · exact h
  obtain ⟨c₁, c₂, c₃, h1, h2, h3, h12, h13, h23⟩ := Finset.two_lt_card_iff.1 (by omega : 2 < Fᶜ.card)
  have hτ : Equiv.swap c₁ c₂ ∈ N := by
    have hA : g⁻¹ * Equiv.swap c₁ c₂ ∈ alternatingGroup Ω := by
      rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, map_inv, hsg,
        Equiv.Perm.sign_swap h12]
      decide
    have := N.mul_mem hgN (hNA hA)
    simpa using this
  have hτ2 : Equiv.swap c₁ c₂ * Equiv.swap c₁ c₂ = 1 := Equiv.swap_mul_self c₁ c₂
  have hτ1 : Equiv.swap c₁ c₂ ≠ 1 := by
    intro h
    have := congrArg (fun p : Perm Ω => p c₁) h
    simp at this
    exact h12 this.symm
  have hτK : ∀ k ∈ K, Equiv.swap c₁ c₂ * k = k * Equiv.swap c₁ c₂ := by
    intro k hk
    have hk' := mem_altOn.1 (hKF ▸ hk)
    have hc1 : k c₁ = c₁ := hk'.1 c₁ (Finset.mem_compl.1 h1)
    have hc2 : k c₂ = c₂ := hk'.1 c₂ (Finset.mem_compl.1 h2)
    rw [Equiv.mul_swap_eq_swap_mul, hc1, hc2]
  have := moves_outside hF5 hKF hK1 hterm hτ hτ2 hτ1 hτK c₃ (Finset.mem_compl.1 h3)
  exact this (Equiv.swap_apply_of_ne_of_ne h13.symm h23.symm)

theorem alt_main (hΩ : Fintype.card Ω ≤ 11) {N K Q : Subgroup (Perm Ω)} {a b : Perm Ω}
    (hNA : alternatingGroup Ω ≤ N) (hKA : K ≤ alternatingGroup Ω)
    (hKp : Group.IsPerfect K) (hK1 : K ≠ ⊥)
    (hQN : Q ≤ N) (hQK : ∀ q ∈ Q, ∀ k ∈ K, q * k = k * q) (hQ2 : IsPGroup 2 Q)
    (hQ4 : 4 ≤ Nat.card Q)
    (ha : a ∈ Q) (hb : b ∈ Q) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab1 : a ≠ b)
    (ha2 : a * a = 1) (hb2 : b * b = 1) (habc : a * b = b * a)
    (hterm : Terminal N K) :
    ∃ F : Finset Ω, K = altOn F ∧ 5 ≤ F.card ∧ F.card + 4 = Fintype.card Ω ∧
      N ≤ alternatingGroup Ω ∧ Nat.card Q ≤ 4 := by
  obtain ⟨F, hKF, hF5⟩ := exists_altOn_eq hΩ hKA hKp hK1 hQN hQK ha hb ha1 hb1 hab1 ha2 hb2 habc hterm
  have hfixQ : ∀ q ∈ Q, ∀ x ∈ F, q x = x := fun q hq x hx =>
    fixes_of_commute_altOn hF5 (fun k hk => hQK q hq k (hKF ▸ hk)) hx
  have hmovQ : ∀ q ∈ Q, q * q = 1 → q ≠ 1 → ∀ x, x ∉ F → q x ≠ x :=
    fun q hq h2 h1 => moves_outside hF5 hKF hK1 hterm (hQN hq) h2 h1 (hQK q hq)
  obtain ⟨x₀, hx₀⟩ : ∃ x, a x ≠ x := by
    by_contra h
    push Not at h
    exact ha1 (Equiv.ext h)
  have hx₀F : x₀ ∉ F := fun h => hx₀ (hfixQ a ha x₀ h)
  have hQc : Nat.card Q ≤ Fᶜ.card := card_le_card_compl hQ2 hfixQ hmovQ hx₀F
  have hab' : a * b ≠ 1 := by
    intro h
    apply hab1
    have : a⁻¹ = b := (mul_eq_one_iff_inv_eq.1 h)
    rw [← this]
    exact (inv_eq_of_mul_eq_one_right ha2).symm
  have hab2 := mul_self_eq_one_of_commute ha2 hb2 habc
  have hsa : a.support = Fᶜ := support_eq_compl (hfixQ a ha) (hmovQ a ha ha2 ha1)
  have hsb : b.support = Fᶜ := support_eq_compl (hfixQ b hb) (hmovQ b hb hb2 hb1)
  have hsab : (a * b).support = Fᶜ :=
    support_eq_compl (hfixQ _ (Q.mul_mem ha hb)) (hmovQ _ (Q.mul_mem ha hb) hab2 hab')
  have hdvd := four_dvd_card_compl ha2 hb2 habc hsa hsb hsab
  have hcard : F.card + Fᶜ.card = Fintype.card Ω := Finset.card_add_card_compl F
  have hc4 : Fᶜ.card = 4 := by omega
  refine ⟨F, hKF, hF5, by omega, le_alternatingGroup_of_card hNA hF5 hKF hK1 hterm (by omega), by omega⟩

end Main

end CFSG.GH74.GLS.IVK.GHInv
