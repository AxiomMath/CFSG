module

public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.IntervalCases

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup

section Homocyclic

variable {M : Type*} [Group M] [Finite M]

omit [Finite M] in
theorem pushUp_exists_powHom (hM : ∀ x y : M, x * y = y * x) (n : ℕ) :
    ∃ P : M →* M, ∀ x, P x = x ^ n :=
  ⟨{ toFun := fun x => x ^ n
     map_one' := one_pow n
     map_mul' := fun x y => (Commute.mul_pow (hM x y) n) }, fun _ => rfl⟩

theorem pushUp_card_pow_eq_one_le (hM : ∀ x y : M, x * y = y * x) {q : ℕ}
    (hΩ : ∀ P : M →* M, (∀ x, P x = x ^ 2) → Nat.card P.ker ≤ q) :
    ∀ j : ℕ, ∀ P : M →* M, (∀ x, P x = x ^ 2 ^ j) → Nat.card P.ker ≤ q ^ j := by
  intro j
  induction j with
  | zero =>
    intro P hP
    have : P.ker = ⊥ := by
      ext x
      rw [MonoidHom.mem_ker, hP, pow_zero, pow_one, mem_bot]
    rw [this, card_bot, pow_zero]
  | succ j ih =>
    intro P hP
    obtain ⟨Pj, hPj⟩ := pushUp_exists_powHom hM (2 ^ j)
    obtain ⟨P2, hP2⟩ := pushUp_exists_powHom hM 2
    set φ := Pj.domRestrict P.ker with hφ
    have h1 := card_mul_index φ.ker
    rw [index_ker] at h1
    have h2 : Nat.card φ.ker ≤ q ^ j := by
      refine le_trans ?_ (ih Pj hPj)
      refine Nat.card_le_card_of_injective (fun x => (⟨(x : P.ker), ?_⟩ : Pj.ker)) ?_
      · have hx : φ (x : P.ker) = 1 := MonoidHom.mem_ker.mp x.2
        exact MonoidHom.mem_ker.mpr hx
      · intro a b hab
        exact Subtype.ext (Subtype.ext (congrArg (fun z : Pj.ker => ((z : M))) hab))
    have h3 : Nat.card φ.range ≤ q := by
      refine le_trans (card_le_of_le (K := P2.ker) ?_) (hΩ P2 hP2)
      rintro _ ⟨x, rfl⟩
      rw [MonoidHom.mem_ker, hP2, hφ, MonoidHom.domRestrict_apply, hPj, ← pow_mul, ← pow_succ]
      have hx := x.2
      rw [MonoidHom.mem_ker, hP] at hx
      exact hx
    calc Nat.card P.ker = Nat.card φ.ker * Nat.card φ.range := h1.symm
      _ ≤ q ^ j * q := Nat.mul_le_mul h2 h3
      _ = q ^ (j + 1) := (pow_succ q j).symm

theorem pushUp_range_eq_ker (hM : ∀ x y : M, x * y = y * x) {q e : ℕ} (hq : 0 < q)
    (hcard : Nat.card M = q ^ e) (hpow : ∀ x : M, x ^ 2 ^ e = 1)
    (hΩ : ∀ P : M →* M, (∀ x, P x = x ^ 2) → Nat.card P.ker ≤ q) {j : ℕ} (hj : j ≤ e)
    (P Q : M →* M) (hP : ∀ x, P x = x ^ 2 ^ (e - j)) (hQ : ∀ x, Q x = x ^ 2 ^ j) :
    P.range = Q.ker ∧ q ^ j ≤ Nat.card P.range := by
  have hle : P.range ≤ Q.ker := by
    rintro _ ⟨z, rfl⟩
    rw [MonoidHom.mem_ker, hQ, hP, ← pow_mul, ← pow_add, Nat.sub_add_cancel hj]
    exact hpow z
  have h1 := card_mul_index P.ker
  rw [index_ker, hcard] at h1
  have h2 := pushUp_card_pow_eq_one_le hM hΩ (e - j) P hP
  have h3 := pushUp_card_pow_eq_one_le hM hΩ j Q hQ
  have hge : q ^ j ≤ Nat.card P.range := by
    by_contra hlt
    push Not at hlt
    have hpos : 0 < q ^ (e - j) := pow_pos hq _
    have h4 : Nat.card P.ker * Nat.card P.range < q ^ (e - j) * q ^ j :=
      lt_of_le_of_lt (Nat.mul_le_mul_right _ h2) (Nat.mul_lt_mul_of_pos_left hlt hpos)
    rw [← pow_add, Nat.sub_add_cancel hj] at h4
    omega
  exact ⟨eq_of_le_of_card_ge hle (h3.trans hge), hge⟩

theorem pushUp_pow_two_pow_add {M : Type*} [Monoid M] (x : M) (a b : ℕ) :
    x ^ 2 ^ (a + b) = (x ^ 2 ^ a) ^ 2 ^ b := by
  rw [pow_add, pow_mul]

theorem pushUp_dichotomy_abstract {M : Type*} [CommGroup M] [Finite M] {q e : ℕ} (hq : 0 < q)
    (he : 2 ≤ e) (hcard : Nat.card M = q ^ e) (hpow : ∀ x : M, x ^ 2 ^ e = 1) (A : Subgroup M)
    (hΩ : ∀ x : M, x ^ 2 = 1 → x ∈ A) (hA : Nat.card A ≤ q) (δ : ℕ → M →* M)
    (hδinj : ∀ n x, δ n x = 1 → x = 1)
    (htr : ∀ b ∈ A, ∀ b' ∈ A, b ≠ 1 → b' ≠ 1 → ∃ n, δ n b = b') (ω : M →* M)
    (hω2 : ∀ x, ω (ω x) = x) (hωA : ∀ b ∈ A, ω b = b) (hωδ : ∀ n x, ω (δ n x) = δ n (ω x)) :
    (∀ x, ω x = x → x ∈ A) ∨ ∀ x, x⁻¹ * ω x ∈ A := by
  classical
  have hM : ∀ x y : M, x * y = y * x := mul_comm
  have hΩ' : ∀ P : M →* M, (∀ x, P x = x ^ 2) → Nat.card P.ker ≤ q := by
    intro P hP
    refine le_trans (Nat.card_le_card_of_injective (fun y : P.ker => (⟨(y : M), ?_⟩ : A)) ?_) hA
    · exact hΩ _ (by rw [← hP]; exact MonoidHom.mem_ker.mp y.2)
    · intro a b hab
      exact Subtype.ext (congrArg (fun z : A => (z : M)) hab)
  have hHC : ∀ j ≤ e, ∀ x : M, x ^ 2 ^ j = 1 → ∃ z : M, z ^ 2 ^ (e - j) = x := by
    intro j hj x hx
    obtain ⟨P, hP⟩ := pushUp_exists_powHom hM (2 ^ (e - j))
    obtain ⟨Q, hQ⟩ := pushUp_exists_powHom hM (2 ^ j)
    obtain ⟨heq, -⟩ := pushUp_range_eq_ker hM hq hcard hpow hΩ' hj P Q hP hQ
    have hxQ : x ∈ Q.ker := by rw [MonoidHom.mem_ker, hQ]; exact hx
    rw [← heq] at hxQ
    obtain ⟨z, hz⟩ := hxQ
    exact ⟨z, by rw [← hP]; exact hz⟩
  obtain ⟨ψ, hψ⟩ : ∃ ψ : M →* M, ∀ x, ψ x = x⁻¹ * ω x :=
    ⟨{ toFun := fun x => x⁻¹ * ω x
       map_one' := by rw [inv_one, one_mul, map_one]
       map_mul' := fun x y => by rw [map_mul, mul_inv, mul_mul_mul_comm] }, fun _ => rfl⟩
  have hψA : ∀ b ∈ A, ψ b = 1 := fun b hb => by rw [hψ, hωA b hb, inv_mul_cancel]
  have hψψ : ∀ x, ψ (ψ x) = ((ψ x) ^ 2)⁻¹ := by
    intro x
    have h1 : ω (ψ x) = (ω x)⁻¹ * x := by rw [hψ, map_mul, map_inv, hω2]
    rw [hψ (ψ x), h1, hψ]
    simp only [sq, mul_inv_rev, inv_inv, mul_assoc]
  have hψδ : ∀ n x, ψ (δ n x) = δ n (ψ x) := by
    intro n x
    rw [hψ, hψ, hωδ, map_mul, map_inv]
  have he1 : e - 1 + 1 = e := Nat.sub_add_cancel (by omega)
  have he2 : e - 2 + 1 = e - 1 := by omega
  have hstep1 : ∀ x, ψ x ^ 2 ^ (e - 1) = 1 := by
    intro x
    rw [← map_pow]
    refine hψA _ (hΩ _ ?_)
    rw [← pow_mul, ← pow_succ, he1]
    exact hpow x
  by_cases hP : ∀ x, ψ x ^ 2 ^ (e - 2) = 1
  ·
    right
    have claim : ∀ j, j ≤ e - 2 → (∀ x, ψ x ^ 2 ^ j = 1) → ∀ x, ψ x ^ 2 = 1 := by
      intro j
      induction j using Nat.strong_induction_on with
      | _ j ih =>
        intro hj hQj x
        rcases Nat.lt_or_ge j 2 with hj2 | hj2
        · interval_cases j
          · have := hQj x
            rw [pow_zero, pow_one] at this
            rw [this, one_pow]
          · simpa using hQj x
        · set m := 2 * j - e with hm
          refine ih (m + 1) (by omega) (by omega) (fun y => ?_) x
          obtain ⟨z, hz⟩ := hHC j (by omega) (ψ y) (hQj y)
          have h1 : ((ψ y ^ 2)⁻¹) ^ 2 ^ m = 1 := by
            rw [← hψψ, ← hz, map_pow, ← pow_mul, ← pow_add]
            have hjm : e - j + m = j + (e - j + m - j) := by omega
            rw [hjm, pushUp_pow_two_pow_add, hQj z, one_pow]
          rw [inv_pow, inv_eq_one, ← pow_mul, ← pow_succ'] at h1
          exact h1
    intro x
    exact hΩ _ (by rw [← hψ]; exact claim (e - 2) le_rfl hP x)
  ·
    left
    push Not at hP
    obtain ⟨x₁, hx₁⟩ := hP
    have hb₁ : x₁ ^ 2 ^ (e - 1) ≠ 1 := by
      intro h1
      obtain ⟨z, hz⟩ := hHC (e - 1) (by omega) x₁ h1
      apply hx₁
      rw [← hz, show e - (e - 1) = 1 by omega, map_pow, pow_one, ← pow_mul, ← pow_succ', he2]
      exact hstep1 z
    have claimC : ∀ x, x ^ 2 ^ (e - 1) ≠ 1 → ψ x ^ 2 ^ (e - 2) ≠ 1 := by
      intro x hx
      have hsq : ∀ y : M, (y ^ 2 ^ (e - 1)) ^ 2 = 1 := fun y => by
        rw [← pow_mul, ← pow_succ, he1]; exact hpow y
      obtain ⟨n, hn⟩ := htr _ (hΩ _ (hsq x₁)) _ (hΩ _ (hsq x)) hb₁ hx
      have h1 : (x⁻¹ * δ n x₁) ^ 2 ^ (e - 1) = 1 := by
        rw [mul_pow, inv_pow, ← map_pow, hn, inv_mul_cancel]
      obtain ⟨z, hz⟩ := hHC (e - 1) (by omega) _ h1
      rw [show e - (e - 1) = 1 by omega, pow_one] at hz
      have h2 : δ n x₁ = x * z ^ 2 := by rw [hz, mul_inv_cancel_left]
      intro hψx
      apply hx₁
      apply hδinj n
      rw [map_pow, ← hψδ, h2, map_mul, mul_pow, hψx, one_mul, map_pow, ← pow_mul, ← pow_succ', he2]
      exact hstep1 z
    intro x hωx
    have hψx : ψ x = 1 := by rw [hψ, hωx, inv_mul_cancel]
    by_contra hxA
    have hx2 : x ^ 2 ≠ 1 := fun h => hxA (hΩ x h)
    have hex : ∃ k, x ^ 2 ^ k = 1 := ⟨e, hpow x⟩
    set k₀ := Nat.find hex with hk₀
    have hk₀1 : x ^ 2 ^ k₀ = 1 := Nat.find_spec hex
    have hk₀e : k₀ ≤ e := Nat.find_min' hex (hpow x)
    have hk₀2 : 2 ≤ k₀ := by
      by_contra hlt
      push Not at hlt
      interval_cases h : k₀
      · rw [pow_zero, pow_one] at hk₀1
        exact hx2 (by rw [hk₀1, one_pow])
      · exact hx2 (by simpa using hk₀1)
    have hk₀m : x ^ 2 ^ (k₀ - 1) ≠ 1 := Nat.find_min hex (by omega)
    obtain ⟨z, hz⟩ := hHC k₀ hk₀e x hk₀1
    have hz1 : z ^ 2 ^ (e - 1) ≠ 1 := by
      rw [show e - 1 = (e - k₀) + (k₀ - 1) by omega, pushUp_pow_two_pow_add, hz]
      exact hk₀m
    apply claimC z hz1
    rw [show e - 2 = (e - k₀) + (k₀ - 2) by omega, pushUp_pow_two_pow_add, ← map_pow, hz, hψx,
      one_pow]

theorem pushUp_exists_pow_four_ne_abstract {M : Type*} [CommGroup M] [Finite M] {q e : ℕ}
    (hq : 3 ≤ q) (he : 3 ≤ e) (hcard : Nat.card M = q ^ e) (hpow : ∀ x : M, x ^ 2 ^ e = 1)
    (A : Subgroup M) (hΩ : ∀ x : M, x ^ 2 = 1 → x ∈ A) (hA : Nat.card A ≤ q) :
    ∃ a b : M, ∀ k : ℤ, (a ^ k * b) ^ 4 ≠ 1 ∧ (b ^ k * a) ^ 4 ≠ 1 := by
  classical
  have hM : ∀ x y : M, x * y = y * x := mul_comm
  have hΩ' : ∀ P : M →* M, (∀ x, P x = x ^ 2) → Nat.card P.ker ≤ q := by
    intro P hP
    refine le_trans (Nat.card_le_card_of_injective (fun y : P.ker => (⟨(y : M), ?_⟩ : A)) ?_) hA
    · exact hΩ _ (by rw [← hP]; exact MonoidHom.mem_ker.mp y.2)
    · intro a b hab
      exact Subtype.ext (congrArg (fun z : A => (z : M)) hab)
  obtain ⟨P, hP⟩ := pushUp_exists_powHom hM (2 ^ (e - 1))
  obtain ⟨Q, hQ⟩ := pushUp_exists_powHom hM (2 ^ 1)
  obtain ⟨heq, hge⟩ := pushUp_range_eq_ker hM (by omega) hcard hpow hΩ' (j := 1) (by omega) P Q
    hP hQ
  rw [pow_one] at hge
  have hcard3 : ({1} : Set M).ncard < (P.range : Set M).ncard := by
    rw [Set.ncard_singleton, ← Nat.card_coe_set_eq]
    change 1 < Nat.card P.range
    omega
  obtain ⟨b₁, hb₁P, hb₁1⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard hcard3
  have hcard3' : ({1, b₁} : Set M).ncard < (P.range : Set M).ncard := by
    rw [← Nat.card_coe_set_eq (P.range : Set M)]
    change _ < Nat.card P.range
    calc ({1, b₁} : Set M).ncard ≤ ({b₁} : Set M).ncard + 1 := Set.ncard_insert_le 1 {b₁}
      _ = 2 := by rw [Set.ncard_singleton]
      _ < Nat.card P.range := by omega
  obtain ⟨b₂, hb₂P, hb₂1⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard hcard3'
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hb₁1 hb₂1
  obtain ⟨hb₂ne1, hb₂b₁⟩ := hb₂1
  have hsq : ∀ b ∈ (P.range : Set M), b ^ 2 = 1 := fun b hb => by
    have : b ∈ Q.ker := heq ▸ hb
    rw [MonoidHom.mem_ker, hQ, pow_one] at this
    exact this
  obtain ⟨z₁, hz₁⟩ := hb₁P
  obtain ⟨z₂, hz₂⟩ := hb₂P
  have hfour : ∀ z : M, (z ^ 2 ^ (e - 3)) ^ 4 = P z := fun z => by
    rw [hP, ← pow_mul, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add, show e - 3 + 2 = e - 1 by omega]
  have hzpow : ∀ (x b : M), x ^ 4 = b → b ^ 2 = 1 → ∀ k : ℤ, (x ^ k) ^ 4 = 1 ∨ (x ^ k) ^ 4 = b := by
    intro x b hxb hb k
    have h1 : (x ^ k) ^ 4 = b ^ k := by
      rw [← hxb, ← zpow_natCast, ← zpow_mul, ← zpow_natCast x 4, ← zpow_mul, mul_comm]
    rw [h1]
    rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
    · left
      rw [zpow_mul, show ((2 : ℤ)) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast, hb, one_zpow]
    · right
      rw [zpow_add, zpow_one, zpow_mul, show ((2 : ℤ)) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast,
        hb, one_zpow, one_mul]
  have hb₁sq := hsq b₁ ⟨z₁, hz₁⟩
  have hb₂sq := hsq b₂ ⟨z₂, hz₂⟩
  have hne : b₁ * b₂ ≠ 1 := by
    intro h
    apply hb₂b₁
    have : b₂ = b₁⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [this, inv_eq_of_mul_eq_one_left (by rw [← sq]; exact hb₁sq)]
  have hne' : b₂ * b₁ ≠ 1 := by rw [mul_comm]; exact hne
  refine ⟨z₁ ^ 2 ^ (e - 3), z₂ ^ 2 ^ (e - 3), fun k => ⟨?_, ?_⟩⟩
  · rw [mul_pow, hfour z₂, hz₂]
    rcases hzpow _ b₁ (by rw [hfour, hz₁]) hb₁sq k with h | h <;> rw [h]
    · rw [one_mul]; exact hb₂ne1
    · exact hne
  · rw [mul_pow, hfour z₁, hz₁]
    rcases hzpow _ b₂ (by rw [hfour, hz₂]) hb₂sq k with h | h <;> rw [h]
    · rw [one_mul]; exact hb₁1
    · exact hne'

end Homocyclic

section Stage

variable {G : Type*} [Group G] [Finite G]

theorem pushUp_exists_pow_eq {V A : Subgroup G} (hVc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x)
    {q e : ℕ} (hq : 0 < q) (hcard : Nat.card V = q ^ e) (hpow : ∀ x ∈ V, x ^ 2 ^ e = 1)
    (hΩ : ∀ x ∈ V, x ^ 2 = 1 → x ∈ A) (hA : Nat.card A ≤ q) {j : ℕ} (hj : j ≤ e) {x : G}
    (hx : x ∈ V) (hxj : x ^ 2 ^ j = 1) : ∃ z ∈ V, z ^ 2 ^ (e - j) = x := by
  have hM : ∀ a b : V, a * b = b * a := fun a b => Subtype.ext (hVc _ a.2 _ b.2)
  have hΩ' : ∀ P : V →* V, (∀ y, P y = y ^ 2) → Nat.card P.ker ≤ q := by
    intro P hP
    refine le_trans (Nat.card_le_card_of_injective
      (fun y : P.ker => (⟨((y : V) : G), ?_⟩ : A)) ?_) hA
    · have hy := MonoidHom.mem_ker.mp y.2
      rw [hP] at hy
      exact hΩ _ (y : V).2 (congrArg Subtype.val hy)
    · intro a b hab
      exact Subtype.ext (Subtype.ext (congrArg (fun z : A => (z : G)) hab))
  obtain ⟨P, hP⟩ := pushUp_exists_powHom hM (2 ^ (e - j))
  obtain ⟨Q, hQ⟩ := pushUp_exists_powHom hM (2 ^ j)
  have hpow' : ∀ y : V, y ^ 2 ^ e = 1 := fun y => Subtype.ext (hpow _ y.2)
  obtain ⟨heq, -⟩ := pushUp_range_eq_ker hM hq hcard hpow' hΩ' hj P Q hP hQ
  have hxQ : (⟨x, hx⟩ : V) ∈ Q.ker := by
    rw [MonoidHom.mem_ker, hQ]
    exact Subtype.ext hxj
  rw [← heq] at hxQ
  obtain ⟨z, hz⟩ := hxQ
  refine ⟨z, z.2, ?_⟩
  have := congrArg Subtype.val hz
  rw [hP] at this
  exact this

omit [Finite G] in
theorem pushUp_conj_eq_of_odd {V : Subgroup G} (hVc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x)
    {e : ℕ} (hpow : ∀ x ∈ V, x ^ 2 ^ e = 1) {c : G} (hcV : c ∈ normalizer (V : Set G))
    {m : ℕ} (hm : Odd m) (hcm : c ^ m = 1) (hc2 : ∀ x ∈ V, x ^ 2 = 1 → c * x * c⁻¹ = x) :
    ∀ x ∈ V, c * x * c⁻¹ = x := by
  suffices key : ∀ j : ℕ, ∀ x ∈ V, x ^ 2 ^ j = 1 → c * x * c⁻¹ = x from
    fun x hx => key e x hx (hpow x hx)
  intro j
  induction j with
  | zero =>
    intro x _ hx1
    rw [pow_zero, pow_one] at hx1
    rw [hx1, mul_one, mul_inv_cancel]
  | succ j ih =>
    intro x hx hxj
    set y := c * x * c⁻¹ with hy
    have hyV : y ∈ V := (mem_normalizer_iff.mp hcV x).mp hx
    have hx2 : c * x ^ 2 * c⁻¹ = x ^ 2 :=
      ih (x ^ 2) (pow_mem hx 2) (by rw [← pow_mul, ← pow_succ']; exact hxj)
    have hy2 : y ^ 2 = x ^ 2 := by rw [hy, conj_pow, hx2]
    set a := x⁻¹ * y with ha
    have haV : a ∈ V := mul_mem (inv_mem hx) hyV
    have ha2 : a ^ 2 = 1 := by
      have hc : (x⁻¹ * y) * (x⁻¹ * y) = (x⁻¹ * x⁻¹) * (y * y) := by
        rw [mul_assoc, ← mul_assoc y x⁻¹ y, hVc y hyV x⁻¹ (inv_mem hx)]
        group
      rw [ha, sq, hc, ← sq, ← sq, hy2, inv_pow, inv_mul_cancel]
    have hca : c * a * c⁻¹ = a := hc2 a haV ha2
    have hn : ∀ n : ℕ, c ^ n * x * (c ^ n)⁻¹ = x * a ^ n := by
      intro n
      induction n with
      | zero => simp
      | succ n ihn =>
        calc c ^ (n + 1) * x * (c ^ (n + 1))⁻¹ = c * (c ^ n * x * (c ^ n)⁻¹) * c⁻¹ := by
              rw [pow_succ']; group
          _ = (c * x * c⁻¹) * (c * a ^ n * c⁻¹) := by rw [ihn]; group
          _ = y * a ^ n := by rw [← conj_pow, hca]
          _ = x * a ^ (n + 1) := by rw [pow_succ', ← mul_assoc, ha, mul_inv_cancel_left]
    have h1 := hn m
    rw [hcm, one_mul, inv_one, mul_one] at h1
    obtain ⟨k, rfl⟩ := hm
    rw [pow_succ, pow_mul, ha2, one_pow, one_mul] at h1
    have ha1 : a = 1 := by
      have := congrArg (fun z => x⁻¹ * z) h1
      simpa using this.symm
    rw [ha] at ha1
    exact (inv_mul_eq_one.mp ha1).symm

theorem pushUp_sign_dichotomy {V A : Subgroup G} (hVc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x)
    {q e : ℕ} (hq : 0 < q) (he : 2 ≤ e) (hcard : Nat.card V = q ^ e)
    (hpow : ∀ x ∈ V, x ^ 2 ^ e = 1) (hΩ : ∀ x ∈ V, x ^ 2 = 1 → x ∈ A) (hA : Nat.card A ≤ q)
    {d : G} (hdV : d ∈ normalizer (V : Set G))
    (htr : ∀ b ∈ A, ∀ b' ∈ A, b ≠ 1 → b' ≠ 1 → ∃ n : ℕ, (d ^ n)⁻¹ * b * d ^ n = b')
    {w : G} (hwV : w ∈ normalizer (V : Set G)) (hw2 : w ^ 2 = 1)
    (hwA : ∀ b ∈ A, w * b * w⁻¹ = b)
    (hwd : ∀ x ∈ V, w * (d * x * d⁻¹) * w⁻¹ = d * (w * x * w⁻¹) * d⁻¹) :
    (∀ u ∈ V, w * u * w⁻¹ = u → u ∈ A) ∨ ∀ u ∈ V, u⁻¹ * (w * u * w⁻¹) ∈ A := by
  let _ : CommGroup V :=
    { (inferInstance : Group V) with mul_comm := fun a b => Subtype.ext (hVc _ a.2 _ b.2) }
  have hdV' : ∀ n : ℕ, ∀ x ∈ V, (d ^ n)⁻¹ * x * d ^ n ∈ V := fun n x hx =>
    (mem_normalizer_iff''.mp (pow_mem hdV n) x).mp hx
  have hwV' : ∀ x ∈ V, w * x * w⁻¹ ∈ V := fun x hx => (mem_normalizer_iff.mp hwV x).mp hx
  obtain ⟨δ, hδ⟩ : ∃ δ : ℕ → V →* V, ∀ n x, ((δ n x : V) : G) = (d ^ n)⁻¹ * x * d ^ n :=
    ⟨fun n =>
      { toFun := fun x => ⟨(d ^ n)⁻¹ * x * d ^ n, hdV' n x x.2⟩
        map_one' := Subtype.ext (show (d ^ n)⁻¹ * 1 * d ^ n = 1 by group)
        map_mul' := fun x y => Subtype.ext (show (d ^ n)⁻¹ * ((x : G) * y) * d ^ n =
          ((d ^ n)⁻¹ * x * d ^ n) * ((d ^ n)⁻¹ * y * d ^ n) by group) }, fun _ _ => rfl⟩
  obtain ⟨ω, hω⟩ : ∃ ω : V →* V, ∀ x, ((ω x : V) : G) = w * x * w⁻¹ :=
    ⟨{ toFun := fun x => ⟨w * x * w⁻¹, hwV' x x.2⟩
       map_one' := Subtype.ext (show w * 1 * w⁻¹ = 1 by group)
       map_mul' := fun x y => Subtype.ext (show w * ((x : G) * y) * w⁻¹ =
          (w * x * w⁻¹) * (w * y * w⁻¹) by group) }, fun _ => rfl⟩
  set A' := A.subgroupOf V with hA'
  have hA'card : Nat.card A' ≤ q := by
    refine le_trans (Nat.card_le_card_of_injective (fun x : A' => (⟨((x : V) : G), x.2⟩ : A)) ?_)
      hA
    intro a b hab
    exact Subtype.ext (Subtype.ext (congrArg (fun z : A => (z : G)) hab))
  have hwd' : ∀ x ∈ V, w * (d⁻¹ * x * d) * w⁻¹ = d⁻¹ * (w * x * w⁻¹) * d := by
    intro x hx
    have hy : d⁻¹ * x * d ∈ V := by simpa using hdV' 1 x hx
    have h1 := hwd _ hy
    rw [show d * (d⁻¹ * x * d) * d⁻¹ = x by group] at h1
    rw [h1]
    group
  have hwdn : ∀ n : ℕ, ∀ x ∈ V, w * ((d ^ n)⁻¹ * x * d ^ n) * w⁻¹ =
      (d ^ n)⁻¹ * (w * x * w⁻¹) * d ^ n := by
    intro n
    induction n with
    | zero => intro x _; simp
    | succ n ih =>
      intro x hx
      rw [pow_succ, show (d ^ n * d)⁻¹ * x * (d ^ n * d) = d⁻¹ * ((d ^ n)⁻¹ * x * d ^ n) * d by
        group, hwd' _ (hdV' n x hx), ih x hx]
      group
  have key := pushUp_dichotomy_abstract (M := V) hq he hcard (fun x => Subtype.ext (hpow _ x.2))
    A' (fun x hx => mem_subgroupOf.mpr (hΩ _ x.2 (congrArg Subtype.val hx))) hA'card δ
    (fun n x hx => Subtype.ext (by
      have h1 := congrArg Subtype.val hx
      rw [hδ] at h1
      have h2 := congrArg (fun z => d ^ n * z * (d ^ n)⁻¹) h1
      simp only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one] at h2
      simpa using h2))
    (fun b hb b' hb' hb1 hb1' => by
      obtain ⟨n, hn⟩ := htr _ (mem_subgroupOf.mp hb) _ (mem_subgroupOf.mp hb')
        (fun h => hb1 (Subtype.ext h)) (fun h => hb1' (Subtype.ext h))
      exact ⟨n, Subtype.ext (by rw [hδ]; exact hn)⟩)
    ω (fun x => Subtype.ext (by
      rw [hω, hω]
      calc w * (w * (x : G) * w⁻¹) * w⁻¹ = (w * w) * x * (w * w)⁻¹ := by group
        _ = x := by rw [← sq, hw2]; group))
    (fun b hb => Subtype.ext (by rw [hω]; exact hwA _ (mem_subgroupOf.mp hb)))
    (fun n x => Subtype.ext (by rw [hω, hδ, hδ, hω]; exact hwdn n x x.2))
  rcases key with h | h
  · left
    intro u hu hwu
    exact mem_subgroupOf.mp (h ⟨u, hu⟩ (Subtype.ext (by rw [hω]; exact hwu)))
  · right
    intro u hu
    have := mem_subgroupOf.mp (h ⟨u, hu⟩)
    rwa [coe_mul, coe_inv, hω] at this

theorem pushUp_exists_pow_four_ne {V A : Subgroup G} (hVc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x)
    {q e : ℕ} (hq : 3 ≤ q) (he : 3 ≤ e) (hcard : Nat.card V = q ^ e)
    (hpow : ∀ x ∈ V, x ^ 2 ^ e = 1) (hΩ : ∀ x ∈ V, x ^ 2 = 1 → x ∈ A) (hA : Nat.card A ≤ q) :
    ∃ a ∈ V, ∃ b ∈ V, ∀ k : ℤ, (a ^ k * b) ^ 4 ≠ 1 ∧ (b ^ k * a) ^ 4 ≠ 1 := by
  let _ : CommGroup V :=
    { (inferInstance : Group V) with mul_comm := fun a b => Subtype.ext (hVc _ a.2 _ b.2) }
  have hA'card : Nat.card (A.subgroupOf V) ≤ q := by
    refine le_trans (Nat.card_le_card_of_injective
      (fun x : A.subgroupOf V => (⟨((x : V) : G), x.2⟩ : A)) ?_) hA
    intro a b hab
    exact Subtype.ext (Subtype.ext (congrArg (fun z : A => (z : G)) hab))
  obtain ⟨a, b, hab⟩ := pushUp_exists_pow_four_ne_abstract (M := V) hq he hcard
    (fun x => Subtype.ext (hpow _ x.2)) (A.subgroupOf V)
    (fun x hx => mem_subgroupOf.mpr (hΩ _ x.2 (congrArg Subtype.val hx))) hA'card
  refine ⟨a, a.2, b, b.2, fun k => ⟨fun h => (hab k).1 (Subtype.ext h),
    fun h => (hab k).2 (Subtype.ext h)⟩⟩

end Stage

end CFSG.SeitzReduction.RankOne
