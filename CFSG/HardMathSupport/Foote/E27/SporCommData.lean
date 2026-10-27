module

public import CFSG.HardMathSupport.Foote.E27.SporSpecial
public import CFSG.Monster.B.Pinned.Primes.Extraspecial

public section

namespace CFSG.HardMathSupport.Foote.E27

open Subgroup CFSG.Monster.B.Pinned

variable {X : Type} [Group X] [Finite X] {K R T : Subgroup X} {z : X}

theorem E27Config.false_of_commData (h : E27Config X K R T z) (hz : z ∈ K)
    {J : Type*} [Group J] [Finite J] (φ : ↥K ≃* J) {k : ℕ} (hk : 4 ≤ k) {q : Fin (2 * k) → J}
    {w : J} {M : Matrix (Fin (2 * k)) (Fin (2 * k)) (ZMod 3)} (hD : CommData 3 q w M)
    {L : Subgroup J}
    (hLQ : ∀ b ∈ L, ∀ g ∈ closure (Set.range q), b⁻¹ * g * b ∈ closure (Set.range q))
    (hL : 3 ^ (Nat.card J).factorization 3 ∣ Nat.card L) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcen := hD.center_eq
  refine h.false_of_normal_special hz φ (Q := closure (Set.range q)) (L := L) hk hD.card_eq
    ?_ ?_ ?_ (fun b hb => mem_normalizer_of_conj (hLQ b hb)) hL
  · rw [hcen]
    exact hD.card_zQ
  · intro x y
    rw [hcen, mem_subgroupOf]
    have e : ((x * y * x⁻¹ * y⁻¹ : closure (Set.range q)) : J) = bcomm (x : J)⁻¹ (y : J)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, bcomm, inv_inv]
    rw [e]
    exact hD.bcomm_mem (inv_mem x.2) (inv_mem y.2)
  · intro x
    rw [hcen]
    obtain ⟨_, e, -, -⟩ := hD.quotient_equiv
    rw [← QuotientGroup.eq_one_iff]
    apply e.injective
    rw [QuotientGroup.mk_pow, map_pow, map_one]
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one]
    ext i
    simp only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul]
    rw [show ((3 : ℕ) : ZMod 3) = 0 from rfl, zero_mul]

section Rel

variable {G : Type*} [Group G]

theorem bcomm_eq_of_conj {a b c : G} (hca : c * a = a * c) (h : a * b * a⁻¹ = b * c) :
    bcomm a b = c := by
  have hab : a * b = b * c * a := by rw [← h]; group
  calc bcomm a b = a⁻¹ * b⁻¹ * (a * b) := by simp only [bcomm]; group
    _ = a⁻¹ * (c * a) := by rw [hab]; group
    _ = c := by rw [hca]; group

theorem pow_comm_of_conj {a z : G} (h : a * z * a⁻¹ = z) : ∀ e : ℕ, z ^ e * a = a * z ^ e
  | 0 => by rw [pow_zero, one_mul, mul_one]
  | e + 1 => by
    have hc : a * z = z * a := by rw [← mul_inv_eq_iff_eq_mul.mp h]
    rw [pow_succ, mul_assoc, ← hc, ← mul_assoc, pow_comm_of_conj h e, mul_assoc]

theorem inv_pow_val {z : G} (hz : z ^ 3 = 1) {a b : ZMod 3} (hab : a = -b) :
    (z ^ b.val)⁻¹ = z ^ a.val := by
  have hs : b.val + a.val = 0 ∨ b.val + a.val = 3 := by
    subst hab
    fin_cases b <;> decide
  rw [inv_eq_iff_mul_eq_one, ← pow_add]
  rcases hs with h | h <;> rw [h]
  · rw [pow_zero]
  · exact hz

theorem commData_of_rel {n : ℕ} {M : Matrix (Fin n) (Fin n) (ZMod 3)}
    (hanti : ∀ i j, M i j = -M j i) (hdiag : ∀ i, M i i = 0) (hdet : IsUnit M.det)
    {i₀ j₀ : Fin n} (h01 : (M i₀ j₀).val = 1) {q : Fin n → G} {z : G} (hq : ∀ i, q i ^ 3 = 1)
    (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) (hzc : ∀ i, q i * z * (q i)⁻¹ = z)
    (hchain : ∀ i j, i < j → q i * q j * (q i)⁻¹ = q j * z ^ (M i j).val) :
    CommData 3 q z M := by
  have hb : ∀ i j, bcomm (q i) (q j) = z ^ (M i j).val := by
    intro i j
    rcases lt_trichotomy i j with hij | rfl | hij
    · exact bcomm_eq_of_conj (pow_comm_of_conj (hzc i) _) (hchain i j hij)
    · rw [hdiag i, ZMod.val_zero, pow_zero, bcomm]
      group
    · rw [bcomm_swap, bcomm_eq_of_conj (pow_comm_of_conj (hzc j) _) (hchain j i hij)]
      exact inv_pow_val hz3 (hanti i j)
  refine ⟨hq, orderOf_eq_prime hz3 hz1, fun i => ?_, hb, hdet, ?_⟩
  · have h := hzc i
    rw [mul_inv_eq_iff_eq_mul] at h
    exact h
  · have h := hb i₀ j₀
    rw [h01, pow_one] at h
    rw [← h]
    simp only [bcomm]
    exact mul_mem (mul_mem (mul_mem (inv_mem (subset_closure ⟨i₀, rfl⟩))
      (inv_mem (subset_closure ⟨j₀, rfl⟩))) (subset_closure ⟨i₀, rfl⟩))
      (subset_closure ⟨j₀, rfl⟩)

theorem ofFn_mem {n : ℕ} {q : Fin n → G} {z : G} (hz : z ∈ closure (Set.range q))
    (e : Fin n → ℕ) (c : ℕ) :
    (List.ofFn fun j => q j ^ e j).prod * z ^ c ∈ closure (Set.range q) := by
  refine mul_mem (list_prod_mem fun g hg => ?_) (pow_mem hz c)
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hg
  exact pow_mem (subset_closure (Set.mem_range_self j)) (e j)

theorem local_of_rel [Finite G] {n : ℕ} {M : Matrix (Fin n) (Fin n) (ZMod 3)} {q : Fin n → G}
    {z b₁ b₂ : G} (hD : CommData 3 q z M) {X Y : GL (Fin n) (ZMod 3)} {c₁ c₂ : Fin n → ℕ}
    (h₁ : ∀ i, b₁⁻¹ * q i * b₁ = (List.ofFn fun j =>
      q j ^ ((X : Matrix (Fin n) (Fin n) (ZMod 3)) i j).val).prod * z ^ c₁ i)
    (h₂ : ∀ i, b₂⁻¹ * q i * b₂ = (List.ofFn fun j =>
      q j ^ ((Y : Matrix (Fin n) (Fin n) (ZMod 3)) i j).val).prod * z ^ c₂ i)
    {m : ℕ} (hK : 3 ^ m ∣ Nat.card (Subgroup.closure {g | g ∈ [X, Y]})) :
    (∀ b ∈ closure ({b₁, b₂} ∪ Set.range q), ∀ g ∈ closure (Set.range q),
      b⁻¹ * g * b ∈ closure (Set.range q)) ∧
    3 ^ (n + 1 + m) ∣ Nat.card (closure ({b₁, b₂} ∪ Set.range q)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set L := closure ({b₁, b₂} ∪ Set.range q) with hLdef
  have hb₁ : b₁ ∈ L := subset_closure (Or.inl (Or.inl rfl))
  have hb₂ : b₂ ∈ L := subset_closure (Or.inl (Or.inr rfl))
  have hQL : closure (Set.range q) ≤ L := closure_mono Set.subset_union_right
  have hLQ : ∀ b ∈ L, ∀ g ∈ closure (Set.range q), b⁻¹ * g * b ∈ closure (Set.range q) := by
    intro b hb
    refine conj_mem_of_mem_closure (S := {b₁, b₂} ∪ Set.range q) ?_ hb
    rintro b' ((rfl | rfl) | ⟨j, rfl⟩) g hg
    · exact CommData.conj_mem (fun i => by rw [h₁]; exact ofFn_mem hD.mem_z _ _) hg
    · exact CommData.conj_mem (fun i => by rw [h₂]; exact ofFn_mem hD.mem_z _ _) hg
    · exact mul_mem (mul_mem (inv_mem (subset_closure ⟨j, rfl⟩)) hg) (subset_closure ⟨j, rfl⟩)
  refine ⟨hLQ, ?_⟩
  let ρ : L →* GL (Fin n) (ZMod 3) :=
    (hD.actHom L fun b hb i => hLQ b hb _ (subset_closure ⟨i, rfl⟩)).toHomUnits
  have hρ : ∀ b : L, ((ρ b : GL (Fin n) (ZMod 3)) : Matrix (Fin n) (Fin n) (ZMod 3)) =
      CommData.actMat 3 q z M b := fun b => rfl
  have hX : ρ ⟨b₁, hb₁⟩ = X := Units.ext (by
    rw [hρ]
    exact hD.actMat_eq _ c₁ h₁)
  have hY : ρ ⟨b₂, hb₂⟩ = Y := Units.ext (by
    rw [hρ]
    exact hD.actMat_eq _ c₂ h₂)
  have hKr : Subgroup.closure {g | g ∈ [X, Y]} ≤ ρ.range := by
    rw [Subgroup.closure_le]
    intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false, Set.mem_ofPred_eq] at hg
    rcases hg with rfl | rfl
    · exact ⟨_, hX⟩
    · exact ⟨_, hY⟩
  have hker : (closure (Set.range q)).subgroupOf L ≤ ρ.ker := by
    intro b hb
    rw [MonoidHom.mem_ker]
    apply Units.ext
    rw [hρ, Units.val_one]
    exact hD.actMat_of_mem (mem_subgroupOf.mp hb)
  have h1 : Nat.card ρ.ker * Nat.card ρ.range = Nat.card L := by
    rw [← index_ker, card_mul_index]
  have h2 : 3 ^ (n + 1) ∣ Nat.card ρ.ker := by
    have := card_dvd_of_le hker
    rwa [Nat.card_congr (subgroupOfEquivOfLe hQL).toEquiv, hD.card_eq] at this
  have h3 : 3 ^ m ∣ Nat.card ρ.range := hK.trans (card_dvd_of_le hKr)
  rw [← h1, pow_add]
  exact Nat.mul_dvd_mul h2 h3

end Rel

end CFSG.HardMathSupport.Foote.E27
