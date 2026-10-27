module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5SwapComm
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5SwapDiag

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS

open scoped commutatorElement

section Central

variable {W : Type} [Group W] [Finite W]

omit [Finite W] in
theorem le_normalizer_of_comm {K₁ K₂ : Subgroup W} (hcomm : ∀ a ∈ K₁, ∀ b ∈ K₂, Commute a b) :
    K₂ ≤ normalizer (K₁ : Set W) := by
  intro b hb
  have h : ∀ c ∈ K₂, ∀ a ∈ K₁, c * a * c⁻¹ = a := fun c hc a ha => by
    have := (hcomm a ha c hc).eq
    calc c * a * c⁻¹ = (a * c) * c⁻¹ := by rw [← this]
      _ = a := by group
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [h b hb x hx]
    exact hx
  · intro hx
    have h1 := h b⁻¹ (K₂.inv_mem hb) (b * x * b⁻¹) hx
    have e : b⁻¹ * (b * x * b⁻¹) * b⁻¹⁻¹ = x := by group
    rw [e] at h1
    rw [h1]
    exact hx

omit [Finite W] in
theorem normal_subgroupOf_inf {K N : Subgroup W} (hN : ∀ q ∈ K, ∀ m ∈ N, q * m * q⁻¹ ∈ N) :
    ((N ⊓ K).subgroupOf K).Normal := by
  refine ⟨fun x hx g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  exact ⟨hN g g.2 x hx.1, K.mul_mem (K.mul_mem g.2 hx.2) (K.inv_mem g.2)⟩

theorem inf_eq_bot_of_normalized {K M : Subgroup W} (hK : IsQuasisimple ↥K)
    (hZ : IsPGroup 2 ↥(center ↥K)) (hMn : ∀ q ∈ K, ∀ m ∈ M, q * m * q⁻¹ ∈ M)
    (hModd : Odd (Nat.card M)) : M ⊓ K = ⊥ := by
  have := normal_subgroupOf_inf hMn
  have hcard : Nat.card ((M ⊓ K).subgroupOf K) = Nat.card ↥(M ⊓ K) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  have hodd : Odd (Nat.card ((M ⊓ K).subgroupOf K)) :=
    hcard ▸ hModd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have hbot := normal_odd_eq_bot_of_quasisimple hK hZ hodd
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  have hx' : (⟨x, hx.2⟩ : ↥K) ∈ (M ⊓ K).subgroupOf K := hx
  rw [hbot, Subgroup.mem_bot] at hx'
  exact congrArg Subtype.val hx'

omit [Finite W] in
theorem exists_pow_two_eq_one {K : Subgroup W} (hZ : IsPGroup 2 ↥(center ↥K)) {b : W}
    (hb : b ∈ K) (hc : ∀ y ∈ K, b * y = y * b) : ∃ n : ℕ, b ^ (2 ^ n) = 1 := by
  have hmem : (⟨b, hb⟩ : ↥K) ∈ center ↥K := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hc g g.2).symm
  obtain ⟨n, hn⟩ := hZ ⟨⟨b, hb⟩, hmem⟩
  refine ⟨n, ?_⟩
  have := congrArg (fun x : ↥(center ↥K) => ((x : ↥K) : W)) hn
  simpa using this

omit [Finite W] in
theorem mul_comm_of_conj_eq {K M : Subgroup W} (hMn : ∀ q ∈ K, ∀ m ∈ M, q * m * q⁻¹ ∈ M)
    (hMK : M ⊓ K = ⊥) {m b y : W} (hm : m ∈ M) (hb : b ∈ K) (hy : y ∈ K)
    (hconj : m * y * m⁻¹ = b * y * b⁻¹) : b * y = y * b := by
  have h1 : m * y * m⁻¹ * y⁻¹ ∈ M ⊓ K := by
    refine ⟨?_, ?_⟩
    · have := M.mul_mem hm (hMn y hy m⁻¹ (M.inv_mem hm))
      simpa [mul_assoc] using this
    · rw [hconj]
      exact K.mul_mem (K.mul_mem (K.mul_mem hb hy) (K.inv_mem hb)) (K.inv_mem hy)
  rw [hMK, Subgroup.mem_bot, hconj] at h1
  exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h1)

theorem odd_normal_eq_bot_sup {K₁ K₂ : Subgroup W} (hK₁ : IsQuasisimple ↥K₁)
    (hZ₁ : IsPGroup 2 ↥(center ↥K₁)) (hK₂ : IsQuasisimple ↥K₂) (hZ₂ : IsPGroup 2 ↥(center ↥K₂))
    (hcomm : ∀ a ∈ K₁, ∀ b ∈ K₂, Commute a b) {M : Subgroup W} (hMQ : M ≤ K₁ ⊔ K₂)
    (hMn : ∀ q ∈ K₁ ⊔ K₂, ∀ m ∈ M, q * m * q⁻¹ ∈ M) (hModd : Odd (Nat.card M)) : M = ⊥ := by
  have hn₁ : ∀ q ∈ K₁, ∀ m ∈ M, q * m * q⁻¹ ∈ M := fun q hq m hm =>
    hMn q (Subgroup.mem_sup_left hq) m hm
  have hn₂ : ∀ q ∈ K₂, ∀ m ∈ M, q * m * q⁻¹ ∈ M := fun q hq m hm =>
    hMn q (Subgroup.mem_sup_right hq) m hm
  have hM₁ : M ⊓ K₁ = ⊥ := inf_eq_bot_of_normalized hK₁ hZ₁ hn₁ hModd
  have hM₂ : M ⊓ K₂ = ⊥ := inf_eq_bot_of_normalized hK₂ hZ₂ hn₂ hModd
  have hcomm' : ∀ a ∈ K₂, ∀ b ∈ K₁, Commute a b := fun a ha b hb => (hcomm b hb a ha).symm
  rw [Subgroup.eq_bot_iff_forall]
  intro m hm
  obtain ⟨a, ha, b, hb, rfl⟩ :=
    (CFSG.SignalizerFunctor.Helpers.mem_sup_of_normalizing K₂ K₁
      (le_normalizer_of_comm hcomm') m).mp (by rw [sup_comm]; exact hMQ hm)
  have hb2 : ∃ n : ℕ, b ^ (2 ^ n) = 1 := by
    refine exists_pow_two_eq_one hZ₁ hb fun y hy => mul_comm_of_conj_eq hn₁ hM₁ hm hb hy ?_
    have hc : Commute a (b * y * b⁻¹) :=
      hcomm' a ha _ (K₁.mul_mem (K₁.mul_mem hb hy) (K₁.inv_mem hb))
    calc a * b * y * (a * b)⁻¹ = a * (b * y * b⁻¹) * a⁻¹ := by group
      _ = b * y * b⁻¹ := by rw [hc.eq]; group
  have ha2 : ∃ n : ℕ, a ^ (2 ^ n) = 1 := by
    refine exists_pow_two_eq_one hZ₂ ha fun y hy => mul_comm_of_conj_eq hn₂ hM₂ hm ha hy ?_
    have hc : Commute b y := hcomm b hb y hy
    calc a * b * y * (a * b)⁻¹ = a * (b * y * b⁻¹) * a⁻¹ := by group
      _ = a * y * a⁻¹ := by rw [hc.eq]; group
  obtain ⟨k, hk⟩ := hb2
  obtain ⟨l, hl⟩ := ha2
  have hab : Commute a b := hcomm' a ha b hb
  have hpa : a ^ (2 ^ (k + l)) = 1 := by rw [pow_add, pow_mul', hl, one_pow]
  have hpb : b ^ (2 ^ (k + l)) = 1 := by rw [pow_add, pow_mul, hk, one_pow]
  have hdvd : orderOf (a * b) ∣ 2 ^ (k + l) :=
    orderOf_dvd_of_pow_eq_one (by rw [hab.mul_pow, hpa, hpb, one_mul])
  have hdvd' : orderOf (a * b) ∣ Nat.card M := by
    have := orderOf_dvd_natCard (⟨a * b, hm⟩ : M)
    rwa [Subgroup.orderOf_mk] at this
  have hcop : Nat.Coprime (orderOf (a * b)) (2 ^ (k + l)) :=
    Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr (hModd.of_dvd_nat hdvd'))
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop hdvd)

theorem swap_central_contra {K₁ K₂ : Subgroup W} (hK₁ : IsQuasisimple ↥K₁)
    (hcomm : ∀ a ∈ K₁, ∀ b ∈ K₂, Commute a b) {R : Subgroup W} (hRQ : R ≤ K₁ ⊔ K₂)
    (hRn : ∀ q ∈ K₁ ⊔ K₂, ∀ ρ ∈ R, q * ρ * q⁻¹ ∈ R) (hRp : IsPGroup 2 ↥R)
    (hmem : ∀ k ∈ K₁, ∃ k' ∈ K₂, k * k'⁻¹ ∈ R) : False := by
  have hnorm : K₁ ⊔ K₂ ≤ normalizer (K₁ : Set W) :=
    sup_le Subgroup.le_normalizer (le_normalizer_of_comm hcomm)
  have hρK : ∀ ρ ∈ R, ∀ k ∈ K₁, ρ * k * ρ⁻¹ ∈ K₁ := fun ρ hρ k hk =>
    (mem_normalizer_iff.mp (hnorm (hRQ hρ)) k).mp hk
  have hn₁ : ∀ q ∈ K₁, ∀ ρ ∈ R, q * ρ * q⁻¹ ∈ R := fun q hq ρ hρ =>
    hRn q (Subgroup.mem_sup_left hq) ρ hρ
  have hN := normal_subgroupOf_inf hn₁
  have hp : IsPGroup 2 ↥((R ⊓ K₁).subgroupOf K₁) :=
    (hRp.to_le inf_le_left).of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
  have hcen := normal_pgroup_le_center_of_quasisimple hK₁ hp
  have hcen' : ∀ x ∈ R ⊓ K₁, ∀ y ∈ K₁, Commute y x := by
    intro x hx y hy
    have hx' : (⟨x, hx.2⟩ : ↥K₁) ∈ (R ⊓ K₁).subgroupOf K₁ := hx
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp (hcen hx') ⟨y, hy⟩)
  have hRc : ∀ ρ ∈ R, ∀ k ∈ K₁, Commute ρ k := by
    intro ρ hρ
    refine commute_of_central_comm (commutator_eq_self_of_quasisimple hK₁) (hρK ρ hρ) ?_
    intro k hk x hx
    have h1 : k⁻¹ * ρ * k⁻¹⁻¹ ∈ R := hn₁ k⁻¹ (K₁.inv_mem hk) ρ hρ
    have e : k⁻¹ * (ρ * k * ρ⁻¹) = k⁻¹ * ρ * k⁻¹⁻¹ * ρ⁻¹ := by group
    have hmemR : k⁻¹ * (ρ * k * ρ⁻¹) ∈ R := by
      rw [e]
      exact R.mul_mem h1 (R.inv_mem hρ)
    have hmemK : k⁻¹ * (ρ * k * ρ⁻¹) ∈ K₁ :=
      K₁.mul_mem (K₁.inv_mem hk) (hρK ρ hρ k hk)
    exact hcen' _ ⟨hmemR, hmemK⟩ x hx
  refine not_commutative_of_quasisimple hK₁ fun a ha y hy => ?_
  obtain ⟨k', hk', hR⟩ := hmem a ha
  have h1 : Commute (a * k'⁻¹) y := hRc _ hR y hy
  have h2 : Commute y k'⁻¹ := hcomm y hy k'⁻¹ (K₂.inv_mem hk')
  have h3 : a * y * k'⁻¹ = y * a * k'⁻¹ :=
    calc a * y * k'⁻¹ = a * (y * k'⁻¹) := by group
      _ = a * (k'⁻¹ * y) := by rw [h2.eq]
      _ = a * k'⁻¹ * y := by group
      _ = y * (a * k'⁻¹) := h1.eq
      _ = y * a * k'⁻¹ := by group
  exact mul_right_cancel h3

end Central

end CFSG.OddStandard.Solomon75
