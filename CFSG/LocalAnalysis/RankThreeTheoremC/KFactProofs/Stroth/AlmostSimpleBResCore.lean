module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG CFSG.Open Subgroup

section RelPPrimeCore

variable {G : Type*} [Group G] [Finite G] {p : ℕ}

private theorem card_join_dvd_mul {K : Type*} [Group K] (A B : Subgroup K) [B.Normal] :
    Nat.card (A ⊔ B : Subgroup K) ∣ Nat.card A * Nat.card B := by
  have hmul : B.relIndex (A ⊔ B) * Nat.card B = Nat.card (A ⊔ B : Subgroup K) := by
    have h := Subgroup.relIndex_mul_card (H := B) (K := A ⊔ B)
    rwa [inf_eq_left.2 (le_sup_right : B ≤ A ⊔ B)] at h
  rw [← hmul, Subgroup.relIndex_sup_right (H := A) (K := B)]
  exact mul_dvd_mul (Subgroup.relIndex_dvd_card (H := B) (K := A)) dvd_rfl

private theorem coprime_card_join {H N₁ N₂ : Subgroup G} (h₁ : N₁ ≤ H) (h₂ : N₂ ≤ H)
    (hn₂ : (N₂.subgroupOf H).Normal) (c₁ : Nat.Coprime p (Nat.card N₁))
    (c₂ : Nat.Coprime p (Nat.card N₂)) : Nat.Coprime p (Nat.card (N₁ ⊔ N₂ : Subgroup G)) := by
  have e₀ : Nat.card (N₁ ⊔ N₂ : Subgroup G) = Nat.card ((N₁ ⊔ N₂ : Subgroup G).subgroupOf H) :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (sup_le h₁ h₂)).toEquiv).symm
  have e₁ : Nat.card N₁ = Nat.card (N₁.subgroupOf H) :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe h₁).toEquiv).symm
  have e₂ : Nat.card N₂ = Nat.card (N₂.subgroupOf H) :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe h₂).toEquiv).symm
  have hdvd : Nat.card ((N₁ ⊔ N₂ : Subgroup G).subgroupOf H) ∣
      Nat.card (N₁.subgroupOf H) * Nat.card (N₂.subgroupOf H) := by
    rw [Subgroup.subgroupOf_sup h₁ h₂]
    exact card_join_dvd_mul _ _
  have c₁' : Nat.Coprime p (Nat.card (N₁.subgroupOf H)) := e₁ ▸ c₁
  have c₂' : Nat.Coprime p (Nat.card (N₂.subgroupOf H)) := e₂ ▸ c₂
  rw [e₀]
  exact Nat.Coprime.coprime_dvd_right hdvd (Nat.Coprime.mul_right c₁' c₂')

private theorem directedOn_normal_coprime (H : Subgroup G) :
    DirectedOn (· ≤ ·)
      {N : Subgroup G | N ≤ H ∧ (N.subgroupOf H).Normal ∧ Nat.Coprime p (Nat.card N)} := by
  rintro N₁ ⟨h₁, hn₁, c₁⟩ N₂ ⟨h₂, hn₂, c₂⟩
  refine ⟨N₁ ⊔ N₂, ⟨sup_le h₁ h₂, ?_, coprime_card_join h₁ h₂ hn₂ c₁ c₂⟩, le_sup_left, le_sup_right⟩
  rw [Subgroup.subgroupOf_sup h₁ h₂]
  infer_instance

private theorem mem_relPPrimeCore_iff {H : Subgroup G} {x : G} :
    x ∈ relPPrimeCore p H ↔
      ∃ N : Subgroup G, (N ≤ H ∧ (N.subgroupOf H).Normal ∧ Nat.Coprime p (Nat.card N)) ∧ x ∈ N := by
  have hne : {N : Subgroup G | N ≤ H ∧ (N.subgroupOf H).Normal ∧ Nat.Coprime p (Nat.card N)}.Nonempty :=
    ⟨⊥, bot_le, inferInstance, by rw [Subgroup.card_bot]; exact Nat.coprime_one_right p⟩
  unfold relPPrimeCore
  exact Subgroup.mem_sSup_of_directedOn hne (directedOn_normal_coprime H)

theorem relPPrimeCore_conj_mem {H : Subgroup G} {x : G} (hx : x ∈ relPPrimeCore p H) {h : G}
    (hh : h ∈ H) : h * x * h⁻¹ ∈ relPPrimeCore p H := by
  obtain ⟨N, ⟨hNH, hNn, hNc⟩, hxN⟩ := mem_relPPrimeCore_iff.1 hx
  refine mem_relPPrimeCore_iff.2 ⟨N, ⟨hNH, hNn, hNc⟩, ?_⟩
  have hxH : x ∈ H := hNH hxN
  have hc : (⟨h, hh⟩ : H) * ⟨x, hxH⟩ * (⟨h, hh⟩ : H)⁻¹ ∈ N.subgroupOf H :=
    hNn.conj_mem ⟨x, hxH⟩ (Subgroup.mem_subgroupOf.2 hxN) ⟨h, hh⟩
  exact Subgroup.mem_subgroupOf.1 hc

theorem coprime_orderOf_of_mem_relPPrimeCore {H : Subgroup G} {x : G}
    (hx : x ∈ relPPrimeCore p H) : Nat.Coprime p (orderOf x) := by
  obtain ⟨N, ⟨-, -, hNc⟩, hxN⟩ := mem_relPPrimeCore_iff.1 hx
  have hdvd : orderOf (⟨x, hxN⟩ : N) ∣ Nat.card N := orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk] at hdvd
  exact Nat.Coprime.coprime_dvd_right hdvd hNc

theorem false_of_inverted_mem_relPPrimeCore (hp : p.Prime) (hp2 : p ≠ 2) {H : Subgroup G}
    {t y : G} (ht : t ∈ relPPrimeCore p H) (ht2 : t ^ 2 = 1) (hy : y ∈ H) (hyp : y ^ p = 1)
    (hy1 : y ≠ 1) (hty : t * y * t⁻¹ = y⁻¹) : False := by
  haveI := Fact.mk hp
  have ht_inv : t⁻¹ = t := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact ht2)
  have hprod : t * (y * t * y⁻¹) ∈ relPPrimeCore p H :=
    (relPPrimeCore p H).mul_mem ht (relPPrimeCore_conj_mem ht hy)
  have hz : t * (y * t * y⁻¹) = y⁻¹ * y⁻¹ := by
    calc t * (y * t * y⁻¹) = t * y * t⁻¹ * y⁻¹ := by
          rw [ht_inv]; simp only [mul_assoc]
      _ = y⁻¹ * y⁻¹ := by rw [hty]
  rw [hz] at hprod
  have hord := coprime_orderOf_of_mem_relPPrimeCore hprod
  have hyord : orderOf y = p := orderOf_eq_prime hyp hy1
  have hcop : Nat.Coprime (orderOf y⁻¹) 2 := by
    rw [orderOf_inv, hyord]
    exact (Nat.coprime_primes hp Nat.prime_two).2 hp2
  have hsq : orderOf (y⁻¹ * y⁻¹) = p := by
    rw [← sq, Nat.Coprime.orderOf_pow hcop, orderOf_inv, hyord]
  rw [hsq] at hord
  exact hp.one_lt.ne' ((Nat.coprime_self p).1 hord)

theorem eq_bot_of_forall_inverted (hp : p.Prime) (hp2 : p ≠ 2) {H S : Subgroup G}
    (hSH : S ≤ H) (hS : S ≤ relPPrimeCore p H) (hS2 : IsPGroup 2 S)
    (hinv : ∀ t ∈ H, t ^ 2 = 1 → t ≠ 1 →
      ∃ y ∈ H, y ^ p = 1 ∧ y ≠ 1 ∧ t * y * t⁻¹ = y⁻¹) : S = ⊥ := by
  by_contra hne
  have hgt : 1 < Nat.card S := (Subgroup.one_lt_card_iff_ne_bot (H := S)).2 hne
  have h2 : 2 ∣ Nat.card S := by
    rcases hS2.card_eq_or_dvd with h | h
    · omega
    · exact h
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have ht2 : (g : G) ^ 2 = 1 := by
    have h := pow_orderOf_eq_one g
    rw [hg] at h
    simpa using congrArg Subtype.val h
  have ht1 : (g : G) ≠ 1 := by
    intro h1
    have hg1 : g = 1 := Subtype.ext (by simpa using h1)
    rw [hg1, orderOf_one] at hg
    omega
  obtain ⟨y, hyH, hyp, hy1, hty⟩ := hinv (g : G) (hSH g.2) ht2 ht1
  exact false_of_inverted_mem_relPPrimeCore hp hp2 (hS g.2) ht2 hyH hyp hy1 hty

end RelPPrimeCore

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
