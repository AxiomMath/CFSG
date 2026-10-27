module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCorePOuter
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.EscapingCaseOneComponent

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open CFSG.Open

theorem twoRank_le_one_of_unique {G : Type} [Group G] [Finite G] {e : G} {R : Subgroup G}
    (hR : ∀ x ∈ R, orderOf x = 2 → x = e) : twoRank R ≤ 1 := by
  rw [twoRank, ← CFSG.RankThreeCoreUniqueness.Helpers.pRank_subgroup_eq_internal_top 2
    (by decide)]
  by_contra hlt
  obtain ⟨a, haR, b, hbR, ha, hb, hab, -⟩ :=
    CFSG.ProperTwoGeneratedCore.Assembly.exists_commuting_involutions_of_two_le_pRank (K := R)
      (by omega)
  exact hab ((hR a haR ha).trans (hR b hbR hb).symm)

theorem card_quaternionGroup_two_pow {n : ℕ} (hn : 3 ≤ n) :
    Nat.card (QuaternionGroup (2 ^ (n - 2))) = 2 ^ n := by
  have : NeZero (2 ^ (n - 2)) := ⟨by positivity⟩
  rw [Nat.card_eq_fintype_card, QuaternionGroup.card,
    show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
  congr 1
  omega

namespace PartC

variable {G : Type} [Group G] {T Q P₁ : Subgroup G} {e u y : G}

theorem self_ne (hc : PartC T Q P₁ e u) : u ≠ 1 ∧ u ≠ e := by
  refine ⟨fun h => hc.centralElt_ne_one ?_, fun h => hc.centralElt_ne_one ?_⟩
  · rw [← hc.sq, h, mul_one]
  · have h2 := hc.sq
    rw [h] at h2
    exact mul_eq_left.mp h2

theorem eq_of_mem_right_of_mul_self (hc : PartC T Q P₁ e u) {p : G} (hp : p ∈ P₁)
    (hpp : p * p = 1) : p = 1 ∨ p = e := by
  by_cases hp1 : p = 1
  · exact Or.inl hp1
  · exact Or.inr (hc.unique p hp (orderOf_eq_prime (by rw [pow_two]; exact hpp) hp1))

theorem exists_mul_self_of_comm (hc : PartC T Q P₁ e u)
    (hcomm : ∀ p ∈ P₁, ∀ p' ∈ P₁, p * p' = p' * p) {t : G} (htT : t ∈ T)
    (ht : orderOf t = 2) (hte : t ≠ e) : ∃ q ∈ Q, t = q * u := by
  obtain ⟨φ⟩ := hc.quaternion
  obtain ⟨q, hq, p, hp, rfl⟩ := hc.mem_sup_iff.mp (hc.involution_mem t htT ht)
  have htt : q * p * (q * p) = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  have hqp : q * q * (p * p) = 1 := by
    rw [← htt, show q * p * (q * p) = q * (p * q) * p by group, ← hc.commute q hq p hp]
    group
  have ht1 : q * p ≠ 1 := fun h => by rw [h, orderOf_one] at ht; exact absurd ht (by decide)
  rcases quaternion_mul_self φ hc.mem_left hc.order hq with hqq | hqq
  · exfalso
    rw [hqq, one_mul] at hqp
    rcases quaternion_eq_of_mul_self φ hc.mem_left hc.order hq hqq with h1 | h1 <;>
      rcases hc.eq_of_mem_right_of_mul_self hp hqp with h2 | h2 <;> rw [h1, h2] at ht1 hte
    · exact ht1 (mul_one 1)
    · exact hte (one_mul e)
    · exact hte (mul_one e)
    · exact ht1 hc.centralElt_mul_self
  · rw [hqq] at hqp
    have hpp : p * p = e := by
      calc p * p = e⁻¹ * (e * (p * p)) := by group
        _ = e := by rw [hqp, mul_one, hc.centralElt_inv]
    have hpu : p * u⁻¹ * (p * u⁻¹) = 1 := by
      rw [show p * u⁻¹ * (p * u⁻¹) = p * (u⁻¹ * p) * u⁻¹ by group,
        ← hcomm p hp u⁻¹ (P₁.inv_mem hc.self_mem),
        show p * (p * u⁻¹) * u⁻¹ = p * p * (u * u)⁻¹ by group, hpp, hc.sq, mul_inv_cancel]
    rcases hc.eq_of_mem_right_of_mul_self (P₁.mul_mem hp (P₁.inv_mem hc.self_mem)) hpu with
      h | h
    · rw [mul_inv_eq_one] at h
      exact ⟨q, hq, by rw [h]⟩
    · rw [mul_inv_eq_iff_eq_mul] at h
      refine ⟨q * e, Q.mul_mem hq hc.mem_left, ?_⟩
      rw [h, mul_assoc]

theorem pRank_le_two_of_comm [Finite G] (hc : PartC T Q P₁ e u)
    (hcomm : ∀ p ∈ P₁, ∀ p' ∈ P₁, p * p' = p' * p) : CFSG.Open.pRank 2 T ≤ 2 := by
  refine CFSG.SectionRank.pRank_le (by decide) fun E hET hE => ?_
  have hsq : ∀ x ∈ E, x * x = 1 := fun x hx => by rw [← pow_two]; exact hE.2 x hx
  have hinv : ∀ x ∈ E, x ≠ 1 → x ≠ e → ∃ q ∈ Q, x = q * u := fun x hx hx1 hxe =>
    hc.exists_mul_self_of_comm hcomm (hET hx)
      (orderOf_eq_prime (by rw [pow_two]; exact hsq x hx) hx1) hxe
  have hcard : ∀ s : Set G, (E : Set G) ⊆ s → s.ncard ≤ 4 → Nat.card E ≤ 2 ^ 2 := fun s hs h4 =>
    (Set.ncard_le_ncard hs (Set.toFinite s)).trans h4
  by_cases hall : ∀ x ∈ E, x = 1 ∨ x = e
  · refine hcard {1, e} (fun x hx => hall x hx) ?_
    exact (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton]; norm_num)
  push Not at hall
  obtain ⟨a, haE, ha1, hae⟩ := hall
  obtain ⟨q₁, hq₁, rfl⟩ := hinv a haE ha1 hae
  refine hcard {1, e, q₁ * u, q₁ * u * e} (fun b hbE => ?_) ?_
  · by_cases hb : b = 1 ∨ b = e
    · rcases hb with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
    push Not at hb
    obtain ⟨q₂, hq₂, rfl⟩ := hinv _ hbE hb.1 hb.2
    have hab : q₁ * u * (q₂ * u) = q₁ * q₂ * e := by
      rw [← hc.sq, show q₁ * u * (q₂ * u) = q₁ * (u * q₂) * u by group,
        ← hc.commute q₂ hq₂ u hc.self_mem]
      group
    have habE : q₁ * u * (q₂ * u) ∈ E := E.mul_mem haE hbE
    have habQ : q₁ * u * (q₂ * u) ∈ Q := by
      rw [hab]
      exact Q.mul_mem (Q.mul_mem hq₁ hq₂) hc.mem_left
    have hab' : q₁ * u * (q₂ * u) = 1 ∨ q₁ * u * (q₂ * u) = e := by
      by_contra hne
      push Not at hne
      obtain ⟨q₃, hq₃, h3⟩ := hinv _ habE hne.1 hne.2
      have huQ : u ∈ Q := by
        rw [show u = q₃⁻¹ * (q₁ * u * (q₂ * u)) by rw [h3]; group]
        exact Q.mul_mem (Q.inv_mem hq₃) habQ
      rcases hc.mem_inf u huQ hc.self_mem with h | h
      · exact hc.self_ne.1 h
      · exact hc.self_ne.2 h
    have haa : q₁ * u * (q₁ * u) = 1 := hsq _ haE
    have hainv : (q₁ * u)⁻¹ = q₁ * u := inv_eq_of_mul_eq_one_right haa
    rcases hab' with h | h
    · refine Or.inr (Or.inr (Or.inl ?_))
      rw [← hainv]
      exact eq_inv_of_mul_eq_one_right h
    · refine Or.inr (Or.inr (Or.inr ?_))
      change _ = q₁ * u * e
      calc q₂ * u = (q₁ * u)⁻¹ * (q₁ * u * (q₂ * u)) := by group
        _ = q₁ * u * e := by rw [h, hainv]
  · calc ({1, e, q₁ * u, q₁ * u * e} : Set G).ncard
        ≤ ({e, q₁ * u, q₁ * u * e} : Set G).ncard + 1 := Set.ncard_insert_le _ _
      _ ≤ ({q₁ * u, q₁ * u * e} : Set G).ncard + 1 + 1 := by
        gcongr
        exact Set.ncard_insert_le _ _
      _ ≤ ({q₁ * u * e} : Set G).ncard + 1 + 1 + 1 := by
        gcongr
        exact Set.ncard_insert_le _ _
      _ = 4 := by rw [Set.ncard_singleton]

theorem exists_not_comm [Finite G] (hc : PartC T Q P₁ e u)
    (hrank : 3 ≤ CFSG.Open.pRank 2 T) : ∃ p ∈ P₁, ∃ p' ∈ P₁, p * p' ≠ p' * p := by
  by_contra h
  push Not at h
  have := hc.pRank_le_two_of_comm h
  omega

theorem quaternion_of_unique [Finite G] (hc : PartC T Q P₁ e u) {R : Subgroup G} (hRT : R ≤ T)
    (hR : ∀ x ∈ R, orderOf x = 2 → x = e) (hRc : ¬ IsCyclic R) :
    ∃ n, 3 ≤ n ∧ Nat.card R = 2 ^ n ∧ Nonempty (R ≃* QuaternionGroup (2 ^ (n - 2))) := by
  rcases CFSG.TwoRankLowerBound.Helpers.rank_one_two_group_cyclic_or_quaternion R
      (hc.isPGroup.to_le hRT) (twoRank_le_one_of_unique hR) with h | ⟨n, hn, ⟨φ⟩⟩
  · exact absurd h hRc
  · exact ⟨n, hn, by rw [Nat.card_congr φ.toEquiv, card_quaternionGroup_two_pow hn], ⟨φ⟩⟩

theorem right_cyclic_or_quaternion [Finite G] (hc : PartC T Q P₁ e u) :
    IsCyclic P₁ ∨ ∃ n, 3 ≤ n ∧ Nonempty (P₁ ≃* QuaternionGroup (2 ^ (n - 2))) :=
  CFSG.TwoRankLowerBound.Helpers.rank_one_two_group_cyclic_or_quaternion P₁
    (hc.isPGroup.to_le hc.right_le) (twoRank_le_one_of_unique hc.unique)

theorem not_isCyclic_right [Finite G] (hc : PartC T Q P₁ e u)
    (hrank : 3 ≤ CFSG.Open.pRank 2 T) : ¬ IsCyclic P₁ := fun hcyc => by
  obtain ⟨p, hp, p', hp', hne⟩ := hc.exists_not_comm hrank
  let : CommGroup P₁ := IsCyclic.commGroup
  exact hne (congrArg Subtype.val (mul_comm (⟨p, hp⟩ : P₁) ⟨p', hp'⟩))

theorem index_le_two (hc : PartC T Q P₁ e u) : ((Q ⊔ P₁).subgroupOf T).index ≤ 2 := by
  by_cases hT : T ≤ Q ⊔ P₁
  · rw [Subgroup.subgroupOf_eq_top.mpr hT, Subgroup.index_top]
    omega
  · obtain ⟨y, hyT, hy⟩ := Set.not_subset.mp hT
    refine le_of_eq (Subgroup.index_eq_two_iff.mpr ⟨⟨y, hyT⟩, fun b => ?_⟩)
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
    by_cases hb : (b : G) ∈ Q ⊔ P₁
    · exact Or.inr ⟨hb, fun h => hy (by simpa using (Q ⊔ P₁).mul_mem ((Q ⊔ P₁).inv_mem hb) h)⟩
    · refine Or.inl ⟨?_, hb⟩
      have h := hc.inv_mul_mem (b : G)⁻¹ (T.inv_mem b.2) y hyT
        (fun h => hb (by simpa using (Q ⊔ P₁).inv_mem h)) hy
      rwa [inv_inv] at h

theorem right_quaternion [Finite G] (hc : PartC T Q P₁ e u)
    (hrank : 3 ≤ CFSG.Open.pRank 2 T) :
    ∃ n, 3 ≤ n ∧ Nat.card P₁ = 2 ^ n ∧ Nonempty (P₁ ≃* QuaternionGroup (2 ^ (n - 2))) :=
  hc.quaternion_of_unique hc.right_le hc.unique (hc.not_isCyclic_right hrank)

theorem sup_zpowers_quaternion [Finite G] (hc : PartC T Q P₁ e u)
    (hrank : 3 ≤ CFSG.Open.pRank 2 T) (hyT : y ∈ T) (hy : y ∉ Q ⊔ P₁) (hyy : y * y ∈ P₁) :
    ∃ n, 3 ≤ n ∧ Nat.card P₁ = 2 ^ n ∧ Nonempty (P₁ ≃* QuaternionGroup (2 ^ (n - 2))) ∧
      Nat.card (P₁ ⊔ Subgroup.zpowers y : Subgroup G) = 2 ^ (n + 1) ∧
      Nonempty ((P₁ ⊔ Subgroup.zpowers y : Subgroup G) ≃* QuaternionGroup (2 ^ (n + 1 - 2))) := by
  obtain ⟨n, hn, hcard, hφ⟩ := hc.right_quaternion hrank
  have hcardP : Nat.card (P₁ ⊔ Subgroup.zpowers y : Subgroup G) = 2 ^ (n + 1) := by
    rw [hc.card_sup_zpowers hyT hy hyy, hcard, pow_succ, mul_comm]
  refine ⟨n, hn, hcard, hφ, hcardP, ?_⟩
  have hPc : ¬ IsCyclic (P₁ ⊔ Subgroup.zpowers y : Subgroup G) := fun hcyc => by
    obtain ⟨p, hp, p', hp', hne⟩ := hc.exists_not_comm hrank
    let : CommGroup (P₁ ⊔ Subgroup.zpowers y : Subgroup G) := IsCyclic.commGroup
    exact hne (congrArg Subtype.val (mul_comm
      (⟨p, Subgroup.mem_sup_left hp⟩ : (P₁ ⊔ Subgroup.zpowers y : Subgroup G))
      ⟨p', Subgroup.mem_sup_left hp'⟩))
  obtain ⟨m, hm, hcardm, hψ⟩ := hc.quaternion_of_unique (hc.sup_zpowers_le hyT)
    (fun x hx hx2 => hc.eq_of_mem_sup_zpowers hyT hy hyy hx hx2) hPc
  have hmn : m = n + 1 := by
    rw [hcardP] at hcardm
    exact (Nat.pow_right_injective (le_refl 2) hcardm).symm
  subst hmn
  exact hψ

theorem cases [Finite G] (hc : PartC T Q P₁ e u) (hrank : 3 ≤ CFSG.Open.pRank 2 T) :
    (T = Q ⊔ P₁ ∧ ∃ n, 4 ≤ n ∧ Nat.card P₁ = 2 ^ n ∧
      Nonempty (P₁ ≃* QuaternionGroup (2 ^ (n - 2)))) ∨
    (T = Q ⊔ P₁ ∧ Nonempty (P₁ ≃* QuaternionGroup 2)) ∨
    (∃ y ∈ T, y ∉ Q ⊔ P₁ ∧ y * y ∈ P₁ ∧ ∃ n, 5 ≤ n ∧
      Nat.card (P₁ ⊔ Subgroup.zpowers y : Subgroup G) = 2 ^ n ∧
      Nonempty ((P₁ ⊔ Subgroup.zpowers y : Subgroup G) ≃* QuaternionGroup (2 ^ (n - 2)))) ∨
    (∃ y ∈ T, y ∉ Q ⊔ P₁ ∧ y * y ∈ P₁ ∧
      Nat.card (P₁ ⊔ Subgroup.zpowers y : Subgroup G) = 16 ∧
      Nonempty ((P₁ ⊔ Subgroup.zpowers y : Subgroup G) ≃* QuaternionGroup 4) ∧
      Nonempty (P₁ ≃* QuaternionGroup 2)) := by
  by_cases hT : T ≤ Q ⊔ P₁
  · have hTeq : T = Q ⊔ P₁ := le_antisymm hT hc.sup_le
    obtain ⟨n, hn, hcard, hφ⟩ := hc.right_quaternion hrank
    rcases Nat.lt_or_ge n 4 with h4 | h4
    · obtain rfl : n = 3 := by omega
      exact Or.inr (Or.inl ⟨hTeq, hφ⟩)
    · exact Or.inl ⟨hTeq, n, h4, hcard, hφ⟩
  · obtain ⟨y, hyT, hy, hyy⟩ := hc.exists_mul_self_mem hT
    obtain ⟨n, hn, -, hφ, hcardP, hψ⟩ := hc.sup_zpowers_quaternion hrank hyT hy hyy
    rcases Nat.lt_or_ge n 4 with h4 | h4
    · obtain rfl : n = 3 := by omega
      exact Or.inr (Or.inr (Or.inr ⟨y, hyT, hy, hyy, hcardP, hψ, hφ⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨y, hyT, hy, hyy, n + 1, by omega, hcardP, hψ⟩))

end PartC

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
