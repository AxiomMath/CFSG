module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.ThetaCore

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Coordinator

open CFSG.RankThree.LocalRank Subgroup

variable {G : Type*} [Group G]

theorem exists_zpow_mul_of_mem_sup {x : G} {K : Subgroup G} (hK : ∀ k ∈ K, k * x = x * k)
    {c : G} (hc : c ∈ zpowers x ⊔ K) : ∃ i : ℤ, ∃ k ∈ K, c = x ^ i * k := by
  rw [sup_eq_closure] at hc
  induction hc using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with hy | hy
    · obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hy
      exact ⟨i, 1, K.one_mem, by rw [mul_one]⟩
    · exact ⟨0, y, hy, by rw [zpow_zero, one_mul]⟩
  | one => exact ⟨0, 1, K.one_mem, by rw [zpow_zero, one_mul]⟩
  | mul y z _ _ ihy ihz =>
    obtain ⟨i, k, hk, rfl⟩ := ihy
    obtain ⟨j, l, hl, rfl⟩ := ihz
    refine ⟨i + j, k * l, K.mul_mem hk hl, ?_⟩
    have hc : Commute k (x ^ j) := ((Commute.zpow_right (hK k hk) j))
    rw [zpow_add, mul_assoc, ← mul_assoc k, hc.eq, mul_assoc, mul_assoc]
  | inv y _ ihy =>
    obtain ⟨i, k, hk, rfl⟩ := ihy
    refine ⟨-i, k⁻¹, K.inv_mem hk, ?_⟩
    have hc : Commute k⁻¹ (x ^ (-i)) := (Commute.zpow_right (hK k⁻¹ (K.inv_mem hk)) (-i))
    rw [mul_inv_rev, ← zpow_neg, hc.eq]

theorem aschbacherSolvableCore_eq_bot_of_simple_complement [Finite G] {x : G} (hx3 : x ^ 3 = 1)
    {K : Subgroup G} (hK : K ≤ centralizer ({x} : Set G))
    (hsup : zpowers x ⊔ K = centralizer ({x} : Set G)) [IsSimpleGroup K]
    (hnc : ∃ a b : K, a * b ≠ b * a) :
    aschbacherSolvableCore 3 (centralizer ({x} : Set G)) = ⊥ := by
  set C := centralizer ({x} : Set G) with hC
  set N := thetaOf x with hN
  have hKx : ∀ k ∈ K, k * x = x * k := fun k hk => mem_centralizer_singleton_iff.mp (hK hk)
  have hdec : ∀ c ∈ C, ∃ i : ℤ, ∃ k ∈ K, c = x ^ i * k := fun c hc =>
    exists_zpow_mul_of_mem_sup hKx (hsup ▸ hc)
  have hKn : ∀ c ∈ C, ∀ k ∈ K, c * k * c⁻¹ ∈ K := by
    intro c hc k hk
    obtain ⟨i, k₀, hk₀, rfl⟩ := hdec c hc
    have hc' : Commute (x ^ i) (k₀ * k * k₀⁻¹) :=
      (Commute.zpow_left (hKx _ (K.mul_mem (K.mul_mem hk₀ hk) (K.inv_mem hk₀))).symm i)
    have : x ^ i * k₀ * k * (x ^ i * k₀)⁻¹ = k₀ * k * k₀⁻¹ := by
      rw [mul_inv_rev, show x ^ i * k₀ * k * (k₀⁻¹ * (x ^ i)⁻¹) =
        x ^ i * (k₀ * k * k₀⁻¹) * (x ^ i)⁻¹ by group, hc'.eq, mul_inv_cancel_right]
    rw [this]
    exact K.mul_mem (K.mul_mem hk₀ hk) (K.inv_mem hk₀)
  have hNK : ∀ k ∈ K, k ∈ N → k = 1 := by
    set M : Subgroup K := N.subgroupOf K with hM
    have hMn : M.Normal := by
      refine ⟨fun m hm g => ?_⟩
      rw [hM, mem_subgroupOf] at hm ⊢
      exact thetaOf_conj (hK g.2) hm
    have hMs : Group.IsSolvable M := by
      have := thetaOf_isSolvable x
      let f : M →* N :=
        { toFun := fun m => ⟨((m : K) : G), m.2⟩
          map_one' := rfl
          map_mul' := fun _ _ => rfl }
      exact Group.isSolvable_of_isSolvable_injective (f := f)
        (fun a b h => by
          have h1 := congrArg Subtype.val h
          exact Subtype.ext (Subtype.ext h1))
    rcases hMn.eq_bot_or_eq_top with hbot | htop
    · intro k hk hkN
      have : (⟨k, hk⟩ : K) ∈ M := mem_subgroupOf.mpr hkN
      rw [hbot, mem_bot] at this
      exact congrArg Subtype.val this
    · exfalso
      have hKs : Group.IsSolvable K := by
        have : Group.IsSolvable (⊤ : Subgroup K) := htop ▸ hMs
        exact Group.isSolvable_of_surjective (f := (⊤ : Subgroup K).subtype)
          (fun k => ⟨⟨k, mem_top k⟩, rfl⟩)
      obtain ⟨a, b, hab⟩ := hnc
      exact hab ((IsSimpleGroup.comm_iff_isSolvable.mpr hKs) a b)
  have hNcomm : ∀ n ∈ N, ∀ k ∈ K, n * k = k * n := by
    intro n hn k hk
    have hnC : n ∈ C := thetaOf_le x hn
    have h1 : n * k * n⁻¹ * k⁻¹ ∈ K := K.mul_mem (hKn n hnC k hk) (K.inv_mem hk)
    have h2 : n * k * n⁻¹ * k⁻¹ ∈ N := by
      have := N.mul_mem hn (thetaOf_conj (hK hk) (N.inv_mem hn))
      rwa [show n * (k * n⁻¹ * k⁻¹) = n * k * n⁻¹ * k⁻¹ by group] at this
    have h3 := hNK _ h1 h2
    calc n * k = n * k * n⁻¹ * k⁻¹ * (k * n) := by group
      _ = k * n := by rw [h3, one_mul]
  have hNx : ∀ n ∈ N, n ^ 3 = 1 := by
    intro n hn
    obtain ⟨i, k, hk, rfl⟩ := hdec n (thetaOf_le x hn)
    have hkZ : (⟨k, hk⟩ : K) ∈ center K := by
      rw [mem_center_iff]
      intro l
      apply Subtype.ext
      have h := hNcomm _ hn l.1 l.2
      have hl : Commute (x ^ i) l.1 := (Commute.zpow_left (hKx l.1 l.2).symm i)
      change l.1 * k = k * l.1
      have : x ^ i * (k * l.1) = x ^ i * (l.1 * k) := by
        calc x ^ i * (k * l.1) = x ^ i * k * l.1 := by rw [mul_assoc]
          _ = l.1 * (x ^ i * k) := h
          _ = x ^ i * (l.1 * k) := by rw [← mul_assoc, ← hl.eq, mul_assoc]
      exact (mul_left_cancel this).symm
    have hcen : center K = ⊥ := by
      rcases (inferInstance : (center K).Normal).eq_bot_or_eq_top with h | h
      · exact h
      · exfalso
        obtain ⟨a, b, hab⟩ := hnc
        exact hab ((mem_center_iff.mp (h ▸ mem_top b)) a)
    rw [hcen, mem_bot] at hkZ
    have hk1 : k = 1 := congrArg Subtype.val hkZ
    rw [hk1, mul_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx3, one_zpow]
  have hNbot : N = ⊥ := by
    rw [eq_bot_iff]
    intro n hn
    rw [mem_bot]
    by_contra hn1
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hord : orderOf (⟨n, hn⟩ : N) = 3 := by
      rw [Subgroup.orderOf_mk]
      exact orderOf_eq_prime (hNx n hn) hn1
    exact thetaOf_not_three_dvd x (hord ▸ orderOf_dvd_natCard _)
  rw [hN, thetaOf] at hNbot
  exact (Subgroup.map_eq_bot_iff_of_injective _ (centralizer ({x} : Set G)).subtype_injective).mp
    hNbot

theorem exists_mul_ne_of_isSimpleGroup {H : Type*} [Group H] [Finite H] [IsSimpleGroup H] {n : ℕ}
    (h : Nat.card H = n) (h2 : 2 ∣ n) (hn : n ≠ 2) : ∃ a b : H, a * b ≠ b * a := by
  by_contra hc
  push Not at hc
  have := Fact.mk Nat.prime_two
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := H) 2 (by rw [h]; exact h2)
  have hnorm : (zpowers g).Normal := by
    constructor
    intro m _ x
    rwa [hc x m, mul_inv_cancel_right]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (zpowers g) with hb | ht
  · rw [zpowers_eq_bot] at hb
    rw [hb, orderOf_one] at hg
    exact absurd hg (by norm_num)
  · have := congrArg (fun K : Subgroup H => Nat.card K) ht
    simp only [Nat.card_zpowers, hg, card_top, h] at this
    exact hn this.symm

end CFSG.AGLEmbeddingD2.Wilson.Coordinator
