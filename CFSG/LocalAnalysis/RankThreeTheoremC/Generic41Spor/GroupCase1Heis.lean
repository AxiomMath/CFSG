module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerRank
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.Glauberman281.Corollary
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.Glauberman281.Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open Subgroup CFSG.LocalAnalysis.RankThreeTheoremC.Glauberman281

variable {G : Type} [Group G] [Finite G]

theorem exists_elemAbelian_ge_of_le_pRank_gen {p : ℕ} {Q : Subgroup G} {k : ℕ} (hp : 1 < p) (hk : 0 < k)
    (h : k ≤ CFSG.Open.pRank p Q) :
    ∃ E : Subgroup G, E ≤ Q ∧ IsElemAbelian p E ∧ ∃ j : ℕ, k ≤ j ∧ Nat.card E = p ^ j := by
  set S : Set ℕ := {j | ∃ E : Subgroup G, E ≤ Q ∧ IsElemAbelian p E ∧ Nat.card E = p ^ j} with hS
  have hbdd : BddAbove S := by
    refine ⟨Nat.card G, ?_⟩
    rintro n ⟨F, -, -, hF⟩
    have h1 : n < p ^ n := Nat.lt_pow_self hp
    have h2 : Nat.card F ≤ Nat.card G := Subgroup.card_le_card_group F
    omega
  have hne : S.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    have : CFSG.Open.pRank p Q = 0 := by
      unfold CFSG.Open.pRank
      rw [← hS, hne]
      simp
    omega
  obtain ⟨E, hEQ, hEel, hEc⟩ := Nat.sSup_mem hne hbdd
  exact ⟨E, hEQ, hEel, _, h, hEc⟩

theorem exists_mul_zpow_of_mem_sup {T : Subgroup G} {x : G} (hxT : ∀ t ∈ T, x * t = t * x) :
    ∀ v ∈ T ⊔ zpowers x, ∃ t ∈ T, ∃ k : ℤ, v = t * x ^ k := by
  let D : Subgroup G :=
    { carrier := {v | ∃ t ∈ T, ∃ k : ℤ, v = t * x ^ k}
      mul_mem' := by
        rintro _ _ ⟨t, ht, k, rfl⟩ ⟨t', ht', l, rfl⟩
        have hc : Commute (x ^ k) t' := Commute.zpow_left (hxT t' ht' : Commute x t') k
        refine ⟨t * t', T.mul_mem ht ht', k + l, ?_⟩
        calc t * x ^ k * (t' * x ^ l) = t * (x ^ k * t') * x ^ l := by simp only [mul_assoc]
          _ = t * (t' * x ^ k) * x ^ l := by rw [hc.eq]
          _ = t * t' * (x ^ k * x ^ l) := by simp only [mul_assoc]
          _ = t * t' * x ^ (k + l) := by rw [zpow_add]
      one_mem' := ⟨1, T.one_mem, 0, by simp⟩
      inv_mem' := by
        rintro _ ⟨t, ht, k, rfl⟩
        have hxt : Commute x t := hxT t ht
        have hc : Commute x t⁻¹ := hxt.inv_right
        refine ⟨t⁻¹, T.inv_mem ht, -k, ?_⟩
        calc (t * x ^ k)⁻¹ = (x ^ k)⁻¹ * t⁻¹ := mul_inv_rev _ _
          _ = x ^ (-k) * t⁻¹ := by rw [zpow_neg]
          _ = t⁻¹ * x ^ (-k) := (Commute.zpow_left hc (-k)).eq }
  have hTD : T ≤ D := fun t ht => ⟨t, ht, 0, by simp⟩
  have hxD : zpowers x ≤ D := by
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact ⟨1, T.one_mem, k, by simp⟩
  exact fun v hv => (sup_le hTD hxD) hv

theorem three_le_pRank_of_mul_heis {p : ℕ} (hp : p.Prime) {T A B S : Subgroup G} {x : G}
    (hSdef : S = T ⊔ zpowers x) (hTe : ∀ t ∈ T, t ^ p = 1) (hTc : ¬ IsCyclic T)
    (hxp : x ^ p = 1) (hx1 : x ≠ 1) (hxcT : ∀ t ∈ T, x * t = t * x) (hxT : x ∉ T)
    (hAS : A ≤ S) (hBS : B ≤ S) (hxA : x ∈ A) (hxB : x ∈ B)
    (hAB : ∀ s ∈ S, ∃ a ∈ A, ∃ b ∈ B, s = a * b) (hint : A ⊓ B ⊓ T ≠ ⊥) :
    3 ≤ CFSG.Open.pRank p A ∨ 3 ≤ CFSG.Open.pRank p B := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hTS : T ≤ S := hSdef ▸ le_sup_left
  have hxS : x ∈ S := hSdef ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have hdec : ∀ s ∈ S, ∃ t ∈ T, ∃ k : ℤ, s = t * x ^ k := by
    intro s hs
    exact exists_mul_zpow_of_mem_sup hxcT s (hSdef ▸ hs)
  have hTx : ∀ k : ℤ, x ^ k ∈ T → x ^ k = 1 := by
    intro k hk
    have hcard : Nat.card (zpowers x) = p := by
      rw [Nat.card_zpowers, orderOf_eq_prime hxp hx1]
    by_contra hne
    apply hxT
    have hord : orderOf (x ^ k) = p := by
      have h1 : orderOf (x ^ k) ∣ p := by
        apply orderOf_dvd_of_pow_eq_one
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hxp, one_zpow]
      rcases (Nat.dvd_prime hp).1 h1 with h | h
      · exact absurd (orderOf_eq_one_iff.1 h) hne
      · exact h
    have hle : zpowers (x ^ k) ≤ T := Subgroup.zpowers_le.2 hk
    have heq : zpowers (x ^ k) = zpowers x := by
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 ?_) ?_
      · exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers x) k
      · simp only [Nat.card_zpowers]
        rw [hord, orderOf_eq_prime hxp hx1]
    have : x ∈ zpowers (x ^ k) := by rw [heq]; exact Subgroup.mem_zpowers x
    exact hle this
  set A' : Subgroup G := A ⊓ T with hA'
  set B' : Subgroup G := B ⊓ T with hB'
  have hA'T : A' ≤ T := inf_le_right
  have hB'T : B' ≤ T := inf_le_right
  have hTAB : ∀ t ∈ T, ∃ a ∈ A', ∃ b ∈ B', t = a * b := by
    intro t ht
    obtain ⟨a, ha, b, hb, hab⟩ := hAB t (hTS ht)
    obtain ⟨a₁, ha₁, i, rfl⟩ := hdec a (hAS ha)
    obtain ⟨b₁, hb₁, j, rfl⟩ := hdec b (hBS hb)
    have hxiA : x ^ i ∈ A := Subgroup.zpow_mem _ hxA i
    have hxjB : x ^ j ∈ B := Subgroup.zpow_mem _ hxB j
    have ha₁A : a₁ ∈ A := by
      have := A.mul_mem ha (A.inv_mem hxiA)
      simpa [mul_assoc] using this
    have hb₁B : b₁ ∈ B := by
      have := B.mul_mem hb (B.inv_mem hxjB)
      simpa [mul_assoc] using this
    have hcomm : x ^ i * b₁ = b₁ * x ^ i :=
      (Commute.zpow_left (hxcT b₁ hb₁ : Commute x b₁) i).eq
    have h2 : t = (a₁ * b₁) * x ^ (i + j) := by
      rw [hab, zpow_add]
      calc a₁ * x ^ i * (b₁ * x ^ j) = a₁ * (x ^ i * b₁) * x ^ j := by simp only [mul_assoc]
        _ = a₁ * (b₁ * x ^ i) * x ^ j := by rw [hcomm]
        _ = a₁ * b₁ * (x ^ i * x ^ j) := by simp only [mul_assoc]
    have h3 : x ^ (i + j) ∈ T := by
      have : x ^ (i + j) = (a₁ * b₁)⁻¹ * t := by rw [h2]; group
      rw [this]
      exact T.mul_mem (T.inv_mem (T.mul_mem ha₁ hb₁)) ht
    have h4 := hTx _ h3
    exact ⟨a₁, ⟨ha₁A, ha₁⟩, b₁, ⟨hb₁B, hb₁⟩, by rw [h2, h4, mul_one]⟩
  have hint' : A' ⊓ B' ≠ ⊥ := by
    intro h
    apply hint
    rw [eq_bot_iff]
    intro g hg
    have : g ∈ A' ⊓ B' := ⟨⟨hg.1.1, hg.2⟩, ⟨hg.1.2, hg.2⟩⟩
    rw [h] at this
    exact this
  have hrank2 := two_le_pRank_of_mul hp hTe hTc hA'T hB'T hTAB hint'
  have hxe : IsElemAbelian p (zpowers x) := by
    refine ⟨inferInstance, ?_⟩
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hxp, one_zpow]
  have hxc : Nat.card (zpowers x) = p ^ 1 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hxp hx1, pow_one]
  have key : ∀ C : Subgroup G, x ∈ C → 2 ≤ CFSG.Open.pRank p (C ⊓ T) → 3 ≤ CFSG.Open.pRank p C := by
    intro C hxC h2
    obtain ⟨E, hEC, hEe, j, hj, hEc⟩ :=
      exists_elemAbelian_ge_of_le_pRank_gen hp.one_lt (by norm_num) h2
    have hET : E ≤ T := hEC.trans inf_le_right
    have hcommE : ∀ a ∈ E, ∀ b ∈ zpowers x, a * b = b * a := by
      intro a ha b hb
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      exact (Commute.zpow_left (hxcT a (hET ha) : Commute x a) k).eq.symm
    have hdisj : Disjoint E (zpowers x) := by
      rw [disjoint_iff, eq_bot_iff]
      intro g hg
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (Subgroup.mem_inf.1 hg).2
      have h1 : x ^ k ∈ T := hET (Subgroup.mem_inf.1 hg).1
      rw [Subgroup.mem_bot]
      exact hTx k h1
    have hsum := add_le_pRank_of_commute (P := C) hEe hxe hEc hxc hcommE hdisj
      (hEC.trans inf_le_left) (Subgroup.zpowers_le.2 hxC)
    omega
  rcases hrank2 with h | h
  · exact Or.inl (key A hxA h)
  · exact Or.inr (key B hxB h)

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
