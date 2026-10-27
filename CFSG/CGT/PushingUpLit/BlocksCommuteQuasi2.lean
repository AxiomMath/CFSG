module

public import CFSG.CGT.PushingUpLit.BlocksCommuteQuasi1

public section

namespace CFSG.CGT.PushingUpLit

open CFSG CFSG.RankThree.PartOne
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem map_commutator_subtype (X : Subgroup G) :
    (commutator ↥X).map X.subtype = ⁅X, X⁆ := by
  rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]

theorem commutator_eq_self_of_qs {X : Subgroup G} (hX : IsShortGroup ↥X)
    (hq : IsQuasisimple (↥X ⧸ pCore 2 ↥X)) : ⁅X, X⁆ = X := by
  refine le_antisymm (Subgroup.le_normalizer_iff_commutator_le_right.1
    (Subgroup.le_normalizer (H := X))) ?_
  refine noTwoQuot_of_short hX ⁅X, X⁆ ?_ ?_
  · intro g hg n hn
    exact (Subgroup.mem_normalizer_iff.1 (Subgroup.normalizer_commutator_ge_left X X hg) n).1 hn
  · intro g hg
    have hperf : commutator (↥X ⧸ pCore 2 ↥X) = ⊤ := hq.1.commutator_eq_top
    have hmem : (QuotientGroup.mk (⟨g, hg⟩ : ↥X) : ↥X ⧸ pCore 2 ↥X) ∈
        Subgroup.map (QuotientGroup.mk' (pCore 2 ↥X)) (commutator ↥X) := by
      rw [commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _), ← commutator_def,
        hperf]
      trivial
    obtain ⟨c, hc, hcg⟩ := hmem
    have hr : c⁻¹ * ⟨g, hg⟩ ∈ pCore 2 ↥X := QuotientGroup.eq.1 hcg
    obtain ⟨k, hk⟩ := (pCore_isPGroup (p := 2) (G := ↥X)) ⟨c⁻¹ * ⟨g, hg⟩, hr⟩
    refine ⟨k, ?_⟩
    have hk' : (c⁻¹ * ⟨g, hg⟩ : ↥X) ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have hc1 : Abelianization.of c = 1 := by
      rw [← MonoidHom.mem_ker, Abelianization.ker_of]
      exact hc
    have h2 : Abelianization.of (⟨g, hg⟩ : ↥X) = Abelianization.of (c⁻¹ * ⟨g, hg⟩) := by
      have : (⟨g, hg⟩ : ↥X) = c * (c⁻¹ * ⟨g, hg⟩) := by group
      conv_lhs => rw [this]
      rw [map_mul, hc1, one_mul]
    have hab : Abelianization.of ((⟨g, hg⟩ : ↥X) ^ 2 ^ k) = 1 := by
      rw [map_pow, h2, ← map_pow, hk', map_one]
    have h1 : (⟨g, hg⟩ : ↥X) ^ 2 ^ k ∈ commutator ↥X := by
      rw [← Abelianization.ker_of, MonoidHom.mem_ker]
      exact hab
    rw [← map_commutator_subtype]
    exact ⟨_, h1, by simp⟩

theorem commutator_eq_one_of_mem_blockZ {Y : Subgroup G} (hY : IsBlockOf Y) {a : G}
    (h : ∀ l ∈ Y, ⁅a, l⁆ ∈ blockZ Y) : ∀ l ∈ Y, ⁅a, l⁆ = 1 := by
  let N : Subgroup G := Y ⊓ Subgroup.centralizer ({a} : Set G)
  have hodd : ∀ g ∈ Y, Odd (orderOf g) → g ∈ N := by
    intro g hg hgo
    refine Subgroup.mem_inf.2 ⟨hg, ?_⟩
    obtain ⟨t, ht⟩ : ∃ t, t = ⁅a, g⁆ := ⟨_, rfl⟩
    have htZ : t ∈ blockZ Y := ht ▸ h g hg
    have hcent : ∀ m : ℕ, g ^ m * t = t * g ^ m := fun m =>
      (Subgroup.mem_centralizer_iff.1 htZ.2) (g ^ m) (pow_mem hg m)
    have key : ∀ m : ℕ, ⁅a, g ^ m⁆ = t ^ m := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        have e2 : ⁅a, g ^ (m + 1)⁆ = ⁅a, g ^ m⁆ * (g ^ m * t * (g ^ m)⁻¹) := by
          rw [ht]
          simp only [commutatorElement_def]
          group
        have e3 : g ^ m * t * (g ^ m)⁻¹ = t := by
          rw [hcent m]
          group
        rw [e2, ih, e3]
        group
    have h1 : t ^ orderOf g = 1 := by
      have := key (orderOf g)
      rw [pow_orderOf_eq_one] at this
      simpa using this.symm
    have htR : t ∈ oTwoIn Y := blockU_le_oTwoIn Y (blockZ_le_blockU Y htZ)
    have ht1 : t ∈ (⊥ : Subgroup G) :=
      mem_of_pow_mem_odd (exists_pow_eq_one_of_mem_oTwoIn htR) hgo ⊥ (by rw [h1]; exact one_mem _)
    have ht1' : t = 1 := ht1
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact commutatorElement_eq_one_iff_mul_comm.1 (ht.symm.trans ht1')
  intro l hl
  have hYN : Y ≤ N := by
    refine (eq_oTwoUpper_of_short hY.2).le.trans ?_
    exact (Subgroup.closure_le N).2 fun g hg => hodd g hg.1 hg.2
  have := (Subgroup.mem_centralizer_iff.1 (hYN hl).2) a (Set.mem_singleton a)
  exact commutatorElement_eq_one_iff_mul_comm.2 this

theorem commutator_mem_blockZ_of_odd {X Y : Subgroup G} (hY : IsBlockOf Y)
    (hXY : ∀ x ∈ X, ∀ l ∈ Y, ⁅x, l⁆ ∈ blockU Y)
    (hXZ : ∀ x ∈ X, ∀ u ∈ blockU Y, ⁅x, u⁆ ∈ blockZ Y) {a : G} (ha : a ∈ X)
    (hodd : Odd (orderOf a)) : ∀ l ∈ Y, ⁅a, l⁆ ∈ blockZ Y := by
  intro l hl
  have hw1 : ⁅a, l⁆ ∈ blockU Y := hXY a ha l hl
  have key : ∀ k : ℕ, ∃ z ∈ blockZ Y, ⁅a ^ k, l⁆ = ⁅a, l⁆ ^ k * z := by
    intro k
    induction k with
    | zero => exact ⟨1, one_mem _, by simp⟩
    | succ k ih =>
      obtain ⟨z, hz, e⟩ := ih
      have hwk : ⁅a ^ k, l⁆ ∈ blockU Y := hXY _ (pow_mem ha k) l hl
      obtain ⟨z', hz'def⟩ : ∃ z', z' = ⁅a, ⁅a ^ k, l⁆⁆ := ⟨_, rfl⟩
      have hz' : z' ∈ blockZ Y := hz'def ▸ hXZ a ha _ hwk
      refine ⟨z' * z, mul_mem hz' hz, ?_⟩
      have e2 : ⁅a ^ (k + 1), l⁆ = z' * ⁅a ^ k, l⁆ * ⁅a, l⁆ := by
        rw [hz'def]
        simp only [commutatorElement_def, pow_succ']
        group
      rw [e2, e]
      have c1 : z' * ⁅a, l⁆ ^ k = ⁅a, l⁆ ^ k * z' :=
        blockU_commute hY.2 (blockZ_le_blockU Y hz') (pow_mem hw1 k)
      have c2 : z * ⁅a, l⁆ = ⁅a, l⁆ * z := blockU_commute hY.2 (blockZ_le_blockU Y hz) hw1
      have c3 : z' * ⁅a, l⁆ = ⁅a, l⁆ * z' :=
        blockU_commute hY.2 (blockZ_le_blockU Y hz') hw1
      calc z' * (⁅a, l⁆ ^ k * z) * ⁅a, l⁆
          = (z' * ⁅a, l⁆ ^ k) * (z * ⁅a, l⁆) := by group
        _ = (⁅a, l⁆ ^ k * z') * (⁅a, l⁆ * z) := by rw [c1, c2]
        _ = ⁅a, l⁆ ^ k * (z' * ⁅a, l⁆) * z := by group
        _ = ⁅a, l⁆ ^ k * (⁅a, l⁆ * z') * z := by rw [c3]
        _ = ⁅a, l⁆ ^ (k + 1) * (z' * z) := by rw [pow_succ]; simp only [mul_assoc]
  obtain ⟨z, hz, e⟩ := key (orderOf a)
  rw [pow_orderOf_eq_one] at e
  have hpow : ⁅a, l⁆ ^ orderOf a ∈ blockZ Y := by
    have e' : ⁅a, l⁆ ^ orderOf a = z⁻¹ := by
      have : ⁅a, l⁆ ^ orderOf a * z = 1 := by simpa using e.symm
      exact eq_inv_of_mul_eq_one_left this
    rw [e']
    exact inv_mem hz
  exact mem_of_pow_mem_odd (exists_pow_eq_one_of_mem_oTwoIn (blockU_le_oTwoIn Y hw1)) hodd _ hpow

end CFSG.CGT.PushingUpLit
