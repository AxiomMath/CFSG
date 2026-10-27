module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.TightEmbedding
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FinalGroup

public section

namespace CFSG.QuasithinUnique.Claim2526

open CFSG.ComponentClassification.AschbacherTightEmbedding

section Cyclic4

variable {G : Type} [Group G]

theorem orderOf_eq_four {v t : G} (hv2 : v ^ 2 = t) (ht1 : t ≠ 1) (hv4 : v ^ 4 = 1) :
    orderOf v = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := v) (by simpa [hv2] using ht1)
    (by simpa using hv4)
  simpa using h

theorem mem_zpowers_four {v : G} (hv : orderOf v = 4) {y : G} (hy : y ∈ Subgroup.zpowers v) :
    y = 1 ∨ y = v ∨ y = v ^ 2 ∨ y = v ^ 3 := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hk : v ^ k = v ^ (k % 4) := by
    have := zpow_mod_orderOf v k
    rw [hv] at this
    simpa using this.symm
  have h4 : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by omega
  rcases h4 with h | h | h | h <;> rw [hk, h] <;> simp

theorem sq_mem_zpowers_four {v t : G} (hv2 : v ^ 2 = t) (hv4 : v ^ 4 = 1) (ht1 : t ≠ 1) {y : G}
    (hy : y ∈ Subgroup.zpowers v) : y ^ 2 = 1 ∨ y ^ 2 = t := by
  have hord := orderOf_eq_four hv2 ht1 hv4
  rcases mem_zpowers_four hord hy with rfl | rfl | rfl | rfl
  · left; simp
  · right; exact hv2
  · left; rw [← pow_mul]; exact hv4
  · right
    rw [← pow_mul, show 3 * 2 = 4 + 2 by norm_num, pow_add, hv4, one_mul, hv2]

theorem eq_one_or_eq_of_sq_eq_one {v t : G} (hv2 : v ^ 2 = t) (hv4 : v ^ 4 = 1) (ht1 : t ≠ 1) {y : G}
    (hy : y ∈ Subgroup.zpowers v) (hy2 : y ^ 2 = 1) : y = 1 ∨ y = t := by
  have hord := orderOf_eq_four hv2 ht1 hv4
  rcases mem_zpowers_four hord hy with rfl | rfl | rfl | rfl
  · left; rfl
  · exact absurd (hv2 ▸ hy2) ht1
  · right; exact hv2
  · exfalso
    apply ht1
    rw [← hv2, ← hy2, ← pow_mul, show 3 * 2 = 4 + 2 by norm_num, pow_add, hv4, one_mul]

end Cyclic4

section Tight

variable {G : Type} [Group G]

theorem tightlyEmbedded_zpowers_four {v t : G} (hv2 : v ^ 2 = t) (hv4 : v ^ 4 = 1) (ht1 : t ≠ 1)
    (hVN : ∀ g : G, g * t = t * g → g ∈ Subgroup.normalizer (Subgroup.zpowers v : Set G)) :
    TightlyEmbedded (Subgroup.zpowers v) := by
  have hord := orderOf_eq_four hv2 ht1 hv4
  refine ⟨by rw [Nat.card_zpowers, hord]; exact ⟨2, rfl⟩, fun g hg => ?_⟩
  have hbot : Subgroup.zpowers v ⊓ rightConjugate (Subgroup.zpowers v) g = ⊥ := by
    by_contra hne
    obtain ⟨⟨x, hx⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    have hxV : x ∈ Subgroup.zpowers v := hx.1
    have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
    have htI : t ∈ Subgroup.zpowers v ⊓ rightConjugate (Subgroup.zpowers v) g := by
      rcases sq_mem_zpowers_four hv2 hv4 ht1 hxV with h2 | h2
      · rcases eq_one_or_eq_of_sq_eq_one hv2 hv4 ht1 hxV h2 with h1 | h1
        · exact absurd h1 hx1'
        · rw [← h1]; exact hx
      · rw [← h2, sq]; exact Subgroup.mul_mem _ hx hx
    have htg : g * t * g⁻¹ ∈ Subgroup.zpowers v := (mem_rightConjugate_iff _ _ _).mp htI.2
    have hsq : (g * t * g⁻¹) ^ 2 = 1 := by
      have : t ^ 2 = 1 := by rw [← hv2, ← pow_mul]; exact hv4
      calc (g * t * g⁻¹) ^ 2 = g * t ^ 2 * g⁻¹ := by rw [sq, sq]; group
        _ = 1 := by rw [this]; group
    have hgt : g * t * g⁻¹ = t := by
      rcases eq_one_or_eq_of_sq_eq_one hv2 hv4 ht1 htg hsq with h1 | h1
      · exfalso
        apply ht1
        calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
          _ = 1 := by rw [h1]; group
      · exact h1
    apply hg
    apply hVN
    calc g * t = g * t * g⁻¹ * g := by group
      _ = t * g := by rw [hgt]
  rw [hbot, Subgroup.card_bot]
  exact odd_one

end Tight

section Fusion

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem conj_pow_inv (g v : G) (n : ℕ) : (g⁻¹ * v * g) ^ n = g⁻¹ * v ^ n * g := by
  have := conj_pow (i := n) (a := g⁻¹) (b := v)
  simpa only [inv_inv] using this

omit [Finite G] in
theorem isSylowTwoOf_top_inf_self {V : Subgroup G} (hV : IsPGroup 2 V) :
    IsSylowTwoOf V (⊤ ⊓ V) := by
  refine ⟨le_inf le_top le_rfl, hV, ?_⟩
  have : V.subgroupOf (⊤ ⊓ V) = ⊤ := by
    rw [Subgroup.subgroupOf_eq_top]
    exact inf_le_right
  rw [this, Subgroup.index_top]
  omega

theorem commute_of_conj {T : Subgroup G} (hT2 : IsPGroup 2 T) {v t : G} (hv2 : v ^ 2 = t)
    (hv4 : v ^ 4 = 1) (ht1 : t ≠ 1)
    (hVN : ∀ g : G, g * t = t * g → g ∈ Subgroup.normalizer (Subgroup.zpowers v : Set G))
    (hvT : v ∈ T) {g : G} (hg : CFSG.conjugate (Subgroup.zpowers v) g ≤ T)
    (hne : CFSG.conjugate (Subgroup.zpowers v) g ≠ Subgroup.zpowers v) :
    ∀ a ∈ Subgroup.zpowers v, ∀ b ∈ CFSG.conjugate (Subgroup.zpowers v) g, a * b = b * a := by
  have hV2 : IsPGroup 2 (Subgroup.zpowers v) := hT2.to_le (Subgroup.zpowers_le.mpr hvT)
  have hV0 : Subgroup.zpowers v ≠ ⊥ := by
    intro h
    have hmem : v ∈ (⊥ : Subgroup G) := h ▸ Subgroup.mem_zpowers v
    have hv1 : v = 1 := Subgroup.mem_bot.mp hmem
    apply ht1
    rw [← hv2, hv1]
    simp
  have hset : Tight.Setup (Subgroup.zpowers v) ⊤ (Subgroup.zpowers v) T :=
    ⟨tightlyEmbedded_zpowers_four hv2 hv4 ht1 hVN, isSylowTwoOf_top_inf_self hV2, hV0, hT2, le_top,
      Subgroup.zpowers_le.mpr hvT⟩
  have hΦ : ∃ y ∈ Subgroup.zpowers v, y ^ 2 ≠ 1 :=
    ⟨v, Subgroup.mem_zpowers v, by rw [hv2]; exact ht1⟩
  exact hset.delta_commute hΦ _ hset.mem_delta_self _ ⟨⟨g, Subgroup.mem_top g, rfl⟩, hg⟩
    (Ne.symm hne)

omit [Finite G] in
theorem commute_zpowers_of_commute {a v : G} (h : a * v = v * a) :
    ∀ y ∈ Subgroup.zpowers v, a * y = y * a := by
  intro y hy
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  exact ((Commute.zpow_right (show Commute a v from h) k)).eq

theorem t_conj_cases {T S SC : Subgroup G} {t z v : G} (hT2 : IsPGroup 2 T) (hST : S ≤ T)
    (hSCS : SC ≤ S) (hCT : ∀ g ∈ T, g * t = t * g → g ∈ S) (hv2 : v ^ 2 = t) (hv4 : v ^ 4 = 1)
    (ht1 : t ≠ 1) (hvSC : v ∈ SC)
    (hVN : ∀ g : G, g * t = t * g → g ∈ Subgroup.normalizer (Subgroup.zpowers v : Set G))
    (hCSC : ∀ s ∈ SC, (∀ y ∈ Subgroup.zpowers v, s * y = y * s) → s ∈ Subgroup.zpowers v)
    (hz2 : z ^ 2 = 1) (hzS : ∀ s ∈ S, z * s = s * z) (hnc : ∀ g : G, g⁻¹ * z * g ≠ t)
    (hsq : ∀ w ∈ S, w ^ 4 = 1 → w ^ 2 ∈ SC ∨ ∃ s ∈ SC, w ^ 2 = z * s) {g : G}
    (hg : CFSG.conjugate (Subgroup.zpowers v) g ≤ T) : g⁻¹ * t * g = t ∨ g⁻¹ * t * g = t * z := by
  have hvS : v ∈ S := hSCS hvSC
  have hvT : v ∈ T := hST hvS
  have htS : t ∈ S := by rw [← hv2]; exact S.pow_mem hvS 2
  set w : G := g⁻¹ * v * g with hw
  have hwV : w ∈ CFSG.conjugate (Subgroup.zpowers v) g := by
    rw [BenderBranch.mem_conjugate_iff]
    have : g * w * g⁻¹ = v := by rw [hw]; group
    rw [this]
    exact Subgroup.mem_zpowers v
  have hwT : w ∈ T := hg hwV
  have hw2 : w ^ 2 = g⁻¹ * t * g := by rw [hw, conj_pow_inv, hv2]
  have hw4 : w ^ 4 = 1 := by rw [hw, conj_pow_inv, hv4]; group
  have htg1 : g⁻¹ * t * g ≠ 1 := by
    intro h1
    apply ht1
    calc t = g * (g⁻¹ * t * g) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group
  by_cases hVg : CFSG.conjugate (Subgroup.zpowers v) g = Subgroup.zpowers v
  ·
    left
    have hwV' : w ∈ Subgroup.zpowers v := hVg ▸ hwV
    rcases sq_mem_zpowers_four hv2 hv4 ht1 hwV' with h | h
    · exact absurd (hw2 ▸ h) htg1
    · rw [← hw2]; exact h
  · have hcomm := commute_of_conj hT2 hv2 hv4 ht1 hVN hvT hg hVg
    have hvw : v * w = w * v := hcomm v (Subgroup.mem_zpowers v) w hwV
    have hwv : w * v = v * w := hvw.symm
    have hwt : w * t = t * w := by
      rw [← hv2, sq]
      exact ((Commute.mul_right (show Commute w v from hwv) (show Commute w v from hwv))).eq
    have hwS : w ∈ S := hCT w hwT hwt
    have hw2v : w ^ 2 * v = v * w ^ 2 := by
      rw [sq]
      exact ((Commute.mul_left (show Commute w v from hwv) (show Commute w v from hwv))).eq
    have hw22 : (w ^ 2) ^ 2 = 1 := by
      rw [← pow_mul]
      exact hw4
    rcases hsq w hwS hw4 with h | ⟨s, hsSC, hs⟩
    · left
      have hV := hCSC (w ^ 2) h (commute_zpowers_of_commute hw2v)
      rcases eq_one_or_eq_of_sq_eq_one hv2 hv4 ht1 hV hw22 with h' | h'
      · exact absurd (hw2 ▸ h') htg1
      · rw [← hw2]
        exact h'
    · have hzv : z * v = v * z := hzS v hvS
      have hsv : s * v = v * s := by
        have h1 : z * (s * v) = z * (v * s) := by
          calc z * (s * v) = (z * s) * v := by rw [mul_assoc]
            _ = w ^ 2 * v := by rw [hs]
            _ = v * w ^ 2 := hw2v
            _ = v * (z * s) := by rw [hs]
            _ = (v * z) * s := by rw [mul_assoc]
            _ = (z * v) * s := by rw [hzv]
            _ = z * (v * s) := by rw [mul_assoc]
        exact mul_left_cancel h1
      have hsV : s ∈ Subgroup.zpowers v := hCSC s hsSC (commute_zpowers_of_commute hsv)
      have hsS : s ∈ S := hSCS hsSC
      have hzs : z * s = s * z := hzS s hsS
      have hs2 : s ^ 2 = 1 := by
        have h1 := hw22
        rw [hs, Commute.mul_pow (show Commute z s from hzs) 2, hz2, one_mul] at h1
        exact h1
      rcases eq_one_or_eq_of_sq_eq_one hv2 hv4 ht1 hsV hs2 with h1 | h1
      · exfalso
        have hz : g⁻¹ * t * g = z := by rw [← hw2, hs, h1, mul_one]
        apply hnc g⁻¹
        rw [← hz]
        group
      · right
        rw [← hw2, hs, h1]
        exact hzS t htS

theorem card_le_two_mul {T S : Subgroup G} {t z : G} (hCT : ∀ g ∈ T, g * t = t * g → g ∈ S)
    (hcases : ∀ g ∈ T, g⁻¹ * t * g = t ∨ g⁻¹ * t * g = t * z) : Nat.card T ≤ 2 * Nat.card S := by
  have hS : ∀ g ∈ T, g⁻¹ * t * g = t → g ∈ S := by
    intro g hg h
    apply hCT g hg
    calc g * t = g * (g⁻¹ * t * g) := by rw [h]
      _ = t * g := by group
  by_cases hex : ∃ b ∈ T, b⁻¹ * t * b = t * z
  · obtain ⟨b, hbT, hb⟩ := hex
    refine A6Final.card_le_two_mul_of_cosets (b := b) fun g hg => ?_
    rcases hcases g hg with h | h
    · exact Or.inl (hS g hg h)
    · right
      apply hCT _ (T.mul_mem hg (T.inv_mem hbT))
      have h1 : g⁻¹ * t * g = b⁻¹ * t * b := by rw [h, hb]
      calc g * b⁻¹ * t = g * b⁻¹ * t * (g * b⁻¹)⁻¹ * (g * b⁻¹) := by group
        _ = (g * (b⁻¹ * t * b) * g⁻¹)⁻¹⁻¹ * (g * b⁻¹) := by group
        _ = t * (g * b⁻¹) := by
          rw [← h1]
          group
  · refine A6Final.card_le_two_mul_of_cosets (b := 1) fun g hg => ?_
    rcases hcases g hg with h | h
    · exact Or.inl (hS g hg h)
    · exact absurd ⟨g, hg, h⟩ hex

omit [Finite G] in
theorem mem_normalizer_zpowers_of_sqrt {SC : Subgroup G} {t v : G} (hv2 : v ^ 2 = t)
    (hsqrt : ∀ x ∈ SC, x ^ 2 = t → x ∈ Subgroup.zpowers v)
    (hHN : ∀ g : G, g * t = t * g → g ∈ Subgroup.normalizer (SC : Set G)) (hvSC : v ∈ SC) :
    ∀ g : G, g * t = t * g → g ∈ Subgroup.normalizer (Subgroup.zpowers v : Set G) := by
  have key : ∀ g : G, g * t = t * g → g⁻¹ * v * g ∈ Subgroup.zpowers v := by
    intro g hg
    have hgi : g⁻¹ ∈ Subgroup.normalizer (SC : Set G) := Subgroup.inv_mem _ (hHN g hg)
    have h1 : g⁻¹ * v * g⁻¹⁻¹ ∈ SC := (Subgroup.mem_normalizer_iff.mp hgi v).mp hvSC
    rw [inv_inv] at h1
    apply hsqrt _ h1
    rw [conj_pow_inv, hv2]
    calc g⁻¹ * t * g = g⁻¹ * (t * g) := by rw [mul_assoc]
      _ = g⁻¹ * (g * t) := by rw [hg]
      _ = t := by group
  have conj_le : ∀ a : G, a⁻¹ * v * a ∈ Subgroup.zpowers v → ∀ x ∈ Subgroup.zpowers v,
      a⁻¹ * x * a ∈ Subgroup.zpowers v := by
    intro a ha x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have : a⁻¹ * v ^ k * a = (a⁻¹ * v * a) ^ k := by
      have := conj_zpow (i := k) (a := a⁻¹) (b := v)
      simpa only [inv_inv] using this.symm
    rw [this]
    exact Subgroup.zpow_mem _ ha k
  intro g hg
  have hg' : g⁻¹ * t = t * g⁻¹ := by
    calc g⁻¹ * t = g⁻¹ * (t * g) * g⁻¹ := by group
      _ = g⁻¹ * (g * t) * g⁻¹ := by rw [hg]
      _ = t * g⁻¹ := by group
  have hg1 := key g hg
  have hg2 := key g⁻¹ hg'
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have := conj_le g⁻¹ hg2 x hx
    rwa [inv_inv] at this
  · intro hx
    have := conj_le g hg1 _ hx
    have e : g⁻¹ * (g * x * g⁻¹) * g = x := by group
    rwa [e] at this

end Fusion

end CFSG.QuasithinUnique.Claim2526
