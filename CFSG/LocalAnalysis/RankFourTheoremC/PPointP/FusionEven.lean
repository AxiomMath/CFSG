module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointP.Fusion
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointP.FieldTwo
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointP.FieldFacts

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PPointP

open Subgroup CFSG.Open

theorem conj_ne_one {G : Type} [Group G] {y : G} (hy1 : y ≠ 1) (m : G) : m * y * m⁻¹ ≠ 1 := by
  intro h0
  exact hy1 ((MulEquiv.map_eq_one_iff (MulAut.conj m)).mp h0)

namespace FusionData

variable {G : Type} [Group G] [Finite G] {p n : ℕ} {F : Type} [Field F] {f : F → G} {x : G}
  {W : Subgroup G} (h : FusionData G p n F f x W)

include h

theorem not_conjLine_A_of_even [hp : Fact p.Prime] [CharP F p] [Finite F] (hp2 : p ≠ 2)
    (hn : Even n) {k : F} (hk : k ≠ 0) (hA : ConjLine x (f k * x)) : False := by
  refine h.false_of_A_plane hk fun m hm => ?_
  by_cases hm0 : m = 0
  · rw [hm0, Nat.cast_zero, zero_mul, h.f_zero, one_mul]
    exact conjLine_self x
  obtain ⟨b, hb⟩ := isSquare_natCast_of_even h.card_F hp2 hn m
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact natCast_ne_zero_of_lt (Nat.pos_of_ne_zero hm0) hm (by rw [hb, mul_zero])
  have hmk : (m : F) * k = b ^ 2 * k := by rw [hb]; ring
  rw [hmk]
  exact h.conjLine_A_torus hA hb0

omit [Finite G] in
theorem not_conjLine_B_of_even_four [hp : Fact p.Prime] [CharP F p] [Finite F] (hp2 : p ≠ 2)
    (hn : Even n) (h4 : 4 ≤ n) {t : F} (ht : t ≠ 0) (hB : ConjLine x (f t)) : False := by
  obtain ⟨c, hc, hsq⟩ := exists_square_line h.card_F hp2 hn h4
  refine h.false_of_B_plane ht hc fun m _ => ?_
  obtain ⟨b, hb⟩ := hsq m
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact natCast_add_ne_zero hc m (by rw [hb, mul_zero])
  have hm : t * ((m : F) + c) = b ^ 2 * t := by rw [hb]; ring
  rw [hm]
  exact h.conjLine_B_torus hB hb0

omit [Finite G] in
theorem f_ne_one {s : F} (hs : s ≠ 0) : f s ≠ 1 := fun h1 => hs (h.f_inj (h1.trans h.f_zero.symm))

theorem false_of_rank_two [hp : Fact p.Prime] [CharP F p] (hn : n = 2) {m : G} {y y' : G}
    (hmx : m * x * m⁻¹ ∈ h.V) (hy : y ∈ h.V) (hy' : y' ∈ h.V) (hy1 : y ≠ 1)
    (hy'y : y' ∉ zpowers y) (hmy : m * y * m⁻¹ ∈ h.V) (hmy' : m * y' * m⁻¹ ∈ h.V) : False := by
  obtain ⟨a, rfl⟩ := hy
  obtain ⟨b, rfl⟩ := hy'
  have hcard := card_closure_pair (h.f_comm' a b) hy1 (h.f_pow_p a) (h.f_pow_p b) hy'y
  have hcl : closure ({f a, f b} : Set G) ≤ h.V := by
    rw [closure_le]
    rintro _ (rfl | hz)
    · exact ⟨a, rfl⟩
    · rw [Set.mem_singleton_iff.mp hz]
      exact ⟨b, rfl⟩
  have hclV : closure ({f a, f b} : Set G) = h.V :=
    Subgroup.eq_of_le_of_card_ge hcl (by rw [h.card_V, hn, hcard])
  have hconj : ∀ v ∈ h.V, m * v * m⁻¹ ∈ h.V := by
    intro v hv
    rw [← hclV] at hv
    induction hv using Subgroup.closure_induction with
    | mem z hz =>
      rcases hz with rfl | hz
      · exact hmy
      · rw [Set.mem_singleton_iff.mp hz]
        exact hmy'
    | one => simp
    | mul u w _ _ ihu ihw =>
      have : m * (u * w) * m⁻¹ = (m * u * m⁻¹) * (m * w * m⁻¹) := by group
      rw [this]
      exact h.V.mul_mem ihu ihw
    | inv u _ ihu =>
      have : m * u⁻¹ * m⁻¹ = (m * u * m⁻¹)⁻¹ := by group
      rw [this]
      exact h.V.inv_mem ihu
  let φ : h.V → h.V := fun v => ⟨m * v * m⁻¹, hconj v v.2⟩
  have hφinj : Function.Injective φ := by
    intro u w huw
    have h1 : m * (u : G) * m⁻¹ = m * (w : G) * m⁻¹ := congrArg Subtype.val huw
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h1))
  obtain ⟨⟨v, hvV⟩, hv⟩ := Finite.surjective_of_injective hφinj ⟨m * x * m⁻¹, hmx⟩
  have h1 : m * v * m⁻¹ = m * x * m⁻¹ := congrArg Subtype.val hv
  have hvx : v = x := mul_left_cancel (mul_right_cancel h1)
  obtain ⟨t, ht⟩ := hvV
  exact h.f_ne t (ht.trans hvx)

theorem conj_mem_V_or_zpowers [hp : Fact p.Prime] [CharP F p]
    (hnoA : ∀ k : F, k ≠ 0 → ¬ ConjLine x (f k * x)) {m : G}
    (hm : m ∈ normalizer (W : Set G)) {s : F} (hs : ConjLine x (f s)) :
    m * f s * m⁻¹ ∈ h.V ∨ m * f s * m⁻¹ ∈ zpowers x := by
  have hyW : m * f s * m⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp hm _).mp (h.f_mem s)
  have hyc := hs.conj m
  by_cases hyx : m * f s * m⁻¹ ∈ zpowers x
  · exact Or.inr hyx
  · left
    rcases h.exists_type hyW hyc hyx with ⟨t', ht', heq⟩ | ⟨t', ht', heq⟩
    · have hmem : m * f s * m⁻¹ ∈ zpowers (f t') := heq ▸ mem_zpowers _
      exact (zpowers_le.mpr ⟨t', rfl⟩ : zpowers (f t') ≤ h.V) hmem
    · exfalso
      obtain ⟨g', hg'⟩ := hyc
      exact hnoA t' ht' ⟨g', heq.symm.trans hg'⟩

theorem not_both_mem_zpowers [hp : Fact p.Prime] {y y' : G}
    (hy' : ConjLine x y') (hy1 : y ≠ 1) (hy'1 : y' ≠ 1) (hind : y' ∉ zpowers y) (m : G)
    (h1 : m * y * m⁻¹ ∈ zpowers x) (h2 : m * y' * m⁻¹ ∈ zpowers x) : False := by
  have hz' : zpowers (m * y' * m⁻¹) = zpowers x :=
    h.zpowers_eq_of_mem (conjLine_self x) h2 (conj_ne_one hy'1 m)
  have hmem : m * y * m⁻¹ ∈ zpowers (m * y' * m⁻¹) := by rw [hz']; exact h1
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hmem
  rw [conj_zpow] at hk
  have hyk : y' ^ k = y := mul_left_cancel (mul_right_cancel hk)
  have hzz : zpowers y = zpowers y' := h.zpowers_eq_of_mem hy' (mem_zpowers_iff.mpr ⟨k, hyk⟩) hy1
  exact hind (hzz ▸ mem_zpowers y')

theorem not_conjLine_B_two [hp : Fact p.Prime] [CharP F p] [Finite F] (hn : n = 2) (hp5 : 5 ≤ p)
    (hnoA : ∀ k : F, k ≠ 0 → ¬ ConjLine x (f k * x)) {t : F} (ht : t ≠ 0)
    (hB : ConjLine x (f t)) : False := by
  obtain ⟨γ, hγ0, hγ2, hγ4⟩ := exists_three_squares (by rw [h.card_F, hn]) hp5
  obtain ⟨m, hm, hmx⟩ : ∃ m ∈ normalizer (W : Set G), m * x * m⁻¹ ∈ h.V := by
    obtain ⟨g, hg⟩ := hB
    have hgx : g * x * g⁻¹ ∈ zpowers (f t) := by
      rw [hg]
      exact Subgroup.mem_map.mpr ⟨x, mem_zpowers x, by simp⟩
    obtain ⟨m, hm, hmx⟩ := h.trans g ((zpowers_le.mpr (h.f_mem t)) hgx)
    exact ⟨m, hm, by rw [hmx]; exact (zpowers_le.mpr ⟨t, rfl⟩ : zpowers (f t) ≤ h.V) hgx⟩
  have hs1 : ConjLine x (f (γ ^ 2 * t)) := h.conjLine_B_torus hB hγ0
  have hs2 : ConjLine x (f (γ ^ 4 * t)) := by
    have := h.conjLine_B_torus hB (pow_ne_zero 2 hγ0)
    have e : (γ ^ 2) ^ 2 = γ ^ 4 := by ring
    rwa [e] at this
  have hind : ∀ s s' : F, (∀ k : ℕ, s' ≠ (k : F) * s) → f s' ∉ zpowers (f s) := by
    intro s s' hk hmem
    obtain ⟨j, hj⟩ := mem_zpowers_iff.mp hmem
    rw [← h.f_intCast_mul] at hj
    have h2 : (j : F) * s = s' := h.f_inj hj
    apply hk ((j % p).toNat)
    rw [← intCast_eq_natCast_emod (F := F) (p := p) j]
    exact h2.symm
  have hpair : ∀ s s' : F, s ≠ 0 → s' ≠ 0 → ConjLine x (f s) → ConjLine x (f s') →
      (∀ k : ℕ, s' ≠ (k : F) * s) → (m * f s * m⁻¹ ∈ h.V ∨ m * f s' * m⁻¹ ∈ h.V) := by
    intro s s' hs0 hs'0 hs hs' hk
    rcases h.conj_mem_V_or_zpowers hnoA hm hs with h1 | h1
    · exact Or.inl h1
    rcases h.conj_mem_V_or_zpowers hnoA hm hs' with h2 | h2
    · exact Or.inr h2
    exact (h.not_both_mem_zpowers hs' (h.f_ne_one hs0) (h.f_ne_one hs'0) (hind s s' hk) m h1
      h2).elim
  have hfin : ∀ s s' : F, s ≠ 0 → (∀ k : ℕ, s' ≠ (k : F) * s) → m * f s * m⁻¹ ∈ h.V →
      m * f s' * m⁻¹ ∈ h.V → False := by
    intro s s' hs0 hk h1 h2
    exact h.false_of_rank_two hn hmx ⟨s, rfl⟩ ⟨s', rfl⟩ (h.f_ne_one hs0) (hind s s' hk) h1 h2
  have hγ2t : γ ^ 2 * t ≠ 0 := mul_ne_zero (pow_ne_zero 2 hγ0) ht
  have hγ4t : γ ^ 4 * t ≠ 0 := mul_ne_zero (pow_ne_zero 4 hγ0) ht
  have hk01 : ∀ k : ℕ, γ ^ 2 * t ≠ (k : F) * t := fun k hk => hγ2 k (mul_right_cancel₀ ht hk)
  have hk02 : ∀ k : ℕ, γ ^ 4 * t ≠ (k : F) * t := fun k hk => hγ4 k (mul_right_cancel₀ ht hk)
  have hk12 : ∀ k : ℕ, γ ^ 4 * t ≠ (k : F) * (γ ^ 2 * t) := by
    intro k hk
    exact hγ2 k (mul_right_cancel₀ hγ2t (by linear_combination hk))
  by_cases q0 : m * f t * m⁻¹ ∈ h.V
  · by_cases q1 : m * f (γ ^ 2 * t) * m⁻¹ ∈ h.V
    · exact hfin t (γ ^ 2 * t) ht hk01 q0 q1
    · have q2 := (hpair (γ ^ 2 * t) (γ ^ 4 * t) hγ2t hγ4t hs1 hs2 hk12).resolve_left q1
      exact hfin t (γ ^ 4 * t) ht hk02 q0 q2
  · have q1 := (hpair t (γ ^ 2 * t) ht hγ2t hB hs1 hk01).resolve_left q0
    have q2 := (hpair t (γ ^ 4 * t) ht hγ4t hB hs2 hk02).resolve_left q0
    exact hfin (γ ^ 2 * t) (γ ^ 4 * t) hγ2t hk12 q1 q2

end FusionData

end CFSG.LocalAnalysis.RankFourTheoremC.PPointP
