module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.OmegaMinusCentPairs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.OmegaMinusCentSingular
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.OmegaMinusCentIndex

public section

namespace CFSG.AGLEmbedding.OmegaMinusCent

open QuadraticMap CFSG.ClassicalGroups.Orthogonal Module

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}

theorem exists_subgroup_le_card_three_pow {G : Type*} [Group G] {Y : Subgroup G} {t n : ℕ}
    (hY : Nat.card Y = 3 ^ t) (hn : n ≤ t) : ∃ K ≤ Y, Nat.card K = 3 ^ n := by
  have hP : IsPGroup 3 Y := IsPGroup.of_card hY
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime_of_le_card (n := n) Nat.prime_three hP
    (by rw [hY]; exact Nat.pow_le_pow_right (by norm_num) hn)
  refine ⟨K.map Y.subtype, Subgroup.map_subtype_le _, ?_⟩
  rw [← hK]
  exact Nat.card_congr (K.equivMapOfInjective Y.subtype Y.subtype_injective).symm.toEquiv

theorem exists_rotation_group [FiniteDimensional (ZMod 2) V] (hQ : (polarBilin Q).Nondegenerate)
    {m : ℕ} (hm : 5 ≤ m) (hdim : finrank (ZMod 2) V = 2 * m)
    (hws : ∀ T : Submodule (ZMod 2) V, (∀ y ∈ T, Q y = 0) → finrank (ZMod 2) T ≤ m - 1)
    {P₁ P₂ : HypPair Q} (hP : P₁.Orth P₂) {x : V ≃ₗ[ZMod 2] V}
    (hx : x ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hx3 : x ^ 3 = 1) :
    ∃ Y : Subgroup (V ≃ₗ[ZMod 2] V), Y ≤ elementaryGroup Q ∧ Y ≤ Subgroup.centralizer {x} ∧
      (∀ g ∈ Y, g ^ 3 = 1) ∧ (∀ g ∈ Y, ∀ h ∈ Y, g * h = h * g) ∧
      ∃ t : ℕ, 5 ≤ t ∧ Nat.card Y = 3 ^ t := by
  have hx3' : ∀ v, x (x (x v)) = v := fun v => by
    have h := congrArg (fun g : V ≃ₗ[ZMod 2] V => g v) hx3
    simpa [pow_succ, LinearEquiv.mul_apply] using h
  obtain ⟨Ps, hpw, hcomm, hcases⟩ := exists_pairs_commuting hQ hx hx3' hdim
  have h5 : 5 ≤ Ps.length := by
    rcases hcases with h | ⟨h, e, he0, heQ, heP⟩
    · omega
    · by_contra hlt
      push Not at hlt
      have hmeq : Ps.length = 4 := by omega
      obtain ⟨T, hT, hle⟩ := exists_totSing_of_pairs Ps (Submodule.span (ZMod 2) {e})
        (fun y hy => by
          obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
          rw [QuadraticMap.map_smul, heQ, smul_zero]) hpw
        (fun y hy P hP => by
          obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
          exact ⟨by rw [polar_smul_right_eq, (heP P hP).1, mul_zero],
            by rw [polar_smul_right_eq, (heP P hP).2, mul_zero]⟩)
      have h1 := hws T hT
      rw [finrank_span_singleton he0] at hle
      omega
  obtain ⟨Y, hYO, hYc, hY3, hYcomm, t, ht, hcard⟩ := exists_rotSubgroup Ps hpw hcomm
  have h5dim : 5 ≤ finrank (ZMod 2) V := by omega
  exact ⟨Y, fun g hg => mem_elementaryGroup_of_pow_three hQ h5dim hP (hYO hg) (hY3 g hg), hYc,
    hY3, hYcomm, t, by omega, hcard⟩

theorem exists_three_groups [FiniteDimensional (ZMod 2) V] (hQ : (polarBilin Q).Nondegenerate)
    {m : ℕ} (hm : 5 ≤ m) (hdim : finrank (ZMod 2) V = 2 * m)
    (hws : ∀ T : Submodule (ZMod 2) V, (∀ y ∈ T, Q y = 0) → finrank (ZMod 2) T ≤ m - 1)
    {P₁ P₂ : HypPair Q} (hP : P₁.Orth P₂) {x : V ≃ₗ[ZMod 2] V}
    (hx : x ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hx3 : x ^ 3 = 1) :
    ∀ n : ℕ, n ≤ 5 → ∃ Y : Subgroup (V ≃ₗ[ZMod 2] V), Y ≤ elementaryGroup Q ∧
      Y ≤ Subgroup.centralizer {x} ∧ (∀ g ∈ Y, g ^ 3 = 1) ∧
      (∀ g ∈ Y, ∀ h ∈ Y, g * h = h * g) ∧ Nat.card Y = 3 ^ n := by
  intro n hn
  obtain ⟨Y, hYE, hYc, hY3, hYcomm, t, ht, hcard⟩ := exists_rotation_group hQ hm hdim hws hP hx hx3
  obtain ⟨K, hKY, hKcard⟩ := exists_subgroup_le_card_three_pow hcard (hn.trans ht)
  exact ⟨K, hKY.trans hYE, hKY.trans hYc, fun g hg => hY3 g (hKY hg),
    fun g hg h hh => hYcomm g (hKY hg) h (hKY hh), hKcard⟩

end CFSG.AGLEmbedding.OmegaMinusCent
