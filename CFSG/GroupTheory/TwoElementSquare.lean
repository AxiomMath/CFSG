module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.Data.Rat.Floor

public section

namespace CFSG

theorem sq_eq_one_of_surjective_of_sq_mem_ker {Y H : Type*} [Group Y] [Finite Y] [Group H]
    (φ : Y →* H) (hφ : Function.Surjective φ)
    (h : ∀ y : Y, (∃ k : ℕ, y ^ 2 ^ k = 1) → y ^ 2 ∈ φ.ker)
    {g : H} (hg : ∃ k : ℕ, g ^ 2 ^ k = 1) : g ^ 2 = 1 := by
  obtain ⟨y, rfl⟩ := hφ g
  obtain ⟨k, hk⟩ := hg
  obtain ⟨a, u, hu, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos y).ne'
  have hy : (y ^ u) ^ 2 ^ a = 1 := by
    rw [← pow_mul, mul_comm u (2 ^ a), ← hord, pow_orderOf_eq_one]
  have hmem : (φ y) ^ (u * 2) = 1 := by
    have h' := h (y ^ u) ⟨a, hy⟩
    rw [MonoidHom.mem_ker, map_pow, map_pow, ← pow_mul] at h'
    exact h'
  have hdvd : orderOf (φ y) ∣ u * 2 := orderOf_dvd_of_pow_eq_one hmem
  have hdvd2 : orderOf (φ y) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  obtain ⟨c, -, hc⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd2
  have hcop : Nat.Coprime (2 ^ c) u := hu.coprime_two_left.pow_left c
  have hdvd2u : 2 ^ c ∣ 2 * u := by
    rw [← hc, mul_comm 2 u]
    exact hdvd
  have hc2 : 2 ^ c ∣ 2 := hcop.dvd_of_dvd_mul_right hdvd2u
  rw [← hc, orderOf_dvd_iff_pow_eq_one] at hc2
  exact hc2

theorem eq_bot_of_normal_isPGroup_of_isSimpleGroup {H : Type*} [Group H] [Finite H]
    [IsSimpleGroup H] (hnonab : ∃ a b : H, a * b ≠ b * a) {N : Subgroup H} [N.Normal]
    (hN : IsPGroup 2 N) : N = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · exact h
  · exfalso
    subst h
    have hH2 : IsPGroup 2 H := hN.of_equiv Subgroup.topEquiv
    haveI : Nontrivial (Subgroup.center H) := hH2.center_nontrivial
    have hZ : Subgroup.center H ≠ ⊥ := by
      intro hbot
      obtain ⟨z, hz⟩ := exists_ne (1 : Subgroup.center H)
      have hzbot : (z : H) ∈ (⊥ : Subgroup H) := hbot ▸ z.2
      exact hz (Subtype.ext (Subgroup.mem_bot.mp hzbot))
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center H) with hc | hc
    · exact hZ hc
    · obtain ⟨a, b, hab⟩ := hnonab
      exact hab ((Subgroup.center_eq_top_iff.mp hc).is_comm.comm a b)

theorem sq_eq_one_of_surjective_of_sq_mem {X H : Type*} [Group X] [Group H] [IsSimpleGroup H]
    (hH : ∃ a b : H, a * b ≠ b * a) {Y Q : Subgroup X} [Finite Y]
    (hQ : IsPGroup 2 Q) (hYQ : Y ≤ Subgroup.normalizer (Q : Set X))
    (hsq : ∀ y ∈ Y, (∃ k : ℕ, y ^ 2 ^ k = 1) → y ^ 2 ∈ Q)
    (φ : ↥Y →* H) (hφ : Function.Surjective φ) {g : H} (hg : ∃ k : ℕ, g ^ 2 ^ k = 1) :
    g ^ 2 = 1 := by
  haveI : Finite H := Finite.of_surjective φ hφ
  let R : Subgroup ↥Y := (Q ⊓ Y).subgroupOf Y
  haveI hRnormal : R.Normal := by
    rw [show R = (Q ⊓ Y).subgroupOf Y from rfl,
      Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right]
    exact (le_inf hYQ Subgroup.le_normalizer).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hR2 : IsPGroup 2 R := by
    rw [show R = (Q ⊓ Y).subgroupOf Y from rfl]
    exact (hQ.to_inf_left (K := Y)).of_equiv
      (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
  haveI hRmapN : (R.map φ).Normal := Subgroup.Normal.map hRnormal φ hφ
  have hRmap : R.map φ = ⊥ :=
    eq_bot_of_normal_isPGroup_of_isSimpleGroup hH (hR2.map φ)
  refine sq_eq_one_of_surjective_of_sq_mem_ker φ hφ ?_ hg
  intro y hy
  have hyX : (y : X) ^ 2 ∈ Q := by
    obtain ⟨k, hk⟩ := hy
    exact hsq (y : X) y.2 ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hmemR : y ^ 2 ∈ R := by
    rw [show R = (Q ⊓ Y).subgroupOf Y from rfl, Subgroup.mem_subgroupOf]
    exact ⟨by simpa using hyX, pow_mem y.2 2⟩
  have hmap : φ (y ^ 2) ∈ R.map φ := Subgroup.mem_map_of_mem φ hmemR
  rw [hRmap, Subgroup.mem_bot] at hmap
  simpa [MonoidHom.mem_ker] using hmap

end CFSG
