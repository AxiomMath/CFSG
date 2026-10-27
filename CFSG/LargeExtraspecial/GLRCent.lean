module

public import CFSG.LargeExtraspecial.GLRCentModel
public import CFSG.LargeExtraspecial.GLRCentCount
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.GLR

open Module

section General

variable {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V]

theorem card_commute_of_comp_eq_zero {N : V →ₗ[F] V} (hN : N ∘ₗ N = 0) {k m : ℕ}
    (hk : finrank F (LinearMap.range N) = k) (hm : finrank F V = 2 * k + m) :
    Nat.card {h : V ≃ₗ[F] V // ∀ v, h (N v) = N (h v)} =
      Nat.card (GL (Fin k) F) * Nat.card (GL (Fin m) F) * Nat.card F ^ (k * k + m * k + k * m) := by
  obtain ⟨e, he⟩ := exists_linearEquiv_nilModel hN hk hm
  have he' : ∀ v, e.symm (N v) = nilModelMap F k m (e.symm v) := fun v => by
    apply e.injective
    rw [LinearEquiv.apply_symm_apply, ← he, LinearEquiv.apply_symm_apply]
  rw [← card_nilModelCent]
  refine Nat.card_congr
    { toFun := fun h => ⟨e.trans (h.1.trans e.symm), fun w => ?_⟩
      invFun := fun h => ⟨e.symm.trans (h.1.trans e), fun v => ?_⟩
      left_inv := fun h => by
        apply Subtype.ext
        apply LinearEquiv.ext
        intro v
        simp
      right_inv := fun h => by
        apply Subtype.ext
        apply LinearEquiv.ext
        intro w
        simp }
  · simp only [LinearEquiv.trans_apply]
    rw [← he, h.2, he']
  · simp only [LinearEquiv.trans_apply]
    rw [he', h.2, he]

variable [CharP F 2]

omit [FiniteDimensional F V] in
theorem sub_id_comp_sub_id_eq_zero {g : V ≃ₗ[F] V} (hg : g * g = 1) :
    ((g : V →ₗ[F] V) - LinearMap.id) ∘ₗ ((g : V →ₗ[F] V) - LinearMap.id) = 0 := by
  have h2 : ∀ x : V, x + x = 0 := fun x => by
    rw [← two_smul F x, CharTwo.two_eq_zero, zero_smul]
  have hgg : ∀ v, g (g v) = v := fun v => by
    rw [← LinearEquiv.mul_apply, hg]
    rfl
  ext v
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply,
    map_sub, hgg, LinearMap.zero_apply]
  calc v - g v - (g v - v) = (v + v) - (g v + g v) := by abel
    _ = 0 := by rw [h2, h2, sub_zero]

omit [FiniteDimensional F V] [CharP F 2] in
theorem mem_centralizer_iff_commute_sub_id {g h : V ≃ₗ[F] V} :
    h ∈ Subgroup.centralizer {g} ↔
      ∀ v, h (((g : V →ₗ[F] V) - LinearMap.id : V →ₗ[F] V) v) =
        ((g : V →ₗ[F] V) - LinearMap.id : V →ₗ[F] V) (h v) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply, map_sub,
    sub_left_inj]
  constructor
  · intro hc v
    rw [← LinearEquiv.mul_apply, hc, LinearEquiv.mul_apply]
  · intro hc
    apply LinearEquiv.ext
    intro v
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hc]

theorem two_mul_finrank_range_sub_id_le {g : V ≃ₗ[F] V} (hg : g * g = 1) :
    2 * finrank F (LinearMap.range ((g : V →ₗ[F] V) - LinearMap.id)) ≤ finrank F V :=
  two_mul_finrank_range_le_of_comp_eq_zero (sub_id_comp_sub_id_eq_zero hg)

theorem card_centralizer_of_mul_self_eq_one {g : V ≃ₗ[F] V} (hg : g * g = 1) {k m : ℕ}
    (hk : finrank F (LinearMap.range ((g : V →ₗ[F] V) - LinearMap.id)) = k)
    (hm : finrank F V = 2 * k + m) :
    Nat.card (Subgroup.centralizer {g}) =
      Nat.card (GL (Fin k) F) * Nat.card (GL (Fin m) F) * Nat.card F ^ (k * k + m * k + k * m) := by
  rw [← card_commute_of_comp_eq_zero (sub_id_comp_sub_id_eq_zero hg) hk hm]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun h => mem_centralizer_iff_commute_sub_id)

end General

theorem factorization_card_GL_zmod_two (a : ℕ) :
    (Nat.card (GL (Fin a) (ZMod 2))).factorization 2 = a * (a - 1) / 2 := by
  rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_GL_eq, Nat.card_zmod]
  have hodd : ¬ 2 ∣ ∏ j ∈ Finset.Icc 1 a, (2 ^ j - 1) := by
    rw [Prime.dvd_finsetProd_iff Nat.prime_two.prime]
    rintro ⟨j, hj, hdvd⟩
    rw [Finset.mem_Icc] at hj
    have h2 : 2 ∣ 2 ^ j := dvd_pow_self 2 (by omega)
    have h1 : 1 ≤ 2 ^ j := Nat.one_le_two_pow
    generalize 2 ^ j = t at h1 h2 hdvd
    omega
  have hne : ∏ j ∈ Finset.Icc 1 a, (2 ^ j - 1) ≠ 0 := fun h => hodd (h ▸ dvd_zero 2)
  rw [Nat.factorization_mul (pow_ne_zero _ two_ne_zero) hne, Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hodd, add_zero]

section Two

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {g : V ≃ₗ[ZMod 2] V} (hg : g * g = 1) {n k : ℕ} (hn : finrank (ZMod 2) V = n)
  (hk : finrank (ZMod 2) (LinearMap.range ((g : V →ₗ[ZMod 2] V) - LinearMap.id)) = k)
include hg hn hk

theorem two_mul_rank_le_of_involution : 2 * k ≤ n := by
  rw [← hn, ← hk]
  exact two_mul_finrank_range_sub_id_le hg

theorem card_centralizer_involution_eq :
    Nat.card (Subgroup.centralizer {g}) = 2 ^ (k * (2 * n - 3 * k)) *
      Nat.card (GL (Fin k) (ZMod 2)) * Nat.card (GL (Fin (n - 2 * k)) (ZMod 2)) := by
  have h2k := two_mul_rank_le_of_involution hg hn hk
  obtain ⟨m, rfl⟩ : ∃ m, n = 2 * k + m := ⟨n - 2 * k, by omega⟩
  rw [card_centralizer_of_mul_self_eq_one hg hk hn, Nat.card_zmod, Nat.add_sub_cancel_left]
  have e1 : 2 * (2 * k + m) - 3 * k = k + 2 * m := by omega
  rw [e1]
  ring

theorem factorization_card_centralizer_involution :
    (Nat.card (Subgroup.centralizer {g})).factorization 2 =
      k * (2 * n - 3 * k) + k * (k - 1) / 2 + (n - 2 * k) * (n - 2 * k - 1) / 2 := by
  rw [card_centralizer_involution_eq hg hn hk]
  have hGL : ∀ a : ℕ, Nat.card (GL (Fin a) (ZMod 2)) ≠ 0 := fun a => Nat.card_pos.ne'
  rw [Nat.factorization_mul (mul_ne_zero (pow_ne_zero _ two_ne_zero) (hGL k)) (hGL _),
    Nat.factorization_mul (pow_ne_zero _ two_ne_zero) (hGL k), Finsupp.add_apply,
    Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    factorization_card_GL_zmod_two, factorization_card_GL_zmod_two]

theorem factorization_card_centralizer_involution_add :
    (Nat.card (Subgroup.centralizer {g})).factorization 2 + k * (k - 1) / 2 = n * (n - 1) / 2 := by
  rw [factorization_card_centralizer_involution hg hn hk]
  exact centExp_add_choose (two_mul_rank_le_of_involution hg hn hk)

end Two

end CFSG.LargeExtraspecial.GLR
