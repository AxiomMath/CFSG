module

public import CFSG.GH74.GLS.LU.Local.FiveFacts

public section

open Subgroup
open scoped Pointwise

namespace CFSG.GH74.GLS.LU.Local.Five

private theorem hinv_le_normalizer {G : Type} [Group G] {H A : Subgroup G} (hA : HInv H A) :
    H ≤ normalizer (A : Set G) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => hA.mem hh hx, fun hx => ?_⟩
  have := hA.mem (inv_mem hh) hx
  simpa [mul_assoc] using this

theorem exists_invariant_sylow {G : Type} [Group G] [Finite G] {H O : Subgroup G}
    (hH : IsPGroup 2 ↥H) (hO : Odd (Nat.card ↥O)) (hHO : HInv H O) (r : ℕ) [Fact r.Prime] :
    ∃ P : Subgroup G, P ≤ O ∧ IsPGroup r ↥P ∧ ¬ r ∣ (P.subgroupOf O).index ∧ HInv H P := by
  classical
  let φ : ↥H →* MulAut ↥O :=
    O.normalizerMonoidHom.comp (Subgroup.inclusion (hinv_le_normalizer hHO))
  let _ : MulAction ↥H (Sylow r ↥O) := MulAction.compHom (Sylow r ↥O) φ
  have hodd : ¬ 2 ∣ Nat.card (Sylow r ↥O) := by
    have h1 : Nat.card (Sylow r ↥O) ∣ Nat.card ↥O :=
      (Sylow.card_dvd_index (default : Sylow r ↥O)).trans (Subgroup.index_dvd_card _)
    intro h2
    exact (Nat.not_even_iff_odd.mpr hO) (even_iff_two_dvd.mpr (h2.trans h1))
  obtain ⟨P₀, hP₀⟩ := hH.nonempty_fixed_point_of_prime_not_dvd_card (Sylow r ↥O) hodd
  have hfix : ∀ (h : ↥H) (x : ↥O), x ∈ (P₀ : Subgroup ↥O) → φ h x ∈ (P₀ : Subgroup ↥O) := by
    intro h x hx
    have e : φ h • P₀ = P₀ := MulAction.mem_fixedPoints.mp hP₀ h
    have hmem : (φ h) • x ∈ (φ h) • (P₀ : Subgroup ↥O) :=
      Subgroup.smul_mem_pointwise_smul x (φ h) _ hx
    rw [← Sylow.pointwise_smul_def, e] at hmem
    exact hmem
  have key : ∀ k ∈ H, ∀ x ∈ (P₀ : Subgroup ↥O).map O.subtype, k * x * k⁻¹ ∈
      (P₀ : Subgroup ↥O).map O.subtype := by
    intro k hk x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    refine Subgroup.mem_map.mpr ⟨φ ⟨k, hk⟩ y, hfix ⟨k, hk⟩ y hy, ?_⟩
    simp [φ]
  refine ⟨(P₀ : Subgroup ↥O).map O.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
  · exact P₀.isPGroup'.of_equiv (Subgroup.equivMapOfInjective _ O.subtype O.subtype_injective)
  · have : ((P₀ : Subgroup ↥O).map O.subtype).subgroupOf O = (P₀ : Subgroup ↥O) :=
      Subgroup.comap_map_eq_self_of_injective O.subtype_injective _
    rw [this]
    exact P₀.not_dvd_index
  · intro h hh
    ext x
    rw [mem_cjL]
    constructor
    · intro hx
      have := key h hh _ hx
      simpa [mul_assoc] using this
    · intro hx
      have := key h⁻¹ (inv_mem hh) x hx
      simpa using this

theorem isPGroup_five_of_noInv {G : Type} [Group G] [Finite G] {H O : Subgroup G}
    (hH : IsPGroup 2 ↥H) (hO : Odd (Nat.card ↥O)) (hHO : HInv H O)
    (hno : ∀ Y : Subgroup G, (∀ y ∈ Y, ¬ 2 ∣ orderOf y ∧ ¬ 5 ∣ orderOf y) → HInv H Y → Y = ⊥) :
    IsPGroup 5 ↥O := by
  have h5 : Nat.Prime 5 := by norm_num
  have hall : ∀ {r : ℕ}, r.Prime → r ∣ Nat.card ↥O → r = 5 := by
    intro r hr hrd
    by_contra hr5
    have : Fact r.Prime := ⟨hr⟩
    have hr2 : r ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hO) (even_iff_two_dvd.mpr hrd)
    obtain ⟨P, hPO, hP, hidx, hPinv⟩ := exists_invariant_sylow hH hO hHO r
    have hPbot : P = ⊥ := by
      refine hno P (fun y hy => ?_) hPinv
      obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hP ⟨y, hy⟩
      have hord : orderOf y = r ^ k := by rw [← hk, Subgroup.orderOf_mk]
      refine ⟨fun h2 => hr2 ?_, fun h2 => hr5 ?_⟩
      · rw [hord] at h2
        exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hr).mp
          (Nat.prime_two.dvd_of_dvd_pow h2)).symm
      · rw [hord] at h2
        exact ((Nat.prime_dvd_prime_iff_eq h5 hr).mp (h5.dvd_of_dvd_pow h2)).symm
    have hrP : r ∣ Nat.card ↥P := by
      have h1 := Subgroup.card_mul_index (P.subgroupOf O)
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPO).toEquiv] at h1
      have : r ∣ Nat.card ↥P * (P.subgroupOf O).index := by rw [h1]; exact hrd
      exact (hr.dvd_mul.mp this).resolve_right hidx
    rw [hPbot, Subgroup.card_bot] at hrP
    exact hr.one_lt.ne' (Nat.dvd_one.mp hrP)
  have : Fact (Nat.Prime 5) := ⟨h5⟩
  exact IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' hall)

end CFSG.GH74.GLS.LU.Local.Five
