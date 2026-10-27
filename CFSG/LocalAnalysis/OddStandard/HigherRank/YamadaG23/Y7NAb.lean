module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7NIn

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G]

theorem y7n_aut_bound (h29 : Aut29Idx) {Lam : Subgroup G} (hext : Sec2.IsExt26 1 ↥Lam)
    (hns : ¬ SplitsOver (⊤ : Subgroup ↥Lam) (pCoreOf 2 (⊤ : Subgroup ↥Lam)))
    (hcard : Nat.card ↥Lam = 1344)
    (hcenter : ∀ x ∈ Lam, (∀ y ∈ Lam, y * x = x * y) → x = 1)
    {Z : Subgroup G} (hZ : IsPGroup 2 Z) (hN : Z ≤ normalizer (Lam : Set G)) :
    Nat.card ↥Z ≤ 2 ^ 7 * Nat.card ↥(Z ⊓ centralizer (Lam : Set G)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hfinAut : Finite (MulAut ↥Lam) :=
    Finite.of_injective (fun f : MulAut ↥Lam => (f : ↥Lam → ↥Lam)) (by
      intro f g h
      ext x
      simpa using congrFun h x)
  let ρ : ↥Z →* MulAut ↥Lam := Lam.normalizerMonoidHom.comp (Subgroup.inclusion hN)
  have hcenter_bot : Subgroup.center ↥Lam = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    exact hcenter x.1 x.2 (fun y hy => by
      have := Subgroup.mem_center_iff.1 hx ⟨y, hy⟩
      simpa using congrArg (fun t : ↥Lam => (t : G)) this)
  have hker_conj : (MulAut.conj : ↥Lam →* MulAut ↥Lam).ker = Subgroup.center ↥Lam := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
    constructor
    · intro h y
      have hy : x * y * x⁻¹ = y := by
        simpa [MulAut.conj_apply] using congrArg (fun β : MulAut ↥Lam => β y) h
      calc y * x = (x * y * x⁻¹) * x := by rw [hy]
        _ = x * y := by group
    · intro h
      ext y
      rw [MulAut.conj_apply, ← h y]
      simp
  have hconj_inj : Function.Injective (MulAut.conj : ↥Lam →* MulAut ↥Lam) := by
    rw [← MonoidHom.ker_eq_bot_iff, hker_conj, hcenter_bot]
  have hcard_inner : Nat.card (innerAut ↥Lam) = 1344 := by
    rw [innerAut]
    exact (Nat.card_range_of_injective hconj_inj).trans hcard
  have hidx : (innerAut ↥Lam).index ≤ 2 := h29 ↥Lam hext hns
  have hidx_pos : 1 ≤ (innerAut ↥Lam).index :=
    Nat.one_le_iff_ne_zero.mpr Subgroup.index_ne_zero_of_finite
  have hidx12 : (innerAut ↥Lam).index = 1 ∨ (innerAut ↥Lam).index = 2 := by omega
  have hker_eq : ρ.ker = (Z ⊓ centralizer (Lam : Set G)).subgroupOf Z := by
    change (Lam.normalizerMonoidHom.comp (Subgroup.inclusion hN)).ker = _
    rw [← MonoidHom.comap_ker, Subgroup.normalizerMonoidHom_ker,
      Subgroup.comap_inclusion_subgroupOf hN (centralizer (Lam : Set G))]
    exact (Subgroup.inf_subgroupOf_left (centralizer (Lam : Set G)) Z).symm
  have hker_card : Nat.card ↥ρ.ker = Nat.card ↥(Z ⊓ centralizer (Lam : Set G)) := by
    rw [hker_eq]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hrange_pg : IsPGroup 2 ↥ρ.range :=
    hZ.of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
  obtain ⟨k, hk⟩ := hrange_pg.exists_card_eq
  have hcardAut : Nat.card (MulAut ↥Lam) = (innerAut ↥Lam).index * 1344 := by
    rw [← Subgroup.index_mul_card (innerAut ↥Lam), hcard_inner]
  have hdvd : 2 ^ k ∣ (innerAut ↥Lam).index * 1344 := by
    rw [← hk, ← hcardAut]
    exact Subgroup.card_subgroup_dvd_card ρ.range
  have hk7 : k ≤ 7 := by
    have hcop : Nat.Coprime (2 ^ k) 21 := (by norm_num : Nat.Coprime 2 21).pow_left k
    have hdvd2 : 2 ^ k ∣ 2 * 1344 := by
      rcases hidx12 with h1 | h2
      · rw [h1, one_mul] at hdvd
        exact hdvd.trans (dvd_mul_left 1344 2)
      · rwa [h2] at hdvd
    have h2688 : (2 * 1344 : ℕ) = 2 ^ 7 * 21 := by norm_num
    rw [h2688] at hdvd2
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp
      (hcop.dvd_of_dvd_mul_right hdvd2)
  have hZcard : Nat.card ↥Z = Nat.card ↥ρ.range * Nat.card ↥ρ.ker := by
    rw [← Subgroup.card_ker_mul_card_range ρ, mul_comm]
  calc
    Nat.card ↥Z = Nat.card ↥ρ.range * Nat.card ↥ρ.ker := hZcard
    _ = 2 ^ k * Nat.card ↥(Z ⊓ centralizer (Lam : Set G)) := by rw [hk, hker_card]
    _ ≤ 2 ^ 7 * Nat.card ↥(Z ⊓ centralizer (Lam : Set G)) :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hk7)

end CFSG.OddStandard.HigherRank.YamadaG23
