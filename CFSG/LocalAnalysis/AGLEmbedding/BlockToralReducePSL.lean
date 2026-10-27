module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralReduceRank
public import CFSG.LocalAnalysis.AGLEmbedding.LinearThreeKitCycle

public section

namespace CFSG.AGLEmbedding

open CFSG.LocalAnalysis.ComponentInitial LinearFlag

namespace ToralReduce

variable {K : Type} [Field K]

theorem three_ne_zero_of_charTwo [CharP K 2] : (3 : K) ≠ 0 := by
  have h := CharP.cast_eq_zero_iff K 2 3
  norm_num at h
  exact h

theorem scalars_eq_bot_of_not_dvd [Finite K] (h : ¬ 3 ∣ Nat.card K - 1) : scalars 3 K = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  obtain ⟨c, hc, hgc⟩ := mem_scalars.mp hg
  have hc1 : c = 1 := by
    have h1 : orderOf c ∣ 3 := orderOf_dvd_of_pow_eq_one hc
    have h2 : orderOf c ∣ Nat.card K - 1 := Nat.card_units K ▸ orderOf_dvd_natCard c
    rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h3 | h3
    · exact orderOf_eq_one_iff.mp h3
    · exact absurd (h3 ▸ h2) h
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [hgc, hc1, Units.val_one, map_one, Matrix.SpecialLinearGroup.coe_one]

theorem proj_injective_of_not_dvd [Finite K] (h : ¬ 3 ∣ Nat.card K - 1) :
    Function.Injective (proj 3 K) := by
  rw [← MonoidHom.ker_eq_bot_iff, ker_proj, scalars_eq_bot_of_not_dvd h]

theorem exists_cube_root_of_dvd [Finite K] (h : 3 ∣ Nat.card K - 1) :
    ∃ ω : K, ω ≠ 1 ∧ ω ^ 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 (by rwa [Nat.card_units])
  refine ⟨(c : K), fun h1 => ?_, ?_⟩
  · have : c = 1 := Units.ext h1
    rw [this, orderOf_one] at hc
    exact absurd hc (by norm_num)
  · rw [← Units.val_pow_eq_pow_val, ← hc, pow_orderOf_eq_one, Units.val_one]

theorem card_le_nine_of_not_dvd [Finite K] [CharP K 2] (h : ¬ 3 ∣ Nat.card K - 1)
    {Eb : Subgroup (projectiveSL 3 K)} (hc : ∀ x ∈ Eb, ∀ y ∈ Eb, x * y = y * x)
    (hexp : ∀ x ∈ Eb, x ^ 3 = 1) : Nat.card Eb ≤ 3 ^ 2 := by
  have hinj := proj_injective_of_not_dvd h
  have hmap : (Eb.comap (proj 3 K)).map (proj 3 K) = Eb :=
    Subgroup.map_comap_eq_self_of_surjective (proj_surjective 3 K) Eb
  rw [← hmap, Subgroup.card_map_of_injective hinj]
  refine card_le_sq_of_commute Nat.prime_three (by norm_num) three_ne_zero_of_charTwo
    (fun a ha b hb => hinj ?_) fun g hg => hinj ?_
  · rw [map_mul, map_mul]
    exact hc _ ha _ hb
  · rw [map_pow, map_one]
    exact hexp _ hg

theorem mem_zpowers_of_commute_of_not_dvd [Finite K] [CharP K 2] (h : ¬ 3 ∣ Nat.card K - 1)
    {x y : projectiveSL 3 K} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) (hy3 : y ^ 3 = 1)
    (hxy : x * y = y * x) : y ∈ Subgroup.zpowers x := by
  have : Fintype K := Fintype.ofFinite K
  have hinj := proj_injective_of_not_dvd h
  obtain ⟨u, rfl⟩ := proj_surjective 3 K x
  obtain ⟨v, rfl⟩ := proj_surjective 3 K y
  have hu3 : u ^ 3 = 1 := hinj (by rw [map_pow, hx3, map_one])
  have hv3 : v ^ 3 = 1 := hinj (by rw [map_pow, hy3, map_one])
  have hu1 : u ≠ 1 := fun h1 => hx1 (by rw [h1, map_one])
  have huv : v ∈ Subgroup.centralizer ({u} : Set (Matrix.SpecialLinearGroup (Fin 3) K)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    rw [Set.mem_singleton_iff.mp hk]
    exact hinj (by rw [map_mul, map_mul, hxy])
  have hus : u ∉ scalars 3 K := by
    rw [scalars_eq_bot_of_not_dvd h, Subgroup.mem_bot]
    exact hu1
  obtain ⟨w, hw0, hw⟩ := LinearThreeKit.exists_mulVec_eq_smul_of_pow_three
    (LinearThreeKit.coe_pow_eq_one hu3) u.prop (LinearThreeKit.ne_smul_one_of_notMem_scalars hus)
    (one_pow 3)
  have hfl := isFixedLine_of_fixed (by decide : Odd 3) three_ne_zero_of_charTwo hu3 hu1 hw0
    (by simpa using hw)
  have hz := hfl.mem_zpowers_of_not_dvd Nat.prime_three
    (by rwa [← Nat.card_eq_fintype_card]) huv hv3
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  exact ⟨k, by rw [map_zpow]⟩

end ToralReduce

end CFSG.AGLEmbedding
