module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongNoncycE3Torus

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent.CentralThree

open CFSG.Open Matrix CFSG.SectionRank.ClassicalEven
open CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongNoncyc

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

theorem four_le_pRank_of_scalarKer {H : Subgroup (GL ι K)} {Q : Type*} [Group Q] [Finite Q]
    (π : H →* Q) (hπ : π.ker ≤ (StatedScalars ι K).subgroupOf H) {p : ℕ} [hp : Fact p.Prime]
    {x y z w : GL ι K} (hxH : x ∈ H) (hyH : y ∈ H) (hzH : z ∈ H) (hwH : w ∈ H)
    (hx : x ^ p = 1) (hy : y ^ p = 1) (hz : z ^ p = 1) (hw : w ^ p = 1)
    (hxy : Commute x y) (hxz : Commute x z) (hxw : Commute x w)
    (hyz : Commute y z) (hyw : Commute y w) (hzw : Commute z w)
    (hx1 : x ∉ StatedScalars ι K)
    (hy1 : ∀ n : ℕ, ∀ c ∈ StatedScalars ι K, x ^ n * c ≠ y)
    (hz1 : ∀ n m : ℕ, ∀ c ∈ StatedScalars ι K, x ^ n * y ^ m * c ≠ z)
    (hw1 : ∀ n m l : ℕ, ∀ c ∈ StatedScalars ι K, x ^ n * y ^ m * z ^ l * c ≠ w) :
    4 ≤ pRank p (⊤ : Subgroup Q) := by
  have hpow : ∀ (a : GL ι K) (ha : a ∈ H), a ^ p = 1 → π ⟨a, ha⟩ ^ p = 1 := fun a ha h => by
    rw [← map_pow]
    have : (⟨a, ha⟩ : H) ^ p = 1 := Subtype.ext (by rw [SubgroupClass.coe_pow]; exact h)
    rw [this, map_one]
  have hcomm : ∀ (a b : GL ι K) (ha : a ∈ H) (hb : b ∈ H), Commute a b →
      Commute (π ⟨a, ha⟩) (π ⟨b, hb⟩) := fun a b ha hb h =>
    Commute.map (show Commute (⟨a, ha⟩ : H) ⟨b, hb⟩ from Subtype.ext h.eq) π
  have hmem : ∀ u v : H, π u = π v → ((u : GL ι K)⁻¹ * v) ∈ StatedScalars ι K := fun u v h => by
    have hk : u⁻¹ * v ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
    have := hπ hk
    rw [Subgroup.mem_subgroupOf] at this
    simpa using this
  refine four_le_pRank_of_gens (hpow x hxH hx) (hpow y hyH hy) (hpow z hzH hz) (hpow w hwH hw)
    (hcomm _ _ _ _ hxy) (hcomm _ _ _ _ hxz) (hcomm _ _ _ _ hxw)
    (hcomm _ _ _ _ hyz) (hcomm _ _ _ _ hyw) (hcomm _ _ _ _ hzw)
    (fun h => hx1 ?_) (fun n h => ?_) (fun n m h => ?_) (fun n m l h => ?_)
  · have := hmem _ _ (h.trans (map_one π).symm)
    simpa using this
  · rw [← map_pow] at h
    have := hmem _ _ h
    simp only [SubgroupClass.coe_pow] at this
    exact hy1 n _ this (mul_inv_cancel_left _ _)
  · rw [← map_pow, ← map_pow, ← map_mul] at h
    have := hmem _ _ h
    simp only [Subgroup.coe_mul, SubgroupClass.coe_pow] at this
    exact hz1 n m _ this (mul_inv_cancel_left _ _)
  · rw [← map_pow, ← map_pow, ← map_pow, ← map_mul, ← map_mul] at h
    have := hmem _ _ h
    simp only [Subgroup.coe_mul, SubgroupClass.coe_pow] at this
    exact hw1 n m l _ this (mul_inv_cancel_left _ _)

variable [Finite K]

theorem torusVec_indep {ζ : Kˣ} (hζ : orderOf ζ = 3) {i₀ i₁ i₂ i₃ i₄ : ι}
    (h01 : i₀ ≠ i₁) (h02 : i₀ ≠ i₂) (h03 : i₀ ≠ i₃) (h04 : i₀ ≠ i₄)
    (h12 : i₁ ≠ i₂) (h13 : i₁ ≠ i₃) (h14 : i₁ ≠ i₄)
    (h23 : i₂ ≠ i₃) (h24 : i₂ ≠ i₄) (h34 : i₃ ≠ i₄) :
    torusDiag (torusVec ζ i₀ i₄) ∉ StatedScalars ι K ∧
    (∀ n : ℕ, ∀ c ∈ StatedScalars ι K,
      torusDiag (torusVec ζ i₀ i₄) ^ n * c ≠ torusDiag (torusVec ζ i₁ i₄)) ∧
    (∀ n m : ℕ, ∀ c ∈ StatedScalars ι K, torusDiag (torusVec ζ i₀ i₄) ^ n *
      torusDiag (torusVec ζ i₁ i₄) ^ m * c ≠ torusDiag (torusVec ζ i₂ i₄)) ∧
    (∀ n m l : ℕ, ∀ c ∈ StatedScalars ι K, torusDiag (torusVec ζ i₀ i₄) ^ n *
      torusDiag (torusVec ζ i₁ i₄) ^ m * torusDiag (torusVec ζ i₂ i₄) ^ l * c ≠
        torusDiag (torusVec ζ i₃ i₄)) := by
  have hζ1 : ζ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hζ
    norm_num at hζ
  have hent {d d' : ι → Kˣ} (h : torusDiag d = torusDiag d') (i : ι) : d i = d' i :=
    congrFun (torusDiag_injective h) i
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro ⟨c, hc⟩
    rw [scalar_eq_torusDiag] at hc
    have e0 := hent hc i₀
    have e1 := hent hc i₁
    rw [torusVec_apply_left ζ h04] at e0
    rw [torusVec_apply_of_ne ζ h01.symm h14] at e1
    exact hζ1 (e0.symm.trans e1)
  · rintro a _ ⟨c, rfl⟩ h
    rw [← map_pow, torusVec_pow, scalar_eq_torusDiag, ← map_mul] at h
    have e1 := hent h i₁
    have e2 := hent h i₂
    simp only [Pi.mul_apply, one_mul, torusVec_apply_of_ne _ h01.symm h14,
      torusVec_apply_left _ h14, torusVec_apply_of_ne _ h02.symm h24,
      torusVec_apply_of_ne _ h12.symm h24] at e1 e2
    exact hζ1 (e1.symm.trans e2)
  · rintro a b _ ⟨c, rfl⟩ h
    rw [← map_pow, ← map_pow, torusVec_pow, torusVec_pow, scalar_eq_torusDiag, ← map_mul,
      ← map_mul] at h
    have e2 := hent h i₂
    have e3 := hent h i₃
    simp only [Pi.mul_apply, one_mul, torusVec_apply_left _ h24,
      torusVec_apply_of_ne _ h02.symm h24, torusVec_apply_of_ne _ h12.symm h24,
      torusVec_apply_of_ne _ h03.symm h34, torusVec_apply_of_ne _ h13.symm h34,
      torusVec_apply_of_ne _ h23.symm h34] at e2 e3
    exact hζ1 (e2.symm.trans e3)
  · rintro a b l _ ⟨c, rfl⟩ h
    rw [← map_pow, ← map_pow, ← map_pow, torusVec_pow, torusVec_pow, torusVec_pow,
      scalar_eq_torusDiag, ← map_mul, ← map_mul, ← map_mul] at h
    have e0 := hent h i₀
    have e1 := hent h i₁
    have e2 := hent h i₂
    have e3 := hent h i₃
    have e4 := hent h i₄
    simp only [Pi.mul_apply, one_mul, mul_one, torusVec_apply_left _ h04,
      torusVec_apply_left _ h14, torusVec_apply_left _ h24, torusVec_apply_left _ h34,
      torusVec_apply_right _ h04, torusVec_apply_right _ h14, torusVec_apply_right _ h24,
      torusVec_apply_right _ h34, torusVec_apply_of_ne _ h01 h04,
      torusVec_apply_of_ne _ h02 h04, torusVec_apply_of_ne _ h03 h04,
      torusVec_apply_of_ne _ h01.symm h14, torusVec_apply_of_ne _ h12 h14,
      torusVec_apply_of_ne _ h13 h14, torusVec_apply_of_ne _ h02.symm h24,
      torusVec_apply_of_ne _ h12.symm h24, torusVec_apply_of_ne _ h23 h24,
      torusVec_apply_of_ne _ h03.symm h34, torusVec_apply_of_ne _ h13.symm h34,
      torusVec_apply_of_ne _ h23.symm h34] at e0 e1 e2 e3 e4
    rw [e3] at e0 e1 e2 e4
    rw [inv_eq_of_mul_eq_one_right e0, inv_eq_of_mul_eq_one_right e1,
      inv_eq_of_mul_eq_one_right e2] at e4
    have h5 : ζ ^ 5 = 1 := by
      rw [pow_succ, pow_succ, pow_succ, pow_succ, pow_one, e4, inv_mul_cancel]
    have hdvd : orderOf ζ ∣ 5 := orderOf_dvd_of_pow_eq_one h5
    rw [hζ] at hdvd
    norm_num at hdvd

theorem four_le_pRank_torus_of_scalarKer {H : Subgroup (GL ι K)} {Q : Type*} [Group Q] [Finite Q]
    (π : H →* Q) (hπ : π.ker ≤ (StatedScalars ι K).subgroupOf H) {ζ : Kˣ} (hζ : orderOf ζ = 3)
    {i₀ i₁ i₂ i₃ i₄ : ι}
    (h01 : i₀ ≠ i₁) (h02 : i₀ ≠ i₂) (h03 : i₀ ≠ i₃) (h04 : i₀ ≠ i₄)
    (h12 : i₁ ≠ i₂) (h13 : i₁ ≠ i₃) (h14 : i₁ ≠ i₄)
    (h23 : i₂ ≠ i₃) (h24 : i₂ ≠ i₄) (h34 : i₃ ≠ i₄)
    (hH : ∀ j, torusDiag (torusVec ζ j i₄) ∈ H) : 4 ≤ pRank 3 (⊤ : Subgroup Q) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hpow (j : ι) : torusDiag (torusVec ζ j i₄) ^ 3 = 1 := by
    rw [← map_pow, torusVec_pow, ← hζ, pow_orderOf_eq_one, torusVec_one, map_one]
  have hcomm (a b : ι → Kˣ) : Commute (torusDiag a) (torusDiag b) :=
    (Commute.all a b).map torusDiag
  obtain ⟨hx1, hy1, hz1, hw1⟩ :=
    torusVec_indep hζ h01 h02 h03 h04 h12 h13 h14 h23 h24 h34 (K := K)
  exact four_le_pRank_of_scalarKer π hπ (p := 3) (hH i₀) (hH i₁) (hH i₂) (hH i₃)
    (hpow i₀) (hpow i₁) (hpow i₂) (hpow i₃)
    (hcomm _ _) (hcomm _ _) (hcomm _ _) (hcomm _ _) (hcomm _ _) (hcomm _ _) hx1 hy1 hz1 hw1

end CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent.CentralThree
