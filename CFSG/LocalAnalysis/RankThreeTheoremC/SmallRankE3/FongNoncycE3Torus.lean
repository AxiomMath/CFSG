module

public import CFSG.LocalAnalysis.SectionRank.ClassicalEven.Torus

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongNoncyc

open CFSG.Open CFSG.Assembly.LowTwoRank Matrix CFSG.SectionRank CFSG.SectionRank.ClassicalEven

theorem four_le_pRank_of_gens {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]
    {x y z w : G} (hx : x ^ p = 1) (hy : y ^ p = 1) (hz : z ^ p = 1) (hw : w ^ p = 1)
    (hxy : Commute x y) (hxz : Commute x z) (hxw : Commute x w)
    (hyz : Commute y z) (hyw : Commute y w) (hzw : Commute z w)
    (hx1 : x ≠ 1) (hy1 : ∀ n : ℕ, x ^ n ≠ y) (hz1 : ∀ n m : ℕ, x ^ n * y ^ m ≠ z)
    (hw1 : ∀ n m l : ℕ, x ^ n * y ^ m * z ^ l ≠ w) :
    4 ≤ pRank p (⊤ : Subgroup G) := by
  set B₀ : Subgroup G := ⊥
  have h₀ : ∀ b : B₀, B₀.subtype b = 1 := fun b => Subgroup.mem_bot.1 b.2
  have hc₀ : ∀ a b : B₀, a * b = b * a := fun a b => Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.mem_bot.1 a.2, Subgroup.mem_bot.1 b.2])
  have hp₀ : ∀ a : B₀, a ^ p = 1 := fun a => Subtype.ext (by
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [Subgroup.mem_bot.1 a.2, one_pow])
  have hcard₀ : Nat.card B₀ = p ^ 0 := by rw [pow_zero]; exact Subgroup.card_bot
  obtain ⟨F₁, hF₁, hc₁, hp₁, hcard₁, hr₁⟩ := exists_extend hc₀ hp₀ hcard₀ B₀.subtype
    Subtype.val_injective (y := x) hx (by
      rintro ⟨b, hb⟩
      exact hx1 (hb ▸ h₀ b))
    (fun b => by rw [h₀ b]; exact Commute.one_left x)
  have hr₁' : ∀ a, ∃ n : ℕ, F₁ a = x ^ n := fun a => by
    obtain ⟨b, n, hb⟩ := hr₁ a
    exact ⟨n, by rw [hb, h₀ b, one_mul]⟩
  obtain ⟨F₂, hF₂, hc₂, hp₂, hcard₂, hr₂⟩ := exists_extend hc₁ hp₁ hcard₁ F₁ hF₁ (y := y) hy
    (by
      rintro ⟨a, ha⟩
      obtain ⟨n, hn⟩ := hr₁' a
      exact hy1 n (hn ▸ ha))
    (fun a => by
      obtain ⟨n, hn⟩ := hr₁' a
      rw [hn]
      exact hxy.pow_left n)
  have hr₂' : ∀ a, ∃ n m : ℕ, F₂ a = x ^ n * y ^ m := fun a => by
    obtain ⟨b, m, hb⟩ := hr₂ a
    obtain ⟨n, hn⟩ := hr₁' b
    exact ⟨n, m, by rw [hb, hn]⟩
  obtain ⟨F₃, hF₃, hc₃, hp₃, hcard₃, hr₃⟩ := exists_extend hc₂ hp₂ hcard₂ F₂ hF₂ (y := z) hz
    (by
      rintro ⟨a, ha⟩
      obtain ⟨n, m, hnm⟩ := hr₂' a
      exact hz1 n m (hnm ▸ ha))
    (fun a => by
      obtain ⟨n, m, hnm⟩ := hr₂' a
      rw [hnm]
      exact (hxz.pow_left n).mul_left (hyz.pow_left m))
  have hr₃' : ∀ a, ∃ n m l : ℕ, F₃ a = x ^ n * y ^ m * z ^ l := fun a => by
    obtain ⟨b, l, hb⟩ := hr₃ a
    obtain ⟨n, m, hnm⟩ := hr₂' b
    exact ⟨n, m, l, by rw [hb, hnm]⟩
  obtain ⟨F₄, hF₄, hc₄, hp₄, hcard₄, -⟩ := exists_extend hc₃ hp₃ hcard₃ F₃ hF₃ (y := w) hw
    (by
      rintro ⟨a, ha⟩
      obtain ⟨n, m, l, hnml⟩ := hr₃' a
      exact hw1 n m l (hnml ▸ ha))
    (fun a => by
      obtain ⟨n, m, l, hnml⟩ := hr₃' a
      rw [hnml]
      exact ((hxw.pow_left n).mul_left (hyw.pow_left m)).mul_left (hzw.pow_left l))
  exact le_pRank_of_injective hp.out.one_lt hc₄ hp₄ hcard₄ F₄ hF₄ le_top

theorem four_le_pRank_statedProj {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    [Finite K] {H : Subgroup (GL ι K)} {p : ℕ} [hp : Fact p.Prime] {x y z w : GL ι K}
    (hxH : x ∈ H) (hyH : y ∈ H) (hzH : z ∈ H) (hwH : w ∈ H)
    (hx : x ^ p = 1) (hy : y ^ p = 1) (hz : z ^ p = 1) (hw : w ^ p = 1)
    (hxy : Commute x y) (hxz : Commute x z) (hxw : Commute x w)
    (hyz : Commute y z) (hyw : Commute y w) (hzw : Commute z w)
    (hx1 : x ∉ StatedScalars ι K)
    (hy1 : ∀ n : ℕ, ∀ c ∈ StatedScalars ι K, x ^ n * c ≠ y)
    (hz1 : ∀ n m : ℕ, ∀ c ∈ StatedScalars ι K, x ^ n * y ^ m * c ≠ z)
    (hw1 : ∀ n m l : ℕ, ∀ c ∈ StatedScalars ι K, x ^ n * y ^ m * z ^ l * c ≠ w) :
    4 ≤ pRank p (⊤ : Subgroup (StatedProj H)) := by
  let N := (StatedScalars ι K).subgroupOf H
  let π : H →* StatedProj H := QuotientGroup.mk' N
  have hpow : ∀ (a : GL ι K) (ha : a ∈ H), a ^ p = 1 → π ⟨a, ha⟩ ^ p = 1 := fun a ha h => by
    rw [← map_pow]
    have : (⟨a, ha⟩ : H) ^ p = 1 := Subtype.ext (by rw [SubgroupClass.coe_pow]; exact h)
    rw [this, map_one]
  have hcomm : ∀ (a b : GL ι K) (ha : a ∈ H) (hb : b ∈ H), Commute a b →
      Commute (π ⟨a, ha⟩) (π ⟨b, hb⟩) := fun a b ha hb h =>
    Commute.map (show Commute (⟨a, ha⟩ : H) ⟨b, hb⟩ from Subtype.ext h.eq) π
  have hmem : ∀ u v : H, π u = π v → ((u : GL ι K)⁻¹ * v) ∈ StatedScalars ι K := fun u v h => by
    change QuotientGroup.mk' N u = QuotientGroup.mk' N v at h
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf] at h
    simpa using h
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

theorem four_le_pRank_torus {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    [Finite K] {H : Subgroup (GL ι K)} {ζ : Kˣ} (hζ : orderOf ζ = 3) {i₀ i₁ i₂ i₃ i₄ : ι}
    (h01 : i₀ ≠ i₁) (h02 : i₀ ≠ i₂) (h03 : i₀ ≠ i₃) (h04 : i₀ ≠ i₄)
    (h12 : i₁ ≠ i₂) (h13 : i₁ ≠ i₃) (h14 : i₁ ≠ i₄)
    (h23 : i₂ ≠ i₃) (h24 : i₂ ≠ i₄) (h34 : i₃ ≠ i₄)
    (hH : ∀ j, torusDiag (torusVec ζ j i₄) ∈ H) :
    4 ≤ pRank 3 (⊤ : Subgroup (StatedProj H)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hζ1 : ζ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hζ
    norm_num at hζ
  have hpow (j : ι) : torusDiag (torusVec ζ j i₄) ^ 3 = 1 := by
    rw [← map_pow, torusVec_pow, ← hζ, pow_orderOf_eq_one, torusVec_one, map_one]
  have hcomm (a b : ι → Kˣ) : Commute (torusDiag a) (torusDiag b) :=
    (Commute.all a b).map torusDiag
  have hent {d d' : ι → Kˣ} (h : torusDiag d = torusDiag d') (i : ι) : d i = d' i :=
    congrFun (torusDiag_injective h) i
  refine four_le_pRank_statedProj (p := 3) (hH i₀) (hH i₁) (hH i₂) (hH i₃)
    (hpow i₀) (hpow i₁) (hpow i₂) (hpow i₃)
    (hcomm _ _) (hcomm _ _) (hcomm _ _) (hcomm _ _) (hcomm _ _) (hcomm _ _) ?_ ?_ ?_ ?_
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

theorem psl_four_le_pRank_three {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 5 ≤ n)
    (h3 : 3 ∣ Nat.card Kˣ) : 4 ≤ pRank 3 (⊤ : Subgroup (StatedProj (StatedSL n K))) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 h3
  exact four_le_pRank_torus hζ (i₀ := ⟨0, by omega⟩) (i₁ := ⟨1, by omega⟩)
    (i₂ := ⟨2, by omega⟩) (i₃ := ⟨3, by omega⟩) (i₄ := ⟨4, by omega⟩)
    (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    (by simp) fun j => torusDiag_mem_SL (prod_torusVec ζ j _)

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongNoncyc
