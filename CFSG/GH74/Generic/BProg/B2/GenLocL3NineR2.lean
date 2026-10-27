module

public import CFSG.GH74.Generic.BProg.B2.GenLocL3NineBase

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 Subgroup CFSG.Blueprint CFSG.GorensteinWalter CFSG.LocalAnalysis.ComponentInitial
  CFSG.ComponentClassification.CatalogueBHigherLinearAction GenLocL3Good GenLocL3Pair GenLocL3Nine GenLocL3Seven
open scoped MatrixGroups

namespace GenLocL3NineR2

variable {K : Type} [Field K]

theorem gammaAct_subtype_rank2 [Finite K] (hK : Nat.card K = 9)
    (D : Subgroup (MulAut (LinearFlag.projectiveSL 3 K))) (hfs : D ≤ frameStab 3 K)
    (hA : IsRank23 ↥D) (h4 : Nat.card ↥D = 4) : gammaAct D.subtype = ⊤ := by
  have hfin : Finite ↥D := Nat.finite_of_card_ne_zero (by rw [h4]; norm_num)
  have hα : D.subtype.range ≤ frameStab 3 K := by rwa [Subgroup.range_subtype]
  have hK' : Nat.card K = 3 ^ 2 := by simpa using hK
  have hsq : ∀ y : D, y * y = 1 := fun y => WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hA.1 y
  have good_ker : ∀ (m : Fin 3) (y : D), y ≠ 1 → restM m ⟨(y : MulAut (LinearFlag.projectiveSL 3 K)), hfs y.2⟩ = 1 →
      gammaAct ((restM m).comp (toFrame D.subtype hα)) = ⊤ := by
    intro m y hy1 hker
    refine gammaAct_eq_top_of_le_ker _ (E := Subgroup.zpowers y) (GenLocL2.adm_zpowers hA.1 h4 hy1) ?_
    rw [Subgroup.zpowers_le]
    exact hker
  have good_ni : ∀ m : Fin 3, ¬ ((restM m).comp (toFrame D.subtype hα)).range ≤
      (MulAut.conj : SL(2, K) →* MulAut SL(2, K)).range →
      gammaAct ((restM m).comp (toFrame D.subtype hα)) = ⊤ := by
    intro m hni
    refine gammaAct_sl2_of_not_inner_small Nat.prime_three (by norm_num) hK' (by norm_num) _ hA hni ?_
    calc Nat.card ((restM m).comp (toFrame D.subtype hα)).range
        ≤ Nat.card D := Nat.card_le_card_of_surjective _ (MonoidHom.rangeRestrict_surjective _)
      _ = 4 := h4
  by_cases hF : ∃ (y : D) (u : Fin 3 → Kˣ) (σ : K ≃+* K) (ε : ℕ), ε ≤ 1 ∧
      (y : MulAut (LinearFlag.projectiveSL 3 K)) = LinearFlag.conjAut 3 K (diag3 u) *
        LinearFlag.fieldAut 3 K σ * LinearFlag.dualAut 3 K ^ ε ∧ σ ≠ 1
  · obtain ⟨y, u, σ, ε, hε, hy, hσ⟩ := hF
    have hni : ∀ m : Fin 3, ¬ ((restM m).comp (toFrame D.subtype hα)).range ≤
        (MulAut.conj : SL(2, K) →* MulAut SL(2, K)).range := fun m h =>
      rho_not_inner_of_field m (hfs y.2) hε hy hσ (h ⟨y, rfl⟩)
    exact gammaAct_eq_top_of_two_good D.subtype hα (m := 0) (m' := 1) (by decide) (good_ni 0 (hni 0))
      (good_ni 1 (hni 1))
  push Not at hF
  have nd : ∀ y : D, (y : MulAut (LinearFlag.projectiveSL 3 K)) ∈ noDual K →
      ∃ u : Fin 3 → Kˣ, (y : MulAut (LinearFlag.projectiveSL 3 K)) = LinearFlag.conjAut 3 K (diag3 u) := by
    intro y hy
    obtain ⟨x, σ, hx, hax⟩ := hy
    obtain ⟨u, rfl⟩ := exists_diag3 hx
    have := hF y u σ 0 (Nat.zero_le 1) (by rw [pow_zero, mul_one]; exact hax)
    refine ⟨u, ?_⟩
    rw [hax, this, map_one, mul_one]
  have blk : ∀ (y : D) (u : Fin 3 → Kˣ), (y : MulAut (LinearFlag.projectiveSL 3 K)) =
      LinearFlag.conjAut 3 K (diag3 u) → ∃ m : Fin 3, u (crd m 0) = u (crd m 1) := by
    intro y u hu
    have h1 : LinearFlag.conjAut 3 K (diag3 u) * LinearFlag.conjAut 3 K (diag3 u) = 1 := by
      rw [← hu]
      exact congrArg Subtype.val (hsq y)
    exact exists_block_eq (sq_equal_of_conjAut_sq u h1)
  by_cases hall : ∀ y : D, (y : MulAut (LinearFlag.projectiveSL 3 K)) ∈ noDual K
  · obtain ⟨a, b, ha, hb, hab, -⟩ := GenLocL2.exists_klein_gens hA.1 h4
    obtain ⟨ua, hua⟩ := nd a (hall a)
    obtain ⟨ub, hub⟩ := nd b (hall b)
    obtain ⟨ma, hma⟩ := blk a ua hua
    obtain ⟨mb, hmb⟩ := blk b ub hub
    have hm : ma ≠ mb := by
      rintro rfl
      apply hab
      have hne : ∀ (y : D) (u : Fin 3 → Kˣ), y ≠ 1 → (y : MulAut (LinearFlag.projectiveSL 3 K)) =
          LinearFlag.conjAut 3 K (diag3 u) → LinearFlag.conjAut 3 K (diag3 u) ≠ 1 := by
        intro y u hy1 hyu h1
        apply hy1
        apply Subtype.ext
        rw [hyu, h1]; rfl
      have e := eq_of_trivial_block ma
        (sq_equal_of_conjAut_sq ua (by rw [← hua]; exact congrArg Subtype.val (hsq a)))
        (sq_equal_of_conjAut_sq ub (by rw [← hub]; exact congrArg Subtype.val (hsq b)))
        hma hmb (hne a ua ha hua) (hne b ub hb hub)
      apply Subtype.ext
      rw [hua, hub, e]
    refine gammaAct_eq_top_of_two_good D.subtype hα hm
      (good_ker ma a ha (rho_eq_one_of_eq ma (hfs a.2) hua hma))
      (good_ker mb b hb (rho_eq_one_of_eq mb (hfs b.2) hub hmb))
  push Not at hall
  obtain ⟨r, hr⟩ := hall
  obtain ⟨u, σ, ε, hε, hru⟩ := exists_data (hfs r.2)
  have hσ : σ = 1 := hF r u σ ε hε hru
  have hε1 : ε = 1 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hε with rfl | rfl
    · exact absurd ⟨diag3 u, σ, isDiag_diag3 u, by rw [hru, pow_zero, mul_one]⟩ hr
    · rfl
  subst hσ hε1
  have hr1 : r ≠ 1 := by
    rintro rfl
    exact hr (one_mem _)
  have hadm := adm_comap_noDual hA.1 D.subtype hα
  obtain ⟨y0, hy0, hy01⟩ : ∃ y0 : D, y0 ∈ (noDual K).comap D.subtype ∧ y0 ≠ 1 := by
    set E0 : Subgroup ↥D := (noDual K).comap D.subtype with hE0
    have hidx : E0.index ≤ 2 := (GenLocBasic.adm_iff_index hA.1 E0).1 hadm
    have h1 := Subgroup.card_mul_index E0
    rw [h4] at h1
    have hlt : 1 < Nat.card E0 := by
      by_contra hle
      push Not at hle
      have : Nat.card E0 * E0.index ≤ 1 * 2 := Nat.mul_le_mul hle hidx
      omega
    obtain ⟨⟨y0, hy0⟩, hne⟩ := (Subgroup.one_lt_card_iff_ne_bot E0).1 hlt |> Subgroup.ne_bot_iff_exists_ne_one.1
    exact ⟨y0, hy0, fun h => hne (Subtype.ext h)⟩
  obtain ⟨u0, hu0⟩ := nd y0 hy0
  obtain ⟨m0, hm0⟩ := blk y0 u0 hu0
  have g0 := good_ker m0 y0 hy01 (rho_eq_one_of_eq m0 (hfs y0.2) hu0 hm0)
  set m1 : Fin 3 := m0 + 1 with hm1
  have hm01 : m0 ≠ m1 := by
    rw [hm1]; fin_cases m0 <;> decide
  by_cases hni : ((restM m1).comp (toFrame D.subtype hα)).range ≤
      (MulAut.conj : SL(2, K) →* MulAut SL(2, K)).range
  ·
    have hin : restM m1 ⟨(r : MulAut (LinearFlag.projectiveSL 3 K)), hfs r.2⟩ ∈
        (MulAut.conj : SL(2, K) →* MulAut SL(2, K)).range := hni ⟨r, rfl⟩
    have hsqr := isSquare_of_rho_inner m1 (hfs r.2) le_rfl hru hin
    obtain ⟨t, ht⟩ := hsqr
    have hk0 : ((u (crd m1 1) : Kˣ) : K) ≠ 0 := (u (crd m1 1)).ne_zero
    have hj0 : ((u (crd m1 0) : Kˣ) : K) ≠ 0 := (u (crd m1 0)).ne_zero
    have ht0 : t ≠ 0 := by
      rintro rfl
      simp at ht
    have hβ : t / (u (crd m1 1) : K) ≠ 0 := div_ne_zero ht0 hk0
    have hrel : (t / (u (crd m1 1) : K)) * (t / (u (crd m1 1) : K)) * (u (crd m1 1) : K) =
        (u (crd m1 0) : K) := by
      field_simp
      linear_combination -ht
    have hfix := fixed_anti_of_reflection m1 (hfs r.2) hru hβ hrel
    have hw : phiM m1 (anti hβ) ∈ gammaAct D.subtype :=
      le_gammaAct D.subtype (GenLocL2.adm_zpowers hA.1 h4 hr1) (GenLocL2.fixedIn_zpowers D.subtype hfix)
    exact gammaAct_eq_top_of_good_mono D.subtype hα hm01 g0 hβ hw
  · exact gammaAct_eq_top_of_two_good D.subtype hα hm01 g0 (good_ni m1 hni)


end GenLocL3NineR2

end CFSG.GH74.Generic.BProg.B2
