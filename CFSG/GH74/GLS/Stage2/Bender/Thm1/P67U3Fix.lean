module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67U3Coord
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSemilinearAut

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Matrix CFSG CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

section Fix

variable {p f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData p f K}

theorem u3_conj_eq_of_fix {x₀ : semilinearSimilitudes h 1 1} {g : hypSU h 1 1}
    (hg : g ∈ hypUnitriangular h 1 1)
    (hfix : semilinearAutHom h (le_refl 1) (le_refl 1) x₀ (hypProj h 1 1 g) = hypProj h 1 1 g) :
    (x₀ : SemiGL (HypIndex 1 1) K).left * glAut (x₀ : SemiGL (HypIndex 1 1) K).right
        (g : GL (HypIndex 1 1) K) * (x₀ : SemiGL (HypIndex 1 1) K).left⁻¹ =
      (g : GL (HypIndex 1 1) K) := by
  classical
  have hpp : p.Prime := h.prime
  have : Fact p.Prime := ⟨hpp⟩
  set A : GL (HypIndex 1 1) K := (x₀ : SemiGL (HypIndex 1 1) K).left with hA
  set σ : K ≃+* K := (x₀ : SemiGL (HypIndex 1 1) K).right with hσ
  set ψ : hypSU h 1 1 :=
    ⟨A * glAut σ (g : GL (HypIndex 1 1) K) * A⁻¹, conj_mem_hypSU x₀.2 g⟩ with hψ
  rw [semilinearAutHom_apply h (le_refl 1) (le_refl 1) x₀ g] at hfix
  have hs : ψ⁻¹ * g ∈ hypScalars h 1 1 := by
    have := QuotientGroup.eq.mp hfix
    exact this
  obtain ⟨hcard, -, -, -, -, -, -⟩ := unitary_order_and_Sylow h (r := 1) (ε := 1) le_rfl le_rfl
  set N : ℕ := Nat.card (hypUnitriangular h 1 1) with hN
  have hNp : N = p ^ (3 * f) := by
    rw [hcard, ← pow_mul]
    norm_num [mul_comm]
  have hgN : g ^ N = 1 := by
    have := pow_card_eq_one' (G := hypUnitriangular h 1 1) (x := ⟨g, hg⟩)
    exact congrArg Subtype.val this
  have hψN : ψ ^ N = 1 := by
    apply Subtype.ext
    have h1 : (g : GL (HypIndex 1 1) K) ^ N = 1 := by
      have := congrArg Subtype.val hgN
      simpa using this
    have h2 : A * glAut σ (g : GL (HypIndex 1 1) K) * A⁻¹ =
        (MulAut.conj A) (glAut σ (g : GL (HypIndex 1 1) K)) := by
      simp [MulAut.conj_apply]
    change (A * glAut σ (g : GL (HypIndex 1 1) K) * A⁻¹) ^ N = 1
    rw [h2, ← map_pow, ← map_pow, h1, map_one, map_one]
  have hcent : ψ⁻¹ * g ∈ Subgroup.center (hypSU h 1 1) :=
    normOneScalars_le_center h (hypSU h 1 1) (2 * 1 + 1) hs
  have hcomm : Commute ψ (ψ⁻¹ * g) := Subgroup.mem_center_iff.mp hcent ψ
  have hsN : (ψ⁻¹ * g) ^ N = 1 := by
    have h1 : g ^ N = ψ ^ N * (ψ⁻¹ * g) ^ N := by
      rw [← hcomm.mul_pow]
      congr 1
      group
    rw [h1, hψN, one_mul] at hgN
    exact hgN
  set s : ↥(hypScalars h 1 1) := ⟨ψ⁻¹ * g, hs⟩ with hsdef
  have hsN' : s ^ N = 1 := Subtype.ext hsN
  have hZp : ¬ p ∣ Nat.card (hypScalars h 1 1) := by
    rw [card_hypScalars h (by norm_num)]
    exact not_dvd_gcd_pow_add_one h _
  have hcop : Nat.Coprime (Nat.card (hypScalars h 1 1)) N := by
    rw [hNp]
    exact Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd hpp).mpr hZp).symm
  have hs1 : s = 1 := by
    have hord := Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_natCard s)
      (orderOf_dvd_of_pow_eq_one hsN')
    exact orderOf_eq_one_iff.mp hord
  have hψg : ψ⁻¹ * g = 1 := congrArg Subtype.val hs1
  have : ψ = g := by
    have := congrArg (fun t => ψ * t) hψg
    simpa using this.symm
  exact congrArg Subtype.val this


theorem u3_fix_matrix_eq {x₀ : semilinearSimilitudes h 1 1} {g : hypSU h 1 1}
    (hg : g ∈ hypUnitriangular h 1 1) {α β : K}
    (hgM : ((g : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) = u3Mat h α β)
    (hfix : semilinearAutHom h (le_refl 1) (le_refl 1) x₀ (hypProj h 1 1 g) = hypProj h 1 1 g) :
    (((x₀ : SemiGL (HypIndex 1 1) K).left : GL (HypIndex 1 1) K) :
        Matrix (HypIndex 1 1) (HypIndex 1 1) K) *
      u3Mat h ((x₀ : SemiGL (HypIndex 1 1) K).right α) ((x₀ : SemiGL (HypIndex 1 1) K).right β) =
    u3Mat h α β * (((x₀ : SemiGL (HypIndex 1 1) K).left : GL (HypIndex 1 1) K) :
        Matrix (HypIndex 1 1) (HypIndex 1 1) K) := by
  have h1 := mul_inv_eq_iff_eq_mul.mp (u3_conj_eq_of_fix hg hfix)
  have h2 := congrArg
    (fun t : GL (HypIndex 1 1) K => (t : Matrix (HypIndex 1 1) (HypIndex 1 1) K)) h1
  simp only [Units.val_mul, coe_glAut] at h2
  rw [hgM, uMat_map] at h2
  exact h2


theorem u3_aut_eq_one (hp : p ≠ 2) {z : MulAut (hypPSU h 1 1)} (hodd : Odd (orderOf z))
    (hcop : Nat.Coprime (orderOf z) p)
    (hcen : ∀ g : hypSU h 1 1, g ∈ hypUnitriangular h 1 1 → ∀ β : K,
      ((g : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) = u3Mat h 0 β →
        z (hypProj h 1 1 g) = hypProj h 1 1 g)
    {α₁ β₁ : K} (hα₁ : α₁ ≠ 0) {g₁ : hypSU h 1 1} (hg₁ : g₁ ∈ hypUnitriangular h 1 1)
    (hg₁M : ((g₁ : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) = u3Mat h α₁ β₁)
    (hfix₁ : z (hypProj h 1 1 g₁) = hypProj h 1 1 g₁) : z = 1 := by
  classical
  have hpp : p.Prime := h.prime
  have : Fact p.Prime := ⟨hpp⟩
  have : Finite K := h.finite
  have : CharP K p := h.charP
  obtain ⟨x₀, hx₀⟩ := semilinearAutHom_surjective h (le_refl 1) (le_refl 1) hp (by norm_num) z
  set A : GL (HypIndex 1 1) K := (x₀ : SemiGL (HypIndex 1 1) K).left with hA
  set σ : K ≃+* K := (x₀ : SemiGL (HypIndex 1 1) K).right with hσ
  have hcentral : ∀ β : K, β + h.bar β = 0 → β ≠ 0 →
      (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K) (.inr (.inl 0)) (.inl 0) = 0 ∧
      (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K) (.inr (.inr 0)) (.inl 0) = 0 ∧
      (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K) (.inr (.inr 0)) (.inr (.inl 0)) = 0 ∧
      σ β * (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K) (.inl 0) (.inl 0) =
        β * (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K) (.inr (.inr 0)) (.inr (.inr 0)) := by
    intro β hβ hβ0
    obtain ⟨g, hg, hgM⟩ := exists_mem_of_uMat (h := h) (α := 0) (β := β) (by simpa using hβ)
    have hfix := hcen g hg β hgM
    rw [← hx₀] at hfix
    have heq := u3_fix_matrix_eq hg hgM hfix
    rw [map_zero] at heq
    exact u3_fix_entries_central hβ0 (fun h0 => hβ0 (σ.injective (by rw [h0, map_zero]))) heq
  obtain ⟨β₀, hβ₀E, hβ₀0⟩ := exists_mem_traceZero_ne_zero' h
  have hβ₀ : β₀ + h.bar β₀ = 0 := hβ₀E
  obtain ⟨hwe, hfe, hfw, hrel₀⟩ := hcentral β₀ hβ₀ hβ₀0
  have hAtri : (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K).BlockTriangular fullPos :=
    u3_blockTriangular_of_hyp3 hwe hfe hfw
  have hAff : (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K) (.inr (.inr 0)) (.inr (.inr 0)) ≠ 0 :=
    u3_diag_ne_zero_of_blockTriangular hAtri _
  have hσF : ∀ c : K, h.bar c = c → σ c = c := by
    intro c hc
    by_cases hc0 : c = 0
    · rw [hc0, map_zero]
    · have hβ : β₀ * c + h.bar (β₀ * c) = 0 := by
        rw [map_mul, hc, ← add_mul, hβ₀, zero_mul]
      have hβ0 : β₀ * c ≠ 0 := mul_ne_zero hβ₀0 hc0
      obtain ⟨-, -, -, hrel⟩ := hcentral (β₀ * c) hβ hβ0
      rw [map_mul] at hrel
      have : β₀ * (σ c - c) * (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K) (.inr (.inr 0))
          (.inr (.inr 0)) = 0 := by
        linear_combination hrel - (σ c) * hrel₀
      rcases mul_eq_zero.mp this with h1 | h1
      · rcases mul_eq_zero.mp h1 with h2 | h2
        · exact absurd h2 hβ₀0
        · exact sub_eq_zero.mp h2
      · exact absurd h1 hAff
  have hσσ : σ * σ = 1 := by
    ext x
    have ht : σ (x + h.bar x) = x + h.bar x := hσF _ (by rw [map_add, h.bar_bar, add_comm])
    have hn : σ (x * h.bar x) = x * h.bar x := hσF _ (by rw [map_mul, h.bar_bar, mul_comm])
    have h0 : x * x - (x + h.bar x) * x + x * h.bar x = 0 := by ring
    have h3 := congrArg σ h0
    have h1 : σ ((x + h.bar x) * x) = (x + h.bar x) * σ x := by rw [map_mul, ht]
    rw [map_add, map_sub, h1, map_mul σ x x, hn, map_zero] at h3
    have hq : (σ x - x) * (σ x - h.bar x) = 0 := by linear_combination h3
    rcases mul_eq_zero.mp hq with h4 | h4
    · have h5 : σ x = x := sub_eq_zero.mp h4
      change σ (σ x) = x
      rw [h5, h5]
    · have h5 : σ x = h.bar x := sub_eq_zero.mp h4
      change σ (σ x) = x
      rw [h5, map_bar_comm h σ x, h5, h.bar_bar]
  have hσ1 : σ = 1 := by
    obtain ⟨k, hk⟩ := hodd
    have hzm : z ^ orderOf z = 1 := pow_orderOf_eq_one z
    have hxm : semilinearAutHom h (le_refl 1) (le_refl 1) (x₀ ^ orderOf z) = 1 := by
      rw [map_pow, hx₀, hzm]
    have hσm : σ ^ orderOf z = 1 := by
      have h1 := ((semilinearAutHom_eq_one_iff h (le_refl 1) (le_refl 1) (by norm_num) _).mp hxm).1
      have h2 : (((x₀ ^ orderOf z : semilinearSimilitudes h 1 1)) : SemiGL (HypIndex 1 1) K).right =
          σ ^ orderOf z := by
        rw [Subgroup.coe_pow]
        exact map_pow SemidirectProduct.rightHom _ _
      rw [h2] at h1
      exact h1
    rw [hk, pow_succ, pow_mul, sq, hσσ, one_pow, one_mul] at hσm
    exact hσm
  have hσc : ∀ c, σ c = c := fun c => by rw [hσ1]; rfl
  have hfix1 := hfix₁
  rw [← hx₀] at hfix1
  have heq1 := u3_fix_matrix_eq hg₁ hg₁M hfix1
  rw [hσc α₁, hσc β₁] at heq1
  obtain ⟨-, -, -, hrw, hrf⟩ := u3_fix_entries_regular hα₁ heq1
  have hbα : h.bar α₁ ≠ 0 := fun h0 => hα₁ (h.bar.injective (by rw [h0, map_zero]))
  have hee_ww : (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K) (.inl 0) (.inl 0) =
      (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K) (.inr (.inl 0)) (.inr (.inl 0)) :=
    mul_left_cancel₀ hα₁ hrw
  have hww_ff : (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K) (.inr (.inl 0)) (.inr (.inl 0)) =
      (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K) (.inr (.inr 0)) (.inr (.inr 0)) :=
    mul_left_cancel₀ hbα hrf
  set a : K := (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K) (.inl 0) (.inl 0) with ha
  have ha0 : a ≠ 0 := u3_diag_ne_zero_of_blockTriangular hAtri _
  set au : Kˣ := Units.mk0 a ha0 with hau
  have hdiag : ∀ i, (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K) i i = a := by
    intro i
    rcases i with i | i | i
    · rw [Subsingleton.elim i 0]
    · rw [Subsingleton.elim i 0, ← hee_ww]
    · rw [Subsingleton.elim i 0, ← hww_ff, ← hee_ww]
  set u'' : GL (HypIndex 1 1) K := GeneralLinearGroup.scalar _ au⁻¹ * A with hu''
  have hu''mat : (u'' : Matrix (HypIndex 1 1) (HypIndex 1 1) K) =
      ((au⁻¹ : Kˣ) : K) • (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K) := by
    rw [hu'', Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_eq_diagonal_mul]
  have hu''U : u'' ∈ fullUnitriangular 1 1 K := by
    refine ⟨?_, fun i => ?_⟩
    · intro i j hij
      rw [hu''mat, Matrix.smul_apply, hAtri hij, smul_zero]
    · rw [hu''mat, Matrix.smul_apply, hdiag i, smul_eq_mul]
      simp [hau, ha0]
  have hu''p : u'' ^ p = 1 := u3_fullUnitriangular_pow_prime hp hu''U
  have hAeq : A = GeneralLinearGroup.scalar _ au * u'' := by
    rw [hu'', ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  have hAp : A ^ p = GeneralLinearGroup.scalar (HypIndex 1 1) (au ^ p) := by
    rw [hAeq, (commute_scalar au u'').symm.mul_pow, hu''p, mul_one, map_pow]
  have hxinl : (x₀ : SemiGL (HypIndex 1 1) K) = SemidirectProduct.inl A :=
    SemidirectProduct.ext (by simp [hA]) (by simpa using hσ1)
  have hxp : semilinearAutHom h (le_refl 1) (le_refl 1) (x₀ ^ p) = 1 := by
    refine (semilinearAutHom_eq_one_iff h (le_refl 1) (le_refl 1) (by norm_num) _).mpr
      ⟨?_, au ^ p, ?_⟩
    · rw [Subgroup.coe_pow, hxinl, ← map_pow, SemidirectProduct.right_inl]
      rfl
    · rw [Subgroup.coe_pow, hxinl, ← map_pow, SemidirectProduct.left_inl, hAp]
  have hzp : z ^ p = 1 := by
    rw [← hx₀, ← map_pow]
    exact hxp
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop (orderOf_dvd_of_pow_eq_one hzp))


section Assembly

theorem u3_blockTriangular_of_fix {x₀ : semilinearSimilitudes h 1 1} {g : hypSU h 1 1}
    (hg : g ∈ hypUnitriangular h 1 1) {α β : K}
    (hgM : ((g : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) = u3Mat h α β)
    (hnt : α ≠ 0 ∨ β ≠ 0)
    (hfix : semilinearAutHom h (le_refl 1) (le_refl 1) x₀ (hypProj h 1 1 g) = hypProj h 1 1 g) :
    (((x₀ : SemiGL (HypIndex 1 1) K).left : GL (HypIndex 1 1) K) :
      Matrix (HypIndex 1 1) (HypIndex 1 1) K).BlockTriangular fullPos := by
  have heq := u3_fix_matrix_eq hg hgM hfix
  by_cases hα : α = 0
  · have hβ : β ≠ 0 := hnt.resolve_left (not_not.mpr hα)
    rw [hα, map_zero] at heq
    obtain ⟨hwe, hfe, hfw, -⟩ := u3_fix_entries_central hβ
      (fun h0 => hβ ((x₀ : SemiGL (HypIndex 1 1) K).right.injective (by rw [h0, map_zero]))) heq
    exact u3_blockTriangular_of_hyp3 hwe hfe hfw
  · obtain ⟨hwe, hfe, hfw, -, -⟩ := u3_fix_entries_regular hα heq
    exact u3_blockTriangular_of_hyp3 hwe hfe hfw

theorem u3_preserves_P (hp : p ≠ 2) {z : MulAut (hypPSU h 1 1)} {g : hypSU h 1 1}
    (hg : g ∈ hypUnitriangular h 1 1) {α β : K}
    (hgM : ((g : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) = u3Mat h α β)
    (hnt : α ≠ 0 ∨ β ≠ 0) (hfix : z (hypProj h 1 1 g) = hypProj h 1 1 g) :
    ∀ y ∈ hypProjUnitriangular h 1 1, z y ∈ hypProjUnitriangular h 1 1 := by
  obtain ⟨x₀, hx₀⟩ := semilinearAutHom_surjective h (le_refl 1) (le_refl 1) hp (by norm_num) z
  have hAtri := u3_blockTriangular_of_fix hg hgM hnt (x₀ := x₀) (by rw [hx₀]; exact hfix)
  rintro _ ⟨u', hu', rfl⟩
  rw [← hx₀, semilinearAutHom_apply h (le_refl 1) (le_refl 1) x₀ u']
  exact ⟨_, u3_conj_mem_fullUnitriangular hAtri _ hu', rfl⟩

end Assembly

end Fix

end CFSG.GH74.GLS.Stage2.Bender.Thm1
