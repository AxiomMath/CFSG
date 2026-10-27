module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalSpYCent
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofSpAut

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Matrix Subgroup CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement

section Fix

open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Steinberg (sl2Upper sl2Lower)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective mat_elt_positiveLong
  mat_elt_negativeLong)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldSp fieldAut)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (upperUnipotentSp)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldAut_proj)
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain (spInner spInner_eq_conj
  spInner_mul_fieldAut_proj spInner_injective exceptionalAut exceptionalAut_proj
  exceptionalSpAut_upperUnipotent displacementInLine_conj displacementInLine_upperUnipotent
  not_displacementInLine_upperUnipotent_swap transpose_single_zero_zero transpose_single_swap)

variable {K : Type} [Field K] [CharP K 2]

theorem mat_apply_eq_one_of_commute {n : ℕ} {k : Fin n} {g : StatedSp n K}
    (h₁ : g * longBlock K n k (sl2Upper 1) = longBlock K n k (sl2Upper 1) * g)
    (h₂ : g * longBlock K n k (sl2Lower 1) = longBlock K n k (sl2Lower 1) * g)
    {t : Fin n ⊕ Fin n} (ht : t ∈ coords k) (r : Fin n ⊕ Fin n) :
    mat n K g r t = (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) r t := by
  set e : Fin n ⊕ Fin n := Sum.inl k with he
  set f : Fin n ⊕ Fin n := Sum.inr k with hf
  set M := mat n K g with hM
  have hU : M * single e f 1 = single e f 1 * M := by
    have h := congrArg (mat n K) h₁
    rw [map_mul, map_mul, longBlock_sl2Upper, mat_elt_positiveLong, transvection,
      Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul] at h
    exact add_left_cancel h
  have hL : M * single f e 1 = single f e 1 * M := by
    have h := congrArg (mat n K) h₂
    rw [map_mul, map_mul, longBlock_sl2Lower, mat_elt_negativeLong, transvection,
      Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul] at h
    exact add_left_cancel h
  have c1 : ∀ r, r ≠ e → M r e = 0 := fun r hr => by
    have h := congrFun (congrFun hU r) f
    rw [mul_single_apply_same, single_mul_apply_of_ne _ _ _ _ _ hr] at h
    simpa using h
  have c2 : ∀ r, r ≠ f → M r f = 0 := fun r hr => by
    have h := congrFun (congrFun hL r) e
    rw [mul_single_apply_same, single_mul_apply_of_ne _ _ _ _ _ hr] at h
    simpa using h
  have c3 : M e e = M f f := by
    have h := congrFun (congrFun hU e) f
    rw [mul_single_apply_same, single_mul_apply_same] at h
    simpa using h
  have hform : M e e * M f f = 1 := by
    have key := congrFun (congrFun (mat_transpose_mul_gram_mul g) e) f
    rw [transpose_mul_gram_mul_apply, CFSG.ClassicalInvolution.Models.SymplecticPairs.gram_apply,
      Finset.sum_eq_single e] at key
    · simpa [he, hf, par, sgn] using key
    · intro c _ hc
      rw [show (mat n K) g c e = 0 from c1 c hc, zero_mul]
    · simp
  have hc : M e e = 1 := eq_one_of_mul_self_eq_one (by rw [← hform, ← c3])
  rcases mem_coords.1 ht with rfl | rfl
  · by_cases hr : r = e
    · rw [hr, hc, Matrix.one_apply_eq]
    · rw [c1 r hr, Matrix.one_apply_ne hr]
  · by_cases hr : r = f
    · rw [hr, ← c3, hc, Matrix.one_apply_eq]
    · rw [c2 r hr, Matrix.one_apply_ne hr]

omit [CharP K 2] in
theorem longBlock_castSucc_mem_range_spL {m : ℕ} (i : Fin m) (X : SL(2, K)) :
    longBlock K (m + 1) i.castSucc X ∈ (spL K m).range := by
  rw [range_spL]
  exact suppGroup_mono (coords_subset_compl (Fin.castSucc_lt_last i).ne) (isSupp_longBlock _ X)

theorem mem_range_spW_of_commute {m : ℕ} {g : StatedSp (m + 1) K}
    (h : ∀ i : Fin m,
      g * longBlock K (m + 1) i.castSucc (sl2Upper 1) =
          longBlock K (m + 1) i.castSucc (sl2Upper 1) * g ∧
        g * longBlock K (m + 1) i.castSucc (sl2Lower 1) =
          longBlock K (m + 1) i.castSucc (sl2Lower 1) * g) :
    g ∈ (spW K m).range := by
  rw [range_spW, mem_suppGroup_iff (parClosed_coords _)]
  intro t ht r
  obtain ⟨i, hi⟩ : ∃ i : Fin m, t ∈ coords i.castSucc := by
    rcases t with j | j <;>
    · have hj : j ≠ Fin.last m := fun hj => ht (by rw [hj]; simp [mem_coords])
      obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.mpr hj
      exact ⟨i, by simp [mem_coords]⟩
  exact mat_apply_eq_one_of_commute (h i).1 (h i).2 hi r

theorem fix_spBarL {m : ℕ} (hm : 1 ≤ m) (s : StatedSp (m + 1) K) (φ : K ≃+* K)
    (hL : ∀ l ∈ spBarL K m, (spInner (m + 1) K s * fieldAut (m + 1) K φ) l = l) :
    (∀ a, φ a = a) ∧ s ∈ (spW K m).range := by
  have key : ∀ S : StatedSp m K, s * fieldSp (m + 1) K φ (spL K m S) * s⁻¹ = spL K m S := by
    intro S
    have h := hL _ ⟨S, rfl⟩
    simp only [MonoidHom.comp_apply] at h
    rw [spInner_mul_fieldAut_proj] at h
    exact proj_sp_injective h
  have hcomm : ∀ x ∈ (spL K m).range, fieldSp (m + 1) K φ x = x → s * x = x * s := by
    rintro _ ⟨S, rfl⟩ hS
    have h := key S
    rw [hS] at h
    calc s * spL K m S = s * spL K m S * s⁻¹ * s := by group
      _ = spL K m S * s := by rw [h]
  have hs : s ∈ (spW K m).range := by
    refine mem_range_spW_of_commute fun i =>
      ⟨hcomm _ (longBlock_castSucc_mem_range_spL i _) ?_,
        hcomm _ (longBlock_castSucc_mem_range_spL i _) ?_⟩
    · rw [fieldSp_longBlock_upper, map_one]
    · rw [fieldSp_longBlock_lower, map_one]
  refine ⟨fun a => ?_, hs⟩
  obtain ⟨t, rfl⟩ := hs
  obtain ⟨S, hS⟩ := longBlock_castSucc_mem_range_spL ⟨0, hm⟩ (sl2Upper a)
  obtain ⟨S', hS'⟩ := longBlock_castSucc_mem_range_spL ⟨0, hm⟩ (sl2Upper (φ a))
  have h := key S
  rw [hS, fieldSp_longBlock_upper, ← hS', spW_commute_spL, mul_inv_cancel_right, hS'] at h
  exact sl2Upper_injective (longBlock_injective _ h)

theorem eq_one_of_semilinear_fixes {m : ℕ} (hm : 1 ≤ m) {X : SL(2, K)}
    (hX : ((X : Matrix (Fin 2) (Fin 2) K) - 1).det ≠ 0) (s : StatedSp (m + 1) K) (φ : K ≃+* K)
    (h2 : spInner (m + 1) K s * fieldAut (m + 1) K φ *
      (spInner (m + 1) K s * fieldAut (m + 1) K φ) = 1)
    (hL : ∀ l ∈ spBarL K m, (spInner (m + 1) K s * fieldAut (m + 1) K φ) l = l)
    (hy : (spInner (m + 1) K s * fieldAut (m + 1) K φ) (proj (m + 1) K (spW K m X)) =
      proj (m + 1) K (spW K m X)) :
    spInner (m + 1) K s * fieldAut (m + 1) K φ = 1 := by
  obtain ⟨hφ, a, rfl⟩ := fix_spBarL hm s φ hL
  rw [fieldAut_sp_eq_one hφ, mul_one] at h2 hy ⊢
  rw [spInner_eq_conj, conj_proj_sp] at hy
  have h3 := proj_sp_injective hy
  rw [← map_inv, ← map_mul, ← map_mul] at h3
  have h4 := longBlock_injective _ h3
  have hcomm : (a : Matrix (Fin 2) (Fin 2) K) * X = X * a := by
    have h5 : a * X = X * a := by
      calc a * X = a * X * a⁻¹ * a := by group
        _ = X * a := by rw [h4]
    exact congrArg Subtype.val h5
  rw [← map_mul] at h2
  have h6 := spInner_injective (h2.trans (map_one _).symm)
  rw [← map_mul] at h6
  have h7 : a * a = 1 := longBlock_injective _ (h6.trans (map_one _).symm)
  rw [eq_one_of_commute_of_mul_self hX hcomm h7, map_one, map_one]

theorem eq_one_of_fixes_spY [Finite K] {m : ℕ} (hm : 1 ≤ m) {X : SL(2, K)}
    (hX : ((X : Matrix (Fin 2) (Fin 2) K) - 1).det ≠ 0)
    (α : MulAut (StatedProj (StatedSp (m + 1) K))) (h2 : α * α = 1)
    (hL : ∀ l ∈ spBarL K m, α l = l)
    (hy : α (proj (m + 1) K (spW K m X)) = proj (m + 1) K (spW K m X)) : α = 1 := by
  rcases (show m = 1 ∨ 2 ≤ m by omega) with rfl | hm2
  · classical
    by_contra hne
    have hord : orderOf α = 2 := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact orderOf_eq_prime (by rw [sq]; exact h2) hne
    have : Fintype K := Fintype.ofFinite K
    obtain ⟨f, -, hKf⟩ := FiniteField.card K 2
    have hKf' : Nat.card K = 2 ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hKf]
    obtain ⟨Fr, hFr, hFrord, hzp, -, -⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
        Nat.prime_two f.pos hKf'
    obtain ⟨-, -, -, -, -, -, -, -, -, hinv⟩ :=
      CFSG.ComponentClassification.UnbalancedCatalog.SpChain.exceptionalAut_structure f.pos hFr
        hFrord hzp
    obtain ⟨g, j, hj, hαeq⟩ := hinv α hord
    have hγ2 := CFSG.ComponentClassification.UnbalancedCatalog.SpChain.exceptionalAut_sq
      (K := K) hFr
    have hE : ∀ φ : K ≃+* K, α = spInner 2 K g * fieldAut 2 K φ → False := by
      intro φ hαφ
      apply hne
      rw [hαφ] at h2 hL hy ⊢
      exact eq_one_of_semilinear_fixes le_rfl hX g φ h2 hL hy
    rcases hj with rfl | rfl
    · exact hE 1 (by rw [hαeq, pow_zero, mul_one, map_one, mul_one])
    · rcases Nat.even_or_odd (f : ℕ) with ⟨k, hk⟩ | ⟨k, hk⟩
      · refine hE (Fr ^ k) ?_
        rw [hαeq, show (f : ℕ) = 2 * k by omega, pow_mul, hγ2, ← map_pow]
      ·
        set t₀ : StatedSp (1 + 1) K := longBlock K (1 + 1) 0 (sl2Upper 1) with ht₀
        have hfix : α (proj (1 + 1) K t₀) = proj (1 + 1) K t₀ :=
          hL _ ((longBlock_zero_mem_range_spL le_rfl (sl2Upper 1)).elim fun S hS =>
            ⟨S, by simp only [MonoidHom.comp_apply]; rw [hS]; rfl⟩)
        have hpow : exceptionalAut K ^ (f : ℕ) = exceptionalAut K * fieldAut 2 K (Fr ^ k) := by
          rw [show (f : ℕ) = 1 + 2 * k by omega, pow_add, pow_one, pow_mul, hγ2, ← map_pow]
        rw [hαeq, hpow, ← mul_assoc, MulAut.mul_apply, MulAut.mul_apply] at hfix
        have h1 : fieldAut 2 K (Fr ^ k) (proj (1 + 1) K t₀) = proj (1 + 1) K t₀ := by
          change fieldAut 2 K (Fr ^ k) (proj 2 K t₀) = proj 2 K t₀
          rw [fieldAut_proj, ht₀, fieldSp_longBlock_upper, map_one]
        rw [h1, ht₀, longBlock_zero_upper_eq] at hfix
        change spInner 2 K g (exceptionalAut K (proj 2 K _)) = proj 2 K _ at hfix
        rw [exceptionalAut_proj, exceptionalSpAut_upperUnipotent, spInner_eq_conj,
          conj_proj_sp (m := 1)] at hfix
        have h2' := proj_sp_injective (m := 1) hfix
        have h3 := displacementInLine_conj g⁻¹ (upperUnipotentSp 2 K
          (transpose_single_zero_zero (K := K))) (RingEquiv.refl K)
          displacementInLine_upperUnipotent
        have h4 : fieldSp 2 K (RingEquiv.refl K)
            (upperUnipotentSp 2 K (transpose_single_zero_zero (K := K))) =
            upperUnipotentSp 2 K (transpose_single_zero_zero (K := K)) := by
          rw [← longBlock_zero_upper_eq]
          exact (fieldSp_longBlock_upper _ _ _).trans (by rfl)
        rw [h4, ← h2'] at h3
        have h5 : g⁻¹ * (g * upperUnipotentSp 2 K (transpose_single_swap (K := K)) * g⁻¹) *
            g⁻¹⁻¹ = upperUnipotentSp 2 K (transpose_single_swap (K := K)) := by group
        rw [h5] at h3
        exact not_displacementInLine_upperUnipotent_swap h3
  · obtain ⟨hE, -⟩ := CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.automorphism_generation
      (K := K) (r := m + 1) (by omega)
    obtain ⟨s, φ, rfl⟩ :=
      CFSG.ComponentClassification.UnbalancedCatalog.SpChain.exists_eq_spInner_mul_fieldAut
        (hE ▸ Subgroup.mem_top α)
    exact eq_one_of_semilinear_fixes hm hX s φ h2 hL hy

end Fix

section NoInv

open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)

variable {K : Type} [Field K] {m : ℕ} {G : Type} [Group G] {A : Subgroup G}
  {θ : ↥A →* StatedProj (StatedSp (m + 1) K)} [Finite K] [CharP K 2]

theorem noInv_spY (hA : commutator ↥A = ⊤) (hker : θ.ker = center ↥A)
    (hθ : Function.Surjective θ) (h4 : ∃ s : Finset K, s.card = 4) (hm : 1 ≤ m) {X : SL(2, K)}
    (hX : ((X : Matrix (Fin 2) (Fin 2) K) - 1).det ≠ 0) {y : G} (hyA : y ∈ A)
    (hyθ : θ ⟨y, hyA⟩ = proj (m + 1) K (spW K m X)) :
    NoInvolutoryCentralizing A (zpowers y ⊔ spLeviL θ) := by
  intro σ hσ hfix
  obtain ⟨α, hα⟩ := exists_inducedAut hker hθ σ
  have hL := inducedAut_fix_of_levLift hθ (commutator_spBarL h4) le_sup_right hfix hα
  have hy : α (proj (m + 1) K (spW K m X)) = proj (m + 1) K (spW K m X) := by
    rw [← hyθ, hα, hfix ⟨y, hyA⟩ (mem_sup_left (mem_zpowers y))]
  have h1 := eq_one_of_fixes_spY hm hX α (inducedAut_sq hθ hσ hα) hL hy
  exact eq_one_of_theta_eq hker hA σ fun a => by rw [← hα, h1, MulAut.one_apply]

end NoInv

end CFSG.ComponentClassification.RankTwoClassical
