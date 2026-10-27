module

public import CFSG.HardMathSupport.Seitz.G2Anisotropic.UnitaryEmbedding.QPlusModel

public noncomputable section

namespace CFSG.HardMathSupport.Seitz.G2Anisotropic.UnitaryEmbedding

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ComponentClassification.UnbalancedCatalog CFSG.RankThree.Chevalley
  CFSG.RankThree.QuadraticSL2 CFSG.RankThree.Classical CFSG.RankThree.PartOne.RF4

section Matrices

variable {L : Type} [Field L]

theorem nSL_eq_uvu (c : Lˣ) :
    nSL c = uSL (c : L) * vSL (-((c⁻¹ : Lˣ) : L)) * uSL (c : L) := by
  have hc : (c : L) ≠ 0 := c.ne_zero
  have hc' : ((c⁻¹ : Lˣ) : L) = (c : L)⁻¹ := by simp
  apply Subtype.ext
  rw [hc', Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [nSL, uSL, vSL, Matrix.mul_apply, Fin.sum_univ_two]

theorem WSL_eq_uvu : (WSL : SL2 L) = uSL 1 * vSL (-1) * uSL 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [WSL, uSL, vSL, Matrix.mul_apply, Fin.sum_univ_two]

theorem WSL_eq_vuv : (WSL : SL2 L) = vSL (-1) * uSL 1 * vSL (-1) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [WSL, uSL, vSL, Matrix.mul_apply, Fin.sum_univ_two]

theorem mul_eq_one_of_vuv_eq_uvu {a b : L} (hb : b ≠ 0)
    (h : vSL a * uSL (-b) * vSL a = uSL (-b) * vSL a * uSL (-b)) : a * b = 1 := by
  have h01 := congrArg (fun A : SL2 L => (A : Matrix (Fin 2) (Fin 2) L) 0 1) h
  simp only [Matrix.SpecialLinearGroup.coe_mul] at h01
  simp [uSL, vSL, Matrix.mul_apply, Fin.sum_univ_two] at h01
  rcases h01 with h0 | h0
  · linear_combination -h0
  · exact absurd h0 hb

theorem vuv_eq_nSL (c : Lˣ) {X Y : L} (hY : Y = (c : L)) (hX : X = -(c : L)⁻¹) :
    vSL X * uSL Y * vSL X = nSL c := by
  have hc : (c : L) ≠ 0 := c.ne_zero
  subst hY hX
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [nSL, uSL, vSL, Matrix.mul_apply, Fin.sum_univ_two]

theorem uSL_injective : Function.Injective (uSL : L → SL2 L) := fun x y h => by
  have := congrArg (fun A : SL2 L => (A : Matrix (Fin 2) (Fin 2) L) 0 1) h
  simpa [uSL] using this

end Matrices

section Norm

variable {K K₂ : Type} [Field K] [Finite K] [Field K₂] [Algebra K K₂] [Finite K₂]

theorem exists_norm_eq (hdeg : Module.finrank K K₂ = 2) (σ : K₂ ≃+* K₂)
    (hσ : ∀ c, σ c = c ^ Nat.card K) {x : K₂} (hx0 : x ≠ 0)
    (hx : x ∈ Set.range (algebraMap K K₂)) : ∃ c : K₂ˣ, (c : K₂) * σ c = x := by
  classical
  have hq2 := natCard_eq_sq_of_finrank_eq_two hdeg
  have hq : 2 ≤ Nat.card K := by
    have := Finite.one_lt_card (α := K)
    omega
  obtain ⟨k, rfl⟩ := hx
  have hkq : k ^ Nat.card K = k := by
    have : Fintype K := Fintype.ofFinite K
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.pow_card k
  have hxq : (algebraMap K K₂ k) ^ Nat.card K = algebraMap K K₂ k := by
    rw [← map_pow, hkq]
  set u : K₂ˣ := Units.mk0 (algebraMap K K₂ k) hx0 with hu
  have huq : u ^ (Nat.card K - 1) = 1 := by
    have h1 : u ^ Nat.card K = u := Units.ext (by simpa [hu] using hxq)
    have h2 : u ^ (Nat.card K - 1) * u = u := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega)]
      exact h1
    exact mul_eq_right.1 h2
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := K₂ˣ)
  have hord : orderOf γ = Nat.card K ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hγ, Nat.card_units, hq2]
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 (hγ u)
  have hdvd : ((Nat.card K ^ 2 - 1 : ℕ) : ℤ) ∣ m * ((Nat.card K - 1 : ℕ) : ℤ) := by
    rw [← hord, orderOf_dvd_iff_zpow_eq_one, zpow_mul, hm, zpow_natCast, huq]
  have hfac : ((Nat.card K ^ 2 - 1 : ℕ) : ℤ) =
      ((Nat.card K - 1 : ℕ) : ℤ) * ((Nat.card K + 1 : ℕ) : ℤ) := by
    have h1 : 1 ≤ Nat.card K ^ 2 := Nat.one_le_pow _ _ (by omega)
    push_cast [Nat.cast_sub (by omega : 1 ≤ Nat.card K), Nat.cast_sub h1]
    ring
  have hpos : ((Nat.card K - 1 : ℕ) : ℤ) ≠ 0 := by
    have : 0 < Nat.card K - 1 := by omega
    exact_mod_cast this.ne'
  rw [hfac, mul_comm m] at hdvd
  obtain ⟨t, ht⟩ := (mul_dvd_mul_iff_left hpos).1 hdvd
  refine ⟨γ ^ t, ?_⟩
  have hcσ : σ ((γ ^ t : K₂ˣ) : K₂) = ((γ ^ t : K₂ˣ) : K₂) ^ Nat.card K := hσ _
  rw [hcσ, ← pow_succ']
  have : (γ ^ t) ^ (Nat.card K + 1) = u := by
    rw [← zpow_natCast, ← zpow_mul, ← hm]
    congr 1
    rw [mul_comm]
    exact_mod_cast ht.symm
  have h3 := congrArg (fun w : K₂ˣ => (w : K₂)) this
  simpa [hu] using h3

end Norm

section Model

variable {K K₂ : Type} [Field K] [Finite K] [Field K₂] [Algebra K K₂] [Finite K₂]
  {σ : K₂ ≃+* K₂}

theorem QPlusModel.exists_fixed_weyl (M : QPlusModel K σ) (hdeg : Module.finrank K K₂ = 2)
    (hσ : ∀ c, σ c = c ^ Nat.card K) {β : Fin Tag.G2.rank → ℤ} (hβ : IsRoot .G2 β) :
    ∃ c : K₂ˣ, rootWeylSL2 .G2 K₂ β c ∈ M.gamma ∧
      ∃ h : rootWeylSL2 .G2 K₂ β c ∈ monomialSubgroup .G2 K₂,
        weylQuotientHom .G2 K₂ ⟨_, h⟩ = rootReflection β := by
  classical
  obtain ⟨-, hord, hfix⟩ := quadratic_frobenius hdeg σ hσ
  have hinv : ∀ c, σ (σ c) = c := fun c => by
    have h2 : σ * σ = 1 := by rw [← pow_two, ← hord]; exact pow_orderOf_eq_one σ
    simpa using RingEquiv.ext_iff.1 h2 c
  set F := twistedEntrywise M.z (σ : K₂ →+* K₂) with hF
  have hF2 : ∀ y, F (F y) = y := twistedEntrywise_twistedEntrywise (σ := (σ : K₂ →+* K₂)) hinv
    M.hzdef
  obtain ⟨a, b, hu, hv⟩ := exists_twistedEntrywise_rootSL2 M.hz M.hw σ hβ
  set ρ := rootSL2 .G2 K₂ β with hρ
  have hinj : Function.Injective ρ := rootSL2_injective_of_field β
  have hσ1 : σ 1 = 1 := map_one σ
  have hσm1 : σ (-1) = -1 := by rw [map_neg, hσ1]
  have hFu : ∀ c, F (ρ (uSL c)) = ρ (vSL ((a : K₂) * σ c)) := hu
  have hFv : ∀ c, F (ρ (vSL c)) = ρ (uSL ((b : K₂) * σ c)) := hv
  have hab : (a : K₂) * b = 1 := by
    have e1 : F (ρ WSL) = ρ (vSL (a : K₂) * uSL (-(b : K₂)) * vSL (a : K₂)) := by
      rw [WSL_eq_uvu, map_mul, map_mul, map_mul, map_mul]
      simp only [hFu, hFv, hσ1, hσm1, mul_one, mul_neg, map_mul]
    have e2 : F (ρ WSL) = ρ (uSL (-(b : K₂)) * vSL (a : K₂) * uSL (-(b : K₂))) := by
      rw [WSL_eq_vuv, map_mul, map_mul, map_mul, map_mul]
      simp only [hFu, hFv, hσ1, hσm1, mul_one, mul_neg, map_mul]
    have := hinj (e1.symm.trans e2)
    exact mul_eq_one_of_vuv_eq_uvu b.ne_zero this
  have hbσ : (b : K₂) * σ a = 1 := by
    have h1 : F (F (ρ (uSL 1))) = ρ (uSL 1) := hF2 _
    rw [hFu 1, hσ1, mul_one, hFv, ← hσ1] at h1
    have := uSL_injective (hinj h1)
    simpa using this
  have hσa : σ (a : K₂) = a := by
    have hb : (b : K₂) = (a : K₂)⁻¹ := eq_inv_of_mul_eq_one_right hab
    rw [hb] at hbσ
    have := a.ne_zero
    field_simp at hbσ
    exact hbσ
  obtain ⟨a0, ha0⟩ := (hfix a).1 hσa
  have hx : (-(b : K₂)) ∈ Set.range (algebraMap K K₂) := by
    have hb : (b : K₂) = (a : K₂)⁻¹ := eq_inv_of_mul_eq_one_right hab
    refine ⟨-(a0⁻¹), ?_⟩
    rw [hb, map_neg, map_inv₀, ha0]
  obtain ⟨c, hc⟩ := exists_norm_eq hdeg σ hσ (neg_ne_zero.2 b.ne_zero) hx
  have hb : (b : K₂) = (a : K₂)⁻¹ := eq_inv_of_mul_eq_one_right hab
  have hc0 : (c : K₂) ≠ 0 := c.ne_zero
  have hσc0 : σ (c : K₂) ≠ 0 := by simp
  refine ⟨c, ?_⟩
  have key : F (ρ (nSL c)) = ρ (nSL c) := by
    conv_lhs => rw [nSL_eq_uvu]
    simp only [map_mul]
    rw [hFu, hFv]
    rw [← map_mul, ← map_mul]
    congr 1
    simp only [map_neg, Units.val_inv_eq_inv_val, map_inv₀]
    refine vuv_eq_nSL c ?_ ?_
    · field_simp
      linear_combination (-1 : K₂) * hc
    · field_simp
      linear_combination (a : K₂) * hc - hab
  have hfixn : F (rootWeylSL2 .G2 K₂ β c) = rootWeylSL2 .G2 K₂ β c := key
  have hadj : rootWeylSL2 .G2 K₂ β c ∈ adjointGroup .G2 K₂ :=
    ((exceptional_Lang_root_rank_one_data .G2 K₂ β).2.2.2.2.2.2.1 c).2
  have hΓ := M.gamma_eq_fixed hσ
  refine ⟨?_, (exceptional_Lang_root_rank_one_torus_transport .G2 K₂ hβ).2.2.1 c⟩
  rw [hΓ]
  exact ⟨hadj, hfixn⟩

end Model

end CFSG.HardMathSupport.Seitz.G2Anisotropic.UnitaryEmbedding
