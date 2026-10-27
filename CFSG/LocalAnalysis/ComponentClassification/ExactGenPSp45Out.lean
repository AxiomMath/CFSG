module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd

public section

namespace CFSG.ComponentClassification.SolMax.SwapP2.ExactPSp45

open Matrix CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (conjAut fieldAut gsp multiplier
  multiplier_eq ker_multiplier statedSp_le_gsp conjAut_statedSp formJ)

variable {r : ℕ} {K : Type} [Field K]

private theorem scalar_transpose_mul_formJ_mul (c : Kˣ) :
    ((GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)ᵀ * formJ r K *
      ((GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      ((c ^ 2 : Kˣ) : K) • formJ r K := by
  rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal]
  simp [Matrix.smul_mul, Matrix.mul_smul, smul_smul, sq]

private def scalarGsp (c : Kˣ) : gsp r K :=
  ⟨GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c, c ^ 2, scalar_transpose_mul_formJ_mul c⟩

private theorem multiplier_scalarGsp [NeZero r] (c : Kˣ) :
    multiplier r K (scalarGsp c) = c ^ 2 :=
  multiplier_eq _ (scalar_transpose_mul_formJ_mul c)

private theorem conjAut_scalarGsp [Finite K] (hr : 1 ≤ r) (c : Kˣ) :
    conjAut r K (scalarGsp c) = 1 := by
  have h :=
    (CFSG.ComponentClassification.CatalogueBSymplecticRepresentation.conjAut_mul_fieldAut_eq_one_iff
      hr (scalarGsp c) 1).mpr ⟨rfl, c, rfl⟩
  rwa [map_one, mul_one] at h

private theorem conjAut_mem_inner [Finite K] {A : gsp 2 K} {c : Kˣ}
    (hA : multiplier 2 K A = c ^ 2) : conjAut 2 K A ∈ inner (StatedProj (StatedSp 2 K)) := by
  have hB : multiplier 2 K (A * (scalarGsp c)⁻¹) = 1 := by
    rw [map_mul, map_inv, hA, multiplier_scalarGsp, mul_inv_cancel]
  have hker : A * (scalarGsp c)⁻¹ ∈ (multiplier 2 K).ker := hB
  rw [ker_multiplier, Subgroup.mem_subgroupOf] at hker
  have hAB : A = (⟨_, statedSp_le_gsp hker⟩ : gsp 2 K) * scalarGsp c := by
    change A = A * (scalarGsp c)⁻¹ * scalarGsp c
    rw [inv_mul_cancel_right]
  have h1 := congrArg (conjAut 2 K) hAB
  rw [map_mul, conjAut_scalarGsp one_le_two, mul_one] at h1
  exact ⟨_, (h1.trans (conjAut_statedSp ⟨_, hker⟩)).symm⟩

theorem card_outer_dvd_two [Finite K] (hodd : ringChar K ≠ 2) (hσ : ∀ σ : K ≃+* K, σ = 1) :
    Nat.card (Outer (StatedProj (StatedSp 2 K))) ∣ 2 := by
  let q : gsp 2 K →* Outer (StatedProj (StatedSp 2 K)) :=
    (QuotientGroup.mk' (inner (StatedProj (StatedSp 2 K)))).comp (conjAut 2 K)
  have hq : Function.Surjective q := by
    intro x
    obtain ⟨α, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨A, σ, rfl⟩ :=
      CFSG.ComponentClassification.CatalogueBSymplecticRepresentation.automorphism_standard
        hodd le_rfl α
    refine ⟨A, ?_⟩
    rw [hσ σ, map_one, mul_one]
    rfl
  let Sq : Subgroup Kˣ := (powMonoidHom 2 : Kˣ →* Kˣ).range
  have hle : Sq.comap (multiplier 2 K) ≤ q.ker := by
    intro A hA
    obtain ⟨c, hc⟩ := hA
    exact (QuotientGroup.eq_one_iff _).mpr (conjAut_mem_inner (c := c) hc.symm)
  have h1 : Nat.card (Outer (StatedProj (StatedSp 2 K))) = q.ker.index := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hq, Subgroup.card_top]
  have h2 : q.ker.index ∣ (Sq.comap (multiplier 2 K)).index := Subgroup.index_dvd_of_le hle
  have h3 : (Sq.comap (multiplier 2 K)).index ∣ Sq.index := by
    rw [Subgroup.index_comap]
    exact Subgroup.relIndex_dvd_index_of_normal _ _
  have h4 : Sq.index ∣ 2 := by
    rw [IsCyclic.index_powMonoidHom_range]
    exact Nat.gcd_dvd_right _ _
  rw [h1]
  exact h2.trans (h3.trans h4)

private theorem ringChar_ne_two_of_card_five [Finite K] (hK : Nat.card K = 5) :
    ringChar K ≠ 2 := by
  intro h
  have : Fintype K := Fintype.ofFinite K
  have h5 : (5 : K) = 0 := by
    have h := FiniteField.cast_card_eq_zero K
    rw [Fintype.card_eq_nat_card, hK] at h
    exact_mod_cast h
  have h2 : (2 : K) = 0 := by
    have := ringChar.Nat.cast_ringChar (R := K)
    rw [h] at this
    exact_mod_cast this
  have h1 : (1 : K) = 0 := by linear_combination h5 - 2 * h2
  exact one_ne_zero h1

private theorem ringAut_eq_one_of_card_five (hK : Nat.card K = 5) (σ : K ≃+* K) : σ = 1 := by
  obtain ⟨-, -, -, -, hcard, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      (p := 5) (n := 1) (by norm_num) le_rfl (by rw [hK, pow_one])
  have : Subsingleton (K ≃+* K) := (Nat.card_eq_one_iff_unique.mp hcard).1
  exact Subsingleton.elim σ 1

theorem outer_psp45_le_two (S : Type) [Group S] [Finite S] (h : Blueprint.LieModel S .PSp 2 5 1) :
    Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer S) ≤ 2 := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ :=
    Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) h
  have hK5 : Nat.card K = 5 := by rw [hK, pow_one]
  have hdvd := card_outer_dvd_two (ringChar_ne_two_of_card_five hK5)
    (ringAut_eq_one_of_card_five hK5)
  rw [Nat.card_congr (equivalence e).toEquiv]
  exact Nat.le_of_dvd (by norm_num) hdvd

end CFSG.ComponentClassification.SolMax.SwapP2.ExactPSp45
