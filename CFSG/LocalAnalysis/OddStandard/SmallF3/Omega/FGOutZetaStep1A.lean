module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2Vocab
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5SpinorInvol

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open TauCeti QuadraticMap CFSG.ClassicalInvolution CFSG.ClassicalGroups.Orthogonal

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

@[expose] def FGOZIsZeta (hQ : Q.Nondegenerate) (x : ProjSim Q) : Prop :=
  ∃ o : OGroup Q, x = projOrthToProjSim Q (toProj Q o) ∧
    (detSpinorNorm hQ o).1 = 1 ∧ (detSpinorNorm hQ o).2 ≠ 1

private lemma aux_units_mul_self (u : (ZMod 3)ˣ) : u * u = 1 := by
  rcases aux_units_zmod3 u with h | h <;> rw [h] <;> decide

private lemma aux_sqclass_add_self {K : Type*} [Field K] (x : SquareClassGroup K) : x + x = 0 := by
  have hx : x = squareClass (Additive.toMul (Quotient.out x)) := (squareClass_toMul_out x).symm
  rw [hx, ← squareClass_mul, squareClass_eq_zero_iff]
  exact ⟨_, rfl⟩

private lemma aux_sqclass_mul_self {K : Type*} [Field K]
    (a : Multiplicative (SquareClassGroup K)) : a * a = 1 := by
  rw [← ofAdd_toAdd a, ← ofAdd_add, aux_sqclass_add_self]
  exact ofAdd_zero

private lemma aux_mul_eq_one_iff_eq {A : Type*} [Group A] {a b : A} (hb : b * b = 1) :
    a * b = 1 ↔ a = b := by
  constructor
  · intro h
    calc a = a * (b * b) := by rw [hb, mul_one]
      _ = (a * b) * b := by rw [mul_assoc]
      _ = 1 * b := by rw [h]
      _ = b := one_mul b
  · intro h
    rw [h, hb]

theorem fg_oz_core (hQ : Q.Nondegenerate) {t : OGroup Q} (htt : t * t = 1) (ht1 : invDim t = 1)
    {z : ProjSim Q} (hz : ¬ SimInOmegaStar hQ z)
    (hzt : ¬ SimInOmegaStar hQ (z * projOrthToProjSim Q (toProj Q t))) :
    FGOZIsZeta hQ z ∨ FGOZIsZeta hQ (z * projOrthToProjSim Q (toProj Q t)) ∨
      FGOZIsZeta hQ (z ^ 2) ∨
      FGOZIsZeta hQ ((z * projOrthToProjSim Q (toProj Q t)) ^ 2) := by
  obtain ⟨x', hx'⟩ := QuotientGroup.mk_surjective z
  obtain ⟨c, hc⟩ := x'.2
  have hδt1 : (detSpinorNorm hQ t).1 = -1 := by
    rw [t5_detSpinorNorm_involution hQ htt, ht1, pow_one]
  rcases aux_unit_eq_one_or_neg_one c with hc1 | hc1
  ·
    have hc1' : IsSimilitude Q (x' : V ≃ₗ[ZMod 3] V) 1 := by
      rw [hc1] at hc
      exact hc
    have hmem : (x' : V ≃ₗ[ZMod 3] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
      isSimilitude_one_iff.mp hc1'
    let o : OGroup Q := ⟨(x' : V ≃ₗ[ZMod 3] V), hmem⟩
    have ho : orthToSim Q o = x' := Subtype.ext rfl
    have hz_eq : z = projOrthToProjSim Q (toProj Q o) := by
      rw [projOrthToProjSim_toProj, ho, hx']
    have hzxt : projOrthToProjSim Q (toProj Q (o * t)) =
        z * projOrthToProjSim Q (toProj Q t) := by
      rw [map_mul, map_mul, projOrthToProjSim_toProj, ho, hx']
    have ho_notmem : o ∉ omegaGroup hQ := by
      intro hmem'
      exact hz ⟨toProj Q o, (mem_omegaProj_iff hQ).mpr ⟨o, hmem', rfl⟩, hz_eq.symm⟩
    have ho_t_notmem : o * t ∉ omegaGroup hQ := by
      intro hmem'
      exact hzt ⟨toProj Q (o * t), (mem_omegaProj_iff hQ).mpr ⟨o * t, hmem', rfl⟩, hzxt⟩
    have hδne : detSpinorNorm hQ o ≠ 1 :=
      fun h => ho_notmem ((mem_omegaGroup_iff hQ).mpr h)
    have hδδt_ne : detSpinorNorm hQ o * detSpinorNorm hQ t ≠ 1 := by
      intro h
      exact ho_t_notmem ((mem_omegaGroup_iff hQ).mpr (by rw [map_mul]; exact h))
    rcases aux_units_zmod3 (detSpinorNorm hQ o).1 with hδ1 | hδ1
    · refine Or.inl ⟨o, hz_eq, hδ1, ?_⟩
      intro h2
      exact hδne (Prod.ext hδ1 h2)
    · refine Or.inr (Or.inl ⟨o * t, hzxt.symm, ?_, ?_⟩)
      · rw [map_mul]
        change (detSpinorNorm hQ o).1 * (detSpinorNorm hQ t).1 = 1
        rw [hδ1, hδt1]
        decide
      · intro h2
        have h1' : (detSpinorNorm hQ o * detSpinorNorm hQ t).1 = 1 := by
          change (detSpinorNorm hQ o).1 * (detSpinorNorm hQ t).1 = 1
          rw [hδ1, hδt1]
          decide
        have h2' : (detSpinorNorm hQ o * detSpinorNorm hQ t).2 = 1 := by
          rw [← map_mul]
          exact h2
        exact hδδt_ne (Prod.ext h1' h2')
  ·
    have hc1' : IsSimilitude Q (x' : V ≃ₗ[ZMod 3] V) (-1) := by
      rw [hc1] at hc
      exact hc
    set σ : V ≃ₗ[ZMod 3] V := (x' : V ≃ₗ[ZMod 3] V) with hσdef
    have hσ : IsSimilitude Q σ (-1) := by
      rw [hσdef]
      exact hc1'
    have hσ2 : IsSimilitude Q (σ * σ) 1 := by
      have h := aux_isSimilitude_mul hσ hσ
      rwa [show (-1 : (ZMod 3)ˣ) * (-1) = 1 by decide] at h
    have hmem2 : ((x' * x' : simGroup Q) : V ≃ₗ[ZMod 3] V) ∈
        TauCeti.QuadraticMap.orthogonalGroup Q := by
      rw [Subgroup.coe_mul, ← hσdef]
      exact isSimilitude_one_iff.mp hσ2
    let o₂ : OGroup Q := ⟨((x' * x' : simGroup Q) : V ≃ₗ[ZMod 3] V), hmem2⟩
    have ho₂ : orthToSim Q o₂ = x' * x' := Subtype.ext rfl
    have ho₂_coe : (o₂ : V ≃ₗ[ZMod 3] V) = σ * σ := by
      change ((x' * x' : simGroup Q) : V ≃ₗ[ZMod 3] V) = σ * σ
      rw [Subgroup.coe_mul, ← hσdef]
    have hdet2 : (detSpinorNorm hQ o₂).1 = 1 := by
      rw [detSpinorNorm_apply, QuadraticMap.orthogonalDet_apply, ho₂_coe, map_mul]
      exact aux_units_mul_self _
    have hz2_eq : z ^ 2 = projOrthToProjSim Q (toProj Q o₂) := by
      rw [pow_two, ← hx', ← QuotientGroup.mk_mul, projOrthToProjSim_toProj, ho₂]
    by_cases hmem : o₂ ∈ omegaGroup hQ
    ·
      have hδ₂ : detSpinorNorm hQ o₂ = 1 := (mem_omegaGroup_iff hQ).mp hmem
      let ν : OGroup Q := simConj hσ t
      have hνdef : ν = simConj hσ t := rfl
      obtain ⟨hν_sq, hν_type⟩ := invType_simConj hQ hσ htt
      have hν_dim : invDim ν = invDim t := congrArg Prod.fst hν_type
      have hν_dim1 : invDim ν = 1 := hν_dim.trans ht1
      have hν_sign0 : invSign ν = toSign (-1) ^ invDim t * invSign t :=
        congrArg Prod.snd hν_type
      have hν_sign : invSign ν = -invSign t := by
        rw [hν_sign0, ht1, pow_one, aux_toSign_neg_one, neg_one_mul]
      have hν_sign_ne : invSign ν ≠ invSign t := by
        rw [hν_sign]
        exact neg_units_ne_self (invSign t)
      have hδν1 : (detSpinorNorm hQ ν).1 = -1 := by
        rw [t5_detSpinorNorm_involution hQ hν_sq, hν_dim1, pow_one]
      have hδν_ne : detSpinorNorm hQ ν ≠ detSpinorNorm hQ t := by
        intro h
        exact hν_sign_ne (t5_invSign_eq_of_detSpinorNorm_eq hQ hν_sq htt h
          (hν_dim1.trans ht1.symm))
      have hδν2_ne : (detSpinorNorm hQ ν).2 ≠ (detSpinorNorm hQ t).2 := by
        intro h
        exact hδν_ne (Prod.ext (hδν1.trans hδt1.symm) h)
      let o₃ : OGroup Q := ν * o₂ * t
      have hδ₃ : detSpinorNorm hQ o₃ = detSpinorNorm hQ ν * detSpinorNorm hQ t := by
        change detSpinorNorm hQ (ν * o₂ * t) = detSpinorNorm hQ ν * detSpinorNorm hQ t
        rw [map_mul, map_mul, hδ₂, mul_one]
      have hδ₃1 : (detSpinorNorm hQ o₃).1 = 1 := by
        rw [hδ₃]
        change (detSpinorNorm hQ ν).1 * (detSpinorNorm hQ t).1 = 1
        rw [hδν1, hδt1]
        decide
      have hδ₃2 : (detSpinorNorm hQ o₃).2 ≠ 1 := by
        rw [hδ₃]
        change (detSpinorNorm hQ ν).2 * (detSpinorNorm hQ t).2 ≠ 1
        intro h
        exact hδν2_ne ((aux_mul_eq_one_iff_eq (aux_sqclass_mul_self _)).mp h)
      have hconj : x' * orthToSim Q t * x'⁻¹ = orthToSim Q ν := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_orthToSim]
        rw [hνdef, coe_simConj, hσdef]
      let x'' : simGroup Q := x' * orthToSim Q t
      have hx''def : x'' = x' * orthToSim Q t := rfl
      have hx''_sq : x'' * x'' = orthToSim Q o₃ := by
        have hfac : x'' * x'' =
            (x' * orthToSim Q t * x'⁻¹) * (x' * x') * orthToSim Q t := by
          rw [hx''def]
          group
        rw [hfac, hconj, ← ho₂, ← map_mul, ← map_mul]
      have hzx1_eq : z * projOrthToProjSim Q (toProj Q t) = QuotientGroup.mk x'' := by
        rw [← hx', projOrthToProjSim_toProj, ← QuotientGroup.mk_mul]
      have hzx1_sq : (z * projOrthToProjSim Q (toProj Q t)) ^ 2 =
          projOrthToProjSim Q (toProj Q o₃) := by
        rw [pow_two, hzx1_eq, ← QuotientGroup.mk_mul, hx''_sq, projOrthToProjSim_toProj]
      exact Or.inr (Or.inr (Or.inr ⟨o₃, hzx1_sq, hδ₃1, hδ₃2⟩))
    ·
      have hδ₂ : detSpinorNorm hQ o₂ ≠ 1 := fun h => hmem ((mem_omegaGroup_iff hQ).mpr h)
      have hδ₂2 : (detSpinorNorm hQ o₂).2 ≠ 1 := by
        intro h2
        exact hδ₂ (Prod.ext hdet2 h2)
      exact Or.inr (Or.inr (Or.inl ⟨o₂, hz2_eq, hdet2, hδ₂2⟩))

end CFSG.OddStandard.SmallF3.Omega
