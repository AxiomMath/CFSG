module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SESim

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private theorem simAct_mk_simConj {σ : V ≃ₗ[ZMod 3] V} {c : (ZMod 3)ˣ}
    (hσ : IsSimilitude Q σ c) (t : OGroup Q) :
    simAct Q ⟨σ, ⟨c, hσ⟩⟩ t = simConj hσ t := by
  apply Subtype.ext
  rw [coe_simAct, coe_simConj]

theorem sec9u_orthToSim_simAct (γ : simGroup Q) (t : OGroup Q) :
    orthToSim Q (simAct Q γ t) = γ * orthToSim Q t * γ⁻¹ := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_orthToSim, coe_simAct]

theorem sec9u_conj_dim3 (hQ : Q.Nondegenerate) (h6 : Module.finrank (ZMod 3) V = 6)
    {x y : ProjSim Q} (hx : SimHasDim x 3) (hy : SimHasDim y 3) :
    ∃ δ : ProjSim Q, δ * y * δ⁻¹ = x := by
  obtain ⟨t, htt, ht3, htx⟩ := hx
  obtain ⟨t', ht't', ht'3, hty⟩ := hy
  have hx' : x = QuotientGroup.mk (orthToSim Q t) :=
    htx.symm.trans (projOrthToProjSim_toProj t)
  have hy' : y = QuotientGroup.mk (orthToSim Q t') :=
    hty.symm.trans (projOrthToProjSim_toProj t')
  have key : ∃ γ : simGroup Q, simAct Q γ t' = t := by
    by_cases hsign : invSign t = invSign t'
    ·
      have htype : invType t = invType t' := by
        apply Prod.ext
        · simp only [invType]
          rw [ht3, ht'3]
        · simpa only [invType] using hsign
      obtain ⟨g, hg⟩ := isConj_iff.mp (isConj_of_invType_eq hQ ht't' htt htype.symm)
      exact ⟨orthToSim Q g, by rw [simAct_orthToSim, hg]⟩
    ·
      have hneg : invSign t = - invSign t' := by
        rcases Int.units_eq_one_or (invSign t) with h | h
        · rcases Int.units_eq_one_or (invSign t') with h' | h'
          · exact absurd (h.trans h'.symm) hsign
          · simp only [h, h', neg_neg]
        · rcases Int.units_eq_one_or (invSign t') with h' | h'
          · simp only [h, h', neg_neg]
          · exact absurd (h.trans h'.symm) hsign
      obtain ⟨σ, hσ⟩ := (exists_isSimilitude_neg_one_iff hQ).mpr (by rw [h6]; decide)
      have hodd : Odd (invDim t') := ⟨1, by simp [ht'3]⟩
      have hsq : simConj hσ t' * simConj hσ t' = 1 := (invType_simConj hQ hσ ht't').1
      have htype : invType (simConj hσ t') = invType t := by
        rw [invType_simConj_neg_one_of_odd hQ hσ ht't' hodd]
        simp only [invType]
        exact Prod.ext (ht'3.trans ht3.symm) hneg.symm
      obtain ⟨g, hg⟩ := isConj_iff.mp (isConj_of_invType_eq hQ hsq htt htype)
      refine ⟨orthToSim Q g * ⟨σ, ⟨-1, hσ⟩⟩, ?_⟩
      rw [map_mul, MulAut.mul_apply, simAct_mk_simConj hσ, simAct_orthToSim, hg]
  obtain ⟨γ, hγ⟩ := key
  refine ⟨QuotientGroup.mk γ, ?_⟩
  rw [hx', hy', ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
    ← sec9u_orthToSim_simAct, hγ]

end CFSG.OddStandard.SmallF3.Omega
