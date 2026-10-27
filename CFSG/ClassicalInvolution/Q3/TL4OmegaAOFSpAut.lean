module

public import CFSG.ClassicalInvolution.Q3.TL4OmegaAOFSpStd
public import CFSG.ClassicalInvolution.Q3.TL4OmegaAOFBase
public import CFSG.ClassicalInvolution.Q3.Q3MFOSSpB

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.SpL

open Matrix CFSG CFSG.Blueprint CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Q3.Q3NM
  CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.ClassicalInvolution.Generic
open CFSG.LocalAnalysis.ComponentInitial (SymplecticTorusWeyl.mem_statedSp_iff)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open scoped MatrixGroups

section Aut

variable {F : Type} [Field F] [Finite F]

theorem ringChar_ne_two_of_card_three (hF : Nat.card F = 3) : ringChar F ≠ 2 := by
  intro h
  apply Q3MFOD.two_ne_zero_of_card_three hF
  have := (ringChar.spec F 2).mpr (by rw [h])
  exact_mod_cast this

theorem exists_conjSp_of_aut (hF : Nat.card F = 3)
    (ρ : MulAut (StatedSp 2 F ⧸ Subgroup.center (StatedSp 2 F))) :
    ∃ A : gsp 2 F, autToCentralQuotient (StatedSp 2 F) (conjSp 2 F A) = ρ := by
  obtain ⟨A, σ, hA⟩ :=
    CFSG.ComponentClassification.CatalogueBSymplecticRepresentation.automorphism_standard
      (ringChar_ne_two_of_card_three hF) le_rfl (MulAut.congr Q3MFO.Sp.centralQuotEquiv ρ)
  have hσ : σ = 1 := Q3MFO.ringEquiv_eq_one hF σ
  rw [hσ, map_one, mul_one] at hA
  refine ⟨A, MulEquiv.ext fun xb => ?_⟩
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective xb
  rw [autToCentralQuotient_mk]
  have h1 : (MulAut.congr Q3MFO.Sp.centralQuotEquiv ρ) (proj 2 F x) =
      conjAut 2 F A (proj 2 F x) := by rw [hA]
  rw [conjAut_proj] at h1
  change Q3MFO.Sp.centralQuotEquiv (ρ (Q3MFO.Sp.centralQuotEquiv.symm (proj 2 F x))) = _ at h1
  rw [Q3MFO.Sp.centralQuotEquiv_symm_proj] at h1
  rw [← Q3MFO.Sp.centralQuotEquiv_symm_proj (conjSp 2 F A x), ← h1, MulEquiv.symm_apply_apply]

variable (F) in
@[expose] def SpCplxStatement : Prop :=
  ∀ A : gsp 2 F,
    ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)ᵀ * formJ 2 F *
      (A : GL (Fin 2 ⊕ Fin 2) F) = (-1 : F) • formJ 2 F →
    ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
      (A : GL (Fin 2 ⊕ Fin 2) F) = -1 →
    oddCoreIn (fixedSubgroup (autToCentralQuotient (StatedSp 2 F) (conjSp 2 F A))) = ⊥

theorem oddCoreIn_fixed_of_outer_psp (hF : Nat.card F = 3) (hB : SpCplxStatement F)
    (ρ : MulAut (StatedSp 2 F ⧸ Subgroup.center (StatedSp 2 F))) (hρ2 : ρ * ρ = 1)
    (hout : ρ ∉ innSubgroup (StatedSp 2 F ⧸ Subgroup.center (StatedSp 2 F))) :
    oddCoreIn (fixedSubgroup ρ) = ⊥ := by
  have : Group.IsPerfect (StatedSp 2 F) :=
    CFSG.ClassicalGroups.Symplectic.isPerfect_statedSp 2 F (Or.inr (Or.inl ⟨hF, le_rfl⟩))
  obtain ⟨A, rfl⟩ := exists_conjSp_of_aut hF ρ
  have h1 : conjSp 2 F (A * A) = 1 := by
    apply autToCentralQuotient_injective (X := StatedSp 2 F)
    rw [map_mul, map_mul, hρ2, map_one]
  have hcomm : ∀ g ∈ StatedSp 2 F, ((A : GL (Fin 2 ⊕ Fin 2) F) * A) * g =
      g * ((A : GL (Fin 2 ⊕ Fin 2) F) * A) := by
    intro g hg
    have h3 := congrArg (fun φ : MulAut (StatedSp 2 F) =>
      ((φ ⟨g, hg⟩ : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F)) h1
    simp only [coe_conjSp, MulAut.one_apply, Subgroup.coe_mul] at h3
    calc ((A : GL (Fin 2 ⊕ Fin 2) F) * A) * g
        = (((A : GL (Fin 2 ⊕ Fin 2) F) * A) * g * ((A : GL (Fin 2 ⊕ Fin 2) F) * A)⁻¹) *
          ((A : GL (Fin 2 ⊕ Fin 2) F) * A) := by group
      _ = g * ((A : GL (Fin 2 ⊕ Fin 2) F) * A) := by rw [h3]
  have hmat : ∀ g ∈ StatedSp 2 F,
      (((A : GL (Fin 2 ⊕ Fin 2) F) * A : GL (Fin 2 ⊕ Fin 2) F) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) * (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
      (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
        (((A : GL (Fin 2 ⊕ Fin 2) F) * A : GL (Fin 2 ⊕ Fin 2) F) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) := fun g hg => by
    rw [← Units.val_mul, ← Units.val_mul, hcomm g hg]
  obtain ⟨d, hd⟩ := CFSG.ClassicalGroups.Symplectic.eq_scalar_of_commute_unipotents
    ((((A : GL (Fin 2 ⊕ Fin 2) F) * A : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F))
    (fun B hB => by
      have hmem : (((CFSG.ClassicalGroups.Symplectic.upperUnipotent hB :
          TauCeti.GLSymplectic (Fin 2) F) : GL (Fin 2 ⊕ Fin 2) F)) ∈ StatedSp 2 F := by
        rw [CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic]
        exact (CFSG.ClassicalGroups.Symplectic.upperUnipotent hB).2
      have hU := hmat _ hmem
      rwa [CFSG.ClassicalGroups.Symplectic.coe_upperUnipotent] at hU)
    (fun C hC => by
      have hmem : (((CFSG.ClassicalGroups.Symplectic.lowerUnipotent hC :
          TauCeti.GLSymplectic (Fin 2) F) : GL (Fin 2 ⊕ Fin 2) F)) ∈ StatedSp 2 F := by
        rw [CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic]
        exact (CFSG.ClassicalGroups.Symplectic.lowerUnipotent hC).2
      have hL := hmat _ hmem
      rwa [CFSG.ClassicalGroups.Symplectic.coe_lowerUnipotent] at hL)
  have hd0 : d ≠ 0 := by
    intro h0
    have h3 := congrArg Matrix.det hd
    rw [h0, map_zero, det_zero] at h3
    exact ((A : GL (Fin 2 ⊕ Fin 2) F) * A).isUnit.map Matrix.detMonoidHom |>.ne_zero h3
  obtain ⟨μ, hμ⟩ := A.2
  rcases Q3MFOD.cases_of_card_three hF (μ : F) with h | h | h
  · exact absurd h μ.ne_zero
  ·
    exfalso
    apply hout
    have hAsp : (A : GL (Fin 2 ⊕ Fin 2) F) ∈ StatedSp 2 F :=
      SymplecticTorusWeyl.mem_statedSp_iff.mpr (by rw [hμ, h, one_smul])
    refine ⟨QuotientGroup.mk ⟨A, hAsp⟩, MulEquiv.ext fun xb => ?_⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective xb
    rw [MulAut.conj_apply, autToCentralQuotient_mk, ← QuotientGroup.mk_inv,
      ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    rfl
  ·
    have hA' : ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)ᵀ *
        formJ 2 F * (A : GL (Fin 2 ⊕ Fin 2) F) = (-1 : F) • formJ 2 F := by rw [hμ, h]
    rcases Q3MFOD.cases_of_card_three hF d with hd1 | hd1 | hd1
    · exact absurd hd1 hd0
    · refine oddCoreIn_fixed_conjSp_of_sim_involution hF (by norm_num) A hA' (Units.ext ?_)
      rw [hd, hd1, map_one, Units.val_one]
    · refine hB A hA' ?_
      rw [← Units.val_mul, hd, hd1]
      ext i j
      by_cases hij : i = j <;> simp [Matrix.scalar_apply, hij]

end Aut

section Model


theorem outerFixedOddFree_psp_of (hB : SpCplxStatement (GaloisField 3 1)) :
    OuterFixedOddFree .PSp 2 := by
  intro S _ _ _ hS σ hσ hout
  have hFT : IsFundTag StatedLieTag.PSp := trivial
  have hadm : StatedLieAdmissible .PSp 2 3 1 := ⟨Nat.prime_three, le_rfl, by norm_num, by decide⟩
  obtain ⟨ψ, hψ, hker⟩ :=
    Upgrade.lieModelCentralCover _ 2 3 1 Nat.prime_three (by norm_num) hFT hadm S hS
  obtain ⟨hSq, -, -, -, -⟩ := Q3NM.centralQuotientData Nat.prime_three hFT hadm S ψ hψ hker
  have hZ := center_eq_bot_of_isQuasisimple hSq
  have : Group.IsPerfect (modelUniv .PSp 2 3 1 Nat.prime_three).K :=
    ⟨((ModelFacts.modelClauseZero .PSp 2 3 1 Nat.prime_three hFT hadm).1).1⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hF : Nat.card (GaloisField 3 1) = 3 := by simpa using GaloisField.card 3 1 one_ne_zero
  let e : S ≃* StatedSp 2 (GaloisField 3 1) ⧸ Subgroup.center (StatedSp 2 (GaloisField 3 1)) :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans
      (Q3NM.centralQuotientIso ψ hψ hker).symm
  have hρ2 : MulAut.congr e σ * MulAut.congr e σ = 1 := by rw [← map_mul, hσ, map_one]
  have hρout : MulAut.congr e σ ∉ innSubgroup (StatedSp 2 (GaloisField 3 1) ⧸
      Subgroup.center (StatedSp 2 (GaloisField 3 1))) := by
    rintro ⟨y, hy⟩
    apply hout
    refine ⟨e.symm y, MulEquiv.ext fun x => ?_⟩
    have h1 := congrArg (fun φ => φ (e x)) hy
    simp only [MulAut.conj_apply, MulAut.congr_apply] at h1
    rw [MulAut.conj_apply]
    apply e.injective
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, h1]
    simp
  have h1 := Q3NM.oddCoreIn_fixed_congr_eq_bot' e.symm (MulAut.congr e σ)
    (oddCoreIn_fixed_of_outer_psp hF hB _ hρ2 hρout)
  have h2 : MulAut.congr e.symm (MulAut.congr e σ) = σ := by
    ext x
    simp [MulAut.congr_apply]
  rwa [h2] at h1

end Model

end CFSG.ClassicalInvolution.Q3.TL4.SpL
