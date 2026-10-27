module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6PE16

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem ffOutFF6PE16Cl_hat_conv (fr : PFrame Q (Option (Fin 5)) ffC)
    (τ : Equiv.Perm (Fin 5)) (K : Finset (Option (Fin 5))) :
    ffHat fr τ * fr.signChange K =
      fr.pOrth τ * fr.signChange
        (symmDiff (if Equiv.Perm.sign τ = 1 then ∅ else {none}) K) := by
  rw [ffHat, mul_assoc, fr.signChange_mul]

theorem ffOutFF6PE16Cl_hat_inv (fr : PFrame Q (Option (Fin 5)) ffC)
    (τ : Equiv.Perm (Fin 5)) : (ffHat fr τ)⁻¹ = ffHat fr τ⁻¹ := by
  apply inv_eq_of_mul_eq_one_right
  rw [ffHat_mul, mul_inv_cancel, ffHat_one]

theorem ffOutFF6PE16Cl_conj_hat (fr : PFrame Q (Option (Fin 5)) ffC)
    (τ σ : Equiv.Perm (Fin 5)) (J : Finset (Fin 5)) :
    ffHat fr τ * (ffHat fr σ * fr.signChange (ffOpt J)) * (ffHat fr τ)⁻¹ =
      ffHat fr (τ * σ * τ⁻¹) * fr.signChange (ffOpt (ffAct τ J)) := by
  have htinv := ffOutFF6PE16Cl_hat_inv fr τ
  have h1 := ffHat_conj_signChange_ffOpt fr τ J
  have h2 : fr.signChange (ffOpt J) * (ffHat fr τ)⁻¹ =
      (ffHat fr τ)⁻¹ * fr.signChange (ffOpt (ffAct τ J)) := by
    have h := congrArg (fun x => (ffHat fr τ)⁻¹ * x) h1
    simpa [mul_assoc] using h
  calc ffHat fr τ * (ffHat fr σ * fr.signChange (ffOpt J)) * (ffHat fr τ)⁻¹
      = ffHat fr τ * ffHat fr σ * fr.signChange (ffOpt J) * (ffHat fr τ)⁻¹ := by group
    _ = ffHat fr (τ * σ) * fr.signChange (ffOpt J) * (ffHat fr τ)⁻¹ := by
          rw [ffHat_mul]
    _ = ffHat fr (τ * σ) * (fr.signChange (ffOpt J) * (ffHat fr τ)⁻¹) := by group
    _ = ffHat fr (τ * σ) * ((ffHat fr τ)⁻¹ * fr.signChange (ffOpt (ffAct τ J))) := by
          rw [h2]
    _ = (ffHat fr (τ * σ) * (ffHat fr τ)⁻¹) * fr.signChange (ffOpt (ffAct τ J)) := by group
    _ = ffHat fr (τ * σ * τ⁻¹) * fr.signChange (ffOpt (ffAct τ J)) := by
          rw [htinv, ffHat_mul]

theorem ffOutFF6PE16Cl_hat_mem_P (hQ : Q.Nondegenerate) (fr : PFrame Q (Option (Fin 5)) ffC)
    {τ : Equiv.Perm (Fin 5)} (hτ : τ ∈ ffD8p) : ffHat fr τ ∈ ffP0p hQ fr := by
  refine (mem_ffP0p_iff_hatOpt hQ fr).mpr ⟨τ, hτ, ∅, by simp, ?_⟩
  rw [ffOpt, Finset.map_empty, fr.signChange_empty, mul_one]

theorem ffOutFF6PE16Cl_sq_fix (hQ : Q.Nondegenerate) (fr : PFrame Q (Option (Fin 5)) ffC)
    {U : Subgroup (OGroup Q)} (hU : IsNormalE16In (ffP0p hQ fr) U)
    {σ : Equiv.Perm (Fin 5)} (hσ : σ ∈ ffD8p) {J : Finset (Fin 5)}
    (hu : ffHat fr σ * fr.signChange (ffOpt J) ∈ U) :
    σ * σ = 1 ∧ symmDiff (ffAct σ⁻¹ J) J = ∅ ∧
      ∀ K : Finset (Fin 5), fr.signChange (ffOpt K) ∈ U → ffAct σ K = K := by
  classical
  have huu : (ffHat fr σ * fr.signChange (ffOpt J)) *
      (ffHat fr σ * fr.signChange (ffOpt J)) = 1 := by
    have h := hU.2.1.1.2 (ffHat fr σ * fr.signChange (ffOpt J)) hu
    rwa [pow_two] at h
  have hOne : (1 : OGroup Q) = ffHat fr 1 * fr.signChange (ffOpt (∅ : Finset (Fin 5))) := by
    rw [ffHat_one, ffOpt, Finset.map_empty, fr.signChange_empty, one_mul]
  have hEq : ffHat fr (σ * σ) * fr.signChange (ffOpt (symmDiff (ffAct σ⁻¹ J) J)) =
      ffHat fr 1 * fr.signChange (ffOpt (∅ : Finset (Fin 5))) :=
    (ffHat_mul_ffOpt fr σ σ J J).symm.trans (huu.trans hOne)
  have hkey : fr.pOrth (σ * σ) * fr.signChange
        (symmDiff (if Equiv.Perm.sign (σ * σ) = 1 then ∅ else {none})
          (ffOpt (symmDiff (ffAct σ⁻¹ J) J))) =
      fr.pOrth 1 * fr.signChange
        (symmDiff (if Equiv.Perm.sign (1 : Equiv.Perm (Fin 5)) = 1 then ∅ else {none})
          (ffOpt (∅ : Finset (Fin 5)))) := by
    rw [← ffOutFF6PE16Cl_hat_conv fr (σ * σ) (ffOpt (symmDiff (ffAct σ⁻¹ J) J)),
      ← ffOutFF6PE16Cl_hat_conv fr 1 (ffOpt (∅ : Finset (Fin 5)))]
    exact hEq
  obtain ⟨hsq, hsymm⟩ := ffMonoP_unique fr hkey
  have hX : symmDiff (ffAct σ⁻¹ J) J = ∅ := by
    rw [hsq, Equiv.Perm.sign_one, if_pos rfl] at hsymm
    rw [← Finset.bot_eq_empty, bot_symmDiff, bot_symmDiff] at hsymm
    exact ffOpt_injective hsymm
  refine ⟨hsq, hX, ?_⟩
  intro K hK
  haveI : IsMulCommutative U := hU.2.1.1.1
  have hcomm := setLike_mul_comm (s := U) hu hK
  have htJ : (fr.signChange (ffOpt J))⁻¹ = fr.signChange (ffOpt J) :=
    inv_eq_of_mul_eq_one_right (fr.signChange_mul_self (ffOpt J))
  have hmid : fr.signChange (ffOpt J) * fr.signChange (ffOpt K) * fr.signChange (ffOpt J) =
      fr.signChange (ffOpt K) := by
    rw [fr.signChange_comm (ffOpt J) (ffOpt K), mul_assoc, fr.signChange_mul_self, mul_one]
  have hconj : (ffHat fr σ * fr.signChange (ffOpt J)) * fr.signChange (ffOpt K) *
      (ffHat fr σ * fr.signChange (ffOpt J))⁻¹ =
      fr.signChange (ffOpt (ffAct σ K)) := by
    calc (ffHat fr σ * fr.signChange (ffOpt J)) * fr.signChange (ffOpt K) *
          (ffHat fr σ * fr.signChange (ffOpt J))⁻¹
        = ffHat fr σ * (fr.signChange (ffOpt J) * fr.signChange (ffOpt K) *
            fr.signChange (ffOpt J)) * (ffHat fr σ)⁻¹ := by
            rw [mul_inv_rev, htJ]; group
      _ = ffHat fr σ * fr.signChange (ffOpt K) * (ffHat fr σ)⁻¹ := by rw [hmid]
      _ = fr.signChange (ffOpt (ffAct σ K)) := ffHat_conj_signChange_ffOpt fr σ K
  have hconj' : (ffHat fr σ * fr.signChange (ffOpt J)) * fr.signChange (ffOpt K) *
      (ffHat fr σ * fr.signChange (ffOpt J))⁻¹ = fr.signChange (ffOpt K) := by
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  have heq : fr.signChange (ffOpt K) = fr.signChange (ffOpt (ffAct σ K)) :=
    hconj'.symm.trans hconj
  rw [fr.signChange_injective.eq_iff, ffOpt_injective.eq_iff] at heq
  exact heq.symm

private theorem ffOutFF6PE16Cl_g0_fixed_even_E0 {J : Finset (Fin 5)} (hJ : Even J.card)
    (h : ffAct ffD8g J = J) : J ∈ ffE0s := by
  revert J
  decide +kernel

theorem ffOutFF6PE16Cl_E0_of_ffD8g (hQ : Q.Nondegenerate) (fr : PFrame Q (Option (Fin 5)) ffC)
    {U : Subgroup (OGroup Q)} (hU : IsNormalE16In (ffP0p hQ fr) U) {J : Finset (Fin 5)}
    (hJe : Even J.card) (hu : ffHat fr ffD8g * fr.signChange (ffOpt J) ∈ U) : J ∈ ffE0s := by
  have hσD : ffD8g ∈ ffD8p := by rw [mem_ffD8p_iff]
  obtain ⟨hsq, hsymm, -⟩ := ffOutFF6PE16Cl_sq_fix hQ fr hU hσD hu
  have hg : (ffD8g)⁻¹ = ffD8g := inv_eq_of_mul_eq_one_right hsq
  have hAct : ffAct ffD8g J = J := by
    have h := Finset.symmDiff_eq_empty.mp hsymm
    rwa [hg] at h
  exact ffOutFF6PE16Cl_g0_fixed_even_E0 hJe hAct

theorem ffOutFF6PE16Cl_E0_of_swap02 (hQ : Q.Nondegenerate) (fr : PFrame Q (Option (Fin 5)) ffC)
    {U : Subgroup (OGroup Q)} (hU : IsNormalE16In (ffP0p hQ fr) U) {J : Finset (Fin 5)}
    (hJe : Even J.card) (hu : ffHat fr (Equiv.swap 0 2) * fr.signChange (ffOpt J) ∈ U) :
    J ∈ ffE0s := by
  have hσD : Equiv.swap 0 2 ∈ ffD8p := by rw [mem_ffD8p_iff]; decide
  obtain ⟨hsq, hsymm, -⟩ := ffOutFF6PE16Cl_sq_fix hQ fr hU hσD hu
  have hAct : ffAct (Equiv.swap 0 2) J = J := by
    have h := Finset.symmDiff_eq_empty.mp hsymm
    rwa [inv_eq_of_mul_eq_one_right hsq] at h
  have hu'U : ffHat fr ffRot * (ffHat fr (Equiv.swap 0 2) * fr.signChange (ffOpt J)) *
      (ffHat fr ffRot)⁻¹ ∈ U :=
    (Subgroup.normal_subgroupOf_iff hU.1).mp hU.2.2 _ _ hu
      (ffOutFF6PE16Cl_hat_mem_P hQ fr ffRot_mem_ffD8p)
  have hrotconj : ffRot * Equiv.swap 0 2 * ffRot⁻¹ = Equiv.swap 1 3 := by decide +kernel
  have hu'eq : ffHat fr ffRot * (ffHat fr (Equiv.swap 0 2) * fr.signChange (ffOpt J)) *
      (ffHat fr ffRot)⁻¹ =
      ffHat fr (Equiv.swap 1 3) * fr.signChange (ffOpt (ffAct ffRot J)) := by
    rw [ffOutFF6PE16Cl_conj_hat, hrotconj]
  have hJ''even : Even (symmDiff (ffAct (Equiv.swap 1 3) J) (ffAct ffRot J)).card :=
    (Finset.even_card_symmDiff_iff _ _).mpr
      (iff_of_true (by rw [ffAct_card]; exact hJe) (by rw [ffAct_card]; exact hJe))
  have hu''eq : (ffHat fr (Equiv.swap 0 2) * fr.signChange (ffOpt J)) *
      (ffHat fr (Equiv.swap 1 3) * fr.signChange (ffOpt (ffAct ffRot J))) =
      ffHat fr ffD8g * fr.signChange
        (ffOpt (symmDiff (ffAct (Equiv.swap 1 3) J) (ffAct ffRot J))) := by
    rw [show ffD8g = Equiv.swap 0 2 * Equiv.swap 1 3 from rfl, ffHat_mul_ffOpt]
    simp only [Equiv.swap_inv]
  have hu''U : ffHat fr ffD8g * fr.signChange
      (ffOpt (symmDiff (ffAct (Equiv.swap 1 3) J) (ffAct ffRot J))) ∈ U := by
    rw [← hu''eq]
    exact Subgroup.mul_mem _ hu (hu'eq ▸ hu'U)
  exact ff_coset_E0 hJe hAct (ffOutFF6PE16Cl_E0_of_ffD8g hQ fr hU hJ''even hu''U)

end CFSG.OddStandard.SmallF3.Omega
