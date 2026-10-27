module

public import CFSG.ClassicalInvolution.ModelFacts.FundNoncentralSimple
public import CFSG.ClassicalInvolution.ModelFacts.FundNoncentralAdjoint
public import CFSG.LieType.Steinberg.TwistedD4.Perfect
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate120
public import Certificates.Certificate123
public import CFSG.ClassicalInvolution.ModelFacts.FundNoncentralChevalley
public import CFSG.ClassicalInvolution.WeakCT.B2Signs

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.LieType.Steinberg.TwistedD4 CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.CurtisTits
  CFSG.ClassicalInvolution.WeakCT CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

section D4

variable {K : Type} [Field K]

local notation "𝕩" => xPar (rootOperatorFamily d4)

local notation "𝕃" => CFSG.LieType.CurtisTits.rankOne (rootGroup (rootOperatorFamily d4) K)

theorem map_sl2Upper {F : Type} [Field F] (ι : F →+* K) (c : F) :
    Matrix.SpecialLinearGroup.map ι (sl2Upper c) = sl2Upper (ι c) :=
  Subtype.ext (by
    ext p q
    fin_cases p <;> fin_cases q <;> simp [WeakCT.coe_sl2Upper])

theorem map_sl2Lower {F : Type} [Field F] (ι : F →+* K) (c : F) :
    Matrix.SpecialLinearGroup.map ι (sl2Lower c) = sl2Lower (ι c) :=
  Subtype.ext (by
    ext p q
    fin_cases p <;> fin_cases q <;> simp [WeakCT.coe_sl2Lower])

theorem map_wS_one {F : Type} [Field F] (ι : F →+* K) :
    Matrix.SpecialLinearGroup.map ι (wS (1 : Fˣ)) = wS (1 : Kˣ) := by
  simp [wS, map_sl2Upper, map_sl2Lower]

section Long

variable (K) in
noncomputable def phi2 : Matrix.SpecialLinearGroup (Fin 2) K →* adjointGroup d4 K :=
  (𝕃 (nd 2)).subtype.comp
    (restrictEquiv (rootOperatorFamily d4) cartan_two_zero).symm.toMonoidHom

theorem phi2_upper (c : K) : phi2 K (sl2Upper c) = 𝕩 (Pi.single (nd 2) 1) c := by
  simp only [phi2, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, restrictEquiv_symm_upper,
    Subgroup.coe_subtype, rankOneRels_x]
  exact (xPar_simple _ _).symm

theorem phi2_lower (c : K) : phi2 K (sl2Lower c) = 𝕩 (-Pi.single (nd 2) 1) c := by
  simp only [phi2, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, restrictEquiv_symm_lower,
    Subgroup.coe_subtype, rankOneRels_y]
  exact (xPar_neg_simple _ _).symm

variable {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c)
include hσ

theorem slLong_wS_sq_val :
    (slLong σ hσ (wS (1 : (fixedField σ)ˣ) * wS (1 : (fixedField σ)ˣ)) : adjointGroup d4 K) =
      (torusElement d4 K (nd 2) (-1))⁻¹ := by
  change slLongE σ _ = _
  have h : slLongE σ (wS (1 : (fixedField σ)ˣ) * wS (1 : (fixedField σ)ˣ)) =
      phi2 K (Matrix.SpecialLinearGroup.map (fixedField σ).subtype
        (wS (1 : (fixedField σ)ˣ) * wS (1 : (fixedField σ)ˣ))) := rfl
  rw [h, map_mul, map_wS_one]
  exact map_wS_sq_eq_inv_torusElement (nd 2) (phi2 K) phi2_upper phi2_lower

theorem slLong_wS_sq_not_central (h2 : (2 : K) ≠ 0) :
    slLong σ hσ (wS (1 : (fixedField σ)ˣ) * wS (1 : (fixedField σ)ˣ)) ∉
      Subgroup.center (twistedGroup σ) := by
  intro hc
  have h22 : 22 < (Tag.rootCertificate d4).roots.length := by decide
  set y : twistedGroup σ := ⟨_, xPar_d4Root_mem_twistedGroup hσ h22 rho_d4Root_22 (map_one σ)⟩
    with hy
  have h1 := congrArg Subtype.val (Subgroup.mem_center_iff.mp hc y)
  simp only [Subgroup.coe_mul] at h1
  rw [slLong_wS_sq_val hσ] at h1
  have h3 : torusElement d4 K (nd 2) (-1) * 𝕩 (d4Root 22) 1 *
      (torusElement d4 K (nd 2) (-1))⁻¹ = 𝕩 (d4Root 22) 1 := by
    have h1' : 𝕩 (d4Root 22) (1 : K) * (torusElement d4 K (nd 2) (-1))⁻¹ =
        (torusElement d4 K (nd 2) (-1))⁻¹ * 𝕩 (d4Root 22) (1 : K) := h1
    calc torusElement d4 K (nd 2) (-1) * 𝕩 (d4Root 22) 1 * (torusElement d4 K (nd 2) (-1))⁻¹
        = torusElement d4 K (nd 2) (-1) *
          (𝕩 (d4Root 22) 1 * (torusElement d4 K (nd 2) (-1))⁻¹) := by rw [mul_assoc]
      _ = 𝕩 (d4Root 22) 1 := by rw [h1']; group
  have hpair : (∑ j, d4.cartan (nd 2) j * (d4Root 22) j) = 1 := by decide
  rw [torusElement_conj_xPar (F := rootOperatorFamily d4) (nd 2) (-1) (isRoot_d4Root h22) 1,
    hpair] at h3
  have h5 := xPar_injective (F := rootOperatorFamily d4) (K := K) (isRoot_d4Root h22) h3
  apply h2
  simp only [zpow_one, mul_one, Units.val_neg, Units.val_one] at h5
  linear_combination -h5

theorem rankOne_long_le_range_slLong' :
    rankOne (twistedRootGroup σ) (ng 0) ≤ (slLong σ hσ).range := by
  refine sup_le (fun x hx => ?_) (fun x hx => ?_)
  · obtain ⟨c, hc, hxc⟩ := (mem_twistedRootSubgroupD4_iff_of_fixed hσ (isRoot_single d4 (nd 2))
      proj_single_two rho_single_two _).1 ((mem_twistedRootGroup (σ := σ)).1 hx)
    exact ⟨sl2Upper ⟨c, hc⟩, Subtype.ext (by rw [slLong_val, slLongE_upper]; exact hxc.symm)⟩
  · obtain ⟨c, hc, hxc⟩ := (mem_twistedRootSubgroupD4_iff_of_fixed hσ (isRoot_neg_single d4 (nd 2))
      proj_neg_single_two rho_neg_single_two _).1 ((mem_twistedRootGroup (σ := σ)).1 hx)
    exact ⟨sl2Lower ⟨c, hc⟩, Subtype.ext (by rw [slLong_val, slLongE_lower]; exact hxc.symm)⟩

theorem d4_long_eq_one_of_mem_center {r : twistedGroup σ}
    (hrc : r ∈ Subgroup.center (twistedGroup σ))
    (hrl : r ∈ rankOne (twistedRootGroup σ) (ng 0)) : r = 1 := by
  refine eq_one_of_mem_center_of_param (slLong_injective hσ) (fun h2 => ?_) hrc
    (rankOne_long_le_range_slLong' hσ hrl)
  refine slLong_wS_sq_not_central hσ (fun h => h2 (Subtype.ext ?_))
  push_cast
  exact h

end Long

section Short

variable (K) in
noncomputable def psi0 : Matrix.SpecialLinearGroup (Fin 2) K →* adjointGroup d4 K :=
  (𝕃 (nd 0)).subtype.comp
    (restrictEquiv (rootOperatorFamily d4) cartan_zero_two).symm.toMonoidHom

theorem psi0_upper (c : K) : psi0 K (sl2Upper c) = 𝕩 (Pi.single (nd 0) 1) c := by
  simp only [psi0, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, restrictEquiv_symm_upper,
    Subgroup.coe_subtype, rankOneRels_x]
  exact (xPar_simple _ _).symm

theorem psi0_lower (c : K) : psi0 K (sl2Lower c) = 𝕩 (-Pi.single (nd 0) 1) c := by
  simp only [psi0, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, restrictEquiv_symm_lower,
    Subgroup.coe_subtype, rankOneRels_y]
  exact (xPar_neg_simple _ _).symm

variable {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c)
include hσ

theorem slShort_wS_sq_val :
    (slShort σ hσ (wS (1 : Kˣ) * wS (1 : Kˣ)) : adjointGroup d4 K) = (hShortHom σ (-1))⁻¹ := by
  have h1 : (restrictEquiv (rootOperatorFamily d4) cartan_zero_two).symm
      (wS (1 : Kˣ) * wS (1 : Kˣ)) =
      (⟨torusElement d4 K (nd 0) (-1), torusElement_mem_rankOne (nd 0) (-1)⟩ : 𝕃 (nd 0))⁻¹ := by
    apply Subtype.ext
    have := map_wS_sq_eq_inv_torusElement (nd 0) (psi0 K) psi0_upper psi0_lower
    simpa [psi0] using this
  change phiShort σ ((restrictEquiv (rootOperatorFamily d4) cartan_zero_two).symm _) = _
  rw [h1, map_inv, phiShort_torusElement]

theorem slShort_wS_sq_not_central (h2 : (2 : K) ≠ 0) :
    slShort σ hσ (wS (1 : Kˣ) * wS (1 : Kˣ)) ∉ Subgroup.center (twistedGroup σ) := by
  intro hc
  obtain ⟨u, -, hu⟩ := exists_xLong hσ (c := (1 : K)) (map_one σ)
  have h1 := congrArg Subtype.val (Subgroup.mem_center_iff.mp hc u)
  simp only [Subgroup.coe_mul] at h1
  rw [slShort_wS_sq_val hσ, hu] at h1
  set x : adjointGroup d4 K := 𝕩 (Pi.single (nd 2) 1) 1 with hx
  have h3 : hShortHom σ (-1) * x * (hShortHom σ (-1))⁻¹ = x := by
    have h1' : x * (hShortHom σ (-1))⁻¹ = (hShortHom σ (-1))⁻¹ * x := h1
    calc hShortHom σ (-1) * x * (hShortHom σ (-1))⁻¹
        = hShortHom σ (-1) * (x * (hShortHom σ (-1))⁻¹) := by rw [mul_assoc]
      _ = x := by rw [h1']; group
  have hp : ∀ k : Fin d4.rank,
      (∑ j, d4.cartan k j * (Pi.single (nd 2) 1 : Fin d4.rank → ℤ) j) = d4.cartan k (nd 2) :=
    fun k => by simp [Pi.single_apply]
  have hσm : (Units.map σ.toMonoidHom (-1 : Kˣ)) = -1 := Units.ext (by simp)
  have hneg : ∀ z : ℤ, z = -1 → (((-1 : Kˣ) ^ z : Kˣ) : K) = -1 := fun z hz => by
    subst hz; simp
  rw [hShortHom_apply, hσm, hσm] at h3
  have e : torusElement d4 K (nd 0) (-1) * torusElement d4 K (nd 1) (-1) *
      torusElement d4 K (nd 3) (-1) * x *
        (torusElement d4 K (nd 0) (-1) * torusElement d4 K (nd 1) (-1) *
          torusElement d4 K (nd 3) (-1))⁻¹ =
      torusElement d4 K (nd 0) (-1) * (torusElement d4 K (nd 1) (-1) *
        (torusElement d4 K (nd 3) (-1) * x * (torusElement d4 K (nd 3) (-1))⁻¹) *
          (torusElement d4 K (nd 1) (-1))⁻¹) * (torusElement d4 K (nd 0) (-1))⁻¹ := by group
  rw [e] at h3
  have hr2 : IsRoot d4 (Pi.single (nd 2) 1) := isRoot_single d4 (nd 2)
  rw [hx, torusElement_conj_xPar (F := rootOperatorFamily d4) (nd 3) (-1) hr2 1, hp,
    torusElement_conj_xPar (F := rootOperatorFamily d4) (nd 1) (-1) hr2, hp,
    torusElement_conj_xPar (F := rootOperatorFamily d4) (nd 0) (-1) hr2, hp,
    hneg _ (by decide), hneg _ (by decide), hneg _ (by decide)] at h3
  have h5 := xPar_injective (F := rootOperatorFamily d4) (K := K) hr2 h3
  apply h2
  linear_combination -h5

theorem range_slShort' : (slShort σ hσ).range = (phiShortTw σ hσ).range := by
  rw [slShort, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (MulEquiv.surjective _),
    Subgroup.map_top]

theorem d4_short_eq_one_of_mem_center {r : twistedGroup σ}
    (hrc : r ∈ Subgroup.center (twistedGroup σ))
    (hrl : r ∈ rankOne (twistedRootGroup σ) (ng 1)) : r = 1 := by
  refine eq_one_of_mem_center_of_param (slShort_injective hσ)
    (fun h2 => slShort_wS_sq_not_central hσ h2) hrc ?_
  rw [range_slShort']
  exact rankOne_short_le_range hσ hrl

end Short

end D4

theorem eq_one_of_mem_center_D4 (n p e : ℕ) (hp : p.Prime) (hfund : IsFundTag .trialityD4)
    (hadm : StatedLieAdmissible .trialityD4 n p e)
    {R : Subgroup (modelUniv .trialityD4 n p e hp).K}
    (hR : R ∈ fundamentalSubgroups .trialityD4 (modelUniv .trialityD4 n p e hp).D)
    {r : (modelUniv .trialityD4 n p e hp).K} (hrR : r ∈ R)
    (hrc : r ∈ Subgroup.center (modelUniv .trialityD4 n p e hp).K) : r = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have he : 1 ≤ e := hadm.2.1
  have hK : Nat.card (GaloisField p (3 * e)) = (p ^ e) ^ 3 := by
    rw [GaloisField.card p (3 * e) (by omega), pow_mul']
  have hσ := sigma_three_of_card (σ := iterateFrobenius (GaloisField p (3 * e)) p e) (q := p ^ e)
    hK (fun c => iterateFrobenius_def p e c)
  refine eq_one_of_mem_center_of_all_nodes .trialityD4 n p e hp hfund hadm ?_ hR hrR hrc
  intro k r' hr' hrk
  match k with
  | ⟨0, _⟩ => exact d4_long_eq_one_of_mem_center hσ hr' hrk
  | ⟨1, _⟩ => exact d4_short_eq_one_of_mem_center hσ hr' hrk

end CFSG.ClassicalInvolution.ModelFacts
