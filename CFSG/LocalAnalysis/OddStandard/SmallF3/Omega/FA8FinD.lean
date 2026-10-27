module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5C3qP510Inputs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FA8FinCore
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FA8FinOP
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FA8FinPre
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGAutCentTrans
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGAutCentInv
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5CoverAct

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82FactQCentOrd6_of (hS : Asc82SchurU43) : Asc82FactQCentOrd6 := by
  intro G _ _ L z hL hI4 Q₁ Q₂ hQ₁L hQ₂L h₁ h₂ hcomm hcard hcen _ Y hYN hYC
  have hz2 : orderOf z = 2 := hI4.1
  have hzz : z * z = 1 := by rw [← pow_two, ← hz2]; exact pow_orderOf_eq_one z
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz2
    omega
  obtain ⟨hzQ, hzc, hsq, hpart⟩ := fa8fin_partner hzz hz1 h₁ h₂ hcomm hcen
  have hle : Q₁ ⊔ Q₂ ≤ L := sup_le hQ₁L hQ₂L
  have hzL : z ∈ L := hle hzQ
  obtain ⟨V, _, _, _, Q, hQ, φ, hφ⟩ := t5_exists_cover hS hL
  have hcov : OddCentralCover φ := hφ.oddCentralCover hL
  obtain ⟨hztt, hW, hP, hsigP⟩ := fa8fin_type4 hL hφ hcov hI4 hzL
  obtain ⟨R, hRcard, -, -, hRex, hsR, hcent, -, hpartner⟩ :=
    fa8fin_image hcov hle hcard hzQ hzc hsq hpart
  obtain ⟨e, he⟩ := t5_exists_model hL hφ
  have h6 : (Module.finrank (ZMod 3) V = 5 ∧ quadSign Q = 1) ∨
      (Module.finrank (ZMod 3) V = 6 ∧ (quadSign Q = 1 ∨ quadSign Q = -1)) :=
    Or.inr ⟨hφ.finrank_eq, Or.inr hφ.quadSign_eq⟩
  have hLp : commutator ↥L = ⊤ := hL.1.1.commutator_eq_top
  rw [fg_relIndex_eq_card_range hQ h6 e hLp hYN]
  have hle' : (fgThetaR hQ h6 e hYN).range ≤ (fgIotaP (FGSplit.comm hQ hztt)).range := by
    rintro _ ⟨y, rfl⟩
    have hyN : (y : G) ∈ normalizer (L : Set G) := hYN y.2
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (ffTheta hQ h6 e ⟨(y : G), hyN⟩)
    have hcovy : CoverAct L φ (y : G) x :=
      t5_coverAct_of_inducesViaP hL hφ he (ffTheta_induces hQ h6 e ⟨(y : G), hyN⟩) hx
    have hfix : ∀ g ∈ R, simAct Q x g = g := by
      intro g hg
      obtain ⟨l, hlM, rfl⟩ := hRex g hg
      exact t5_cent_map_mem hcovy ((Subgroup.mem_centralizer_iff.mp (hYC y.2) (l : G) hlM).symm)
    obtain ⟨b, hb⟩ := fa8fin_core hQ hztt hW R hsR hRcard hcent hpartner hfix
    exact ⟨b, hb.symm.trans hx⟩
  have hWpos : 0 < Module.finrank (ZMod 3) (FGSplit.comm hQ hztt).W := by
    show 0 < Module.finrank (ZMod 3) (commSp (sec5cdPhi φ ⟨z, hzL⟩))
    rw [hW]
    norm_num
  have hcardP : Nat.card (fgIotaP (FGSplit.comm hQ hztt)).range = 8 := by
    rw [← natCard_oGroup_two_minus (nondegenerate_restrict_fixSp hQ hztt) hP hsigP]
    exact Nat.card_congr (MonoidHom.ofInjective (fg_iotaP_injective _ hWpos)).toEquiv.symm
  have hdvd : Nat.card (fgThetaR hQ h6 e hYN).range ∣ 8 := by
    rw [← hcardP]
    exact Subgroup.card_dvd_of_le hle'
  refine ⟨hdvd, fun h8 => ?_⟩
  haveI : Finite ↥(fgIotaP (FGSplit.comm hQ hztt)).range :=
    Nat.finite_of_card_ne_zero (by rw [hcardP]; norm_num)
  have heq : (fgThetaR hQ h6 e hYN).range = (fgIotaP (FGSplit.comm hQ hztt)).range :=
    Subgroup.eq_of_le_of_card_ge hle' (by rw [h8, hcardP])
  obtain ⟨a', b', hab'⟩ : ∃ a b : OGroup (Q.restrict (FGSplit.comm hQ hztt).P), a * b ≠ b * a :=
    fa8fin_oGroup_two_minus_nonabelian (nondegenerate_restrict_fixSp hQ hztt) hP hsigP
  obtain ⟨y₁, hy₁⟩ : fgIotaP (FGSplit.comm hQ hztt) a' ∈ (fgThetaR hQ h6 e hYN).range :=
    heq ▸ ⟨a', rfl⟩
  obtain ⟨y₂, hy₂⟩ : fgIotaP (FGSplit.comm hQ hztt) b' ∈ (fgThetaR hQ h6 e hYN).range :=
    heq ▸ ⟨b', rfl⟩
  refine ⟨(y₁ : G), y₁.2, (y₂ : G), y₂.2, fun hmem => hab' ?_⟩
  have hker : y₁ * y₂ * y₁⁻¹ * y₂⁻¹ ∈ (fgThetaR hQ h6 e hYN).ker := by
    rw [fg_thetaR_ker hQ h6 e hLp hYN, Subgroup.mem_subgroupOf]
    exact hmem
  rw [MonoidHom.mem_ker] at hker
  simp only [map_mul, map_inv] at hker
  rw [hy₁, hy₂] at hker
  have hker' : fgIotaP (FGSplit.comm hQ hztt) (a' * b' * a'⁻¹ * b'⁻¹) = 1 := by
    simpa only [map_mul, map_inv] using hker
  have hcomm' := fg_iotaP_injective _ hWpos (hker'.trans (map_one _).symm)
  calc a' * b' = (a' * b' * a'⁻¹ * b'⁻¹) * (b' * a') := by group
    _ = b' * a' := by rw [hcomm', one_mul]

end CFSG.OddStandard.SmallF3.Omega
