module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5C3qP510Inputs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FA8FinF4Core
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FA8FinPre
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SEFin1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5CoverAct

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82FactReflCentQ6_of (hS : Asc82SchurU43) : Asc82FactReflCentQ6 := by
  intro G _ _ L z hL hI4 Q₁ Q₂ hQ₁L hQ₂L h₁ h₂ hcomm hcard hcen _ σ hσN _ hσz ⟨α₁, hα₁⟩ ⟨α₂, hα₂⟩
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
  have hdim := hφ.finrank_eq
  have hsgn := hφ.quadSign_eq
  obtain ⟨hztt, hW, hP, hsigP⟩ := fa8fin_type4 hL hφ hcov hI4 hzL
  obtain ⟨R, -, hRΩ, hRmem, -, -, hcent, hRsq, hpartner⟩ :=
    fa8fin_image hcov hle hcard hzQ hzc hsq hpart
  obtain ⟨e, he⟩ := t5_exists_model hL hφ
  have hm : Module.finrank (ZMod 3) V = 6 ∧ quadSign Q = -1 := ⟨hdim, hsgn⟩
  have hzN : z ∈ normalizer (L : Set G) := Subgroup.le_normalizer hzL
  have hσzN : σ * z ∈ normalizer (L : Set G) := Subgroup.mul_mem _ hσN hzN
  let Φ := ffInducesHom hm e (L := L)
  obtain ⟨t₀, h0, h01, h0Φ⟩ := simHasDim_of_inducesTypeSome hm e hσN hα₁
  obtain ⟨t₁, h1, h11, h1Φ⟩ := simHasDim_of_inducesTypeSome hm e hσzN hα₂
  have hΦz : Φ ⟨z, hzN⟩ =
      projOrthToProjSim Q (toProj Q (sec5cdPhi φ ⟨z, hzL⟩)) := by
    rw [show Φ ⟨z, hzN⟩ = ffInducesHom hm e ⟨(⟨z, hzL⟩ : ↥L), hzN⟩ from rfl,
      ffInducesHom_of_mem hm e ⟨z, hzL⟩ hzN, he]
    rfl
  have hac : (⟨σ, hσN⟩ : ↥(normalizer (L : Set G))) * ⟨z, hzN⟩ = ⟨z, hzN⟩ * ⟨σ, hσN⟩ :=
    Subtype.ext hσz
  have hcommΦ : Φ ⟨σ, hσN⟩ * Φ ⟨z, hzN⟩ = Φ ⟨z, hzN⟩ * Φ ⟨σ, hσN⟩ := by
    rw [← map_mul, hac, map_mul]
  have hcl : projOrthToProjSim Q (toProj Q (t₀ * sec5cdPhi φ ⟨z, hzL⟩)) =
      projOrthToProjSim Q (toProj Q (sec5cdPhi φ ⟨z, hzL⟩ * t₀)) := by
    simp only [map_mul]
    rw [h0Φ, ← hΦz]
    exact hcommΦ
  have hcomm' : toProj Q (t₀ * sec5cdPhi φ ⟨z, hzL⟩) =
      toProj Q (sec5cdPhi φ ⟨z, hzL⟩ * t₀) := projOrthToProjSim_injective hcl
  have hprod : toProj Q t₁ = toProj Q (t₀ * sec5cdPhi φ ⟨z, hzL⟩) := by
    apply projOrthToProjSim_injective
    rw [h1Φ, show Φ ⟨σ * z, hσzN⟩ = Φ ⟨σ, hσN⟩ * Φ ⟨z, hzN⟩ from map_mul Φ ⟨σ, hσN⟩ ⟨z, hzN⟩,
      map_mul, map_mul, h0Φ, hΦz]
  have hcore := fa8fin_refl_cent hQ hdim hztt hW hP hsigP hRΩ hcent hRsq hpartner h0 h01 h1 h11
    hcomm' hprod
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (Φ ⟨σ, hσN⟩)
  have hcovσ : CoverAct L φ σ x :=
    t5_coverAct_of_inducesViaP hL hφ he (ffInducesHom_spec hm e ⟨σ, hσN⟩) hx
  have hact : ∀ g : OGroup Q, simAct Q x g = t₀ * g * t₀⁻¹ := by
    intro g
    rw [← projSimActO_mk, hx, ← h0Φ, projSimActO_projOrthToProjSim_toProj]
  have hpow : ∀ g ∈ Q₁ ⊔ Q₂, g ^ 32 = 1 := by
    intro g hg
    have h := pow_card_eq_one' (G := ↥(Q₁ ⊔ Q₂)) (x := ⟨g, hg⟩)
    rw [hcard] at h
    exact congrArg Subtype.val h
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  let lq : ↥L := ⟨q, hle hq⟩
  let l' : ↥L := ⟨σ * q * σ⁻¹, (Subgroup.mem_normalizer_iff.mp hσN q).mp (hle hq)⟩
  have hfix : ((φ l' : omegaGroup hQ) : OGroup Q) = ((φ lq : omegaGroup hQ) : OGroup Q) := by
    have h := hcovσ.2 lq l' rfl
    rw [h, hact]
    exact (mul_inv_eq_iff_eq_mul.mpr (hcore _ (hRmem lq hq)))
  have hq32 : lq ^ 2 ^ 5 = 1 := Subtype.ext (hpow q hq)
  have hl32 : l' ^ 2 ^ 5 = 1 := Subtype.ext (by
    show (σ * q * σ⁻¹) ^ 32 = 1
    rw [conj_pow, hpow q hq, mul_one, mul_inv_cancel])
  have hl : l' = lq := fa8fin_cover_inj hcov hl32 hq32 (Subtype.ext hfix)
  have hσq : σ * q * σ⁻¹ = q := congrArg Subtype.val hl
  exact (mul_inv_eq_iff_eq_mul.mp hσq).symm

end CFSG.OddStandard.SmallF3.Omega
