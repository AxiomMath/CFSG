module

public import CFSG.Walter.Ree.Model.JTHyp
public import CFSG.LieType.Ree.G2ExceptionalCosetInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorOddInner

public noncomputable section

namespace CFSG.ComponentClassification.ExcSelector

open CFSG Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.G2.prime]

theorem two_mul_504_ne (r : ℕ) : 2 * 504 ≠ r * (r ^ 2 - 1) := by
  intro h
  have hr : r < 11 := by
    by_contra hc
    push Not at hc
    have h1 : 120 ≤ r ^ 2 - 1 := by
      have : 11 ^ 2 ≤ r ^ 2 := Nat.pow_le_pow_left hc 2
      omega
    have : 11 * 120 ≤ r * (r ^ 2 - 1) := Nat.mul_le_mul hc h1
    omega
  interval_cases r <;> norm_num at h

theorem reeGamma_component_not_smallType {b : ℕ} (hK : Nat.card K = 3 ^ (2 * b + 1))
    {M : Subgroup (ModGL ReeTag.G2.tag K)}
    (hM : Assembly.IsComponentOf M (ReeTag.G2.reeGamma K b)) : ¬ SmallType M := by
  set Γ := ReeTag.G2.reeGamma K b with hΓ
  obtain ⟨hDs, hnab, -, htop, hzero, -⟩ :=
    CatalogueBSmallRee.small_Ree_whole_group_p_components b K hK
  set D := commutator Γ
  set J := D.map Γ.subtype with hJ
  have eJ : D ≃* J := D.equivMapOfInjective _ Subtype.val_injective
  have : IsSimpleGroup J := (MulEquiv.isSimpleGroup_congr eJ).1 hDs
  have hJF : J ≤ Γ := Subgroup.map_subtype_le D
  have hJsub : J.subgroupOf Γ = D :=
    Subgroup.comap_map_eq_self_of_injective Subtype.val_injective D
  have hJn : (J.subgroupOf Γ).Normal := by
    rw [hJsub]
    exact Subgroup.commutator_normal ⊤ ⊤
  have hsolv : Group.IsSolvable (Γ ⧸ J.subgroupOf Γ) := by
    have : Group.IsSolvable (Abelianization Γ) := inferInstance
    exact Group.isSolvable_of_surjective
      (f := (QuotientGroup.quotientMulEquivOfEq hJsub.symm).toMonoidHom)
      (QuotientGroup.quotientMulEquivOfEq hJsub.symm).surjective
  rw [eq_of_isComponentOf_of_normal_simple hJF hJn hsolv hM, ← smallType_congr eJ]
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem ReeTag.G2.tag).length
  have hZ : center D = ⊥ := center_eq_bot_of_isSimpleGroup' hnab
  rcases Nat.eq_zero_or_pos b with rfl | hb
  ·
    have hD := (hzero rfl w₀ hw₀).2.1
    refine not_smallType_of_card hZ (fun r _ => by rw [hD]; exact two_mul_504_ne r) ?_ ?_
    · rw [hD]
      norm_num
    · rw [hD]
      norm_num
  ·
    have eD : D ≃* Γ := (MulEquiv.subgroupCongr (htop hb)).trans Subgroup.topEquiv
    rw [smallType_congr eD]
    obtain ⟨hE, hE8, -⟩ := CFSG.Walter.Ree.Model.smallRee_E8_sylow hK hw₀
    have hcard := (small_Ree_Borel_coset_Sylow_action b K hK w₀ hw₀).2.2.2.2.2.2.2.2.2.1
    have h27 : 27 ∣ Nat.card Γ := by
      rw [hcard, show (27 : ℕ) = 3 ^ 3 by norm_num]
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_right
        (pow_dvd_pow_of_dvd (dvd_pow_self 3 (by omega)) 3) _) _
    exact not_smallType_of_elementary (center_reeGamma_G2_eq_bot hK) _ hE8.ge
      (fun h => by rw [h] at h27; norm_num at h27) (fun h => by rw [h] at h27; norm_num at h27)

theorem small_ree_involution_not_smallType {b : ℕ} (hK : Nat.card K = 3 ^ (2 * b + 1))
    (g : adjointGroup ReeTag.G2.tag K)
    (hα : (MulAut.conj g * ReeTag.G2.finiteReeAut K b) ^ 2 = 1)
    {L : Subgroup (adjointGroup ReeTag.G2.tag K)}
    (hL : Assembly.IsComponentOf L (fixedSubgroup (MulAut.conj g * ReeTag.G2.finiteReeAut K b))) :
    ¬ SmallType L := by
  obtain ⟨⟨ψ, hψ⟩, -, -⟩ := G2_exceptional_coset_involution_fixed_p_components b K hK g hα
  set α := MulAut.conj g * ReeTag.G2.finiteReeAut K b
  have hc : MulAut.congr ψ α = ψ * α * ψ⁻¹ := MulEquiv.ext fun _ => rfl
  have hfix := fixedSubgroup_congr ψ α
  rw [hc, hψ] at hfix
  refine not_smallType_of_map_eq ((adjointGroup ReeTag.G2.tag K).subtype.comp ψ.toMonoidHom)
    (Subtype.val_injective.comp ψ.injective) (MonoidHom.id _) Function.injective_id
    (X := ReeTag.G2.reeGamma K b) ?_ (fun M hM => reeGamma_component_not_smallType hK hM) hL
  rw [← Subgroup.map_map, ← hfix, Subgroup.map_id]
  rfl

end CFSG.ComponentClassification.ExcSelector
