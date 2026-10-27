module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl2FamExc
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl2FamToral
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl2FamE8E7
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE8Inner

public noncomputable section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open CFSG
  CFSG.ComponentClassification.CatLeafProof
  CFSG.ComponentClassification
open CFSG CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.LieType.CurtisTits
open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

section


theorem cl24_family_E8_of_inner
    (hinner : Cl24ExcInnerDiag .E8) : Cl24OddFamily .E8 :=
  cl24_family_of_explicit (τ := .E8) (by decide) (fun _ _ _ _ h => h.2)
    fun K _ _ p f hp hp2 hf hK β hβ _ _ Ψ _ hL =>
      cl24_odd_F4_E8_G2_explicit (Or.inr (Or.inl rfl)) hinner hp hp2 (fun h => absurd h
        (by decide)) hf
        hK β hβ Ψ hL

end

section


theorem cl24_e8_toral_D8_component
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f)
    {M : Subgroup (toralCentralizer .E8 K (bitsTuple e8BitsD8))} (hM : IsComponent M)
    {Rel : ℕ → Prop} (hRel : ∀ f', f' = f → Rel f' := by cl24_rel) :
    Cl24Q p Rel M := by
  classical
  obtain ⟨hf, -⟩ := one_le_and_three_le_of_card hp hp2 hK
  have : CharP K p :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hK
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  have hadm : StatedLieAdmissible .POmegaPlus 8 p f := ⟨hp, hf, by norm_num⟩
  obtain ⟨hSX, hSn, hsolv, -, -⟩ :=
    odd_toral_involution_centralizer_p_component_root_reduction .E8 K hK2 _
      (bitsTuple_mem (K := K) e8BitsD8)
  obtain ⟨-, -, -, hqs, hlie⟩ := exists_psi_D8_E8 hp hp2 hK
  let e₁ : ↥(⨆ k, e8D8Chain K k) ≃*
      rootSpan .E8 K (rootCharKernel (bitsTuple (K := K) e8BitsD8)) :=
    ((⨆ k, e8D8Chain K k).equivMapOfInjective _ (adjointGroup .E8 K).subtype_injective).trans
      (MulEquiv.subgroupCongr (map_subtype_iSup_e8D8Chain hK2))
  let e₂ := Subgroup.subgroupOfEquivOfLe hSX
  have hq := LocalCores.isQuasisimple_of_mulEquiv (e₂.trans e₁.symm).symm hqs
  have hMeq := eq_of_isComponent_of_normal_quasisimple hq hsolv hM
  let e : M ≃* ↥(⨆ k, e8D8Chain K k) := (MulEquiv.subgroupCongr hMeq).trans (e₂.trans e₁.symm)
  exact ⟨.POmegaPlus, 8, f, hRel f rfl, hadm, lieModel_of_mulEquiv
    (QuotientGroup.congr _ _ e.symm (Subgroup.map_center_eq e.symm)) hlie⟩

end

section


theorem cl24_excInnerDiag_E8
    : Cl24ExcInnerDiag .E8 := by
  intro K _ _ p f hp hp2 hKp α g a hαg hαo L hL
  obtain ⟨hf, -⟩ := one_le_and_three_le_of_card hp hp2 hKp
  have hKodd : Odd (Nat.card K) := by
    rw [hKp]
    exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  have : CharP K p := finite_field_prime_power_characteristic hp hf hKp
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  have hα : α ^ 2 = 1 := hαo ▸ pow_orderOf_eq_one α
  have hα1 : α ≠ 1 := fun h => by
    rw [h, orderOf_one] at hαo
    exact absurd hαo (by norm_num)
  obtain ⟨b, hb, hb1, ⟨Θ⟩⟩ :=
    exists_toralCentralizer_equiv_of_innerDiag (Or.inr (Or.inr (Or.inr rfl))) hKodd hαg hα
  refine cl24_of_mulEquiv (L.equivMapOfInjective Θ.toMonoidHom Θ.injective)
    (cl24_toralCentralizer_component_of_orbitCheck hK2 e8SignOrbit_check
      (fun ρ hρ hne N hN => ?_) hb
      (hb1 hα1) (LocalCores.isComponent_map_mulEquiv Θ hL))
  have hlen : e8SignReps.length = 3 := rfl
  rw [hlen] at hρ
  interval_cases ρ
  · exact absurd (by funext i; revert i; decide) hne
  · exact cl24_e8_toral_D8_component hp hp2 hKp hN
  ·
    have hmap := map_conj_toralCentralizer_of_maskAct (K := K) hK2 e8MaskWord e8BitsE7
    rw [maskAct_e8MaskWord] at hmap
    let e : toralCentralizer .E8 K (bitsTuple e8BitsE7) ≃*
        toralCentralizer .E8 K (bitsTuple (listMask (e8SignReps.getD 2 []))) :=
      ((toralCentralizer .E8 K _).equivMapOfInjective _ (MulAut.conj _).injective).trans
        (MulEquiv.subgroupCongr hmap)
    exact cl24_of_mulEquiv (N.equivMapOfInjective e.symm.toMonoidHom
      e.symm.injective) (cl24_e8_toral_E7_component hp hp2 hKp
        (LocalCores.isComponent_map_mulEquiv e.symm hN))

theorem cl24_family_E8 : Cl24OddFamily .E8 :=
  cl24_family_E8_of_inner cl24_excInnerDiag_E8

end

end CFSG.OddStandard.SmallF3.HypA2Leaves
