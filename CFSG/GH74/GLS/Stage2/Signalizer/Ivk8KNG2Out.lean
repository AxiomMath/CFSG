module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93ResG2
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67G2Field

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.GH74.GLS.IVK.Proofs2 CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open CFSG.LieType.Ree (ReeTag)


variable {F : Type} [Field F] [Finite F]

theorem kn_g2_quadratic_fixed (hF2 : ringChar F ≠ 2) {p e : ℕ} (hp : p.Prime)
    (he : 1 ≤ e) (hKe : Nat.card F = (p ^ e) ^ 2) (δ : F ≃+* F) (hδ : ∀ c, δ c = c ^ (p ^ e))
    {α : MulAut (adjointGroup ReeTag.G2.tag F)} {g : adjointGroup ReeTag.G2.tag F}
    {a : Fin ReeTag.G2.tag.rank → Fˣ}
    (hαg : ∀ h : adjointGroup ReeTag.G2.tag F, (α h : ModGL ReeTag.G2.tag F) =
      (g : ModGL ReeTag.G2.tag F) * rootDiagUnit ReeTag.G2.tag a *
        Units.map (entrywiseHom δ.toRingHom) (h : ModGL ReeTag.G2.tag F) *
          (rootDiagUnit ReeTag.G2.tag a)⁻¹ * (g : ModGL ReeTag.G2.tag F)⁻¹)
    (hα : α ^ 2 = 1) :
    IsSimpleGroup ↥(fixSub α) ∧ ∃ x y : ↥(fixSub α), x * y ≠ y * x := by
  classical
  obtain ⟨hQ1, -⟩ := exceptional_Lang_quadratic_field_coset_conjugacy hp he F hKe δ.toRingHom hδ
  obtain ⟨β, hβ, hβα⟩ := hQ1 ReeTag.G2.tag
  obtain ⟨-, hconj⟩ := hβα g a
  obtain ⟨ψ, -, -, ⟨e₁, -⟩, -⟩ := hconj α hαg (by rw [← sq]; exact hα)
  have hβg : β = CFSG.RankThree.PartTwo.KFacts.g2FieldHom F δ :=
    MulEquiv.ext fun u => Subtype.ext
      ((hβ u).trans (CFSG.RankThree.PartTwo.KFacts.coe_g2FieldHom δ u).symm)
  obtain ⟨eG⟩ := CFSG.GH74.GLS.Stage2.Bender.Thm1.g2_fixSub_equiv δ
  rw [hβg] at e₁
  let eT : ↥(fixSub α) ≃* adjointGroup ReeTag.G2.tag (fixSubfield δ) := e₁.trans eG.symm
  have hkodd : ringChar (fixSubfield δ) ≠ 2 := ringChar_fixSubfield_ne_two hF2 δ
  obtain ⟨hsimple, ⟨x, y, hxy⟩, -⟩ :=
    odd_pinned_Chevalley_p_components ReeTag.G2.tag (fixSubfield δ) hkodd
  refine ⟨(MulEquiv.isSimpleGroup_congr eT).2 hsimple, eT.symm x, eT.symm y, fun h => hxy ?_⟩
  have := congrArg eT h
  rw [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at this
  exact this

theorem kn_g2_ree_fixed [CharP F ReeTag.G2.prime] {b : ℕ} (hb : 1 ≤ b)
    (hK : Nat.card F = 3 ^ (2 * b + 1)) {g : adjointGroup ReeTag.G2.tag F}
    (hα : (MulAut.conj g * ReeTag.G2.finiteReeAut F b) ^ 2 = 1) :
    IsSimpleGroup ↥(fixSub (MulAut.conj g * ReeTag.G2.finiteReeAut F b)) ∧
      ∃ x y : ↥(fixSub (MulAut.conj g * ReeTag.G2.finiteReeAut F b)), x * y ≠ y * x := by
  classical
  have : Finite (ModGL ReeTag.G2.tag F) := finite_modGL
  obtain ⟨⟨ψ, hψ⟩, -, -⟩ :=
    CFSG.LieType.Ree.G2_exceptional_coset_involution_fixed_p_components b F hK g hα
  obtain ⟨-, ⟨e, -⟩, -, -⟩ := fixed_centralizer_of_conj_eq hψ
  have hmap : ((ReeTag.G2.finiteReeAut F b).toMonoidHom.eqLocus (MonoidHom.id _)).map
      (adjointGroup ReeTag.G2.tag F).subtype = ReeTag.G2.reeGamma F b := rfl
  let Ψ' : ↥(fixSub (MulAut.conj g * ReeTag.G2.finiteReeAut F b)) ≃*
      ↥(ReeTag.G2.reeGamma F b) :=
    e.trans ((Subgroup.equivMapOfInjective _ _ Subtype.val_injective).trans
      (MulEquiv.subgroupCongr hmap))
  obtain ⟨hDs, ⟨x, y, hxy⟩, -, htop, -, -⟩ :=
    CFSG.ComponentClassification.CatalogueBSmallRee.small_Ree_whole_group_p_components b F hK
  have ec : ↥(commutator (ReeTag.G2.reeGamma F b)) ≃* ↥(ReeTag.G2.reeGamma F b) :=
    (MulEquiv.subgroupCongr (htop hb)).trans Subgroup.topEquiv
  have hΓs : IsSimpleGroup ↥(ReeTag.G2.reeGamma F b) := (MulEquiv.isSimpleGroup_congr ec).1 hDs
  refine ⟨(MulEquiv.isSimpleGroup_congr Ψ').2 hΓs, Ψ'.symm (ec x), Ψ'.symm (ec y),
    fun h => hxy ?_⟩
  apply ec.injective
  have := congrArg Ψ' h
  rw [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at this
  rw [map_mul, map_mul]
  exact this

theorem kn_g2_outer_fixed (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F)
    {α : MulAut (adjointGroup ReeTag.G2.tag F)} (hα : α ^ 2 = 1)
    (hnot : α ∉ (MulAut.conj : adjointGroup ReeTag.G2.tag F →*
      MulAut (adjointGroup ReeTag.G2.tag F)).range) :
    IsSimpleGroup ↥(fixSub α) ∧ ∃ x y : ↥(fixSub α), x * y ≠ y * x := by
  classical
  obtain ⟨p, f, hp, hp2, hf, hchar, hcard⟩ := exists_odd_prime_pow_card_of_odd hodd
  have hF2 : ringChar F ≠ 2 := hchar ▸ hp2
  have hquad : ∀ {p' e : ℕ}, p'.Prime → 1 ≤ e → Nat.card F = (p' ^ e) ^ 2 → ∀ δ : F ≃+* F,
      (∀ c, δ c = c ^ (p' ^ e)) → ∀ (g : adjointGroup ReeTag.G2.tag F)
        (a : Fin ReeTag.G2.tag.rank → Fˣ),
      (∀ h : adjointGroup ReeTag.G2.tag F, (α h : ModGL ReeTag.G2.tag F) =
        (g : ModGL ReeTag.G2.tag F) * rootDiagUnit ReeTag.G2.tag a *
          Units.map (entrywiseHom δ.toRingHom) (h : ModGL ReeTag.G2.tag F) *
            (rootDiagUnit ReeTag.G2.tag a)⁻¹ * (g : ModGL ReeTag.G2.tag F)⁻¹) →
      IsSimpleGroup ↥(fixSub α) ∧ ∃ x y : ↥(fixSub α), x * y ≠ y * x := by
    intro p' e hp' he hKe δ hδ g a hαg
    exact kn_g2_quadratic_fixed hF2 hp' he hKe δ hδ hαg hα
  by_cases hp3 : p = 3
  · subst hp3
    have : CharP F ReeTag.G2.prime := by
      have h := ringChar.charP F
      rw [hchar] at h
      exact h
    rcases G2_three_involution_inner_quadratic_or_exceptional hf hcard hα with
      ⟨g, a, hαg⟩ | ⟨e, he, hKe, δ, hδ, g, a, hαg⟩ | ⟨b, g, hfb, rfl⟩
    · exact absurd (ivk93res_inner_of_diag hαg) hnot
    · exact hquad Nat.prime_three he hKe δ hδ g a hαg
    · have hb : 1 ≤ b := by
        by_contra hb0
        have hb0' : b = 0 := by omega
        subst hb0'
        simp at hfb
        subst hfb
        simp at hcard
        omega
      have hK' : Nat.card F = 3 ^ (2 * b + 1) := hfb ▸ hcard
      exact kn_g2_ree_fixed hb hK' hα
  · rcases odd_F4_E8_G2_involution_inner_or_quadratic
        (Or.inr (Or.inr ⟨rfl, by rw [hchar]; exact hp3⟩)) hodd hα with
      ⟨g, a, hαg⟩ | ⟨p', e, hp', he, hKe, δ, hδ, g, a, hαg⟩
    · exact absurd (ivk93res_inner_of_diag hαg) hnot
    · exact hquad hp' he hKe δ hδ g a hαg

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
