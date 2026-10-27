module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.P911OddCycFix
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.P911ExcCommon
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FG2
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67G2Aut
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67G2Field

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.P911

open Subgroup CFSG CFSG.ComponentClassification.OuterAutomorphisms CFSG.Blueprint.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.GH74.GLS.IVK.Proofs2
open CFSG.LieType.Ree (ReeTag)


section Fixed

variable {F : Type} [Field F] [Finite F]

theorem g2_quadratic_fixed_equiv {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e)
    (hKe : Nat.card F = (p ^ e) ^ 2) (δ : F ≃+* F) (hδ : ∀ c, δ c = c ^ (p ^ e))
    {α : MulAut (adjointGroup ReeTag.G2.tag F)} {g : adjointGroup ReeTag.G2.tag F}
    {a : Fin ReeTag.G2.tag.rank → Fˣ}
    (hαg : ∀ h : adjointGroup ReeTag.G2.tag F, (α h : ModGL ReeTag.G2.tag F) =
      (g : ModGL ReeTag.G2.tag F) * rootDiagUnit ReeTag.G2.tag a *
        Units.map (entrywiseHom δ.toRingHom) (h : ModGL ReeTag.G2.tag F) *
          (rootDiagUnit ReeTag.G2.tag a)⁻¹ * (g : ModGL ReeTag.G2.tag F)⁻¹)
    (hα : α ^ 2 = 1) :
    Nonempty (↥(fixSub α) ≃* adjointGroup ReeTag.G2.tag (fixSubfield δ)) := by
  classical
  obtain ⟨hQ1, -⟩ := exceptional_Lang_quadratic_field_coset_conjugacy hp he F hKe δ.toRingHom hδ
  obtain ⟨β, hβ, hβα⟩ := hQ1 ReeTag.G2.tag
  obtain ⟨-, hconj⟩ := hβα g a
  obtain ⟨ψ, -, -, ⟨e₁, -⟩, -⟩ := hconj α hαg (by rw [← sq]; exact hα)
  have hββ : β = CFSG.RankThree.PartTwo.KFacts.g2FieldHom F δ :=
    MulEquiv.ext fun u => Subtype.ext ((hβ u).trans
      (CFSG.RankThree.PartTwo.KFacts.coe_g2FieldHom (σ := δ) (h := u)).symm)
  obtain ⟨e₂⟩ := CFSG.GH74.GLS.Stage2.Bender.Thm1.g2_fixSub_equiv (K := F) δ
  refine ⟨e₁.trans ?_ |>.trans e₂.symm⟩
  exact MulEquiv.subgroupCongr (by rw [hββ]; rfl)

theorem g2_quadratic_fixOddFree (hF2 : ringChar F ≠ 2) {p e : ℕ}
    (hp : p.Prime) (he : 1 ≤ e) (hKe : Nat.card F = (p ^ e) ^ 2) (δ : F ≃+* F)
    (hδ : ∀ c, δ c = c ^ (p ^ e)) {α : MulAut (adjointGroup ReeTag.G2.tag F)}
    {g : adjointGroup ReeTag.G2.tag F} {a : Fin ReeTag.G2.tag.rank → Fˣ}
    (hαg : ∀ h : adjointGroup ReeTag.G2.tag F, (α h : ModGL ReeTag.G2.tag F) =
      (g : ModGL ReeTag.G2.tag F) * rootDiagUnit ReeTag.G2.tag a *
        Units.map (entrywiseHom δ.toRingHom) (h : ModGL ReeTag.G2.tag F) *
          (rootDiagUnit ReeTag.G2.tag a)⁻¹ * (g : ModGL ReeTag.G2.tag F)⁻¹)
    (hα : α ^ 2 = 1) : FixOddFree α := by
  have : Finite (ModGL ReeTag.G2.tag F) := finite_modGL
  obtain ⟨e₀⟩ := g2_quadratic_fixed_equiv hp he hKe δ hδ hαg hα
  have hkodd : ringChar (fixSubfield δ) ≠ 2 := ringChar_fixSubfield_ne_two hF2 δ
  obtain ⟨hsimple, ⟨x, y, hxy⟩, -⟩ :=
    odd_pinned_Chevalley_p_components ReeTag.G2.tag (fixSubfield δ) hkodd
  refine fixOddFree_of_simple_nonabelian α ((MulEquiv.isSimpleGroup_congr e₀.symm).1 hsimple)
    ⟨e₀.symm x, e₀.symm y, fun h => hxy (e₀.symm.injective (by rw [map_mul, map_mul]; exact h))⟩

theorem g2_ree_fixed_equiv [CharP F ReeTag.G2.prime] {b : ℕ}
    (hK : Nat.card F = 3 ^ (2 * b + 1)) {g : adjointGroup ReeTag.G2.tag F}
    (hα : (MulAut.conj g * ReeTag.G2.finiteReeAut F b) ^ 2 = 1) :
    Nonempty (↥(fixSub (MulAut.conj g * ReeTag.G2.finiteReeAut F b)) ≃*
      ↥(ReeTag.G2.reeGamma F b)) := by
  classical
  have : Finite (ModGL ReeTag.G2.tag F) := finite_modGL
  obtain ⟨⟨ψ, hψ⟩, -, -⟩ :=
    CFSG.LieType.Ree.G2_exceptional_coset_involution_fixed_p_components b F hK g hα
  obtain ⟨-, ⟨e, -⟩, -, -⟩ := fixed_centralizer_of_conj_eq hψ
  have hmap : ((ReeTag.G2.finiteReeAut F b).toMonoidHom.eqLocus (MonoidHom.id _)).map
      (adjointGroup ReeTag.G2.tag F).subtype = ReeTag.G2.reeGamma F b := rfl
  exact ⟨e.trans ((Subgroup.equivMapOfInjective _ _ Subtype.val_injective).trans
      (MulEquiv.subgroupCongr hmap))⟩

theorem g2_ree_fixOddFree [CharP F ReeTag.G2.prime] {b : ℕ} (hb : 1 ≤ b)
    (hK : Nat.card F = 3 ^ (2 * b + 1)) {g : adjointGroup ReeTag.G2.tag F}
    (hα : (MulAut.conj g * ReeTag.G2.finiteReeAut F b) ^ 2 = 1) :
    FixOddFree (MulAut.conj g * ReeTag.G2.finiteReeAut F b) := by
  classical
  have : Finite (ModGL ReeTag.G2.tag F) := finite_modGL
  obtain ⟨Ψ⟩ := g2_ree_fixed_equiv hK hα
  obtain ⟨hDs, ⟨x, y, hxy⟩, -, htop, -, -⟩ :=
    CFSG.ComponentClassification.CatalogueBSmallRee.small_Ree_whole_group_p_components b F hK
  have ec : ↥(commutator (ReeTag.G2.reeGamma F b)) ≃* ↥(ReeTag.G2.reeGamma F b) :=
    (MulEquiv.subgroupCongr (htop hb)).trans Subgroup.topEquiv
  have hΓs : IsSimpleGroup ↥(ReeTag.G2.reeGamma F b) := (MulEquiv.isSimpleGroup_congr ec).1 hDs
  refine fixOddFree_of_simple_nonabelian _ ((MulEquiv.isSimpleGroup_congr Ψ).2 hΓs)
    ⟨Ψ.symm (ec x), Ψ.symm (ec y), fun h => hxy (ec.injective ?_)⟩
  have := congrArg Ψ h
  rw [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at this
  rw [map_mul, map_mul]
  exact this

theorem g2_outer_fixOddFree (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F)
    {α : MulAut (adjointGroup ReeTag.G2.tag F)} (hα : α ^ 2 = 1)
    (hnot : α ∉ (MulAut.conj : adjointGroup ReeTag.G2.tag F →*
      MulAut (adjointGroup ReeTag.G2.tag F)).range) : FixOddFree α := by
  classical
  obtain ⟨p, f, hp, hp2, hf, hchar, hcard⟩ := exists_odd_prime_pow_card_of_odd hodd
  have hF2 : ringChar F ≠ 2 := hchar ▸ hp2
  by_cases hp3 : p = 3
  · subst hp3
    have : CharP F ReeTag.G2.prime := by
      have h := ringChar.charP F
      rw [hchar] at h
      exact h
    rcases G2_three_involution_inner_quadratic_or_exceptional hf hcard hα with
      ⟨g, a, hαg⟩ | ⟨e, he, hKe, δ, hδ, g, a, hαg⟩ | ⟨b, g, hfb, rfl⟩
    · exact absurd (ivk93res_inner_of_diag hαg) hnot
    · exact g2_quadratic_fixOddFree hF2 Nat.prime_three he hKe δ hδ hαg hα
    · have hb : 1 ≤ b := by
        by_contra hb0
        have hb0' : b = 0 := by omega
        subst hb0'
        simp at hfb
        subst hfb
        simp at hcard
        omega
      have hK' : Nat.card F = 3 ^ (2 * b + 1) := hfb ▸ hcard
      exact g2_ree_fixOddFree hb hK' hα
  · rcases odd_F4_E8_G2_involution_inner_or_quadratic
        (Or.inr (Or.inr ⟨rfl, by rw [hchar]; exact hp3⟩)) hodd hα with
      ⟨g, a, hαg⟩ | ⟨p', e, hp', he, hKe, δ, hδ, g, a, hαg⟩
    · exact absurd (ivk93res_inner_of_diag hαg) hnot
    · exact g2_quadratic_fixOddFree hF2 hp' he hKe δ hδ hαg hα

end Fixed

section Cell

theorem g2_fixOddFree {F : Type} [Field F] [Finite F] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) (hcard : Nat.card F = p ^ f) (α : MulAut ↥(adjointGroup Tag.G2 F))
    (hα2 : α * α = 1) (hα1 : α ≠ 1) : FixOddFree α := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (ModGL Tag.G2 F) := finite_modGL
  have hodd : Odd (Nat.card F) := by rw [hcard]; exact (hp.odd_of_ne_two hp2).pow
  have hα : α ^ 2 = 1 := by rw [sq]; exact hα2
  by_cases h3 : p = 3 ∧ f = 1
  · obtain ⟨rfl, rfl⟩ := h3
    exact g2_three_fixOddFree (Ivk47ab.lieModel_G2g hp hf (by norm_num) hcard) α hα2 hα1
  · have hq5 := five_le_pow_of_ne_three_one hp hp2 hf h3
    by_cases hin : α ∈ (MulAut.conj : ↥(adjointGroup Tag.G2 F) →*
        MulAut ↥(adjointGroup Tag.G2 F)).range
    · have hm := Ivk47ab.lieModel_G2g hp hf (by omega) hcard
      have hadm : StatedLieAdmissible .G2 0 p f := ⟨hp, hf, rfl, by omega⟩
      obtain ⟨ψ⟩ := equiv_modelUniv_g2 hp hp2 hf (by omega) hm
      have hO : InvOddCore ↥(adjointGroup Tag.G2 F) :=
        invOddCore_of_equiv ψ (CFSG.ClassicalInvolution.Asc77.thm5IH_g2_oddCoreTrivial hp2 hadm)
      exact fixOddFree_of_inner center_adjointGroup_eq_bot hO hin hα2 hα1
    · exact g2_outer_fixOddFree hodd (by rw [hcard]; exact hq5) hα hin

theorem oddCoreCyclic_g2 {F : Type} [Field F] [Finite F] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) (hcard : Nat.card F = p ^ f) : OddCoreCyclic ↥(adjointGroup Tag.G2 F) := by
  classical
  have : Finite (ModGL Tag.G2 F) := finite_modGL
  obtain ⟨-, H, _, _, Θ, hΘ⟩ :=
    CFSG.GH74.GLS.Stage2.Bender.Thm1.g2_aut_facts hp hp2 hf F hcard
  exact oddCoreCyclic_of_outCyc_fix center_adjointGroup_eq_bot (isCyclic_outer_of_hom Θ hΘ)
    fun α hα2 hα1 => g2_fixOddFree hp hp2 hf hcard α hα2 hα1

theorem core911_g2 : Core911G2 := by
  intro Y _ _ _ _ hF
  obtain ⟨p, f, hp, hf, hp2, hm⟩ := hF
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := Ivk47ab.exists_equiv_of_lieModel hm
  have : Finite (ModGL Tag.G2 F) := finite_modGL
  exact no911_of_mulEquiv e (no911_of_oddCoreCyclic (oddCoreCyclic_g2 hp hp2 hf hcard))

end Cell

end CFSG.GH74.GLS.Stage2.Bender.Thm2.P911
