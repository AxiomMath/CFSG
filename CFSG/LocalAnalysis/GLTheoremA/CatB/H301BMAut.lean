module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BGenTr
public import CFSG.Monster.SteinbergMCatalogInner
public import CFSG.Sporadic.Bridge.MonsterModelsGriess
public import CFSG.LocalAnalysis.GLTheoremA.S8.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H301B

open CFSG.Monster.Existence CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S8


private theorem mGriess_central_eq_one (t : MGriess) (ht : ∀ u : MGriess, u * t = t * u) :
    t = 1 := by
  obtain ⟨-, hS, g, h, hgh⟩ := MGriess_finite_nonabelian_simple
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center MGriess) with hb | ht'
  · exact Subgroup.mem_bot.1 (hb ▸ Subgroup.mem_center_iff.2 ht)
  · exact absurd (Subgroup.mem_center_iff.1
      (ht' ▸ Subgroup.mem_top h : h ∈ Subgroup.center MGriess) g) hgh

theorem nonempty_mulAut_equiv_MGriess (S : Type) [Group S] [Finite S]
    (hS : catalogIs S (sporIs .M)) : Nonempty (MulAut S ≃* MGriess) := by
  obtain ⟨i, hi, ⟨φ⟩⟩ := hS
  simp only [sporIs] at hi
  subst hi
  obtain ⟨e₀⟩ := CFSG.Blueprint.NativeSporadic.MonsterModel.iso_griess_y443Derived
  obtain ⟨e₁⟩ := CFSG.Blueprint.NativeSporadic.MonsterModel.iso_y443Derived_tauCeti
  have eS : S ≃* MGriess := φ.trans (e₀.trans e₁).symm
  have eM : S ≃* CFSG.Blueprint.NativeSporadic.M := φ.trans e₁.symm
  haveI : IsSimpleGroup MGriess := MGriess_finite_nonabelian_simple.2.1
  haveI : IsSimpleGroup S := eS.isSimpleGroup
  have hAut : ∀ α : MulAut S, ∃ g : S, α = MulAut.conj g := fun α =>
    let ⟨g, hg⟩ := CFSG.ComponentClassification.BMCase.catalogM_mulAut_mem_inner S
      inferInstance ⟨eM⟩ α
    ⟨g, hg.symm⟩
  exact @nonempty_mulAut_equiv_of_inner S MGriess _ inferInstance eS mGriess_central_eq_one hAut

end CFSG.LocalAnalysis.GLTheoremA.H301B

end
