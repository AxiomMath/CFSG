module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107F3S
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107F3SCover2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107F3SF4Datum
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTwE6SplitEmbed
public import Certificates.Certificate89026

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.AGLEmbedding CFSG.AGLEmbedding.R3 CFSG.Assembly

theorem i1066CoverAt_twE6
    : I1066CoverAt ⟨.twE6, 0, 1⟩ := by
  intro K _ _ _ hraw
  have hraw' : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = (2 ^ 1) ^ 2 ∧
      Nonempty (K ⧸ Subgroup.center K ≃* CFSG.StandardType.TwE6Delta.RecipeR F 1) := hraw
  obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := hraw'
  obtain ⟨k, _, _, _, ι, -, hι⟩ :=
    CFSG.StandardType.exists_injective_f4_recipeR (K := F) le_rfl hcard
  let D : ModuleSpec (CFSG.StandardType.TwE6Delta.RecipeR F 1) 2 := (F4Sym.f4Spec0 k).map ι hι
  let π : K →* CFSG.StandardType.TwE6Delta.RecipeR F 1 :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = Subgroup.center K := by
    ext x
    simp only [π, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hcert := (Certificates.certificate89026 : F4Sym.f4Check () = true)
  simp only [F4Sym.f4Check, Bool.and_eq_true] at hcert
  obtain ⟨hfun, halt⟩ := hcert
  have hA : D.NoAlt := fun B hB hinv => noAlt_of_altOK halt B hB hinv
  have hFun : D.NoFun := fun v hv => noFun_of_funOK hfun v hv
  have h := add_pRank_center_le_of_moduleSpec_two π hπ hker D hA hFun
  have h10 : D.n = 10 := rfl
  have h9 : twoRankLow107 ⟨.twE6, 0, 1⟩ = 9 := rfl
  omega

end CFSG.LocalAnalysis.GLTheoremA
