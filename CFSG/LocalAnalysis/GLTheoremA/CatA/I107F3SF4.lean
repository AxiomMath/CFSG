module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107F3S
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107F3SCover2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107F3SF4Datum
public import Certificates.Certificate89026

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.AGLEmbedding CFSG.AGLEmbedding.R3 CFSG.Assembly

theorem i1066CoverAt_F4
    : I1066CoverAt ⟨.F4, 0, 1⟩ := by
  intro K _ _ _ hraw
  have hraw' : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ 1 ∧
      Nonempty (K ⧸ Subgroup.center K ≃*
        LargeEvenCenterQuot (LargeEvenChevH LargeEvenCartanF4 F false)) := hraw
  obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := hraw'
  have hF : Nat.card F = 2 := by rw [hcard]; norm_num
  let π : K →* LargeEvenCenterQuot (LargeEvenChevH LargeEvenCartanF4 F false) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = Subgroup.center K := by
    ext x
    simp only [π, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hcert := (Certificates.certificate89026 : F4Sym.f4Check () = true)
  simp only [F4Sym.f4Check, Bool.and_eq_true] at hcert
  obtain ⟨hfun, halt⟩ := hcert
  have hA : (F4Sym.f4Spec F hF).NoAlt := fun B hB hinv => noAlt_of_altOK halt B hB hinv
  have hFun : (F4Sym.f4Spec F hF).NoFun := fun v hv => noFun_of_funOK hfun v hv
  have h := add_pRank_center_le_of_moduleSpec_two π hπ hker (F4Sym.f4Spec F hF) hA hFun
  have h10 : (F4Sym.f4Spec F hF).n = 10 := rfl
  have h7 : twoRankLow107 ⟨.F4, 0, 1⟩ = 7 := rfl
  omega

end CFSG.LocalAnalysis.GLTheoremA
