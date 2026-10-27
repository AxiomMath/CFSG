module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107F3S
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107F3SCover2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107F3SU6Datum
public import Certificates.Certificate89025

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.AGLEmbedding CFSG.AGLEmbedding.R3 CFSG.Assembly

theorem i1066CoverAt_U6 : I1066CoverAt ⟨.twA, 5, 1⟩ := by
  intro K _ _ _ hraw
  have hraw' : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = (2 ^ 1) ^ 2 ∧
      Nonempty (K ⧸ Subgroup.center K ≃* LargeEvenProj (LargeEvenSUGroup (Fin (5 + 1)) F (2 ^ 1)))
      := hraw
  obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := hraw'
  have hF : Nat.card F = 4 := by rw [hcard]; norm_num
  let π : K →* LargeEvenProj (LargeEvenSUGroup (Fin 6) F 2) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  have hπ : Function.Surjective π :=
    e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = Subgroup.center K := by
    ext x
    simp only [π, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hcert := (Certificates.certificate89025 : U6Herm.u6Check () = true)
  simp only [U6Herm.u6Check, Bool.and_eq_true] at hcert
  obtain ⟨hfun, halt⟩ := hcert
  have hA : (U6Herm.u6Spec F hF).NoAlt := fun B hB hinv => noAlt_of_altOK halt B hB hinv
  have hFun : (U6Herm.u6Spec F hF).NoFun := fun v hv => noFun_of_funOK hfun v hv
  have h := add_pRank_center_le_of_moduleSpec_two π hπ hker (U6Herm.u6Spec F hF) hA hFun
  exact h

end CFSG.LocalAnalysis.GLTheoremA
