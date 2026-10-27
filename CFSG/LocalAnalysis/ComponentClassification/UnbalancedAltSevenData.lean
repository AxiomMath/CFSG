module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedAltSevenAlternating
public import CFSG.Sporadic.Schreier.LyDoubleCover

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedAltSeven

open Equiv Subgroup CFSG.Sporadic.Ly CFSG.Sporadic.LySchreier

@[expose] def lyPi : lyC →* alternatingGroup (Fin 11) :=
  lyCoverEquiv.toMonoidHom.comp (QuotientGroup.mk' zGroup)

theorem lyPi_apply (g : lyC) : lyPi g = lyCoverEquiv (g : lyC ⧸ zGroup) := rfl

theorem coe_lyPi (g : lyC) : (lyPi g : Perm (Fin 11)) = imgC g := rfl

theorem lyPi_surjective : Function.Surjective lyPi :=
  lyCoverEquiv.surjective.comp (QuotientGroup.mk'_surjective zGroup)

theorem lyPi_ker : lyPi.ker = zGroup := by
  ext g
  rw [MonoidHom.mem_ker, lyPi_apply, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]

theorem lyPi_zC : lyPi zC = 1 := (MonoidHom.mem_ker).1 (lyPi_ker ▸ mem_zpowers zC)

theorem lyCoverEquiv_unique (e : lyC ⧸ zGroup ≃* alternatingGroup (Fin 11))
    (he : ∀ j < 12, ∀ x : Fin 11,
      (e (QuotientGroup.mk ⟨cStar j, cStar_mem j⟩) : Perm (Fin 11)) x = pStar j x) :
    e = lyCoverEquiv := by
  have hhom : e.toMonoidHom.comp (QuotientGroup.mk' zGroup) =
      lyCoverEquiv.toMonoidHom.comp (QuotientGroup.mk' zGroup) := by
    apply MonoidHom.eq_of_eqOn_dense closure_cC
    rintro _ ⟨i, rfl⟩
    have hc : cC i = ⟨cStar i, cStar_mem i⟩ := Subtype.ext (cSeed_eq_cStar i).symm
    apply Subtype.ext
    ext x
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      QuotientGroup.mk'_apply]
    rw [lyCoverEquiv_cC i, hc, he i (by omega) x]
    rw [pGen, pPerm_apply (by omega)]
  ext q x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  have := DFunLike.congr_fun hhom g
  simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
    QuotientGroup.mk'_apply] at this
  rw [this]

@[expose] def altSevenE : Subgroup lyC := stabFour.comap lyPi

theorem mem_altSevenE {g : lyC} :
    g ∈ altSevenE ↔ ∀ i : Fin 11, i.val < 4 → (lyPi g : Perm (Fin 11)) i = i := Iff.rfl

theorem zC_mem_altSevenE : zC ∈ altSevenE := by
  change lyPi zC ∈ stabFour
  rw [lyPi_zC]
  exact one_mem _

@[expose] def altSevenZ : altSevenE := ⟨zC, zC_mem_altSevenE⟩

@[expose] def altSevenPi : altSevenE →* alternatingGroup (Fin 7) :=
  relabel.toMonoidHom.comp (lyPi.subgroupComap stabFour)

theorem altSevenPi_apply (g : altSevenE) :
    altSevenPi g = relabel ⟨lyPi g, g.2⟩ := rfl

theorem altSevenPi_apply_val (g : altSevenE) (i : Fin 7) :
    ((altSevenPi g : Perm (Fin 7)) i).val =
      ((lyPi g : Perm (Fin 11)) ⟨i.val + 4, by omega⟩).val - 4 :=
  relabel_apply ⟨lyPi g, g.2⟩ i

theorem alternating_seven_cover_data :
    (∀ j < 12, ∀ x : Fin 11,
      (lyCoverEquiv (QuotientGroup.mk ⟨cStar j, cStar_mem j⟩) : Perm (Fin 11)) x = pStar j x) ∧
    (∀ e : lyC ⧸ zGroup ≃* alternatingGroup (Fin 11), (∀ j < 12, ∀ x : Fin 11,
      (e (QuotientGroup.mk ⟨cStar j, cStar_mem j⟩) : Perm (Fin 11)) x = pStar j x) →
        e = lyCoverEquiv) ∧
    (∀ g : lyC, lyPi g = lyCoverEquiv (g : lyC ⧸ zGroup)) ∧
    (∀ g : lyC, g ∈ altSevenE ↔ ∀ i : Fin 11, i.val < 4 → (lyPi g : Perm (Fin 11)) i = i) ∧
    ((altSevenZ : lyC) : J) = lyz ∧
    ∀ (g : altSevenE) (i : Fin 7), ((altSevenPi g : Perm (Fin 7)) i).val =
      ((lyPi g : Perm (Fin 11)) ⟨i.val + 4, by omega⟩).val - 4 := by
  refine ⟨fun j hj x => ?_, lyCoverEquiv_unique, lyPi_apply, fun _ => Iff.rfl, rfl,
    altSevenPi_apply_val⟩
  have := imgC_cStar hj
  rw [imgC_apply] at this
  rw [this, pPerm_apply hj]

end CFSG.ComponentClassification.UnbalancedAltSeven
