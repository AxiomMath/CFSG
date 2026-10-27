module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma44a
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitCompTools
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma46a

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup

variable {X : Type} [Group X] [Finite X]

namespace Cor441

theorem nontrivial_of_isTwoQuasisimple {K : Type*} [Group K] (hK : IsTwoQuasisimple K) :
    Nontrivial K := by
  have h := LocalCores.isQuasisimple_nontrivial hK.2
  by_contra hK'
  rw [not_nontrivial_iff_subsingleton] at hK'
  have : Subsingleton (K ⧸ pPrimeCore 2 K) := by
    refine ⟨fun a b => ?_⟩
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    rw [Subsingleton.elim a b]
  exact not_nontrivial _ h

omit [Finite X] in
theorem map_map_conj_subgroupOf {C : Subgroup X} {J : Subgroup X} (hJ : J ≤ C) (c : ↥C) :
    ((J.subgroupOf C).map (MulAut.conj c).toMonoidHom).map C.subtype =
      J.map (MulAut.conj (c : X)).toMonoidHom := by
  rw [map_map]
  have hcomp : C.subtype.comp (MulAut.conj c).toMonoidHom =
      (MulAut.conj (c : X)).toMonoidHom.comp C.subtype := by
    ext y
    simp [MulAut.conj_apply]
  rw [hcomp, ← map_map, subgroupOf_map_subtype, inf_eq_left.mpr hJ]

end Cor441

theorem map_conj_eq_of_isTwoComponentIn (h219 : Harris82Lemma219Input) {t z : X}
    (ht : orderOf t = 2) (htz : t ∈ centralizer ({z} : Set X))
    (hC : IsPGroup 2 (↥(centralizer ({t} : Set X) ⊓ centralizer {z}) ⧸
      pPrimeCore 2 ↥(centralizer ({t} : Set X) ⊓ centralizer {z})))
    {J : Subgroup X} (hJ : IsTwoComponentIn J (centralizer {z})) :
    J.map (MulAut.conj t).toMonoidHom = J := by
  set C := centralizer ({z} : Set X)
  set t' : ↥C := ⟨t, htz⟩
  have ht' : orderOf t' = 2 := by rw [Subgroup.orderOf_mk]; exact ht
  set J' := J.subgroupOf C
  have hJ'2 : IsTwoComponent J' :=
    ⟨hJ.2.1, isTwoQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hJ.1).symm hJ.2.2⟩
  by_contra hne
  have hne' : J'.map (MulAut.conj t').toMonoidHom ≠ J' := by
    intro heq
    apply hne
    rw [← Cor441.map_map_conj_subgroupOf hJ.1 t', heq, subgroupOf_map_subtype,
      inf_eq_left.mpr hJ.1]
  obtain ⟨hcomp, -, -⟩ := ((h219 ↥C t' ht').1 J' hJ'2).2 hne'
  set R := centralizerResidual (J' ⊔ J'.map (MulAut.conj t').toMonoidHom) t'
  have e : ↥(centralizer ({t'} : Set ↥C)) ≃* ↥(centralizer ({t} : Set X) ⊓ centralizer {z}) :=
    (equivMapOfInjective _ C.subtype C.subtype_injective).trans
      (MulEquiv.subgroupCongr (map_subtype_centralizer htz))
  have hC' := isPGroup_quot_of_mulEquiv e.symm hC
  have : Group.IsPerfect ↥R := hcomp.2.2.1
  have hperf : Group.IsPerfect ↥(R.subgroupOf (centralizer ({t'} : Set ↥C))) :=
    Group.IsPerfect.ofSurjective (f := ((subgroupOfEquivOfLe hcomp.1).symm : ↥R →*
      ↥(R.subgroupOf (centralizer ({t'} : Set ↥C)))))
      (subgroupOfEquivOfLe hcomp.1).symm.surjective
  have hbot := eq_bot_of_isPerfect_of_isPGroup_quotient hC' hperf
  have hR : R = ⊥ := by
    have hRC : R ≤ centralizer ({t'} : Set ↥C) := hcomp.1
    refine eq_bot_iff.mpr fun x hx => ?_
    have hx' : (⟨x, hRC hx⟩ : ↥(centralizer ({t'} : Set ↥C))) ∈
        R.subgroupOf (centralizer ({t'} : Set ↥C)) := hx
    have hx'' : (⟨x, hRC hx⟩ : ↥(centralizer ({t'} : Set ↥C))) ∈ (⊥ : Subgroup _) :=
      hbot ▸ hx'
    exact mem_bot.mpr (congrArg Subtype.val (mem_bot.mp hx''))
  have := Cor441.nontrivial_of_isTwoQuasisimple hcomp.2.2
  rw [hR] at this
  exact (not_nontrivial_iff_subsingleton.mpr inferInstance) this

theorem isPGroup_quot_inf_centralizer {t z : X}
    (hC : IsPGroup 2 (↥(centralizer ({t} : Set X) ⊓ centralizer {z}) ⧸
      pPrimeCore 2 ↥(centralizer ({t} : Set X) ⊓ centralizer {z})))
    {J : Subgroup X} (hJ : J ≤ centralizer ({z} : Set X)) :
    IsPGroup 2 (↥(J ⊓ centralizer {t}) ⧸ pPrimeCore 2 ↥(J ⊓ centralizer {t})) :=
  isPGroup_quot_of_le (le_inf inf_le_right (inf_le_left.trans hJ)) hC

end CFSG.ComponentClassification.HarrisLit
