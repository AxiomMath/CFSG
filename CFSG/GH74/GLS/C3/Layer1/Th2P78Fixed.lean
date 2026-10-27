module

public import CFSG.GH74.GLS.C3.Layer1.Th2P61A7
public import CFSG.GH74.GLS.Balance.SolvCompBasic
public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.GlueLib
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L102Quasi
public import CFSG.GH74.GLS.Stage1.Thm6.Prod.L145Back

public section

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Th2.Obs

namespace CFSG.GH74.GLS.Th2.Fixed

variable {G : Type} [Group G] [Finite G]

noncomputable def kBarFixedBy (J V : Subgroup G)
    (hVJ : V ≤ normalizer (J : Set G)) : Subgroup (kBar J) :=
  ⨅ v : ↥V, fixedSubgroup (kBar J) (barAct J ⟨v, hVJ v.2⟩)

omit [Finite G] in
theorem mem_fixedSubgroup_iff {L : Type*} [Group L] (φ : MulAut L) {x : L} :
    x ∈ fixedSubgroup L φ ↔ φ x = x := Iff.rfl

omit [Finite G] in
theorem mem_kBarFixedBy {J V : Subgroup G} (hVJ : V ≤ normalizer (J : Set G))
    {x : kBar J} :
    x ∈ kBarFixedBy J V hVJ ↔
      ∀ v : ↥V, barAct J ⟨v, hVJ v.2⟩ x = x := by
  classical
  rw [kBarFixedBy, Subgroup.mem_iInf]
  constructor
  · intro h v
    exact (mem_fixedSubgroup_iff _).1 (h v)
  · intro h v
    exact (mem_fixedSubgroup_iff _).2 (h v)

theorem map_kBarFixedBy_eq_centralizer
    {J B V : Subgroup G} (hBJ : B ≤ normalizer (J : Set G)) (hVB : V ≤ B)
    (Φ : kBar J ≃* alternatingGroup (Fin 7)) (θ : ↥B →* Equiv.Perm (Fin 7))
    (hrel : ∀ (b : ↥B) (x : kBar J),
      ((Φ (barAct J ⟨b, hBJ b.2⟩ x) : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) =
        θ b * ((Φ x : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) * (θ b)⁻¹) :
    (kBarFixedBy J V (hVB.trans hBJ)).map
        ((alternatingGroup (Fin 7)).subtype.comp Φ.toMonoidHom) =
      centralizer (Set.range (θ.comp (Subgroup.inclusion hVB))) ⊓ alternatingGroup (Fin 7) := by
  classical
  let θV : ↥V →* Equiv.Perm (Fin 7) := θ.comp (Subgroup.inclusion hVB)
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨?_, (Φ y).2⟩
    change ((Φ y : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) ∈
      Subgroup.centralizer (Set.range θV)
    rw [Subgroup.mem_centralizer_iff]
    rintro r ⟨v, rfl⟩
    have hyv := (mem_kBarFixedBy (hVB.trans hBJ)).1 hy v
    have hfix : ((Φ (barAct J ⟨v, hVB.trans hBJ v.2⟩ y) : alternatingGroup (Fin 7)) :
        Equiv.Perm (Fin 7)) = ((Φ y : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) := by
      simpa using congrArg (fun z => ((Φ z : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7))) hyv
    have hconj := hrel ⟨v, hVB v.2⟩ y
    rw [hfix] at hconj
    have hθv : (θV v : Equiv.Perm (Fin 7)) = θ ⟨v, hVB v.2⟩ := rfl
    have hconj' : ((Φ y : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) =
        (θV v : Equiv.Perm (Fin 7)) * ((Φ y : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) *
          (θV v : Equiv.Perm (Fin 7))⁻¹ := by
      rw [hθv]
      exact hconj
    have hcomm : (θV v : Equiv.Perm (Fin 7)) * ((Φ y : alternatingGroup (Fin 7)) :
        Equiv.Perm (Fin 7)) = ((Φ y : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) * θV v := by
      calc (θV v : Equiv.Perm (Fin 7)) * ((Φ y : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) =
          ((θV v : Equiv.Perm (Fin 7)) * ((Φ y : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) *
            (θV v : Equiv.Perm (Fin 7))⁻¹) * (θV v : Equiv.Perm (Fin 7)) := by group
        _ = ((Φ y : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) * θV v := by rw [← hconj']
    exact hcomm
  · rintro ⟨hxc, hxA⟩
    refine ⟨Φ.symm ⟨x, hxA⟩, ?_, by simp⟩
    change Φ.symm ⟨x, hxA⟩ ∈ kBarFixedBy J V (hVB.trans hBJ)
    rw [mem_kBarFixedBy (hVB.trans hBJ)]
    intro v
    apply Φ.injective
    apply Subtype.ext
    have hx : (θV v : Equiv.Perm (Fin 7)) * x = x * θV v :=
      Subgroup.mem_centralizer_iff.mp hxc (θV v) ⟨v, rfl⟩
    have hθv : (θV v : Equiv.Perm (Fin 7)) = θ ⟨v, hVB v.2⟩ := rfl
    have hconj := hrel ⟨v, hVB v.2⟩ (Φ.symm ⟨x, hxA⟩)
    have hΦ : ((Φ (Φ.symm ⟨x, hxA⟩) : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) = x := by
      simp
    rw [hΦ] at hconj
    calc
      ((Φ (barAct J ⟨v, hVB.trans hBJ v.2⟩ (Φ.symm ⟨x, hxA⟩)) :
          alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7))
          = (θV v : Equiv.Perm (Fin 7)) * x * (θV v : Equiv.Perm (Fin 7))⁻¹ := by
            rw [hθv]
            exact hconj
      _ = (x * θV v) * (θV v : Equiv.Perm (Fin 7))⁻¹ := by rw [hx]
      _ = x := by group
      _ = ((Φ (Φ.symm ⟨x, hxA⟩) : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) := by rw [hΦ]

theorem pPrimeCoreOf_centralizer_inter_alternating
    (s : Set (Equiv.Perm (Fin 7))) :
    pPrimeCoreOf 2 (Subgroup.centralizer s) =
      pPrimeCoreOf 2 (Subgroup.centralizer s ⊓ alternatingGroup (Fin 7)) := by
  classical
  let CS : Subgroup (Equiv.Perm (Fin 7)) := centralizer s
  let CA : Subgroup (Equiv.Perm (Fin 7)) := CS ⊓ alternatingGroup (Fin 7)
  have hCA_le : CA ≤ CS := inf_le_left
  have hnorm : (CA.subgroupOf CS).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hCA_le]
    intro h k hh hk
    refine ⟨?_, ?_⟩
    · exact CS.mul_mem (CS.mul_mem hk hh.1) (CS.inv_mem hk)
    · exact (inferInstance : (alternatingGroup (Fin 7)).Normal).conj_mem h hh.2 k
  have hle1 : pPrimeCoreOf 2 CA ≤ pPrimeCoreOf 2 CS :=
    CFSG.GH74.GLS.Stage2.Bender.Thm2.L102.pPrimeCoreOf_le_of_subnormalIn hCA_le
      hnorm.isSubnormal
  have hOS_le_CA : pPrimeCoreOf 2 CS ≤ CA := by
    refine le_inf (TwoThin.pPrimeCoreOf_le CS) ?_
    intro x hx
    exact mem_alternatingGroup_of_odd_orderOf
      (CFSG.GH74.GLS.Balance.SolvComp.odd_orderOf_of_mem_pPrimeCoreOf hx)
  have hnormOS : ∀ c ∈ CA, ∀ n ∈ pPrimeCoreOf 2 CS, c * n * c⁻¹ ∈ pPrimeCoreOf 2 CS :=
    fun c hc n hn => TwoThin.pPrimeCoreOf_normalized CS hc.1 hn
  have hle2 : pPrimeCoreOf 2 CS ≤ pPrimeCoreOf 2 CA :=
    CFSG.GH74.GLS.Stage1.Thm3.Sec4.le_pPrimeCoreOf' hOS_le_CA hnormOS
      (TwoThin.card_pPrimeCoreOf_odd CS)
  exact le_antisymm (by simpa [CS, CA] using hle2) (by simpa [CS, CA] using hle1)

theorem kBarFixedBy_oddCore_of_A7
    {J B V : Subgroup G} (hBJ : B ≤ normalizer (J : Set G)) (hVB : V ≤ B)
    (Φ : kBar J ≃* alternatingGroup (Fin 7)) (θ : ↥B →* Equiv.Perm (Fin 7))
    (hrel : ∀ (b : ↥B) (x : kBar J),
      ((Φ (barAct J ⟨b, hBJ b.2⟩ x) : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) =
        θ b * ((Φ x : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) * (θ b)⁻¹)
    {c' : Equiv.Perm (Fin 7)} (hc'A : c' ∈ alternatingGroup (Fin 7))
    (hc'core : c' ∈ pPrimeCoreOf 2
      (Subgroup.centralizer (Set.range (θ.comp (Subgroup.inclusion hVB)) :
        Set (Equiv.Perm (Fin 7)))))
    {c : kBar J}
    (hc : ((Φ c : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) = c') :
    c ∈ pPrimeCoreOf 2 (kBarFixedBy J V (hVB.trans hBJ)) := by
  classical
  let Cbar : Subgroup (kBar J) := kBarFixedBy J V (hVB.trans hBJ)
  let e : kBar J →* Equiv.Perm (Fin 7) :=
    (alternatingGroup (Fin 7)).subtype.comp Φ.toMonoidHom
  have he : Function.Injective e :=
    (Subgroup.subtype_injective _).comp Φ.injective
  have hmap : Cbar.map e =
      centralizer (Set.range (θ.comp (Subgroup.inclusion hVB))) ⊓ alternatingGroup (Fin 7) :=
    map_kBarFixedBy_eq_centralizer hBJ hVB Φ θ hrel
  have hcoreeq := pPrimeCoreOf_centralizer_inter_alternating
    (Set.range (θ.comp (Subgroup.inclusion hVB)) : Set (Equiv.Perm (Fin 7)))
  have hc'CA : c' ∈ pPrimeCoreOf 2
      (centralizer (Set.range (θ.comp (Subgroup.inclusion hVB))) ⊓ alternatingGroup (Fin 7)) := by
    rw [← hcoreeq]
    exact hc'core
  have hcoremap := CFSG.GH74.GLS.Stage1.Thm6.Prod.L145.pPrimeCoreOf_map e he Cbar
  rw [hmap] at hcoremap
  have hc'map : c' ∈ (pPrimeCoreOf 2 Cbar).map e := by
    rw [← hcoremap]
    exact hc'CA
  obtain ⟨y, hy, hyc⟩ := hc'map
  have hc_e : e c = c' := hc
  have hyc' : y = c := he (by rw [hyc, hc_e])
  rwa [hyc'] at hy

end CFSG.GH74.GLS.Th2.Fixed
