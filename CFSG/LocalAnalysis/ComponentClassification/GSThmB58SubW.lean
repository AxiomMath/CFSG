module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58SubDefs

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.LocalCores CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open scoped commutatorElement

namespace SubWAux

variable {G : Type*} [Group G]

theorem conjugate_le_of_mem {M H : Subgroup G} (hMH : M ≤ H) {g : G} (hg : g ∈ H) :
    conjugate M g ≤ H := fun x hx => by
  rw [UnbalancedLayer.mem_conjugate_iff] at hx
  have h := mul_mem (mul_mem (inv_mem hg) (hMH hx)) hg
  rwa [show g⁻¹ * (g * x * g⁻¹) * g = x by group] at h

theorem conjClosure_subgroupOf {H T Y : Subgroup G} (hT : T ≤ H) (hY : Y ≤ H) :
    conjClosure (T.subgroupOf H) (Y.subgroupOf H) = (conjClosure T Y).subgroupOf H := by
  apply le_antisymm
  · refine iSup₂_le fun g hg => ?_
    rw [conjugate_subgroupOf_eq]
    have h1 : conjugate T (g : G) ≤ conjClosure T Y :=
      le_iSup₂_of_le (f := fun g (_ : g ∈ Y) => conjugate T g) (g : G) (mem_subgroupOf.mp hg)
        le_rfl
    exact fun z hz => h1 (mem_subgroupOf.mp hz)
  · intro x hx
    have h1 : conjClosure T Y ≤
        (conjClosure (T.subgroupOf H) (Y.subgroupOf H)).map H.subtype := by
      refine iSup₂_le fun g hg => ?_
      have h2 : conjugate T g = (conjugate (T.subgroupOf H) ⟨g, hY hg⟩).map H.subtype := by
        rw [conjugate_subgroupOf_eq, map_subgroupOf_eq_of_le (conjugate_le_of_mem hT (hY hg))]
      rw [h2]
      exact map_mono (le_iSup₂_of_le (f := fun g (_ : g ∈ Y.subgroupOf H) =>
        conjugate (T.subgroupOf H) g) (⟨g, hY hg⟩ : ↥H) hg le_rfl)
    obtain ⟨c, hc, hcx⟩ := mem_map.mp (h1 (mem_subgroupOf.mp hx))
    rwa [show c = x from Subtype.ext hcx] at hc

theorem commutator_subgroupOf {H A C : Subgroup G} (hA : A ≤ H) (hC : C ≤ H) :
    ⁅A.subgroupOf H, C.subgroupOf H⁆ = ⁅A, C⁆.subgroupOf H := by
  apply map_injective H.subtype_injective
  rw [map_commutator, map_subgroupOf_eq_of_le ((commutator_mono hA hC).trans
    (commutator_le_self _)), map_subgroupOf_eq_of_le hA, map_subgroupOf_eq_of_le hC]

theorem zpowers_subgroupOf {H : Subgroup G} {g : G} (hg : g ∈ H) :
    zpowers (⟨g, hg⟩ : ↥H) = (zpowers g).subgroupOf H := by
  show zpowers (⟨g, hg⟩ : ↥H) = (zpowers (H.subtype ⟨g, hg⟩)).subgroupOf H
  rw [← MonoidHom.map_zpowers]
  exact (comap_map_eq_self_of_injective H.subtype_injective _).symm

end SubWAux

namespace Hyp52

variable {X : Type} [Group X] [Finite X] {h : Hyp52 X} {y : X}

private theorem layerIn_inf_secSubImg (hc : h.SecCond y) :
    layerIn (normalizer (h.secImage y h.B : Set (h.secBar y)) ⊓ h.secSubImg y) =
      h.secImage y h.V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Wp := normalizer (h.secImage y h.B : Set (h.secBar y)) ⊓ h.secSubImg y with hWp
  have hKs : ∀ {L : Subgroup X}, (L = h.K ∨ L = conjugate h.K h.a) →
      h.secImage y L ≤ Wp ∧ IsPComponent 2 ((h.secImage y L).subgroupOf Wp) := by
    intro L hL
    obtain ⟨hLW, hLc⟩ := isPComponent_secK hc hL
    have hLH : h.secImage y L ≤ h.secSubImg y := by
      rcases hL with rfl | rfl
      · exact secImage_K_le hc
      · exact secImage_mono (conjugate_K_le_secSub hc)
    rw [hWp]
    exact ⟨le_inf hLW hLH,
      CatalogueBPrimeJoin.pComponent_subgroupOf_of_le (le_inf hLW hLH) inf_le_left hLc⟩
  obtain ⟨hK1, hK1c⟩ := hKs (Or.inl rfl)
  obtain ⟨hK2, hK2c⟩ := hKs (Or.inr rfl)
  rw [secImage_conjugate h.K hc.a_mem_G0] at hK2 hK2c
  have hV' := secImage_V hc
  obtain ⟨-, -, hO1, hO2⟩ := B5a.pComponent_sup_facts hK1 hK2 hK1c hK2c
  apply le_antisymm
  · refine map_le_iff_le_comap.mpr (sSup_le fun M hM => ?_)
    rw [← map_le_iff_le_comap]
    set M₀ := M.map Wp.subtype with hM₀
    have hM₀W : M₀ ≤ Wp := map_subtype_le _
    have hM₀c : IsPComponent 2 (M₀.subgroupOf Wp) := by
      rw [show M₀.subgroupOf Wp = M from comap_map_eq_self_of_injective Wp.subtype_injective M]
      exact hM
    by_cases hM1 : M₀ = h.secImage y h.K
    · rw [hM1, hV']
      exact le_sup_left
    by_cases hM2 : M₀ = conjugate (h.secImage y h.K) hc.secA
    · rw [hM2, hV']
      exact le_sup_right
    exfalso
    have hMK : M₀ ≤ coreActionKernel (h.secImage y h.V) := by
      intro m hm
      rw [hV']
      exact B5a.mem_coreActionKernel_sup hO1 hO2
        (B5a.le_coreActionKernel_of_ne hK1 hM₀W hK1c hM₀c (Ne.symm hM1) hm)
        (B5a.le_coreActionKernel_of_ne hK2 hM₀W hK2c hM₀c (Ne.symm hM2) hm)
    have hpre : h.secPre y M₀ ≤ h.W ⊓ coreActionKernel h.V := by
      intro g hg
      have hgG := secPre_le_G0 M₀ hg
      have hg' := secMk_mem_of_mem_secPre hg
      have hgW : g ∈ h.W := by
        have h1 := hM₀W hg'
        rw [hWp] at h1
        have h2 := (mem_inf.mp h1).1
        rw [hc.normalizer_secB,
          secMk_mem_secImage_iff ((h.secB0_le_B y).trans le_normalizer)] at h2
        exact h2
      have : Group.IsPerfect h.V := isPerfect_V
      exact mem_inf.mpr ⟨hgW, mem_coreActionKernel_of_secMk (h.V_le_G0 y)
        (h.V_le_centralizer_secB0 y) hgG (OddQuot.le_normalizer_layerIn _ hgW) (hMK hg')⟩
    have : Group.IsSolvable ↥(h.W ⊓ coreActionKernel h.V) := isSolvable_kernel_V
    have : Group.IsSolvable ↥(h.secPre y M₀) :=
      Group.isSolvable_of_isSolvable_injective (inclusion_injective hpre)
    have : Group.IsSolvable ↥((h.secPre y M₀).subgroupOf (h.secG0 y)) :=
      Group.isSolvable_of_isSolvable_injective
        (f := (subgroupOfEquivOfLe (secPre_le_G0 M₀)).toMonoidHom)
        (subgroupOfEquivOfLe (secPre_le_G0 M₀)).injective
    have : Group.IsSolvable ↥(h.secImage y (h.secPre y M₀)) :=
      Group.isSolvable_of_surjective ((h.secMk y).subgroupMap_surjective _)
    have : Group.IsSolvable ↥M₀ := Group.isSolvable_of_isSolvable_injective
      (f := (MulEquiv.subgroupCongr (secImage_secPre M₀).symm).toMonoidHom)
      (MulEquiv.subgroupCongr (secImage_secPre M₀).symm).injective
    have : Group.IsPerfect M₀ := B5a.isPerfect_of_isPComponent_subgroupOf hM₀W hM₀c
    have : Nontrivial M₀ := B5a.nontrivial_of_isPComponent_subgroupOf hM₀W hM₀c
    exact Group.IsPerfect.not_isSolvable M₀ inferInstance
  · rw [hV']
    refine sup_le ?_ ?_
    · have h1 := map_mono (f := Wp.subtype)
        (show (h.secImage y h.K).subgroupOf Wp ≤ pLayer ↥Wp 2 from le_sSup hK1c)
      rwa [map_subgroupOf_eq_of_le hK1] at h1
    · have h1 := map_mono (f := Wp.subtype)
        (show (conjugate (h.secImage y h.K) hc.secA).subgroupOf Wp ≤ pLayer ↥Wp 2 from
          le_sSup hK2c)
      rwa [map_subgroupOf_eq_of_le hK2] at h1

theorem SecCond.layerIn_subW (hc : h.SecCond y) :
    layerIn (normalizer ((h.subB y : Subgroup ↥(h.secSubImg y)) : Set ↥(h.secSubImg y))) =
      (h.secImage y h.V).subgroupOf (h.secSubImg y) := by
  rw [normalizer_subB, ← inf_subgroupOf_right (normalizer (h.secImage y h.B : Set (h.secBar y)))
    (h.secSubImg y), B5a.layerIn_subgroupOf inf_le_right, layerIn_inf_secSubImg hc]

theorem SecCond.conjClosure_subW (hc : h.SecCond y) :
    conjClosure (GSLit.fixedLayer (h.subJ y) (h.subB y))
      (layerIn (normalizer ((h.subB y : Subgroup ↥(h.secSubImg y)) : Set ↥(h.secSubImg y)))) =
      layerIn (normalizer ((h.subB y : Subgroup ↥(h.secSubImg y)) : Set ↥(h.secSubImg y))) := by
  have hJBV : GSLit.fixedLayer h.J h.B ≤ h.V := B5a.fixedLayer_le_V h
  have hF : GSLit.fixedLayer (h.subJ y) (h.subB y) =
      (h.secImage y (GSLit.fixedLayer h.J h.B)).subgroupOf (h.secSubImg y) := by
    have h1 := B5a.fixedLayer_subgroupOf (h.secImage_secJ0_le y) (h.secImage_B_le y)
    rw [secFixedLayer_B hc] at h1
    exact h1
  have hC : conjClosure (h.secImage y (GSLit.fixedLayer h.J h.B)) (h.secImage y h.V) =
      h.secImage y h.V := by
    have h1 := conjClosure_secW hc
    rwa [layerIn_secW hc, secFixedLayer_B hc] at h1
  rw [hc.layerIn_subW, hF, SubWAux.conjClosure_subgroupOf
    ((secImage_mono hJBV).trans (secImage_V_le hc)) (secImage_V_le hc), hC]

theorem SecCond.commutator_subW (hc : h.SecCond y) :
    ⁅layerIn (normalizer ((h.subB y : Subgroup ↥(h.secSubImg y)) : Set ↥(h.secSubImg y))),
      zpowers hc.subA⁆ =
      layerIn (normalizer ((h.subB y : Subgroup ↥(h.secSubImg y)) : Set ↥(h.secSubImg y))) := by
  have hC : ⁅h.secImage y h.V, zpowers hc.secA⁆ = h.secImage y h.V := by
    have h1 := commutator_secW hc
    rwa [layerIn_secW hc] at h1
  rw [hc.layerIn_subW, SubWAux.zpowers_subgroupOf hc.secA_mem_secSubImg,
    SubWAux.commutator_subgroupOf (secImage_V_le hc) (zpowers_le.mpr hc.secA_mem_secSubImg), hC]

theorem SecCond.subB_le_kernel (hc : h.SecCond y) :
    h.subB y ≤ normalizer ((h.subB y : Subgroup ↥(h.secSubImg y)) : Set ↥(h.secSubImg y)) ⊓
      coreActionKernel (layerIn (normalizer ((h.subB y : Subgroup ↥(h.secSubImg y)) :
        Set ↥(h.secSubImg y)))) := by
  have h1 := secB_le_kernel hc
  rw [layerIn_secW hc] at h1
  rw [hc.layerIn_subW, B5a.coreActionKernel_subgroupOf (secImage_V_le hc)]
  exact le_inf le_normalizer fun b hb => (mem_inf.mp (h1 hb)).2

theorem SecCond.subB_sylow_kernel (hc : h.SecCond y) :
    ∃ R : Sylow 2 ↥(normalizer ((h.subB y : Subgroup ↥(h.secSubImg y)) : Set ↥(h.secSubImg y)) ⊓
      coreActionKernel (layerIn (normalizer ((h.subB y : Subgroup ↥(h.secSubImg y)) :
        Set ↥(h.secSubImg y))))),
      (R : Subgroup _) = (h.subB y).subgroupOf
        (normalizer ((h.subB y : Subgroup ↥(h.secSubImg y)) : Set ↥(h.secSubImg y)) ⊓
          coreActionKernel (layerIn (normalizer ((h.subB y : Subgroup ↥(h.secSubImg y)) :
            Set ↥(h.secSubImg y))))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := normalizer ((h.subB y : Subgroup ↥(h.secSubImg y)) : Set ↥(h.secSubImg y)) ⊓
    coreActionKernel (layerIn (normalizer ((h.subB y : Subgroup ↥(h.secSubImg y)) :
      Set ↥(h.secSubImg y)))) with hN
  set C' := normalizer (h.secImage y h.B : Set (h.secBar y)) ⊓
    coreActionKernel (h.secImage y h.V) with hC'
  have hNC : N = (C' ⊓ h.secSubImg y).subgroupOf (h.secSubImg y) := by
    rw [hN, hc.layerIn_subW, B5a.coreActionKernel_subgroupOf (secImage_V_le hc), normalizer_subB,
      inf_subgroupOf_right, hC']
    exact (comap_inf _ _ _).symm
  have hBC' : h.secImage y h.B ≤ C' := by
    have h1 := secB_le_kernel hc
    rwa [layerIn_secW hc] at h1
  obtain ⟨R, hR⟩ := secB_sylow_kernel hc
  have hodd : ¬ 2 ∣ (h.secImage y h.B).relIndex C' := by
    have h2 := R.not_dvd_index
    rw [hR, layerIn_secW hc] at h2
    exact h2
  have hrel := relIndex_mul_relIndex (h.secImage y h.B) (C' ⊓ h.secSubImg y) C'
    (le_inf hBC' (h.secImage_B_le y)) inf_le_left
  have hodd' : ¬ 2 ∣ (h.secImage y h.B).relIndex (C' ⊓ h.secSubImg y) :=
    fun h2 => hodd (hrel ▸ dvd_mul_of_dvd_left h2 _)
  have hidx : ¬ 2 ∣ ((h.subB y).subgroupOf N).index := by
    have e1 : (h.subB y).relIndex N =
        (h.secImage y h.B).relIndex (C' ⊓ h.secSubImg y) := by
      rw [hNC]
      exact relIndex_subgroupOf inf_le_right
    show ¬ 2 ∣ (h.subB y).relIndex N
    rw [e1]
    exact hodd'
  have hB2 : IsPGroup 2 (h.secImage y h.B) :=
    ((B5a.isPGroup_B h).comap_subtype (K := h.secG0 y)).map (h.secMk y)
  have hB2' : IsPGroup 2 (h.subB y) := hB2.comap_subtype
  have hp : IsPGroup 2 ((h.subB y).subgroupOf N) := hB2'.comap_subtype
  exact ⟨hp.toSylow hidx, IsPGroup.toSylow_coe hp hidx⟩

theorem SecCond.isPComponent_subK (hc : h.SecCond y) :
    h.subK y ≤ normalizer ((h.subB y : Subgroup ↥(h.secSubImg y)) : Set ↥(h.secSubImg y)) ∧
      IsPComponent 2 ((h.subK y).subgroupOf
        (normalizer ((h.subB y : Subgroup ↥(h.secSubImg y)) : Set ↥(h.secSubImg y)))) :=
  hc.isPComponent_subL (Or.inl rfl)

theorem SecCond.layer_eq_subK (hc : h.SecCond y) :
    h.subK y ⊔ conjugate (h.subK y) hc.subA =
      layerIn (normalizer ((h.subB y : Subgroup ↥(h.secSubImg y)) : Set ↥(h.secSubImg y))) := by
  have hK := secImage_K_le hc
  have hKa : conjugate (h.secImage y h.K) hc.secA ≤ h.secSubImg y :=
    SubWAux.conjugate_le_of_mem hK hc.secA_mem_secSubImg
  have e : conjugate (h.subK y) hc.subA =
      (conjugate (h.secImage y h.K) hc.secA).subgroupOf (h.secSubImg y) :=
    conjugate_subgroupOf_eq _ _ _
  rw [e, hc.layerIn_subW, secImage_V hc, subgroupOf_sup hK hKa]

theorem SecCond.type_subK (hc : h.SecCond y) :
    GSRestricted (↥(h.subK y) ⧸ Open.fusionZStar ↥(h.subK y)) ∨
      (conjugate (h.subK y) hc.subA ≠ h.subK y ∧
        Nonempty (↥(h.subK y) ⧸ Open.fusionZStar ↥(h.subK y) ≃*
          ↥(h.subJ y) ⧸ Open.fusionZStar ↥(h.subJ y))) := by
  have hK := secImage_K_le hc
  obtain ⟨eK⟩ := TwoQuot.nonempty_fusionZStar_equiv_of_pPrimeCore_equiv
    (UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2 (subgroupOfEquivOfLe hK))
  obtain ⟨eJ⟩ := TwoQuot.nonempty_fusionZStar_equiv_of_pPrimeCore_equiv
    (UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2
      (subgroupOfEquivOfLe (h.secImage_secJ0_le y)))
  rcases type_secK hc with hR | ⟨hne, ⟨e⟩⟩
  · exact Or.inl (OddQuot.gsRestricted_of_mulEquiv eK.symm hR)
  · refine Or.inr ⟨fun heq => hne ?_, ⟨eK.trans (e.trans eJ.symm)⟩⟩
    have hKa : conjugate (h.secImage y h.K) hc.secA ≤ h.secSubImg y :=
      SubWAux.conjugate_le_of_mem hK hc.secA_mem_secSubImg
    have e1 : conjugate (h.subK y) hc.subA =
        (conjugate (h.secImage y h.K) hc.secA).subgroupOf (h.secSubImg y) :=
      conjugate_subgroupOf_eq _ _ _
    rw [e1, subgroupOf_inj, inf_of_le_left hKa, inf_of_le_left hK] at heq
    exact heq

end Hyp52

end CFSG.ComponentClassification.GSThmB
