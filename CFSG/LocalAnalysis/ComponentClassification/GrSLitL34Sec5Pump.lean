module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Std

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem le_layerIn_of_commute (hS : SchreierFor Blueprint.Catalog)
    (hK : Assembly.KProper Blueprint.Catalog G) {J : Subgroup G} {b t : G} (hb : orderOf b = 2)
    (ht : orderOf t = 2) (hbt : b * t = t * b) (htZ : t ∉ center G)
    (hJb : J ≤ centralizer ({b} : Set G))
    (hJp : IsPComponent 2 (J.subgroupOf (centralizer ({b} : Set G))))
    (hJt : J ≤ centralizer ({t} : Set G)) : J ≤ layerIn (centralizer ({t} : Set G)) := by
  have hgs := gsFixedLayer_eq_of_le hJb hJp hJt
  have hJbb : conjugate J b = J := UnbalancedCorr.conjugate_eq_self_of_le_centralizer hJb
  have hKe : ∀ k ∈ J ⊔ conjugate J b, k⁻¹ * t⁻¹ * k * t ∈
      (pPrimeCore 2 (centralizer ({b} : Set G))).map (centralizer ({b} : Set G)).subtype := by
    rw [hJbb, sup_idem]
    intro k hk
    have hkt : k * t = t * k := mem_centralizer_singleton_iff.mp (hJt hk)
    rw [show k⁻¹ * t⁻¹ * k * t = k⁻¹ * t⁻¹ * (k * t) by group, hkt,
      show k⁻¹ * t⁻¹ * (t * k) = 1 by group]
    exact one_mem _
  obtain ⟨-, -, -, -, -, -, hTV, hVE, -, -, -, -⟩ :=
    UGSChain.kProper_core_trivial_orbit_fixed_layer_containment_of_schreier hS hK (a := b)
      (b := b) (e := t) hb ht rfl hbt htZ hJb hJp hKe
  rw [← hgs]
  exact hTV.trans hVE

omit [Finite G] in
theorem mem_normalizer_pumpUp {J : Subgroup G} {t g : G}
    (hg : g ∈ layerIn (centralizer ({t} : Set G))) : g ∈ normalizer (pumpUp J t : Set G) :=
  UnbalancedCorr.mem_normalizer_iSup_conjugate_of_mem (E := layerIn (centralizer ({t} : Set G)))
    (T := gsFixedLayer J t) hg

omit [Finite G] in
theorem pumpUp_le_layerIn {J : Subgroup G} {t : G} (hgs : gsFixedLayer J t = J)
    (hJL : J ≤ layerIn (centralizer ({t} : Set G))) :
    pumpUp J t ≤ layerIn (centralizer ({t} : Set G)) :=
  iSup₂_le fun g hg => by
    rw [hgs]
    exact UnbalancedCorr.conjugate_le_of_mem hJL hg

omit [Finite G] in
theorem le_pumpUp {J : Subgroup G} {t : G} (hgs : gsFixedLayer J t = J) : J ≤ pumpUp J t := by
  refine le_iSup₂_of_le 1 (one_mem _) ?_
  rw [hgs]
  intro x hx
  exact ⟨x, hx, by simp⟩

theorem sup_oddIn_pumpUp {J : Subgroup G} {t : G} (hJt : J ≤ centralizer ({t} : Set G))
    (hgs : gsFixedLayer J t = J)
    (hT91 : (⨆ (g : G) (_ : conjugate J g ≤ centralizer ({t} : Set G)), conjugate J g) ≤
      oddIn (centralizer ({t} : Set G)) ⊔ J) :
    J ⊔ oddIn (pumpUp J t) = pumpUp J t := by
  set C := centralizer ({t} : Set G) with hC
  set P := pumpUp J t with hP
  have hPC : P ≤ C := pumpUp_le_centralizer J t
  have hJP : J ≤ P := le_pumpUp hgs
  have hPO : P ≤ oddIn C ⊔ J := by
    refine iSup₂_le fun g hg => ?_
    rw [hgs]
    have hgC : g ∈ C := map_subtype_le _ hg
    have hJg : conjugate J g ≤ C := by
      rintro _ ⟨l, hl, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      exact mul_mem (mul_mem (inv_mem hgC) (hJt hl)) hgC
    exact (le_iSup₂_of_le g hJg le_rfl).trans hT91
  have hJN : J ≤ normalizer (oddIn C : Set G) := fun x hx =>
    normalizer_le_normalizer_oddIn C (le_normalizer (hJt hx))
  refine le_antisymm (sup_le hJP (map_subtype_le _)) fun p hp => ?_
  have hp' : p ∈ (oddIn C : Set G) * (J : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left (oddIn C) J hJN]
    exact hPO hp
  obtain ⟨o, ho, j, hj, rfl⟩ := hp'
  have hoP : o ∈ P := by
    have := mul_mem hp (inv_mem (hJP hj))
    rwa [mul_inv_cancel_right] at this
  have hoO : o ∈ oddIn P := inf_oddIn_le_oddIn hPC (mem_inf.mpr ⟨ho, hoP⟩)
  show o * j ∈ J ⊔ oddIn P
  rw [show o * j = j * (j⁻¹ * o * j) by group]
  refine mul_mem (mem_sup_left hj) (mem_sup_right ?_)
  have hjN : j⁻¹ ∈ normalizer (oddIn P : Set G) :=
    normalizer_le_normalizer_oddIn P (le_normalizer (inv_mem (hJP hj)))
  simpa using (mem_normalizer_iff.mp hjN o).mp hoO

omit [Finite G] in
theorem primeResidual_pumpUp {J : Subgroup G} {t : G} (hgs : gsFixedLayer J t = J)
    (hJ : CatalogueBPrimeJoin.primeResidual 2 ↥J = ⊤) :
    CatalogueBPrimeJoin.primeResidual 2 ↥(pumpUp J t) = ⊤ := by
  set P := pumpUp J t with hP
  suffices h : P ≤ (CatalogueBPrimeJoin.primeResidual 2 ↥P).map P.subtype by
    rw [eq_top_iff]
    intro x _
    obtain ⟨y, hy, hyx⟩ := h x.2
    rwa [← Subtype.ext hyx]
  refine iSup₂_le fun g hg => ?_
  rw [hgs]
  have hJgP : conjugate J g ≤ P := by
    have h2 : conjugate (gsFixedLayer J t) g ≤ pumpUp J t := le_iSup₂_of_le g hg le_rfl
    rwa [hgs] at h2
  let e : ↥J ≃* ↥(conjugate J g) :=
    J.equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective
  have hJg := CatalogueBPrimeJoin.primeResidual_eq_top_of_equiv 2 e hJ
  have hle := CatalogueBPrimeJoin.primeResidual_map_le 2 (inclusion hJgP)
  intro y hy
  have hy' : (⟨y, hy⟩ : ↥(conjugate J g)) ∈
      CatalogueBPrimeJoin.primeResidual 2 ↥(conjugate J g) := by
    rw [hJg]
    exact mem_top _
  exact ⟨inclusion hJgP ⟨y, hy⟩, hle ⟨_, hy', rfl⟩, rfl⟩

theorem isPComponent_pumpUp (hS : SchreierFor Blueprint.Catalog)
    (hK : Assembly.KProper Blueprint.Catalog G) {J : Subgroup G} {b t : G} (hb : orderOf b = 2)
    (ht : orderOf t = 2) (hbt : b * t = t * b) (htZ : t ∉ center G)
    (hJb : J ≤ centralizer ({b} : Set G))
    (hJp : IsPComponent 2 (J.subgroupOf (centralizer ({b} : Set G))))
    (hJt : J ≤ centralizer ({t} : Set G))
    (hT91 : (⨆ (g : G) (_ : conjugate J g ≤ centralizer ({t} : Set G)), conjugate J g) ≤
      oddIn (centralizer ({t} : Set G)) ⊔ J) :
    IsPComponent 2 ((pumpUp J t).subgroupOf (centralizer ({t} : Set G))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer ({t} : Set G) with hC
  set P := pumpUp J t with hP
  have hgs := gsFixedLayer_eq_of_le hJb hJp hJt
  have hPL : P ≤ layerIn C :=
    pumpUp_le_layerIn hgs (le_layerIn_of_commute hS hK hb ht hbt htZ hJb hJp hJt)
  have hPC : P ≤ C := pumpUp_le_centralizer J t
  obtain ⟨-, hres, hq⟩ := (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 J _ hJb).mp hJp
  have hLs : ((layerIn C).subgroupOf C).IsSubnormal := by
    have : (pLayer ↥C 2).Characteristic := CatalogueBPrimeJoin.pLayer_characteristic
    have hP' : (layerIn C).subgroupOf C = pLayer ↥C 2 :=
      comap_map_eq_self_of_injective C.subtype_injective _
    rw [hP']
    exact Subgroup.Normal.isSubnormal inferInstance
  have hPn : ((P.subgroupOf C).subgroupOf ((layerIn C).subgroupOf C)).Normal := by
    constructor
    intro x hx g
    rw [mem_subgroupOf, mem_subgroupOf] at hx ⊢
    have hgP : ((g : C) : G) ∈ layerIn C := mem_subgroupOf.mp g.2
    have := (mem_normalizer_iff.mp (mem_normalizer_pumpUp hgP) _).mp hx
    simpa using this
  have hsub : (P.subgroupOf C).IsSubnormal :=
    Subgroup.IsSubnormal.trans (fun x hx => hPL hx) hPn.isSubnormal hLs
  have hsup := sup_oddIn_pumpUp hJt hgs hT91
  obtain ⟨-, e, -⟩ := restriction_quotient_mulEquiv (le_pumpUp hgs) hsup
  exact (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 P C hPC).mpr
    ⟨hsub, primeResidual_pumpUp hgs hres, LocalCores.isQuasisimple_of_mulEquiv e hq⟩

theorem gsCorr_pumpUp (hS : SchreierFor Blueprint.Catalog)
    (hK : Assembly.KProper Blueprint.Catalog G) {J : Subgroup G} {b t : G} (hb : orderOf b = 2)
    (ht : orderOf t = 2) (hbt : b * t = t * b) (htZ : t ∉ center G)
    (hJb : J ≤ centralizer ({b} : Set G))
    (hJp : IsPComponent 2 (J.subgroupOf (centralizer ({b} : Set G))))
    (hJt : J ≤ centralizer ({t} : Set G))
    (hT91 : (⨆ (g : G) (_ : conjugate J g ≤ centralizer ({t} : Set G)), conjugate J g) ≤
      oddIn (centralizer ({t} : Set G)) ⊔ J) :
    GSCorr b J t (pumpUp J t) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := pumpUp J t with hP
  have hgs := gsFixedLayer_eq_of_le hJb hJp hJt
  have hPp := isPComponent_pumpUp hS hK hb ht hbt htZ hJb hJp hJt hT91
  have hJP : J ≤ P := le_pumpUp hgs
  obtain ⟨-, e, -⟩ := restriction_quotient_mulEquiv hJP (sup_oddIn_pumpUp hJt hgs hT91)
  have hidx : (pPrimeCore 2 ↥J).index = (pPrimeCore 2 ↥P).index := by
    rw [index_eq_card, index_eq_card]
    exact Nat.card_congr e.toEquiv
  have hTK : J ≤ (P ⊔ conjugate P b) ⊓ centralizer ({b} : Set G) :=
    le_inf (hJP.trans le_sup_left) hJb
  have hTpc : IsPComponent 2
      (J.subgroupOf ((P ⊔ conjugate P b) ⊓ centralizer ({b} : Set G))) :=
    CatalogueBPrimeJoin.pComponent_subgroupOf_of_le hTK inf_le_right hJp
  obtain ⟨-, -, h3⟩ := UGSChain.orbit_fixed_component_comparison hb hbt
    (pumpUp_le_centralizer J t) hPp hTK hTpc
  refine ⟨hb, ht, hbt, hJb, hJp, pumpUp_le_centralizer J t, hPp,
    mem_normalizer_of_commute fun l hl => (mem_centralizer_singleton_iff.mp (hJt hl)).symm,
    fun j hj => ?_, ?_⟩
  · rw [show j⁻¹ * t⁻¹ * j * t = j⁻¹ * t⁻¹ * (j * t) by group,
      mem_centralizer_singleton_iff.mp (hJt hj), show j⁻¹ * t⁻¹ * (t * j) = 1 by group]
    exact one_mem _
  · rw [hgs]
    exact (h3 hidx).1.symm

omit [Finite G] in
theorem not_oddIn_le_center_pumpUp {J : Subgroup G} {t : G}
    (hsup : J ⊔ oddIn (pumpUp J t) = pumpUp J t)
    (hperf : ⁅pumpUp J t, pumpUp J t⁆ = pumpUp J t)
    (hbad : ¬ oddIn (pumpUp J t) ≤ (center ↥J).map J.subtype) :
    ¬ oddIn (pumpUp J t) ≤ (center ↥(pumpUp J t)).map (pumpUp J t).subtype := by
  set P := pumpUp J t with hP
  intro hc
  have hJP : J ≤ P := le_sup_left.trans hsup.le
  have hJN : J ≤ normalizer (oddIn P : Set G) := fun x hx =>
    normalizer_le_normalizer_oddIn P (le_normalizer (hJP hx))
  have hcen : ∀ o ∈ oddIn P, ∀ y ∈ P, o * y = y * o := by
    intro o ho y hy
    obtain ⟨z, hz, rfl⟩ := hc ho
    exact congrArg Subtype.val (mem_center_iff.mp hz ⟨y, hy⟩).symm
  have hdec : ∀ p ∈ P, ∃ j ∈ J, ∃ o ∈ oddIn P, p = j * o := by
    intro p hp
    have hp' : p ∈ (J : Set G) * (oddIn P : Set G) := by
      rw [← coe_mul_of_left_le_normalizer_right J (oddIn P) hJN, hsup]
      exact hp
    obtain ⟨j, hj, o, ho, rfl⟩ := hp'
    exact ⟨j, hj, o, ho, rfl⟩
  have hPJ : P ≤ J := by
    rw [← hperf, commutator_le]
    intro p hp q hq
    obtain ⟨j, hj, o, ho, rfl⟩ := hdec p hp
    obtain ⟨j', hj', o', ho', rfl⟩ := hdec q hq
    have h1 : o * (j' * o') = j' * o' * o := hcen o ho _ hq
    have h2 : o' * j⁻¹ = j⁻¹ * o' := hcen o' ho' _ (inv_mem (hJP hj))
    have e : ⁅j * o, j' * o'⁆ = ⁅j, j'⁆ := by
      simp only [commutatorElement_def]
      calc j * o * (j' * o') * (j * o)⁻¹ * (j' * o')⁻¹
          = j * (o * (j' * o')) * o⁻¹ * j⁻¹ * (j' * o')⁻¹ := by group
        _ = j * (j' * o' * o) * o⁻¹ * j⁻¹ * (j' * o')⁻¹ := by rw [h1]
        _ = j * j' * (o' * j⁻¹) * o'⁻¹ * j'⁻¹ := by group
        _ = j * j' * (j⁻¹ * o') * o'⁻¹ * j'⁻¹ := by rw [h2]
        _ = j * j' * j⁻¹ * j'⁻¹ := by group
    rw [e, commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hj hj') (inv_mem hj)) (inv_mem hj')
  apply hbad
  have hPeq : P = J := le_antisymm hPJ hJP
  rw [hPeq] at hc
  rw [hPeq]
  exact hc

end CFSG.ComponentClassification.GrSLit.GrS5
