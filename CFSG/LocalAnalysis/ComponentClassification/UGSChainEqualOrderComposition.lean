module

public import CFSG.LocalAnalysis.ComponentClassification.UGSChainOrbitTools

public section

namespace CFSG.ComponentClassification.UGSChain

open CFSG CFSG.LocalCores Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedGS
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem commutator_conj_eq {a e l : G} (hae : a * e = e * a) :
    l⁻¹ * e⁻¹ * l * e = a⁻¹ * ((a * l * a⁻¹)⁻¹ * e⁻¹ * (a * l * a⁻¹) * e) * a⁻¹⁻¹ := by
  have h1 : a⁻¹ * e * a = e := by rw [mul_assoc, ← hae, inv_mul_cancel_left]
  have h2 : a⁻¹ * e⁻¹ * a = e⁻¹ := by
    rw [show a⁻¹ * e⁻¹ * a = (a⁻¹ * e * a)⁻¹ by group, h1]
  calc l⁻¹ * e⁻¹ * l * e = l⁻¹ * (a⁻¹ * e⁻¹ * a) * l * (a⁻¹ * e * a) := by rw [h1, h2]
    _ = a⁻¹ * ((a * l * a⁻¹)⁻¹ * e⁻¹ * (a * l * a⁻¹) * e) * a⁻¹⁻¹ := by group

theorem equal_order_core_trivial_correspondence_composition_of_schreier {G : Type} [Group G]
    [Finite G] (hS : SchreierFor Blueprint.Catalog) (hK : Assembly.KProper Blueprint.Catalog G)
    {a b e : G} {J L M : Subgroup G} (h1 : GSCorr a J b L) (h2 : GSCorr b L e M)
    (hae : a * e = e * a) (heZ : e ∉ center G) (heJ : e ∈ normalizer (J : Set G))
    (hJe : ∀ j ∈ J, j⁻¹ * e⁻¹ * j * e ∈ (pPrimeCore 2 J).map J.subtype)
    (hidx : (pPrimeCore 2 J).index = (pPrimeCore 2 M).index) :
    GSCorr a J e M ∧ (L ≠ conjugate L a → M ≠ conjugate M a ∧ ¬ GSIsoCorr a J e M) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcmp1 := UnbalancingLocal.correspondence_quotient_order_comparison h1
  have hcmp2 := UnbalancingLocal.correspondence_quotient_order_comparison h2
  have h1' := h1
  have h2' := h2
  obtain ⟨ha, hb, hab, hJa, hJ, hLb, hL, hbJ, hJb, -⟩ := h1'
  obtain ⟨-, he, hbe, -, -, hMe, hM, heL, hLe, -⟩ := h2'
  set Ca := centralizer ({a} : Set G) with hCa
  set Hb := centralizer ({b} : Set G) with hHb
  set Ce := centralizer ({e} : Set G) with hCe
  have haa : a * a = 1 := by rw [← pow_two, ← ha, pow_orderOf_eq_one]
  have haHb : a ∈ Hb := mem_centralizer_singleton_iff.mpr hab
  have hLNb : (pPrimeCore 2 L).map L.subtype ≤ (pPrimeCore 2 Hb).map Hb.subtype :=
    map_pPrimeCore_le_of_isPComponent hLb hL
  have hHbN : Hb ≤ normalizer (((pPrimeCore 2 Hb).map Hb.subtype : Subgroup G) : Set G) :=
    fun g hg => normalizer_le_normalizer_map_of_characteristic Hb (pPrimeCore 2 Hb)
      (le_normalizer hg)
  obtain ⟨hLaHb, hLa⟩ := conjugate_isPComponent_centralizer hab hLb hL
  have hKe : ∀ k ∈ L ⊔ conjugate L a, k⁻¹ * e⁻¹ * k * e ∈ (pPrimeCore 2 Hb).map Hb.subtype := by
    intro k hk
    refine commutator_mem_of_mem_sup hHbN hLb hLaHb (fun l hl => hLNb (hLe l hl))
      (fun l hl => ?_) hk
    have h3 := hLNb (hLe _ (mem_conjugate_iff.mp hl))
    rw [commutator_conj_eq hae]
    exact (mem_normalizer_iff.mp (hHbN (inv_mem haHb)) _).mp h3
  obtain ⟨-, heLa, -, hLae, hTeHbe, hTepc, hTeV, hVE, -, -, φTe, -⟩ :=
    kProper_core_trivial_orbit_fixed_layer_containment_of_schreier hS hK hb he hab hbe heZ hLb
      hL hKe
  have hJaJ : conjugate J a = J := UnbalancedCorr.conjugate_eq_self_of_le_centralizer hJa
  have hKeJ : ∀ k ∈ J ⊔ conjugate J a, k⁻¹ * e⁻¹ * k * e ∈ (pPrimeCore 2 Ca).map Ca.subtype := by
    intro k hk
    rw [hJaJ, sup_idem] at hk
    exact map_pPrimeCore_le_of_isPComponent hJa hJ (hJe k hk)
  obtain ⟨-, -, -, -, hUae, hUpc, hUV, hVEJ, -, -, φU, -⟩ :=
    kProper_core_trivial_orbit_fixed_layer_containment_of_schreier hS hK (a := a) (b := a)
      (e := e) ha he rfl hae heZ hJa hJ hKeJ
  obtain ⟨A, hACe, hA, hUF, hUFpc⟩ :=
    exists_orbit_component_of_le_pLayer ha hae hUae hUpc (hUV.trans hVEJ)
  obtain ⟨hAaCe, hAa⟩ := conjugate_isPComponent_centralizer hae hACe hA
  have hEF : (pLayer Ce 2).map Ce.subtype ≤
      normalizer ((A ⊔ conjugate A a : Subgroup G) : Set G) := fun g hg =>
    UnbalancedCorr.mem_normalizer_sup (map_pLayer_le_normalizer hACe hA hg)
      (map_pLayer_le_normalizer hAaCe hAa hg)
  have heK : e ∈ normalizer ((L ⊔ conjugate L a : Subgroup G) : Set G) :=
    UnbalancedCorr.mem_normalizer_sup heL heLa
  obtain ⟨hWTU, -, -, -, -, hWV, hWcl⟩ :=
    UnbalancedCorr.correspondence_nested_fixed_layer_normal_closure h1 he hbe heJ heK hJe hKe
      rfl rfl rfl rfl
  have hVF : gsFixedLayer (L ⊔ conjugate L a) e ≤ A ⊔ conjugate A a := by
    set V := gsFixedLayer (L ⊔ conjugate L a) e with hVdef
    have hFn : ((A ⊔ conjugate A a).subgroupOf V).Normal :=
      ⟨fun n hn g => mem_subgroupOf.mpr ((mem_normalizer_iff.mp (hEF (hVE g.2)) n).mp
        (mem_subgroupOf.mp hn))⟩
    have hcl : normalClosure (((pLayer ↥(J ⊓ centralizer ({b, e} : Set G)) 2).map
        (J ⊓ centralizer ({b, e} : Set G)).subtype).subgroupOf V : Set V) ≤
        (A ⊔ conjugate A a).subgroupOf V :=
      normalClosure_le_normal fun x hx => hUF ((hWTU (mem_subgroupOf.mp hx)).2)
    rw [hWcl] at hcl
    intro v hv
    exact hcl (mem_top (⟨v, hv⟩ : V))
  obtain ⟨-, -, hcl2, -⟩ := UnbalancedCorr.correspondence_normal_closure h2
    (E := (pLayer Ce 2).map Ce.subtype) (K := M ⊔ conjugate M b) (T := gsFixedLayer L e) rfl rfl
    rfl
  have hMF : M ≤ A ⊔ conjugate A a := by
    have hle : (⨆ g ∈ (pLayer Ce 2).map Ce.subtype, conjugate (gsFixedLayer L e) g) ≤
        A ⊔ conjugate A a := by
      refine iSup₂_le fun g hg => fun y hy => ?_
      rw [mem_conjugate_iff] at hy
      have h3 := (mem_normalizer_iff.mp (inv_mem (hEF hg)) _).mp ((hTeV.trans hVF) hy)
      rwa [show g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y by group] at h3
    rw [hcl2] at hle
    exact le_sup_left.trans hle
  have hAsub : (A.subgroupOf Ce).IsSubnormal :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 A Ce hACe).mp hA).1
  have hAasub : ((conjugate A a).subgroupOf Ce).IsSubnormal :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 _ Ce hAaCe).mp hAa).1
  have hF : A ⊔ conjugate A a = M ⊔ conjugate M a := by
    rcases le_or_le_of_le_sup hMe hM hACe hAaCe hAsub hAasub hMF with h | h
    · have h3 := (CatalogueBPrimeJoin.distinct_p_components_core_commutation 2 Nat.prime_two _ _
        hM hA).1 (fun x hx => h hx)
      rw [eq_of_subgroupOf_eq hMe hACe h3]
    · have h3 := (CatalogueBPrimeJoin.distinct_p_components_core_commutation 2 Nat.prime_two _ _
        hM hAa).1 (fun x hx => h hx)
      rw [eq_of_subgroupOf_eq hMe hAaCe h3, conjugate_conjugate_self_of_mul_self haa, sup_comm]
  have hUK : gsFixedLayer J e ≤ (M ⊔ conjugate M a) ⊓ Ca :=
    le_inf (hF ▸ hUF) (hUae.trans inf_le_left)
  have hUKpc : IsPComponent 2 ((gsFixedLayer J e).subgroupOf ((M ⊔ conjugate M a) ⊓ Ca)) :=
    hF ▸ hUFpc
  have hidxU : (pPrimeCore 2 (gsFixedLayer J e)).index = (pPrimeCore 2 M).index := by
    rw [← hidx, index_eq_card, index_eq_card]
    exact Nat.card_congr φU.toEquiv
  obtain ⟨-, -, hcomp⟩ := orbit_fixed_component_comparison ha hae hMe hM hUK hUKpc
  have hcorr : GSCorr a J e M := ⟨ha, he, hae, hJa, hJ, hMe, hM, heJ, hJe, ((hcomp hidxU).1).symm⟩
  refine ⟨hcorr, fun hLne => ?_⟩
  have hMne : M ≠ conjugate M a := by
    intro hMa
    have hVM : gsFixedLayer (L ⊔ conjugate L a) e ≤ M := by
      have h3 := hVF
      rwa [hF, ← hMa, sup_idem] at h3
    have hKeLa : ∀ k ∈ conjugate L a ⊔ conjugate (conjugate L a) a,
        k⁻¹ * e⁻¹ * k * e ∈ (pPrimeCore 2 Hb).map Hb.subtype := by
      rw [conjugate_conjugate_self_of_mul_self haa, sup_comm]
      exact hKe
    obtain ⟨-, -, -, -, -, hTapc, hTaV, -, -, -, φTa, -⟩ :=
      kProper_core_trivial_orbit_fixed_layer_containment_of_schreier hS hK hb he hab hbe heZ
        hLaHb hLa hKeLa
    rw [conjugate_conjugate_self_of_mul_self haa, sup_comm] at hTaV
    have hVle : gsFixedLayer (L ⊔ conjugate L a) e ≤ Hb ⊓ Ce :=
      (gsFixedLayer_le_inf _ e).trans (inf_le_inf_right _ (sup_le hLb hLaHb))
    have hTepcV := CatalogueBPrimeJoin.pComponent_subgroupOf_of_le hTeV hVle hTepc
    have hTapcV := CatalogueBPrimeJoin.pComponent_subgroupOf_of_le hTaV hVle hTapc
    have hdL : Nat.card (L ⧸ pPrimeCore 2 L) = Nat.card (M ⧸ pPrimeCore 2 M) := by
      have hJM : Nat.card (J ⧸ pPrimeCore 2 J) = Nat.card (M ⧸ pPrimeCore 2 M) := by
        rw [← index_eq_card, ← index_eq_card, hidx]
      exact le_antisymm hcmp2.1 (hJM ▸ hcmp1.1)
    have hLaL : Nat.card (conjugate L a ⧸ pPrimeCore 2 (conjugate L a)) =
        Nat.card (L ⧸ pPrimeCore 2 L) :=
      (UnbalancingLocal.Correspondence.card_quotient_pPrimeCore_congr
        ((MulAut.conj a⁻¹).subgroupMap L)).symm
    have hidxTe : (pPrimeCore 2 (gsFixedLayer L e)).index = (pPrimeCore 2 M).index := by
      rw [index_eq_card, index_eq_card, Nat.card_congr φTe.toEquiv, hdL]
    have hidxTa : (pPrimeCore 2 (gsFixedLayer (conjugate L a) e)).index =
        (pPrimeCore 2 M).index := by
      rw [index_eq_card, index_eq_card, Nat.card_congr φTa.toEquiv, hLaL, hdL]
    obtain ⟨-, hse⟩ := OrbitFixedComponent.stable_case M _ hVM _ hTeV hTepcV
    obtain ⟨-, hsa⟩ := OrbitFixedComponent.stable_case M _ hVM _ hTaV hTapcV
    have hTeq : gsFixedLayer L e = gsFixedLayer (conjugate L a) e :=
      (hse hidxTe).1.symm.trans (hsa hidxTa).1
    have hLq := ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 L Hb hLb).mp hL).2.2
    have hLaq := ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 _ Hb hLaHb).mp hLa).2.2
    have hq1 := map_mk_eq_of_sup_pPrimeCore hLb hL (gsFixedLayer_sup_map_pPrimeCore he hLq heL hLe)
    have hq2 := map_mk_eq_of_sup_pPrimeCore hLaHb hLa
      (gsFixedLayer_sup_map_pPrimeCore he hLaq heLa hLae)
    rw [hTeq] at hq1
    exact hLne (eq_of_subgroupOf_eq hLb hLaHb (pComponent_eq_of_map_eq hL hLa (hq1.trans hq2.symm)))
  refine ⟨hMne, fun hiso => hMne ?_⟩
  have hMaM : conjugate M a ≤ M := le_sup_right.trans hiso.2.1.le
  have hcard : Nat.card M ≤ Nat.card (conjugate M a) := by
    rw [conjugate, card_map_of_injective (MulAut.conj a⁻¹).injective]
  exact (eq_of_le_of_card_ge hMaM hcard).symm

end CFSG.ComponentClassification.UGSChain
