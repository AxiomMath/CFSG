module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrSourceChange
public import CFSG.GroupTheory.SubnormalJoin
public import CFSG.ClassicalInvolution.LBalance.Main
public import CFSG.Blueprint.Catalog
public import CFSG.LocalAnalysis.ComponentInitial.KProperPumpUpStatement

public section

namespace CFSG.ComponentClassification.UGSChain

open CFSG CFSG.LocalCores Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedGS
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open scoped Pointwise

variable {G : Type*} [Group G] [Finite G]

theorem normalizer_and_core_of_commutator_mem {b e : G} {M : Subgroup G}
    (hMb : M ≤ centralizer ({b} : Set G))
    (hM : IsPComponent 2 (M.subgroupOf (centralizer ({b} : Set G))))
    (heb : e ∈ centralizer ({b} : Set G))
    (hMe : ∀ m ∈ M, m⁻¹ * e⁻¹ * m * e ∈
      (pPrimeCore 2 (centralizer ({b} : Set G))).map (centralizer ({b} : Set G)).subtype) :
    e ∈ normalizer (M : Set G) ∧
      ∀ m ∈ M, m⁻¹ * e⁻¹ * m * e ∈ (pPrimeCore 2 M).map M.subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Hb := centralizer ({b} : Set G) with hHb
  set M' := M.subgroupOf Hb with hM'
  set e' : Hb := ⟨e, heb⟩ with he'
  set q := QuotientGroup.mk' (pPrimeCore 2 Hb) with hq
  have hcomm : ∀ m' : Hb, m' ∈ M' → m'⁻¹ * e'⁻¹ * m' * e' ∈ pPrimeCore 2 Hb := by
    intro m' hm'
    obtain ⟨n, hn, hneq⟩ := mem_map.mp (hMe m' hm')
    have hn' : n = m'⁻¹ * e'⁻¹ * m' * e' := Subtype.ext hneq
    rw [← hn']
    exact hn
  have hcen : q e' ∈ centralizer ((M'.map q : Subgroup (Hb ⧸ pPrimeCore 2 Hb)) : Set _) := by
    rw [mem_centralizer_iff]
    rintro _ ⟨m', hm', rfl⟩
    have h1 : q (m'⁻¹ * e'⁻¹ * m' * e') = 1 := (QuotientGroup.eq_one_iff _).mpr (hcomm m' hm')
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    calc q m' * q e' = q e' * q m' * ((q m')⁻¹ * (q e')⁻¹ * q m' * q e') := by group
      _ = q e' * q m' := by rw [h1, mul_one]
  have hnorm : e' ∈ normalizer (M' : Set Hb) :=
    mem_normalizer_of_map hM (centralizer_le_normalizer _ hcen)
  have heM : e ∈ normalizer (M : Set G) := mem_normalizer_of_subgroupOf hMb hnorm
  refine ⟨heM, fun m hm => ?_⟩
  have hsub : M'.IsSubnormal := by
    obtain ⟨_, _, h, _, _⟩ := hM
    exact h
  set m' : Hb := ⟨m, hMb hm⟩ with hm'
  have hcM : m'⁻¹ * e'⁻¹ * m' * e' ∈ M' := by
    rw [mem_subgroupOf]
    have h2 : e⁻¹ * m * e⁻¹⁻¹ ∈ M := (mem_normalizer_iff.mp (inv_mem heM) m).mp hm
    rw [inv_inv] at h2
    have h3 := mul_mem (inv_mem hm) h2
    rwa [← mul_assoc, ← mul_assoc] at h3
  have hc : m'⁻¹ * e'⁻¹ * m' * e' ∈ (pPrimeCore 2 M').map M'.subtype := by
    rw [UnbalancedCorr.map_pPrimeCore_eq_inf_of_isSubnormal hsub]
    exact mem_inf.mpr ⟨hcM, hcomm m' (mem_subgroupOf.mpr hm)⟩
  have h4 := mem_map_of_mem Hb.subtype hc
  rw [pPrimeCore_map_subgroupOf 2 M Hb hMb] at h4
  exact h4

omit [Finite G] in
theorem conjugate_isPComponent_centralizer {a b : G} (hab : a * b = b * a) {L : Subgroup G}
    (hLb : L ≤ centralizer ({b} : Set G))
    (hL : IsPComponent 2 (L.subgroupOf (centralizer ({b} : Set G)))) :
    conjugate L a ≤ centralizer ({b} : Set G) ∧
      IsPComponent 2 ((conjugate L a).subgroupOf (centralizer ({b} : Set G))) := by
  have haHb : a ∈ centralizer ({b} : Set G) := mem_centralizer_singleton_iff.mpr hab
  refine ⟨fun x hx => ?_, ?_⟩
  · rw [mem_conjugate_iff] at hx
    have h2 := mul_mem (mul_mem (inv_mem haHb) (hLb hx)) haHb
    rwa [show a⁻¹ * (a * x * a⁻¹) * a = x by group] at h2
  · have h := isPComponent_conjugate hL (⟨a, haHb⟩ : centralizer ({b} : Set G))
    rwa [conjugate_subgroupOf_eq] at h

theorem core_trivial_orbit_fixed_layer_containment {G : Type} [Group G]
    [Finite G]
    {a b e : G} (hb : orderOf b = 2) (he : orderOf e = 2) (hab : a * b = b * a)
    (hbe : b * e = e * b) {L : Subgroup G}
    (hLb : L ≤ centralizer ({b} : Set G))
    (hL : IsPComponent 2 (L.subgroupOf (centralizer ({b} : Set G))))
    (hKe : ∀ k ∈ L ⊔ conjugate L a, k⁻¹ * e⁻¹ * k * e ∈
      (pPrimeCore 2 (centralizer ({b} : Set G))).map (centralizer ({b} : Set G)).subtype) :
    e ∈ normalizer (L : Set G) ∧ e ∈ normalizer (conjugate L a : Set G) ∧
    (∀ l ∈ L, l⁻¹ * e⁻¹ * l * e ∈ (pPrimeCore 2 L).map L.subtype) ∧
    (∀ l ∈ conjugate L a, l⁻¹ * e⁻¹ * l * e ∈
      (pPrimeCore 2 (conjugate L a)).map (conjugate L a).subtype) ∧
    gsFixedLayer L e ≤ centralizer ({b} : Set G) ⊓ centralizer ({e} : Set G) ∧
    IsPComponent 2 ((gsFixedLayer L e).subgroupOf
      (centralizer ({b} : Set G) ⊓ centralizer ({e} : Set G))) ∧
    gsFixedLayer L e ≤ gsFixedLayer (L ⊔ conjugate L a) e ∧
    gsFixedLayer (L ⊔ conjugate L a) e ≤
      (pLayer (centralizer ({e} : Set G)) 2).map (centralizer ({e} : Set G)).subtype ∧
    (gsFixedLayer L e : Set G) * ((pPrimeCore 2 L).map L.subtype : Set G) = L ∧
    (pPrimeCore 2 (gsFixedLayer L e)).map (gsFixedLayer L e).subtype =
      gsFixedLayer L e ⊓ (pPrimeCore 2 L).map L.subtype ∧
    ∃ φ : gsFixedLayer L e ⧸ pPrimeCore 2 (gsFixedLayer L e) ≃* L ⧸ pPrimeCore 2 L,
      ∀ (t : gsFixedLayer L e) (ht : (t : G) ∈ L),
        φ t = ((⟨(t : G), ht⟩ : L) : L ⧸ pPrimeCore 2 L) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Hb := centralizer ({b} : Set G) with hHb
  set Ce := centralizer ({e} : Set G) with hCe
  have heHb : e ∈ Hb := mem_centralizer_singleton_iff.mpr hbe.symm
  obtain ⟨hLaHb, hLa⟩ := conjugate_isPComponent_centralizer hab hLb hL
  obtain ⟨heL, hcoreL⟩ := normalizer_and_core_of_commutator_mem hLb hL heHb
    fun l hl => hKe l (mem_sup_left hl)
  obtain ⟨heLa, hcoreLa⟩ := normalizer_and_core_of_commutator_mem hLaHb hLa heHb
    fun l hl => hKe l (mem_sup_right hl)
  obtain ⟨hLsub, -, hLq⟩ := (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 L Hb hLb).mp hL
  have hLasub := ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 _ Hb hLaHb).mp hLa).1
  have hTpc := UnbalancedCorr.gsFixedLayer_isPComponent hLb hLsub heHb he heL hLq hcoreL
  have hTL : gsFixedLayer L e ≤ L := (gsFixedLayer_le_inf L e).trans inf_le_left
  have hTbe : gsFixedLayer L e ≤ Hb ⊓ Ce :=
    (gsFixedLayer_le_inf L e).trans (inf_le_inf_right _ hLb)
  have hsup := gsFixedLayer_sup_map_pPrimeCore he hLq heL hcoreL
  obtain ⟨hcore, φ, hφ⟩ := restriction_quotient_mulEquiv hTL hsup
  have hmul : (gsFixedLayer L e : Set G) * ((pPrimeCore 2 L).map L.subtype : Set G) = L := by
    rw [← coe_sup_primeCore_eq_mul hTL, hsup]
  have hKHb : L ⊔ conjugate L a ≤ Hb := sup_le hLb hLaHb
  have hTK : gsFixedLayer L e ≤ (L ⊔ conjugate L a) ⊓ Ce :=
    (gsFixedLayer_le_inf L e).trans (inf_le_inf_right _ le_sup_left)
  have hTpcK : IsPComponent 2 ((gsFixedLayer L e).subgroupOf ((L ⊔ conjugate L a) ⊓ Ce)) :=
    CatalogueBPrimeJoin.pComponent_subgroupOf_of_le hTK (inf_le_inf_right _ hKHb) hTpc
  have hTV : gsFixedLayer L e ≤ gsFixedLayer (L ⊔ conjugate L a) e := by
    have h1 : (gsFixedLayer L e).subgroupOf ((L ⊔ conjugate L a) ⊓ Ce) ≤
        pLayer ↥((L ⊔ conjugate L a) ⊓ Ce) 2 := le_sSup hTpcK
    have h2 := map_mono (f := ((L ⊔ conjugate L a) ⊓ Ce).subtype) h1
    rwa [map_subgroupOf_eq_of_le hTK] at h2
  have hKsub : ((L ⊔ conjugate L a).subgroupOf Hb).IsSubnormal := by
    rw [subgroupOf_sup hLb hLaHb]
    exact GroupTheory.isSubnormal_sup hLsub hLasub
  have hCKsub : (((L ⊔ conjugate L a) ⊓ Ce).subgroupOf (Hb ⊓ Ce)).IsSubnormal := by
    have h := CatalogueBPrimeJoin.subgroupOf_isSubnormal_of_le (inf_le_left : Hb ⊓ Ce ≤ Hb) hKsub
    have heq : ((L ⊔ conjugate L a) ⊓ Ce).subgroupOf (Hb ⊓ Ce) =
        (L ⊔ conjugate L a).subgroupOf (Hb ⊓ Ce) := by
      ext x
      rw [mem_subgroupOf, mem_subgroupOf, mem_inf]
      exact ⟨fun h => h.1, fun h => ⟨h, (mem_inf.mp x.2).2⟩⟩
    rwa [heq]
  have hW : ∀ W : Subgroup G, W ≤ (L ⊔ conjugate L a) ⊓ Ce →
      IsPComponent 2 (W.subgroupOf ((L ⊔ conjugate L a) ⊓ Ce)) →
      W ≤ (pLayer Ce 2).map Ce.subtype := by
    intro W hWK hWpc
    have hWHb : IsPComponent 2 (W.subgroupOf (Hb ⊓ Ce)) :=
      (CatalogueBPrimeJoin.pComponent_subgroupOf_iff_of_subnormal hWK
        (inf_le_inf_right _ hKHb) hCKsub).mpr hWpc
    have hWCe : W ≤ Ce := hWK.trans inf_le_right
    have hbCe : b ∈ Ce := mem_centralizer_singleton_iff.mpr hbe
    have hb' : orderOf (⟨b, hbCe⟩ : Ce) = 2 := by rw [Subgroup.orderOf_mk]; exact hb
    have hcenb : centralizer ({(⟨b, hbCe⟩ : Ce)} : Set Ce) = (Hb ⊓ Ce).subgroupOf Ce := by
      ext x
      rw [mem_centralizer_singleton_iff, mem_subgroupOf, mem_inf, mem_centralizer_singleton_iff]
      exact ⟨fun h => ⟨congrArg Subtype.val h, x.2⟩, fun h => Subtype.ext h.1⟩
    have hW' : IsPComponent 2
        ((W.subgroupOf Ce).subgroupOf (centralizer ({(⟨b, hbCe⟩ : Ce)} : Set Ce))) := by
      rw [hcenb, UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' inf_le_right 2
        Nat.prime_two]
      exact hWHb
    have hWb : W.subgroupOf Ce ≤ centralizer ({(⟨b, hbCe⟩ : Ce)} : Set Ce) := by
      rw [hcenb]
      intro x hx
      exact mem_subgroupOf.mpr (inf_le_inf_right _ hKHb (hWK (mem_subgroupOf.mp hx)))
    have hb2 : IsPGroup 2 (zpowers (⟨b, hbCe⟩ : Ce)) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hb', pow_one])
    have hbal := ClassicalInvolution.l2PrimeBalance Ce (zpowers (⟨b, hbCe⟩ : Ce)) hb2
    rw [centralizer_zpowers_eq] at hbal
    have hWsubLayer : (W.subgroupOf Ce).subgroupOf
        (centralizer ({(⟨b, hbCe⟩ : Ce)} : Set Ce)) ≤
        pLayer ↥(centralizer ({(⟨b, hbCe⟩ : Ce)} : Set Ce)) 2 := le_sSup hW'
    have hWlayer : W.subgroupOf Ce ≤ pLayer Ce 2 := fun x hx =>
      hbal ⟨⟨x, hWb hx⟩, hWsubLayer (show (⟨x, hWb hx⟩ :
        centralizer ({(⟨b, hbCe⟩ : Ce)} : Set Ce)) ∈
        (W.subgroupOf Ce).subgroupOf _ from hx), rfl⟩
    have h1 := map_mono (f := Ce.subtype) hWlayer
    rwa [map_subgroupOf_eq_of_le hWCe] at h1
  have hVE : gsFixedLayer (L ⊔ conjugate L a) e ≤ (pLayer Ce 2).map Ce.subtype := by
    rw [gsFixedLayer, map_le_iff_le_comap]
    refine sSup_le fun W' hW' => ?_
    rw [← map_le_iff_le_comap]
    have hW'eq : (W'.map ((L ⊔ conjugate L a) ⊓ Ce).subtype).subgroupOf
        ((L ⊔ conjugate L a) ⊓ Ce) = W' :=
      comap_map_eq_self_of_injective ((L ⊔ conjugate L a) ⊓ Ce).subtype_injective W'
    exact hW _ (map_subtype_le W') (by rw [hW'eq]; exact hW')
  exact ⟨heL, heLa, hcoreL, hcoreLa, hTbe, hTpc, hTV, hVE, hmul, hcore, φ, hφ⟩

theorem kProper_core_trivial_orbit_fixed_layer_containment_of_schreier {G : Type} [Group G]
    [Finite G] (hS : SchreierFor Blueprint.Catalog) (hK : Assembly.KProper Blueprint.Catalog G)
    {a b e : G} (hb : orderOf b = 2) (he : orderOf e = 2) (hab : a * b = b * a)
    (hbe : b * e = e * b) (heZ : e ∉ center G) {L : Subgroup G}
    (hLb : L ≤ centralizer ({b} : Set G))
    (hL : IsPComponent 2 (L.subgroupOf (centralizer ({b} : Set G))))
    (hKe : ∀ k ∈ L ⊔ conjugate L a, k⁻¹ * e⁻¹ * k * e ∈
      (pPrimeCore 2 (centralizer ({b} : Set G))).map (centralizer ({b} : Set G)).subtype) :
    e ∈ normalizer (L : Set G) ∧ e ∈ normalizer (conjugate L a : Set G) ∧
    (∀ l ∈ L, l⁻¹ * e⁻¹ * l * e ∈ (pPrimeCore 2 L).map L.subtype) ∧
    (∀ l ∈ conjugate L a, l⁻¹ * e⁻¹ * l * e ∈
      (pPrimeCore 2 (conjugate L a)).map (conjugate L a).subtype) ∧
    gsFixedLayer L e ≤ centralizer ({b} : Set G) ⊓ centralizer ({e} : Set G) ∧
    IsPComponent 2 ((gsFixedLayer L e).subgroupOf
      (centralizer ({b} : Set G) ⊓ centralizer ({e} : Set G))) ∧
    gsFixedLayer L e ≤ gsFixedLayer (L ⊔ conjugate L a) e ∧
    gsFixedLayer (L ⊔ conjugate L a) e ≤
      (pLayer (centralizer ({e} : Set G)) 2).map (centralizer ({e} : Set G)).subtype ∧
    (gsFixedLayer L e : Set G) * ((pPrimeCore 2 L).map L.subtype : Set G) = L ∧
    (pPrimeCore 2 (gsFixedLayer L e)).map (gsFixedLayer L e).subtype =
      gsFixedLayer L e ⊓ (pPrimeCore 2 L).map L.subtype ∧
    ∃ φ : gsFixedLayer L e ⧸ pPrimeCore 2 (gsFixedLayer L e) ≃* L ⧸ pPrimeCore 2 L,
      ∀ (t : gsFixedLayer L e) (ht : (t : G) ∈ L),
        φ t = ((⟨(t : G), ht⟩ : L) : L ⧸ pPrimeCore 2 L) := by
  exact core_trivial_orbit_fixed_layer_containment hb he hab hbe hLb hL hKe

end CFSG.ComponentClassification.UGSChain
