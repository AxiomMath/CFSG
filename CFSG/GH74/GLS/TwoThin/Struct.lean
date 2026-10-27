module

public import CFSG.GH74.GLS.TwoThin.Orbit
public import CFSG.ClassicalInvolution.LBalance.Main
public import CFSG.ClassicalInvolution.LocalComponent.Layer
public import CFSG.LocalAnalysis.ComponentClassification.OddKernelInvolutions
public import CFSG.GH74.GLS.AssemblyComponents

public section

namespace CFSG.GH74.GLS.TwoThin

open Subgroup CFSG.ComponentClassification CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

abbrev barQ (Y : Type) [Group Y] : Type := Y ⧸ pPrimeCore 2 Y

abbrev barMk (Y : Type) [Group Y] : Y →* barQ Y :=
  QuotientGroup.mk' (pPrimeCore 2 Y)

variable {Y : Type} [Group Y] [Finite Y]

omit [Finite Y] in
theorem barMk_surjective : Function.Surjective (barMk Y) := QuotientGroup.mk'_surjective _

omit [Finite Y] in
theorem ker_barMk : (barMk Y).ker = pPrimeCore 2 Y := QuotientGroup.ker_mk' _

theorem odd_card_pPrimeCore (X : Type*) [Group X] [Finite X] : Odd (Nat.card (pPrimeCore 2 X)) :=
  Nat.coprime_two_left.mp pPrimeCore_coprime_card

theorem odd_card_ker_barMk : Odd (Nat.card (barMk Y).ker) := by
  rw [ker_barMk]
  exact odd_card_pPrimeCore Y

theorem orderOf_barMk {s : Y} (hs : orderOf s = 2) : orderOf (barMk Y s) = 2 := by
  have h2 : s ^ 2 = 1 := by
    have := pow_orderOf_eq_one s
    rwa [hs] at this
  have hsq : barMk Y s * barMk Y s = 1 := by
    rw [← map_mul, ← pow_two, h2, map_one]
  refine orderOf_eq_prime (by rw [pow_two]; exact hsq) ?_
  intro h1
  have hmem : s ∈ pPrimeCore 2 Y := (QuotientGroup.eq_one_iff s).mp h1
  have hdvd := Subgroup.orderOf_dvd_natCard _ hmem
  rw [hs] at hdvd
  exact (Nat.not_even_iff_odd.mpr (odd_card_pPrimeCore Y)) (even_iff_two_dvd.mpr hdvd)

theorem oddCore_barQ : CFSG.Open.componentClassificationOddCore (barQ Y) = ⊥ := by
  rw [← CatalogueBAlternating.primeCore_two_eq_oddCore]
  exact pPrimeCore_quotient_eq_bot Y

theorem layer_subgroup_eq_layer {H : Type*} [Group H] : Layer.subgroup H = CFSG.layer H :=
  (CFSG.layer_eq_componentClassification H).symm

theorem map_centralizer_barMk {s : Y} (hs : orderOf s = 2) :
    (centralizer ({s} : Set Y)).map (barMk Y) = centralizer ({barMk Y s} : Set (barQ Y)) :=
  OddKernelInvolutions.image_centralizer (barMk Y) barMk_surjective odd_card_ker_barMk s hs

noncomputable def barMkCentralizer {s : Y} (hs : orderOf s = 2) :
    ↥(centralizer ({s} : Set Y)) →* ↥(centralizer ({barMk Y s} : Set (barQ Y))) :=
  ((barMk Y).comp (centralizer ({s} : Set Y)).subtype).codRestrict _ fun c => by
    rw [← map_centralizer_barMk hs]
    exact ⟨c, c.2, rfl⟩

theorem barMkCentralizer_apply {s : Y} (hs : orderOf s = 2) (c : ↥(centralizer ({s} : Set Y))) :
    ((barMkCentralizer hs c : ↥(centralizer ({barMk Y s} : Set (barQ Y)))) : barQ Y) =
      barMk Y (c : Y) := by
  unfold barMkCentralizer
  rfl

theorem barMkCentralizer_surjective {s : Y} (hs : orderOf s = 2) :
    Function.Surjective (barMkCentralizer hs) := by
  intro x
  have hx : (x : barQ Y) ∈ (centralizer ({s} : Set Y)).map (barMk Y) := by
    rw [map_centralizer_barMk hs]
    exact x.2
  obtain ⟨c, hc, hcx⟩ := hx
  exact ⟨⟨c, hc⟩, Subtype.ext hcx⟩

theorem odd_card_ker_barMkCentralizer {s : Y} (hs : orderOf s = 2) :
    Odd (Nat.card (barMkCentralizer hs).ker) := by
  have h := OddKernel.odd_card_restriction_kernel (barMk Y) odd_card_ker_barMk
    (centralizer ({s} : Set Y))
  have hker : (barMkCentralizer hs).ker = ((barMk Y).domRestrict (centralizer ({s} : Set Y))).ker :=
    MonoidHom.ker_codRestrict _ _ _
  rw [hker]
  exact h

theorem isTwoComponent_map_barMk {s : Y} (hs : orderOf s = 2) {Λ : Subgroup Y}
    (hΛC : Λ ≤ centralizer ({s} : Set Y))
    (hΛ : TwoComponents.IsTwoComponent (Λ.subgroupOf (centralizer ({s} : Set Y)))) :
    TwoComponents.IsTwoComponent
      ((Λ.map (barMk Y)).subgroupOf (centralizer ({barMk Y s} : Set (barQ Y)))) := by
  have h := OddKernelTwoComponents.image (barMkCentralizer hs) (barMkCentralizer_surjective hs)
    (odd_card_ker_barMkCentralizer hs) _ hΛ
  have heq : (Λ.subgroupOf (centralizer ({s} : Set Y))).map (barMkCentralizer hs) =
      (Λ.map (barMk Y)).subgroupOf (centralizer ({barMk Y s} : Set (barQ Y))) := by
    ext x
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact Subgroup.mem_subgroupOf.mpr
        (Subgroup.mem_map.mpr ⟨(c : Y), Subgroup.mem_subgroupOf.mp hc, rfl⟩)
    · intro hx
      obtain ⟨l, hl, hlx⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hx)
      exact ⟨⟨l, hΛC hl⟩, Subgroup.mem_subgroupOf.mpr hl, Subtype.ext hlx⟩
  rwa [heq] at h

theorem map_barMk_le_layer {s : Y} (hs : orderOf s = 2) {Λ : Subgroup Y}
    (hΛC : Λ ≤ centralizer ({s} : Set Y))
    (hΛ : TwoComponents.IsTwoComponent (Λ.subgroupOf (centralizer ({s} : Set Y)))) :
    Λ.map (barMk Y) ≤ CFSG.layer (barQ Y) := by
  have hsq : barMk Y s * barMk Y s = 1 := by
    have := pow_orderOf_eq_one (barMk Y s)
    rwa [orderOf_barMk hs, pow_two] at this
  have hPC : Λ.map (barMk Y) ≤ centralizer ({barMk Y s} : Set (barQ Y)) :=
    (Subgroup.map_mono hΛC).trans (map_centralizer_barMk hs).le
  have h := CFSG.ClassicalInvolution.twoComponent_le_layer_of_l2PrimeBalance
    CFSG.ClassicalInvolution.l2PrimeBalance oddCore_barQ hsq
    (C := centralizer ({barMk Y s} : Set (barQ Y))) rfl (isTwoComponent_map_barMk hs hΛC hΛ)
  rw [Subgroup.map_subgroupOf_eq_of_le hPC, layer_subgroup_eq_layer] at h
  exact h

theorem isComponent_map_barMk {K : Subgroup Y} (hK : TwoComponents.IsTwoComponent K) :
    CFSG.IsComponent (K.map (barMk Y)) :=
  (CFSG.isComponent_iff_open _).mpr
    (TwoComponents.ordinary_of_corefree oddCore_barQ
      (OddKernelTwoComponents.image (barMk Y) barMk_surjective odd_card_ker_barMk K hK))

theorem map_twoLayer_le_layer : (TwoLayer.subgroup Y).map (barMk Y) ≤ CFSG.layer (barQ Y) := by
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le fun K hK => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  exact le_sSup (isComponent_map_barMk hK)

theorem pumpup_structure {s : Y} (hs : orderOf s = 2) {Λ J : Subgroup Y}
    (hΛC : Λ ≤ centralizer ({s} : Set Y))
    (hΛ : TwoComponents.IsTwoComponent (Λ.subgroupOf (centralizer ({s} : Set Y))))
    (hJ : J.map (barMk Y) ≤ ⨆ g ∈ CFSG.layer (barQ Y),
      (Λ.map (barMk Y)).map (MulAut.conj g).toMonoidHom) :
    ∃ L : Subgroup (barQ Y), CFSG.IsComponent L ∧
      ((conjSub (barMk Y s)⁻¹ L = L ∧ Λ.map (barMk Y) ≤ L) ∨
        (conjSub (barMk Y s)⁻¹ L ≠ L ∧ ∃ hAB : ⁅L, conjSub (barMk Y s)⁻¹ L⁆ = ⊥,
          Λ.map (barMk Y) ≤ (swapDiag hAB).range)) ∧
      ∀ K' : Subgroup Y, TwoComponents.IsTwoComponent K' → K' ≤ J →
        K'.map (barMk Y) = L ∨ K'.map (barMk Y) = conjSub (barMk Y s)⁻¹ L := by
  have hs' : orderOf (barMk Y s) = 2 := orderOf_barMk hs
  have hPC : Λ.map (barMk Y) ≤ centralizer ({barMk Y s} : Set (barQ Y)) :=
    (Subgroup.map_mono hΛC).trans (map_centralizer_barMk hs).le
  have hP := isTwoComponent_map_barMk hs hΛC hΛ
  have hPE := map_barMk_le_layer hs hΛC hΛ
  obtain ⟨L, hL, hcases⟩ := exists_component_orbit_location hs' hPC hP hPE
  refine ⟨L, hL, hcases, ?_⟩
  intro K' hK' hKJ
  have hKc := isComponent_map_barMk hK'
  have hLs : CFSG.IsComponent (conjSub (barMk Y s)⁻¹ L) := isComponent_conjSub hL _
  set T : Subgroup (barQ Y) := L ⊔ conjSub (barMk Y s)⁻¹ L with hT
  have hPT : Λ.map (barMk Y) ≤ T := by
    rcases hcases with ⟨-, hPL⟩ | ⟨-, hAB, hPD⟩
    · exact hPL.trans le_sup_left
    · refine hPD.trans ?_
      rintro _ ⟨x, rfl⟩
      exact swapDiag_mem_sup hAB x
  have hnorm : ∀ g ∈ CFSG.layer (barQ Y), T.map (MulAut.conj g).toMonoidHom = T := by
    intro g hg
    have hg' : g ∈ Layer.subgroup (barQ Y) := by rwa [layer_subgroup_eq_layer]
    rw [hT, Subgroup.map_sup]
    have h1 : L.map (MulAut.conj g).toMonoidHom = L :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp
        (ClassicalInvolution.layer_le_normalizer_of_isComponentOf
          ((CFSG.isComponent_iff_open L).mp hL) hg')
    have h2 : (conjSub (barMk Y s)⁻¹ L).map (MulAut.conj g).toMonoidHom =
        conjSub (barMk Y s)⁻¹ L :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp
        (ClassicalInvolution.layer_le_normalizer_of_isComponentOf
          ((CFSG.isComponent_iff_open _).mp hLs) hg')
    rw [h1, h2]
  have hJT : J.map (barMk Y) ≤ T := by
    refine hJ.trans (iSup₂_le fun g hg => ?_)
    exact (Subgroup.map_mono hPT).trans (hnorm g hg).le
  have hKT : K'.map (barMk Y) ≤ T := (Subgroup.map_mono hKJ).trans hJT
  by_contra hne
  obtain ⟨hne1, hne2⟩ := not_or.mp hne
  have hc1 : ⁅K'.map (barMk Y), L⁆ = ⊥ :=
    (CFSG.LocalCores.distinct_components_commute hKc hL).resolve_left hne1
  have hc2 : ⁅K'.map (barMk Y), conjSub (barMk Y s)⁻¹ L⁆ = ⊥ :=
    (CFSG.LocalCores.distinct_components_commute hKc hLs).resolve_left hne2
  have hTc : T ≤ centralizer ((K'.map (barMk Y) : Subgroup (barQ Y)) : Set (barQ Y)) :=
    sup_le (le_centralizer_iff.1 (commutator_eq_bot_iff_le_centralizer.1 hc1))
      (le_centralizer_iff.1 (commutator_eq_bot_iff_le_centralizer.1 hc2))
  exact not_le_centralizer_self_of_isQuasisimple (assembly_isQuasisimple_of_isComponent hKc)
    (hKT.trans hTc)

end CFSG.GH74.GLS.TwoThin
