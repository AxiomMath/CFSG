module

public import CFSG.GH74.GLS.TwoThin.Equivariance
public import CFSG.GH74.GLS.TwoThin.PhiData
public import CFSG.GH74.Generic.BProg.B1.Lift0
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAFixedLayerPComponent
public import CFSG.GH74.GLS.TwoThin.PumpData

public section

namespace CFSG.GH74.Generic.BProg.B2.SD.TwoA7Geo

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.TwoThin CFSG.GH74.Generic CFSG.GH74.Generic.BProg
  CFSG.ComponentClassification CFSG.LocalAnalysis.ComponentInitial
  CFSG.ABGLocalTools CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem conj_mem_centralizer_of_mem_normalizer {X : Type*} [Group X] {S : Subgroup X} {g h : X}
    (hg : g ∈ normalizer (S : Set X)) (hh : h ∈ centralizer (S : Set X)) :
    g * h * g⁻¹ ∈ centralizer (S : Set X) := by
  rw [Subgroup.mem_centralizer_iff] at hh ⊢
  intro s hs
  have hs' : g⁻¹ * s * g ∈ S := by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) s).mp hs
    simpa using this
  have h2 := hh _ hs'
  calc s * (g * h * g⁻¹) = g * ((g⁻¹ * s * g) * h) * g⁻¹ := by group
    _ = g * (h * (g⁻¹ * s * g)) * g⁻¹ := by rw [h2]
    _ = (g * h * g⁻¹) * s := by group

theorem mem_normalizer_centralizer' {X : Type*} [Group X] {S : Subgroup X} {g : X}
    (hg : g ∈ normalizer (S : Set X)) : g ∈ normalizer (centralizer (S : Set X) : Set X) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => conj_mem_centralizer_of_mem_normalizer hg hh, fun hh => ?_⟩
  have := conj_mem_centralizer_of_mem_normalizer (inv_mem hg) hh
  simpa [mul_assoc] using this

theorem isSubnormal_of_le_layer_of_isSubnormal_centralizer {Hb : Type} [Group Hb] [Finite Hb]
    {L D Eb : Subgroup Hb} (hL : IsComponent L) (hEL : Eb ≤ L) (hDlayer : D ≤ layer Hb)
    (hDL : D ≤ centralizer (L : Set Hb))
    (hDsub : (D.subgroupOf (centralizer (Eb : Set Hb))).IsSubnormal) : D.IsSubnormal := by
  set P₀ := layer Hb ⊓ centralizer (L : Set Hb) with hP₀
  have hDP : D ≤ P₀ := le_inf hDlayer hDL
  have hPC : P₀ ≤ centralizer (Eb : Set Hb) :=
    inf_le_right.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hEL))
  have h1 : (D.subgroupOf P₀).IsSubnormal := by
    have := B1.isSubnormal_subgroupOf_inf (S := P₀) hDsub
    rwa [inf_eq_left.mpr hDP, inf_eq_right.mpr hPC] at this
  have hLay : (layer Hb).IsSubnormal := by
    have : (layer Hb).Characteristic := LocalCores.layer_characteristic
    exact (inferInstance : (layer Hb).Normal).isSubnormal
  have hnorm : layer Hb ≤ normalizer (P₀ : Set Hb) := by
    intro g hg
    exact TwoThin.mem_normalizer_inf (Subgroup.le_normalizer hg)
      (mem_normalizer_centralizer' (LocalCores.layer_le_normalizer hL hg))
  have hPnormal : (P₀.subgroupOf (layer Hb)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr hnorm
  have hP₀sub : P₀.IsSubnormal :=
    Subgroup.IsSubnormal.trans inf_le_left hPnormal.isSubnormal hLay
  exact Subgroup.IsSubnormal.trans hDP h1 hP₀sub


theorem centralizer_map_barMk_le {H E : Subgroup G} (hEH : E ≤ H) (hE2 : IsPGroup 2 ↥E) :
    centralizer (((E.subgroupOf H).map (barMk ↥H) : Subgroup (barQ ↥H)) : Set (barQ ↥H)) ≤
      ((H ⊓ centralizer (E : Set G)).subgroupOf H).map (barMk ↥H) := by
  have h1 := B1.map_centralizer_eq_centralizer_map_of_isPGroup (pPrimeCore 2 ↥H)
    (Nat.coprime_two_left.mp pPrimeCore_coprime_card) (A := E.subgroupOf H) hE2.comap_subtype
  have h1' : (centralizer ((E.subgroupOf H : Subgroup ↥H) : Set ↥H)).map (barMk ↥H) =
      centralizer (((E.subgroupOf H).map (barMk ↥H) : Subgroup (barQ ↥H)) : Set (barQ ↥H)) := h1
  rw [← h1']
  refine Subgroup.map_mono fun h hh => ?_
  rw [Subgroup.mem_subgroupOf]
  refine Subgroup.mem_inf.mpr ⟨h.2, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro e he
  have := Subgroup.mem_centralizer_iff.mp hh ⟨e, hEH he⟩ (Subgroup.mem_subgroupOf.mpr he)
  exact congrArg Subtype.val this



omit [Finite G] in
theorem pLayerOf_eq_map_pLayer (p : ℕ) (H : Subgroup G) :
    pLayerOf p H = (pLayer ↥H p).map H.subtype := by
  apply le_antisymm
  · refine sSup_le fun L hL => ?_
    obtain ⟨hLH, hL2⟩ := hL
    rw [← Subgroup.map_subgroupOf_eq_of_le hLH]
    exact Subgroup.map_mono (le_sSup hL2)
  · rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun M hM => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    refine le_sSup ⟨?_, ?_⟩
    · rintro _ ⟨m, -, rfl⟩
      exact m.2
    · have : (M.map H.subtype).subgroupOf H = M :=
        Subgroup.comap_map_eq_self_of_injective H.subtype_injective M
      rw [this]
      exact hM


theorem pLayerOf_inf_centralizer_le_two {H U : Subgroup G} (hUH : U ≤ H) (hU2 : IsPGroup 2 ↥U) :
    pLayerOf 2 (H ⊓ centralizer (U : Set G)) ≤ pLayerOf 2 H := by
  rw [pLayerOf_eq_map_pLayer, pLayerOf_eq_map_pLayer]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A' : Subgroup ↥H := U.subgroupOf H with hA'
  have hA'2 : IsPGroup 2 ↥A' := hU2.comap_of_injective H.subtype H.subtype_injective
  have hbal := ClassicalInvolution.l2PrimeBalance ↥H A' hA'2
  set Z : Subgroup ↥H := centralizer (A' : Set ↥H) with hZ
  have hZmap : Z.map H.subtype = H ⊓ centralizer (U : Set G) := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine Subgroup.mem_inf.mpr ⟨z.2, Subgroup.mem_centralizer_iff.mpr fun a ha => ?_⟩
      exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hz ⟨a, hUH ha⟩ ha)
    · intro hx
      obtain ⟨hxH, hxC⟩ := Subgroup.mem_inf.mp hx
      refine ⟨⟨x, hxH⟩, Subgroup.mem_centralizer_iff.mpr fun a ha => ?_, rfl⟩
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC (a : G) ha)
  let e : ↥Z ≃* ↥(H ⊓ centralizer (U : Set G)) :=
    (Z.equivMapOfInjective H.subtype H.subtype_injective).trans (MulEquiv.subgroupCongr hZmap)
  have hlayer := ComponentClassification.UnbalancedGS.FixedLayerPComponent.map_pLayer_mulEquiv 2 e
  have key : (pLayer ↥(H ⊓ centralizer (U : Set G)) 2).map (H ⊓ centralizer (U : Set G)).subtype =
      ((pLayer ↥Z 2).map Z.subtype).map H.subtype := by
    rw [← hlayer, Subgroup.map_map, Subgroup.map_map]
    congr 1
  rw [key]
  exact Subgroup.map_mono hbal

theorem geo_component {H E J₂ : Subgroup G} (hE2 : IsPGroup 2 ↥E) (hEH : E ≤ H)
    (hJ₂ : IsPCompIn 2 (H ⊓ centralizer (E : Set G)) J₂)
    {L : Subgroup (barQ ↥H)} (hL : IsComponent L)
    (hEL : ∀ (e : G) (he : e ∈ E), barMk ↥H ⟨e, hEH he⟩ ∈ L)
    {N : Subgroup (barQ ↥H)} (hNodd : ¬ 2 ∣ Nat.card ↥N)
    (hNL : ∀ l ∈ L, ∀ n ∈ N, l * n * l⁻¹ ∈ N)
    (hcomm : ∀ (j : G) (hj : j ∈ H), j ∈ J₂ → ∀ l ∈ L, ⁅barMk ↥H ⟨j, hj⟩, l⁆ ∈ N) :
    IsComponent ((J₂.subgroupOf H).map (barMk ↥H)) ∧
      ∀ (j : G) (hj : j ∈ H), j ∈ J₂ → ∀ l ∈ L,
        barMk ↥H ⟨j, hj⟩ * l = l * barMk ↥H ⟨j, hj⟩ := by
  set Y : Subgroup G := H ⊓ centralizer (E : Set G) with hY
  have hYH : Y ≤ H := inf_le_left
  have hJ₂Y : J₂ ≤ Y := hJ₂.1
  have hJ₂H : J₂ ≤ H := hJ₂Y.trans hYH
  set D : Subgroup (barQ ↥H) := (J₂.subgroupOf H).map (barMk ↥H) with hD
  set Eb : Subgroup (barQ ↥H) := (E.subgroupOf H).map (barMk ↥H) with hEb
  set R : Subgroup (barQ ↥H) := (Y.subgroupOf H).map (barMk ↥H) with hR
  have hDlayer : D ≤ layer (barQ ↥H) := by
    have h1 : J₂ ≤ pLayerOf 2 H :=
      (le_sSup hJ₂ : J₂ ≤ pLayerOf 2 Y).trans (pLayerOf_inf_centralizer_le_two hEH hE2)
    rw [pLayerOf_two_eq_map] at h1
    have h2 : J₂.subgroupOf H ≤ TwoLayer.subgroup ↥H := by
      intro x hx
      obtain ⟨t, ht, htx⟩ := h1 (Subgroup.mem_subgroupOf.mp hx)
      have : t = x := Subtype.ext htx
      rwa [← this]
    exact (Subgroup.map_mono h2).trans map_twoLayer_le_layer
  have hLcore : pPrimeCore 2 ↥L = ⊥ := by
    rw [CatalogueBAlternating.primeCore_two_eq_oddCore (G := ↥L)]
    exact OddCore.subnormal_corefree oddCore_barQ L (Components.chain_of_mathlib_subnormal hL.2)
  have hcommDL : ∀ (j : G) (hj : j ∈ H), j ∈ J₂ → ∀ l ∈ L,
      barMk ↥H ⟨j, hj⟩ * l = l * barMk ↥H ⟨j, hj⟩ := by
    intro j hj hjJ l hl
    have hjD : barMk ↥H ⟨j, hj⟩ ∈ D := ⟨⟨j, hj⟩, hjJ, rfl⟩
    have hnorm := LocalCores.layer_le_normalizer hL (hDlayer hjD)
    have h1 : barMk ↥H ⟨j, hj⟩ * l * (barMk ↥H ⟨j, hj⟩)⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp hnorm l).mp hl
    have h2 : ⁅barMk ↥H ⟨j, hj⟩, l⁆ ∈ L := by
      rw [commutatorElement_def]
      exact mul_mem h1 (inv_mem hl)
    have h3 := hcomm j hj hjJ l hl
    have hnormal : ((L ⊓ N).subgroupOf L).Normal := by
      refine ⟨fun m hm g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hm ⊢
      exact Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem g.2 hm.1) (inv_mem g.2),
        hNL g g.2 m hm.2⟩
    have hdvd : Nat.card ((L ⊓ N).subgroupOf L) ∣ Nat.card N := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : L ⊓ N ≤ L)).toEquiv]
      exact Subgroup.card_dvd_of_le inf_le_right
    have hcard : Nat.Coprime 2 (Nat.card ((L ⊓ N).subgroupOf L)) :=
      Nat.Coprime.coprime_dvd_right hdvd (Nat.coprime_two_left.mpr
        (Nat.odd_iff.mpr (Nat.mod_two_ne_zero.mp fun h => hNodd (Nat.dvd_of_mod_eq_zero h))))
    have hle : (L ⊓ N).subgroupOf L ≤ pPrimeCore 2 ↥L := le_sSup ⟨hnormal, hcard⟩
    rw [hLcore, le_bot_iff] at hle
    have h4 : (⟨⁅barMk ↥H ⟨j, hj⟩, l⁆, h2⟩ : ↥L) ∈ (L ⊓ N).subgroupOf L :=
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨h2, h3⟩)
    rw [hle, Subgroup.mem_bot] at h4
    have h5 : ⁅barMk ↥H ⟨j, hj⟩, l⁆ = 1 := congrArg Subtype.val h4
    rwa [commutatorElement_eq_one_iff_mul_comm] at h5
  refine ⟨?_, hcommDL⟩
  have hEbL : Eb ≤ L := by
    rintro _ ⟨e, he, rfl⟩
    exact hEL (e : G) he
  have hRC : R = centralizer (Eb : Set (barQ ↥H)) := by
    apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨e, he, rfl⟩
      have hyc : (y : G) ∈ centralizer (E : Set G) := (Subgroup.mem_inf.mp hy).2
      have := Subgroup.mem_centralizer_iff.mp hyc (e : G) he
      rw [← map_mul, ← map_mul]
      exact congrArg (barMk ↥H) (Subtype.ext this)
    · exact centralizer_map_barMk_le hEH hE2
  let ψ : ↥Y →* ↥R :=
    ((barMk ↥H).comp (Subgroup.inclusion hYH)).codRestrict R
      (fun y => ⟨Subgroup.inclusion hYH y, y.2, rfl⟩)
  have hψs : Function.Surjective ψ := by
    rintro ⟨r, h, hh, rfl⟩
    exact ⟨⟨h.1, hh⟩, Subtype.ext rfl⟩
  have hψk : Odd (Nat.card ψ.ker) := by
    have hnd : ¬ 2 ∣ Nat.card ((barMk ↥H).comp (Subgroup.inclusion hYH)).ker :=
      B1.not_two_dvd_card_ker_comp_mk (Subgroup.inclusion hYH) (Subgroup.inclusion_injective hYH)
        (pPrimeCore 2 ↥H) (Nat.coprime_two_left.mp pPrimeCore_coprime_card)
    have hkerψ : ψ.ker = ((barMk ↥H).comp (Subgroup.inclusion hYH)).ker :=
      MonoidHom.ker_codRestrict _ _ _
    rw [hkerψ]
    exact Nat.odd_iff.mpr (Nat.mod_two_ne_zero.mp fun h => hnd (Nat.dvd_of_mod_eq_zero h))
  have hDR : D ≤ R := Subgroup.map_mono fun x hx => hJ₂Y hx
  have hmapeq : (J₂.subgroupOf Y).map ψ = D.subgroupOf R := by
    ext ⟨r, hr⟩
    constructor
    · rintro ⟨y, hy, hyr⟩
      have : r = barMk ↥H (Subgroup.inclusion hYH y) := congrArg Subtype.val hyr.symm
      rw [Subgroup.mem_subgroupOf]
      show r ∈ D
      rw [this]
      exact ⟨Subgroup.inclusion hYH y, hy, rfl⟩
    · intro hmem
      obtain ⟨h, hh, hhr⟩ := Subgroup.mem_subgroupOf.mp hmem
      exact ⟨⟨h.1, hJ₂Y hh⟩, hh, Subtype.ext hhr⟩
  have hJ₂c : TwoComponents.IsTwoComponent (J₂.subgroupOf Y) := (isPCompIn_two_iff.mp hJ₂).2
  have hX : TwoComponents.IsTwoComponent ((J₂.subgroupOf Y).map ψ) :=
    OddKernelTwoComponents.image ψ hψs hψk _ hJ₂c
  rw [hmapeq] at hX
  obtain ⟨hDsubR, hDres, hDqs⟩ := (TwoComponentTransport.subgroupOf_iff D R hDR).mp hX
  have hDsubC : (D.subgroupOf (centralizer (Eb : Set (barQ ↥H)))).IsSubnormal := by
    rw [← hRC]
    exact hDsubR
  have hDL : D ≤ centralizer (L : Set (barQ ↥H)) := by
    rintro _ ⟨j, hj, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact (hcommDL j.1 j.2 hj l hl).symm
  have hDsub : D.IsSubnormal :=
    isSubnormal_of_le_layer_of_isSubnormal_centralizer hL hEbL hDlayer hDL hDsubC
  have hD2 : TwoComponents.IsTwoComponent D :=
    (TwoComponentConvention.twoComponent_iff D).mpr
      ⟨Components.chain_of_mathlib_subnormal hDsub, hDres, hDqs⟩
  exact (CFSG.isComponent_iff_open D).mpr (TwoComponents.ordinary_of_corefree oddCore_barQ hD2)



theorem mem_conjSub' {X : Type*} [Group X] {x : X} {H : Subgroup X} {v : X} :
    v ∈ conjSub x H ↔ x⁻¹ * v * x ∈ H := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    change x⁻¹ * (x * h * x⁻¹) * x ∈ H
    simpa [mul_assoc] using hh
  · intro hv
    refine ⟨x⁻¹ * v * x, hv, ?_⟩
    change x * (x⁻¹ * v * x) * x⁻¹ = v
    group


omit [Finite G] in
theorem conjSub_barMk_eq_of_mem_normalizer {Y' MG : Subgroup G} {g : G}
    (hgY : g ∈ Y') (hg : g ∈ normalizer (MG : Set G)) :
    conjSub (barMk ↥Y' ⟨g, hgY⟩)⁻¹ ((MG.subgroupOf Y').map (barMk ↥Y')) =
      (MG.subgroupOf Y').map (barMk ↥Y') := by
  ext v
  rw [mem_conjSub', inv_inv]
  constructor
  · rintro ⟨m, hm, hmv⟩
    refine ⟨(⟨g, hgY⟩ : ↥Y')⁻¹ * m * ⟨g, hgY⟩, ?_, ?_⟩
    · have hm' : (m : G) ∈ MG := Subgroup.mem_subgroupOf.mp hm
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) (m : G)).mp hm'
      exact Subgroup.mem_subgroupOf.mpr (by simpa using this)
    · rw [map_mul, map_mul, map_inv, hmv]
      group
  · rintro ⟨y, hy, rfl⟩
    refine ⟨⟨g, hgY⟩ * y * ⟨g, hgY⟩⁻¹, ?_, ?_⟩
    · have hy' : (y : G) ∈ MG := Subgroup.mem_subgroupOf.mp hy
      have := (Subgroup.mem_normalizer_iff.mp hg (y : G)).mp hy'
      exact Subgroup.mem_subgroupOf.mpr this
    · rw [map_mul, map_mul, map_inv]


theorem pumpup_component_of_terminal {x u : G} {K : Subgroup G} (hterm : IsTwoTerminal x K)
    (hu2 : orderOf u = 2) (hux : u ∈ centralizer ({x} : Set G))
    (huK : u ∈ centralizerSection K (pPrimeCoreOf 2 K))
    (hrank : oBound 2 ≤ pRank 2 ↥(centralizer ({u} : Set G))) :
    ∃ Λ : Subgroup G, IsPCompIn 2 (centralizer ({x} : Set G) ⊓ centralizer ({u} : Set G)) Λ ∧
      Λ ≤ K ∧ (∀ z ∈ K ⊓ centralizer ({u} : Set G), (∃ n : ℕ, z ^ 2 ^ n = 1) → z ∈ Λ) ∧
      IsComponent ((Λ.subgroupOf (centralizer ({u} : Set G))).map
        (barMk ↥(centralizer ({u} : Set G)))) := by
  obtain ⟨hKILo, hterm1, -⟩ := hterm
  have hxo : orderOf x = 2 := hKILo.1
  have hKc : IsPCompIn 2 (centralizer ({x} : Set G)) K := hKILo.2.2
  obtain ⟨Λ, hΛX, hΛlay, hΛpc, hΛuniq, hΛW, h2el, hcovΛ⟩ := pumpup_cover hu2 hKc huK
  have hxY : x ∈ centralizer ({u} : Set G) := mem_centralizer_symm hux
  set Y' := centralizer ({u} : Set G) with hY'
  have hso : orderOf (⟨x, hxY⟩ : ↥Y') = 2 := orderOf_mk_centralizer hxY hxo
  have hΛC := le_centralizer_mk (isPCompIn_two_iff.mp hΛW).1 hxY
  have hΛ2 := isTwoComponent_centralizer_mk hΛW hxY
  obtain ⟨hΛE, hJsub, L, hL, hcases, hLJ, hLsJ, hiff⟩ := pumpupY_structure hso hΛC hΛ2
  have hΛK : Λ ≤ K := hΛX.trans inf_le_left
  have hΛY : Λ ≤ Y' := hΛX.trans inf_le_right
  obtain ⟨φ, hφs, hφo, hφρ⟩ := exists_phi hΛK hΛY hcovΛ
  have hL2 : TwoComponents.IsTwoComponent L :=
    TwoLayerTransport.ordinary_isTwoComponent_of_corefree oddCore_barQ L
      ((CFSG.isComponent_iff_open L).mp hL)
  obtain ⟨M, hM2, hML⟩ := OddKernelTwoComponents.exists_lift (barMk ↥Y') barMk_surjective
    odd_card_ker_barMk L hL2
  have hMJ : M ≤ pumpupY (Λ.subgroupOf Y') := (hiff M hM2).mpr (Or.inl hML)
  set MG : Subgroup G := M.map Y'.subtype with hMG
  have hMGY : MG ≤ Y' := Subgroup.map_subtype_le M
  have hMGsub : MG.subgroupOf Y' = M :=
    Subgroup.comap_map_eq_self_of_injective Y'.subtype_injective M
  have hMG2 : TwoComponents.IsTwoComponent (MG.subgroupOf Y') := by
    rw [hMGsub]
    exact hM2
  have hJ : pumpUp 2 K u = (pumpupY (Λ.subgroupOf Y')).map Y'.subtype := by
    rw [pumpUp_eq_map_pumpupY, hΛlay]
  have hMGJ : MG ≤ pumpUp 2 K u := by
    rw [hJ]
    exact Subgroup.map_mono hMJ
  have hpumpPC : IsPCompIn 2 (pumpUp 2 K u) MG :=
    ⟨hMGJ, (CatalogueBAlternating.pComponent_two_iff _).mpr
      (TwoComponentTransport.restrict_nested MG (pumpUp 2 K u) Y' hMGJ
        (pumpUp_le_centralizer K u) hMG2)⟩
  have hILo : IsILo 2 u MG := ⟨hu2, hrank, isPCompIn_two_iff.mpr ⟨hMGY, hMG2⟩⟩
  have hlt : PumpUpLT 2 x K u MG := ⟨hKILo, hILo, hux, huK, hpumpPC⟩
  obtain ⟨hxN, ⟨e⟩⟩ := hterm1 u MG hlt
  have hMGL : (MG.subgroupOf Y').map (barMk ↥Y') = L := by
    rw [hMGsub]
    exact hML
  have hLinv : conjSub (barMk ↥Y' ⟨x, hxY⟩)⁻¹ L = L := by
    rw [← hMGL]
    exact conjSub_barMk_eq_of_mem_normalizer hxY hxN
  have hvert : (Λ.subgroupOf Y').map (barMk ↥Y') ≤ L :=
    (hcases.resolve_right fun h => h.1 hLinv).2
  obtain ⟨e1⟩ := hat_equiv_subgroupOf hMGY
  have hMGsubn : (MG.subgroupOf Y').IsSubnormal := by
    rw [hMGsub]
    exact Components.mathlib_subnormal_of_chain hM2.1 Subgroup.IsSubnormal.top
  obtain ⟨e2⟩ := hat_equiv_map hMGsubn
  have hcardMG : Nat.card (↥MG ⧸ pPrimeCore 2 ↥MG) = Nat.card ↥L := by
    rw [Nat.card_congr (e1.trans e2).toEquiv]
    exact Nat.card_congr (MulEquiv.subgroupCongr hMGL).toEquiv
  have hKI : Nat.card (↥K ⧸ pPrimeCore 2 ↥K) ≤
      Nat.card ↥((Λ.subgroupOf Y').map (barMk ↥Y')) := Nat.card_le_card_of_surjective φ hφs
  have hMGK : Nat.card (↥MG ⧸ pPrimeCore 2 ↥MG) = Nat.card (↥K ⧸ pPrimeCore 2 ↥K) :=
    Nat.card_congr e.toEquiv
  have hIL : (Λ.subgroupOf Y').map (barMk ↥Y') = L :=
    Subgroup.eq_of_le_of_card_ge hvert (by omega)
  refine ⟨Λ, hΛW, hΛK, h2el, ?_⟩
  rw [hIL]
  exact hL




theorem isPComponent_two_of_isComponent' {X : Type} [Group X] [Finite X] {L : Subgroup X}
    (hL : IsComponent L) : IsPComponent 2 L := by
  refine CFSG.LocalAnalysis.ComponentInitial.isPComponent_of_isComponent_of_not_le 2 hL ?_
  intro hle
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : Odd (Nat.card ↥(pPrimeCore 2 X)) :=
    Nat.coprime_two_left.1 (pPrimeCore_coprime_card (p := 2) (G := X))
  exact CFSG.LocalAnalysis.ComponentInitial.not_le_of_isComponent_of_isSolvable hL
    (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd) hle

theorem quotient_equiv_of_odd_ker {A B : Type*} [Group A] [Group B] [Finite A] (f : A →* B)
    (hs : Function.Surjective f) (hk : ¬ 2 ∣ Nat.card f.ker) (hB : pPrimeCore 2 B = ⊥) :
    Nonempty ((A ⧸ pPrimeCore 2 A) ≃* B) := by
  have : Finite B := Finite.of_surjective f hs
  have hker : f.ker = pPrimeCore 2 A := by
    apply le_antisymm
    · exact le_sSup ⟨inferInstance, Nat.coprime_two_left.mpr
        (Nat.odd_iff.mpr (Nat.mod_two_ne_zero.mp fun h => hk (Nat.dvd_of_mod_eq_zero h)))⟩
    · exact normal_odd_le_ker f hs hB _ (odd_card_pPrimeCore A)
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hs)⟩

theorem exists_J₂ {M Y : Subgroup G} (hYM : Y ≤ M) {J : Subgroup (barQ ↥M)} (hJ : IsComponent J)
    (hJY : ∀ j ∈ J, ∃ (y : G) (hy : y ∈ Y), barMk ↥M ⟨y, hYM hy⟩ = j) :
    ∃ J₂ : Subgroup G, IsPCompIn 2 Y J₂ ∧
      (∀ (j : G) (hj : j ∈ M), j ∈ J₂ → barMk ↥M ⟨j, hj⟩ ∈ J) ∧
      (∀ (z : G) (hz : z ∈ Y), barMk ↥M ⟨z, hYM hz⟩ ∈ J →
        (∃ n : ℕ, z ^ 2 ^ n = 1) → z ∈ J₂) ∧
      Nonempty ((↥J₂ ⧸ pPrimeCore 2 ↥J₂) ≃* ↥J) := by
  let φ : ↥Y →* barQ ↥M := (QuotientGroup.mk' (pPrimeCore 2 ↥M)).comp (Subgroup.inclusion hYM)
  have hker : ¬ 2 ∣ Nat.card φ.ker :=
    B1.not_two_dvd_card_ker_comp_mk (Subgroup.inclusion hYM) (Subgroup.inclusion_injective hYM)
      (pPrimeCore 2 ↥M) (Nat.coprime_two_left.mp pPrimeCore_coprime_card)
  have hJR : J ≤ φ.range := by
    intro j hj
    obtain ⟨y, hy, rfl⟩ := hJY j hj
    exact ⟨⟨y, hy⟩, rfl⟩
  have hJ2 : TwoComponents.IsTwoComponent J :=
    (CatalogueBAlternating.pComponent_two_iff J).mp (isPComponent_two_of_isComponent' hJ)
  have hJb : IsPCompIn 2 φ.range J :=
    isPCompIn_two_iff.mpr ⟨hJR, TwoComponentTransport.of_overgroup hJ2 hJR⟩
  obtain ⟨hJ₂c, hJ₂map⟩ := B1.exists_isPCompIn_lift_of_odd_ker φ hker hJb
  set J₂ : Subgroup G := oPrimeResidualOf 2 ((J.comap φ).map Y.subtype) with hJ₂
  have hJ₂Y : J₂ ≤ Y := hJ₂c.1
  have hJ₂M : J₂ ≤ M := hJ₂Y.trans hYM
  have hmemJ : ∀ (j : G) (hj : j ∈ J₂), barMk ↥M ⟨j, hJ₂M hj⟩ ∈ J := by
    intro j hj
    have hj' : (⟨j, hJ₂Y hj⟩ : ↥Y) ∈ J₂.subgroupOf Y := hj
    have : φ ⟨j, hJ₂Y hj⟩ ∈ (J₂.subgroupOf Y).map φ := ⟨_, hj', rfl⟩
    rw [hJ₂map] at this
    exact this
  refine ⟨J₂, hJ₂c, fun j hj hjJ => hmemJ j hjJ, ?_, ?_⟩
  · intro z hz hzJ h2
    have hzP : z ∈ (J.comap φ).map Y.subtype := ⟨⟨z, hz⟩, hzJ, rfl⟩
    exact Balance.mem_oPrimeResidualOf_of_two_element hzP h2
  · let f : ↥J₂ →* ↥J :=
      ((QuotientGroup.mk' (pPrimeCore 2 ↥M)).comp (Subgroup.inclusion hJ₂M)).codRestrict J
        (fun j => hmemJ j.1 j.2)
    have hfs : Function.Surjective f := by
      rintro ⟨v, hv⟩
      have : v ∈ (J₂.subgroupOf Y).map φ := by rw [hJ₂map]; exact hv
      obtain ⟨y, hy, hyv⟩ := this
      exact ⟨⟨y.1, hy⟩, Subtype.ext hyv⟩
    have hfk : ¬ 2 ∣ Nat.card f.ker := by
      have hkerf : f.ker = ((QuotientGroup.mk' (pPrimeCore 2 ↥M)).comp
          (Subgroup.inclusion hJ₂M)).ker := MonoidHom.ker_codRestrict _ _ _
      rw [hkerf]
      exact B1.not_two_dvd_card_ker_comp_mk (Subgroup.inclusion hJ₂M)
        (Subgroup.inclusion_injective hJ₂M) (pPrimeCore 2 ↥M)
        (Nat.coprime_two_left.mp pPrimeCore_coprime_card)
    have hJcore : pPrimeCore 2 ↥J = ⊥ := by
      rw [CatalogueBAlternating.primeCore_two_eq_oddCore (G := ↥J)]
      exact OddCore.subnormal_corefree oddCore_barQ J (Components.chain_of_mathlib_subnormal hJ.2)
    exact quotient_equiv_of_odd_ker f hfs hfk hJcore


omit [Finite G] in
theorem le_normalizer_pPrimeCoreOf' (M : Subgroup G) : M ≤ normalizer (pPrimeCoreOf 2 M : Set G) := by
  have hnormal : (pPrimeCore 2 ↥M).Normal := pPrimeCore_normal
  have key : ∀ m ∈ M, ∀ n ∈ pPrimeCoreOf 2 M, m * n * m⁻¹ ∈ pPrimeCoreOf 2 M := by
    intro m hm n hn
    obtain ⟨n0, hn0, rfl⟩ := Subgroup.mem_map.1 hn
    exact Subgroup.mem_map.2 ⟨⟨m, hm⟩ * n0 * ⟨m, hm⟩⁻¹, hnormal.conj_mem n0 hn0 ⟨m, hm⟩, by simp⟩
  intro m hm
  rw [Subgroup.mem_normalizer_iff]
  intro n
  exact ⟨fun hn => key m hm n hn, fun hn => by
    have := key m⁻¹ (inv_mem hm) _ hn
    simpa [mul_assoc] using this⟩

theorem odd_card_pPrimeCoreOf' (M : Subgroup G) : Odd (Nat.card ↥(pPrimeCoreOf 2 M)) := by
  rw [pPrimeCoreOf, Subgroup.card_map_of_injective M.subtype_injective]
  exact Nat.coprime_two_left.1 pPrimeCore_coprime_card

omit [Finite G] in
theorem commutator_mem_pPrimeCoreOf {M : Subgroup G} {j l : G} (hj : j ∈ M) (hl : l ∈ M)
    (h : barMk ↥M ⟨j, hj⟩ * barMk ↥M ⟨l, hl⟩ = barMk ↥M ⟨l, hl⟩ * barMk ↥M ⟨j, hj⟩) :
    ⁅j, l⁆ ∈ pPrimeCoreOf 2 M := by
  have hc : ⁅j, l⁆ ∈ M := by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hj hl) (inv_mem hj)) (inv_mem hl)
  have h1 : barMk ↥M ⟨⁅j, l⁆, hc⟩ = 1 := by
    have h3 : (⟨⁅j, l⁆, hc⟩ : ↥M) = ⁅(⟨j, hj⟩ : ↥M), (⟨l, hl⟩ : ↥M)⁆ := rfl
    rw [h3, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact h
  have h2 : (⟨⁅j, l⁆, hc⟩ : ↥M) ∈ pPrimeCore 2 ↥M := (QuotientGroup.eq_one_iff _).mp h1
  exact Subgroup.mem_map.2 ⟨_, h2, rfl⟩

theorem exists_odd_normalized {M H Λ J₂ : Subgroup G} (hΛM : Λ ≤ M)
    (hcomm : ∀ (j : G) (hj : j ∈ M), j ∈ J₂ → ∀ (l : G) (hl : l ∈ M), l ∈ Λ →
      barMk ↥M ⟨j, hj⟩ * barMk ↥M ⟨l, hl⟩ = barMk ↥M ⟨l, hl⟩ * barMk ↥M ⟨j, hj⟩)
    (hJ₂M : J₂ ≤ M) :
    ∃ N : Subgroup (barQ ↥H), ¬ 2 ∣ Nat.card ↥N ∧
      (∀ l ∈ (Λ.subgroupOf H).map (barMk ↥H), ∀ n ∈ N, l * n * l⁻¹ ∈ N) ∧
      ∀ (j : G) (hj : j ∈ H), j ∈ J₂ → ∀ l ∈ (Λ.subgroupOf H).map (barMk ↥H),
        ⁅barMk ↥H ⟨j, hj⟩, l⁆ ∈ N := by
  set S : Subgroup ↥H := (pPrimeCoreOf 2 M).subgroupOf H with hS
  refine ⟨S.map (barMk ↥H), ?_, ?_, ?_⟩
  · intro h2
    have hodd : Odd (Nat.card ↥(pPrimeCoreOf 2 M)) := odd_card_pPrimeCoreOf' M
    let f : ↥S →* ↥(pPrimeCoreOf 2 M) := ((H.subtype).comp S.subtype).codRestrict _ (fun x => x.2)
    have hf : Function.Injective f := by
      intro a b hab
      have h1 : ((a : ↥H) : G) = ((b : ↥H) : G) :=
        congrArg (fun z : ↥(pPrimeCoreOf 2 M) => (z : G)) hab
      exact Subtype.ext (Subtype.ext h1)
    have h3 : Nat.card ↥S ∣ Nat.card ↥(pPrimeCoreOf 2 M) := Subgroup.card_dvd_of_injective f hf
    have h4 : Nat.card ↥(S.map (barMk ↥H)) ∣ Nat.card ↥S := Subgroup.card_map_dvd S (barMk ↥H)
    have h5 : 2 ∣ Nat.card ↥(pPrimeCoreOf 2 M) := h2.trans (h4.trans h3)
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h5)
  · rintro _ ⟨l, hl, rfl⟩ _ ⟨n, hn, rfl⟩
    refine ⟨l * n * l⁻¹, ?_, by simp⟩
    have hl' : (l : G) ∈ Λ := Subgroup.mem_subgroupOf.mp hl
    have hn' : (n : G) ∈ pPrimeCoreOf 2 M := Subgroup.mem_subgroupOf.mp hn
    exact Subgroup.mem_subgroupOf.mpr (by
      have := le_normalizer_pPrimeCoreOf' M (hΛM hl')
      have h := (Subgroup.mem_normalizer_iff.mp this (n : G)).mp hn'
      simpa using h)
  · rintro j hj hjJ _ ⟨l, hl, rfl⟩
    refine ⟨⁅(⟨j, hj⟩ : ↥H), l⁆, ?_, by simp [map_commutatorElement]⟩
    have hl' : (l : G) ∈ Λ := Subgroup.mem_subgroupOf.mp hl
    exact Subgroup.mem_subgroupOf.mpr (commutator_mem_pPrimeCoreOf (hJ₂M hjJ) (hΛM hl')
      (hcomm j (hJ₂M hjJ) hjJ l (hΛM hl') hl'))

theorem le_image_centralizer_of_comm {M T : Subgroup G} (hTM : T ≤ M) (hT2 : IsPGroup 2 ↥T)
    {J : Subgroup (barQ ↥M)}
    (hJT : ∀ (t : G) (ht : t ∈ T), ∀ j ∈ J,
      barMk ↥M ⟨t, hTM ht⟩ * j = j * barMk ↥M ⟨t, hTM ht⟩) :
    ∀ j ∈ J, ∃ (y : G) (hy : y ∈ M ⊓ centralizer (T : Set G)), barMk ↥M ⟨y, hy.1⟩ = j := by
  intro j hj
  have h1 := B1.map_centralizer_eq_centralizer_map_of_isPGroup (pPrimeCore 2 ↥M)
    (Nat.coprime_two_left.mp pPrimeCore_coprime_card) (A := T.subgroupOf M) hT2.comap_subtype
  have h1' : (centralizer ((T.subgroupOf M : Subgroup ↥M) : Set ↥M)).map (barMk ↥M) =
      centralizer (((T.subgroupOf M).map (barMk ↥M) : Subgroup (barQ ↥M)) : Set (barQ ↥M)) := h1
  have hjc : j ∈ centralizer (((T.subgroupOf M).map (barMk ↥M) : Subgroup (barQ ↥M)) :
      Set (barQ ↥M)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨a, ha, rfl⟩
    exact hJT (a : G) (Subgroup.mem_subgroupOf.mp ha) j hj
  rw [← h1'] at hjc
  obtain ⟨y₀, hy₀, rfl⟩ := hjc
  refine ⟨(y₀ : G), Subgroup.mem_inf.mpr ⟨y₀.2, ?_⟩, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  have := Subgroup.mem_centralizer_iff.mp hy₀ ⟨t, hTM ht⟩ (Subgroup.mem_subgroupOf.mpr ht)
  exact congrArg Subtype.val this

theorem exists_lift_component {H : Subgroup G} {D : Subgroup (barQ ↥H)} (hD : IsComponent D) {u : G}
    (hu : u ∈ H) (hu2 : ∃ n : ℕ, u ^ 2 ^ n = 1) (huD : barMk ↥H ⟨u, hu⟩ ∈ D) :
    ∃ I : Subgroup G, IsPCompIn 2 H I ∧ u ∈ I ∧ Nonempty ((↥I ⧸ pPrimeCore 2 ↥I) ≃* ↥D) := by
  let φ : ↥H →* barQ ↥H := barMk ↥H
  have hker : ¬ 2 ∣ Nat.card φ.ker := by
    have := odd_card_ker_barMk (Y := ↥H)
    intro h2
    exact (Nat.not_even_iff_odd.mpr this) (even_iff_two_dvd.mpr h2)
  have hDR : D ≤ φ.range := by
    intro d _
    obtain ⟨y, rfl⟩ := barMk_surjective (Y := ↥H) d
    exact ⟨y, rfl⟩
  have hD2 : TwoComponents.IsTwoComponent D :=
    (CatalogueBAlternating.pComponent_two_iff D).mp (isPComponent_two_of_isComponent' hD)
  have hDb : IsPCompIn 2 φ.range D :=
    isPCompIn_two_iff.mpr ⟨hDR, TwoComponentTransport.of_overgroup hD2 hDR⟩
  obtain ⟨hIc, hImap⟩ := B1.exists_isPCompIn_lift_of_odd_ker φ hker hDb
  set I : Subgroup G := oPrimeResidualOf 2 ((D.comap φ).map H.subtype) with hI
  have hIH : I ≤ H := hIc.1
  refine ⟨I, hIc, Balance.mem_oPrimeResidualOf_of_two_element ⟨⟨u, hu⟩, huD, rfl⟩ hu2, ?_⟩
  have hmemD : ∀ (i : G) (hi : i ∈ I), barMk ↥H ⟨i, hIH hi⟩ ∈ D := by
    intro i hi
    have hi' : (⟨i, hIH hi⟩ : ↥H) ∈ I.subgroupOf H := hi
    have : φ ⟨i, hIH hi⟩ ∈ (I.subgroupOf H).map φ := ⟨_, hi', rfl⟩
    rw [hImap] at this
    exact this
  let f : ↥I →* ↥D :=
    ((barMk ↥H).comp (Subgroup.inclusion hIH)).codRestrict D (fun i => hmemD i.1 i.2)
  have hfs : Function.Surjective f := by
    rintro ⟨v, hv⟩
    have : v ∈ (I.subgroupOf H).map φ := by rw [hImap]; exact hv
    obtain ⟨y, hy, hyv⟩ := this
    exact ⟨⟨y.1, hy⟩, Subtype.ext hyv⟩
  have hfk : ¬ 2 ∣ Nat.card f.ker := by
    have hkerf : f.ker = ((barMk ↥H).comp (Subgroup.inclusion hIH)).ker :=
      MonoidHom.ker_codRestrict _ _ _
    rw [hkerf]
    exact B1.not_two_dvd_card_ker_comp_mk (Subgroup.inclusion hIH)
      (Subgroup.inclusion_injective hIH) (pPrimeCore 2 ↥H)
      (Nat.coprime_two_left.mp pPrimeCore_coprime_card)
  have hDcore : pPrimeCore 2 ↥D = ⊥ := by
    rw [CatalogueBAlternating.primeCore_two_eq_oddCore (G := ↥D)]
    exact OddCore.subnormal_corefree oddCore_barQ D (Components.chain_of_mathlib_subnormal hD.2)
  exact quotient_equiv_of_odd_ker f hfs hfk hDcore

theorem equiv_image_of_equiv {H J₂ : Subgroup G} (hJ₂H : J₂ ≤ H)
    (hD : IsComponent ((J₂.subgroupOf H).map (barMk ↥H))) {J : Type*} [Group J]
    (e : (↥J₂ ⧸ pPrimeCore 2 ↥J₂) ≃* J) :
    Nonempty (↥((J₂.subgroupOf H).map (barMk ↥H)) ≃* J) := by
  set D : Subgroup (barQ ↥H) := (J₂.subgroupOf H).map (barMk ↥H) with hDdef
  have hmemD : ∀ (j : G) (hj : j ∈ J₂), barMk ↥H ⟨j, hJ₂H hj⟩ ∈ D := fun j hj =>
    ⟨⟨j, hJ₂H hj⟩, hj, rfl⟩
  let f : ↥J₂ →* ↥D :=
    ((barMk ↥H).comp (Subgroup.inclusion hJ₂H)).codRestrict D (fun j => hmemD j.1 j.2)
  have hfs : Function.Surjective f := by
    rintro ⟨v, y, hy, rfl⟩
    exact ⟨⟨y.1, hy⟩, rfl⟩
  have hfk : ¬ 2 ∣ Nat.card f.ker := by
    have hkerf : f.ker = ((barMk ↥H).comp (Subgroup.inclusion hJ₂H)).ker :=
      MonoidHom.ker_codRestrict _ _ _
    rw [hkerf]
    exact B1.not_two_dvd_card_ker_comp_mk (Subgroup.inclusion hJ₂H)
      (Subgroup.inclusion_injective hJ₂H) (pPrimeCore 2 ↥H)
      (Nat.coprime_two_left.mp pPrimeCore_coprime_card)
  have hDcore : pPrimeCore 2 ↥D = ⊥ := by
    rw [CatalogueBAlternating.primeCore_two_eq_oddCore (G := ↥D)]
    exact OddCore.subnormal_corefree oddCore_barQ D (Components.chain_of_mathlib_subnormal hD.2)
  obtain ⟨e'⟩ := quotient_equiv_of_odd_ker f hfs hfk hDcore
  exact ⟨e'.symm.trans e⟩

end CFSG.GH74.Generic.BProg.B2.SD.TwoA7Geo
