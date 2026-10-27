module

public import CFSG.ClassicalInvolution.Q3.Q3AMBadPsp
public import CFSG.ClassicalInvolution.Q3.Q3AMBadLayer
public import CFSG.ClassicalInvolution.Q3.Q3CHLayer

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.Q3T8.Asc77 CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Q3.Q3CP CFSG.ClassicalInvolution.Q3.Q3CH
open scoped MatrixGroups commutatorElement

section Nbhd


variable {G : Type} [Group G] [Finite G]

abbrev nbrLayer (Ω : Set (Subgroup G)) (M : Subgroup G) (a : G) : Subgroup G :=
  centralizingLayer (nbrCoreFam Ω M a) {a}

theorem exactCore3_le_nbrLayer {Ω : Set (Subgroup G)} {M N : Subgroup G} {a : G}
    (hN : N ∈ omegaNbr Ω M) : exactCore3 a N ≤ nbrLayer Ω M a :=
  le_centralizingLayer ⟨⟨N, hN, rfl⟩, exactCore3_le_centralizer a N⟩

theorem nbrLayer_le_centralizer (Ω : Set (Subgroup G)) (M : Subgroup G) (a : G) :
    nbrLayer Ω M a ≤ Subgroup.centralizer ({a} : Set G) :=
  centralizingLayer_le_centralizer _ _

theorem conjSub_mem_omegaNbr_of_conjSub_eq {Ω : Set (Subgroup G)} (hΩ : HypOmegaMod Ω)
    {M J' : Subgroup G} {b : G} (hb : conjSub b M = M) (hJ' : J' ∈ omegaNbr Ω M) :
    conjSub b J' ∈ omegaNbr Ω M := by
  obtain ⟨hJΩ, hJK, R', hR', hR'J, hR'N⟩ := hJ'
  have hbN : b ∈ Subgroup.normalizer (M : Set G) := mem_normalizer_iff_conjSub_eq.mpr hb
  refine ⟨hΩ.conjInvariant b J' hJΩ, ?_, conjSub b R', Q3.Q3CL.Thompson.conjSub_mem_RSet hΩ hR' b,
    conjSub_mono hR'J, ?_⟩
  · intro h
    apply hJK
    have h2 : conjSub b⁻¹ (conjSub b J') = conjSub b⁻¹ M := by rw [h]
    rw [conjSub_inv_conjSub] at h2
    calc J' = conjSub b⁻¹ M := h2
      _ = conjSub b⁻¹ (conjSub b M) := by rw [hb]
      _ = M := conjSub_inv_conjSub b M
  · intro x hx
    rw [mem_conjSub_iff] at hx
    have hy := hR'N hx
    have e : x = b * (b⁻¹ * x * b) * b⁻¹ := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hbN hy) (Subgroup.inv_mem _ hbN)

theorem conj_mem_nbrLayer {Ω : Set (Subgroup G)} (hΩ : HypOmegaMod Ω)
    {M : Subgroup G} {a : G}
    (hCM : ∀ g ∈ Subgroup.centralizer ({a} : Set G), conjSub g M = M) {g : G}
    (hg : g ∈ Subgroup.centralizer ({a} : Set G)) {y : G} (hy : y ∈ nbrLayer Ω M a) :
    g * y * g⁻¹ ∈ nbrLayer Ω M a := by
  have hle : conjSub g (nbrLayer Ω M a) ≤ nbrLayer Ω M a := by
    show (nbrLayer Ω M a).map (MulAut.conj g).toMonoidHom ≤ nbrLayer Ω M a
    rw [Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun L hL => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    obtain ⟨⟨N, hN, rfl⟩, -⟩ := hL
    have h := exactCore3_conjSub g a N
    rw [conj_eq_of_mem_centralizer_singleton hg] at h
    show conjSub g (exactCore3 a N) ≤ _
    rw [← h]
    exact exactCore3_le_nbrLayer (conjSub_mem_omegaNbr_of_conjSub_eq hΩ (hCM g hg) hN)
  exact hle (Subgroup.mem_map.mpr ⟨y, hy, rfl⟩)

theorem conj_mem_oddCoreOf_of_mem_self {Y : Subgroup G} {y o : G} (hy : y ∈ Y)
    (ho : o ∈ oddCoreOf Y) : y * o * y⁻¹ ∈ oddCoreOf Y :=
  conj_mem_oddCoreOf_of_mem_normalizer (fun _ hx => Y.mul_mem (Y.mul_mem hy hx) (Y.inv_mem hy))
    (fun _ hx => Y.mul_mem (Y.mul_mem (Y.inv_mem hy) hx) hy) ho

theorem mem_of_conjSub_eq {M : Subgroup G} {g : G} (h : conjSub g M = M) {x : G} (hx : x ∈ M) :
    g * x * g⁻¹ ∈ M := by
  have : g * x * g⁻¹ ∈ conjSub g M := Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  rwa [h] at this

theorem commutator_oddCore_mem_oddCoreOf_layer {M Y : Subgroup G} {a : G}
    (hMa : M ≤ Subgroup.centralizer ({a} : Set G)) (hYa : Y ≤ Subgroup.centralizer ({a} : Set G))
    (hCM : ∀ g ∈ Subgroup.centralizer ({a} : Set G), conjSub g M = M)
    (hCY : ∀ g ∈ Subgroup.centralizer ({a} : Set G), ∀ y ∈ Y, g * y * g⁻¹ ∈ Y) {u y : G}
    (hu : u ∈ oddCoreOf M) (hy : y ∈ Y) : ⁅u, y⁆ ∈ oddCoreOf Y := by
  have hOn : ∀ g ∈ Subgroup.centralizer ({a} : Set G), ∀ o ∈ oddCoreOf M,
      g * o * g⁻¹ ∈ oddCoreOf M := fun g hg o ho =>
    conj_mem_oddCoreOf_of_mem_normalizer (fun _ hx => mem_of_conjSub_eq (hCM g hg) hx)
      (fun _ hx => by
        simpa using mem_of_conjSub_eq (hCM g⁻¹ (Subgroup.inv_mem _ hg)) hx) ho
  have huM : u ∈ M := oddCoreOf_le_self M hu
  have h1 : y * u⁻¹ * y⁻¹ ∈ oddCoreOf M :=
    hOn y (hYa hy) u⁻¹ ((oddCoreOf M).inv_mem hu)
  have hm1 : ⁅u, y⁆ ∈ oddCoreOf M := by
    have e : ⁅u, y⁆ = u * (y * u⁻¹ * y⁻¹) := by rw [commutatorElement_def]; group
    rw [e]
    exact (oddCoreOf M).mul_mem hu h1
  have hm2 : ⁅u, y⁆ ∈ Y := by
    have e : ⁅u, y⁆ = (u * y * u⁻¹) * y⁻¹ := by rw [commutatorElement_def]
    rw [e]
    exact Y.mul_mem (hCY u (hMa huM) y hy) (Y.inv_mem hy)
  exact inf_le_oddCoreOf_of_normalized (oddCoreOf_odd_natCard M)
    (fun y' hy' x hx => hOn y' (hYa hy') x hx) ⟨hm1, hm2⟩

theorem oddCoreOf_le_of_card_image {Y L : Subgroup G} (hLY : L ≤ Y)
    (hcard : Nat.card ↥(Subgroup.map (QuotientGroup.mk' (classicalInvolutionOddCore ↥Y))
      (L.subgroupOf Y)) = 24)
    (hL : Nonempty (↥L ⧸ classicalInvolutionOddCore ↥L ≃* SL(2, ZMod 3))) :
    oddCoreOf L ≤ oddCoreOf Y := by
  classical
  obtain ⟨e⟩ := hL
  let π := QuotientGroup.mk' (classicalInvolutionOddCore ↥Y)
  let φ : ↥L →* (↥Y ⧸ classicalInvolutionOddCore ↥Y) := π.comp (Subgroup.inclusion hLY)
  have hrange : φ.range = Subgroup.map π (L.subgroupOf Y) := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
  have hkodd : Odd (Nat.card φ.ker) := by
    have hle : φ.ker.map L.subtype ≤ oddCoreOf Y := by
      rintro _ ⟨x, hx, rfl⟩
      have h1 : π (Subgroup.inclusion hLY x) = 1 := MonoidHom.mem_ker.mp hx
      have h2 := (QuotientGroup.ker_mk' _).le (MonoidHom.mem_ker.mpr h1)
      exact mem_oddCoreOf_iff.mpr ⟨hLY x.2, h2⟩
    have hc : Nat.card (φ.ker.map L.subtype) = Nat.card φ.ker :=
      Subgroup.card_map_of_injective (Subgroup.subtype_injective _)
    rw [← hc]
    exact (oddCoreOf_odd_natCard Y).of_dvd_nat (Subgroup.card_dvd_of_le hle)
  have hker_le : φ.ker ≤ classicalInvolutionOddCore ↥L :=
    CFSG.ComponentClassification.OddCore.maximal ↥L φ.ker φ.normal_ker hkodd
  have hidx1 : φ.ker.index = 24 := by
    rw [Subgroup.index_eq_card, Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv,
      hrange]
    exact hcard
  have hidx2 : (classicalInvolutionOddCore ↥L).index = 24 := by
    rw [Subgroup.index_eq_card, Nat.card_congr e.toEquiv]
    exact natCard_sl2Three
  have h3 : Nat.card φ.ker = Nat.card (classicalInvolutionOddCore ↥L) := by
    have a1 := Subgroup.card_mul_index φ.ker
    have a2 := Subgroup.card_mul_index (classicalInvolutionOddCore ↥L)
    rw [hidx1] at a1
    rw [hidx2] at a2
    omega
  have heq : φ.ker = classicalInvolutionOddCore ↥L :=
    Subgroup.eq_of_le_of_card_ge hker_le (le_of_eq h3.symm)
  intro u hu
  obtain ⟨hu1, hu2⟩ := mem_oddCoreOf_iff.mp hu
  have hmem : (⟨u, hu1⟩ : ↥L) ∈ φ.ker := by
    rw [heq]
    exact hu2
  have h1 : π (Subgroup.inclusion hLY ⟨u, hu1⟩) = 1 := MonoidHom.mem_ker.mp hmem
  exact mem_oddCoreOf_iff.mpr ⟨hLY hu1, (QuotientGroup.eq_one_iff _).mp h1⟩

theorem nbrExact_of_lieSystem {Ω : Set (Subgroup G)} {M : Subgroup G} {a : G} {ι : Type}
    (D : LieSystemData3 ι (↥(nbrLayer Ω M a) ⧸ classicalInvolutionOddCore ↥(nbrLayer Ω M a))
      (oddQuotientFamily (restrictFamily (centralizingMembers (nbrCoreFam Ω M a) {a})
        (nbrLayer Ω M a))))
    {N : Subgroup G} (hN : N ∈ omegaNbr Ω M) :
    Nat.card ↥(Subgroup.map (QuotientGroup.mk' (classicalInvolutionOddCore ↥(nbrLayer Ω M a)))
      ((exactCore3 a N).subgroupOf (nbrLayer Ω M a))) = 24 := by
  apply D.card_eq
  exact ⟨(exactCore3 a N).subgroupOf (nbrLayer Ω M a), ⟨exactCore3 a N,
    ⟨⟨N, hN, rfl⟩, exactCore3_le_centralizer a N⟩, exactCore3_le_nbrLayer hN, rfl⟩, rfl⟩


theorem commutator_centM_mem_oddCoreOf_layer [IsSimpleGroup G] {K : Subgroup G} {z : G}
    {M N : Subgroup G} {a b : G} (he : EdgeSetup K z M N a b) (hnab : ∃ x y : G, x * y ≠ y * x)
    (hBelow : Q3.CIT3Below (Nat.card G)) {Y : Subgroup G} (hY : exactCore3 a N ≤ Y)
    (hcard : Nat.card ↥(Subgroup.map (QuotientGroup.mk' (classicalInvolutionOddCore ↥Y))
      ((exactCore3 a N).subgroupOf Y)) = 24) {c x : G}
    (hc : c ∈ M ⊓ Subgroup.centralizer ({b} : Set G)) (hx : x ∈ exactCore3 a N) :
    ⁅c, x⁆ ∈ oddCoreOf Y := by
  have hMa : M ≤ Subgroup.centralizer ({a} : Set G) := isSubnormal_le he.invM.subnormal
  have haM : a ∈ M ⊓ Subgroup.centralizer ({b} : Set G) := by
    obtain ⟨R, R', hp⟩ := he.exists_sylowPair
    refine ⟨he.uniqueM.mem, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    exact (hp.commutes b hp.mem_t a hp.mem_a).symm
  have hc2 : IsPGroup 2 (Subgroup.zpowers a) :=
    isPGroup_zpowers_of_mul_self_eq_one he.uniqueM.sq he.uniqueM.ne_one
  have hcK : a ∈ trivialOnQuot N :=
    ⟨mem_normalizer_iff_conjSub_eq.mpr (he.conjSub_eq_of_mem_centM hnab hBelow a haM),
      fun n hn => he.commutator_centM_le_oddCore hnab hBelow a haM n hn⟩
  have hcN : conjSub c N = N := he.conjSub_eq_of_mem_centM hnab hBelow c hc
  have hcomm : ⁅c, x⁆ ∈ oddCoreOf N := he.commutator_centM_le_oddCore hnab hBelow c hc x hx.1
  have hmem : ⁅c, x⁆ ∈ exactCore3 a N := by
    have e : ⁅c, x⁆ = (c * x * c⁻¹) * x⁻¹ := by rw [commutatorElement_def]
    rw [e]
    have h1 : c * x * c⁻¹ ∈ N := mem_of_conjSub_eq hcN hx.1
    have hca : c ∈ Subgroup.centralizer ({a} : Set G) := hMa hc.1
    have h2 : c * x * c⁻¹ ∈ Subgroup.centralizer ({a} : Set G) :=
      (Subgroup.centralizer ({a} : Set G)).mul_mem
        ((Subgroup.centralizer ({a} : Set G)).mul_mem hca hx.2)
        ((Subgroup.centralizer ({a} : Set G)).inv_mem hca)
    exact ⟨N.mul_mem h1 (N.inv_mem hx.1), (Subgroup.centralizer ({a} : Set G)).mul_mem h2
      ((Subgroup.centralizer ({a} : Set G)).inv_mem hx.2)⟩
  have hO : ⁅c, x⁆ ∈ oddCoreOf (exactCore3 a N) := by
    have h1 : Balance.oddCoreIn (exactCore3 a N) = exactCore3 a N ⊓ Balance.oddCoreIn N :=
      oddCoreIn_exactCore3 he.invN hc2 hcK
    have h2 : ⁅c, x⁆ ∈ Balance.oddCoreIn (exactCore3 a N) := by
      rw [h1]
      exact ⟨hmem, hcomm⟩
    exact h2
  exact oddCoreOf_le_of_card_image hY hcard
    (isSectionMember3_exactCore3 he.invN hc2 hcK).nonempty_equiv hO

theorem commutator_mem_oddCoreOf_nbrLayer [IsSimpleGroup G] {Ω : Set (Subgroup G)}
    {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}
    (h : Q3T8.Asc77.BadStd8 Ω K J S R T W z t) (hint : IsIntrinsicU (.sl2 3 1) K z)
    {M : Subgroup G} {a : G} (hM : M ∈ Ω) (ha : IsUniqueInvolution M a)
    (hex : ∀ N ∈ omegaNbr Ω M, Nat.card ↥(Subgroup.map
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥(nbrLayer Ω M a)))
      ((exactCore3 a N).subgroupOf (nbrLayer Ω M a))) = 24)
    {g : G} (hg : g ∈ M) {y : G} (hy : y ∈ nbrLayer Ω M a) :
    ⁅g, y⁆ ∈ oddCoreOf (nbrLayer Ω M a) := by
  classical
  have hstd := h.std
  have hΩ : HypOmegaMod Ω := hstd.stand.hyp
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hstd.stand.trans hstd.noTwins hM
  have hBelow : Q3.CIT3Below (Nat.card G) :=
    (citBelowT_three_iff (p := 3) (f := 1) (by norm_num) _).mp hstd.stand.below
  have hnab : ∃ x y : G, x * y ≠ y * x := h.nonabelian
  have hMc : IsClassicalMember3 M a :=
    Q3T8.Asc77.isClassicalMember3_of_uniqueInvolution hstd.stand.modU hM ha
  have hMa : M ≤ Subgroup.centralizer ({a} : Set G) := isSubnormal_le hMc.subnormal
  have hCM : ∀ g ∈ Subgroup.centralizer ({a} : Set G), conjSub g M = M := fun g hg =>
    mem_normalizer_iff_conjSub_eq.mp
      (T8.centralizer_le_normalizer_of_noTwins hΩ.conjInvariant hM (hnt M hM) ha hg)
  have hYa : nbrLayer Ω M a ≤ Subgroup.centralizer ({a} : Set G) := nbrLayer_le_centralizer Ω M a
  have hCY : ∀ g ∈ Subgroup.centralizer ({a} : Set G), ∀ y ∈ nbrLayer Ω M a,
      g * y * g⁻¹ ∈ nbrLayer Ω M a := fun g hg y hy => conj_mem_nbrLayer hΩ hCM hg hy
  have hgC : g ∈ Subgroup.centralizer ({a} : Set G) := hMa hg
  let P : Subgroup G :=
    { carrier := {y | y ∈ nbrLayer Ω M a ∧ ⁅g, y⁆ ∈ oddCoreOf (nbrLayer Ω M a)}
      mul_mem' := by
        rintro y y' ⟨hy, hy1⟩ ⟨hy', hy1'⟩
        refine ⟨(nbrLayer Ω M a).mul_mem hy hy', ?_⟩
        have e : ⁅g, y * y'⁆ = ⁅g, y⁆ * (y * ⁅g, y'⁆ * y⁻¹) := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact (oddCoreOf _).mul_mem hy1 (conj_mem_oddCoreOf_of_mem_self hy hy1')
      one_mem' := ⟨(nbrLayer Ω M a).one_mem, by
        have e : ⁅g, (1 : G)⁆ = 1 := by simp [commutatorElement_def]
        rw [e]
        exact (oddCoreOf _).one_mem⟩
      inv_mem' := by
        rintro y ⟨hy, hy1⟩
        refine ⟨(nbrLayer Ω M a).inv_mem hy, ?_⟩
        have e : ⁅g, y⁻¹⁆ = y⁻¹ * ⁅g, y⁆⁻¹ * y⁻¹⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact conj_mem_oddCoreOf_of_mem_self ((nbrLayer Ω M a).inv_mem hy)
          ((oddCoreOf _).inv_mem hy1) }
  have hYP : nbrLayer Ω M a ≤ P := by
    refine iSup₂_le fun L hL x hx => ?_
    obtain ⟨⟨N, hN, rfl⟩, -⟩ := hL
    refine ⟨exactCore3_le_nbrLayer hN hx, ?_⟩
    obtain ⟨b, hb⟩ := hΩ.exists_uniqueInvolution hN.1
    have he := h.toEdgeSetup hint hM hN ha hb
    obtain ⟨c, hc, u, hu, hgcu⟩ := he.exists_mul_centM g hg
    have hcC : c ∈ Subgroup.centralizer ({a} : Set G) := hMa hc.1
    have e : ⁅g, x⁆ = c * ⁅u, x⁆ * c⁻¹ * ⁅c, x⁆ := by
      rw [hgcu]
      simp only [commutatorElement_def]
      group
    rw [e]
    have h1 : ⁅u, x⁆ ∈ oddCoreOf (nbrLayer Ω M a) :=
      commutator_oddCore_mem_oddCoreOf_layer hMa hYa hCM hCY hu (exactCore3_le_nbrLayer hN hx)
    have h2 : c * ⁅u, x⁆ * c⁻¹ ∈ oddCoreOf (nbrLayer Ω M a) :=
      conj_mem_oddCoreOf_of_mem_normalizer (fun y hy => hCY c hcC y hy)
        (fun y hy => by simpa using hCY c⁻¹ (Subgroup.inv_mem _ hcC) y hy) h1
    have h3 : ⁅c, x⁆ ∈ oddCoreOf (nbrLayer Ω M a) :=
      commutator_centM_mem_oddCoreOf_layer he hnab hBelow (exactCore3_le_nbrLayer hN) (hex N hN)
        hc hx
    exact (oddCoreOf _).mul_mem h2 h3
  exact (hYP hy).2

theorem mem_omegaNbr_symm [IsSimpleGroup G] {Ω : Set (Subgroup G)} {K J : Subgroup G}
    {S : Sylow 2 G} {R T W : Subgroup G} {z t : G} (h : Q3T8.Asc77.BadStd8 Ω K J S R T W z t)
    (hint : IsIntrinsicU (.sl2 3 1) K z) {M N : Subgroup G} {a b : G} (hM : M ∈ Ω)
    (hN : N ∈ omegaNbr Ω M) (ha : IsUniqueInvolution M a) (hb : IsUniqueInvolution N b) :
    M ∈ omegaNbr Ω N := by
  have := (h.toEdgeSetup hint hM hN ha hb).symm.nbr
  rwa [← h.eq_conjClass] at this

theorem exists_layer_at_vertex [IsSimpleGroup G] {Ω : Set (Subgroup G)} {K J : Subgroup G}
    {S : Sylow 2 G} {R T W : Subgroup G} {z t : G} (h : Q3T8.Asc77.BadStd8 Ω K J S R T W z t)
    (hint : IsIntrinsicU (.sl2 3 1) K z) {M : Subgroup G} {a : G} (hM : M ∈ Ω)
    (ha : IsUniqueInvolution M a) (hD : PspNbhdSp4 Ω M a) {w t₀ s : G}
    (hw : w ∈ nbrLayer Ω M a) (hww : w * w = a) (ht₀ : t₀ ∈ M) (hs : s = t₀ * w)
    (hsa : s * a = a * s) (hs2 : s * s = 1) :
    ∃ L : Subgroup G, IsSectionMember3 (Subgroup.centralizer ({s} : Set G)) L a := by
  classical
  obtain ⟨ι, hι, D, ha', hS⟩ := hD
  have hstd := h.std
  have hΩ : HypOmegaMod Ω := hstd.stand.hyp
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hstd.stand.trans hstd.noTwins hM
  have hMc : IsClassicalMember3 M a :=
    Q3T8.Asc77.isClassicalMember3_of_uniqueInvolution hstd.stand.modU hM ha
  have hCM : ∀ g ∈ Subgroup.centralizer ({a} : Set G), conjSub g M = M := fun g hg =>
    mem_normalizer_iff_conjSub_eq.mp
      (T8.centralizer_le_normalizer_of_noTwins hΩ.conjInvariant hM (hnt M hM) ha hg)
  have hCY : ∀ g ∈ Subgroup.centralizer ({a} : Set G), ∀ y ∈ nbrLayer Ω M a,
      g * y * g⁻¹ ∈ nbrLayer Ω M a := fun g hg y hy => conj_mem_nbrLayer hΩ hCM hg hy
  have hex : ∀ N ∈ omegaNbr Ω M, Nat.card ↥(Subgroup.map
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥(nbrLayer Ω M a)))
      ((exactCore3 a N).subgroupOf (nbrLayer Ω M a))) = 24 := fun N hN =>
    nbrExact_of_lieSystem D hN
  have hact : ∀ y ∈ nbrLayer Ω M a,
      s * y * s⁻¹ * (w * y * w⁻¹)⁻¹ ∈ oddCoreOf (nbrLayer Ω M a) := by
    intro y hy
    have hwy : w * y * w⁻¹ ∈ nbrLayer Ω M a :=
      (nbrLayer Ω M a).mul_mem ((nbrLayer Ω M a).mul_mem hw hy) ((nbrLayer Ω M a).inv_mem hw)
    have h1 := commutator_mem_oddCoreOf_nbrLayer h hint hM ha hex ht₀ hwy
    have e : s * y * s⁻¹ * (w * y * w⁻¹)⁻¹ = ⁅t₀, w * y * w⁻¹⁆ := by
      rw [hs, commutatorElement_def]
      group
    rwa [e]
  obtain ⟨i₁, hall, hk, f, hf, hfz⟩ := hS
  set π := QuotientGroup.mk' (classicalInvolutionOddCore ↥(nbrLayer Ω M a)) with hπ
  have hne : π ⟨a, ha'⟩ ≠ 1 :=
    Q3Y.mk_ne_one_of_involution (nbrLayer Ω M a) ha' ha.sq ha.ne_one
  have hfz' : D.hom i₁ f = π ⟨a, ha'⟩ := hfz
  have hfne : D.hom i₁ f ≠ 1 := by
    rw [hfz']
    exact hne
  let wY : ↥(nbrLayer Ω M a) := ⟨w, hw⟩
  have hwwY : wY * wY = ⟨a, ha'⟩ := Subtype.ext hww
  have hub : π wY * π wY = D.hom i₁ f := by
    rw [← map_mul, hwwY, hfz']
  have hψs : Function.Surjective (D.hom i₁) :=
    MonoidHom.range_eq_top.mp (range_eq_top_of_forall_eq D hall)
  obtain ⟨Lb, hLc, hLn, hubL, hLiso⟩ :=
    exists_layer_bar_comp hk (D.hom i₁) hψs (D.ker_le_center i₁) hf hfne hub
  exact exists_layer_of_action hMc.orderOf_eq_two (nbrLayer_le_centralizer Ω M a) hCY ha' hw hww
    hsa hs2 hact hLc hLn hubL hLiso

end Nbhd

end CFSG.ClassicalInvolution.Q3.Q3AM
