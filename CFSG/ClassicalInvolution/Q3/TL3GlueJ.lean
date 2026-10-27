module

public import CFSG.ClassicalInvolution.Q3.TL3GlueEdge
public import CFSG.ClassicalInvolution.Q3.TL3GlueR
public import CFSG.ClassicalInvolution.Q3.TL3SecRestr

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement

section Member

variable {X : Type} [Group X] [Finite X]

theorem IsClassicalMember3.map_mk_odd {N : Subgroup X} [N.Normal] (hN : Odd (Nat.card N))
    {L : Subgroup X} {z : X} (h : IsClassicalMember3 L z) :
    IsClassicalMember3 (L.map (QuotientGroup.mk' N)) (QuotientGroup.mk' N z) where
  orderOf_eq_two := by
    have hnot : z ∉ N := by
      intro hmem
      have h1 := Subgroup.orderOf_dvd_natCard _ hmem
      rw [h.orderOf_eq_two] at h1
      exact (Nat.not_even_iff_odd.mpr hN) (even_iff_two_dvd.mpr h1)
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow, ← h.orderOf_eq_two, pow_orderOf_eq_one, map_one]
    · rw [QuotientGroup.mk'_apply, Ne, QuotientGroup.eq_one_iff]
      exact hnot
  mem := Subgroup.mem_map_of_mem _ h.mem
  subnormal := by
    have hz2 : z * z = 1 := by rw [← sq, ← h.orderOf_eq_two, pow_orderOf_eq_one]
    rw [OddQ.centralizer_mk_eq hN hz2]
    exact CFSG.ComponentClassification.Components.chain_map _ h.subnormal
  nonempty_equiv := by
    obtain ⟨e⟩ := h.nonempty_equiv
    have hk : Odd (Nat.card ((QuotientGroup.mk' N).subgroupMap L).ker) := by
      have hkernel : ((QuotientGroup.mk' N).subgroupMap L).ker =
          ((QuotientGroup.mk' N).domRestrict L).ker := by
        ext x
        change (QuotientGroup.mk' N).subgroupMap L x = 1 ↔ QuotientGroup.mk' N (x : X) = 1
        exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
      rw [hkernel]
      apply CFSG.ComponentClassification.OddKernel.odd_card_restriction_kernel
      rw [QuotientGroup.ker_mk']
      exact hN
    exact ⟨(CFSG.ComponentClassification.OddKernel.coreQuotientEquiv
      ((QuotientGroup.mk' N).subgroupMap L) (MonoidHom.subgroupMap_surjective _ L) hk).symm.trans
      e⟩

end Member

variable {G : Type} [Group G] [Finite G] {R : Subgroup G} {S : Sylow 2 R} {t : G}

omit [Finite G] in
theorem le_tightCore_of_isPGroup {V : Subgroup G} (hVR : V ≤ R) (hV2 : IsPGroup 2 V) :
    V ≤ tightCore R := fun _ hv =>
  Subgroup.subset_closure ⟨hVR hv, hV2.to_le (Subgroup.zpowers_le.mpr hv)⟩

omit [Finite G] in
theorem exists_sylow_map_eq {V P : Subgroup G} (h : IsSylow2In V P) :
    ∃ S' : Sylow 2 ↥P, ((S' : Subgroup P).map P.subtype : Subgroup G) = V := by
  refine ⟨{ toSubgroup := V.subgroupOf P
            isPGroup' := h.2.1.comap_subtype
            is_maximal' := ?_ }, Subgroup.map_subgroupOf_eq_of_le h.1⟩
  intro Q hQ hle
  have hVQ : V ≤ Q.map P.subtype := by
    rw [← Subgroup.map_subgroupOf_eq_of_le h.1]
    exact Subgroup.map_mono hle
  have := h.2.2 (Q.map P.subtype) (Subgroup.map_subtype_le _) (hQ.map _) hVQ
  rw [← Subgroup.comap_map_eq_self_of_injective P.subtype_injective Q, this]
  rfl

omit [Finite G] in
theorem isSylow2In_of_isSylow2In_tightCore {P : Subgroup G} (hP : IsSylow2In P (tightCore R)) :
    IsSylow2In P R :=
  ⟨hP.1.trans (tightCore_le R), hP.2.1, fun V hVR hV2 hPV =>
    hP.2.2 V (le_tightCore_of_isPGroup hVR hV2) hV2 hPV⟩

omit [Finite G] in
theorem TightDatum.mem_oddCoreImg_of_odd (hd : TightDatum R S t) {w : G} (hw : w ∈ R)
    (hodd : Odd (orderOf w)) : w ∈ oddCoreImg R := by
  set π : R →* R ⧸ classicalInvolutionOddCore R := QuotientGroup.mk' _ with hπ
  have h1 : orderOf (π ⟨w, hw⟩) ∣ orderOf w := by
    have := orderOf_map_dvd π ⟨w, hw⟩
    rwa [Subgroup.orderOf_mk] at this
  obtain ⟨m, hm⟩ := hd.twoGroup (π ⟨w, hw⟩)
  have h2 : orderOf (π ⟨w, hw⟩) ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hm
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
  have hj0 : j = 0 := by
    by_contra hj0
    have h3 : Odd (2 ^ j) := hj ▸ hodd.of_dvd_nat h1
    exact (Nat.not_even_iff_odd.mpr h3) ((Nat.even_pow' hj0).mpr even_two)
  rw [hj0, pow_zero] at hj
  have h4 : π ⟨w, hw⟩ = 1 := orderOf_eq_one_iff.mp hj
  exact ⟨⟨w, hw⟩, (QuotientGroup.eq_one_iff _).mp h4, rfl⟩

theorem TightDatum.mem_ker_act_of_isSylow2In (hd : TightDatum R S t) {P : Subgroup G}
    (hP : IsSylow2In P R) {g : G} (hg : g ∈ Subgroup.centralizer ({t} : Set G))
    (h : ∀ p ∈ P, ⁅g, p⁆ ∈ oddCoreImg R) :
    (⟨g, hg⟩ : Subgroup.centralizer ({t} : Set G)) ∈ hd.act.ker := by
  obtain ⟨S', e⟩ := exists_sylow_map_eq hP
  exact (hd.ofSylow S').mem_ker_act_of_sylow hg fun s hs => h s (e ▸ hs)

theorem TightDatum.exists_member_dbar (hd : TightDatum R S t) {RJ : Subgroup G}
    {SJ : Sylow 2 RJ} {u : G} (hdJ : TightDatum RJ SJ u)
    (hut : u ∈ Subgroup.centralizer ({t} : Set G))
    (huK : (⟨u, hut⟩ : Subgroup.centralizer ({t} : Set G)) ∈ hd.act.ker)
    {T : Subgroup G} (hT : IsSylow2In T (tightCore RJ))
    (hTc : T ≤ Subgroup.centralizer ({t} : Set G))
    (hTD : ∀ τ (hτ : τ ∈ T), (⟨τ, hTc hτ⟩ : Subgroup.centralizer ({t} : Set G)) ∈ hd.act.ker)
    {T' : Subgroup G} (hT' : IsSylow2In T' (tightCore R))
    (hT'c : T' ≤ Subgroup.centralizer ({u} : Set G))
    (hT'D : ∀ τ (hτ : τ ∈ T'), (⟨τ, hT'c hτ⟩ : Subgroup.centralizer ({u} : Set G)) ∈ hdJ.act.ker)
    (hg : GoodThreeElement (RJ.subgroupOf (Subgroup.centralizer ({t} : Set G))) (⟨u, hut⟩ : _)) :
    ∃ L : Subgroup hd.Dbar, IsClassicalMember3 L (hd.toDbar ⟨⟨u, hut⟩, huK⟩) := by
  classical
  set C : Subgroup G := Subgroup.centralizer ({t} : Set G) with hC
  set Cu : Subgroup G := Subgroup.centralizer ({u} : Set G) with hCu
  obtain ⟨x, k, hxu, hxt, hx3, ⟨r0, hr0, hxr0⟩, hxD⟩ := partial_good_of_restrict hut hg
  have hT'R : IsSylow2In T' R := isSylow2In_of_isSylow2In_tightCore hT'
  have hTRJ : IsSylow2In T RJ := isSylow2In_of_isSylow2In_tightCore hT
  have hxK : (⟨x, hxt⟩ : C) ∈ hd.act.ker := by
    refine hd.mem_ker_act_of_isSylow2In hT'R hxt fun τ hτ => ?_
    have hτR : τ ∈ R := hT'R.1 hτ
    have hτJ : ∀ r ∈ RJ, ⁅τ, r⁆ ∈ oddCoreImg RJ := (hdJ.mem_ker_act_iff _).mp (hT'D τ hτ)
    have h1 := hxD τ (hT'c hτ) (hd.cent hτR) hτJ
    have hxτR : ⁅x, τ⁆ ∈ R := by
      rw [commutatorElement_def]
      exact R.mul_mem (hd.conj_mem hxt hτR) (R.inv_mem hτR)
    exact hd.mem_oddCoreImg_of_odd hxτR
      ((odd_natCard_oddCoreImg _).of_dvd_nat (Subgroup.orderOf_dvd_natCard _ h1))
  set DY : Subgroup G := hd.act.ker.map C.subtype with hDY
  have hDYC : DY ≤ C := Subgroup.map_subtype_le _
  have hmemDY : ∀ {g : G} (hg : g ∈ C), (⟨g, hg⟩ : C) ∈ hd.act.ker → g ∈ DY :=
    fun hg h => ⟨⟨_, hg⟩, h, rfl⟩
  have hTDY : T ≤ DY := fun τ hτ => hmemDY (hTc hτ) (hTD τ hτ)
  have hxDY : x ∈ DY := hmemDY hxt hxK
  have huDY : u ∈ DY := hmemDY hut huK
  have hDYker : ∀ y (hy : y ∈ DY), (⟨y, hDYC hy⟩ : C) ∈ hd.act.ker := by
    rintro _ ⟨y, hy, rfl⟩
    exact hy
  obtain ⟨SJ', hSJ'T⟩ := exists_sylow_map_eq hTRJ
  have hdJ' : TightDatum RJ SJ' u := hdJ.ofSylow SJ'
  have hSDY : ((SJ' : Subgroup RJ).map RJ.subtype : Subgroup G) ≤ DY := hSJ'T ▸ hTDY
  obtain ⟨SH, hdH, -⟩ := hdJ'.restrict hSDY
  have hoddmem : ∀ (y : G) (hy : y ∈ DY) (hyu : y ∈ Cu), (∀ τ (hτ : τ ∈ T),
      ⁅(⟨y, hy⟩ : DY), (⟨τ, hTDY hτ⟩ : DY)⁆ ∈ oddCoreImg (RJ.subgroupOf DY)) →
      (⟨y, hyu⟩ : Cu) ∈ hdJ.act.ker := by
    intro y hy hyu hyT
    refine hdJ.mem_ker_act_of_isSylow2In hTRJ hyu fun τ hτ => ?_
    have h1 := hyT τ hτ
    have hodd : Odd (orderOf ⁅y, τ⁆) := by
      have h2 := (odd_natCard_oddCoreImg _).of_dvd_nat (Subgroup.orderOf_dvd_natCard _ h1)
      rwa [← Subgroup.orderOf_coe] at h2
    have hτJ : τ ∈ RJ := hTRJ.1 hτ
    have hyτR : ⁅y, τ⁆ ∈ RJ := by
      rw [commutatorElement_def]
      exact RJ.mul_mem (hdJ.conj_mem hyu hτJ) (RJ.inv_mem hτJ)
    exact hdJ.mem_oddCoreImg_of_odd hyτR hodd
  have hCH : (Cu ⊓ DY).subgroupOf DY = Subgroup.centralizer ({(⟨u, huDY⟩ : DY)} : Set DY) := by
    ext y
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, hCu, Subgroup.mem_centralizer_iff,
      Set.mem_singleton_iff, forall_eq]
    exact ⟨fun hy => Subtype.ext hy.1, fun hy => ⟨congrArg Subtype.val hy, y.2⟩⟩
  have hgH : GoodThreeElement (RJ.subgroupOf DY) (⟨u, huDY⟩ : DY) := by
    refine ⟨⟨x, hxDY⟩, k, ?_, Subtype.ext (by simpa using hx3), ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hxu)
    · by_contra hcon
      push Not at hcon
      apply hxr0
      have hxJ := hoddmem x hxDY hxu (fun τ hτ => hcon _ (Subgroup.mem_subgroupOf.mpr (hTRJ.1 hτ)))
      exact (hdJ.mem_ker_act_iff _).mp hxJ r0 hr0
    · intro y hyC hyR
      have hyt : (y : G) ∈ C := hDYC y.2
      have hyu : (y : G) ∈ Cu := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hyC)
      have hyJ := hoddmem y y.2 hyu (fun τ hτ => hyR _ (Subgroup.mem_subgroupOf.mpr (hTRJ.1 hτ)))
      have h1 := hxD y hyu hyt ((hdJ.mem_ker_act_iff _).mp hyJ)
      have hwDY : ⁅x, (y : G)⁆ ∈ DY := by
        rw [commutatorElement_def]
        exact DY.mul_mem (DY.mul_mem (DY.mul_mem hxDY y.2) (DY.inv_mem hxDY)) (DY.inv_mem y.2)
      have h2 : ⁅x, (y : G)⁆ ∈ oddCoreImg ((Cu ⊓ C) ⊓ DY) :=
        oddCoreImg_inf_le (Cu ⊓ C) DY ⟨h1, hwDY⟩
      have e : (Cu ⊓ C) ⊓ DY = Cu ⊓ DY := by
        rw [inf_assoc, inf_eq_right.mpr hDYC]
      rw [e] at h2
      rw [← hCH, mem_oddCoreImg_subgroupOf_iff inf_le_right]
      exact h2
  obtain ⟨L, -, hL⟩ := tightHasLift_of_good hdH hgH
  set e : ↥hd.act.ker ≃* ↥DY := hd.act.ker.equivMapOfInjective C.subtype C.subtype_injective
    with he
  have heu : e.symm (⟨u, huDY⟩ : DY) = ⟨⟨u, hut⟩, huK⟩ := by
    apply e.injective
    rw [MulEquiv.apply_symm_apply]
    rfl
  have hL' := hL.map_mulEquiv e.symm
  rw [heu] at hL'
  have hNodd : Odd (Nat.card hd.oddKer) := by
    have h1 : Nat.card hd.oddKer = Nat.card ((oddCore C).subgroupOf hd.act.ker) := rfl
    have h2 : Nat.card ((oddCore C).subgroupOf hd.act.ker) ∣ Nat.card (oddCore C) := by
      have := Subgroup.card_dvd_of_le (inf_le_left : oddCore C ⊓ hd.act.ker ≤ oddCore C)
      rwa [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (inf_le_right : oddCore C ⊓ hd.act.ker ≤ hd.act.ker)).toEquiv,
        Subgroup.inf_subgroupOf_right] at this
    rw [h1]
    exact (QuaternionStructure.odd_natCard_oddCore C).of_dvd_nat h2
  exact ⟨_, hL'.map_mk_odd (N := hd.oddKer) hNodd⟩

end CFSG.ClassicalInvolution.Q3
