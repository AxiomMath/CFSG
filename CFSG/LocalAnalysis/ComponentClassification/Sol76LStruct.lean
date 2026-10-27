module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76CentLayer
public import CFSG.LocalAnalysis.ComponentClassification.Sol76PumpDown

public section

namespace CFSG.ComponentClassification.Sol76

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer

section Quot

variable {A B : Type*} [Group A] [Finite A] [Group B] [Finite B]

noncomputable def coreQuotEquivOfSurjective (f : A →* B) (hf : Function.Surjective f)
    (hodd : Odd (Nat.card f.ker)) : A ⧸ pPrimeCore 2 A ≃* B ⧸ pPrimeCore 2 B :=
  (QuotientGroup.quotientMulEquivOfEq (CatalogueBAlternating.primeCore_two_eq_oddCore A)).trans
    ((OddKernel.coreQuotientEquiv f hf hodd).trans
      (QuotientGroup.quotientMulEquivOfEq (CatalogueBAlternating.primeCore_two_eq_oddCore B)).symm)

theorem coreQuotEquivOfSurjective_mk (f : A →* B) (hf : Function.Surjective f)
    (hodd : Odd (Nat.card f.ker)) (a : A) :
    coreQuotEquivOfSurjective f hf hodd (QuotientGroup.mk' (pPrimeCore 2 A) a) =
      QuotientGroup.mk' (pPrimeCore 2 B) (f a) := by
  unfold coreQuotEquivOfSurjective
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply]
  change (QuotientGroup.quotientMulEquivOfEq
      (CatalogueBAlternating.primeCore_two_eq_oddCore B)).symm
    (OddKernel.coreQuotientEquiv f hf hodd
      (QuotientGroup.mk' (CFSG.Open.componentClassificationOddCore A) a)) =
    QuotientGroup.mk' (pPrimeCore 2 B) (f a)
  rw [OddKernel.coreQuotientEquiv_mk]
  rfl

omit [Finite A] in
noncomputable def coreQuotEquivSelf (h : pPrimeCore 2 A = ⊥) : A ⧸ pPrimeCore 2 A ≃* A :=
  (QuotientGroup.quotientMulEquivOfEq h).trans QuotientGroup.quotientBot

noncomputable def coreQuotCoreQuotEquiv (A : Type*) [Group A] [Finite A] :
    (A ⧸ pPrimeCore 2 A) ⧸ pPrimeCore 2 (A ⧸ pPrimeCore 2 A) ≃* A ⧸ pPrimeCore 2 A :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  coreQuotEquivSelf (pPrimeCore_quotient_pPrimeCore_eq_bot 2)

end Quot

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem odd_card_ker_mk_comp_inclusion {H K : Subgroup G} (h : H ≤ K) (N : Subgroup ↥K)
    [N.Normal] (hN : Odd (Nat.card N)) :
    Odd (Nat.card ((QuotientGroup.mk' N).comp (Subgroup.inclusion h)).ker) := by
  let ι : ((QuotientGroup.mk' N).comp (Subgroup.inclusion h)).ker →* N :=
    { toFun := fun x => ⟨Subgroup.inclusion h x, by
        have h1 : ((QuotientGroup.mk' N).comp (Subgroup.inclusion h)) x = 1 := x.2
        exact (QuotientGroup.eq_one_iff _).mp h1⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hι : Function.Injective ι := fun a b hab => by
    have h2 : (((ι a : N) : ↥K) : G) = ((ι b : N) : ↥K) :=
      congrArg (fun z : N => ((z : ↥K) : G)) hab
    exact Subtype.ext (Subtype.ext h2)
  exact hN.of_dvd_nat (Subgroup.card_dvd_of_injective ι hι)

omit [Finite G] in
theorem surjective_mk_comp_inclusion {H K : Subgroup G} (h : H ≤ K) {N : Subgroup ↥K}
    [N.Normal] (hsup : H ⊔ N.map K.subtype = K) :
    Function.Surjective ((QuotientGroup.mk' N).comp (Subgroup.inclusion h)) := by
  intro q
  obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective N q
  have hk : k ∈ H.subgroupOf K ⊔ N := by
    have h0 : (N.map K.subtype).subgroupOf K = N := by
      rw [← comap_subtype, comap_map_eq_self_of_injective K.subtype_injective]
    have h1 : (H ⊔ N.map K.subtype).subgroupOf K = H.subgroupOf K ⊔ N := by
      rw [subgroupOf_sup h (map_subtype_le N), h0]
    rw [← h1, hsup, subgroupOf_self]
    exact mem_top k
  obtain ⟨y, hy, n, hn, rfl⟩ := mem_sup_of_normal_right.mp hk
  refine ⟨⟨y, mem_subgroupOf.mp hy⟩, ?_⟩
  change QuotientGroup.mk' N y = QuotientGroup.mk' N (y * n)
  rw [map_mul, show QuotientGroup.mk' N n = 1 from (QuotientGroup.eq_one_iff n).mpr hn, mul_one]

theorem oddResidualIn_eq_map_primeResidual (Y : Subgroup G) :
    oddResidualIn Y = (CatalogueBPrimeJoin.primeResidual 2 ↥Y).map Y.subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CatalogueBPrimeJoin.primeResidual_eq_closure, MonoidHom.map_closure, oddResidualIn]
  congr 1
  ext x
  constructor
  · rintro ⟨hx, k, hk⟩
    exact ⟨⟨x, hx⟩, ⟨k, by rw [← Subgroup.orderOf_coe]; exact hk⟩, rfl⟩
  · rintro ⟨y, ⟨k, hk⟩, rfl⟩
    exact ⟨y.2, k, by rw [Subgroup.coe_subtype, Subgroup.orderOf_coe]; exact hk⟩

theorem coprime_index_oddResidualIn (Y : Subgroup G) :
    Nat.Coprime 2 ((oddResidualIn Y).subgroupOf Y).index := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [oddResidualIn_eq_map_primeResidual, ← comap_subtype,
    comap_map_eq_self_of_injective Y.subtype_injective]
  exact CatalogueBPrimeJoin.primeResidual_coprime_index 2 ↥Y

omit [Finite G] in
theorem le_normalizer_oddCoreIn (D : Subgroup G) : D ≤ normalizer (oddCoreIn D : Set G) :=
  fun _ hc => mem_normalizer_iff_map_conj_eq.mpr (map_conj_oddCoreIn (le_normalizer hc))

theorem isQuasisimple_coreQuot_of_isSolomonMember {L : Subgroup G} (hL : IsSolomonMember L) :
    IsQuasisimple (↥L ⧸ pPrimeCore 2 ↥L) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hLp, T, -, hT2, hTQ, hK0⟩ := hL
  set C := centralizer (T : Set G) with hC
  set Y := L ⊓ C with hY
  set OC := oddCoreIn C with hOC
  set H := OC ⊔ Y with hH
  set K0 := oddResidualIn H with hK0def
  have hYL : Y ≤ L := inf_le_left
  have hYH : Y ≤ H := le_sup_right
  have hOCH : OC ≤ H := le_sup_left
  have hHC : H ≤ C := sup_le (map_subtype_le _) inf_le_right
  have hK0eq : K0 = (CatalogueBPrimeJoin.primeResidual 2 ↥H).map H.subtype :=
    oddResidualIn_eq_map_primeResidual H
  have hK0H : K0 ≤ H := by rw [hK0eq]; exact map_subtype_le _
  have hK0sub : K0.subgroupOf H = CatalogueBPrimeJoin.primeResidual 2 ↥H := by
    rw [hK0eq, ← comap_subtype, comap_map_eq_self_of_injective H.subtype_injective]
  have hOHn : (OC.subgroupOf H).Normal :=
    (normal_subgroupOf_iff_le_normalizer hOCH).mpr (hHC.trans (le_normalizer_oddCoreIn C))
  have hOHodd : Odd (Nat.card (OC.subgroupOf H)) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hOCH).toEquiv]
    exact Nat.coprime_two_left.mp (coprime_card_oddCoreIn C)
  have hoddL : Odd (Nat.card (pPrimeCore 2 ↥L)) :=
    Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := ↥L))
  have hoddH : Odd (Nat.card (pPrimeCore 2 ↥H)) :=
    Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := ↥H))
  have hHsup : Y ⊔ (OC.subgroupOf H).map H.subtype = H := by
    rw [subgroupOf_map_subtype, inf_eq_left.mpr hOCH, sup_comm]
  have hLsup : Y ⊔ (pPrimeCore 2 ↥L).map L.subtype = L := inf_centralizer_sup_oddCoreIn_eq hT2 hTQ
  have e1 := coreQuotEquivOfSurjective _ (surjective_mk_comp_inclusion hYL hLsup)
    (odd_card_ker_mk_comp_inclusion hYL (pPrimeCore 2 ↥L) hoddL)
  have e2 := coreQuotEquivOfSurjective _ (surjective_mk_comp_inclusion hYH hHsup)
    (odd_card_ker_mk_comp_inclusion hYH (OC.subgroupOf H) hOHodd)
  have e3 := coreQuotEquivOfSurjective (QuotientGroup.mk' (OC.subgroupOf H))
    (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk']; exact hOHodd)
  have eLH : ↥L ⧸ pPrimeCore 2 ↥L ≃* ↥H ⧸ pPrimeCore 2 ↥H :=
    (coreQuotCoreQuotEquiv ↥L).symm.trans (e1.symm.trans (e2.trans e3.symm))
  have : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hLp
  have hHperf : Group.IsPerfect (↥H ⧸ pPrimeCore 2 ↥H) :=
    Group.IsPerfect.ofSurjective (f := eLH.toMonoidHom) eLH.surjective
  set κ := (QuotientGroup.mk' (pPrimeCore 2 ↥H)).comp (Subgroup.inclusion hK0H) with hκ
  have hκs : Function.Surjective κ := by
    rw [← MonoidHom.range_eq_top]
    calc κ.range = (K0.subgroupOf H).map (QuotientGroup.mk' (pPrimeCore 2 ↥H)) := by
          rw [hκ, MonoidHom.range_comp, Subgroup.inclusion_range]
      _ = (CatalogueBPrimeJoin.primeResidual 2 ↥H).map (QuotientGroup.mk' (pPrimeCore 2 ↥H)) := by
          rw [hK0sub]
      _ = CatalogueBPrimeJoin.primeResidual 2 (↥H ⧸ pPrimeCore 2 ↥H) :=
          CatalogueBPrimeJoin.primeResidual_map_surjective 2 _ (QuotientGroup.mk'_surjective _)
      _ = ⊤ := primeResidual_two_eq_top hHperf
  have e4 := coreQuotEquivOfSurjective κ hκs
    (odd_card_ker_mk_comp_inclusion hK0H (pPrimeCore 2 ↥H) hoddH)
  have hK0q : IsQuasisimple (↥K0 ⧸ pPrimeCore 2 ↥K0) :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 K0 C hK0.1).mp hK0.2).2.2
  exact LocalCores.isQuasisimple_of_mulEquiv
    (e4.trans ((coreQuotCoreQuotEquiv ↥H).trans eLH.symm)) hK0q

theorem cover_facts {L Y : Subgroup G} (hLq : IsQuasisimple (↥L ⧸ pPrimeCore 2 ↥L))
    (hYL : Y ≤ L) (hYsup : Y ⊔ oddCoreIn L = L) :
    IsTwoComponentIn (oddResidualIn Y) Y ∧ twoLayerIn Y = oddResidualIn Y ∧
      oddResidualIn Y ⊔ oddCoreIn L = L ∧
      Nonempty (↥(oddResidualIn Y) ⧸ pPrimeCore 2 ↥(oddResidualIn Y) ≃* ↥L ⧸ pPrimeCore 2 ↥L) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set J := oddResidualIn Y with hJdef
  have hJeq : J = (CatalogueBPrimeJoin.primeResidual 2 ↥Y).map Y.subtype :=
    oddResidualIn_eq_map_primeResidual Y
  have hJY : J ≤ Y := by rw [hJeq]; exact map_subtype_le _
  have hJsub : J.subgroupOf Y = CatalogueBPrimeJoin.primeResidual 2 ↥Y := by
    rw [hJeq, ← comap_subtype, comap_map_eq_self_of_injective Y.subtype_injective]
  have hoddL : Odd (Nat.card (pPrimeCore 2 ↥L)) :=
    Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := ↥L))
  have hoddY : Odd (Nat.card (pPrimeCore 2 ↥Y)) :=
    Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := ↥Y))
  set β := (QuotientGroup.mk' (pPrimeCore 2 ↥L)).comp (Subgroup.inclusion hYL) with hβ
  have hβs : Function.Surjective β := surjective_mk_comp_inclusion hYL hYsup
  have hβk := odd_card_ker_mk_comp_inclusion hYL (pPrimeCore 2 ↥L) hoddL
  have eY : ↥Y ⧸ pPrimeCore 2 ↥Y ≃* ↥L ⧸ pPrimeCore 2 ↥L :=
    (coreQuotEquivOfSurjective β hβs hβk).trans (coreQuotCoreQuotEquiv ↥L)
  have hYq : IsQuasisimple (↥Y ⧸ pPrimeCore 2 ↥Y) :=
    LocalCores.isQuasisimple_of_mulEquiv eY.symm hLq
  set ι := (QuotientGroup.mk' (pPrimeCore 2 ↥Y)).comp (Subgroup.inclusion hJY) with hι
  have hιs : Function.Surjective ι := by
    rw [← MonoidHom.range_eq_top]
    calc ι.range = (J.subgroupOf Y).map (QuotientGroup.mk' (pPrimeCore 2 ↥Y)) := by
          rw [hι, MonoidHom.range_comp, Subgroup.inclusion_range]
      _ = CatalogueBPrimeJoin.primeResidual 2 (↥Y ⧸ pPrimeCore 2 ↥Y) := by
          rw [hJsub]
          exact CatalogueBPrimeJoin.primeResidual_map_surjective 2 _
            (QuotientGroup.mk'_surjective _)
      _ = ⊤ := primeResidual_two_eq_top hYq.1
  have eJ : ↥J ⧸ pPrimeCore 2 ↥J ≃* ↥Y ⧸ pPrimeCore 2 ↥Y :=
    (coreQuotEquivOfSurjective ι hιs (odd_card_ker_mk_comp_inclusion hJY _ hoddY)).trans
      (coreQuotCoreQuotEquiv ↥Y)
  have hJq : IsQuasisimple (↥J ⧸ pPrimeCore 2 ↥J) :=
    LocalCores.isQuasisimple_of_mulEquiv eJ.symm hYq
  have hJres : CatalogueBPrimeJoin.primeResidual 2 ↥J = ⊤ := by
    set R := CatalogueBPrimeJoin.primeResidual 2 ↥Y with hR
    have hRtop : CatalogueBPrimeJoin.primeResidual 2 ↥R = ⊤ := by
      apply map_injective R.subtype_injective
      rw [CatalogueBPrimeJoin.primeResidual_idempotent, ← MonoidHom.range_eq_map, range_subtype]
    exact CatalogueBPrimeJoin.primeResidual_eq_top_of_equiv 2
      ((R.equivMapOfInjective Y.subtype Y.subtype_injective).trans
        (MulEquiv.subgroupCongr hJeq.symm)) hRtop
  have hJc : IsTwoComponentIn J Y := by
    refine ⟨hJY, (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 J Y hJY).mpr ⟨?_, hJres, hJq⟩⟩
    rw [hJsub]
    have : (CatalogueBPrimeJoin.primeResidual 2 ↥Y).Characteristic :=
      CatalogueBPrimeJoin.primeResidual_characteristic 2 ↥Y
    exact Normal.isSubnormal inferInstance
  refine ⟨hJc, ?_, ?_, ⟨eJ.trans eY⟩⟩
  ·
    have hle : pLayer ↥Y 2 ≤ J.subgroupOf Y := by
      refine sSup_le fun M hM => ?_
      have h1 := CatalogueBPrimeJoin.primeResidual_eq_top_of_pComponent 2 M hM
      have h2 := CatalogueBPrimeJoin.primeResidual_map_le 2 M.subtype
      rw [h1, ← MonoidHom.range_eq_map, range_subtype] at h2
      rw [hJsub]
      exact h2
    have hge : J.subgroupOf Y ≤ pLayer ↥Y 2 := le_sSup hJc.2
    rw [twoLayerIn, le_antisymm hle hge, map_subgroupOf_eq_of_le hJY]
  ·
    apply le_antisymm (sup_le (hJY.trans hYL) (map_subtype_le _))
    refine le_trans hYsup.symm.le (sup_le (fun y hy => ?_) le_sup_right)
    obtain ⟨j, hj⟩ := hιs (QuotientGroup.mk' (pPrimeCore 2 ↥Y) ⟨y, hy⟩)
    set o : ↥Y := (Subgroup.inclusion hJY j)⁻¹ * ⟨y, hy⟩ with ho
    have h1 : o ∈ pPrimeCore 2 ↥Y := by
      rw [ho, ← QuotientGroup.eq]
      exact hj
    have hOY : (pPrimeCore 2 ↥Y).map β ≤ pPrimeCore 2 (↥L ⧸ pPrimeCore 2 ↥L) := by
      refine le_sSup ⟨(pPrimeCore_normal (p := 2) (G := ↥Y)).map β hβs, ?_⟩
      exact Nat.Coprime.coprime_dvd_right (card_map_dvd _ β)
        (pPrimeCore_coprime_card (p := 2) (G := ↥Y))
    rw [pPrimeCore_quotient_pPrimeCore_eq_bot 2] at hOY
    have h2 : β o = 1 := by
      have := hOY (mem_map_of_mem β h1)
      rwa [mem_bot] at this
    have h3 : Subgroup.inclusion hYL o ∈ pPrimeCore 2 ↥L := (QuotientGroup.eq_one_iff _).mp h2
    have h4 : (o : G) = (j : G)⁻¹ * y := by
      rw [ho, Subgroup.coe_mul, Subgroup.coe_inv]
      rfl
    have h5 : y = (j : G) * o := by rw [h4]; group
    rw [h5]
    exact mul_mem (mem_sup_left j.2) (mem_sup_right ⟨Subgroup.inclusion hYL o, h3, rfl⟩)

theorem fixedLayer_facts {X U : Subgroup G} (hX : IsSolomonMember X) (hU2 : IsPGroup 2 U)
    (hUQ : U ≤ coreActionKernel X) :
    IsTwoComponentIn (twoLayerIn (X ⊓ centralizer (U : Set G))) (X ⊓ centralizer (U : Set G)) ∧
      twoLayerIn (X ⊓ centralizer (U : Set G)) ⊔ oddCoreIn X = X ∧
      Nonempty (↥(twoLayerIn (X ⊓ centralizer (U : Set G))) ⧸
          pPrimeCore 2 ↥(twoLayerIn (X ⊓ centralizer (U : Set G))) ≃* ↥X ⧸ pPrimeCore 2 ↥X) := by
  have h := cover_facts (isQuasisimple_coreQuot_of_isSolomonMember hX) inf_le_left
    (inf_centralizer_sup_oddCoreIn_eq hU2 hUQ)
  rw [h.2.1]
  exact ⟨h.1, h.2.2.1, h.2.2.2⟩

end CFSG.ComponentClassification.Sol76
