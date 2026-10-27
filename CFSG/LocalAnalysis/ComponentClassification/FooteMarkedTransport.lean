module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitStep
public import CFSG.LocalAnalysis.ComponentClassification.FooteMarkedFamily
import CFSG.LocalAnalysis.ComponentClassification.FooteLitConjugate
import CFSG.LocalAnalysis.ComponentClassification.FooteLitThm32Tools
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrOddOrbitWitness
import CFSG.LocalAnalysis.ComponentClassification.GrSLitLemma228
import CFSG.LocalAnalysis.ComponentClassification.UGSChainNormalizerSylow
import CFSG.GroupTheory.SmallFixedTwoGroup.LemmaACentral
import CFSG.LocalAnalysis.ComponentClassification.Sol78Semisimple
import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4CorCDiagCover
import CFSG.LocalAnalysis.ComponentClassification.FooteLitThm33

public noncomputable section

namespace CFSG.ComponentClassification.FooteMarked

open CFSG Subgroup FooteLit UnbalancedLayer

variable {G : Type} [Group G] [Finite G]

theorem fixed_twoLayer_eq_perfectResidual {M U : Subgroup G}
    (hM : IsQuasisimple (M ⧸ pPrimeCore 2 M))
    (hU : IsPGroup 2 U) (hUK : U ≤ coreActionKernel M) :
    twoLayerIn (M ⊓ centralizer (U : Set G)) =
      (perfectResidual ↥(M ⊓ centralizer (U : Set G))).map
        (M ⊓ centralizer (U : Set G)).subtype := by
  let C := M ⊓ centralizer (U : Set G)
  let F := twoLayerIn C
  have hUN : U ≤ normalizer (M : Set G) := fun u hu => (mem_coreActionKernel.mp (hUK hu)).1
  have hMN : M ≤ normalizer (M : Set G) := le_normalizer
  have hMNnormal : (M.subgroupOf (normalizer (M : Set G))).Normal :=
    normal_subgroupOf_of_le_normalizer le_rfl
  obtain ⟨hcover, -, hFpc⟩ := UnbalancedCorr.fixedLayer_facts
    hMN hMNnormal.isSubnormal hUN hUN hU hM
    (fun u hu => (mem_coreActionKernel.mp (hUK hu)).2) (T := F) rfl
  have hFC : F ≤ C := map_subtype_le _
  have hCbig : C ≤ normalizer (M : Set G) ⊓ centralizer (U : Set G) :=
    inf_le_inf_right _ hMN
  have hFpcC : IsPComponent 2 (F.subgroupOf C) :=
    UnbalancedCorr.isPComponent_subgroupOf_of_le hFC hCbig hFpc
  have hFperf : Group.IsPerfect F :=
    GSThmB.B5a.isPerfect_of_isPComponent_subgroupOf hFC hFpcC
  have hFnormal : (F.subgroupOf C).Normal := by
    change (((pLayer C 2).map C.subtype).subgroupOf C).Normal
    rw [← comap_subtype, comap_map_eq_self_of_injective C.subtype_injective]
    have : (pLayer C 2).Characteristic := CatalogueBPrimeJoin.pLayer_characteristic
    infer_instance
  let N := (oddCoreIn M).subgroupOf C
  have hNodd : Odd (Nat.card N) := by
    apply Nat.coprime_two_left.mp
    have hcop : Nat.Coprime 2 (Nat.card (oddCoreIn M)) := by
      change Nat.Coprime 2 (Nat.card ↥((pPrimeCore 2 M).map M.subtype))
      rw [← Nat.card_congr ((pPrimeCore 2 M).equivMapOfInjective
        M.subtype M.subtype_injective).toEquiv]
      exact pPrimeCore_coprime_card
    let f : N →* oddCoreIn M := (C.subtype.comp N.subtype).codRestrict
      (oddCoreIn M) (fun n => n.property)
    exact hcop.of_dvd_right (Subgroup.card_dvd_of_injective f
      (fun x y h => by
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun z : oddCoreIn M => (z : G)) h))
  have hNsolv : Group.IsSolvable N := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hNodd
  let q := QuotientGroup.mk' (F.subgroupOf C)
  have hqN : Function.Surjective (q.domRestrict N) := by
    intro y
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective (F.subgroupOf C) y
    have hc : c.val ∈ F ⊔ oddCoreIn M := hcover.symm ▸ c.property.1
    have hON : F ≤ normalizer (oddCoreIn M : Set G) := fun f hf =>
      mem_normalizer_oddCoreIn (le_normalizer (hFC hf).1)
    rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right F (oddCoreIn M) hON] at hc
    obtain ⟨f, hf, n, hn, hfn⟩ := Set.mem_mul.mp hc
    have hnC : n ∈ C := by
      rw [show n = f⁻¹ * c.val by rw [← hfn]; group]
      exact C.mul_mem (C.inv_mem (hFC hf)) c.property
    refine ⟨⟨⟨n, hnC⟩, hn⟩, ?_⟩
    have hcEq : c = (⟨f, hFC hf⟩ : C) * ⟨n, hnC⟩ := Subtype.ext hfn.symm
    change q ⟨n, hnC⟩ = q c
    rw [hcEq, map_mul, show q ⟨f, hFC hf⟩ = 1 from
      (QuotientGroup.eq_one_iff _).mpr hf, one_mul]
  have hquot : Group.IsSolvable (C ⧸ F.subgroupOf C) := by
    have := hNsolv
    exact Group.isSolvable_of_surjective hqN
  apply le_antisymm
  · exact CFSG.RankThreeCoreUniqueness.Helpers.perfect_subgroup_le_perfectResidualOf
      F C hFperf hFC
  · have hle : perfectResidual C ≤ F.subgroupOf C :=
      ((perfect_residual_characterization (G := C)).2.2.2.2.1 _).mp hquot
    exact (Subgroup.map_mono hle).trans (by
      rw [map_subgroupOf_eq_of_le hFC])

theorem fixedShadow_eq_twoLayer {M U : Subgroup G}
    (hM : IsQuasisimple (M ⧸ pPrimeCore 2 M))
    (hU : IsPGroup 2 U) (hUK : U ≤ coreActionKernel M) :
    fixedShadow M U = twoLayerIn (M ⊓ centralizer (U : Set G)) :=
  (fixed_twoLayer_eq_perfectResidual hM hU hUK).symm

theorem fixedShadowAt_eq_gsFixedLayer {M : Subgroup G} {a : G}
    (hM : IsQuasisimple (M ⧸ pPrimeCore 2 M))
    (ha : orderOf a = 2) (haK : a ∈ coreActionKernel M) :
    fixedShadowAt M a = UnbalancedGS.gsFixedLayer M a := by
  rw [← fixedShadow_zpowers]
  have hU : IsPGroup 2 (zpowers a) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha, pow_one])
  rw [fixedShadow_eq_twoLayer hM hU (zpowers_le.mpr haK),
    UnbalancedLayer.centralizer_zpowers_eq]
  rfl

theorem fixedShadow_perfect (M U : Subgroup G) : Group.IsPerfect (fixedShadow M U) := by
  have hp := (CFSG.perfect_residual_characterization
    (G := ↥(M ⊓ centralizer (U : Set G)))).2.2.1
  rw [Subgroup.isPerfect_iff] at hp ⊢
  unfold fixedShadow
  rw [← map_commutator, hp]

theorem fixedShadowAt_perfect (M : Subgroup G) (a : G) :
    Group.IsPerfect (fixedShadowAt M a) := by
  rw [← fixedShadow_zpowers]
  exact fixedShadow_perfect M (zpowers a)

omit [Finite G] in
theorem fixedShadow_le_inf (M U : Subgroup G) :
    fixedShadow M U ≤ M ⊓ centralizer (U : Set G) := map_subtype_le _

omit [Finite G] in
theorem le_fixedShadow_of_perfect {P M U : Subgroup G} (hP : Group.IsPerfect P)
    (hPM : P ≤ M ⊓ centralizer (U : Set G)) : P ≤ fixedShadow M U :=
  CFSG.RankThreeCoreUniqueness.Helpers.perfect_subgroup_le_perfectResidualOf P _ hP hPM

theorem fixedShadow_cover_quotient {M U : Subgroup G}
    (hM : IsQuasisimple (M ⧸ pPrimeCore 2 M))
    (hU : IsPGroup 2 U) (hUK : U ≤ coreActionKernel M) :
    fixedShadow M U ⊔ oddCoreIn M = M ∧
      oddCoreIn (fixedShadow M U) = fixedShadow M U ⊓ oddCoreIn M ∧
      ∃ e : fixedShadow M U ⧸ pPrimeCore 2 (fixedShadow M U) ≃*
          M ⧸ pPrimeCore 2 M,
        ∀ (f : fixedShadow M U) (m : M), (f : G) = m → e f = m := by
  have hUN : U ≤ normalizer (M : Set G) := fun u hu => (hUK hu).1
  have hMn : (M.subgroupOf (normalizer (M : Set G))).Normal :=
    normal_subgroupOf_of_le_normalizer le_rfl
  obtain ⟨hcover, hcore, -⟩ := UnbalancedCorr.fixedLayer_facts
    le_normalizer hMn.isSubnormal hUN hUN hU hM
    (fun u hu => (hUK hu).2) (T := fixedShadow M U)
    (fixedShadow_eq_twoLayer hM hU hUK)
  exact ⟨hcover, hcore, UnbalancedCorr.exists_quotient_equiv_of_sup
    (fixedShadow_le M U) hcover hcore⟩

omit [Finite G] in
theorem mem_normalizer_fixedShadowAt {M : Subgroup G} {a b : G}
    (hbM : b ∈ normalizer (M : Set G)) (hab : a * b = b * a) :
    b ∈ normalizer (fixedShadowAt M a : Set G) := by
  unfold fixedShadowAt
  apply CFSG.RankThreeCoreUniqueness.Helpers.normalizer_le_normalizer_characteristic_map
    (M ⊓ centralizer ({a} : Set G)) _ CFSG.perfectResidual_characteristic'
  exact mem_normalizer_inf' hbM
    (le_normalizer (mem_centralizer_singleton_iff.mpr hab.symm))

theorem eq_of_perfect_contains_simple_component {X W : Subgroup G}
    (hX : IsComponent X) (hXs : IsSimpleGroup X) (hXW : X ≤ W)
    (hW : Group.IsPerfect W)
    (hcard : Nat.card (W ⧸ pPrimeCore 2 W) ≤ Nat.card X) : W = X := by
  have : IsSimpleGroup X := hXs
  have : Group.IsPerfect X := hX.1.1
  have hOX : pPrimeCore 2 X = ⊥ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top (pPrimeCore 2 X) with h | h
    · exact h
    · have hodd : Odd (Nat.card X) := by
        have ho := Nat.coprime_two_left.mp (pPrimeCore_coprime_card (G := X) (p := 2))
        simpa only [h, card_top] using ho
      exact (Group.IsPerfect.not_isSolvable X (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd)).elim
  have hcover : X ⊔ oddCoreIn W = W := sup_oddCoreIn_eq_of_card_le hXW (by
    rw [hOX, Nat.card_congr (QuotientGroup.quotientBot (G := X)).toEquiv]
    exact hcard)
  have hlocal := LocalComponents.of_overgroup ((CFSG.isComponent_iff_open X).mp hX) hXW
  have hnot : ¬ X.subgroupOf W ≤ pPrimeCore 2 W := by
    intro h
    have hXodd : Odd (Nat.card X) := by
      have ho : Odd (Nat.card (X.subgroupOf W)) :=
        (Nat.coprime_two_left.mp (pPrimeCore_coprime_card (G := W) (p := 2))).of_dvd_nat
          (Subgroup.card_dvd_of_le h)
      rwa [Nat.card_congr (subgroupOfEquivOfLe hXW).toEquiv] at ho
    exact Group.IsPerfect.not_isSolvable X (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hXodd)
  have hcomm := (LocalComponents.normal_contains_or_commutes
    (X.subgroupOf W) (pPrimeCore 2 W) hlocal).resolve_left hnot
  have hON : pPrimeCore 2 W ≤ normalizer (X.subgroupOf W : Set W) :=
    fun r hr => centralizer_le_normalizer _
      (commutator_eq_bot_iff_le_centralizer.mp (by rwa [commutator_comm] at hcomm) hr)
  have hcoverW : X.subgroupOf W ⊔ pPrimeCore 2 W = ⊤ := by
    apply map_injective W.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hXW, Subgroup.map_top, range_subtype]
    exact hcover
  have : Group.IsPerfect (⊤ : Subgroup W) := by
    have : Group.IsPerfect W := hW
    exact Group.IsPerfect.ofSurjective (f := (Subgroup.topEquiv (G := W)).symm.toMonoidHom)
      (Subgroup.topEquiv (G := W)).symm.surjective
  have hle := UnbalancedLayer.le_of_perfect_le_sup_of_odd
    (Nat.coprime_two_left.mp (pPrimeCore_coprime_card (G := W) (p := 2)))
    hON (show Group.IsPerfect (⊤ : Subgroup W) from inferInstance) hcoverW.ge
  apply le_antisymm _ hXW
  intro w hw
  exact hle (mem_top (⟨w, hw⟩ : W))

theorem oddCoreImage_eq_of_contains_component {T : Type} [Group T] [IsSimpleGroup T]
    {A F X : Subgroup G} (hA : IsTwoComponentIn A X) (hFX : F ≤ X)
    (hF : Group.IsPerfect F) (eA : A ⧸ pPrimeCore 2 A ≃* T)
    (eF : F ⧸ pPrimeCore 2 F ≃* T) (hAF : A ≤ F ⊔ oddCoreIn X) :
    F ⊔ oddCoreIn X = A ⊔ oddCoreIn X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let π := QuotientGroup.mk' (pPrimeCore 2 X)
  let A' := A.subgroupOf X
  let F' := F.subgroupOf X
  let K := A'.map π
  let W := F'.map π
  have hK : IsComponent K := (CatalogueBPrimeJoin.quotient_component_iff_core_quotient
    2 A' hA.2.choose_spec.2.1).mpr
      (CatalogueBHeldSmallCore.pComponent_coreQuotient_quasisimple 2 A' hA.2)
  let eK : K ≃* T :=
    (CatalogueBHeldSmallCore.subnormalCoreQuotientEquivImage
      2 A' hA.2.choose_spec.2.1).symm.trans
        ((UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2
          (subgroupOfEquivOfLe hA.1)).trans eA)
  have hKs : IsSimpleGroup K := eK.isSimpleGroup
  have hπ : ¬ 2 ∣ Nat.card π.ker := by
    rw [QuotientGroup.ker_mk']
    exact Nat.prime_two.coprime_iff_not_dvd.mp pPrimeCore_coprime_card
  obtain ⟨eW, -⟩ := CatalogueBPrimeJoin.exists_restrict_core_quotient_equiv π F'
    (GSThmB.OddQuot.not_two_dvd_card_ker_domRestrict π hπ F')
  let eWT : W ⧸ pPrimeCore 2 W ≃* T := eW.symm.trans
    ((UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2
      (subgroupOfEquivOfLe hFX)).trans eF)
  have hF' : Group.IsPerfect F' := by
    have : Group.IsPerfect F := hF
    exact Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hFX).symm.toMonoidHom)
      (subgroupOfEquivOfLe hFX).symm.surjective
  have hW : Group.IsPerfect W := by
    have : Group.IsPerfect F' := hF'
    exact Group.IsPerfect.ofSurjective (f := π.subgroupMap F') (π.subgroupMap_surjective F')
  have hAF' : A' ≤ F' ⊔ pPrimeCore 2 X := by
    change A.subgroupOf X ≤ F.subgroupOf X ⊔ pPrimeCore 2 X
    have h : (A.subgroupOf X).map X.subtype ≤
        (F.subgroupOf X ⊔ pPrimeCore 2 X).map X.subtype := by
      rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hA.1, map_subgroupOf_eq_of_le hFX]
      exact hAF
    exact (Subgroup.map_le_map_iff_of_injective X.subtype_injective).mp h
  have hcoremap : (pPrimeCore 2 X).map π = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  have hKW : K ≤ W := by
    have h := map_mono hAF' (f := π)
    rwa [Subgroup.map_sup, hcoremap, sup_bot_eq] at h
  have hWK : W = K := eq_of_perfect_contains_simple_component hK hKs hKW hW (by
    rw [Nat.card_congr eWT.toEquiv, Nat.card_congr eK.toEquiv])
  have hpre := congrArg (comap π) hWK
  change ((F.subgroupOf X).map π).comap π = ((A.subgroupOf X).map π).comap π at hpre
  rw [comap_map_eq, comap_map_eq, QuotientGroup.ker_mk'] at hpre
  have hambient := congrArg (map X.subtype) hpre
  rw [Subgroup.map_sup, Subgroup.map_sup, map_subgroupOf_eq_of_le hFX,
    map_subgroupOf_eq_of_le hA.1] at hambient
  exact hambient

theorem eq_of_perfect_le_conjClosure_sup_odd {X V R : Subgroup G}
    (hX : IsComponent X) (hXV : X ≤ V) (hV : Group.IsPerfect V)
    (hR : R ≤ V) (hRodd : Odd (Nat.card R))
    (hVle : V ≤ FooteLit.conjClosure X V ⊔ R) : V = X := by
  let N := FooteLit.conjClosure X V
  have hVN : V ≤ normalizer (N : Set G) := Sol78.le_normalizer_conjClosure X V
  have hRVN : R ≤ normalizer (N : Set G) := hR.trans hVN
  have hVleN : V ≤ N := by
    refine GSThmB.CorC.le_of_perfect_of_le_sup_odd hRVN hRodd ?_ ?_
    · exact (Subgroup.isPerfect_iff (H := V)).mp hV
    · simpa [N] using hVle
  have hNleLayer : N ≤ layer G := by
    refine Sol78.conjClosure_le (J := X) (E := V) (M := layer G) ?_ ?_
    · exact LocalCores.component_le_layer hX
    · haveI : (layer G).Characteristic := LocalCores.layer_characteristic
      haveI : (layer G).Normal := inferInstance
      simpa [Subgroup.normalizer_eq_top] using (le_top : V ≤ (⊤ : Subgroup G))
  have hVNX : V ≤ normalizer (X : Set G) :=
    (hVleN.trans hNleLayer).trans (LocalCores.layer_le_normalizer hX)
  have hNleX : N ≤ X := Sol78.conjClosure_le (le_refl X) hVNX
  have hXN : X ≤ N := FooteLit.le_conjClosure X V
  have hNX : N = X := le_antisymm hNleX hXN
  exact le_antisymm (hVleN.trans hNX.le) hXV

theorem oddCoreImage_eq_of_perfect_le_conjClosure_sup_odd
    {A P W R : Subgroup G}
    (hPA : P ≤ A) (hWA : W ≤ A) (hPW : P ≤ W)
    (hWperf : Group.IsPerfect W) (hR : R ≤ W)
    (hRodd : Odd (Nat.card R))
    (hWle : W ≤ FooteLit.conjClosure P W ⊔ R)
    (hX : IsComponent ((P.subgroupOf A).map (QuotientGroup.mk' (pPrimeCore 2 A)))) :
    (W.subgroupOf A).map (QuotientGroup.mk' (pPrimeCore 2 A)) =
      (P.subgroupOf A).map (QuotientGroup.mk' (pPrimeCore 2 A)) ∧
    W ⊔ oddCoreIn A = P ⊔ oddCoreIn A := by
  let π := QuotientGroup.mk' (pPrimeCore 2 A)
  let N := FooteLit.conjClosure P W
  let NA := FooteLit.conjClosure (P.subgroupOf A) (W.subgroupOf A)
  have hRA : R ≤ A := hR.trans hWA
  have hNleA : N ≤ A :=
    Sol78.conjClosure_le hPA (hWA.trans le_normalizer)
  have hNmapG : NA.map A.subtype = N := by
    dsimp [NA, N]
    rw [FooteLit.map_conjClosure A.subtype, map_subgroupOf_eq_of_le hPA,
      map_subgroupOf_eq_of_le hWA]
  have hNAsub : N.subgroupOf A = NA := by
    apply map_injective A.subtype_injective
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hNleA]
    exact hNmapG.symm
  have hWleA : W.subgroupOf A ≤ NA ⊔ R.subgroupOf A := by
    have h := Subgroup.subgroupOf_mono A hWle
    rwa [Subgroup.subgroupOf_sup hNleA hRA, hNAsub] at h
  have hWleQ : (W.subgroupOf A).map π ≤ NA.map π ⊔ (R.subgroupOf A).map π := by
    have h := Subgroup.map_mono (f := π) hWleA
    simpa only [Subgroup.map_sup] using h
  have hNmap : NA.map π =
      FooteLit.conjClosure ((P.subgroupOf A).map π) ((W.subgroupOf A).map π) :=
    FooteLit.map_conjClosure π (P.subgroupOf A) (W.subgroupOf A)
  have hWleQ' : (W.subgroupOf A).map π ≤
      FooteLit.conjClosure ((P.subgroupOf A).map π) ((W.subgroupOf A).map π) ⊔
        (R.subgroupOf A).map π := by
    simpa [hNmap] using hWleQ
  have hW' : Group.IsPerfect (W.subgroupOf A) := by
    have : Group.IsPerfect W := hWperf
    exact Group.IsPerfect.ofSurjective
      (f := (subgroupOfEquivOfLe hWA).symm.toMonoidHom)
      (subgroupOfEquivOfLe hWA).symm.surjective
  have hVperf : Group.IsPerfect ((W.subgroupOf A).map π) := by
    have : Group.IsPerfect (W.subgroupOf A) := hW'
    exact Group.IsPerfect.ofSurjective (f := π.subgroupMap (W.subgroupOf A))
      (π.subgroupMap_surjective (W.subgroupOf A))
  have hXV : (P.subgroupOf A).map π ≤ (W.subgroupOf A).map π :=
    Subgroup.map_mono (f := π) (Subgroup.subgroupOf_mono A hPW)
  have hRV : (R.subgroupOf A).map π ≤ (W.subgroupOf A).map π :=
    Subgroup.map_mono (f := π) (Subgroup.subgroupOf_mono A hR)
  have hRodd' : Odd (Nat.card ((R.subgroupOf A).map π)) := by
    apply hRodd.of_dvd_nat
    calc Nat.card ((R.subgroupOf A).map π) ∣ Nat.card (R.subgroupOf A) :=
          Subgroup.card_map_dvd (R.subgroupOf A) π
      _ = Nat.card R := Nat.card_congr (subgroupOfEquivOfLe hRA).toEquiv
  have hVeq : (W.subgroupOf A).map π = (P.subgroupOf A).map π :=
    eq_of_perfect_le_conjClosure_sup_odd hX hXV hVperf hRV hRodd' hWleQ'
  have hcomap : W.subgroupOf A ⊔ pPrimeCore 2 A =
      P.subgroupOf A ⊔ pPrimeCore 2 A := by
    have hWc := Subgroup.comap_map_eq (f := π) (H := W.subgroupOf A)
    have hPc := Subgroup.comap_map_eq (f := π) (H := P.subgroupOf A)
    rw [QuotientGroup.ker_mk'] at hWc hPc
    have h := congrArg (Subgroup.comap π) hVeq
    rwa [hWc, hPc] at h
  have hmapW : (W.subgroupOf A ⊔ pPrimeCore 2 A).map A.subtype =
      W ⊔ oddCoreIn A := by
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hWA]
    rfl
  have hmapP : (P.subgroupOf A ⊔ pPrimeCore 2 A).map A.subtype =
      P ⊔ oddCoreIn A := by
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hPA]
    rfl
  refine ⟨hVeq, ?_⟩
  calc
    W ⊔ oddCoreIn A = (W.subgroupOf A ⊔ pPrimeCore 2 A).map A.subtype := hmapW.symm
    _ = (P.subgroupOf A ⊔ pPrimeCore 2 A).map A.subtype := by rw [hcomap]
    _ = P ⊔ oddCoreIn A := hmapP

theorem eq_sup_oddCoreIn_of_simple_oddCoreImage
    {A P W R : Subgroup G}
    (hPA : P ≤ A) (hWA : W ≤ A) (hPW : P ≤ W)
    (hWperf : Group.IsPerfect W) (hR : R ≤ W)
    (hRodd : Odd (Nat.card R))
    (hWle : W ≤ FooteLit.conjClosure P W ⊔ R)
    (hX : IsComponent ((P.subgroupOf A).map (QuotientGroup.mk' (pPrimeCore 2 A))))
    (hXsimple : IsSimpleGroup ((P.subgroupOf A).map (QuotientGroup.mk' (pPrimeCore 2 A)))) :
    W = P ⊔ oddCoreIn W ∧ W ⊓ oddCoreIn A = oddCoreIn W ∧
    W ⊔ oddCoreIn A = P ⊔ oddCoreIn A := by
  let π := QuotientGroup.mk' (pPrimeCore 2 A)
  obtain ⟨hImgEq, hAmbEq⟩ := oddCoreImage_eq_of_perfect_le_conjClosure_sup_odd
    hPA hWA hPW hWperf hR hRodd hWle hX
  let O := oddCoreIn W
  have hOW : O ≤ W := by
    dsimp [O, FooteLit.oddCoreIn]
    exact map_subtype_le _
  have hO_normal : (O.subgroupOf W).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hOW]
    intro w hw
    exact mem_normalizer_oddCoreIn (le_normalizer hw)
  have hWcopy : Group.IsPerfect (W.subgroupOf A) := by
    have : Group.IsPerfect W := hWperf
    exact Group.IsPerfect.ofSurjective
      (f := (subgroupOfEquivOfLe hWA).symm.toMonoidHom)
      (subgroupOfEquivOfLe hWA).symm.surjective
  have hImgPerf : Group.IsPerfect ((W.subgroupOf A).map π) := by
    have : Group.IsPerfect (W.subgroupOf A) := hWcopy
    exact Group.IsPerfect.ofSurjective (f := π.subgroupMap (W.subgroupOf A))
      (π.subgroupMap_surjective (W.subgroupOf A))
  have hImgSimple : IsSimpleGroup ((W.subgroupOf A).map π) := by
    rw [hImgEq]
    exact hXsimple
  let eW : W ≃* W.subgroupOf A := (subgroupOfEquivOfLe hWA).symm
  let πW : W →* (W.subgroupOf A).map π :=
    (π.subgroupMap (W.subgroupOf A)).comp eW.toMonoidHom
  have hπW_surj : Function.Surjective πW := by
    intro y
    obtain ⟨x, rfl⟩ := π.subgroupMap_surjective (W.subgroupOf A) y
    exact ⟨eW.symm x, by simp [πW, eW]⟩
  have hnormal : ((O.subgroupOf W).map πW).Normal :=
    Subgroup.Normal.map hO_normal πW hπW_surj
  have hOddO : Odd (Nat.card O) := odd_card_oddCoreIn W
  have hOddImg : Odd (Nat.card ((O.subgroupOf W).map πW)) := by
    apply hOddO.of_dvd_nat
    calc Nat.card ((O.subgroupOf W).map πW) ∣ Nat.card (O.subgroupOf W) :=
          Subgroup.card_map_dvd (O.subgroupOf W) πW
      _ = Nat.card O := Nat.card_congr (subgroupOfEquivOfLe hOW).toEquiv
  have hnormal_bot : (O.subgroupOf W).map πW = ⊥ := by
    haveI : IsSimpleGroup ((W.subgroupOf A).map π) := hImgSimple
    haveI : ((O.subgroupOf W).map πW).Normal := hnormal
    rcases Subgroup.Normal.eq_bot_or_eq_top ((O.subgroupOf W).map πW) with hbot | htop
    · exact hbot
    · exfalso
      have htopOdd : Odd (Nat.card ((W.subgroupOf A).map π)) := by
        simpa [htop] using hOddImg
      haveI : IsSimpleGroup ((W.subgroupOf A).map π) := hImgSimple
      haveI : Group.IsPerfect ((W.subgroupOf A).map π) := hImgPerf
      exact (Group.IsPerfect.not_isSolvable ((W.subgroupOf A).map π))
        (CFSG.FeitThompson.isSolvable_of_odd_natCard _ htopOdd)
  have hOker : O.subgroupOf W ≤ πW.ker := by
    rw [← Subgroup.map_eq_bot_iff]
    exact hnormal_bot
  have hO_le_OA : O ≤ oddCoreIn A := by
    intro o ho
    have hoW : o ∈ W := hOW ho
    have hmem : (⟨o, hoW⟩ : W) ∈ O.subgroupOf W := ho
    have h1 : πW ⟨o, hoW⟩ = 1 := MonoidHom.mem_ker.mp (hOker hmem)
    have hx : ((subgroupOfEquivOfLe hWA).symm ⟨o, hoW⟩ : W.subgroupOf A) =
        ⟨⟨o, hWA hoW⟩, hoW⟩ := by
      apply Subtype.ext
      rfl
    have hker : (⟨o, hWA hoW⟩ : A) ∈ π.ker := by
      refine MonoidHom.mem_ker.mpr ?_
      have hval : π (((subgroupOfEquivOfLe hWA).symm ⟨o, hoW⟩ : W.subgroupOf A) : A) = 1 := by
        simpa [πW, eW] using congrArg Subtype.val h1
      rwa [hx] at hval
    have h2 : (⟨o, hWA hoW⟩ : A) ∈ pPrimeCore 2 A := by
      simpa [π, QuotientGroup.ker_mk'] using hker
    exact ⟨⟨o, hWA hoW⟩, h2, rfl⟩
  have hker : W ⊓ oddCoreIn A = O := by
    apply le_antisymm
    · apply le_oddCoreIn
      · exact inf_le_left
      · have hWnW : W ≤ normalizer (W : Set G) := le_normalizer
        have hWnO : W ≤ normalizer (oddCoreIn A : Set G) := by
          intro w hw
          exact mem_normalizer_oddCoreIn (le_normalizer (hWA hw))
        exact (le_inf hWnW hWnO).trans Subgroup.inf_normalizer_le_normalizer_inf
      · exact Odd.of_dvd_nat (odd_card_oddCoreIn A)
          (Subgroup.card_dvd_of_le inf_le_right)
    · exact le_inf hOW hO_le_OA
  have hW_le_sup : W ≤ P ⊔ O := by
    intro w hw
    have hwA : w ∈ A := hWA hw
    have hwImg : π ⟨w, hwA⟩ ∈ (P.subgroupOf A).map π := by
      rw [← hImgEq]
      exact ⟨⟨w, hwA⟩, hw, rfl⟩
    obtain ⟨p, hpP, hpπ⟩ := hwImg
    have hpP' : (p : G) ∈ P := hpP
    have hpW : (p : G) ∈ W := hPW hpP'
    have hkerA : ((p⁻¹ * ⟨w, hwA⟩ : A) : G) ∈ oddCoreIn A := by
      have hker : (p⁻¹ * ⟨w, hwA⟩ : A) ∈ π.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hpπ]
        simp
      have hker' : (p⁻¹ * ⟨w, hwA⟩ : A) ∈ pPrimeCore 2 A := by
        simpa [π, QuotientGroup.ker_mk'] using hker
      exact ⟨p⁻¹ * ⟨w, hwA⟩, hker', rfl⟩
    have hkerW : ((p⁻¹ * ⟨w, hwA⟩ : A) : G) ∈ W := by
      simpa using W.mul_mem (W.inv_mem hpW) hw
    have hkerO : ((p⁻¹ * ⟨w, hwA⟩ : A) : G) ∈ O := by
      rw [← hker]
      exact ⟨hkerW, hkerA⟩
    have hw_eq : w = (p : G) * ((p⁻¹ * ⟨w, hwA⟩ : A) : G) := by
      change w = (p : G) * ((p : G)⁻¹ * w)
      group
    rw [hw_eq]
    exact Subgroup.mul_mem_sup hpP' hkerO
  have hsup_le : P ⊔ O ≤ W := sup_le hPW hOW
  exact ⟨le_antisymm hW_le_sup hsup_le, hker, hAmbEq⟩

theorem exists_weakCorr_of_coreActionKernel {a b : G} {J : Subgroup G}
    (hJ : IsTwoComponentAt a J) (hb : orderOf b = 2)
    (hab : a * b = b * a) (hbJ : b ∈ coreActionKernel J) :
    ∃ H : Subgroup G, GrSLit.GSWeakCorr a J b H := by
  obtain ⟨ha, hJa, hJpc⟩ := hJ
  obtain ⟨hbN, hbcomm⟩ := mem_coreActionKernel.mp hbJ
  by_cases heq : a = b
  · subst b
    exact ⟨J, ha, ha, rfl, hJa, hJpc, hJa, hJpc, hbN, hbcomm,
      (UnbalancedGS.gsFixedLayer_le_inf J a).trans inf_le_left |>.trans le_sup_left⟩
  have hbCa : b ∈ centralizer ({a} : Set G) := mem_centralizer_singleton_iff.mpr hab.symm
  have hJsub : (J.subgroupOf (centralizer ({a} : Set G))).IsSubnormal := hJpc.choose_spec.2.1
  have hJq := isQuasisimple_quotient_of_isPComponent hJa hJpc
  have hFpc := UnbalancedCorr.gsFixedLayer_isPComponent hJa hJsub hbCa hb hbN hJq hbcomm
  have hFle : UnbalancedGS.gsFixedLayer J b ≤
      centralizer ({a} : Set G) ⊓ centralizer ({b} : Set G) :=
    le_inf ((UnbalancedGS.gsFixedLayer_le_inf J b).trans inf_le_left |>.trans hJa)
      ((UnbalancedGS.gsFixedLayer_le_inf J b).trans inf_le_right)
  have hFE : UnbalancedGS.gsFixedLayer J b ≤ twoLayerOf b :=
    le_twoLayerOf_of_isPComponent ha hab (by rwa [inf_comm]) (by rwa [inf_comm])
  obtain ⟨H, hHb, hHpc, hFH, -⟩ := UGSChain.exists_orbit_component_of_le_pLayer ha hab
    hFle hFpc hFE
  exact ⟨H, ha, hb, hab, hJa, hJpc, hHb, hHpc, hbN, hbcomm, hFH⟩

theorem exists_family_correspondent (family : Set (Subgroup G))
    (hIT : ∀ {z c : G} {S H : Subgroup G}, S ∈ family → GrSLit.GSWeakCorr z S c H →
      H ∈ family ∧ UnbalancedGS.gsFixedLayer S c ⊔ oddCoreIn H = H)
    {a b : G} {J : Subgroup G} (hJfam : J ∈ family) (hJ : IsTwoComponentAt a J)
    (hb : orderOf b = 2) (hab : a * b = b * a) (hbJ : b ∈ coreActionKernel J) :
    ∃ H ∈ family, IsTwoComponentAt b H ∧
      UnbalancedGS.gsFixedLayer J b ⊔ oddCoreIn H = H := by
  by_cases heq : a = b
  · subst b
    refine ⟨J, hJfam, hJ, ?_⟩
    have hfixed : UnbalancedGS.gsFixedLayer J a = J := by
      unfold UnbalancedGS.gsFixedLayer
      rw [inf_eq_left.mpr hJ.2.1]
      exact GrSLit.pLayer_eq_self_of_isPComponent hJ.2.1 hJ.2.2
    rw [hfixed]
    exact sup_eq_left.mpr (map_subtype_le _)
  · obtain ⟨H, hcorr⟩ := exists_weakCorr_of_coreActionKernel hJ hb hab hbJ
    obtain ⟨hHfam, hcover⟩ := hIT hJfam hcorr
    exact ⟨H, hHfam, ⟨hb, hcorr.2.2.2.2.2.1, hcorr.2.2.2.2.2.2.1⟩, hcover⟩

theorem twoComponent_eq_residual_oddCoreImage {H X : Subgroup G}
    (hH : IsTwoComponentIn H X) :
    H = (perfectResidual ↥(H ⊔ oddCoreIn X)).map (H ⊔ oddCoreIn X).subtype := by
  let Y := H ⊔ oddCoreIn X
  have hHY : H ≤ Y := le_sup_left
  have hRN : oddCoreIn X ≤ normalizer (H : Set G) :=
    UnbalancedCorr.pPrimeCore_le_normalizer_of_isPComponent hH.1 hH.2
  have hYN : Y ≤ normalizer (H : Set G) := sup_le le_normalizer hRN
  have hHnormal : (H.subgroupOf Y).Normal := normal_subgroupOf_of_le_normalizer hYN
  have hHperf : Group.IsPerfect H := GSThmB.B5a.isPerfect_of_isPComponent_subgroupOf hH.1 hH.2
  let R := (oddCoreIn X).subgroupOf Y
  have hRsolv : Group.IsSolvable R := by
    have hodd : Odd (Nat.card (oddCoreIn X)) := odd_card_oddCoreIn X
    have hcard := Nat.card_congr (subgroupOfEquivOfLe
      (show oddCoreIn X ≤ Y from le_sup_right)).toEquiv
    exact CFSG.FeitThompson.isSolvable_of_odd_natCard _ (hcard.symm ▸ hodd)
  let q := QuotientGroup.mk' (H.subgroupOf Y)
  have hqR : Function.Surjective (q.domRestrict R) := by
    intro z
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (H.subgroupOf Y) z
    have hy : y.val ∈ H ⊔ oddCoreIn X := y.property
    rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left H (oddCoreIn X) hRN] at hy
    obtain ⟨h, hh, r, hr, hhr⟩ := Set.mem_mul.mp hy
    have hyEq : y = (⟨h, hHY hh⟩ : Y) * ⟨r, mem_sup_right hr⟩ := Subtype.ext hhr.symm
    refine ⟨⟨⟨r, mem_sup_right hr⟩, hr⟩, ?_⟩
    change q ⟨r, mem_sup_right hr⟩ = q y
    rw [hyEq, map_mul, show q ⟨h, hHY hh⟩ = 1 from
      (QuotientGroup.eq_one_iff _).mpr hh, one_mul]
  have hquot : Group.IsSolvable (Y ⧸ H.subgroupOf Y) := by
    have := hRsolv
    exact Group.isSolvable_of_surjective hqR
  apply le_antisymm
  · exact CFSG.RankThreeCoreUniqueness.Helpers.perfect_subgroup_le_perfectResidualOf H Y
      hHperf hHY
  · have hle : perfectResidual Y ≤ H.subgroupOf Y :=
      ((perfect_residual_characterization (G := Y)).2.2.2.2.1 _).mp hquot
    exact (map_mono hle).trans (by rw [map_subgroupOf_eq_of_le hHY])

theorem cover_of_equal_oddCoreImage {F H X : Subgroup G}
    (hH : IsTwoComponentIn H X) (hF : Group.IsPerfect F) (hFX : F ≤ X)
    (himage : F ⊔ oddCoreIn X = H ⊔ oddCoreIn X) :
    F ≤ H ∧ F ⊔ oddCoreIn H = H ∧
      H = (perfectResidual ↥(F ⊔ oddCoreIn X)).map (F ⊔ oddCoreIn X).subtype := by
  have hcanonical := twoComponent_eq_residual_oddCoreImage hH
  have hFH : F ≤ H := by
    rw [hcanonical]
    exact CFSG.RankThreeCoreUniqueness.Helpers.perfect_subgroup_le_perfectResidualOf
      F _ hF (le_sup_left.trans himage.le)
  refine ⟨hFH, le_antisymm (sup_le hFH (map_subtype_le _)) ?_, by
    rw [himage]
    exact hcanonical⟩
  intro h hh
  have hhimage : h ∈ F ⊔ oddCoreIn X := himage.symm ▸ mem_sup_left hh
  have hFN : F ≤ normalizer (oddCoreIn X : Set G) := fun f hf =>
    mem_normalizer_oddCoreIn (le_normalizer (hFX hf))
  rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right F (oddCoreIn X) hFN] at hhimage
  obtain ⟨f, hf, r, hr, hfr⟩ := Set.mem_mul.mp hhimage
  have hrH : r ∈ H := by
    rw [show r = f⁻¹ * h by rw [← hfr]; group]
    exact H.mul_mem (H.inv_mem (hFH hf)) hh
  have hrOH : r ∈ oddCoreIn H := GSThmB.B5a.inf_oddCoreIn_le_of_le hH.1 ⟨hrH, hr⟩
  rw [← hfr]
  exact (F ⊔ oddCoreIn H).mul_mem (mem_sup_left hf) (mem_sup_right hrOH)

theorem recover_component_at_centralizing_involution
    {T : Type} [Group T] (family : Set (Subgroup G))
    (hocc : ∀ S ∈ family, ∃ z : G, IsTwoComponentAt z S)
    (hquot : ∀ S ∈ family, Nonempty (S ⧸ pPrimeCore 2 S ≃* T))
    (hIT : ∀ {z c : G} {S H : Subgroup G}, S ∈ family → GrSLit.GSWeakCorr z S c H →
      H ∈ family ∧ UnbalancedGS.gsFixedLayer S c ⊔ oddCoreIn H = H)
    {S : Subgroup G} (hS : S ∈ family) {a : G} (ha : orderOf a = 2)
    (haS : a ∈ centralizer (S : Set G)) :
    ∃ A ∈ family, IsTwoComponentAt a A ∧ S ≤ A ∧ S ⊔ oddCoreIn A = A ∧
      S ⊔ oddCoreOfCentralizer a = A ⊔ oddCoreOfCentralizer a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hzS⟩ := hocc S hS
  have hSperf : Group.IsPerfect S :=
    GSThmB.B5a.isPerfect_of_isPComponent_subgroupOf hzS.2.1 hzS.2.2
  let W := centralizer (S : Set G)
  let aW : W := ⟨a, haS⟩
  have haW : orderOf aW = 2 := (Subgroup.orderOf_coe aW).symm.trans ha
  have ha2 : IsPGroup 2 (zpowers aW) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, haW, pow_one])
  obtain ⟨P, hP⟩ := ha2.exists_le_sylow
  let Pbase : Subgroup G := (P : Subgroup W).map W.subtype
  have hPbaseW : Pbase ≤ W := map_subtype_le _
  have hPbaseSyl : ∃ Q : Sylow 2 W, (Q : Subgroup W) = Pbase.subgroupOf W :=
    ⟨P, (comap_map_eq_self_of_injective W.subtype_injective _).symm⟩
  have hzW : z ∈ W := by
    rw [mem_centralizer_iff]
    intro s hs
    exact mem_centralizer_singleton_iff.mp (hzS.2.1 hs)
  obtain ⟨g, hgW, hzgP⟩ := UnbalancedCorr.exists_conj_mem_of_sylow hPbaseSyl hzW hzS.1
  let z' := g⁻¹ * z * g
  have hgS : conjugate S g = S :=
    conjugate_eq_of_mem_normalizer (centralizer_le_normalizer _ hgW)
  have hz'S : IsTwoComponentAt z' S := by
    have h := isTwoComponentAt_map_mulEquiv (MulAut.conj g⁻¹) hzS
    have hmap : S.map (MulAut.conj g⁻¹).toMonoidHom = S := hgS
    simpa only [MulAut.conj_apply, inv_inv, z', hmap] using h
  have haP : a ∈ Pbase := ⟨aW, hP (mem_zpowers aW), rfl⟩
  have hP2 : IsPGroup 2 Pbase := P.isPGroup'.map W.subtype
  have hPnt : Nontrivial Pbase := by
    apply (nontrivial_iff_ne_bot Pbase).mpr
    intro hbot
    have ha1 : a = 1 := by simpa only [hbot, mem_bot] using haP
    rw [ha1, orderOf_one] at ha
    omega
  have := hPnt
  obtain ⟨cP, hcPZ, hcP⟩ :=
    CFSG.GroupTheory.SmallFixedTwoGroup.exists_mem_center_orderOf_eq_two hP2
  let c : G := cP
  have hc : orderOf c = 2 := (Subgroup.orderOf_coe cP).trans hcP
  have hcS : c ∈ centralizer (S : Set G) := hPbaseW cP.property
  have hcomm : ∀ x ∈ Pbase, c * x = x * c := by
    intro x hx
    exact congrArg Subtype.val ((mem_center_iff.mp hcPZ) ⟨x, hx⟩).symm
  have hcz' : z' * c = c * z' := (hcomm z' hzgP).symm
  have hca : c * a = a * c := hcomm a haP
  have hcSK : c ∈ coreActionKernel S := GSThmB.B5a.centralizer_le_coreActionKernel S hcS
  obtain ⟨H, hHfam, hHc, hHcover⟩ := exists_family_correspondent family hIT hS hz'S hc hcz' hcSK
  have hSc : S ≤ centralizer ({c} : Set G) := by
    intro s hs
    rw [mem_centralizer_singleton_iff]
    exact mem_centralizer_iff.mp hcS s hs
  have hfixedS : UnbalancedGS.gsFixedLayer S c = S := by
    unfold UnbalancedGS.gsFixedLayer
    rw [inf_eq_left.mpr hSc]
    exact GrSLit.pLayer_eq_self_of_isPComponent hz'S.2.1 hz'S.2.2
  rw [hfixedS] at hHcover
  have hSH : S ≤ H := le_sup_left.trans hHcover.le
  have hambient : S ⊔ oddCoreOfCentralizer c = H ⊔ oddCoreOfCentralizer c := by
    have hOH : oddCoreIn H ≤ oddCoreOfCentralizer c :=
      oddCoreIn_le_of_isTwoComponentIn hHc.2
    apply le_antisymm (sup_le_sup_right hSH _)
    exact sup_le (by rw [← hHcover]; exact sup_le le_sup_left (hOH.trans le_sup_right)) le_sup_right
  have hcanonical := (cover_of_equal_oddCoreImage hHc.2 hSperf
    (hSH.trans hHc.2.1) hambient).2.2
  have haH : a ∈ normalizer (H : Set G) := by
    rw [hcanonical]
    apply CFSG.RankThreeCoreUniqueness.Helpers.normalizer_le_normalizer_characteristic_map
      (S ⊔ oddCoreOfCentralizer c) _ CFSG.perfectResidual_characteristic'
    apply UnbalancedCorr.mem_normalizer_sup (centralizer_le_normalizer _ haS)
    exact mem_normalizer_oddCoreIn (le_normalizer (mem_centralizer_singleton_iff.mpr hca.symm))
  have haHK : a ∈ coreActionKernel H := mem_coreActionKernel_of_sup hSH hHcover haH
    (GSThmB.B5a.centralizer_le_coreActionKernel S haS)
  obtain ⟨A, hAfam, hAa, hAcover⟩ := exists_family_correspondent family hIT hHfam hHc ha hca haHK
  have hSa : S ≤ centralizer ({a} : Set G) := by
    intro s hs
    rw [mem_centralizer_singleton_iff]
    exact mem_centralizer_iff.mp haS s hs
  have hSfixed : S ≤ UnbalancedGS.gsFixedLayer H a := by
    change S ≤ twoLayerIn (H ⊓ centralizer ({a} : Set G))
    have haU : IsPGroup 2 (zpowers a) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha, pow_one])
    have hUK : zpowers a ≤ coreActionKernel H := zpowers_le.mpr haHK
    rw [← UnbalancedLayer.centralizer_zpowers_eq, fixed_twoLayer_eq_perfectResidual
      (isQuasisimple_quotient_of_isPComponent hHc.2.1 hHc.2.2) haU hUK]
    apply CFSG.RankThreeCoreUniqueness.Helpers.perfect_subgroup_le_perfectResidualOf
      S _ hSperf
    exact le_inf hSH (by rwa [UnbalancedLayer.centralizer_zpowers_eq])
  have hSA : S ≤ A := hSfixed.trans (le_sup_left.trans hAcover.le)
  obtain ⟨eS⟩ := hquot S hS
  obtain ⟨eA⟩ := hquot A hAfam
  have hScoverA : S ⊔ oddCoreIn A = A := sup_oddCoreIn_eq_of_card_le hSA
    (by rw [Nat.card_congr eS.toEquiv, Nat.card_congr eA.toEquiv])
  refine ⟨A, hAfam, hAa, hSA, hScoverA, le_antisymm (sup_le_sup_right hSA _) ?_⟩
  have hOA : oddCoreIn A ≤ oddCoreOfCentralizer a := oddCoreIn_le_of_isTwoComponentIn hAa.2
  exact sup_le (by rw [← hScoverA]; exact sup_le le_sup_left (hOA.trans le_sup_right)) le_sup_right

theorem recover_literal_oddCoreImage_witness
    {T : Type} [Group T] (family : Set (Subgroup G))
    (hocc : ∀ S ∈ family, ∃ z : G, IsTwoComponentAt z S)
    (hquot : ∀ S ∈ family, Nonempty (S ⧸ pPrimeCore 2 S ≃* T))
    (hIT : ∀ {z c : G} {S H : Subgroup G}, S ∈ family → GrSLit.GSWeakCorr z S c H →
      H ∈ family ∧ UnbalancedGS.gsFixedLayer S c ⊔ oddCoreIn H = H)
    {F S : Subgroup G} {a : G} (ha : orderOf a = 2) (hS : S ∈ family)
    (hFa : F ≤ centralizer ({a} : Set G))
    (himage : F ⊔ oddCoreOfCentralizer a = S ⊔ oddCoreOfCentralizer a) :
    ∃ A ∈ family, IsTwoComponentAt a A ∧
      F ⊔ oddCoreOfCentralizer a = A ⊔ oddCoreOfCentralizer a := by
  have hSa : S ≤ centralizer ({a} : Set G) :=
    le_sup_left.trans (himage.ge.trans (sup_le hFa (map_subtype_le _)))
  have haS : a ∈ centralizer (S : Set G) := by
    rw [mem_centralizer_iff]
    intro s hs
    exact mem_centralizer_singleton_iff.mp (hSa hs)
  obtain ⟨A, hA, hAa, -, -, hSA⟩ := recover_component_at_centralizing_involution
    family hocc hquot hIT hS ha haS
  exact ⟨A, hA, hAa, himage.trans hSA⟩

theorem Marked.exists_actual_witness {T : Type} [Group T]
    {family : Set (Subgroup G)} (hfamily : IsomorphicFamily family T)
    {M : Subgroup G} (hM : Marked family T M) :
    ∃ a : G, orderOf a = 2 ∧ a ∈ coreActionKernel M ∧
      ∃ A ∈ family, IsTwoComponentAt a A ∧
        fixedShadowAt M a ⊔ oddCoreOfCentralizer a = A ⊔ oddCoreOfCentralizer a := by
  obtain ⟨a, ha, haK, S, hS, himage⟩ := hM.2.2
  obtain ⟨A, hA, hAa, himageA⟩ := recover_literal_oddCoreImage_witness
    family hfamily.1 hfamily.2.1
    (fun {_ _ _ _} hJ hc => ⟨(hfamily.2.2.2 _ _ _ hJ _ hc).1,
      (hfamily.2.2.2 _ _ _ hJ _ hc).2.2⟩)
    ha hS ((map_subtype_le _).trans inf_le_right) himage
  exact ⟨a, ha, haK, A, hA, hAa, himageA⟩

theorem Marked.quotient_quasisimple {T : Type} [Group T]
    {family : Set (Subgroup G)} (hfamily : IsomorphicFamily family T)
    {M : Subgroup G} (hM : Marked family T M) : IsQuasisimple (M ⧸ pPrimeCore 2 M) := by
  obtain ⟨a, -, -, S, hS, -⟩ := hM.2.2
  obtain ⟨z, hzS⟩ := hfamily.1 S hS
  obtain ⟨eS⟩ := hfamily.2.1 S hS
  obtain ⟨eM⟩ := hM.2.1
  exact LocalCores.isQuasisimple_of_mulEquiv (eS.trans eM.symm)
    (isQuasisimple_quotient_of_isPComponent hzS.2.1 hzS.2.2)

theorem sup_oddCoreIn_eq_of_full_oddQuotient {T : Type*} [Group T]
    {K J : Subgroup G} (hKJ : K ≤ J)
    (hK : Nonempty (K ⧸ pPrimeCore 2 K ≃* T))
    (hJ : Nonempty (J ⧸ pPrimeCore 2 J ≃* T)) :
    K ⊔ oddCoreIn J = J := by
  obtain ⟨eK⟩ := hK
  obtain ⟨eJ⟩ := hJ
  exact FooteLit.sup_oddCoreIn_eq_of_card_le hKJ (by
    rw [Nat.card_congr eJ.toEquiv, Nat.card_congr eK.toEquiv])

theorem not_le_of_full_oddCoreQuotient_of_involution_centralizes
    {T : Type} [Group T] [IsSimpleGroup T]
    (hTnonab : ∃ a b : T, a * b ≠ b * a)
    {J K : Subgroup G} {x : G}
    (hJq : Nonempty (J ⧸ pPrimeCore 2 J ≃* T))
    (hKq : Nonempty (K ⧸ pPrimeCore 2 K ≃* T))
    (hxK : x ∈ K) (hx2 : orderOf x = 2)
    (hJx : J ≤ Subgroup.centralizer ({x} : Set G)) :
    ¬ J ≤ K := by
  classical
  intro hJK
  let π : K →* K ⧸ pPrimeCore 2 K := QuotientGroup.mk' (pPrimeCore 2 K)
  let xK : K := ⟨x, hxK⟩
  have hsup : J ⊔ oddCoreIn K = K :=
    sup_oddCoreIn_eq_of_full_oddQuotient hJK hJq hKq
  have hOD : (oddCoreIn K).subgroupOf K = pPrimeCore 2 K := by
    rw [FooteLit.oddCoreIn]
    exact Subgroup.comap_map_eq_self_of_injective K.subtype_injective (pPrimeCore 2 K)
  have htop : J.subgroupOf K ⊔ pPrimeCore 2 K = ⊤ := by
    rw [← hOD, ← Subgroup.subgroupOf_sup hJK
      (show oddCoreIn K ≤ K from map_subtype_le _), hsup, Subgroup.subgroupOf_self]
  have hker : (pPrimeCore 2 K).map π = ⊥ := by
    simp [π]
  have hmapJ : (J.subgroupOf K).map π = ⊤ := by
    calc (J.subgroupOf K).map π
        = (J.subgroupOf K).map π ⊔ (pPrimeCore 2 K).map π := by
            rw [hker, sup_bot_eq]
      _ = (J.subgroupOf K ⊔ pPrimeCore 2 K).map π := (Subgroup.map_sup _ _ π).symm
      _ = (⊤ : Subgroup K).map π := by rw [htop]
      _ = ⊤ := Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective _)
  have hcenter : π xK ∈ Subgroup.center (K ⧸ pPrimeCore 2 K) := by
    rw [Subgroup.mem_center_iff]
    intro z
    have hz : z ∈ (J.subgroupOf K).map π := by
      rw [hmapJ]
      exact Subgroup.mem_top z
    obtain ⟨j, hj, rfl⟩ := hz
    have hcomm : j * xK = xK * j := by
      refine Subtype.ext ?_
      simpa using (Subgroup.mem_centralizer_singleton_iff.mp (hJx hj))
    rw [← map_mul, ← map_mul, hcomm]
  obtain ⟨e⟩ := hKq
  have hZ : Subgroup.center T = ⊥ :=
    CFSG.LocalAnalysis.ComponentInitial.center_eq_bot_of_isSimpleGroup hTnonab
  have he : e (π xK) ∈ Subgroup.center T := by
    rw [← Subgroup.map_center_eq e]
    exact Subgroup.mem_map_of_mem e.toMonoidHom hcenter
  have he1 : e (π xK) = 1 := by
    rw [hZ, Subgroup.mem_bot] at he
    exact he
  have hπ1 : π xK = 1 := e.injective (by simpa using he1)
  have hxP : xK ∈ pPrimeCore 2 K :=
    (QuotientGroup.eq_one_iff xK).mp (by simpa [π] using hπ1)
  have hxO : x ∈ oddCoreIn K := by
    simpa [xK] using (FooteLit.mem_pPrimeCore_iff_mem_oddCoreIn xK).mp hxP
  have hdvd : orderOf x ∣ Nat.card (oddCoreIn K) := by
    simpa using Subgroup.orderOf_dvd_natCard (oddCoreIn K) hxO
  have h2dvd : 2 ∣ Nat.card (oddCoreIn K) := by
    rw [← hx2]
    exact hdvd
  exact (Nat.not_even_iff_odd.mpr (FooteLit.odd_card_oddCoreIn K))
    (even_iff_two_dvd.mpr h2dvd)

theorem transport_conjugate_witness {T : Type} [Group T]
    {family : Set (Subgroup G)} (hfamily : IsomorphicFamily family T)
    {M A : Subgroup G} (hM : Marked family T M) {a g : G}
    (haK : a ∈ coreActionKernel M) (hAfam : A ∈ family) (hAa : IsTwoComponentAt a A)
    (himage : fixedShadowAt M a ⊔ oddCoreOfCentralizer a = A ⊔ oddCoreOfCentralizer a)
    (hgM : g ∈ normalizer (M : Set G)) :
    conjugate A g ∈ family ∧ IsTwoComponentAt (g⁻¹ * a * g) (conjugate A g) ∧
      g⁻¹ * a * g ∈ coreActionKernel M ∧
      fixedShadowAt M (g⁻¹ * a * g) ⊔ oddCoreOfCentralizer (g⁻¹ * a * g) =
        conjugate A g ⊔ oddCoreOfCentralizer (g⁻¹ * a * g) := by
  let φ : G ≃* G := MulAut.conj g⁻¹
  have hMmap : M.map φ.toMonoidHom = M := conjugate_eq_of_mem_normalizer hgM
  have hAmap : A.map φ.toMonoidHom = conjugate A g := rfl
  have hAa' : IsTwoComponentAt (g⁻¹ * a * g) (conjugate A g) := by
    have h := isTwoComponentAt_map_mulEquiv φ hAa
    simpa only [φ, MulAut.conj_apply, inv_inv, hAmap] using h
  have haK' : g⁻¹ * a * g ∈ coreActionKernel M := by
    have h := FooteLit.conj_mem_coreActionKernel (inv_mem hgM) haK
    simpa only [inv_inv] using h
  refine ⟨hfamily.2.2.1 A hAfam g, hAa', haK', ?_⟩
  have hMq := hM.quotient_quasisimple hfamily
  have h := congrArg (map φ.toMonoidHom) himage
  rw [Subgroup.map_sup, Subgroup.map_sup,
    fixedShadowAt_eq_gsFixedLayer hMq hAa.1 haK,
    UGSChain.map_gsFixedLayer, hMmap,
    map_oddCoreOfCentralizer_mulEquiv, hAmap] at h
  have hφa : φ a = g⁻¹ * a * g := by simp only [φ, MulAut.conj_apply, inv_inv]
  rw [hφa, ← fixedShadowAt_eq_gsFixedLayer hMq hAa'.1 haK'] at h
  exact h

theorem transport_commuting_witness {T : Type} [Group T] [IsSimpleGroup T]
    {family : Set (Subgroup G)} (hfamily : IsomorphicFamily family T)
    {M A : Subgroup G} (hM : Marked family T M) {a b : G}
    (ha : orderOf a = 2) (haK : a ∈ coreActionKernel M)
    (hAfam : A ∈ family) (hAa : IsTwoComponentAt a A)
    (himage : fixedShadowAt M a ⊔ oddCoreOfCentralizer a = A ⊔ oddCoreOfCentralizer a)
    (hb : orderOf b = 2) (hbK : b ∈ coreActionKernel M) (hab : a * b = b * a) :
    ∃ B ∈ family, IsTwoComponentAt b B ∧
      fixedShadowAt M b ⊔ oddCoreOfCentralizer b = B ⊔ oddCoreOfCentralizer b := by
  obtain ⟨eM⟩ := hM.2.1
  obtain ⟨eA⟩ := hfamily.2.1 A hAfam
  have hTq : IsQuasisimple T := LocalCores.isQuasisimple_of_mulEquiv eA
    (isQuasisimple_quotient_of_isPComponent hAa.2.1 hAa.2.2)
  have hMq : IsQuasisimple (M ⧸ pPrimeCore 2 M) :=
    LocalCores.isQuasisimple_of_mulEquiv eM.symm hTq
  have hZa : IsPGroup 2 (zpowers a) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha, pow_one])
  have hZb : IsPGroup 2 (zpowers b) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hb, pow_one])
  let F := fixedShadowAt M a
  have hFperf : Group.IsPerfect F := fixedShadowAt_perfect M a
  have hFCa : F ≤ centralizer ({a} : Set G) := (map_subtype_le _).trans inf_le_right
  obtain ⟨hFA, hFcover, hcanonical⟩ := cover_of_equal_oddCoreImage hAa.2 hFperf hFCa himage
  have hbFN : b ∈ normalizer (F : Set G) := mem_normalizer_fixedShadowAt hbK.1 hab
  have hbFK : b ∈ coreActionKernel F :=
    mem_coreActionKernel_of_le (fixedShadowAt_le M a) hbFN hbK
  have hbAN : b ∈ normalizer (A : Set G) := by
    rw [hcanonical]
    apply CFSG.RankThreeCoreUniqueness.Helpers.normalizer_le_normalizer_characteristic_map
      (F ⊔ oddCoreOfCentralizer a) _ CFSG.perfectResidual_characteristic'
    exact UnbalancedCorr.mem_normalizer_sup hbFN
      (mem_normalizer_oddCoreIn (le_normalizer (mem_centralizer_singleton_iff.mpr hab.symm)))
  have hbAK : b ∈ coreActionKernel A := mem_coreActionKernel_of_sup hFA hFcover hbAN hbFK
  obtain ⟨B, hBfam, hBb, hBcover⟩ := exists_family_correspondent family
    (fun {_ _ _ _} hJ hc => ⟨(hfamily.2.2.2 _ _ _ hJ _ hc).1,
      (hfamily.2.2.2 _ _ _ hJ _ hc).2.2⟩) hAfam hAa hb hab hbAK
  obtain ⟨-, -, eFM, -⟩ := fixedShadow_cover_quotient hMq hZa (zpowers_le.mpr haK)
  let eF : F ⧸ pPrimeCore 2 F ≃* T := by
    rw [fixedShadow_zpowers] at eFM
    exact eFM.trans eM
  have hFq : IsQuasisimple (F ⧸ pPrimeCore 2 F) :=
    LocalCores.isQuasisimple_of_mulEquiv eF.symm hTq
  let D := fixedShadow F (zpowers b)
  obtain ⟨-, -, eDF, hDFmap⟩ := fixedShadow_cover_quotient hFq hZb (zpowers_le.mpr hbFK)
  let eD : D ⧸ pPrimeCore 2 D ≃* T := eDF.trans eF
  have hDperf : Group.IsPerfect D := fixedShadow_perfect _ _
  have hDb : D ≤ centralizer ({b} : Set G) := by
    have h := (fixedShadow_le_inf F (zpowers b)).trans inf_le_right
    rwa [UnbalancedLayer.centralizer_zpowers_eq] at h
  have hDAb : D ≤ UnbalancedGS.gsFixedLayer A b := by
    rw [← fixedShadowAt_eq_gsFixedLayer
      (isQuasisimple_quotient_of_isPComponent hAa.2.1 hAa.2.2) hb hbAK,
      ← fixedShadow_zpowers]
    apply le_fixedShadow_of_perfect hDperf
    exact le_inf ((fixedShadow_le F (zpowers b)).trans hFA)
      ((fixedShadow_le_inf F (zpowers b)).trans inf_le_right)
  have hDB : D ≤ B := hDAb.trans (le_sup_left.trans hBcover.le)
  obtain ⟨eB⟩ := hfamily.2.1 B hBfam
  have hDBcover : D ⊔ oddCoreIn B = B := sup_oddCoreIn_eq_of_card_le hDB (by
    rw [Nat.card_congr eB.toEquiv, Nat.card_congr eD.toEquiv])
  have hDMb : D ≤ fixedShadowAt M b := by
    rw [← fixedShadow_zpowers]
    exact le_fixedShadow_of_perfect hDperf (le_inf
      ((fixedShadow_le F (zpowers b)).trans (fixedShadowAt_le M a))
      ((fixedShadow_le_inf F (zpowers b)).trans inf_le_right))
  have hBMimage : B ≤ fixedShadowAt M b ⊔ oddCoreOfCentralizer b := by
    rw [← hDBcover]
    exact sup_le (hDMb.trans le_sup_left)
      ((oddCoreIn_le_of_isTwoComponentIn hBb.2).trans le_sup_right)
  obtain ⟨-, -, eMbM, -⟩ := fixedShadow_cover_quotient hMq hZb (zpowers_le.mpr hbK)
  rw [fixedShadow_zpowers] at eMbM
  refine ⟨B, hBfam, hBb, ?_⟩
  exact oddCoreImage_eq_of_contains_component hBb.2
    ((map_subtype_le _).trans inf_le_right)
    (by rw [← fixedShadow_zpowers]; exact fixedShadow_perfect _ _) eB (eMbM.trans eM) hBMimage

theorem Marked.witness_at_every_involution {T : Type} [Group T] [IsSimpleGroup T]
    {family : Set (Subgroup G)} (hfamily : IsomorphicFamily family T)
    {M : Subgroup G} (hM : Marked family T M) {u : G}
    (hu : orderOf u = 2) (huK : u ∈ coreActionKernel M) :
    ∃ A ∈ family, IsTwoComponentAt u A ∧
      fixedShadowAt M u ⊔ oddCoreOfCentralizer u = A ⊔ oddCoreOfCentralizer u := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha, haK, A, hAfam, hAa, himage⟩ := hM.exists_actual_witness hfamily
  let W := coreActionKernel M
  let uW : W := ⟨u, huK⟩
  have huW : orderOf uW = 2 := (Subgroup.orderOf_coe uW).symm.trans hu
  have hu2 : IsPGroup 2 (zpowers uW) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, huW, pow_one])
  obtain ⟨P, hP⟩ := hu2.exists_le_sylow
  let Pbase : Subgroup G := (P : Subgroup W).map W.subtype
  have hPbaseW : Pbase ≤ W := map_subtype_le _
  have hPbaseSyl : ∃ Q : Sylow 2 W, (Q : Subgroup W) = Pbase.subgroupOf W :=
    ⟨P, (comap_map_eq_self_of_injective W.subtype_injective _).symm⟩
  obtain ⟨g, hgW, hagP⟩ := UnbalancedCorr.exists_conj_mem_of_sylow hPbaseSyl haK ha
  obtain ⟨hBg, hBa', ha'K, himage'⟩ := transport_conjugate_witness hfamily hM
    haK hAfam hAa himage (mem_coreActionKernel.mp hgW).1
  let a' := g⁻¹ * a * g
  have huP : u ∈ Pbase := ⟨uW, hP (mem_zpowers uW), rfl⟩
  have hP2 : IsPGroup 2 Pbase := P.isPGroup'.map W.subtype
  have hPnt : Nontrivial Pbase := by
    apply (nontrivial_iff_ne_bot Pbase).mpr
    intro hbot
    have hu1 : u = 1 := by simpa only [hbot, mem_bot] using huP
    rw [hu1, orderOf_one] at hu
    omega
  have := hPnt
  obtain ⟨cP, hcPZ, hcP⟩ :=
    CFSG.GroupTheory.SmallFixedTwoGroup.exists_mem_center_orderOf_eq_two hP2
  let c : G := cP
  have hc : orderOf c = 2 := (Subgroup.orderOf_coe cP).trans hcP
  have hcK : c ∈ coreActionKernel M := hPbaseW cP.property
  have hcomm : ∀ x ∈ Pbase, c * x = x * c := by
    intro x hx
    exact congrArg Subtype.val ((mem_center_iff.mp hcPZ) ⟨x, hx⟩).symm
  obtain ⟨C, hCfam, hCc, himageC⟩ := transport_commuting_witness hfamily hM
    hBa'.1 ha'K hBg hBa' himage' hc hcK (hcomm a' hagP).symm
  exact transport_commuting_witness hfamily hM hc hcK hCfam hCc himageC
    hu huK (hcomm u huP)

theorem conjClosure_eq_of_perfect_odd_cover {P S E : Subgroup G}
    (hS : Group.IsPerfect S) (hPS : P ≤ S) (hcover : P ⊔ oddCoreIn S = S)
    (hSE : S ≤ E) (hEN : E ≤ normalizer (S : Set G)) : conjClosure P E = S := by
  let N := conjClosure P E
  have hNS : N ≤ S := Sol78.conjClosure_le hPS hEN
  have hPN : P ≤ N := FooteLit.le_conjClosure P E
  have hSN : S ≤ normalizer (N : Set G) := hSE.trans (Sol78.le_normalizer_conjClosure P E)
  have hNcover : N ⊔ oddCoreIn S = S := le_antisymm
    (sup_le hNS (map_subtype_le _))
    (hcover.ge.trans (sup_le_sup_right hPN _))
  have hNcoverS : N.subgroupOf S ⊔ pPrimeCore 2 S = ⊤ := by
    apply map_injective S.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hNS, Subgroup.map_top, range_subtype]
    exact hNcover
  have hON : pPrimeCore 2 S ≤ normalizer (N.subgroupOf S : Set S) := fun o _ =>
    UnbalancedLayer.mem_normalizer_subgroupOf_of_mem (hSN o.property)
  have : Group.IsPerfect S := hS
  have htop : Group.IsPerfect (⊤ : Subgroup S) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.topEquiv (G := S)).symm.toMonoidHom)
      (Subgroup.topEquiv (G := S)).symm.surjective
  have hle := UnbalancedLayer.le_of_perfect_le_sup_of_odd
    (Nat.coprime_two_left.mp (pPrimeCore_coprime_card (G := S) (p := 2))) hON htop hNcoverS.ge
  apply le_antisymm hNS
  intro s hs
  exact hle (mem_top (⟨s, hs⟩ : S))

theorem kernel_le_witness_kernel {M A U : Subgroup G} {a : G}
    (hAa : IsTwoComponentAt a A)
    (himage : fixedShadowAt M a ⊔ oddCoreOfCentralizer a = A ⊔ oddCoreOfCentralizer a)
    (hUK : U ≤ coreActionKernel M) (hUCa : U ≤ centralizer ({a} : Set G)) :
    U ≤ coreActionKernel A := by
  let F := fixedShadowAt M a
  obtain ⟨hFA, hcover, hcanonical⟩ := cover_of_equal_oddCoreImage hAa.2
    (fixedShadowAt_perfect M a) ((map_subtype_le _).trans inf_le_right) himage
  intro u hu
  have hau : a * u = u * a := (mem_centralizer_singleton_iff.mp (hUCa hu)).symm
  have huFN : u ∈ normalizer (F : Set G) := mem_normalizer_fixedShadowAt (hUK hu).1 hau
  have huAN : u ∈ normalizer (A : Set G) := by
    rw [hcanonical]
    apply CFSG.RankThreeCoreUniqueness.Helpers.normalizer_le_normalizer_characteristic_map
      (F ⊔ oddCoreOfCentralizer a) _ CFSG.perfectResidual_characteristic'
    exact UnbalancedCorr.mem_normalizer_sup huFN
      (mem_normalizer_oddCoreIn (le_normalizer (hUCa hu)))
  exact mem_coreActionKernel_of_sup hFA hcover huAN
    (mem_coreActionKernel_of_le (fixedShadowAt_le M a) huFN (hUK hu))

theorem fixedShadow_isTwoComponentIn_full {A U : Subgroup G} {a : G}
    (hAa : IsTwoComponentAt a A) (haU : a ∈ U)
    (hUCa : U ≤ centralizer ({a} : Set G)) (hU : IsPGroup 2 U)
    (hUKA : U ≤ coreActionKernel A) :
    IsTwoComponentIn (fixedShadow A U) (centralizer (U : Set G)) := by
  have hAq := isQuasisimple_quotient_of_isPComponent hAa.2.1 hAa.2.2
  obtain ⟨-, -, hpc⟩ := UnbalancedCorr.fixedLayer_facts hAa.2.1 hAa.2.2.choose_spec.2.1
    hUCa (fun u hu => (hUKA hu).1) hU hAq (fun u hu => (hUKA hu).2)
    (fixedShadow_eq_twoLayer hAq hU hUKA)
  have hClea : centralizer (U : Set G) ≤ centralizer ({a} : Set G) :=
    centralizer_le (Set.singleton_subset_iff.mpr haU)
  rw [inf_eq_right.mpr hClea] at hpc
  exact ⟨(fixedShadow_le_inf A U).trans inf_le_right, hpc⟩

theorem exists_odd_centralizer_map {U X : Subgroup G} (hUX : U ≤ X)
    (hCX : centralizer (U : Set G) ≤ X) (hU : IsPGroup 2 U) :
    ∃ q : centralizer (U : Set G) →*
        centralizer (((U.subgroupOf X).map (QuotientGroup.mk' (pPrimeCore 2 X))) :
          Set (X ⧸ pPrimeCore 2 X)),
      Function.Surjective q ∧ Odd (Nat.card q.ker) ∧
        ∀ c : centralizer (U : Set G),
          (q c : X ⧸ pPrimeCore 2 X) =
            (QuotientGroup.mk' (pPrimeCore 2 X)) ⟨c, hCX c.property⟩ := by
  let π := QuotientGroup.mk' (pPrimeCore 2 X)
  let E := U.subgroupOf X
  let C := centralizer (U : Set G)
  let Cx := centralizer (E : Set X)
  let Cbar := centralizer ((E.map π) : Set (X ⧸ pPrimeCore 2 X))
  have hCeq : C.subgroupOf X = Cx := by
    ext x
    change (x : G) ∈ centralizer (U : Set G) ↔ x ∈ centralizer (E : Set X)
    rw [mem_centralizer_iff, mem_centralizer_iff]
    constructor
    · intro h e he
      exact Subtype.ext (h e he)
    · intro h u hu
      exact congrArg Subtype.val (h ⟨u, hUX hu⟩ hu)
  have hE : IsPGroup 2 E := hU.comap_of_injective X.subtype X.subtype_injective
  have hmap : Cx.map π = Cbar := (GSThmB.OddQuot.centralizer_map_eq hE).symm
  let e : C ≃* Cx := (subgroupOfEquivOfLe hCX).symm.trans (MulEquiv.subgroupCongr hCeq)
  let q0 : Cx →* Cbar := (MulEquiv.subgroupCongr hmap).toMonoidHom.comp (π.subgroupMap Cx)
  let q : C →* Cbar := q0.comp e.toMonoidHom
  have hq : Function.Surjective q :=
    (MulEquiv.subgroupCongr hmap).surjective.comp
      ((π.subgroupMap_surjective Cx).comp e.surjective)
  have hformula : ∀ c : C, (q c : X ⧸ pPrimeCore 2 X) =
      π ⟨c, hCX c.property⟩ := fun _ => rfl
  have hqodd : Odd (Nat.card q.ker) := by
    let i : q.ker →* π.ker :=
      { toFun := fun c => ⟨⟨c.val, hCX c.val.property⟩, by
          have h := congrArg Subtype.val (MonoidHom.mem_ker.mp c.property)
          exact h⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hi : Function.Injective i := by
      intro c d h
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun x : π.ker => ((x : X) : G)) h
    have hπodd : Odd (Nat.card π.ker) := by
      rw [QuotientGroup.ker_mk']
      exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
    exact hπodd.of_dvd_nat (Subgroup.card_dvd_of_injective i hi)
  exact ⟨q, hq, hqodd, hformula⟩

theorem fixedShadow_canonical_odd_lift {T : Type} [Group T] [IsSimpleGroup T]
    {A U : Subgroup G} {a : G} (hAa : IsTwoComponentAt a A)
    (eA : A ⧸ pPrimeCore 2 A ≃* T) (haU : a ∈ U)
    (hUCa : U ≤ centralizer ({a} : Set G)) (hU : IsPGroup 2 U)
    (hUKA : U ≤ coreActionKernel A)
    (q : centralizer (U : Set G) →*
      centralizer (((U.subgroupOf (centralizer ({a} : Set G))).map
        (QuotientGroup.mk' (pPrimeCore 2 (centralizer ({a} : Set G))))) :
          Set ((centralizer ({a} : Set G)) ⧸ pPrimeCore 2 (centralizer ({a} : Set G)))))
    (hq : Function.Surjective q) (hqodd : Odd (Nat.card q.ker))
    (hformula : ∀ c : centralizer (U : Set G),
      (q c : (centralizer ({a} : Set G)) ⧸ pPrimeCore 2 (centralizer ({a} : Set G))) =
        (QuotientGroup.mk' (pPrimeCore 2 (centralizer ({a} : Set G))))
          ⟨c, centralizer_le (Set.singleton_subset_iff.mpr haU) c.property⟩) :
    let L := (fixedShadow A U).subgroupOf (centralizer (U : Set G))
    IsComponent (L.map q) ∧ Nonempty (L.map q ≃* T) ∧
      (L.map q).map (centralizer (((U.subgroupOf (centralizer ({a} : Set G))).map
        (QuotientGroup.mk' (pPrimeCore 2 (centralizer ({a} : Set G))))) :
          Set ((centralizer ({a} : Set G)) ⧸ pPrimeCore 2 (centralizer ({a} : Set G))))).subtype =
        (A.subgroupOf (centralizer ({a} : Set G))).map
          (QuotientGroup.mk' (pPrimeCore 2 (centralizer ({a} : Set G)))) ∧
      L = Subgroup.closure {x : centralizer (U : Set G) |
        x ∈ (L.map q).comap q ∧ ∃ k : ℕ, orderOf x = 2 ^ k} := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let X := centralizer ({a} : Set G)
  let C := centralizer (U : Set G)
  let π := QuotientGroup.mk' (pPrimeCore 2 X)
  let Cbar := centralizer (((U.subgroupOf X).map π) : Set (X ⧸ pPrimeCore 2 X))
  let S := fixedShadow A U
  let L := S.subgroupOf C
  let K := (A.subgroupOf X).map π
  have hCX : C ≤ X := centralizer_le (Set.singleton_subset_iff.mpr haU)
  have hScomp := fixedShadow_isTwoComponentIn_full hAa haU hUCa hU hUKA
  have hSC : S ≤ C := hScomp.1
  have hSA : S ≤ A := fixedShadow_le _ _
  have hSX : S ≤ X := hSA.trans hAa.2.1
  have hAq := isQuasisimple_quotient_of_isPComponent hAa.2.1 hAa.2.2
  obtain ⟨hcover, -, -, -⟩ := fixedShadow_cover_quotient hAq hU hUKA
  have hOAX : oddCoreIn A ≤ oddCoreIn X := oddCoreIn_le_of_isTwoComponentIn hAa.2
  have himage : S ⊔ oddCoreIn X = A ⊔ oddCoreIn X := by
    apply le_antisymm (sup_le_sup_right hSA _)
    apply sup_le _ le_sup_right
    rw [← hcover]
    exact sup_le le_sup_left (hOAX.trans le_sup_right)
  have himageX : S.subgroupOf X ⊔ pPrimeCore 2 X = A.subgroupOf X ⊔ pPrimeCore 2 X := by
    apply map_injective X.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_sup,
      map_subgroupOf_eq_of_le hSX, map_subgroupOf_eq_of_le hAa.2.1]
    exact himage
  have hcoremap : (pPrimeCore 2 X).map π = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  have hSimage : (S.subgroupOf X).map π = K := by
    have h := congrArg (map π) himageX
    simpa only [Subgroup.map_sup, hcoremap, sup_bot_eq] using h
  have hLimageX : L.map (inclusion hCX) = S.subgroupOf X := by
    apply map_injective X.subtype_injective
    rw [map_map, show X.subtype.comp (inclusion hCX) = C.subtype from rfl,
      map_subgroupOf_eq_of_le hSC, map_subgroupOf_eq_of_le hSX]
  have hqformula : Cbar.subtype.comp q = π.comp (inclusion hCX) := by
    ext c
    exact hformula c
  have hKmap : (L.map q).map Cbar.subtype = K := by
    rw [map_map, hqformula, ← map_map, hLimageX, hSimage]
  have hK : IsComponent K := (CatalogueBPrimeJoin.quotient_component_iff_core_quotient
    2 (A.subgroupOf X) hAa.2.2.choose_spec.2.1).mpr
      (CatalogueBHeldSmallCore.pComponent_coreQuotient_quasisimple 2 _ hAa.2.2)
  have hKCB : K ≤ Cbar := hKmap ▸ map_subtype_le _
  have hKsub : L.map q = K.subgroupOf Cbar := by
    have h := congrArg (comap Cbar.subtype) hKmap
    rw [comap_map_eq_self_of_injective Cbar.subtype_injective] at h
    exact h
  have hKlocal : IsComponent (L.map q) := by
    rw [hKsub]
    exact (CFSG.isComponent_iff_open _).mpr
      (LocalComponents.of_overgroup ((CFSG.isComponent_iff_open K).mp hK) hKCB)
  let eK : K ≃* T :=
    (CatalogueBHeldSmallCore.subnormalCoreQuotientEquivImage
      2 (A.subgroupOf X) hAa.2.2.choose_spec.2.1).symm.trans
        ((UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2
          (subgroupOfEquivOfLe hAa.2.1)).trans eA)
  let eL : L.map q ≃* T := ((L.map q).equivMapOfInjective Cbar.subtype
    Cbar.subtype_injective).trans ((MulEquiv.subgroupCongr hKmap).trans eK)
  obtain ⟨hbij, hcanon, -⟩ := CatalogueBPrimeJoin.prime_complement_quotient_p_component_bijection
    q hq (Nat.prime_two.coprime_iff_not_dvd.mp hqodd.coprime_two_left)
  have hKpc : IsPComponent 2 (L.map q) := hbij.mapsTo hScomp.2
  obtain ⟨hLift, hLiftmap⟩ := hcanon (L.map q) hKpc
  refine ⟨hKlocal, ⟨eL⟩, hKmap, ?_⟩
  exact hbij.injOn hScomp.2 hLift hLiftmap.symm

theorem markedST_of_isomorphicFamily {T : Type} [Group T] [IsSimpleGroup T]
    {family : Set (Subgroup G)} (hfamily : IsomorphicFamily family T) : MarkedST family T := by
  intro M hM U hU hUK hU0
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial U := (nontrivial_iff_ne_bot U).mpr hU0
  obtain ⟨uU, huZ, huU⟩ := CFSG.GroupTheory.SmallFixedTwoGroup.exists_mem_center_orderOf_eq_two hU
  let u : G := uU
  have hu : orderOf u = 2 := (Subgroup.orderOf_coe uU).trans huU
  have huMem : u ∈ U := uU.property
  have hUC : U ≤ centralizer ({u} : Set G) := by
    intro x hx
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val ((mem_center_iff.mp huZ) ⟨x, hx⟩))
  have hClea : centralizer (U : Set G) ≤ centralizer ({u} : Set G) :=
    centralizer_le (Set.singleton_subset_iff.mpr huMem)
  obtain ⟨A, hAfam, hAu, himage⟩ := hM.witness_at_every_involution hfamily hu (hUK huMem)
  obtain ⟨eA⟩ := hfamily.2.1 A hAfam
  have hUKA : U ≤ coreActionKernel A := kernel_le_witness_kernel hAu himage hUK hUC
  let C := centralizer (U : Set G)
  let S := fixedShadow A U
  have hScomp : IsTwoComponentIn S C := fixedShadow_isTwoComponentIn_full hAu huMem hUC hU hUKA
  obtain ⟨q, hq, hqodd, hqformula⟩ := exists_odd_centralizer_map hUC hClea hU
  obtain ⟨hKcomp, eK, hKimage, hcanonical⟩ := fixedShadow_canonical_odd_lift hAu eA
    huMem hUC hU hUKA q hq hqodd hqformula
  let L := S.subgroupOf C
  let Lcanon := Subgroup.closure {x : C | x ∈ (L.map q).comap q ∧ ∃ k : ℕ, orderOf x = 2 ^ k}
  have hcanonical' : L = Lcanon := hcanonical
  have hLift : Lcanon.map C.subtype = S := by
    rw [← hcanonical']
    exact map_subgroupOf_eq_of_le hScomp.1
  let P := fixedShadow M U
  have hPperf : Group.IsPerfect P := fixedShadow_perfect M U
  have hPmu : P ≤ fixedShadowAt M u := by
    rw [← fixedShadow_zpowers]
    apply le_fixedShadow_of_perfect hPperf
    rw [UnbalancedLayer.centralizer_zpowers_eq]
    exact (fixedShadow_le_inf M U).trans (inf_le_inf_left M hClea)
  have hmuA : fixedShadowAt M u ≤ A :=
    (cover_of_equal_oddCoreImage hAu.2 (fixedShadowAt_perfect M u)
      ((map_subtype_le _).trans inf_le_right) himage).1
  have hPS : P ≤ S := le_fixedShadow_of_perfect hPperf
    (le_inf (hPmu.trans hmuA) ((fixedShadow_le_inf M U).trans inf_le_right))
  have hMq := hM.quotient_quasisimple hfamily
  obtain ⟨eM⟩ := hM.2.1
  obtain ⟨-, -, ePM, hPMmap⟩ := fixedShadow_cover_quotient hMq hU hUK
  let eP : P ⧸ pPrimeCore 2 P ≃* T := ePM.trans eM
  have hAq := isQuasisimple_quotient_of_isPComponent hAu.2.1 hAu.2.2
  obtain ⟨hSAcover, -, eSA, hSAmap⟩ := fixedShadow_cover_quotient hAq hU hUKA
  let eS : S ⧸ pPrimeCore 2 S ≃* T := eSA.trans eA
  have hPScover : P ⊔ oddCoreIn S = S := sup_oddCoreIn_eq_of_card_le hPS (by
    rw [Nat.card_congr eS.toEquiv, Nat.card_congr eP.toEquiv])
  have hPcore : oddCoreIn P = P ⊓ oddCoreIn S := le_antisymm
    (le_inf (map_subtype_le _) (oddCoreIn_le_of_sup hPS hPScover))
    (GSThmB.B5a.inf_oddCoreIn_le_of_le hPS)
  obtain ⟨ePS, hPSmap⟩ := UnbalancedCorr.exists_quotient_equiv_of_sup hPS hPScover hPcore
  let f : P →* S ⧸ pPrimeCore 2 S :=
    (QuotientGroup.mk' (pPrimeCore 2 S)).comp (inclusion hPS)
  have hf : Function.Surjective f := by
    intro s
    obtain ⟨pbar, hpbar⟩ := ePS.surjective s
    obtain ⟨p, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 P) pbar
    exact ⟨p, (hPSmap p (inclusion hPS p) rfl).symm.trans hpbar⟩
  have hcoverFromMap : P ⊔ oddCoreIn S = S := by
    apply le_antisymm (sup_le hPS (map_subtype_le _))
    intro s hs
    obtain ⟨p, hp⟩ := hf ((QuotientGroup.mk' (pPrimeCore 2 S)) ⟨s, hs⟩)
    have hker : (inclusion hPS p)⁻¹ * (⟨s, hs⟩ : S) ∈ pPrimeCore 2 S := by
      apply (QuotientGroup.eq_one_iff _).mp
      change (QuotientGroup.mk' (pPrimeCore 2 S))
        ((inclusion hPS p)⁻¹ * (⟨s, hs⟩ : S)) = 1
      rw [map_mul, map_inv, show (QuotientGroup.mk' (pPrimeCore 2 S)) (inclusion hPS p) =
        (QuotientGroup.mk' (pPrimeCore 2 S)) ⟨s, hs⟩ from hp, inv_mul_cancel]
    have ho : (p : G)⁻¹ * s ∈ oddCoreIn S := mem_map_of_mem S.subtype hker
    rw [show s = (p : G) * ((p : G)⁻¹ * s) by group]
    exact (P ⊔ oddCoreIn S).mul_mem (mem_sup_left p.property) (mem_sup_right ho)
  have hSperf : Group.IsPerfect S := fixedShadow_perfect A U
  have hSCu : S ≤ centralizer ({u} : Set G) := hScomp.1.trans hClea
  have huCS : u ∈ centralizer (S : Set G) := by
    rw [mem_centralizer_iff]
    exact fun s hs => mem_centralizer_singleton_iff.mp (hSCu hs)
  have hSfixed : fixedShadowAt S u = S := by
    apply le_antisymm (fixedShadowAt_le S u)
    rw [← fixedShadow_zpowers]
    exact le_fixedShadow_of_perfect hSperf
      (le_inf le_rfl (by rwa [UnbalancedLayer.centralizer_zpowers_eq]))
  have hSimage : S ⊔ oddCoreOfCentralizer u = A ⊔ oddCoreOfCentralizer u := by
    apply le_antisymm (sup_le_sup_right (fixedShadow_le A U) _)
    apply sup_le _ le_sup_right
    exact hSAcover.ge.trans (sup_le
      (show S ≤ S ⊔ oddCoreOfCentralizer u from le_sup_left)
      ((oddCoreIn_le_of_isTwoComponentIn hAu.2).trans le_sup_right))
  have hSmarked : Marked family T S := ⟨hSperf, ⟨eS⟩, u, hu,
    GSThmB.B5a.centralizer_le_coreActionKernel S huCS, A, hAfam, by
      rw [hSfixed]
      exact hSimage⟩
  have hSLayer : S ≤ twoLayerIn C := by
    have h := map_mono (show S.subgroupOf C ≤ pLayer C 2 from le_sSup hScomp.2)
      (f := C.subtype)
    rwa [map_subgroupOf_eq_of_le hScomp.1] at h
  have hnormalClosure := conjClosure_eq_of_perfect_odd_cover hSperf hPS hcoverFromMap
    hSLayer (twoLayerIn_le_normalizer hScomp.1 hScomp.2)
  refine ⟨Lcanon.map C.subtype, ?_⟩
  rw [hLift]
  exact ⟨hScomp, hSmarked, hnormalClosure, hcoverFromMap⟩

end CFSG.ComponentClassification.FooteMarked
