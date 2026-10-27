module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5SolMirror
public import CFSG.LocalAnalysis.ComponentClassification.Foote5SolType

public section

namespace CFSG.ComponentClassification.Foote5.SolMax

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.Sol76

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem centralizer_zpowers' (t : G) :
    centralizer ((zpowers t : Subgroup G) : Set G) = centralizer ({t} : Set G) := by
  rw [zpowers_eq_closure, centralizer_closure]

omit [Finite G] in
theorem isPGroup_zpowers_of_orderOf {t : G} (ht : orderOf t = 2) : IsPGroup 2 (zpowers t) :=
  IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])

omit [Finite G] in
theorem centralizer_zpowers_sup (u t : G) :
    centralizer (((zpowers u ⊔ zpowers t : Subgroup G)) : Set G) =
      centralizer ({u} : Set G) ⊓ centralizer ({t} : Set G) := by
  ext x
  constructor
  · intro hx
    refine mem_inf.mpr ⟨?_, ?_⟩
    · rw [← centralizer_zpowers']
      exact centralizer_le (le_sup_left : zpowers u ≤ zpowers u ⊔ zpowers t) hx
    · rw [← centralizer_zpowers']
      exact centralizer_le (le_sup_right : zpowers t ≤ zpowers u ⊔ zpowers t) hx
  · intro hx
    obtain ⟨hxu, hxt⟩ := mem_inf.mp hx
    have hle : zpowers u ⊔ zpowers t ≤ centralizer ({x} : Set G) := by
      refine sup_le (zpowers_le.mpr ?_) (zpowers_le.mpr ?_)
      · rw [mem_centralizer_singleton_iff]
        exact (mem_centralizer_singleton_iff.mp hxu).symm
      · rw [mem_centralizer_singleton_iff]
        exact (mem_centralizer_singleton_iff.mp hxt).symm
    rw [mem_centralizer_iff]
    intro y hy
    exact mem_centralizer_singleton_iff.mp (hle hy)

theorem twoLayerIn_le_normalizer {X M : Subgroup G} (hM : IsTwoComponentIn M X) :
    twoLayerIn X ≤ normalizer (M : Set G) := by
  rintro _ ⟨y, hy, rfl⟩
  exact mem_normalizer_of_subgroupOf hM.1 (GrSLit.pLayer_le_normalizer_of_isPComponent hM.2 hy)

theorem le_coreActionKernel_of_le_sup {X V V' P T : Subgroup G} (hV : IsTwoComponentIn V X)
    (hV' : IsTwoComponentIn V' X) (hPVV : P ≤ V ⊔ V') (hTX : T ≤ X)
    (hTP : T ≤ normalizer (P : Set G)) (hTV : T ≤ coreActionKernel V)
    (hTV' : T ≤ coreActionKernel V') : T ≤ coreActionKernel P := by
  have hPX : P ≤ X := hPVV.trans (sup_le hV.1 hV'.1)
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥X) with hπ
  intro t ht
  refine ⟨hTP ht, fun p hp => ?_⟩
  have hcen : ∀ (U : Subgroup G) (hU : IsTwoComponentIn U X), T ≤ coreActionKernel U →
      U.subgroupOf X ≤ (centralizer ({π ⟨t, hTX ht⟩} : Set (↥X ⧸ pPrimeCore 2 ↥X))).comap π := by
    intro U hU hTU u hu
    rw [mem_comap, mem_centralizer_singleton_iff]
    have hu' : (u : G) ∈ U := mem_subgroupOf.mp hu
    have h1 := (hTU ht).2 u hu'
    have h2 := oddCoreIn_le_of_isTwoComponentIn hU h1
    obtain ⟨o, ho, hoe⟩ := h2
    have h3 : o = u⁻¹ * ⟨t, hTX ht⟩⁻¹ * u * ⟨t, hTX ht⟩ := Subtype.ext (by simpa using hoe)
    rw [h3] at ho
    rw [← map_mul, ← map_mul]
    refine (QuotientGroup.eq (s := pPrimeCore 2 ↥X)).mpr ?_
    have e : (u * ⟨t, hTX ht⟩)⁻¹ * (⟨t, hTX ht⟩ * u) =
        (u⁻¹ * ⟨t, hTX ht⟩⁻¹ * u * ⟨t, hTX ht⟩)⁻¹ := by group
    rw [e]
    exact inv_mem ho
  have hP' : P.subgroupOf X ≤
      (centralizer ({π ⟨t, hTX ht⟩} : Set (↥X ⧸ pPrimeCore 2 ↥X))).comap π := by
    intro x hx
    have hx' : (x : G) ∈ V ⊔ V' := hPVV (mem_subgroupOf.mp hx)
    have hle : V ⊔ V' ≤ ((centralizer ({π ⟨t, hTX ht⟩} : Set (↥X ⧸ pPrimeCore 2 ↥X))).comap
        π).map X.subtype := by
      refine sup_le (fun v hv => ?_) (fun v hv => ?_)
      · exact ⟨⟨v, hV.1 hv⟩, hcen V hV hTV (mem_subgroupOf.mpr hv), rfl⟩
      · exact ⟨⟨v, hV'.1 hv⟩, hcen V' hV' hTV' (mem_subgroupOf.mpr hv), rfl⟩
    obtain ⟨y, hy, hyx⟩ := hle hx'
    have : y = x := Subtype.ext hyx
    rw [← this]
    exact hy
  have hpc := hP' (x := ⟨p, hPX hp⟩) (mem_subgroupOf.mpr hp)
  rw [mem_comap, mem_centralizer_singleton_iff] at hpc
  have hyP : p⁻¹ * t⁻¹ * p * t ∈ P := by
    have h2 : t⁻¹ * p * t ∈ P := by
      have := (mem_normalizer_iff.mp (inv_mem (hTP ht)) p).mp hp
      simpa [mul_assoc] using this
    rw [show p⁻¹ * t⁻¹ * p * t = p⁻¹ * (t⁻¹ * p * t) by group]
    exact mul_mem (inv_mem hp) h2
  exact mem_oddCoreIn_of_mem_pPrimeCore hPX hyP
    (commutator_mem_pPrimeCore (hPX hp) (hTX ht) hpc)

omit [Finite G] in
theorem card_eq_of_reach {J M : Subgroup G} (hML : GSMirrorMaximal J) (h : GSMirrorReach J M) :
    Nat.card (↥M ⧸ Open.fusionZStar ↥M) = Nat.card (↥J ⧸ Open.fusionZStar ↥J) := by
  obtain ⟨e⟩ := hML M h
  exact (Nat.card_congr e.toEquiv).symm

theorem twoLayerIn_inf_centralizer_anti {L A B : Subgroup G}
    (hLq : IsQuasisimple (↥L ⧸ pPrimeCore 2 ↥L)) (hA2 : IsPGroup 2 A) (hB2 : IsPGroup 2 B)
    (hAQ : A ≤ coreActionKernel L) (hBQ : B ≤ coreActionKernel L) (hAB : A ≤ B) :
    twoLayerIn (L ⊓ centralizer (B : Set G)) ≤ twoLayerIn (L ⊓ centralizer (A : Set G)) := by
  obtain ⟨-, hLB, -, -⟩ := cover_facts hLq inf_le_left (inf_centralizer_sup_oddCoreIn_eq hB2 hBQ)
  obtain ⟨-, hLA, -, -⟩ := cover_facts hLq inf_le_left (inf_centralizer_sup_oddCoreIn_eq hA2 hAQ)
  rw [hLB, hLA]
  exact closure_mono fun x hx => ⟨inf_le_inf_left L (centralizer_le hAB) hx.1, hx.2⟩

omit [Finite G] in
theorem map_conj_conjugate_of_commute (V : Subgroup G) {x c : G} (hxc : x * c = c * x) :
    (conjugate V c).map (MulAut.conj x).toMonoidHom =
      conjugate (V.map (MulAut.conj x).toMonoidHom) c := by
  unfold conjugate
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext y
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  have h1 : x * c⁻¹ = c⁻¹ * x := by
    calc x * c⁻¹ = c⁻¹ * (c * x) * c⁻¹ := by group
      _ = c⁻¹ * (x * c) * c⁻¹ := by rw [hxc]
      _ = c⁻¹ * x := by group
  calc x * (c⁻¹ * y * c⁻¹⁻¹) * x⁻¹ = (x * c⁻¹) * y * (x * c⁻¹)⁻¹ := by group
    _ = (c⁻¹ * x) * y * (c⁻¹ * x)⁻¹ := by rw [h1]
    _ = c⁻¹ * (x * y * x⁻¹) * c⁻¹⁻¹ := by group

theorem reach_of_piece {J V P M : Subgroup G} {w c : G} (hw : orderOf w = 2) (hc : orderOf c = 2)
    (hwc : w * c = c * w) (hV : IsTwoComponentIn V (centralizer ({w} : Set G)))
    (hVcls : GSMirrorReach J V) (hPVV : P ≤ V ⊔ conjugate V c)
    (hfix : conjugate V c = V → c ∈ coreActionKernel V)
    (hP : IsTwoComponentIn P (centralizer ({w} : Set G) ⊓ centralizer ({c} : Set G)))
    (hM : IsTwoComponentIn M (centralizer ({c} : Set G))) (hPM : P ≤ M ⊔ conjugate M w) :
    GSMirrorReach J M := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hVc : conjugate V c = V
  · have hcV := hfix hVc
    obtain ⟨hcN, hcO⟩ := mem_coreActionKernel.mp hcV
    have hVq : IsQuasisimple (↥V ⧸ pPrimeCore 2 ↥V) :=
      ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 V _ hV.1).1 hV.2).2.2
    have hcw : c ∈ centralizer ({w} : Set G) := mem_centralizer_singleton_iff.mpr hwc.symm
    have hVsub : (V.subgroupOf (centralizer ({w} : Set G))).IsSubnormal := by
      obtain ⟨-, -, h, -, -⟩ := hV.2
      exact h
    have hFp := UnbalancedCorr.gsFixedLayer_isPComponent hV.1 hVsub hcw hc hcN hVq hcO
    set F := UnbalancedGS.gsFixedLayer V c with hFdef
    have hFle : F ≤ centralizer ({w} : Set G) ⊓ centralizer ({c} : Set G) :=
      (UnbalancedGS.gsFixedLayer_le_inf V c).trans (inf_le_inf_right _ hV.1)
    have hF : IsTwoComponentIn F (centralizer ({w} : Set G) ⊓ centralizer ({c} : Set G)) :=
      ⟨hFle, hFp⟩
    have hc2 : IsPGroup 2 (zpowers c) := isPGroup_zpowers_of_orderOf hc
    obtain ⟨-, hFeq, -, -⟩ := cover_facts hVq inf_le_left
      (inf_centralizer_sup_oddCoreIn_eq hc2 (zpowers_le.mpr hcV))
    have hPres : CatalogueBPrimeJoin.primeResidual 2 ↥P = ⊤ :=
      ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 P _ hP.1).1 hP.2).2.1
    have hPodd : oddResidualIn P = P := by
      rw [oddResidualIn_eq_map_primeResidual, hPres, ← MonoidHom.range_eq_map, range_subtype]
    have hPV : P ≤ V := by rw [hVc, sup_idem] at hPVV; exact hPVV
    have hPF : P ≤ F := by
      rw [centralizer_zpowers'] at hFeq
      have h1 : F = oddResidualIn (V ⊓ centralizer ({c} : Set G)) := hFeq
      rw [h1, ← hPodd]
      exact closure_mono fun x hx => ⟨mem_inf.mpr ⟨hPV hx.1, (mem_inf.mp (hP.1 hx.1)).2⟩, hx.2⟩
    have hPeq : P = F := eq_of_le_of_isTwoComponentIn hP hF hPF
    have hC : GrSLit.GSWeakCorr w V c M :=
      ⟨hw, hc, hwc, hV.1, hV.2, hM.1, hM.2, hcN, hcO,
        by rw [show UnbalancedGS.gsFixedLayer V c = P from hPeq.symm]; exact hPM⟩
    exact hVcls.tail_corr hC
  · exact hVcls.tail_mirror ⟨w, c, P, hw, hc, hwc, hV, hVc, hM, hP, hPVV, hPM⟩

end CFSG.ComponentClassification.Foote5.SolMax
