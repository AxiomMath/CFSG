module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBHypB2
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58NFb
public import CFSG.Goldschmidt.Steps.G37Basic
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7OS1

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

namespace Hyp52

variable {H : Type} [Group H] [Finite H]

abbrev fixedLayerOdd (h : Hyp52 H) : Subgroup H := GSLit.fixedLayer h.J h.B ⊔ oddCoreIn h.W

structure QSylow36 (h : Hyp52 H) : Prop where
  oddTwoCore_eq : (oddTwoCore ↥h.W).map h.W.subtype = oddCoreIn h.W ⊔ h.B
  isSylowIn : Seven.IsSylowIn h.Q (h.W ⊓ normalizer (h.fixedLayerOdd : Set H))

theorem wbarMk_eq_one_of_mem_B (h : Hyp52 H)
    (hN : (oddTwoCore ↥h.W).map h.W.subtype = oddCoreIn h.W ⊔ h.B) {β : H} (hβ : β ∈ h.B) :
    wbarMk h.B ⟨β, le_normalizer hβ⟩ = 1 := by
  have h1 : β ∈ (oddTwoCore ↥h.W).map h.W.subtype := by
    rw [hN]
    exact mem_sup_right hβ
  obtain ⟨o, ho, hoβ⟩ := h1
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have : o = ⟨β, le_normalizer hβ⟩ := Subtype.ext hoβ
  rw [← this]
  exact ho

theorem wbarMk_mem_centralizer_of_fuse (h : Hyp52 H)
    (hN : (oddTwoCore ↥h.W).map h.W.subtype = oddCoreIn h.W ⊔ h.B) {w : H} (hwN : w ∈ h.W)
    {β : H} (hβ : β ∈ h.B) (hwa : w * h.a * w⁻¹ = β * h.a) :
    wbarMk h.B ⟨w, hwN⟩ ∈
      centralizer ({wbarMk h.B ⟨h.a, h.a_mem_normalizer⟩} : Set (Wbar h.B)) := by
  rw [mem_centralizer_singleton_iff]
  have h1 : (⟨w, hwN⟩ : ↥h.W) * ⟨h.a, h.a_mem_normalizer⟩ * (⟨w, hwN⟩ : ↥h.W)⁻¹ =
      ⟨β, le_normalizer hβ⟩ * ⟨h.a, h.a_mem_normalizer⟩ := Subtype.ext (by simpa using hwa)
  have h2 := congrArg (wbarMk h.B) h1
  rw [map_mul, map_mul, map_inv, map_mul, h.wbarMk_eq_one_of_mem_B hN hβ, one_mul] at h2
  set v := wbarMk h.B ⟨w, hwN⟩
  set u := wbarMk h.B ⟨h.a, h.a_mem_normalizer⟩
  calc v * u = v * u * v⁻¹ * v := by group
    _ = u * v := by rw [h2]

theorem mem_normalizer_wbarJB (h : Hyp52 H) {v : Wbar h.B}
    (hv : v ∈ centralizer ({wbarMk h.B ⟨h.a, h.a_mem_normalizer⟩} : Set (Wbar h.B))) :
    v ∈ normalizer ((wbarImage h.B (GSLit.fixedLayer h.J h.B) : Subgroup (Wbar h.B)) :
      Set (Wbar h.B)) := by
  set C := centralizer ({wbarMk h.B ⟨h.a, h.a_mem_normalizer⟩} : Set (Wbar h.B)) with hC
  set L := wbarImage h.B (GSLit.fixedLayer h.J h.B) with hL
  obtain ⟨hLC, hLcomp⟩ := h.isComponent_bar
  have hL'C : conjugate L v ≤ C := by
    intro y hy
    rw [mem_conjugate_iff] at hy
    have h1 := mul_mem (mul_mem (inv_mem hv) (hLC hy)) hv
    rwa [show v⁻¹ * (v * y * v⁻¹) * v = y by group] at h1
  have hL'comp : IsComponent ((conjugate L v).subgroupOf C) := by
    rw [← conjugate_subgroupOf_eq L C ⟨v, hv⟩]
    exact isComponent_conjugate hLcomp _
  rcases LocalCores.distinct_components_commute hLcomp hL'comp with heq | hcomm
  · apply mem_normalizer_of_conjugate_eq
    have h1 := Subgroup.subgroupOf_inj.mp heq
    rw [inf_of_le_left hLC, inf_of_le_left hL'C] at h1
    exact h1.symm
  · exfalso
    apply h.isStandard_bar.2.2.2.2 v
    have h1 := congrArg (Subgroup.map C.subtype) hcomm
    rwa [map_commutator, map_subgroupOf_eq_of_le hLC, map_subgroupOf_eq_of_le hL'C,
      Subgroup.map_bot] at h1

theorem mem_normalizer_fixedLayerOdd (h : Hyp52 H)
    (hN : (oddTwoCore ↥h.W).map h.W.subtype = oddCoreIn h.W ⊔ h.B) {w : H} (hwN : w ∈ h.W)
    (hwJ : wbarMk h.B ⟨w, hwN⟩ ∈ normalizer ((wbarImage h.B (GSLit.fixedLayer h.J h.B) :
      Subgroup (Wbar h.B)) : Set (Wbar h.B))) :
    w ∈ normalizer (h.fixedLayerOdd : Set H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set JB := GSLit.fixedLayer h.J h.B with hJB
  set O := oddCoreIn h.W with hO
  have hJBC : JB ≤ centralizer (h.B : Set H) :=
    (GSLit.fixedLayer_le_inf h.J h.B).trans inf_le_right
  have hJBW : JB ≤ h.W := hJBC.trans (centralizer_le_normalizer _)
  have hconj : conjugate JB w⁻¹ ≤ h.B ⊔ h.fixedLayerOdd := by
    intro y hy
    rw [mem_conjugate_iff, inv_inv] at hy
    have hyW : y ∈ h.W := by
      have h1 := mul_mem (mul_mem hwN (hJBW hy)) (inv_mem hwN)
      rwa [show w * (w⁻¹ * y * w) * w⁻¹ = y by group] at h1
    have hmem : wbarMk h.B ⟨y, hyW⟩ ∈ wbarImage h.B JB := by
      have h1 : wbarMk h.B ⟨w⁻¹ * y * w, hJBW hy⟩ ∈ wbarImage h.B JB :=
        ⟨⟨w⁻¹ * y * w, hJBW hy⟩, hy, rfl⟩
      have h2 := (mem_normalizer_iff.mp hwJ _).mp h1
      have h3 : (⟨y, hyW⟩ : ↥h.W) =
          ⟨w, hwN⟩ * ⟨w⁻¹ * y * w, hJBW hy⟩ * (⟨w, hwN⟩ : ↥h.W)⁻¹ :=
        Subtype.ext (by simp only [coe_mul, coe_inv]; group)
      rw [h3, map_mul, map_mul, map_inv]
      exact h2
    obtain ⟨j', hj', hj'y⟩ := hmem
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hj'y
    have h3 : ((j'⁻¹ * ⟨y, hyW⟩ : ↥h.W) : H) ∈ O ⊔ h.B := by
      rw [hO, ← hN]
      exact ⟨_, hj'y, rfl⟩
    have h4 : y = (j' : H) * ((j'⁻¹ * ⟨y, hyW⟩ : ↥h.W) : H) := by
      simp only [coe_mul, coe_inv, mul_inv_cancel_left]
    rw [h4]
    have h5 : O ⊔ h.B ≤ h.B ⊔ h.fixedLayerOdd :=
      sup_le (le_sup_right.trans le_sup_right) le_sup_left
    exact mul_mem (mem_sup_right (mem_sup_left (mem_subgroupOf.mp hj'))) (h5 h3)
  have hJBperf : Group.IsPerfect JB :=
    B5a.isPerfect_of_isPComponent_subgroupOf
      ((GSLit.fixedLayer_le_inf h.J h.B).trans (inf_le_inf_right _ h.J_le))
      (B5a.isPComponent_fixedLayer h)
  have hperf : Group.IsPerfect (conjugate JB w⁻¹) := by
    show Group.IsPerfect (JB.map (MulAut.conj w⁻¹⁻¹).toMonoidHom)
    exact Group.IsPerfect.map _
  have hBN : h.B ≤ normalizer (h.fixedLayerOdd : Set H) := fun b hb =>
    OS1.mem_normalizer_sup
      (centralizer_le_normalizer _ (Subgroup.le_centralizer_iff.mp hJBC hb))
      (B5a.mem_normalizer_oddCoreIn (le_normalizer (le_normalizer hb)))
  have hBs : Group.IsSolvable ↥h.B := by
    have := h.isPGroup_B.isNilpotent
    infer_instance
  have hle1 : conjugate JB w⁻¹ ≤ h.fixedLayerOdd :=
    Goldschmidt.G37.le_of_perfect_of_le_sup hperf hconj hBN hBs
  have hOw : conjugate O w⁻¹ = O :=
    conjugate_eq_of_mem_normalizer (B5a.mem_normalizer_oddCoreIn (le_normalizer (inv_mem hwN)))
  have hle : conjugate h.fixedLayerOdd w⁻¹ ≤ h.fixedLayerOdd := by
    show (JB ⊔ O).map (MulAut.conj w⁻¹⁻¹).toMonoidHom ≤ JB ⊔ O
    rw [Subgroup.map_sup]
    exact sup_le hle1 (hOw.le.trans le_sup_right)
  have heq : conjugate h.fixedLayerOdd w⁻¹ = h.fixedLayerOdd :=
    Subgroup.eq_of_le_of_card_ge hle
      (Subgroup.card_map_of_injective (f := (MulAut.conj w⁻¹⁻¹).toMonoidHom)
        (MulAut.conj w⁻¹⁻¹).injective).ge
  have h1 := inv_mem (mem_normalizer_of_conjugate_eq heq)
  rwa [inv_inv] at h1

theorem noFusionW_of_qSylow36 (h : Hyp52 H) (hq : h.QSylow36) : h.NoFusionW := by
  intro w hwN hwQ R hR hwR _ β hβ hwa
  have hv := h.wbarMk_mem_centralizer_of_fuse hq.oddTwoCore_eq hwN hβ hwa
  have hwX := h.mem_normalizer_fixedLayerOdd hq.oddTwoCore_eq hwN (h.mem_normalizer_wbarJB hv)
  have hw2 : IsPGroup 2 (zpowers w) := hR.to_le (zpowers_le.mpr hwR)
  have hwQ' : w ∈ h.Q := OS1.mem_of_isSylowIn hq.isSylowIn (mem_inf.mpr ⟨hwN, hwX⟩) hwQ hw2
  exact h.comm_a (mem_inf.mp hwQ').1

end Hyp52

section Inputs

open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open scoped Pointwise

variable {X : Type} [Group X] [Finite X]

theorem Hyp52.qSylow36_of_inputs (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hCTI : LayerGeneratedUniversalComponentStandard) [IsSimpleGroup X]
    (hnonab : ∃ u v : X, u * v ≠ v * u) (hK : Assembly.KProper Blueprint.Catalog X)
    (h : Hyp52 X) (hmax : GSMaximalUnbalancingTriple h.a h.x h.J) (hiso : GSIsoAt h.a h.J)
    (hnB2a : ¬ ConclusionB2a h.a h.J) : h.QSylow36 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ha := h.orderOf_a
  have hJa := h.J_le
  have hJpc := h.isPComponent_J
  have hSX := h.S_le
  have hSsyl := h.S_sylow
  set d : Subgroup X → ℕ := fun W =>
    Nat.card ((↥W ⧸ pPrimeCore 2 ↥W) ⧸ center (↥W ⧸ pPrimeCore 2 ↥W)) with hd
  have hA2 := actual_two_local_fixed_layer_orbits_of_inputs hS hU hheld hnonab hK ha hJa hJpc hSX
    hSsyl rfl
    (fun B => normalizer (B : Set X)) (fun B => oddCoreIn (normalizer (B : Set X)))
    (fun B => GSLit.fixedLayer h.J B)
    (fun B => GSLit.fixedLayer h.J B ⊔ oddCoreIn (normalizer (B : Set X)))
    (fun B => layerIn (normalizer (B : Set X)))
    (fun B => conjClosure (GSLit.fixedLayer h.J B) (layerIn (normalizer (B : Set X))))
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    d (fun _ => rfl)
  have hbad : ∀ L : Subgroup X, ¬ IsoCorrSub h.a h.J h.B L := fun L hL =>
    commutator_ne_of_isoCorrSub hL (by rw [h.conjClosure_eq]; exact h.commutator_eq)
  have hbadB : d h.J < d (conjClosure (GSLit.fixedLayer h.J h.B)
      (layerIn (normalizer (h.B : Set X)))) := by
    obtain ⟨-, -, -, -, -, -, -, ⟨M, -, -, -, hVM, hVE, -, hdle, hdiff, hdeq, -, -⟩, -⟩ :=
      hA2.1 h.B h.B_ne_bot h.B_le
    by_contra hnot
    have heq : d (conjClosure (GSLit.fixedLayer h.J h.B) (layerIn (normalizer (h.B : Set X)))) =
        d h.J := le_antisymm (not_lt.mp hnot) hdle
    obtain ⟨hVpc, hTO, hTfix⟩ := hdeq heq
    obtain ⟨hMMa, -⟩ := hdiff.mp heq
    set V₂ := conjClosure (GSLit.fixedLayer h.J h.B) (layerIn (normalizer (h.B : Set X)))
    have hVle : V₂ ≤ normalizer (h.B : Set X) := hVE.trans (map_subtype_le _)
    have hVM' : V₂ = M := by rw [hVM, ← hMMa, sup_idem]
    have hVa : conjugate V₂ h.a = V₂ := by rw [hVM', ← hMMa]
    apply hbad V₂
    refine ⟨hVle, hVpc, hVa, ?_, hTfix⟩
    apply le_antisymm
    · refine sup_le (fun t ht => ?_) (map_subtype_le _)
      have h5 : t ∈ ((GSLit.fixedLayer h.J h.B : Set X) *
          ((pPrimeCore 2 ↥V₂).map V₂.subtype : Set X)) :=
        ⟨t, ht, 1, one_mem _, mul_one t⟩
      rw [hTO] at h5
      exact h5
    · intro v hv
      have hv' : v ∈ (V₂ : Set X) := hv
      rw [← hTO] at hv'
      obtain ⟨t, ht, o, ho, rfl⟩ := hv'
      exact mul_mem (mem_sup_left ht) (mem_sup_right ho)
  have hlex : ∀ C : Subgroup X, C ≠ ⊥ → C ≤ h.S ⊓ coreActionKernel h.J →
      d h.J < d (conjClosure (GSLit.fixedLayer h.J C) (layerIn (normalizer (C : Set X)))) →
      Nat.card C < Nat.card h.B ∨ (Nat.card C = Nat.card h.B ∧
        Nat.card ↥(h.S ⊓ normalizer (C : Set X)) ≤
          Nat.card ↥(h.S ⊓ normalizer (h.B : Set X))) := by
    intro C hC hCP hCbad
    by_contra hcon
    push Not at hcon
    obtain ⟨hle, hlt⟩ := hcon
    have hlex' : Nat.card h.B < Nat.card C ∨ (Nat.card C = Nat.card h.B ∧
        Nat.card ↥(h.S ⊓ normalizer (h.B : Set X)) <
          Nat.card ↥(h.S ⊓ normalizer (C : Set X))) := by
      rcases Nat.lt_or_ge (Nat.card h.B) (Nat.card C) with h1 | h1
      · exact Or.inl h1
      · have hCeq : Nat.card C = Nat.card h.B := le_antisymm h1 hle
        exact Or.inr ⟨hCeq, hlt hCeq⟩
    obtain ⟨L, hL⟩ := h.isoCorr_of_lt C hCP hlex'
    obtain ⟨-, -, -, -, -, -, -, ⟨-, -, -, -, -, -, -, -, -, -, hltiff, -⟩, -⟩ :=
      hA2.1 C hC hCP
    exact commutator_ne_of_isoCorrSub hL (hltiff.mp hCbad)
  have hb : ∃ b : X, orderOf b = 2 ∧ b ∈ h.S ⊓ coreActionKernel h.J ∧
      ∀ M : Subgroup X, ¬ UnbalancedGS.GSIsoCorr h.a h.J b M := by
    by_contra hcon
    push Not at hcon
    exact hnB2a (conclusionB2a_of_sylow hSsyl fun b hb hb2 => hcon b hb2 hb)
  have hJ2 : 2 ≤ pRank 2 ↥h.J := by
    have htype' : 2 ≤ pRank 2 ↥h.J ∨
        (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
          Assembly.LowTwoRank.StatedClassicalModel (h.J ⧸ pPrimeCore 2 h.J) .PSL 2 p f) ∨
        Nonempty (h.J ⧸ pPrimeCore 2 h.J ≃* alternatingGroup (Fin 7)) ∨
        Assembly.LowTwoRank.StatedClassicalModel (h.J ⧸ Open.fusionZStar h.J) .PSL 3 2 2 := by
      rcases h.smallType with h7 | ⟨p, f, hp, hp2, hf, -, hm⟩ | h34
      · exact Or.inr (Or.inr (Or.inl h7))
      · exact Or.inr (Or.inl ⟨p, f, hp, hp2, hf, GSLit.statedClassicalModel_of_lieModel_psl_two hm⟩)
      · exact Or.inr (Or.inr (Or.inr (GSLit.statedClassicalModel_of_lieModel_psl_three h34)))
    rcases htype' with h2 | hsmall
    · exact h2
    let e : h.J ⧸ oddCore h.J ≃* h.J ⧸ pPrimeCore 2 h.J :=
      QuotientGroup.quotientMulEquivOfEq (GSLit.oddCore_eq_pPrimeCore_two h.J)
    have hq : IsQuasisimple (h.J ⧸ pPrimeCore 2 h.J) :=
      CatalogueBPrimeJoin.quasisimple_primeCore_quotient_of_equiv 2 (subgroupOfEquivOfLe hJa)
        (CatalogueBHeldSmallCore.pComponent_coreQuotient_quasisimple 2 _ hJpc)
    have hA : IsQuasisimple (h.J ⧸ oddCore h.J) := LocalCores.isQuasisimple_of_mulEquiv e.symm hq
    refine UnbalancedGS.small_source_models_force_rank_at_least_two hA ?_
    rcases hsmall with ⟨p, f, hp, hp2, hf, hm⟩ | h7 | h34
    · exact Or.inl ⟨p, f, hp, hp.odd_of_ne_two hp2, hf,
        SectionRank.statedClassicalModel_of_mulEquiv e hm⟩
    · obtain ⟨e7⟩ := h7
      exact Or.inr (Or.inl ⟨e.trans e7⟩)
    · exact Or.inr (Or.inr h34)
  obtain ⟨_haH, h1, -⟩ :=
    critical_local_quotient_standard_component_at_of_inputs hS hU hheld hCTI hnonab hK ha hJa
      hJpc hSX hSsyl rfl
      (fun B => normalizer (B : Set X)) (fun B => oddCoreIn (normalizer (B : Set X)))
      (fun B => GSLit.fixedLayer h.J B)
      (fun B => GSLit.fixedLayer h.J B ⊔ oddCoreIn (normalizer (B : Set X)))
      (fun B => layerIn (normalizer (B : Set X)))
      (fun B => conjClosure (GSLit.fixedLayer h.J B) (layerIn (normalizer (B : Set X))))
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      d (fun _ => rfl)
      (fun z hz hzP hzS => (sylow_fixed_core_of_central hmax hiso hSX hSsyl hz
        (mem_inf.mp hzP).1 (mem_inf.mp hzP).2 (fun s hs => mem_centralizer_iff.mp hzS s hs) _
        rfl).2)
      hb hJ2 h.B h.B_ne_bot h.B_le hbadB hlex
  obtain ⟨hN, -, -, -, -, -, -, -, hQle, hQsyl⟩ := h1
  exact ⟨hN, hQle, hQsyl⟩

theorem noFusionW_of_inputs (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hCTI : LayerGeneratedUniversalComponentStandard) :
    ∀ (X : Type) [Group X] [Finite X] (h : Hyp52 X), NF58Setting X h → h.NoFusionW := by
  intro X _ _ h hs
  obtain ⟨hsimp, hnonab, hK, -, -, hmax, hiso, -, hnB2a⟩ := hs
  have := hsimp
  exact h.noFusionW_of_qSylow36 (h.qSylow36_of_inputs hS hU hheld hCTI hnonab hK hmax hiso hnB2a)

end Inputs

end CFSG.ComponentClassification.GSThmB
