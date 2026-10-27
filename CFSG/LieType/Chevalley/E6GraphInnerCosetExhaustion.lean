module

public import CFSG.LieType.Chevalley.E6GraphInnerCosetCore
public import CFSG.LieType.Chevalley.E6SecondGraphFixedSubgroup
public import CFSG.LieType.Chevalley.OrdinaryEFieldGraphQuotient
public import CFSG.LieType.Chevalley.E6GraphInvolutionUnitary
public import CFSG.LieType.Chevalley.E6GraphRootSL2Normalizer

public noncomputable section

namespace CFSG.LieType.Chevalley.E6GraphInnerCoset

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.E6GraphHighestRoot
  CFSG.LieType.Chevalley.E6GraphLevi CFSG.LieType.Chevalley.E6GraphRootSL2
  CFSG.LieType.Chevalley.E6GraphRootPair CFSG.LieType.Chevalley.E6GraphInvolution

section Words

variable {E : Type} [Field E]

theorem mem_setA_two : (e6Idx 2 : Fin TwistTag.E6.tag.rank) ∈ setA := by
  simp only [setA, Set.mem_ofPred_eq]
  decide

theorem mem_setA_three : (e6Idx 3 : Fin TwistTag.E6.tag.rank) ∈ setA := by
  simp only [setA, Set.mem_ofPred_eq]
  decide

theorem mem_setA_four : (e6Idx 4 : Fin TwistTag.E6.tag.rank) ∈ setA := by
  simp only [setA, Set.mem_ofPred_eq]
  decide

theorem fusion_conj_mem_subsystemGroup
    (h2 : (2 : E) = 0) :
    wordElt E fusionWord * (pinnedX TwistTag.E6.tag E e6HighestRoot 1 *
      pinnedX TwistTag.E6.tag E sRoot 1) * (wordElt E fusionWord)⁻¹ ∈
        subsystemGroup TwistTag.E6.tag E setA := by
  have e : wordElt E fusionWord * (pinnedX TwistTag.E6.tag E e6HighestRoot 1 *
      pinnedX TwistTag.E6.tag E sRoot 1) * (wordElt E fusionWord)⁻¹ =
      (wordElt E fusionWord * pinnedX TwistTag.E6.tag E e6HighestRoot 1 *
        (wordElt E fusionWord)⁻¹) *
      (wordElt E fusionWord * pinnedX TwistTag.E6.tag E sRoot 1 * (wordElt E fusionWord)⁻¹) := by
    group
  rw [e, wordElt_conj_pinnedX h2 fusionWord isRoot_e6HighestRoot,
    wordElt_conj_pinnedX h2 fusionWord isRoot_sRoot, fusionWord_smul_e6HighestRoot,
    fusionWord_smul_sRoot]
  have h4 : pinnedX TwistTag.E6.tag E (Pi.single (e6Idx 3) 1) 1 ∈
      subsystemGroup TwistTag.E6.tag E setA := by
    rw [pinnedX_single]
    exact xUnit_mem_subsystemGroup mem_setA_three 1
  have hw : wordElt E [e6Idx 2, e6Idx 4] ∈ subsystemGroup TwistTag.E6.tag E setA :=
    Subgroup.list_prod_mem _ fun g hg => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · exact weylElt_mem_subsystemGroup mem_setA_two 1
      · exact weylElt_mem_subsystemGroup mem_setA_four 1
  have h345 : pinnedX TwistTag.E6.tag E
      (Pi.single (e6Idx 2) 1 + Pi.single (e6Idx 3) 1 + Pi.single (e6Idx 4) 1) 1 =
      wordElt E [e6Idx 2, e6Idx 4] * pinnedX TwistTag.E6.tag E (Pi.single (e6Idx 3) 1) 1 *
        (wordElt E [e6Idx 2, e6Idx 4])⁻¹ := by
    rw [wordElt_conj_pinnedX h2 _ (isRoot_single _ _), wordProd_smul]
    congr 1
    decide
  rw [h345]
  exact mul_mem (mul_mem (mul_mem hw h4) (inv_mem hw)) h4

theorem up_conj_sRoot
    (h2 : (2 : E) = 0) :
    wordElt E upWord.reverse * pinnedX TwistTag.E6.tag E sRoot 1 *
      (wordElt E upWord.reverse)⁻¹ = pinnedX TwistTag.E6.tag E e6HighestRoot 1 := by
  rw [wordElt_conj_pinnedX h2 upWord.reverse isRoot_sRoot, upWord_smul_sRoot]

end Words

section NotInner

theorem exactQ_E6 (K : Type) [Field K] (ε : ℕ) :
    exactQ TwistTag.E6.tag K ε = diagramMap TwistTag.E6 K ^ ε := rfl

theorem ordinary_not_inner
    (k : Type) [Field k] [Finite k] {g : ModGL TwistTag.E6.tag k}
    (hg : g ∈ adjointGroup TwistTag.E6.tag k) :
    ¬ ∀ h ∈ adjointGroup TwistTag.E6.tag k,
      diagramMap TwistTag.E6 k * h * (diagramMap TwistTag.E6 k)⁻¹ = g * h * g⁻¹ := by
  intro hPg
  obtain ⟨Θ, -, hΘ, -⟩ := ordinary_E_field_graph_quotient_and_involutions TwistTag.E6.tag
    (Or.inl rfl) k
  have hid : ∀ h : adjointGroup TwistTag.E6.tag k,
      Units.map (entrywiseHom (RingEquiv.refl k).toRingHom) (h : ModGL TwistTag.E6.tag k) = h :=
    fun h => Units.ext (entrywise_id _)
  have h0 := hΘ (MulAut.conj (⟨g, hg⟩ : adjointGroup TwistTag.E6.tag k)) ⟨g, hg⟩ 1
    (RingEquiv.refl k) ⟨0, by decide⟩ fun h => by
      rw [hid, rootDiagUnit_one, MulAut.conj_apply, exactQ_E6]
      simp
  have h1 := hΘ (MulAut.conj (⟨g, hg⟩ : adjointGroup TwistTag.E6.tag k)) 1 1
    (RingEquiv.refl k) ⟨1, by decide⟩ fun h => by
      rw [hid, rootDiagUnit_one, MulAut.conj_apply]
      have := hPg h h.2
      rw [exactQ_E6]
      simp only [pow_one, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one, one_mul, inv_one,
        mul_one]
      exact this.symm
  rw [h0] at h1
  have := congrArg (fun x => Multiplicative.toAdd x.2) h1
  simp only [toAdd_ofAdd] at this
  exact absurd this (by decide)

theorem twisted_not_inner
    {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 2) (σE : K ≃+* K) (hσ : ∀ c, σE c = c ^ 2 ^ f)
    {g : ModGL TwistTag.E6.tag K} (hg : g ∈ graphFixedRootGroup TwistTag.E6 K σE.toRingHom) :
    ¬ ∀ h ∈ graphFixedRootGroup TwistTag.E6 K σE.toRingHom,
      diagramMap TwistTag.E6 K * h * (diagramMap TwistTag.E6 K)⁻¹ = g * h * g⁻¹ := by
  intro hPg
  have : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero
    (two_eq_zero_of_card_sq hf hK)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, hΘ, -⟩, hP, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two hf K hK σE hσ
  have h0 := hΘ (MulAut.conj (⟨g, hg⟩ : twistedE6RootGroup K σE)) ⟨g, hg⟩ 1 1 (by
    rw [map_one, fieldActor_one, mul_one, mul_one])
  have h1 := hΘ (MulAut.conj (⟨g, hg⟩ : twistedE6RootGroup K σE)) 1 1 σE (by
    rw [map_one, map_one, one_mul, one_mul]
    refine MulEquiv.ext fun h => Subtype.ext ?_
    rw [hP h, MulAut.conj_apply]
    exact (hPg h h.2).symm)
  rw [h0] at h1
  obtain ⟨c, hc⟩ := (CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution (p := 2)
    (f := f) hK).exists_ne
  rw [CFSG.LieType.BorelTits.unitaryInvolution_apply, ← hσ, ← h1] at hc
  exact hc rfl

end NotInner

section Data

variable (f : ℕ) (hf : 1 ≤ f) (k K : Type) [Field k] [Field K] [Algebra k K]
  (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2)

include hf hk hK in
theorem ordinaryData
    (σ : K →+* K) (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    ExhaustionData (RingHom.id k) (adjointGroup TwistTag.E6.tag k)
      (subsystemGroup TwistTag.E6.tag k setA ⊓ adjointGroup TwistTag.E6.tag k)
      (parabolicRadical TwistTag.E6.tag k setA ⊓ adjointGroup TwistTag.E6.tag k)
      (posUnipotent TwistTag.E6.tag k) := by
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have hk2 : (2 : k) = 0 := two_eq_zero_of_card hf hk
  obtain ⟨hD, -⟩ := even_E6_graph_finite_Levi_intersections f hf k K hk hK σ hσ
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hγ, -⟩ := hD
  obtain ⟨hE, -⟩ := even_E6_graph_highest_root_normalizer f hf k K hk hK σ hσ
  obtain ⟨-, -, -, -, -, -, hQnC, hQL, hfacC, hSyl, hUcent, -⟩ := hE
  obtain ⟨hS, -⟩ := even_E6_graph_root_SL2_normalizer f hf k K hk hK σ hσ
  obtain ⟨hXG, -, -, hXL, hcomm, huniq, hXfix⟩ := hS
  have hlin := even_E6_graph_linear_Levi_involution_forms f hf k hk
  obtain ⟨hrad, -⟩ := even_E6_graph_radical_cocycle_reduction f hf k K hk hK σ hσ
  obtain ⟨-, hpair, -, -⟩ := even_E6_graph_root_pair_dichotomy f hf k K hk hK σ hσ
  have hγQ := hγ _ (Set.mem_insert _ _)
  have hγL := hγ _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
  exact
    { two_eq_zero := hk2
      P_mul_self := diagramMap_E6_mul_self
      P_conj_G := fun g hg => diagramMap_conj_mem_adjointGroup' hg
      P_not_mem := fun hP => ordinary_not_inner k hP fun h _ => rfl
      U_le := posUnipotent_le_adjointGroup
      U_sylow := hSyl
      P_conj_U := fun u hu => by
        rw [← twistHom_id_eq]
        exact twistHom_mem_posUnipotent (fun x => ⟨x, rfl⟩) hu
      U_le_centralizer := hUcent
      centralizer_factor := fun g hg => by
        obtain ⟨⟨q, l⟩, ⟨hq, hl, he⟩, -⟩ := hfacC g hg
        exact ⟨q, hq, l, hl, he⟩
      Q_le := inf_le_right
      L_le := inf_le_right
      Q_inf_L := hQL
      L_le_normalizer := le_sup_right.trans
        ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).1 hQnC)
      P_conj_Q := fun q hq => conj_mem_of_map_eq hγQ hq
      P_conj_L := fun l hl => conj_mem_of_map_eq hγL hl
      X_le := hXG
      P_conj_X := hXfix
      L_commute_X := hcomm
      X_inf_L := hXL
      normalizer_factor := fun g hg => by
        obtain ⟨⟨x, l⟩, ⟨hx, hl, he⟩, -⟩ := huniq g hg
        exact ⟨x, hx, l, hl, he⟩
      levi_form := fun l hl hsq => (hlin l hl hsq).1
      levi_detector := fun l hl hsq h => by
        obtain ⟨g, hg, hle, hnot⟩ := (hlin l hl hsq).2 h
        exact ⟨g, hg, hle, hnot⟩
      radical := hrad
      pair := fun g₁ hg₁ j hj hjj hnot => by
        obtain ⟨h1, h2, h3, -⟩ := hpair g₁ hg₁ j hj hjj hnot
        exact ⟨h1, h2, h3⟩
      fusion_mem := wordElt_mem_adjointGroup _
      fusion_P := diagramMap_conj_wordElt hk2 weylTwist_fusionWord
      fusion_L := Subgroup.mem_inf.2 ⟨fusion_conj_mem_subsystemGroup hk2,
        mul_mem (mul_mem (wordElt_mem_adjointGroup _) (mul_mem (pinnedX_mem_adjointGroup _ _)
          (pinnedX_mem_adjointGroup _ _))) (inv_mem (wordElt_mem_adjointGroup _))⟩
      up_mem := wordElt_mem_adjointGroup _
      up_P := diagramMap_conj_wordElt hk2 weylTwist_upWord
      up_conj := up_conj_sRoot hk2 }

include hf hk hK in
theorem twistedData
    (σE : K ≃+* K) (hσ : ∀ c, σE c = c ^ 2 ^ f) :
    ExhaustionData (algebraMap k K) (graphFixedRootGroup TwistTag.E6 K σE.toRingHom)
      (subsystemGroup TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σE.toRingHom)
      (parabolicRadical TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σE.toRingHom)
      (graphFixedPosUnipotent TwistTag.E6 K σE.toRingHom) := by
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have hK2 : (2 : K) = 0 := two_eq_zero_of_card_sq hf hK
  have hσ' : ∀ c, σE.toRingHom c = c ^ 2 ^ f := hσ
  have hσk : ∀ c, σE.toRingHom c = c ^ Nat.card k := fun c => by rw [hk]; exact hσ c
  have hσσ : ∀ c, σE.toRingHom (σE.toRingHom c) = c := fun c => by
    rw [hσ', hσ']
    exact CFSG.LieType.Simplicity.pow_pow_card_sq hK c
  obtain ⟨-, hD⟩ := even_E6_graph_finite_Levi_intersections f hf k K hk hK σE.toRingHom hσ'
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, hγ, -⟩ := hD
  obtain ⟨-, hE⟩ := even_E6_graph_highest_root_normalizer f hf k K hk hK σE.toRingHom hσ'
  obtain ⟨-, -, -, -, -, -, hQnC, hQL, hfacC, hSyl, hUcent, -⟩ := hE
  obtain ⟨-, hS⟩ := even_E6_graph_root_SL2_normalizer f hf k K hk hK σE.toRingHom hσ'
  obtain ⟨hXG, -, -, hXL, hcomm, huniq, hXfix⟩ := hS
  have huni := even_E6_graph_unitary_Levi_involution_forms f hf k K hk hK σE.toRingHom hσ'
  obtain ⟨-, hrad⟩ := even_E6_graph_radical_cocycle_reduction f hf k K hk hK σE.toRingHom hσ'
  obtain ⟨-, -, -, hpair⟩ := even_E6_graph_root_pair_dichotomy f hf k K hk hK σE.toRingHom hσ'
  have hγQ := hγ _ (Set.mem_insert _ _)
  have hγL := hγ _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
  have hPG := map_conj_diagramMap_graphFixedRootGroup σE rfl hσσ
  have hsG : pinnedX TwistTag.E6.tag K sRoot 1 ∈ graphFixedRootGroup TwistTag.E6 K σE.toRingHom :=
    graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _ (Subgroup.mem_inf.2
      ⟨pinnedX_mem_rootSpan (S := {α | IsRoot TwistTag.E6.tag α ∧ 0 < height α})
        ⟨isRoot_sRoot, by decide⟩ 1, (mem_twistedFixedGroup_iff_twistHom _ _ _).2
          ⟨pinnedX_mem_adjointGroup _ _, by
            rw [E6GraphRadical.twistHom_pinnedX_of_two hK2 _ isRoot_sRoot, permLattice_sRoot,
              map_one]⟩⟩)
  have htG : pinnedX TwistTag.E6.tag K e6HighestRoot 1 ∈
      graphFixedRootGroup TwistTag.E6 K σE.toRingHom :=
    hXG ((le_sup_left : thetaRootGroup (algebraMap k K) ≤ thetaRankOneGroup (algebraMap k K))
      ((mem_thetaRootGroup _).2 ⟨1, by rw [map_one]⟩))
  have hnf := wordElt_mem_graphFixedRootGroup (σ := σE.toRingHom) hK2 weylTwist_fusionWord
  exact
    { two_eq_zero := hK2
      P_mul_self := diagramMap_E6_mul_self
      P_conj_G := fun g hg => conj_mem_of_map_eq hPG hg
      P_not_mem := fun hP => twisted_not_inner hf K hK σE hσ hP fun h _ => rfl
      U_le := graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
      U_sylow := hSyl
      P_conj_U := fun u hu => by
        obtain ⟨hu1, hu2⟩ := Subgroup.mem_inf.1 hu
        have hu3 := (mem_twistedFixedGroup_iff_twistHom _ _ _).1 hu2
        refine Subgroup.mem_inf.2 ⟨?_, (mem_twistedFixedGroup_iff_twistHom _ _ _).2
          ⟨diagramMap_conj_mem_adjointGroup' hu3.1, ?_⟩⟩
        · rw [← twistHom_id_eq]
          exact twistHom_mem_posUnipotent (fun x => ⟨x, rfl⟩) hu1
        · rw [map_mul, map_mul, map_inv, E6GraphRadical.twistHom_diagramMap', hu3.2]
      U_le_centralizer := hUcent
      centralizer_factor := fun g hg => by
        obtain ⟨⟨q, l⟩, ⟨hq, hl, he⟩, -⟩ := hfacC g hg
        exact ⟨q, hq, l, hl, he⟩
      Q_le := inf_le_right
      L_le := inf_le_right
      Q_inf_L := hQL
      L_le_normalizer := le_sup_right.trans
        ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).1 hQnC)
      P_conj_Q := fun q hq => conj_mem_of_map_eq hγQ hq
      P_conj_L := fun l hl => conj_mem_of_map_eq hγL hl
      X_le := hXG
      P_conj_X := hXfix
      L_commute_X := hcomm
      X_inf_L := hXL
      normalizer_factor := fun g hg => by
        obtain ⟨⟨x, l⟩, ⟨hx, hl, he⟩, -⟩ := huniq g hg
        exact ⟨x, hx, l, hl, he⟩
      levi_form := fun l hl hsq => by
        rcases (huni l hl hsq).1 with ⟨D, -, hD, he⟩ | ⟨D, -, hD, he⟩
        · exact Or.inl ⟨_, hD, he⟩
        · exact Or.inr ⟨_, hD, he⟩
      levi_detector := fun l hl hsq h => by
        obtain ⟨g, hg, hle, hnot⟩ := (huni l hl hsq).2 h
        exact ⟨g, hg, hle, hnot⟩
      radical := hrad
      pair := fun g₁ hg₁ j hj hjj hnot => by
        obtain ⟨h1, h2, h3, -⟩ := hpair g₁ hg₁ j hj hjj hnot
        exact ⟨h1, h2, h3⟩
      fusion_mem := hnf
      fusion_P := diagramMap_conj_wordElt hK2 weylTwist_fusionWord
      fusion_L := Subgroup.mem_inf.2 ⟨fusion_conj_mem_subsystemGroup hK2,
        mul_mem (mul_mem hnf (mul_mem htG hsG)) (inv_mem hnf)⟩
      up_mem := wordElt_mem_graphFixedRootGroup hK2 weylTwist_upWord
      up_P := diagramMap_conj_wordElt hK2 weylTwist_upWord
      up_conj := up_conj_sRoot hK2 }

end Data

theorem faithful_of {E : Type} [Field E] {G : Subgroup (ModGL TwistTag.E6.tag E)}
    (hZ : Subgroup.center ↥G = ⊥)
    (hPG : ∀ g ∈ G, diagramMap TwistTag.E6 E * g * (diagramMap TwistTag.E6 E)⁻¹ ∈ G)
    (hPP : diagramMap TwistTag.E6 E * diagramMap TwistTag.E6 E = 1)
    (hinner : ∀ g ∈ G, ¬ ∀ h ∈ G,
      diagramMap TwistTag.E6 E * h * (diagramMap TwistTag.E6 E)⁻¹ = g * h * g⁻¹)
    {x : ModGL TwistTag.E6.tag E} (hx : x ∈ G ⊔ Subgroup.zpowers (diagramMap TwistTag.E6 E))
    (hfix : ∀ g ∈ G, x * g * x⁻¹ = g) : x = 1 := by
  rcases mem_or_eq_mul_of_mem_sup_zpowers hPG hPP hx with hxG | ⟨a, ha, rfl⟩
  · have hc : (⟨x, hxG⟩ : G) ∈ Subgroup.center ↥G := Subgroup.mem_center_iff.2 fun g =>
      Subtype.ext (by
        have := hfix g g.2
        simp only [Subgroup.coe_mul]
        calc (g : ModGL TwistTag.E6.tag E) * x = x * g * x⁻¹ * x := by rw [this]
          _ = x * g := by group)
    rw [hZ, Subgroup.mem_bot] at hc
    exact congrArg Subtype.val hc
  · exfalso
    refine hinner a⁻¹ (inv_mem ha) fun h hh => ?_
    have := hfix h hh
    calc diagramMap TwistTag.E6 E * h * (diagramMap TwistTag.E6 E)⁻¹ =
          a⁻¹ * (a * diagramMap TwistTag.E6 E * h * (a * diagramMap TwistTag.E6 E)⁻¹) * a := by
          group
      _ = a⁻¹ * h * a⁻¹⁻¹ := by rw [this, inv_inv]

theorem _root_.CFSG.LieType.Chevalley.even_E6_graph_inner_coset_exhaustion
    (f : ℕ)
    (hf : 1 ≤ f) (k K : Type) [Field k] [Field K] [Algebra k K] (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    (diagramMap TwistTag.E6 k ∉ adjointGroup TwistTag.E6.tag k ∧
      diagramMap TwistTag.E6 k * diagramMap TwistTag.E6 k = 1 ∧
      (∀ g ∈ adjointGroup TwistTag.E6.tag k, diagramMap TwistTag.E6 k * g *
        (diagramMap TwistTag.E6 k)⁻¹ ∈ adjointGroup TwistTag.E6.tag k) ∧
      (pinnedX TwistTag.E6.tag k e6HighestRoot 1 * diagramMap TwistTag.E6 k) ^ 2 = 1 ∧
      (∀ a ∈ adjointGroup TwistTag.E6.tag k, (a * diagramMap TwistTag.E6 k) ^ 2 = 1 →
        (∃ g ∈ adjointGroup TwistTag.E6.tag k,
          g * (a * diagramMap TwistTag.E6 k) * g⁻¹ = diagramMap TwistTag.E6 k) ∨
        ∃ g ∈ adjointGroup TwistTag.E6.tag k, g * (a * diagramMap TwistTag.E6 k) * g⁻¹ =
          pinnedX TwistTag.E6.tag k e6HighestRoot 1 * diagramMap TwistTag.E6 k) ∧
      (∀ x ∈ adjointGroup TwistTag.E6.tag k ⊔ Subgroup.zpowers (diagramMap TwistTag.E6 k),
        (∀ g ∈ adjointGroup TwistTag.E6.tag k, x * g * x⁻¹ = g) → x = 1) ∧
      ∃ (ht : pinnedX TwistTag.E6.tag k e6HighestRoot 1 ∈ adjointGroup TwistTag.E6.tag k)
        (η : MulAut (adjointGroup TwistTag.E6.tag k)),
        (∀ g : adjointGroup TwistTag.E6.tag k, (η g : ModGL TwistTag.E6.tag k) =
          diagramMap TwistTag.E6 k * g * (diagramMap TwistTag.E6 k)⁻¹) ∧
        (∀ g : adjointGroup TwistTag.E6.tag k,
          ((MulAut.conj (⟨_, ht⟩ : adjointGroup TwistTag.E6.tag k) * η) g :
            ModGL TwistTag.E6.tag k) =
          (pinnedX TwistTag.E6.tag k e6HighestRoot 1 * diagramMap TwistTag.E6 k) * g *
            (pinnedX TwistTag.E6.tag k e6HighestRoot 1 * diagramMap TwistTag.E6 k)⁻¹) ∧
        ∀ φ : MulAut (adjointGroup TwistTag.E6.tag k),
          φ * η * φ⁻¹ ≠ MulAut.conj (⟨_, ht⟩ : adjointGroup TwistTag.E6.tag k) * η) ∧
    (diagramMap TwistTag.E6 K ∉ graphFixedRootGroup TwistTag.E6 K σ ∧
      diagramMap TwistTag.E6 K * diagramMap TwistTag.E6 K = 1 ∧
      (∀ g ∈ graphFixedRootGroup TwistTag.E6 K σ, diagramMap TwistTag.E6 K * g *
        (diagramMap TwistTag.E6 K)⁻¹ ∈ graphFixedRootGroup TwistTag.E6 K σ) ∧
      (pinnedX TwistTag.E6.tag K e6HighestRoot 1 * diagramMap TwistTag.E6 K) ^ 2 = 1 ∧
      (∀ a ∈ graphFixedRootGroup TwistTag.E6 K σ, (a * diagramMap TwistTag.E6 K) ^ 2 = 1 →
        (∃ g ∈ graphFixedRootGroup TwistTag.E6 K σ,
          g * (a * diagramMap TwistTag.E6 K) * g⁻¹ = diagramMap TwistTag.E6 K) ∨
        ∃ g ∈ graphFixedRootGroup TwistTag.E6 K σ, g * (a * diagramMap TwistTag.E6 K) * g⁻¹ =
          pinnedX TwistTag.E6.tag K e6HighestRoot 1 * diagramMap TwistTag.E6 K) ∧
      (∀ x ∈ graphFixedRootGroup TwistTag.E6 K σ ⊔ Subgroup.zpowers (diagramMap TwistTag.E6 K),
        (∀ g ∈ graphFixedRootGroup TwistTag.E6 K σ, x * g * x⁻¹ = g) → x = 1) ∧
      ∃ (ht : pinnedX TwistTag.E6.tag K e6HighestRoot 1 ∈ graphFixedRootGroup TwistTag.E6 K σ)
        (η : MulAut (graphFixedRootGroup TwistTag.E6 K σ)),
        (∀ g : graphFixedRootGroup TwistTag.E6 K σ, (η g : ModGL TwistTag.E6.tag K) =
          diagramMap TwistTag.E6 K * g * (diagramMap TwistTag.E6 K)⁻¹) ∧
        (∀ g : graphFixedRootGroup TwistTag.E6 K σ,
          ((MulAut.conj (⟨_, ht⟩ : graphFixedRootGroup TwistTag.E6 K σ) * η) g :
            ModGL TwistTag.E6.tag K) =
          (pinnedX TwistTag.E6.tag K e6HighestRoot 1 * diagramMap TwistTag.E6 K) * g *
            (pinnedX TwistTag.E6.tag K e6HighestRoot 1 * diagramMap TwistTag.E6 K)⁻¹) ∧
        ∀ φ : MulAut (graphFixedRootGroup TwistTag.E6 K σ),
          φ * η * φ⁻¹ ≠ MulAut.conj (⟨_, ht⟩ : graphFixedRootGroup TwistTag.E6 K σ) * η) := by
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have hsurj : Function.Surjective σ := Finite.surjective_of_injective σ.injective
  obtain ⟨σE, rfl⟩ : ∃ σE : K ≃+* K, σE.toRingHom = σ :=
    ⟨RingEquiv.ofBijective σ ⟨σ.injective, hsurj⟩, RingHom.ext fun _ => rfl⟩
  have hσ' : ∀ c, σE c = c ^ 2 ^ f := hσ
  have hDO := ordinaryData f hf k K hk hK σE.toRingHom hσ
  have hDT := twistedData f hf k K hk hK σE hσ'
  obtain ⟨-, -, -, -, ⟨eO, -, -, hsecO⟩, ⟨eT, -, -, hsecT⟩⟩ :=
    even_E6_twisted_E6_second_graph_fixed_subgroup f hf k K hk hK σE.toRingHom hσ
  obtain ⟨htJO, hJCO, ηO, hηO, -, hξO, -, -, hncO, -⟩ := hsecO
  obtain ⟨htJT, hJCT, ηT, hηT, -, hξT, -, -, hncT, -⟩ := hsecT
  have htP : ∀ {E : Type} [Field E] {ι : k →+* E} {G L Q U : Subgroup (ModGL TwistTag.E6.tag E)},
      ExhaustionData ι G L Q U →
        (pinnedX TwistTag.E6.tag E e6HighestRoot 1 * diagramMap TwistTag.E6 E) ^ 2 = 1 := by
    intro E _ ι G L Q U D
    have htX : pinnedX TwistTag.E6.tag E e6HighestRoot 1 ∈ thetaRankOneGroup ι :=
      (le_sup_left : thetaRootGroup ι ≤ thetaRankOneGroup ι)
        ((mem_thetaRootGroup ι).2 ⟨1, by rw [map_one]⟩)
    calc (pinnedX TwistTag.E6.tag E e6HighestRoot 1 * diagramMap TwistTag.E6 E) ^ 2 =
          pinnedX TwistTag.E6.tag E e6HighestRoot 1 * (diagramMap TwistTag.E6 E *
            pinnedX TwistTag.E6.tag E e6HighestRoot 1 * (diagramMap TwistTag.E6 E)⁻¹) *
            (diagramMap TwistTag.E6 E * diagramMap TwistTag.E6 E) := by rw [sq]; group
      _ = 1 := by
          rw [D.P_conj_X _ htX, D.P_mul_self, mul_one, ← pinnedX_add,
            show (1 : E) + 1 = 2 by norm_num, D.two_eq_zero, pinnedX_zero]
  have hZO : Subgroup.center ↥(adjointGroup TwistTag.E6.tag k) = ⊥ := center_adjointGroup_eq_bot
  have : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero hDT.two_eq_zero
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hZT, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two hf K hK σE hσ'
  refine ⟨⟨hDO.P_not_mem, hDO.P_mul_self, hDO.P_conj_G, htP hDO, fun a ha hsq => hDO.exhaust ha hsq,
      fun x hx hfix => faithful_of hZO hDO.P_conj_G hDO.P_mul_self
        (fun g hg => ordinary_not_inner k hg) hx hfix,
      hJCO htJO, ηO, hηO, fun g => by rw [hξO g]; group, hncO⟩,
    ⟨hDT.P_not_mem, hDT.P_mul_self, hDT.P_conj_G, htP hDT, fun a ha hsq => hDT.exhaust ha hsq,
      fun x hx hfix => faithful_of hZT hDT.P_conj_G hDT.P_mul_self
        (fun g hg => twisted_not_inner hf K hK σE hσ' hg) hx hfix,
      hJCT htJT, ηT, hηT, fun g => by rw [hξT g]; group, hncT⟩⟩

end CFSG.LieType.Chevalley.E6GraphInnerCoset
