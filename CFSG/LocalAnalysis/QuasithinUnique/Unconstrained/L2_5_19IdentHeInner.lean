module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentHeInnerCheck
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentHeInnerClassCert
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentCompQuot
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentSporGlue
public import CFSG.Sporadic.HeldB.InnerClass

public section

namespace CFSG.QuasithinUnique.Id2519.HeInner

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint
open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Sporadic.HeldB CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Schreier.Native CFSG.Certificates.Native CFSG.Monster.B.Co2
open CFSG.QuasithinUnique.Id2519.MathNoLayer CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement Pointwise

theorem heX1_valid : ValidSchreier heX1 := heInner_X1.1

theorem heX1_noComponent
    : ∀ B : Subgroup ↥heX1.originalSubgroup, ¬ CFSG.IsComponent B := by
  obtain ⟨F, hFK, hn, hp, hc⟩ :=
    exists_normal_selfcentralizing (by norm_num) heX1 heX1_valid _ he1_noLayer_check
  exact fun B => noComponent_of_normal_selfcentralizing hFK hn hp hc B

theorem heInnerGrp1_eq
    : heInnerGrp1 = centralizerIn heP heT1P :=
  (oddCore_eq_bot_of_restrict heInnerGrp1_le heT1P_mem_grp1 heT1P_ne_one heDelta1_injective
    heInnerGrp1_stab heT1P_fix heInnerRes1_range (v := 9) (by rw [card_heX1]; norm_num)
    oddWitness_heX1 (by rw [card_heP_cent1, card_heX1])).1

theorem card_heInnerGrp1
    : Nat.card ↥heInnerGrp1 = 21504 := by
  rw [show Nat.card ↥heInnerGrp1 = Nat.card ↥(centralizerIn heP heT1P) from
    congrArg (fun H : Subgroup (Equiv.Perm (Fin 8330)) => Nat.card ↥H) heInnerGrp1_eq]
  exact card_heP_cent1

noncomputable def heRes1
    : ↥heInnerGrp1 →* ↥heX1.originalSubgroup :=
  (MulEquiv.subgroupCongr heInnerRes1_range).toMonoidHom.comp
    (restrictHom heDelta1_injective heInnerGrp1 heInnerGrp1_stab).rangeRestrict

theorem heRes1_surjective
    : Function.Surjective heRes1 :=
  (MulEquiv.subgroupCongr heInnerRes1_range).surjective.comp
    (restrictHom heDelta1_injective heInnerGrp1 heInnerGrp1_stab).rangeRestrict_surjective

theorem card_ker_heRes1
    : Nat.card ↥heRes1.ker = 2 := by
  have h := Subgroup.card_ker_mul_card_of_surjective heRes1_surjective
  rw [card_heX1, card_heInnerGrp1] at h
  generalize Nat.card ↥heRes1.ker = n at h ⊢
  omega

theorem heInner1_noK
    : ¬ HasKComponent ↥(centralizerIn heP heT1P) := by
  intro hK
  have hker : Group.IsSolvable ↥heRes1.ker := by
    have : IsPGroup 2 ↥heRes1.ker := IsPGroup.of_card (n := 1) (by rw [card_ker_heRes1]; rfl)
    have : Group.IsNilpotent ↥heRes1.ker := this.isNilpotent
    infer_instance
  exact not_hasKComponent_of_quot_noComponent heRes1 heRes1_surjective hker heX1_noComponent
    (hK.of_mulEquiv (MulEquiv.subgroupCongr heInnerGrp1_eq.symm))

section T0

theorem heDeltaP_inc
    : incListOK 8330 105 heDeltaP = true := heP105_big.1

theorem heDeltaP_lt : ∀ k < 105, heDeltaP[k]! < 8330 := by
  have h := heDeltaP_inc
  simp only [incListOK, Bool.and_eq_true, allLt_iff, decide_eq_true_eq] at h
  exact h.1.2

theorem heDeltaP_injective
    : Function.Injective (listPt 8330 heDeltaP (m := 105)) := by
  have h := heDeltaP_inc
  simp only [incListOK, Bool.and_eq_true, allLt_iff, decide_eq_true_eq] at h
  exact listPt_injective_of_inc h.1.2 h.2

theorem heInnerCP0_agreeP
    {j : ℕ} (hj : j < 9) (k : Fin 105) :
    heInnerCP0 j (listPt 8330 heDeltaP k) = listPt 8330 heDeltaP (heSigmaPerm j k) :=
  agreeOK_spec_of_lt heDeltaP_lt (rep_heInnerC0 hj) (permChk_spec (heP105_big.2 j hj).1).1
    (heP105_big.2 j hj).2 k

theorem heInnerGrp0_stabP :
    heInnerGrp0 ≤ MulAction.stabilizer (Equiv.Perm (Fin 8330))
      (Set.range (listPt 8330 heDeltaP (m := 105))) := by
  rw [heInnerGrp0, Subgroup.closure_le]
  rintro _ ⟨j, hj, rfl⟩
  exact mem_stabilizer_of_agree (heInnerCP0_agreeP hj)

theorem heSigmaP_length : heSigmaP.length = 9 := rfl

theorem heXp_eq : heXp.originalSubgroup = Subgroup.closure {g | ∃ j < 9, heSigmaPerm j = g} := by
  rw [heXp, certificate_originalSubgroup]
  congr 1
  ext g
  simp only [List.mem_map, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ha
    refine ⟨j, heSigmaP_length ▸ hj, ?_⟩
    rw [heSigmaPerm, List.getD_eq_getElem _ _ hj]
  · rintro ⟨j, hj, rfl⟩
    have hj' : j < heSigmaP.length := heSigmaP_length ▸ hj
    exact ⟨_, List.getElem_mem hj', by rw [heSigmaPerm, List.getD_eq_getElem _ _ hj']⟩

theorem heRes0_range :
    (restrictHom heDeltaP_injective heInnerGrp0 heInnerGrp0_stabP).range =
      heXp.originalSubgroup := by
  rw [restrictHom_range heDeltaP_injective heInnerGrp0_stabP rfl, heXp_eq]
  congr 1
  ext g
  constructor
  · rintro ⟨h, ⟨j, hj, hjh⟩, rfl⟩
    exact ⟨j, hj, (restrictHom_eq_of_agree heDeltaP_injective heInnerGrp0_stabP h
      (by rw [← hjh]; exact heInnerCP0_agreeP hj)).symm⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨⟨heInnerCP0 j, Subgroup.subset_closure ⟨j, hj, rfl⟩⟩, ⟨j, hj, rfl⟩,
      restrictHom_eq_of_agree heDeltaP_injective heInnerGrp0_stabP _ (heInnerCP0_agreeP hj)⟩

theorem heInnerGrp0_eq
    : heInnerGrp0 = centralizerIn heP (heGenPerm 0) :=
  (oddCore_eq_bot_of_restrict heInnerGrp0_le heA0_mem_grp0 heA0_ne_one heDelta0_injective
    heInnerGrp0_stab heA0_fix heInnerRes0_range (v := 8) (by rw [card_heX0]; norm_num)
    oddWitness_heX0 (by rw [card_heP_cent0, card_heX0])).1

theorem card_heInnerGrp0
    : Nat.card ↥heInnerGrp0 = 161280 := by
  rw [show Nat.card ↥heInnerGrp0 = Nat.card ↥(centralizerIn heP (heGenPerm 0)) from
    congrArg (fun H : Subgroup (Equiv.Perm (Fin 8330)) => Nat.card ↥H) heInnerGrp0_eq]
  exact card_heP_cent0

theorem heXp_valid : ValidSchreier heXp := heXp_check.1

theorem heDp_valid : ValidSchreier heDp := heDp_check.1

theorem card_heXp : Nat.card ↥heXp.originalSubgroup = 40320 := by
  rw [← heXp.orderCertificate_eq_card heXp_valid, heXp_check.2]

theorem card_heDp : Nat.card ↥heDp.originalSubgroup = 20160 := by
  rw [← heDp.orderCertificate_eq_card heDp_valid, heDp_check.2]

noncomputable def heRes0
    : ↥heInnerGrp0 →* ↥heXp.originalSubgroup :=
  (MulEquiv.subgroupCongr heRes0_range).toMonoidHom.comp
    (restrictHom heDeltaP_injective heInnerGrp0 heInnerGrp0_stabP).rangeRestrict

theorem heRes0_surjective
    : Function.Surjective heRes0 :=
  (MulEquiv.subgroupCongr heRes0_range).surjective.comp
    (restrictHom heDeltaP_injective heInnerGrp0 heInnerGrp0_stabP).rangeRestrict_surjective

theorem card_ker_heRes0
    : Nat.card ↥heRes0.ker = 4 := by
  have h := Subgroup.card_ker_mul_card_of_surjective heRes0_surjective
  rw [card_heXp, card_heInnerGrp0] at h
  generalize Nat.card ↥heRes0.ker = n at h ⊢
  omega

theorem heDp_eq
    : heDp.originalSubgroup = Subgroup.closure {g | ∃ k < 5, heDpPerm k = g} := by
  rw [heDp, certificate_originalSubgroup]
  congr 1
  ext g
  simp only [List.mem_map, Set.mem_ofPred_eq]
  have hlen : heDpGens.length = 5 := heDp_gens_check.2.1
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ha
    refine ⟨k, hlen ▸ hk, ?_⟩
    rw [heDpPerm, List.getD_eq_getElem _ _ hk]
  · rintro ⟨k, hk, rfl⟩
    have hk' : k < heDpGens.length := hlen ▸ hk
    exact ⟨_, List.getElem_mem hk', by rw [heDpPerm, List.getD_eq_getElem _ _ hk']⟩

theorem heDp_le_heXp
    : heDp.originalSubgroup ≤ heXp.originalSubgroup := by
  rw [heDp_eq, Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  exact (heXp.sift_eq_true_iff_mem_original heXp_valid (heDpPerm k)).1 (heDp_rel.1 k hk)

theorem conj_mem_of_closure {M : Type*} [Group M] {A : Subgroup M} {S : Set M}
    (hA : A = Subgroup.closure S) (s : M) (h : ∀ g ∈ S, s * g * s⁻¹ ∈ A) :
    ∀ a ∈ A, s * a * s⁻¹ ∈ A := by
  intro a ha
  rw [hA] at ha
  induction ha using Subgroup.closure_induction with
  | mem x hx => exact h x hx
  | one => simp
  | mul x y _ _ ihx ihy =>
    have e : s * (x * y) * s⁻¹ = (s * x * s⁻¹) * (s * y * s⁻¹) := by group
    rw [e]
    exact A.mul_mem ihx ihy
  | inv x _ ihx =>
    have e : s * x⁻¹ * s⁻¹ = (s * x * s⁻¹)⁻¹ := by group
    rw [e]
    exact A.inv_mem ihx

theorem commutator_heXp_le
    : ⁅heXp.originalSubgroup, heXp.originalSubgroup⁆ ≤
    heDp.originalSubgroup := by
  rw [heXp_eq]
  refine commutator_closure_le {g | ∃ j < 9, heSigmaPerm j = g} heDp.originalSubgroup ?_ ?_
  · rintro _ ⟨j, hj, rfl⟩ a ha
    refine ⟨conj_mem_of_closure heDp_eq (heSigmaPerm j) (fun g hg => ?_) a ha, ?_⟩
    · obtain ⟨k, hk, rfl⟩ := hg
      exact (heDp.sift_eq_true_iff_mem_original heDp_valid _).1 (heDp_rel.2.1 j hj k hk)
    · have := conj_mem_of_closure heDp_eq (heSigmaPerm j)⁻¹ (fun g hg => ?_) a ha
      · simpa using this
      · obtain ⟨k, hk, rfl⟩ := hg
        exact (heDp.sift_eq_true_iff_mem_original heDp_valid _).1 (heDp_rel.2.2.1 j hj k hk)
  · rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩
    exact (heDp.sift_eq_true_iff_mem_original heDp_valid _).1 (heDp_rel.2.2.2 i hi j hj)

theorem commutator_le_subgroupOf
    : commutator ↥heXp.originalSubgroup ≤
    heDp.originalSubgroup.subgroupOf heXp.originalSubgroup := by
  rw [commutator_def, Subgroup.commutator_le]
  intro x _ y _
  rw [Subgroup.mem_subgroupOf]
  have h := commutator_heXp_le (Subgroup.commutator_mem_commutator x.2 y.2)
  simpa [commutatorElement_def] using h

end T0

section Classes

@[expose] def heDpSizes : List ℕ := [2880, 2880, 1260, 4032, 4032, 1260, 1260, 2240, 315, 1]

theorem heDp_classes_equiv
    : ∃ e : Fin heDpSizes.length ≃ ConjClasses heDp.originalSubgroup,
    ∀ i, (e i).carrier.ncard = heDpSizes[i] := by
  obtain ⟨ha, hc, hd, he⟩ := heDp_classes
  obtain ⟨e, hs⟩ := heDp_classes_equiv_of heDp_valid card_heDp ha hc hd he
  refine ⟨e, fun i => (hs i).trans ?_⟩
  fin_cases i <;> rfl

@[expose] def heDpSizesF : Fin 10 → ℕ := ![2880, 2880, 1260, 4032, 4032, 1260, 1260, 2240, 315, 1]

theorem heDpSizes_length : heDpSizes.length = 10 := rfl

theorem heDp_simple : IsSimpleGroup ↥heDp.originalSubgroup := by
  obtain ⟨e, he⟩ := heDp_classes_equiv
  have hsizes : ∀ i : Fin 10, heDpSizes[finCongr heDpSizes_length.symm i] = heDpSizesF i := by
    decide
  have hcard : 1 < Nat.card ↥heDp.originalSubgroup := by
    rw [card_heDp]
    norm_num
  refine isSimpleGroup_of_classSizes (m := 9) heDpSizesF
    ((finCongr heDpSizes_length.symm).trans e) (fun i => ?_) 9 (by decide) hcard ?_
  · rw [Equiv.trans_apply, he, hsizes]
  · rw [card_heDp]
    decide +kernel

end Classes

section Orders

theorem not_kOrder_20160 : ¬ KOrder 20160 :=
  not_kOrder_of_gap (p₀ := 34) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem not_kOrder_40320 : ¬ KOrder 40320 :=
  not_kOrder_of_gap (p₀ := 43) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem not_kOrder_80640 : ¬ KOrder 80640 :=
  not_kOrder_of_gap (p₀ := 54) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end Orders

theorem heInner0_noK
    : ¬ HasKComponent ↥(centralizerIn heP (heGenPerm 0)) := by
  intro hK
  have hker : Group.IsSolvable ↥heRes0.ker := by
    have : IsPGroup 2 ↥heRes0.ker := IsPGroup.of_card (n := 2) (by rw [card_ker_heRes0]; rfl)
    have : Group.IsNilpotent ↥heRes0.ker := this.isNilpotent
    infer_instance
  have : IsSimpleGroup ↥heDp.originalSubgroup := heDp_simple
  have : IsSimpleGroup ↥(heDp.originalSubgroup.subgroupOf heXp.originalSubgroup) :=
    (Subgroup.subgroupOfEquivOfLe heDp_le_heXp).isSimpleGroup
  have hD : Nat.card ↥(heDp.originalSubgroup.subgroupOf heXp.originalSubgroup) = 20160 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe heDp_le_heXp).toEquiv, card_heDp]
  refine not_hasKComponent_of_quot_simple heRes0 heRes0_surjective hker (m := 4)
    (by rw [card_ker_heRes0]) commutator_le_subgroupOf ?_
    (hK.of_mulEquiv (MulEquiv.subgroupCongr heInnerGrp0_eq.symm))
  intro k hk
  have hk4 : k ≤ 4 := Nat.le_of_dvd (by norm_num) hk
  rw [hD]
  interval_cases k
  · exact absurd hk (by norm_num)
  · simpa using not_kOrder_20160
  · simpa using not_kOrder_40320
  · exact absurd hk (by norm_num)
  · simpa using not_kOrder_80640

theorem he_inner_centralizer_noK
    {t : Equiv.Perm (Fin 8330)} (ht : t ∈ heP)
    (h2 : orderOf t = 2) : NoK (centralizerIn heP t) := by
  rcases involution_conj_cases ht h2 with ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩
  · exact fun hK => heInner0_noK (hK.of_mulEquiv (infCentralizerConjEquiv hc _))
  · exact fun hK => heInner1_noK (hK.of_mulEquiv (infCentralizerConjEquiv hc _))

theorem he_inner_noK
    : ∀ t : Equiv.Perm (Fin 8330), t ∈ heP → orderOf t = 2 →
    ¬ HasKComponent ↥(heP ⊓ Subgroup.centralizer {t}) :=
  fun _ ht h2 => he_inner_centralizer_noK ht h2

end CFSG.QuasithinUnique.Id2519.HeInner
