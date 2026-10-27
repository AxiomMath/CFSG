module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7.CertQ8
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S5.RowM12
public import Certificates.Certificate517001

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7Cert

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S5 CFSG.Blueprint CFSG.Sporadic.Mathieu
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
  Certificates.S5Rows Certificates.S5RowsM12 Certificates.S7Q8 Certificates.S7M12

namespace M12S7

section Data


theorem basic_holds : m12S7Basic () = true := Certificates.certificate517001.1

theorem class1_holds : m12S7Class1 () = true := Certificates.certificate517001.2.1

theorem class2_holds : m12S7Class2 () = true := Certificates.certificate517001.2.2.1

theorem norm_holds : m12S7Norm () = true := Certificates.certificate517001.2.2.2.1

theorem q8_holds : m12S7Q8 () = true := Certificates.certificate517001.2.2.2.2.1

theorem edge_holds : m12S7Edge () = true := Certificates.certificate517001.2.2.2.2.2

theorem basic_spec : Q8Rel i1 j1 ∧ Q8Rel i2 j2 ∧ i1 * i1 = M12Model.eltM 22 ∧
    i2 * i2 = M12Model.eltM 22 ∧ ∀ x ∈ q8Span i2 j2, M12Model.fp x ≠ M12Model.fp i1 := by
  have h := basic_holds
  simp only [m12S7Basic, Bool.and_eq_true, decide_eq_true_iff, List.all_eq_true, bne_iff_ne,
    ne_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨q8RelB_eq_true_iff.mp h1, q8RelB_eq_true_iff.mp h2, h3, h4, h5⟩

end Data

abbrev Q1 : Subgroup NativeSporadic.M12 := Subgroup.closure {i1, j1}

abbrev Q2 : Subgroup NativeSporadic.M12 := Subgroup.closure {i2, j2}

section Cent


theorem mem_czL_eltM {i : ℕ} (hi : i < 64) {k : ℕ} (hk : k < 3) :
    M12Model.eltM i * M12Model.d0 ^ k ∈ czL () := by
  simp only [czL, List.mem_flatMap, List.mem_range]
  refine ⟨i, hi, ?_⟩
  interval_cases k
  · simp
  · simp
  · simp [sq, mul_assoc]

theorem mem_czL_of_commute {c : NativeSporadic.M12}
    (hc : c * M12Model.eltM 22 = M12Model.eltM 22 * c) : c ∈ czL () := by
  obtain ⟨i, hi, k, hk, rfl⟩ := M12Model.mem_cz0 c hc
  exact mem_czL_eltM hi hk

theorem mem_czL_of_mem_sylow {s : NativeSporadic.M12} (hs : s ∈ sylowM12) : s ∈ czL () := by
  obtain ⟨x, hx, rfl⟩ := M12Model.exists_eltM (Subgroup.mem_subgroupOf.mp hs)
  have := mem_czL_eltM hx (k := 0) (by norm_num)
  rwa [pow_zero, mul_one] at this

theorem sylow_isPGroup : IsPGroup 2 sylowM12 := by
  rw [sylowM12, ← ComponentClassification.M12Cover.coe_sylow]
  exact (ComponentClassification.M12Cover.sylow).isPGroup'

theorem sylow_not_dvd_index : ¬ 2 ∣ sylowM12.index := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [sylowM12, ← ComponentClassification.M12Cover.coe_sylow]
  exact (ComponentClassification.M12Cover.sylow).not_dvd_index

end Cent

section Classes


theorem mem_czL_of_mem_normalizer {i j : NativeSporadic.M12} (h : Q8Rel i j)
    (hz : i * i = M12Model.eltM 22) {n : NativeSporadic.M12}
    (hn : n ∈ Subgroup.normalizer ((Subgroup.closure ({i, j} : Set NativeSporadic.M12)) :
      Set NativeSporadic.M12)) : n ∈ czL () := by
  have h1 := (isUniqueInvolution_closure_pair h).conj_eq (mem_normalizer_iff_conjSub_eq.mp hn)
  rw [hz] at h1
  apply mem_czL_of_commute
  calc n * M12Model.eltM 22 = n * M12Model.eltM 22 * n⁻¹ * n := by group
    _ = M12Model.eltM 22 * n := by rw [h1]

theorem aEmpty_of_checks {i j : NativeSporadic.M12} (h : Q8Rel i j)
    (hz : i * i = M12Model.eltM 22) (hc : classCheck i j (sylowL ()) (conjL ()) = true)
    (hn : normAllB i j (czL ()) = true) :
    AEmpty (CoreAssembly.conjClass (Subgroup.closure ({i, j} : Set NativeSporadic.M12)))
      (Subgroup.closure ({i, j} : Set NativeSporadic.M12)) := by
  refine aEmpty_conjClass_of_sylow (S := sylowM12) (nonempty_closure_pair_mulEquiv h)
    (isUniqueInvolution_closure_pair h) (fun u hu hu4 => ?_) (fun c hc' => ?_)
    (fun u hu hu4 => classCheck_sound h hc (mem_sylowL hu) hu4)
  · exact exists_conj_mem_of_le_normalizer
      (fun s hs => normAllB_sound h hn (mem_czL_of_mem_sylow hs)) sylow_isPGroup
      sylow_not_dvd_index hu (k := 2) (by rw [hu4]; norm_num)
  · rw [hz] at hc'
    exact normAllB_sound h hn (mem_czL_of_commute hc')

theorem norm_spec : normAllB i1 j1 (czL ()) = true ∧ normAllB i2 j2 (czL ()) = true := by
  have h := norm_holds
  simp only [m12S7Norm, Bool.and_eq_true] at h
  exact h

theorem q8_spec : q8InCheck (sylowL ()) i1 j1 i2 j2 = true ∧
    q8InCheck (czL ()) i1 j1 i2 j2 = true := by
  have h := q8_holds
  simp only [m12S7Q8, Bool.and_eq_true] at h
  exact h

theorem classes : ∀ T ∈ q8Fam NativeSporadic.M12, ∃ g : NativeSporadic.M12,
    T = conjSub g Q1 ∨ T = conjSub g Q2 := by
  intro T hT
  obtain ⟨h1, h2, -, -, -⟩ := basic_spec
  obtain ⟨g, hg⟩ := m12_conj_mem_sylow T (isPGroup_of_q8 hT)
  have hT' : conjSub g⁻¹ T ∈ q8Fam NativeSporadic.M12 := nonempty_conjSub_mulEquiv hT g⁻¹
  have hL : ∀ t ∈ conjSub g⁻¹ T, t ∈ sylowL () := by
    intro t ht
    rw [mem_conjSub_iff, inv_inv] at ht
    apply mem_sylowL
    have := hg _ ht
    rwa [show g⁻¹ * (g * t * g⁻¹) * g = t by group] at this
  have hT'' : T = conjSub g (conjSub g⁻¹ T) := (conjSub_conjSub_inv g T).symm
  refine ⟨g, ?_⟩
  rcases q8InCheck_sound h1 h2 q8_spec.1 hT' hL with h | h
  · left
    rw [hT'', h]
  · right
    rw [hT'', h]

theorem aEmpty_q8 : ∀ T ∈ q8Fam NativeSporadic.M12, AEmpty (CoreAssembly.conjClass T) T := by
  obtain ⟨h1, h2, hz1, hz2, -⟩ := basic_spec
  have hc := class1_holds
  have hc' := class2_holds
  simp only [m12S7Class1] at hc
  simp only [m12S7Class2] at hc'
  exact aEmpty_q8Fam_of_classes classes (aEmpty_of_checks h1 hz1 hc norm_spec.1)
    (aEmpty_of_checks h2 hz2 hc' norm_spec.2)

theorem edge_spec : edgeB i1 j1 i2 j2 (edgeE ()) = true ∧
    factB i1 j1 i2 j2 [edgeE ()] m12a (factAL ()) = true ∧
    factB i1 j1 i2 j2 [edgeE ()] m12b (factBL ()) = true := by
  have h := edge_holds
  simp only [m12S7Edge, Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem aStar_vStar {Y : Type} [Group Y] [Finite Y] (θ : Y ≃* NativeSporadic.M12) :
    ∀ K ∈ q8Fam Y, aStar (q8Fam Y) K = q8Fam Y ∧ vStar (q8Fam Y) K = q8Fam Y := by
  obtain ⟨h1, h2, hz1, hz2, hfp⟩ := basic_spec
  obtain ⟨hedge, hfa, hfb⟩ := edge_spec
  have hI1 := isUniqueInvolution_closure_pair h1
  have hI2 := isUniqueInvolution_closure_pair h2
  rw [hz1] at hI1
  rw [hz2] at hI2
  refine aStar_vStar_of_edges_equiv θ (Q₁ := Q1) (Q₂ := Q2) (E := {x | x ∈ [edgeE ()]})
    (nonempty_closure_pair_mulEquiv h1) (nonempty_closure_pair_mulEquiv h2) hI1 hI2 ?_ classes
    ?_ ?_ ?_
  · intro g hg
    have hmem : g * i1 * g⁻¹ ∈ Q2 := by
      rw [← hg]
      exact conj_mem_conjSub (Subgroup.subset_closure (Set.mem_insert _ _))
    exact hfp _ ((mem_closure_pair_iff h2).mp hmem) (M12Model.fp_conj g i1)
  · intro T hT hT1 _
    refine q8InCheck_sound h1 h2 q8_spec.2 hT fun t ht => ?_
    exact mem_czL_of_mem_normalizer h1 hz1 (hT1 ht)
  · intro e he
    rw [Set.mem_setOf_eq, List.mem_singleton] at he
    rw [he]
    exact edgeB_sound h1 h2 hedge
  · rw [eq_top_iff, ← closure_pair_eq_top m12_eq (Subgroup.subset_closure (Set.mem_insert _ _))
      (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)), Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact factB_sound h1 h2 hfa
    · exact factB_sound h1 h2 hfb

end Classes

end M12S7

end CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7Cert
