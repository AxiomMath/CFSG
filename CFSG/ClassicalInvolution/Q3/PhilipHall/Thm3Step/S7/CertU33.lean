module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7.CertQ8
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S5.RowU3Model
public import Certificates.Certificate517002

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7Cert

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S5 CFSG.Blueprint
  CFSG.Certificates CFSG.Sporadic.Schreier CFSG.GH74.KGroups
  Certificates.S5Rows Certificates.S5RowsU33 Certificates.S7Q8 Certificates.S7U33

namespace U33S7

abbrev AA : Type := ↥U33.QA.originalSubgroup

theorem gensA_mem : ∀ g ∈ gensA, g ∈ U33.QA.originalSubgroup := by
  have hgen : ∀ g ∈ [U33.pa, U33.pb, U33.sg0], g ∈ U33.QA.originalSubgroup := by
    intro g hg
    rw [U33.QA, certificate_originalSubgroup]
    exact Subgroup.subset_closure hg
  intro g hg
  simp only [gensA, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hgen _ (by simp)
  · exact hgen _ (by simp)
  · exact hgen _ (by simp)
  · exact Subgroup.inv_mem _ (hgen _ (by simp))
  · exact Subgroup.inv_mem _ (hgen _ (by simp))
  · exact Subgroup.inv_mem _ (hgen _ (by simp))

theorem pa_mem : U33.pa ∈ U33.QA.originalSubgroup := by
  rw [U33.QA, certificate_originalSubgroup]
  exact Subgroup.subset_closure (by simp)

theorem pb_mem : U33.pb ∈ U33.QA.originalSubgroup := by
  rw [U33.QA, certificate_originalSubgroup]
  exact Subgroup.subset_closure (by simp)

theorem sg0_mem : U33.sg0 ∈ U33.QA.originalSubgroup := by
  rw [U33.QA, certificate_originalSubgroup]
  exact Subgroup.subset_closure (by simp)

theorem wA_mem (w : List ℕ) : wA w ∈ U33.QA.originalSubgroup := by
  rw [wA, tab_eq]
  refine list_prod_mem fun g hg => ?_
  obtain ⟨k, -, rfl⟩ := List.mem_map.mp hg
  rw [List.getD_eq_getElem?_getD]
  cases hk : gensA[k]? with
  | none => exact Subgroup.one_mem _
  | some g => exact gensA_mem g (List.mem_of_getElem? hk)

noncomputable def liftA (L : List (Equiv.Perm (Fin 28)))
    (h : ∀ x ∈ L, x ∈ U33.QA.originalSubgroup) : List AA :=
  L.pmap (fun x hx => (⟨x, hx⟩ : AA)) h

theorem liftA_map (L : List (Equiv.Perm (Fin 28))) (h : ∀ x ∈ L, x ∈ U33.QA.originalSubgroup) :
    (liftA L h).map U33.QA.originalSubgroup.subtype = L := by
  rw [liftA, List.map_pmap]
  exact List.pmap_eq_self.mpr fun _ _ => rfl

theorem mem_liftA {L : List (Equiv.Perm (Fin 28))} {h : ∀ x ∈ L, x ∈ U33.QA.originalSubgroup}
    {a : AA} : a ∈ liftA L h ↔ (a : Equiv.Perm (Fin 28)) ∈ L := by
  constructor
  · intro ha
    have := List.mem_map_of_mem (f := U33.QA.originalSubgroup.subtype) ha
    rwa [liftA_map] at this
  · intro ha
    rw [liftA, List.mem_pmap]
    exact ⟨_, ha, rfl⟩

theorem i1_mem : i1 ∈ U33.QA.originalSubgroup := wA_mem _
theorem j1_mem : j1 ∈ U33.QA.originalSubgroup := wA_mem _
theorem i2_mem : i2 ∈ U33.QA.originalSubgroup := wA_mem _
theorem j2_mem : j2 ∈ U33.QA.originalSubgroup := wA_mem _

abbrev i1A : AA := ⟨i1, i1_mem⟩
abbrev j1A : AA := ⟨j1, j1_mem⟩
abbrev i2A : AA := ⟨i2, i2_mem⟩
abbrev j2A : AA := ⟨j2, j2_mem⟩
abbrev sgA : AA := ⟨U33.sg0, sg0_mem⟩
abbrev paA : AA := ⟨U33.pa, pa_mem⟩
abbrev pbA : AA := ⟨U33.pb, pb_mem⟩

abbrev Q1 : Subgroup AA := Subgroup.closure {i1A, j1A}

abbrev Q2 : Subgroup AA := Subgroup.closure {i2A, j2A}

section Data


theorem mem_sylowA {x : Equiv.Perm (Fin 28)} (hx : x ∈ sylowA ()) : x ∈ U33.QA.originalSubgroup :=
  QSA_le_QA ((mem_elemsT QSA QSA_ok x).mp hx)

theorem mem_elemsA {x : Equiv.Perm (Fin 28)} (hx : x ∈ elemsA ()) :
    x ∈ U33.QA.originalSubgroup :=
  (mem_elemsT U33.QA U33.QA_ok x).mp hx

theorem mem_czA {x : Equiv.Perm (Fin 28)} (hx : x ∈ czA ()) : x ∈ U33.QA.originalSubgroup :=
  mem_elemsA (List.mem_filter.mp hx).1

noncomputable abbrev SL : List AA := liftA (sylowA ()) fun _ => mem_sylowA
noncomputable abbrev XL : List AA := liftA (elemsA ()) fun _ => mem_elemsA
noncomputable abbrev CL : List AA := liftA (czA ()) fun _ => mem_czA

theorem mem_SL {s : AA} (hs : s ∈ sylowU33) : s ∈ SL := mem_liftA.mpr (mem_elemsT_QSA hs)

theorem mem_CL {c : AA} (hc : c * (i1A * i1A) = i1A * i1A * c) : c ∈ CL := by
  refine mem_liftA.mpr (List.mem_filter.mpr ⟨(mem_elemsT U33.QA U33.QA_ok _).mpr c.2, ?_⟩)
  rw [decide_eq_true_iff]
  exact congrArg Subtype.val hc

theorem sylow_isPGroup : IsPGroup 2 sylowU33 := by
  have hcard : Nat.card sylowU33 = 64 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe QSA_le_QA).toEquiv, card_group QSA QSA_ok,
      QSA_valid.2.1]
  exact IsPGroup.of_card (n := 6) (by rw [hcard]; norm_num)

theorem sylow_not_dvd_index : ¬ 2 ∣ sylowU33.index := by
  have hcard : Nat.card sylowU33 = 64 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe QSA_le_QA).toEquiv, card_group QSA QSA_ok,
      QSA_valid.2.1]
  have h := Subgroup.card_mul_index sylowU33
  rw [hcard, card_u33A] at h
  have h1 : sylowU33.index = 189 := by omega
  rw [h1]
  decide

end Data

theorem factPa_mem : ∀ x ∈ factPa (), x ∈ U33.QA.originalSubgroup := by
  intro x h
  simp only [factPa, List.mem_cons, List.not_mem_nil, or_false] at h
  have hi := Subgroup.inv_mem _ sg0_mem
  rcases h with h | h | h | h | h | h | h | h | h <;> rw [h]
  exacts [wA_mem _, sg0_mem, wA_mem _, hi, wA_mem _, wA_mem _, wA_mem _, hi, wA_mem _]

theorem factPb_mem : ∀ x ∈ factPb (), x ∈ U33.QA.originalSubgroup := by
  intro x h
  simp only [factPb, List.mem_cons, List.not_mem_nil, or_false] at h
  have hi := Subgroup.inv_mem _ sg0_mem
  rcases h with h | h | h | h | h | h | h | h <;> rw [h]
  exacts [hi, wA_mem _, wA_mem _, hi, wA_mem _, sg0_mem, wA_mem _, sg0_mem]

section Checks


theorem subtype_injective : Function.Injective U33.QA.originalSubgroup.subtype :=
  U33.QA.originalSubgroup.subtype_injective

theorem basic_spec : Q8Rel i1A j1A ∧ Q8Rel i2A j2A ∧ i2A * i2A = i1A * i1A ∧ i1A ∈ u33P ∧
    j1A ∈ u33P ∧ ¬ (i2A ∈ u33P ∧ j2A ∈ u33P) := by
  have h := (Certificates.certificate517002).1
  simp only [u33S7Basic, Bool.and_eq_true, decide_eq_true_iff, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  refine ⟨q8RelB_eq_true_iff.mp ?_, q8RelB_eq_true_iff.mp ?_, Subtype.ext h3,
    (inQP_eq_true_iff (x := i1A)).mp h4, (inQP_eq_true_iff (x := j1A)).mp h5,
    fun ⟨ha, hb⟩ => ?_⟩
  · rw [← q8RelB_map subtype_injective]; exact h1
  · rw [← q8RelB_map subtype_injective]; exact h2
  · have ha' : inQP i2 = true := (inQP_eq_true_iff (x := i2A)).mpr ha
    have hb' : inQP j2 = true := (inQP_eq_true_iff (x := j2A)).mpr hb
    rw [ha', hb'] at h6
    exact absurd h6 (by decide)

theorem class_spec : classCheck i1A j1A SL XL = true ∧ classCheck i2A j2A SL XL = true := by
  have h1 := (Certificates.certificate517002).2.1
  have h2 := (Certificates.certificate517002).2.2.1
  rw [u33S7Class1] at h1
  rw [u33S7Class2] at h2
  refine ⟨?_, ?_⟩
  · rw [← classCheck_map subtype_injective, liftA_map, liftA_map]
    exact h1
  · rw [← classCheck_map subtype_injective, liftA_map, liftA_map]
    exact h2

theorem norm_spec : normAllB i1A j1A CL = true ∧ normAllB i2A j2A CL = true ∧
    normAllB i1A j1A SL = true ∧ normAllB i2A j2A SL = true := by
  have h := (Certificates.certificate517002).2.2.2.1
  simp only [u33S7Norm, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← normAllB_map subtype_injective, liftA_map]; exact h1
  · rw [← normAllB_map subtype_injective, liftA_map]; exact h2
  · rw [← normAllB_map subtype_injective, liftA_map]; exact h3
  · rw [← normAllB_map subtype_injective, liftA_map]; exact h4

theorem q8_spec : q8InCheck SL i1A j1A i2A j2A = true ∧ q8InCheck CL i1A j1A i2A j2A = true := by
  have h := (Certificates.certificate517002).2.2.2.2.1
  simp only [u33S7Q8, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · rw [← q8InCheck_map subtype_injective, liftA_map]; exact h1
  · rw [← q8InCheck_map subtype_injective, liftA_map]; exact h2

theorem edge_spec : edgeB i1A j1A i2A j2A sgA = true ∧
    factB i1A j1A i2A j2A [sgA] paA (liftA (factPa ()) factPa_mem) = true ∧
    factB i1A j1A i2A j2A [sgA] pbA (liftA (factPb ()) factPb_mem) = true ∧
    factB i1A j1A i2A j2A [sgA] sgA [sgA] = true := by
  have h := (Certificates.certificate517002).2.2.2.2.2
  simp only [u33S7Edge, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← edgeB_map subtype_injective]; exact h1
  · rw [← factB_map subtype_injective, liftA_map]; exact h2
  · rw [← factB_map subtype_injective, liftA_map]; exact h3
  · rw [← factB_map subtype_injective]; exact h4

end Checks

section Classes


theorem aEmpty_of_checks {i j : AA} (h : Q8Rel i j) (hz : i * i = i1A * i1A)
    (hc : classCheck i j SL XL = true) (hn : normAllB i j CL = true)
    (hs : normAllB i j SL = true) :
    AEmpty (CoreAssembly.conjClass (Subgroup.closure ({i, j} : Set AA)))
      (Subgroup.closure ({i, j} : Set AA)) := by
  refine aEmpty_conjClass_of_sylow (S := sylowU33) (nonempty_closure_pair_mulEquiv h)
    (isUniqueInvolution_closure_pair h) (fun u hu hu4 => ?_) (fun c hc' => ?_)
    (fun u hu hu4 => classCheck_sound h hc (mem_SL hu) hu4)
  · exact exists_conj_mem_of_le_normalizer (fun s hs' => normAllB_sound h hs (mem_SL hs'))
      sylow_isPGroup sylow_not_dvd_index hu (k := 2) (by rw [hu4]; norm_num)
  · rw [hz] at hc'
    exact normAllB_sound h hn (mem_CL hc')

theorem classes : ∀ T ∈ q8Fam AA, ∃ g : AA, T = conjSub g Q1 ∨ T = conjSub g Q2 := by
  intro T hT
  obtain ⟨h1, h2, -, -, -, -⟩ := basic_spec
  obtain ⟨g, hg⟩ := u33_conj_mem_sylow T (isPGroup_of_q8 hT)
  have hT' : conjSub g⁻¹ T ∈ q8Fam AA := nonempty_conjSub_mulEquiv hT g⁻¹
  have hL : ∀ t ∈ conjSub g⁻¹ T, t ∈ SL := by
    intro t ht
    rw [mem_conjSub_iff, inv_inv] at ht
    apply mem_SL
    have := hg _ ht
    rwa [show g⁻¹ * (g * t * g⁻¹) * g = t by group] at this
  have hT'' : T = conjSub g (conjSub g⁻¹ T) := (conjSub_conjSub_inv g T).symm
  refine ⟨g, ?_⟩
  rcases q8InCheck_sound h1 h2 q8_spec.1 hT' hL with h | h
  · left
    rw [hT'', h]
  · right
    rw [hT'', h]

theorem aEmpty_q8 : ∀ T ∈ q8Fam AA, AEmpty (CoreAssembly.conjClass T) T := by
  obtain ⟨h1, h2, hz2, -, -, -⟩ := basic_spec
  obtain ⟨hc1, hc2⟩ := class_spec
  obtain ⟨hn1, hn2, hs1, hs2⟩ := norm_spec
  exact aEmpty_q8Fam_of_classes classes (aEmpty_of_checks h1 rfl hc1 hn1 hs1)
    (aEmpty_of_checks h2 hz2 hc2 hn2 hs2)

theorem closure_gens_eq_top : Subgroup.closure ({paA, pbA, sgA} : Set AA) = ⊤ := by
  have hK : U33.QA.originalSubgroup =
      Subgroup.closure {g : Equiv.Perm (Fin 28) | g ∈ [U33.pa, U33.pb, U33.sg0]} := by
    rw [U33.QA, certificate_originalSubgroup]
  have htop : Subgroup.closure (((↑) : AA → Equiv.Perm (Fin 28)) ⁻¹'
      {g : Equiv.Perm (Fin 28) | g ∈ [U33.pa, U33.pb, U33.sg0]}) = ⊤ := by
    have key : ∀ {K : Subgroup (Equiv.Perm (Fin 28))} {s : Set (Equiv.Perm (Fin 28))},
        K = Subgroup.closure s → Subgroup.closure (((↑) : K → Equiv.Perm (Fin 28)) ⁻¹' s) = ⊤ := by
      intro K s hKs
      subst hKs
      exact Subgroup.closure_closure_coe_preimage
    exact key hK
  rw [eq_top_iff, ← htop, Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_preimage, Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with hx | hx | hx
  · have : x = paA := Subtype.ext hx
    rw [this]
    exact Subgroup.subset_closure (Set.mem_insert _ _)
  · have : x = pbA := Subtype.ext hx
    rw [this]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  · have : x = sgA := Subtype.ext hx
    rw [this]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))

theorem aStar_vStar {Y : Type} [Group Y] [Finite Y] (θ : Y ≃* AA) :
    ∀ K ∈ q8Fam Y, aStar (q8Fam Y) K = q8Fam Y ∧ vStar (q8Fam Y) K = q8Fam Y := by
  obtain ⟨h1, h2, hz2, hi1, hj1, hout⟩ := basic_spec
  obtain ⟨hedge, hfa, hfb, hfs⟩ := edge_spec
  have hI1 := isUniqueInvolution_closure_pair h1
  have hI2 := isUniqueInvolution_closure_pair h2
  rw [hz2] at hI2
  have hQ1P : Q1 ≤ u33P := closure_pair_le hi1 hj1
  refine aStar_vStar_of_edges_equiv θ (Q₁ := Q1) (Q₂ := Q2) (E := {x | x ∈ [sgA]})
    (nonempty_closure_pair_mulEquiv h1) (nonempty_closure_pair_mulEquiv h2) hI1 hI2 ?_ classes
    ?_ ?_ ?_
  · intro g hg
    haveI := u33P_normal
    have hP : conjSub g u33P = u33P :=
      mem_normalizer_iff_conjSub_eq.mp (by
        rw [Subgroup.normalizer_eq_top_iff.mpr u33P_normal]
        exact Subgroup.mem_top g)
    have hle : Q2 ≤ u33P := by
      rw [← hg, ← hP]
      exact conjSub_mono hQ1P
    exact hout ⟨hle (Subgroup.subset_closure (Set.mem_insert _ _)),
      hle (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))⟩
  · intro T hT hT1 _
    refine q8InCheck_sound h1 h2 q8_spec.2 hT fun t ht => mem_CL ?_
    have h3 := hI1.conj_eq (mem_normalizer_iff_conjSub_eq.mp (hT1 ht))
    calc t * (i1A * i1A) = t * (i1A * i1A) * t⁻¹ * t := by group
      _ = i1A * i1A * t := by rw [h3]
  · intro e he
    rw [Set.mem_setOf_eq, List.mem_singleton] at he
    rw [he]
    exact edgeB_sound h1 h2 hedge
  · rw [eq_top_iff, ← closure_gens_eq_top, Subgroup.closure_le]
    rintro x (rfl | rfl | rfl)
    · exact factB_sound h1 h2 hfa
    · exact factB_sound h1 h2 hfb
    · exact factB_sound h1 h2 hfs

end Classes

end U33S7

end CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7Cert
