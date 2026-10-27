module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7SuzCSCheck
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7SuzCSGrp
public import CFSG.Sporadic.He.Primitive
public import CFSG.Sporadic.SuzOddCore.CTIDefs

public section

namespace CFSG.ComponentClassification.CatFactsL4U4.SuzCS

open CFSG CFSG.LocalCores CFSG.Sporadic.SuzOddCore CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four CFSG.Certificates Subgroup

theorem primOK_parts :
    (fixList 3).length = 100 ∧ (kGens 3).size = 5 ∧ hWords.length = 3 ∧
    (∀ p < 100, (∀ j ∈ transWords.getD p [], j < 5) ∧
      (wordTab 100 (kGens 3) (transWords.getD p []))[0]! = p) ∧
    (∀ w ∈ hWords, (∀ j ∈ w, j < 5) ∧ (wordTab 100 (kGens 3) w)[0]! = 0) ∧
    (∀ p < 100, labList.getD p 0 < 3 ∧ (∀ j ∈ uWords.getD p [], j < 3) ∧
      (wordTab 100 hTabs (uWords.getD p []))[rootList.getD (labList.getD p 0) 0]! = p) ∧
    countBelow 100 (fun p => labList.getD p 0 == 0) = 1 ∧
    countBelow 100 (fun p => labList.getD p 0 == 1) = 36 ∧
    countBelow 100 (fun p => labList.getD p 0 == 2) = 63 := by
  have h := suzCS_three_check
  unfold primOK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, -⟩, h4⟩, -⟩, -⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩ := h
  refine ⟨beq_iff_eq.mp h1, beq_iff_eq.mp h2, beq_iff_eq.mp h4, fun p hp => ?_, fun w hw => ?_,
    fun p hp => ?_, beq_iff_eq.mp h10, beq_iff_eq.mp h11, beq_iff_eq.mp h12⟩
  · have := allBelow_eq_true.mp h7 p hp
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq] at this
    exact this
  · have := List.all_eq_true.mp h8 w hw
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq] at this
    exact this
  · have := allBelow_eq_true.mp h9 p hp
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq] at this
    exact ⟨this.1.1, this.1.2, this.2⟩

theorem hm3 : (fixList 3).length = 100 := primOK_parts.1

theorem invInnerGenArrs_size3 : (invInnerGenArrs 3).size = 5 := by
  simp [invInnerGenArrs, invInnerGenCounts]

@[expose] noncomputable def rho3 :
    invE 3 →* Equiv.Perm (Fin 100) :=
  cRho (i := 3) (by norm_num) hm3

@[expose] noncomputable def kperm3
    (k : ℕ) : Equiv.Perm (Fin 100) :=
  rho3 (innerGenE (i := 3) (by norm_num) k)

theorem tabRep_kperm3
    {k : ℕ} (hk : k < (kGens 3).size) : TabRep (kGens 3)[k]! (kperm3 k) := by
  have h5 : (kGens 3).size = 5 := primOK_parts.2.1
  have hk' : k < (invInnerGenArrs 3).size := by
    rw [invInnerGenArrs_size3]
    rw [h5] at hk
    exact hk
  exact tabRep_kGens (i := 3) (by norm_num) hm3 hk'

@[expose] noncomputable def wordPerm3
    (w : List ℕ) : Equiv.Perm (Fin 100) :=
  (w.map kperm3).prod

theorem wordPerm3_mem
    (w : List ℕ) : wordPerm3 w ∈ rho3.range := by
  refine rho3.range.list_prod_mem fun x hx => ?_
  obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
  exact ⟨_, rfl⟩

theorem tabRep_wordPerm3
    (w : List ℕ) (hw : ∀ j ∈ w, j < 5) : TabRep (wordTab 100 (kGens 3) w) (wordPerm3 w) :=
  tabRep_wordTab (fun j hj => tabRep_kperm3 hj) w
    (fun j hj => by rw [primOK_parts.2.1]; exact hw j hj)

@[expose] noncomputable def hval
    (i : ℕ) : Equiv.Perm (Fin 100) :=
  wordPerm3 (hWords.getD i [])

theorem tabRep_hval
    {i : ℕ} (hi : i < hTabs.size) : TabRep hTabs[i]! (hval i) := by
  have hl : hWords.length = 3 := primOK_parts.2.2.1
  have hi3 : i < hWords.length := by
    simpa [hTabs] using hi
  have hmem : hWords.getD i [] ∈ hWords := by
    rw [List.getD_eq_getElem _ _ hi3]
    exact List.getElem_mem hi3
  have hw := primOK_parts.2.2.2.2.1 _ hmem
  have he : hTabs[i]! = wordTab 100 (kGens 3) (hWords.getD i []) := by
    have hi' : i < (hWords.map (wordTab 100 (kGens 3))).toArray.size := by simpa [hTabs] using hi
    simp only [hTabs]
    rw [getElem!_pos _ i hi', List.getElem_toArray, List.getElem_map,
      List.getD_eq_getElem _ _ hi3]
  rw [he]
  exact tabRep_wordPerm3 _ hw.1

theorem hval_fix
    {i : ℕ} (hi : i < hTabs.size) : hval i 0 = 0 := by
  have hl : hWords.length = 3 := primOK_parts.2.2.1
  have hi3 : i < hWords.length := by
    simpa [hTabs] using hi
  have hmem : hWords.getD i [] ∈ hWords := by
    rw [List.getD_eq_getElem _ _ hi3]
    exact List.getElem_mem hi3
  have hw := primOK_parts.2.2.2.2.1 _ hmem
  have h : (wordTab 100 (kGens 3) (hWords.getD i []))[0]! =
      ((wordPerm3 (hWords.getD i []) 0 : Fin 100) : ℕ) := (tabRep_wordPerm3 _ hw.1).apply 0
  rw [hw.2] at h
  exact Fin.ext h.symm

@[expose] noncomputable def hSub :
    Subgroup (Equiv.Perm (Fin 100)) :=
  Subgroup.closure {g | ∃ i < hTabs.size, hval i = g}

theorem hSub_le :
    hSub ≤ rho3.range := by
  rw [hSub, Subgroup.closure_le]
  rintro _ ⟨i, -, rfl⟩
  exact wordPerm3_mem _

theorem hSub_fix
    {g : Equiv.Perm (Fin 100)} (hg : g ∈ hSub) : g 0 = 0 := by
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨i, hi, rfl⟩ := hg
    exact hval_fix hi
  | one => rfl
  | mul g h _ _ hg hh => rw [Equiv.Perm.mul_apply, hh, hg]
  | inv g _ hg =>
    rw [Equiv.Perm.inv_eq_iff_eq]
    exact hg.symm

@[expose] def lab (p : Fin 100) : Fin 3 := ⟨labList.getD p 0 % 3, Nat.mod_lt _ (by norm_num)⟩

theorem lab_val (p : Fin 100) :
    ((lab p : Fin 3) : ℕ) = labList.getD p 0 := by
  rw [lab]
  exact Nat.mod_eq_of_lt (primOK_parts.2.2.2.2.2.1 p p.2).1

theorem card_lab_eq (i : Fin 3) :
    (Finset.univ.filter fun p : Fin 100 => lab p = i).card = ![1, 36, 63] i := by
  have key : (Finset.univ.filter fun p : Fin 100 => lab p = i).card =
      countBelow 100 (fun p => labList.getD p 0 == i) := by
    rw [countBelow_eq, ← Finset.card_map Fin.valEmbedding]
    congr 1
    ext q
    simp only [Finset.mem_filter, Finset.mem_map, Finset.mem_univ, true_and, Finset.mem_range,
      Fin.valEmbedding_apply, beq_iff_eq]
    constructor
    · rintro ⟨p, hp, rfl⟩
      refine ⟨p.2, ?_⟩
      rw [← lab_val, hp]
    · rintro ⟨hq, hlab⟩
      refine ⟨⟨q, hq⟩, ?_, rfl⟩
      apply Fin.ext
      rw [lab_val]
      exact hlab
  rw [key]
  obtain ⟨-, -, -, -, -, -, h0, h1, h2⟩ := primOK_parts
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

theorem lab_blocks : ∀ S : Finset (Fin 3), (0 : Fin 3) ∈ S →
    (∑ i ∈ S, (![1, 36, 63] : Fin 3 → ℕ) i) ∣ 100 → S = {0} ∨ S = Finset.univ := by
  decide

theorem lab_zero : lab 0 = 0 := by decide

@[expose] noncomputable def uPerm
    (p : Fin 100) : Equiv.Perm (Fin 100) :=
  ((uWords.getD p []).map hval).prod

theorem uPerm_mem
    (p : Fin 100) : uPerm p ∈ hSub := by
  have hu := (primOK_parts.2.2.2.2.2.1 p p.2).2.1
  refine hSub.list_prod_mem fun x hx => ?_
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
  have hj3 : j < hTabs.size := by
    have := hu j hj
    simpa [hTabs, primOK_parts.2.2.1] using this
  exact Subgroup.subset_closure ⟨j, hj3, rfl⟩

theorem uPerm_apply
    (p : Fin 100) (r : Fin 100) (hr : (r : ℕ) = rootList.getD (labList.getD p 0) 0) :
    uPerm p r = p := by
  obtain ⟨-, hu, hw⟩ := primOK_parts.2.2.2.2.2.1 p p.2
  have hrep : TabRep (wordTab 100 hTabs (uWords.getD p [])) (uPerm p) :=
    tabRep_wordTab (fun j hj => tabRep_hval hj) _ (fun j hj => by
      have := hu j hj
      simpa [hTabs, primOK_parts.2.2.1] using this)
  have h := hrep.apply r
  rw [hr, hw] at h
  exact Fin.ext h.symm

theorem rho3_pretransitive :
    MulAction.IsPretransitive rho3.range (Fin 100) := by
  have hg : ∀ p : Fin 100, ∃ g ∈ rho3.range, g 0 = p := by
    intro p
    obtain ⟨hw, h0⟩ := primOK_parts.2.2.2.1 p p.2
    refine ⟨wordPerm3 (transWords.getD p []), wordPerm3_mem _, ?_⟩
    have h : (wordTab 100 (kGens 3) (transWords.getD p []))[0]! =
        ((wordPerm3 (transWords.getD p []) 0 : Fin 100) : ℕ) := (tabRep_wordPerm3 _ hw).apply 0
    rw [h0] at h
    exact Fin.ext h.symm
  refine ⟨fun x y => ?_⟩
  obtain ⟨gx, hgx, hx⟩ := hg x
  obtain ⟨gy, hgy, hy⟩ := hg y
  refine ⟨⟨gy * gx⁻¹, rho3.range.mul_mem hgy (rho3.range.inv_mem hgx)⟩, ?_⟩
  rw [Subgroup.smul_def, Equiv.Perm.smul_def]
  simp only [Equiv.Perm.mul_apply]
  rw [← hx, (Equiv.Perm.inv_eq_iff_eq).2 rfl, hy]

theorem rho3_isPreprimitive :
    MulAction.IsPreprimitive rho3.range (Fin 100) := by
  have := rho3_pretransitive
  refine CFSG.Sporadic.He.isPreprimitive_of_suborbit_labels_witness (0 : Fin 100)
    (hSub.subgroupOf rho3.range) ?_ lab ?_ ?_
  · intro h hh
    rw [Subgroup.mem_subgroupOf] at hh
    rw [Subgroup.smul_def, Equiv.Perm.smul_def]
    exact hSub_fix hh
  · intro p q hpq
    have hr : rootList.getD (labList.getD p 0) 0 = rootList.getD (labList.getD q 0) 0 := by
      rw [← lab_val, ← lab_val, hpq]
    have hrlt : rootList.getD (labList.getD p 0) 0 < 100 := by
      have := (primOK_parts.2.2.2.2.2.1 p p.2).1
      interval_cases h : labList.getD p 0 <;> simp [rootList]
    set r : Fin 100 := ⟨_, hrlt⟩
    have hup := uPerm_apply p r rfl
    have huq := uPerm_apply q r (by rw [← hr])
    refine ⟨⟨uPerm q * (uPerm p)⁻¹, rho3.range.mul_mem (hSub_le (uPerm_mem q))
      (rho3.range.inv_mem (hSub_le (uPerm_mem p)))⟩, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf]
      exact hSub.mul_mem (uPerm_mem q) (hSub.inv_mem (uPerm_mem p))
    · rw [Subgroup.smul_def, Equiv.Perm.smul_def]
      simp only [Equiv.Perm.mul_apply]
      rw [Equiv.Perm.inv_eq_iff_eq.2 hup.symm, huq]
  · intro S hS hdvd
    simp only [card_lab_eq, Fintype.card_fin] at hdvd
    rw [lab_zero] at hS ⊢
    rcases lab_blocks S hS hdvd with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

theorem card_range_rho3_dvd :
    100 ∣ Nat.card rho3.range := by
  have := rho3_pretransitive
  have horb : MulAction.orbit rho3.range (0 : Fin 100) = Set.univ :=
    MulAction.orbit_eq_univ _ _
  have h := MulAction.index_stabilizer (G := rho3.range) (x := (0 : Fin 100))
  rw [horb, Set.ncard_univ, Nat.card_fin] at h
  calc 100 = (MulAction.stabilizer rho3.range (0 : Fin 100)).index := h.symm
    _ ∣ Nat.card rho3.range := Subgroup.index_dvd_card _

theorem card_ker_mul_range_rho3 :
    Nat.card rho3.ker * Nat.card rho3.range = 1209600 := by
  have h := card_ker_cRho (i := 3) (by norm_num) hm3
  rw [show cRho (i := 3) (by norm_num) hm3 = rho3 from rfl] at h
  simpa [invInnerOrders] using h

theorem le_ker_or_dvd
    (N : Subgroup (invE 3)) [hN : N.Normal] : N ≤ rho3.ker ∨ 100 ∣ Nat.card N := by
  by_cases h : N ≤ rho3.ker
  · exact Or.inl h
  · right
    obtain ⟨n, hn, hnk⟩ := Set.not_subset.mp h
    have hρn : rho3 n ≠ 1 := hnk
    obtain ⟨p, hp⟩ : ∃ p, rho3 n p ≠ p := by
      by_contra hc
      push Not at hc
      exact hρn (Equiv.ext hc)
    have := rho3_isPreprimitive
    have hNX : (N.map rho3.rangeRestrict).Normal :=
      hN.map _ (MonoidHom.rangeRestrict_surjective _)
    have h100 := card_dvd_of_normal (N.map rho3.rangeRestrict) (g := rho3.rangeRestrict n)
      ⟨n, hn, rfl⟩ (x := p) (by
        rw [Subgroup.smul_def, Equiv.Perm.smul_def, MonoidHom.coe_rangeRestrict]
        exact hp)
    rw [Nat.card_fin] at h100
    exact h100.trans (Subgroup.card_map_dvd _ _)

theorem three_model
    (B : Subgroup (invE 3)) (hB : IsComponent B) (hcard : Nat.card (B ⧸ center B) = 20160) :
    False := by
  have hE : Nat.card (invE 3) = 1209600 := by
    rw [card_invE (i := 3) (by norm_num)]
    rfl
  have hBn : B.Normal := normal_of_component hB Nat.prime_seven (by rw [hcard]; norm_num)
    (by rw [hE]; decide)
  have hBc : Nat.card B = 20160 * Nat.card (center B) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center B), hcard]
  have hBd : Nat.card B ∣ 1209600 := hE ▸ Subgroup.card_subgroup_dvd_card B
  have hZ60 : Nat.card (center B) ∣ 60 := by
    rw [hBc, show (1209600 : ℕ) = 20160 * 60 by norm_num] at hBd
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) hBd
  have hZpos : 0 < Nat.card (center B) := Nat.card_pos
  have hKX := card_ker_mul_range_rho3
  have hX := card_range_rho3_dvd
  have hXpos : 0 < Nat.card rho3.range := Nat.card_pos
  rcases le_ker_or_dvd B with hBk | hB100
  · have hle := Subgroup.card_le_of_le hBk
    have hX100 : 100 ≤ Nat.card rho3.range := Nat.le_of_dvd hXpos hX
    nlinarith
  have h5 : 5 ∣ Nat.card (center B) := by
    rw [hBc] at hB100
    omega
  set Z : Subgroup (invE 3) := (center B).map B.subtype with hZ
  have hZn : Z.Normal := ConjAct.normal_of_characteristic_of_normal
  have hZc : Nat.card Z = Nat.card (center B) :=
    Subgroup.card_map_of_injective B.subtype_injective
  rcases le_ker_or_dvd Z with hZk | hZ100
  · have h1 : Nat.card Z ∣ Nat.card rho3.ker := Subgroup.card_dvd_of_le hZk
    rw [hZc] at h1
    obtain ⟨m, hm⟩ := hX
    rw [hm] at hKX
    have h2 : Nat.card rho3.ker ∣ 12096 := ⟨m, by linarith⟩
    have := (h5.trans h1).trans h2
    norm_num at this
  · rw [hZc] at hZ100
    have := Nat.le_of_dvd (by norm_num) hZ60
    have := Nat.le_of_dvd hZpos hZ100
    omega

end CFSG.ComponentClassification.CatFactsL4U4.SuzCS
