module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.ThmCDataModel
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.J3
public import Certificates.Certificate25510

public section

namespace CFSG.EvenSporadicStandard.Fin76b.J3

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open CFSG.EvenSporadicStandard.HypOne CFSG.EvenSporadicStandard.HypOne.J3

private theorem sylXList_eq' : sylXList = (mulClosureH 6156 sylXGens 256).1 := by
  unfold sylXList
  rfl

private theorem sylXList_eq'' : sylXList = (mulClosureH 6156 j3SylowGenTbls.toArray 256).1 := by
  unfold sylXList sylXGens
  rfl

theorem outerData_j3P :
    OuterData ↥j3P := by
  have hD := j3_groupData
  have hn : 6156 < 2 ^ 32 := by norm_num
  obtain ⟨hU2, -, -, -, -, -, hSR, -, -⟩ :=
    j3_centData
  obtain ⟨e, he, -, -, hcardAut⟩ := ctuc_j3_full_automorphism_permutation_model
  have hfin : Finite (MulAut ↥j3P) :=
    Nat.finite_of_card_ne_zero (by rw [hcardAut]; norm_num)
  have hsyl := Certificates.certificate24431.1
  simp only [CFSG.EvenSporadicStandard.HypOne.J3.sylowData, Bool.and_eq_true] at hsyl
  obtain ⟨⟨⟨⟨⟨⟨⟨hu, ht0⟩, ht1⟩, hs0⟩, hs1⟩, hs2⟩, hz0⟩, hz1⟩ := hsyl
  simp only [sylowFourOK, Bool.and_eq_true, beq_iff_eq] at hs1
  obtain ⟨⟨⟨⟨⟨⟨hcg, hsg⟩, htree⟩, hclosed⟩, hdist⟩, hsize⟩, -⟩ := hs1
  rw [Array.all_eq_true'] at hsg
  simp only [Bool.and_eq_true] at hsg
  have hsgA : ∀ x ∈ sylXGens, permOK 6156 x = true := fun x hx => (hsg x hx).1.1
  have hsginv : ∀ x ∈ sylXGens, invOK 6156 x (invT 6156 x) = true := fun x hx => (hsg x hx).1.2
  obtain ⟨hErep, hcov, hcard⟩ :=
    enum_spec hn hsgA hsginv htree (closedOK_of_closedOKH hclosed) hdist
  try rw [← sylXList_eq'] at hErep
  try rw [← sylXList_eq''] at hErep
  try rw [← sylXList_eq'] at hcov
  try rw [← sylXList_eq''] at hcov
  try rw [← sylXList_eq'] at hcard
  try rw [← sylXList_eq''] at hcard
  try rw [← sylXList_eq'] at hsize
  try rw [← sylXList_eq''] at hsize
  try rw [← sylXList_eq'] at hdist
  try rw [← sylXList_eq''] at hdist
  set S := closure (tp 6156 '' {x | x ∈ sylXGens}) with hSdef
  have rt0 := rep_tp ht0
  set t := tp 6156 t0 with htdef
  have hSc : ∀ x ∈ S, x * t = t * x := by
    have hle : S ≤ centralizer ({t} : Set (Equiv.Perm (Fin 6156))) := by
      rw [hSdef, closure_le]
      rintro _ ⟨x, hx, rfl⟩
      have h2 := (hsg x hx).2
      simp only [memR, Bool.and_eq_true] at h2
      exact mem_centralizer_singleton_iff.2 ((commTT_iff (rep_tp (hsgA x hx)) rt0).1 h2.2)
    exact fun x hx => mem_centralizer_singleton_iff.1 (hle hx)
  have hchk := Certificates.certificate25510
  simp only [j3OuterCheck, Bool.and_eq_true] at hchk
  obtain ⟨⟨hA, hB⟩, hC⟩ := hchk
  rw [Array.any_eq_true] at hA hC
  rw [Array.all_eq_true'] at hB
  obtain ⟨k0, hk0, hk0e⟩ := hA
  obtain ⟨k1, hk1, hk1e⟩ := hC
  rw [← getElem!_pos sylXList k0 hk0] at hk0e
  rw [← getElem!_pos sylXList k1 hk1] at hk1e
  have hsz : sylXList.size = 256 := hsize
  have hE : ∀ k < sylXList.size, Rep 6156 sylXList[k]! (tablePerm 6156 sylXList[k]!) ∧
      tablePerm 6156 sylXList[k]! ∈ S := hErep
  have htS : t ∈ S := by
    obtain ⟨hr, hm⟩ := hE k0 hk0
    have := (tblEq_iff_eq hr rt0).1 hk0e
    rw [← this]
    exact hm
  have hcenS : ∀ y ∈ S, (∀ x ∈ S, x * y = y * x) → y = 1 ∨ y = t := by
    intro y hyS hy
    obtain ⟨k, hk, hrep⟩ := hcov y hyS
    have hall : (sylXGens.all fun g => commTT 6156 sylXList[k]! g) = true := by
      rw [Array.all_eq_true']
      intro g hg
      refine (commTT_iff hrep (rep_tp (hsgA g hg))).2 ?_
      exact (hy (tp 6156 g) (subset_closure ⟨g, hg, rfl⟩)).symm
    have h := hB sylXList[k]! (getElem!_mem_array hk)
    simp only [Bool.or_eq_true, Bool.not_eq_true'] at h
    rcases h with (h | h) | h
    · rw [hall] at h
      exact absurd h (by decide)
    · exact Or.inl ((tblEq_idT_iff hn hrep).1 h)
    · exact Or.inr ((tblEq_iff_eq hrep rt0).1 h)
  obtain ⟨hP0, h20, -, -, -, -, -, -⟩ := class_data
  have ht2 : t * t = 1 := by
    rw [← sq, htdef, ← h20]
    exact pow_orderOf_eq_one _
  have ht1' : t ≠ 1 := fun h => by
    rw [htdef] at h
    rw [h, orderOf_one] at h20
    exact absurd h20 (by norm_num)
  have hfour : ∃ g : Equiv.Perm (Fin 6156), g ∈ j3P ∧ g * g * (g * g) = t := by
    simp only [Bool.and_eq_true] at hk1e
    obtain ⟨hr, hm⟩ := hE k1 hk1
    refine ⟨_, (hD.sift _ _ hr).1 hk1e.2, ?_⟩
    exact (tblEq_iff_eq (Rep.compT (Rep.compT hr hr) (Rep.compT hr hr)) rt0).1 hk1e.1
  have hSR' : S ≤ j3R := hSR
  have hKcard : Nat.card (S.subgroupOf j3R) = 256 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSR').toEquiv, hcard]
    exact hsz
  have hK2 : IsPGroup 2 (S.subgroupOf j3R) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact IsPGroup.of_card (n := 8) (by rw [hKcard]; norm_num)
  have hKidx : ¬ 2 ∣ (S.subgroupOf j3R).index := by
    have h := (S.subgroupOf j3R).index_mul_card
    rw [hKcard, Nat.card_congr e.toEquiv, hcardAut] at h
    have : (S.subgroupOf j3R).index = 392445 := by omega
    rw [this]
    norm_num
  have htR : t ∈ j3R := (le_sup_left : j3P ≤ j3P ⊔ zpowers j3u) hP0
  have hr : e ⟨t, htR⟩ = MulAut.conj (⟨t, hP0⟩ : ↥j3P) := by
    refine MulEquiv.ext fun p => Subtype.ext ?_
    rw [he]
    simp [MulAut.conj_apply]
  obtain ⟨g, hgP, hg4⟩ := hfour
  refine OuterData.of_model e (S.subgroupOf j3R) hK2 hKidx ⟨t, hP0⟩ ⟨t, htR⟩ hr
    (Subtype.ext ht2) (fun h => ht1' (congrArg Subtype.val h)) ⟨⟨g, hgP⟩, Subtype.ext hg4⟩
    (Subgroup.mem_subgroupOf.2 htS) fun y hy => ⟨fun hall => ?_, fun h => ?_⟩
  · have hcomm : ∀ x ∈ S, x * (y : Equiv.Perm (Fin 6156)) = (y : Equiv.Perm (Fin 6156)) * x :=
      fun x hx => congrArg Subtype.val (hall ⟨x, hSR' hx⟩ (Subgroup.mem_subgroupOf.2 hx))
    rcases hcenS y (Subgroup.mem_subgroupOf.1 hy) hcomm with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  · rintro x hx
    rcases h with rfl | rfl
    · simp
    · exact Subtype.ext (hSc x (Subgroup.mem_subgroupOf.1 hx))

end CFSG.EvenSporadicStandard.Fin76b.J3
