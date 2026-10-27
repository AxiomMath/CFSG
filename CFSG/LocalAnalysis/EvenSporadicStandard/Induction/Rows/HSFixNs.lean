module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.BInvCentGeneric
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.HarEval
public import CFSG.Sporadic.SmallOddCore.HS
public import Certificates.Certificate27201

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
  CFSG.Sporadic.Recognition.HSMultiplier

theorem lift_mk_mem {G : Type*} [Group G] {ι : Type} (H : Subgroup G) (f : ι → G)
    (w : List (ι × Bool)) (hw : ∀ l ∈ w, f l.1 ∈ H) : FreeGroup.lift f (FreeGroup.mk w) ∈ H := by
  rw [FreeGroup.lift_mk]
  refine H.list_prod_mem fun x hx => ?_
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
  obtain ⟨i, b⟩ := l
  cases b
  · exact H.inv_mem (hw _ hl)
  · exact hw _ hl

theorem not_isSolvable_of_a5 {G : Type*} [Group G] (H : Subgroup G) {a b : G} (ha : a ∈ H)
    (hb : b ∈ H) (hoa : orderOf a = 2) (hob : orderOf b = 3) (hoab : orderOf (a * b) = 5) :
    ¬ Group.IsSolvable ↥H := by
  have ha2 : a * a = 1 := by
    have := pow_orderOf_eq_one a
    rwa [hoa, pow_two] at this
  have hb3 : b * b * b = 1 := by
    have := pow_orderOf_eq_one b
    rwa [hob, pow_succ, pow_two] at this
  have hab5 : (a * b) ^ 5 = 1 := by
    have := pow_orderOf_eq_one (a * b)
    rwa [hoab] at this
  have ha1 : a ≠ 1 := fun h => by
    rw [h, orderOf_one] at hoa
    exact absurd hoa (by norm_num)
  have hP := CFSG.EvenSporadicStandard.Induction.Hyp.isPerfect_closure_pair ha2 hb3 hab5
  have hle : Subgroup.closure ({a, b} : Set G) ≤ H := by
    rw [Subgroup.closure_le]
    intro z hz
    rcases hz with h | h
    · rw [h]; exact ha
    · rw [Set.mem_singleton_iff] at h
      rw [h]; exact hb
  have hamem : a ∈ Subgroup.closure ({a, b} : Set G) := Subgroup.subset_closure (Set.mem_insert _ _)
  have : Nontrivial ↥(Subgroup.closure ({a, b} : Set G)) :=
    ⟨⟨⟨a, hamem⟩, 1, fun h => ha1 (congrArg Subtype.val h)⟩⟩
  intro hsolv
  have hs : Group.IsSolvable ↥(Subgroup.closure ({a, b} : Set G)) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
  exact Group.IsPerfect.not_isSolvable _ hs

theorem hns_sound (r : Fin 4) (h : hnsCheck r = true) :
    ∃ a b : Equiv.Perm (Fin 3850),
      (∀ H : Subgroup (Equiv.Perm (Fin 3850)),
        (∀ i : Fin 4, i.val < hnsNum r → tp 3850 (hnsGen r i) ∈ H) → a ∈ H ∧ b ∈ H) ∧
      orderOf a = 2 ∧ orderOf b = 3 ∧ orderOf (a * b) = 5 := by
  have hn : (3850 : ℕ) < 2 ^ 32 := by norm_num
  simp only [hnsCheck, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, forall_const,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hwa, hwb⟩, hgen⟩, hA⟩, hB⟩, hAB⟩ := h
  have hg : ∀ i, Rep 3850 (hnsGen r i) (tp 3850 (hnsGen r i)) := fun i => rep_tp (hgen i).1
  have hgi : ∀ i, Rep 3850 (hnsGenI r i) (tp 3850 (hnsGen r i))⁻¹ := fun i =>
    Rep.inv_of_invOK (hg i) (hgen i).2
  have hAr : Rep 3850 (hnsA r) (FreeGroup.lift (fun i => tp 3850 (hnsGen r i))
      (FreeGroup.mk (hnsWordA r))) := rep_evalW hn hg hgi (hnsWordA r)
  have hBr : Rep 3850 (hnsB r) (FreeGroup.lift (fun i => tp 3850 (hnsGen r i))
      (FreeGroup.mk (hnsWordB r))) := rep_evalW hn hg hgi (hnsWordB r)
  refine ⟨FreeGroup.lift (fun i => tp 3850 (hnsGen r i)) (FreeGroup.mk (hnsWordA r)),
    FreeGroup.lift (fun i => tp 3850 (hnsGen r i)) (FreeGroup.mk (hnsWordB r)),
    fun H hH => ⟨lift_mk_mem H (fun i => tp 3850 (hnsGen r i)) (hnsWordA r)
      fun l hl => hH l.1 (hwa l hl),
      lift_mk_mem H (fun i => tp 3850 (hnsGen r i)) (hnsWordB r)
        fun l hl => hH l.1 (hwb l hl)⟩, ?_, ?_, ?_⟩
  · exact (ordTest_iff_perm hAr (by norm_num)).1 hA
  · exact (ordTest_iff_perm hBr (by norm_num)).1 hB
  · exact (ordTest_iff_perm (Rep.compT hAr hBr) (by norm_num)).1 hAB

theorem hsC_mem_gen {r : ClassRow} {T : Table} (hT : T ∈ r.centGens) : tp 3850 T ∈ hsC r :=
  Subgroup.subset_closure ⟨T, by simpa using hT, rfl⟩

theorem hs_row_a5 {r : ClassRow} (k : Fin 4) (hk : hnsCheck k = true)
    (hgens : ∀ i : Fin 4, i.val < hnsNum k → hnsGen k i ∈ r.centGens) :
    ¬ Group.IsSolvable ↥(hsC r) := by
  obtain ⟨a, b, hH, hoa, hob, hoab⟩ := hns_sound k hk
  obtain ⟨ha, hb⟩ := hH (hsC r) fun i hi => hsC_mem_gen (hgens i hi)
  exact not_isSolvable_of_a5 _ ha hb hoa hob hoab

section


theorem hsRow_nonsolvable {r : ClassRow} (hr : r ∈ hsRows) :
    ¬ Group.IsSolvable
      ↥(hsP ⊓ Subgroup.centralizer ({tp 3850 r.rep} : Set (Equiv.Perm (Fin 3850)))) := by
  obtain ⟨-, -, -, hrows, -⟩ := hs_involution_centralizers
  have hC : hsC r = hsP ⊓ Subgroup.centralizer ({tp 3850 r.rep} : Set (Equiv.Perm (Fin 3850))) :=
    (hrows r hr).2.2.2.1
  rw [← hC]
  have hall : ∀ i : Fin 4, hnsCheck i = true := by
    have h := Certificates.certificate27201
    simp only [hnsOK, List.all_eq_true, List.mem_finRange, forall_const] at h
    exact h
  simp only [hsRows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · refine hs_row_a5 0 (hall 0) fun i hi => ?_
    fin_cases i
    · simp [hnsGen, hnsBase]
    · simp [hnsGen, hnsBase]
    · exact absurd hi (by simp [hnsNum])
    · exact absurd hi (by simp [hnsNum])
  · refine hs_row_a5 1 (hall 1) fun i hi => ?_
    fin_cases i <;> simp [hnsGen, hnsBase]
  · refine hs_row_a5 2 (hall 2) fun i hi => ?_
    fin_cases i <;> simp [hnsGen, hnsBase]
  · refine hs_row_a5 3 (hall 3) fun i hi => ?_
    fin_cases i <;> simp [hnsGen, hnsBase]

end

end CFSG.EvenSporadicStandard.TwoHS
