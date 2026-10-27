module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.PinSub
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.J3ArrInj
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.J3
public import Certificates.Certificate24591
public import Certificates.Certificate24595
public import Certificates.Certificate24607

public section

namespace CFSG.EvenSporadicStandard.Fin76b.J3

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open CFSG.EvenSporadicStandard.HypOne CFSG.EvenSporadicStandard.HypOne.J3

private theorem sylList_eq' : sylList = (mulClosureH 6156 sgP0 128).1 := by
  unfold sylList
  rfl

theorem pinModel_j3P :
    ∃ (T E : Subgroup ↥j3P) (t : ↥j3P), PinModel ↥j3P T E t := by
  have hD := j3_groupData
  have hn : 6156 < 2 ^ 32 := by norm_num
  have hsyl := Certificates.certificate24431.1
  simp only [CFSG.EvenSporadicStandard.HypOne.J3.sylowData, Bool.and_eq_true] at hsyl
  obtain ⟨⟨⟨⟨⟨⟨⟨hu, ht0⟩, ht1⟩, hs0⟩, hs1⟩, hs2⟩, hz0⟩, hz1⟩ := hsyl
  simp only [sylowFourOK, Bool.and_eq_true, beq_iff_eq] at hs0
  obtain ⟨⟨⟨⟨⟨⟨hcg, hsg⟩, htree⟩, hclosed⟩, hdist⟩, hsize⟩, -⟩ := hs0
  rw [Array.all_eq_true'] at hsg
  simp only [Bool.and_eq_true] at hsg
  have hsgA : ∀ x ∈ sgP0, permOK 6156 x = true := fun x hx => (hsg x hx).1.1
  have hsginv : ∀ x ∈ sgP0, invOK 6156 x (invT 6156 x) = true := fun x hx => (hsg x hx).1.2
  obtain ⟨hErep, hcov, hcard⟩ :=
    enum_spec hn hsgA hsginv htree (closedOK_of_closedOKH hclosed) hdist
  rw [← sylList_eq'] at hErep hcov hcard hsize hdist
  set S := closure (tp 6156 '' {x | x ∈ sgP0}) with hSdef
  have rt0 := rep_tp ht0
  set t := tp 6156 t0 with htdef
  have hgenP : ∀ x ∈ sgP0, tp 6156 x ∈ j3P ∧ tp 6156 x * t = t * tp 6156 x := by
    intro x hx
    have h2 := (hsg x hx).2
    simp only [memP, Bool.and_eq_true] at h2
    have rx := rep_tp (hsgA x hx)
    exact ⟨(hD.sift x _ rx).1 h2.1, (commTT_iff rx rt0).1 h2.2⟩
  have hSle : S ≤ j3P ⊓ centralizer ({t} : Set (Equiv.Perm (Fin 6156))) := by
    rw [hSdef, closure_le]
    rintro _ ⟨x, hx, rfl⟩
    exact mem_inf.2 ⟨(hgenP x hx).1, mem_centralizer_singleton_iff.2 (hgenP x hx).2⟩
  have hSP : S ≤ j3P := hSle.trans inf_le_left
  have hSc : ∀ x ∈ S, x * t = t * x := fun x hx =>
    mem_centralizer_singleton_iff.1 (mem_inf.1 (hSle hx)).2
  have hsz : sylList.size = 128 := hsize
  have hScard : Nat.card S = 128 := by rw [hcard, hsize]
  have hS2 : IsPGroup 2 S := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact IsPGroup.of_card (n := 7) (by rw [hScard]; norm_num)
  have hE : ∀ k < 128, Rep 6156 sylList[k]! (tablePerm 6156 sylList[k]!) ∧
      tablePerm 6156 sylList[k]! ∈ S := fun k hk => hErep k (by rw [hsize]; exact hk)
  have hchk := Certificates.certificate24591
  simp only [j3CenterCheck, Bool.and_eq_true] at hchk
  obtain ⟨⟨hA, hB⟩, hC⟩ := hchk
  rw [Array.any_eq_true] at hA hC
  rw [Array.all_eq_true'] at hB
  obtain ⟨k0, hk0, hk0e⟩ := hA
  obtain ⟨k1, hk1, hk1e⟩ := hC
  rw [← getElem!_pos sylList k0 hk0] at hk0e
  rw [← getElem!_pos sylList k1 hk1] at hk1e
  have htS : t ∈ S := by
    obtain ⟨hr, hm⟩ := hE k0 (hsz ▸ hk0)
    have := (tblEq_iff_eq hr rt0).1 hk0e
    rw [← this]
    exact hm
  have hsqE : ∃ g ∈ S, g * g = t := by
    obtain ⟨hr, hm⟩ := hE k1 (hsz ▸ hk1)
    exact ⟨_, hm, (tblEq_iff_eq (Rep.compT hr hr) rt0).1 hk1e⟩
  have hcenS : ∀ y ∈ S, (∀ x ∈ S, x * y = y * x) → y = 1 ∨ y = t := by
    intro y hyS hy
    obtain ⟨k, hk, hrep⟩ := hcov y hyS
    have hall : (sgP0.all fun g => commTT 6156 sylList[k]! g) = true := by
      rw [Array.all_eq_true']
      intro g hg
      refine (commTT_iff hrep (rep_tp (hsgA g hg))).2 ?_
      exact (hy (tp 6156 g) (subset_closure ⟨g, hg, rfl⟩)).symm
    have h := hB sylList[k]! (getElem!_mem_array hk)
    simp only [Bool.or_eq_true, Bool.not_eq_true'] at h
    rcases h with (h | h) | h
    · rw [hall] at h
      exact absurd h (by decide)
    · exact Or.inl ((tblEq_idT_iff hn hrep).1 h)
    · exact Or.inr ((tblEq_iff_eq hrep rt0).1 h)
  obtain ⟨hP0, h20, hc0, hR1, hP1, h21, hc1, hcls⟩ := class_data
  have ht2 : t * t = 1 := by
    rw [← sq, htdef, ← h20]
    exact pow_orderOf_eq_one _
  have ht1' : t ≠ 1 := fun h => by
    rw [htdef] at h
    rw [h, orderOf_one] at h20
    exact absurd h20 (by norm_num)
  have hchkE := Certificates.certificate24595
  simp only [j3E_check, Bool.and_eq_true, decide_eq_true_eq] at hchkE
  obtain ⟨⟨⟨⟨hec, htab⟩, htlt⟩, ht0e⟩, hid⟩ := hchkE
  rw [tableOK] at htab
  have hmulE : ∀ a b, a < 128 → b < 128 → mulJ3 a b < 128 ∧
      tablePerm 6156 sylList[a]! * tablePerm 6156 sylList[b]! =
        tablePerm 6156 sylList[mulJ3 a b]! := by
    intro a b ha hb
    have h1 := allIn_eq_true.1 (allIn_eq_true.1 htab a (Nat.zero_le _) ha) b (Nat.zero_le _) hb
    rw [Bool.and_eq_true, decide_eq_true_eq] at h1
    exact ⟨h1.1, (tblEq_iff_eq (Rep.compT (hE a ha).1 (hE b hb).1) (hE _ h1.1).1).1 h1.2⟩
  have hnodup : (sylList.toList.map (tablePerm 6156)).Nodup :=
    nodup_of_hkeysDistinct (forall₂_tablePerm (e := fun k => tablePerm 6156 sylList[k]!)
      (fun k hk => (hErep k hk).1)) hdist
  have hinjE : ∀ a b, a < 128 → b < 128 →
      tablePerm 6156 sylList[a]! = tablePerm 6156 sylList[b]! → a = b := by
    intro a b ha hb h
    exact arr_getElem!_inj sylList (tablePerm 6156) hnodup (by rw [hsz]; exact ha)
      (by rw [hsz]; exact hb) h
  exact PinModel.of_sub_table hSP hS2 ⟨392445, by decide, by rw [card_j3P, hScard]⟩ ht2 ht1' htS
    hSc hcenS 128 (fun a => tablePerm 6156 sylList[a]!) mulJ3 tIdxJ3 (fun a ha => (hE a ha).2)
    (fun x hx => by
      obtain ⟨k, hk, hrep⟩ := hcov x hx
      exact ⟨k, hsz ▸ hk, tablePerm_eq hrep⟩) hinjE (fun a b ha hb => hmulE a b ha hb)
    ((tblEq_idT_iff hn (hE 0 (by norm_num)).1).1 hid)
    ⟨htlt, (tblEq_iff_eq (hE _ htlt).1 rt0).1 ht0e⟩
    (by norm_num) Certificates.certificate24607

end CFSG.EvenSporadicStandard.Fin76b.J3
