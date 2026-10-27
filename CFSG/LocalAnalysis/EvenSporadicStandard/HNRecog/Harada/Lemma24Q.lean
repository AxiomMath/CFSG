module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.GH73.Statement
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.Lemma24Count
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.Lemma24X0
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.Lemma24QuotOdd
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.Lemma24QuotCenter
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.Lemma24QX0

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup CFSG.GH74.Uniqueness.SU.SU5 CFSG.SectionRank

theorem false_of_quotient_data (hGH : GH73.GH73TheoremA64K) {Q : Type} [Group Q] [Finite Q]
    (hK : IsKGroupCat Q)
    (hO : ∀ N : Subgroup Q, N.Normal → Odd (Nat.card N) → N = ⊥)
    (hmax : ∀ R : Subgroup Q, IsPGroup 2 R → Nat.card R ≤ 64)
    {F P : Subgroup Q} (hFp : ⁅F, F⁆ = F)
    (hFz : ∀ f ∈ F, (∀ g ∈ F, f * g = g * f) → f = 1)
    (hPF : P ≤ F) (hPcard : Nat.card P = 64) (hPA8 : IsA8Type ↥P)
    {x : Q} (hx2 : x ^ 2 = 1) (hx1 : x ≠ 1)
    (hC : Nat.card ↥(centralizer ({x} : Set Q)) = 480)
    {M : Subgroup Q} (hMC : M ≤ centralizer ({x} : Set Q)) (hMp : ⁅M, M⁆ = M)
    (hM : Nat.card M = 60)
    {I : Set Q} (hIcard : I.ncard = 46)
    (hI : ∀ c ∈ I, c ∈ centralizer ({x} : Set Q) ∧ c ^ 2 = 1 ∧ c ≠ 1 ∧ IsConj x c)
    (hJ : ∀ c ∈ centralizer ({x} : Set Q), c ^ 2 = 1 → c ≠ 1 → IsConj x c → c ∈ I) :
    False := by
  classical
  obtain ⟨X0, hX0n, hX0p, hX0max⟩ := exists_largest_perfect Q
  haveI : X0.Normal := hX0n
  have hFX0 : F ≤ X0 := hX0max F hFp
  have hMX0 : M ≤ X0 := hX0max M hMp
  have hPX0 : P ≤ X0 := hPF.trans hFX0
  have hP2 : IsPGroup 2 P := IsPGroup.of_card (n := 6) (by rw [hPcard]; norm_num)
  have h2 : ∀ R : Subgroup Q, IsPGroup 2 R → R ≤ X0 :=
    le_of_isPGroup_of_normal hX0n hPX0 hP2 (fun R hR => by rw [hPcard]; exact hmax R hR)
  have hCxX0 : centralizer ({x} : Set Q) ≤ X0 := le_of_card_eq_480 h2 hC hMC hMX0 hM
  have hxX0 : x ∈ X0 := hCxX0 (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  have hdata : ∀ c ∈ I, centralizer ({c} : Set Q) ≤ X0 ∧
      Nat.card ↥(centralizer ({c} : Set Q)) = 480 := by
    intro c hc
    have hxc : IsConj x c := (hI c hc).2.2.2
    obtain ⟨M', hM'C, hM'p, hM'card, hCc⟩ := conj_centralizer_data hxc hMC hMp hM hC
    have hM'X0 : M' ≤ X0 := hX0max M' hM'p
    have hCcX0 : centralizer ({c} : Set Q) ≤ X0 :=
      le_of_card_eq_480 h2 hCc hM'C hM'X0 hM'card
    exact ⟨hCcX0, hCc⟩
  haveI : Finite ↥X0 := inferInstance
  let x' : ↥X0 := ⟨x, hxX0⟩
  have hx2' : x' ^ 2 = 1 := by
    apply Subtype.ext
    simpa [x'] using hx2
  have hx1' : x' ≠ 1 := by
    intro h
    apply hx1
    have h' := congrArg (fun z : ↥X0 => (z : Q)) h
    simpa [x'] using h'
  have hC' : Nat.card ↥(centralizer ({x'} : Set ↥X0)) = 480 :=
    (card_centralizer_subtype_eq X0 hxX0 hCxX0).trans hC
  have hK0 : IsKGroupCat ↥X0 := hK.subgroup X0
  have hperf : ⁅(⊤ : Subgroup ↥X0), (⊤ : Subgroup ↥X0)⁆ = ⊤ :=
    perfect_top_of_commutator_eq X0 hX0p
  have hodd0 : CFSG.oddCore ↥X0 = ⊥ := oddCore_normal_eq_bot hO X0
  have hcenter0 : Subgroup.center ↥X0 = ⊥ :=
    center_normal_eq_bot hO hmax (X := X0) (F := F) (P := P) hFX0 hPF hP2 hPcard hFz
  have hsyl : ∃ S : Sylow 2 ↥X0, IsA8Type ↥(S : Subgroup ↥X0) :=
    exists_sylow_isA8Type hmax hPX0 hP2 hPcard hPA8
  have hconc := hGH ↥X0 hK0 hperf hodd0 hcenter0 hsyl
  have hMC' : M.subgroupOf X0 ≤ Subgroup.centralizer ({x'} : Set ↥X0) := by
    intro m hm
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    have hmM : (m : Q) ∈ M := Subgroup.mem_subgroupOf.mp hm
    have hcomm := Subgroup.mem_centralizer_singleton_iff.mp (hMC hmM)
    simpa [x'] using hcomm
  have hMp' : ⁅M.subgroupOf X0, M.subgroupOf X0⁆ = M.subgroupOf X0 := by
    rw [commutator_subgroupOf_of_le X0 hMX0 hMX0, hMp]
  have hM' : Nat.card ↥(M.subgroupOf X0) = 60 := by
    rw [card_subgroupOf_of_le X0 hMX0, hM]
  have hIrange : I ⊆ Set.range (Subtype.val : ↥X0 → Q) := by
    intro c hc
    exact ⟨⟨c, (hdata c hc).1 (Subgroup.mem_centralizer_singleton_iff.mpr rfl)⟩, rfl⟩
  have himg : ((Subtype.val : ↥X0 → Q) '' ((Subtype.val : ↥X0 → Q) ⁻¹' I) : Set Q) = I := by
    rw [Set.image_preimage_eq_inter_range]
    exact Set.inter_eq_left.mpr hIrange
  have hIcard' : ((Subtype.val : ↥X0 → Q) ⁻¹' I : Set ↥X0).ncard = 46 := by
    rw [← ncard_image_val X0 ((Subtype.val : ↥X0 → Q) ⁻¹' I), himg, hIcard]
  have hI' : ∀ c' ∈ (Subtype.val ⁻¹' I : Set ↥X0),
      c' ∈ Subgroup.centralizer ({x'} : Set ↥X0) ∧ c' ^ 2 = 1 ∧ c' ≠ 1 ∧
        Nat.card ↥(Subgroup.centralizer ({c'} : Set ↥X0)) = 480 := by
    intro c' hc'
    have hc'I : (c' : Q) ∈ I := hc'
    obtain ⟨hCc', hccard⟩ := hdata (c' : Q) hc'I
    obtain ⟨hc'mem, hc'2, hc'1, -⟩ := hI (c' : Q) hc'I
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      have h := Subgroup.mem_centralizer_singleton_iff.mp hc'mem
      simpa [x'] using h
    · apply Subtype.ext
      simpa using hc'2
    · intro h
      exact hc'1 (by simpa using congrArg Subtype.val h)
    · exact (card_centralizer_subtype_eq X0 c'.2 hCc').trans hccard
  have hJ' : ∀ c' ∈ Subgroup.centralizer ({x'} : Set ↥X0), c' ^ 2 = 1 → c' ≠ 1 →
      IsConj x' c' → c' ∈ (Subtype.val ⁻¹' I : Set ↥X0) := by
    intro c' hc'mem hc'2 hc'1 hconj
    show (c' : Q) ∈ I
    refine hJ (c' : Q) ?_ ?_ ?_ ?_
    · rw [Subgroup.mem_centralizer_singleton_iff] at hc'mem ⊢
      simpa [x'] using congrArg Subtype.val hc'mem
    · simpa using congrArg Subtype.val hc'2
    · intro h
      exact hc'1 (Subtype.ext h)
    · simpa [x'] using X0.subtype.map_isConj hconj
  exact no_X0_of_conclusion (X := ↥X0) hconc hperf hx2' hx1' hC'
    (M := M.subgroupOf X0) hMC' hMp' hM' (I := Subtype.val ⁻¹' I) hIcard' hI' hJ'

end CFSG.EvenSporadicStandard.HNRecog.Harada
