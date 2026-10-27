module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshModelWord

public section

namespace CFSG.EvenSporadicStandard.M12Std.Yosh

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.GH74.M12 CFSG.GH74.M12.Hyp
open CFSG.EvenSporadicStandard.Fin76b
open scoped commutatorElement

section Words

variable {G : Type} [Group G] {e : G}
variable {e₀ : centralizer ({e} : Set G) ≃* Multiplicative (ZMod 2) × G12}

set_option linter.unusedSectionVars false

variable {d : G} {α k : ℕ}

@[expose] noncomputable def uG (E : NEmb e₀ d α k) : G := ψ E (pw α k uWord)

structure L7Fusion (E : NEmb e₀ d α k) : Prop where
  uE : uG E ∈ EG E
  ueE : uG E * e ∈ EG E
  uConj : IsConj e (uG E)
  ueConj : IsConj e (uG E * e)
  euComm : e * uG E = uG E * e
  cover : ∀ y ∈ EG E, IsConj e y → (∃ n ∈ Nn e₀, n * e * n⁻¹ = y) ∨
    (∃ n ∈ Nn e₀, n * uG E * n⁻¹ = y) ∨ (∃ n ∈ Nn e₀, n * (uG E * e) * n⁻¹ = y)
  card56 : Nat.card {y : G // y ∈ EG E ∧ IsConj e y} = 56
  gen : ∀ y ∈ EG E, y ∈ Subgroup.closure {z : G | z ∈ EG E ∧ IsConj e z}

theorem card_E (hue : ueCheck α k = true) : Nat.card (tsub (wgens α k eWords)) = 128 := by
  unfold ueCheck ueCheckG at hue
  simp only [Bool.and_eq_true] at hue
  exact card_tsub hue.1.1

theorem l7Fusion_spec (D : FusionData α k) (E : NEmb e₀ d α k) (he2 : orderOf e = 2)
    (hue : ueCheck α k = true)
    (h : l7Fusion (nEnum α k) (goodTabs α k) (nwT α k eWord) (nwT α k uWord)
      (tenum (wgens α k eWords)).toList = true) : L7Fusion E := by
  obtain ⟨hEs, -⟩ := ueCheck_enum hue
  have hELe : tsub (wgens α k eWords) ≤ NG α k := tsub_wgens_le D hEs.perm
  have hre : Rep 16 (nwT α k eWord) (pw α k eWord) := rep_pw D eWord
  have hru : Rep 16 (nwT α k uWord) (pw α k uWord) := rep_pw D uWord
  have hrue : Rep 16 (compT 16 (nwT α k uWord) (nwT α k eWord))
      (pw α k uWord * pw α k eWord) := hru.compT hre
  have hpe := pw_mem α k eWord
  have hpu := pw_mem α k uWord
  have hpue : pw α k uWord * pw α k eWord ∈ NG α k := (NG α k).mul_mem hpu hpe
  have hψe : ψ E (pw α k eWord) = e := ψ_e E he2
  have hψue : ψ E (pw α k uWord * pw α k eWord) = uG E * e := by
    rw [ψ_mul E hpu hpe, hψe]
    rfl
  have hconj_of_mem : ∀ {T : Table} {g : Equiv.Perm (Fin 16)}, Rep 16 T g → (hg : g ∈ NG α k) →
      memTab 16 (goodTabs α k) T = true → IsConj e (ψ E g) := by
    intro T g hT hg hgood
    rw [ψ_of_mem E hg]
    exact (memTab_good_iff D E he2 hT hg).1 hgood
  unfold l7Fusion at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hcard, hgen⟩, hgu⟩, hgue⟩, hEu⟩, hEue⟩, hcomm⟩, hcov⟩ := h
  refine ⟨(memTab_iff_mem_img E hEs hru hpu).1 hEu, ?_, hconj_of_mem hru hpu hgu, ?_, ?_, ?_, ?_,
    ?_⟩
  · rw [← hψue]
    exact (memTab_iff_mem_img E hEs hrue hpue).1 hEue
  · rw [← hψue]
    exact hconj_of_mem hrue hpue hgue
  · have := (commTT_ψ E hre hru hpe hpu).1 hcomm
    rwa [hψe] at this
  ·
    intro y hy hconj
    obtain ⟨T, hT, rfl, hrepT, hgT⟩ := exists_entry_of_mem_img E hEs hELe hy
    have hgood : memTab 16 (goodTabs α k) T = true := by
      refine (memTab_good_iff D E he2 hrepT hgT).2 ?_
      rw [← ψ_of_mem E hgT]
      exact hconj
    have h1 := hcov T (Array.mem_toList_iff.2 hT)
    rw [hgood] at h1
    simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true] at h1
    rcases h1 with (h1 | h1) | h1
    · left
      obtain ⟨m, hm, hmm⟩ := conjugatesTo_sound D.hsz D.hnC hre hrepT h1
      obtain ⟨n, hn, hnn⟩ := exists_conj_Nn E hpe hgT ⟨m, hm, hmm⟩
      rw [hψe] at hnn
      exact ⟨n, hn, hnn⟩
    · right; left
      obtain ⟨m, hm, hmm⟩ := conjugatesTo_sound D.hsz D.hnC hru hrepT h1
      exact exists_conj_Nn E hpu hgT ⟨m, hm, hmm⟩
    · right; right
      obtain ⟨m, hm, hmm⟩ := conjugatesTo_sound D.hsz D.hnC hrue hrepT h1
      obtain ⟨n, hn, hnn⟩ := exists_conj_Nn E hpue hgT ⟨m, hm, hmm⟩
      rw [hψue] at hnn
      exact ⟨n, hn, hnn⟩
  ·
    have hP : ∀ T ∈ tenum (wgens α k eWords), memTab 16 (goodTabs α k) T = true ↔
        IsConj e (ψ E (tablePerm 16 T)) := by
      intro T hT
      obtain ⟨hrepT, hmem⟩ := hEs.rep_mem hT
      have hgT := hELe hmem
      rw [ψ_of_mem E hgT]
      exact memTab_good_iff D E he2 hrepT hgT
    rw [card_img_filter E hEs hELe (fun y => IsConj e y) (memTab 16 (goodTabs α k)) hP]
    exact hcard
  ·
    have hGs := tsub_spec hgen
    have hcardG : Nat.card (tsub ((tenum (wgens α k eWords)).toList.filter
        (memTab 16 (goodTabs α k))).toArray) = 128 := card_tsub hgen
    have hmemE : ∀ T ∈ ((tenum (wgens α k eWords)).toList.filter
        (memTab 16 (goodTabs α k))).toArray,
        T ∈ tenum (wgens α k eWords) ∧ memTab 16 (goodTabs α k) T = true := by
      intro T hT
      obtain ⟨hT1, hT2⟩ := List.mem_filter.1 (List.mem_toArray.1 hT)
      exact ⟨Array.mem_toList_iff.1 hT1, hT2⟩
    have hle : tsub ((tenum (wgens α k eWords)).toList.filter
        (memTab 16 (goodTabs α k))).toArray ≤ tsub (wgens α k eWords) :=
      tsub_le_of_rep hGs.1.perm fun T hT =>
        ⟨tablePerm 16 T, (hEs.rep_mem (hmemE T hT).1).2, (hEs.rep_mem (hmemE T hT).1).1⟩
    have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [card_E hue, hcardG])
    have hP : (tp 16 '' {x | x ∈ ((tenum (wgens α k eWords)).toList.filter
        (memTab 16 (goodTabs α k))).toArray}) ⊆ NG α k := by
      rintro _ ⟨T, hT, rfl⟩
      obtain ⟨hrepT, hmem⟩ := hEs.rep_mem (hmemE T hT).1
      rw [tp_eq_of_rep (hGs.1.perm T hT) hrepT]
      exact hELe hmem
    intro y hy
    obtain ⟨g, hg, hgK, rfl⟩ := (mem_img' E).1 hy
    rw [← heq] at hgK
    have h1 : ψ E g ∈ img E (Subgroup.closure (tp 16 '' {x | x ∈
        ((tenum (wgens α k eWords)).toList.filter (memTab 16 (goodTabs α k))).toArray})) :=
      ψ_mem_img E hg hgK
    rw [img_closure E hP] at h1
    refine Subgroup.closure_mono ?_ h1
    rintro _ ⟨_, ⟨T, hT, rfl⟩, rfl⟩
    obtain ⟨hTE, hTgood⟩ := hmemE T hT
    obtain ⟨hrepT, hmem⟩ := hEs.rep_mem hTE
    have hgT := hELe hmem
    rw [tp_eq_of_rep (hGs.1.perm T hT) hrepT]
    exact ⟨ψ_mem_img_enum E hEs hELe hTE, hconj_of_mem hrepT hgT hTgood⟩

end Words

end CFSG.EvenSporadicStandard.M12Std.Yosh
