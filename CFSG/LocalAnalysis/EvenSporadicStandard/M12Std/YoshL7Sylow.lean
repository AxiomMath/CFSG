module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshL7Fusion

public section

namespace CFSG.EvenSporadicStandard.M12Std.Yosh

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.GH74.M12 CFSG.GH74.M12.Hyp
open CFSG.EvenSporadicStandard.Fin76b
open scoped commutatorElement

section Sylow

variable {G : Type} [Group G] {e : G}
variable {e₀ : centralizer ({e} : Set G) ≃* Multiplicative (ZMod 2) × G12}


set_option linter.unusedSectionVars false

variable {d : G} {α k : ℕ}

structure L7Sylow (E : NEmb e₀ d α k) : Prop where
  cardT : Nat.card (SG E ⊓ centralizer ({e} : Set G) : Subgroup G) = 128
  cardR : Nat.card (EG E ⊓ centralizer ({e} : Set G) : Subgroup G) = 64
  ZT : ∀ y ∈ SG E ⊓ centralizer ({e} : Set G),
    (∀ z ∈ SG E ⊓ centralizer ({e} : Set G), y * z = z * y) →
      y = 1 ∨ y = e ∨ y = cG e₀ ∨ y = e * cG e₀
  ZR : ∀ y ∈ EG E ⊓ centralizer ({e} : Set G),
    (∀ z ∈ EG E ⊓ centralizer ({e} : Set G), y * z = z * y) →
      y = 1 ∨ y = e ∨ y = cG e₀ ∨ y = e * cG e₀
  Runiq : ∀ y ∈ SG E ⊓ centralizer ({e} : Set G), y ∉ EG E ⊓ centralizer ({e} : Set G) →
    (y * y = 1 ∨ y * y = cG e₀) →
      2 * Nat.card {x : G // x ∈ EG E ⊓ centralizer ({e} : Set G) ∧
        (⁅x, y⁆ = 1 ∨ ⁅x, y⁆ = cG e₀)} < 64
  cardSu : Nat.card (SG E ⊓ centralizer ({uG E} : Set G) : Subgroup G) = 128
  cardEu : Nat.card (EG E ⊓ centralizer ({uG E} : Set G) : Subgroup G) = 64
  cardSue : Nat.card (SG E ⊓ centralizer ({uG E * e} : Set G) : Subgroup G) = 128
  cardEue : Nat.card (EG E ⊓ centralizer ({uG E * e} : Set G) : Subgroup G) = 64

theorem l7Sylow_spec (D : FusionData α k) (E : NEmb e₀ d α k) (he2 : orderOf e = 2)
    (hue : ueCheck α k = true)
    (h : l7Sylow (nwT α k cWord) (nwT α k eWord) (nwT α k uWord)
      (tenum (wgens α k eWords)).toList (tenum (wgens α k sWords)).toList = true) :
    L7Sylow E := by
  obtain ⟨hEs, hSs⟩ := ueCheck_enum hue
  have hELe : tsub (wgens α k eWords) ≤ NG α k := tsub_wgens_le D hEs.perm
  have hSLe : tsub (wgens α k sWords) ≤ NG α k := tsub_wgens_le D hSs.perm
  have hre : Rep 16 (nwT α k eWord) (pw α k eWord) := rep_pw D eWord
  have hru : Rep 16 (nwT α k uWord) (pw α k uWord) := rep_pw D uWord
  have hrc : Rep 16 (nwT α k cWord) (pw α k cWord) := rep_pw D cWord
  have hrue : Rep 16 (compT 16 (nwT α k uWord) (nwT α k eWord))
      (pw α k uWord * pw α k eWord) := hru.compT hre
  have hrec : Rep 16 (compT 16 (nwT α k eWord) (nwT α k cWord))
      (pw α k eWord * pw α k cWord) := hre.compT hrc
  have hpe := pw_mem α k eWord
  have hpu := pw_mem α k uWord
  have hpc := pw_mem α k cWord
  have hpue : pw α k uWord * pw α k eWord ∈ NG α k := (NG α k).mul_mem hpu hpe
  have hpec : pw α k eWord * pw α k cWord ∈ NG α k := (NG α k).mul_mem hpe hpc
  have hψe : ψ E (pw α k eWord) = e := ψ_e E he2
  have hψc : ψ E (pw α k cWord) = cG e₀ := ψ_c E
  have hψue : ψ E (pw α k uWord * pw α k eWord) = uG E * e := by
    rw [ψ_mul E hpu hpe, hψe]
    rfl
  have hψec : ψ E (pw α k eWord * pw α k cWord) = e * cG e₀ := by
    rw [ψ_mul E hpe hpc, hψe, hψc]
  have hcases : ∀ {T' : Table}, Rep 16 T' (tablePerm 16 T') → tablePerm 16 T' ∈ NG α k →
      (((tblEq 16 T' (idT 16) = true ∨ tblEq 16 T' (nwT α k eWord) = true) ∨
        tblEq 16 T' (nwT α k cWord) = true) ∨
        tblEq 16 T' (compT 16 (nwT α k eWord) (nwT α k cWord)) = true) →
      ψ E (tablePerm 16 T') = 1 ∨ ψ E (tablePerm 16 T') = e ∨ ψ E (tablePerm 16 T') = cG e₀ ∨
        ψ E (tablePerm 16 T') = e * cG e₀ := by
    intro T' hrep hg hor
    rcases hor with ((h1 | h1) | h1) | h1
    · exact Or.inl ((tblEq_idT_ψ E hrep hg).1 h1)
    · exact Or.inr (Or.inl (((tblEq_ψ E hrep hre hg hpe).1 h1).trans hψe))
    · exact Or.inr (Or.inr (Or.inl (((tblEq_ψ E hrep hrc hg hpc).1 h1).trans hψc)))
    · exact Or.inr (Or.inr (Or.inr (((tblEq_ψ E hrep hrec hg hpec).1 h1).trans hψec)))
  unfold l7Sylow at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.all_cons, List.all_nil] at h
  obtain ⟨⟨⟨⟨⟨hLT, hLR⟩, hZT⟩, hZR⟩, hRu⟩, hx⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    have := card_img_inf_centralizer E hSs hSLe hre hpe
    rw [hψe] at this
    exact this.trans hLT
  ·
    have := card_img_inf_centralizer E hEs hELe hre hpe
    rw [hψe] at this
    exact this.trans hLR
  ·
    have key := forall_mem_img_inf_centralizer E hSs hre hpe
      (φ := fun y => (∀ z ∈ SG E ⊓ centralizer ({e} : Set G), y * z = z * y) →
        y = 1 ∨ y = e ∨ y = cG e₀ ∨ y = e * cG e₀) ?_
    · rw [hψe] at key
      exact key
    · intro T' hT' hcen
      obtain ⟨hT1, -⟩ := List.mem_filter.1 hT'
      obtain ⟨hrep', hmem'⟩ := hSs.rep_mem (Array.mem_toList_iff.1 hT1)
      have hg' := hSLe hmem'
      have hb := hZT T' hT'
      have hall : ((tenum (wgens α k sWords)).toList.filter
          (commTT 16 (nwT α k eWord))).all (commTT 16 T') = true := by
        rw [List.all_eq_true]
        intro T'' hT''
        have hz := mem_img_inf_centralizer_of_filter E hSs hSLe hre hpe hT''
        rw [hψe] at hz
        obtain ⟨-, hmem''⟩ := hSs.rep_mem (Array.mem_toList_iff.1 (List.mem_filter.1 hT'').1)
        obtain ⟨hrep'', -⟩ := hSs.rep_mem (Array.mem_toList_iff.1 (List.mem_filter.1 hT'').1)
        exact (commTT_ψ E hrep' hrep'' hg' (hSLe hmem'')).2 (hcen _ hz)
      rw [hall] at hb
      simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true] at hb
      exact hcases hrep' hg' hb
  ·
    have key := forall_mem_img_inf_centralizer E hEs hre hpe
      (φ := fun y => (∀ z ∈ EG E ⊓ centralizer ({e} : Set G), y * z = z * y) →
        y = 1 ∨ y = e ∨ y = cG e₀ ∨ y = e * cG e₀) ?_
    · rw [hψe] at key
      exact key
    · intro T' hT' hcen
      obtain ⟨hT1, -⟩ := List.mem_filter.1 hT'
      obtain ⟨hrep', hmem'⟩ := hEs.rep_mem (Array.mem_toList_iff.1 hT1)
      have hg' := hELe hmem'
      have hb := hZR T' hT'
      have hall : ((tenum (wgens α k eWords)).toList.filter
          (commTT 16 (nwT α k eWord))).all (commTT 16 T') = true := by
        rw [List.all_eq_true]
        intro T'' hT''
        have hz := mem_img_inf_centralizer_of_filter E hEs hELe hre hpe hT''
        rw [hψe] at hz
        obtain ⟨hrep'', hmem''⟩ := hEs.rep_mem (Array.mem_toList_iff.1 (List.mem_filter.1 hT'').1)
        exact (commTT_ψ E hrep' hrep'' hg' (hELe hmem'')).2 (hcen _ hz)
      rw [hall] at hb
      simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true] at hb
      exact hcases hrep' hg' hb
  ·
    have key := forall_mem_img_inf_centralizer E hSs hre hpe
      (φ := fun y => y ∉ EG E ⊓ centralizer ({e} : Set G) → (y * y = 1 ∨ y * y = cG e₀) →
        2 * Nat.card {x : G // x ∈ EG E ⊓ centralizer ({e} : Set G) ∧
          (⁅x, y⁆ = 1 ∨ ⁅x, y⁆ = cG e₀)} < 64) ?_
    · rw [hψe] at key
      exact key
    · intro T' hT' hyR hsq
      obtain ⟨hT1, -⟩ := List.mem_filter.1 hT'
      obtain ⟨hrep', hmem'⟩ := hSs.rep_mem (Array.mem_toList_iff.1 hT1)
      have hg' := hSLe hmem'
      have hb := hRu T' hT'
      have hy := mem_img_inf_centralizer_of_filter E hSs hSLe hre hpe hT'
      rw [hψe] at hy
      have hnmem : memTab 16 (tenum (wgens α k eWords)).toList T' = false := by
        rw [Bool.eq_false_iff]
        intro hm
        apply hyR
        refine Subgroup.mem_inf.2 ⟨?_, (Subgroup.mem_inf.1 hy).2⟩
        exact (memTab_iff_mem_img E hEs hrep' hg').1 hm
      have hsqT : sqIn 16 (nwT α k cWord) T' = true := by
        refine (sqIn_ψ E hrc hrep' hpc hg').2 ?_
        rw [hψc]
        exact hsq
      rw [hnmem, hsqT] at hb
      simp only [Bool.false_or, Bool.not_true, decide_eq_true_eq] at hb
      have hcard := card_img_filter E hEs hELe
        (fun x => e * x = x * e ∧ (⁅x, ψ E (tablePerm 16 T')⁆ = 1 ∨
          ⁅x, ψ E (tablePerm 16 T')⁆ = cG e₀))
        (fun T => commTT 16 (nwT α k eWord) T && commIn 16 (nwT α k cWord) T T') ?_
      · have : Nat.card {x : G // x ∈ EG E ⊓ centralizer ({e} : Set G) ∧
            (⁅x, ψ E (tablePerm 16 T')⁆ = 1 ∨ ⁅x, ψ E (tablePerm 16 T')⁆ = cG e₀)} =
            Nat.card {y : G // y ∈ img E (tsub (wgens α k eWords)) ∧
              (e * y = y * e ∧ (⁅y, ψ E (tablePerm 16 T')⁆ = 1 ∨
                ⁅y, ψ E (tablePerm 16 T')⁆ = cG e₀))} := by
          refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
          rw [Subgroup.mem_inf, mem_centralizer_singleton_iff, and_assoc]
          constructor
          · rintro ⟨h1, h2, h3⟩
            exact ⟨h1, h2.symm, h3⟩
          · rintro ⟨h1, h2, h3⟩
            exact ⟨h1, h2.symm, h3⟩
        rw [this, hcard]
        exact hb
      · intro T hT
        obtain ⟨hrepT, hmemT⟩ := hEs.rep_mem hT
        have hgT := hELe hmemT
        rw [Bool.and_eq_true]
        have h1 := commTT_ψ E hre hrepT hpe hgT
        have h2 := commIn_ψ E hrc hrepT hrep' hpc hgT hg'
        rw [hψe] at h1
        rw [hψc] at h2
        exact and_congr h1 h2
  ·
    have := card_img_inf_centralizer E hSs hSLe hru hpu
    exact this.trans (hx.1.1)
  ·
    have := card_img_inf_centralizer E hEs hELe hru hpu
    exact this.trans (hx.1.2)
  ·
    have := card_img_inf_centralizer E hSs hSLe hrue hpue
    rw [hψue] at this
    exact this.trans (hx.2.1.1)
  ·
    have := card_img_inf_centralizer E hEs hELe hrue hpue
    rw [hψue] at this
    exact this.trans (hx.2.1.2)

end Sylow

end CFSG.EvenSporadicStandard.M12Std.Yosh
