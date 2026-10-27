module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecRootSec
public import CFSG.LocalAnalysis.OddStandard.AltStdSecPermFinal
public import CFSG.LocalAnalysis.OddStandard.AltStdSecPermCent
public import CFSG.LocalAnalysis.OddStandard.AltStdSecFuseOpen

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup CFSG.OddStandard.AltStdBal

section Helpers

variable {G : Type} [Group G] {L : Subgroup G} {n : ℕ} (e : L ≃* alternatingGroup (Fin n))

theorem perm_mem_centralizer_of_mem_centralizer_corr {T : Subgroup (Equiv.Perm (Fin n))}
    (hT : T ≤ alternatingGroup (Fin n)) {c : G} (hcL : c ∈ L)
    (hc : c ∈ centralizer (corr (X := G) e T : Set G)) :
    ((e ⟨c, hcL⟩ : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) ∈
      centralizer (T : Set (Equiv.Perm (Fin n))) := by
  rw [mem_centralizer_iff]
  intro g hg
  set a₀ : L := e.symm ⟨g, hT hg⟩ with ha₀
  have hea₀ : e a₀ = ⟨g, hT hg⟩ := by simp [ha₀]
  have ha₀T : (a₀ : G) ∈ corr (X := G) e T := by
    apply mem_corr_of_mem
    rw [hea₀]
    exact hg
  have hcomm : (a₀ : G) * c = c * a₀ := mem_centralizer_iff.1 hc _ ha₀T
  have h2 : a₀ * ⟨c, hcL⟩ = ⟨c, hcL⟩ * a₀ := Subtype.ext hcomm
  have h3 := congrArg e h2
  rw [map_mul, map_mul, hea₀] at h3
  exact congrArg Subtype.val h3

theorem mem_corr_of_perm_mem {T : Subgroup (Equiv.Perm (Fin n))} {c : G} (hcL : c ∈ L)
    (h : ((e ⟨c, hcL⟩ : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) ∈ T) :
    c ∈ corr (X := G) e T :=
  mem_corr.2 ⟨hcL, h⟩

end Helpers

section Four

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {Q : Subgroup G} {z : G}

theorem z_mem_centralizer_corr (h : Setting G L n) (d : Cyc L Q z)
    (e : L ≃* alternatingGroup (Fin n)) (T : Subgroup (Equiv.Perm (Fin n))) :
    z ∈ centralizer (corr (X := G) e T : Set G) := by
  rw [mem_centralizer_iff]
  intro r hr
  exact mem_centralizer_singleton_iff.1 (le_centralizer_single h d (corr_le e T hr))

theorem rootData_of_card_ge_four (h : Setting G L n) (d : Cyc L Q z) (hQ2 : Nat.card Q = 2)
    (e : L ≃* alternatingGroup (Fin n)) {S : Finset (Fin n)} (hS : 4 ≤ S.card)
    (hSc : 5 ≤ n - S.card) :
    RootData L z (rootGroup e S) (corr (X := G) e (altSub Sᶜ)) (n - S.card) := by
  have hz := z_mem_centralizer_corr h d e (altSub S)
  refine ⟨hz, ?_, ?_⟩
  · exact exactShape_section_root (exactShape_of_setting h d hQ2) e hS hSc hz
  · intro c hcL
    refine mem_sup_left ?_
    have hcR : (c : G) ∈ centralizer (corr (X := G) e (altSub S) : Set G) := c.2
    have h1 := perm_mem_centralizer_of_mem_centralizer_corr e (altSub_le_alternatingGroup S)
      hcL hcR
    have h2 : ((e ⟨c, hcL⟩ : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) ∈
        altSub Sᶜ := by
      rw [← centralizer_altSub_inf_alt hS]
      exact Subgroup.mem_inf.2 ⟨h1, (e ⟨c, hcL⟩).2⟩
    exact mem_corr_of_perm_mem e hcL h2

theorem rootData_of_card_three (h : Setting G L n) (d : Cyc L Q z) (hQ2 : Nat.card Q = 2)
    (e : L ≃* alternatingGroup (Fin n)) {S : Finset (Fin n)} (hS : S.card = 3)
    (hSc : 5 ≤ n - S.card) :
    RootData L z (rootGroup e S) (corr (X := G) e (altSub Sᶜ)) (n - S.card) := by
  have hz := z_mem_centralizer_corr h d e (altSub S)
  refine ⟨hz, ?_, ?_⟩
  · exact exactShape_section_three (exactShape_of_setting h d hQ2) e hS hSc hz
  · intro c hcL
    have hRO : rootGroup (G := G) e S ≤ oddCoreOf (centralizer (rootGroup (G := G) e S : Set G)) :=
      corr_altSub_le_oddCoreOf e hS
    have hcR : (c : G) ∈ centralizer (corr (X := G) e (altSub S) : Set G) := c.2
    have h1 := perm_mem_centralizer_of_mem_centralizer_corr e (altSub_le_alternatingGroup S)
      hcL hcR
    obtain ⟨r, hr, s, hs, hrs⟩ := (mem_centralizer_altSub_card_three_iff hS).1 h1
    have hrA : r ∈ alternatingGroup (Fin n) := altSub_le_alternatingGroup S hr
    have hsgn : Equiv.Perm.sign s = 1 := by
      have h2 := Equiv.Perm.mem_alternatingGroup.1 (e ⟨c, hcL⟩).2
      rw [hrs, map_mul, (mem_altSub.1 hr).1, one_mul] at h2
      exact h2
    have hsA : s ∈ altSub Sᶜ :=
      mem_altSub.2 ⟨hsgn, fun i hi => hs i (by simpa using hi)⟩
    have hsA' : s ∈ alternatingGroup (Fin n) := altSub_le_alternatingGroup _ hsA
    have hcomm : r * s = s * r := comm_altSub_fixSub hr hs
    set cr : L := e.symm ⟨r, hrA⟩ with hcr
    set cs : L := e.symm ⟨s, hsA'⟩ with hcs
    have hecr : e cr = ⟨r, hrA⟩ := by simp [hcr]
    have hecs : e cs = ⟨s, hsA'⟩ := by simp [hcs]
    have hcr_mem : (cr : G) ∈ rootGroup (G := G) e S := mem_corr_of_mem (by rw [hecr]; exact hr)
    have hcs_mem : (cs : G) ∈ corr (X := G) e (altSub Sᶜ) :=
      mem_corr_of_mem (by rw [hecs]; exact hsA)
    have hceq : (⟨c, hcL⟩ : L) = cs * cr := by
      apply e.injective
      rw [map_mul, hecs, hecr]
      apply Subtype.ext
      show ((e ⟨c, hcL⟩ : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) = s * r
      rw [hrs, hcomm]
    have hceqG : (c : G) = cs * cr := congrArg Subtype.val hceq
    obtain ⟨hcrH, hcrO⟩ := mem_oddCoreOf_iff.1 (hRO hcr_mem)
    have hcsH : (cs : G) ∈ centralizer (rootGroup (G := G) e S : Set G) := by
      have : (cs : G) = c * (cr : G)⁻¹ := by rw [hceqG]; group
      rw [this]
      exact mul_mem c.2 (inv_mem hcrH)
    have : c = ⟨cs, hcsH⟩ * ⟨cr, hcrH⟩ := Subtype.ext hceqG
    rw [this]
    exact mul_mem_sup hcs_mem hcrO

end Four

end CFSG.OddStandard.AltStdSec
