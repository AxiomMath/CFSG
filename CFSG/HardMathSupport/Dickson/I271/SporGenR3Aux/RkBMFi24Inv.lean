module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.RkBMCoverReps
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24ThreeTables
public import Certificates.Certificate17372

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Blueprint CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three CFSG.Perm CFSG.Sporadic.Fi24.Native
  Timmesfeld.Fi24Cl CFSG.HardMathSupport.Dickson.I271.RkBMFi24Inv

section Words

theorem rkBMFi24_wordElt_append (u v : List ℕ) : wordElt (u ++ v) = wordElt u * wordElt v := by
  unfold wordElt
  rw [List.map_append, List.prod_append]

theorem rkBMFi24_wordElt_nil : wordElt ([] : List ℕ) = 1 := by
  unfold wordElt
  rw [List.map_nil, List.prod_nil]

theorem rkBMFi24_base_lt {t : ℕ} (ht : t < 6) : chainBase[t]! < 306936 := by
  interval_cases t <;> decide

theorem rkBMFi24_invWord_lt {r : List ℕ} (hr : ∀ l ∈ r, l < 26) : ∀ l ∈ invWord r, l < 26 := by
  intro l hl
  unfold invWord at hl
  rw [List.mem_reverse, List.mem_map] at hl
  obtain ⟨l₀, hl₀, rfl⟩ := hl
  have := hr l₀ hl₀
  split_ifs <;> omega

theorem rkBMFi24_append_lt {u v : List ℕ} (hu : ∀ l ∈ u, l < 26) (hv : ∀ l ∈ v, l < 26) :
    ∀ l ∈ u ++ v, l < 26 := fun l hl => by
  rcases List.mem_append.1 hl with h | h
  · exact hu l h
  · exact hv l h

theorem rkBMFi24_eq_of_eqOnBase {u v : List ℕ} (hu : ∀ l ∈ u, l < 26) (hv : ∀ l ∈ v, l < 26)
    (h : eqOnBase CFSG.Sporadic.Fi24.letters u v = true) : wordElt u = wordElt v := by
  have hsz : CFSG.Sporadic.Fi24.letters.size = 26 := letters_size_eq
  apply Fi24Sylow.eq_of_base
  intro t ht
  have hb := rkBMFi24_base_lt ht
  rw [Fi24Sylow.idx_wordElt u (fun z hz => hsz ▸ hu z hz) _ hb,
    Fi24Sylow.idx_wordElt v (fun z hz => hsz ▸ hv z hz) _ hb]
  unfold eqOnBase at h
  have hts : t < chainBase.size := by
    have : chainBase.size = 6 := rfl
    omega
  have h1 := (Array.all_eq_true.1 h) t hts
  rw [beq_iff_eq] at h1
  rw [getElem!_pos chainBase t hts]
  exact h1

theorem rkBMFi24_eqOnBase_of_eq {u v : List ℕ} (hu : ∀ l ∈ u, l < 26) (hv : ∀ l ∈ v, l < 26)
    (h : wordElt u = wordElt v) : eqOnBase CFSG.Sporadic.Fi24.letters u v = true := by
  have hsz : CFSG.Sporadic.Fi24.letters.size = 26 := letters_size_eq
  unfold eqOnBase
  rw [Array.all_eq_true]
  intro i hi
  have hi6 : i < 6 := by
    have : chainBase.size = 6 := rfl
    omega
  have hb := rkBMFi24_base_lt hi6
  rw [getElem!_pos chainBase i hi] at hb
  rw [beq_iff_eq, ← Fi24Sylow.idx_wordElt u (fun z hz => hsz ▸ hu z hz) _ hb,
    ← Fi24Sylow.idx_wordElt v (fun z hz => hsz ▸ hv z hz) _ hb, h]

theorem rkBMInvAt_of_invAt {r s t t' : List ℕ} (hr : ∀ l ∈ r, l < 26)
    (h : invAt CFSG.Sporadic.Fi24.letters r s t t' = true) : RkBMInvAt (wordElt r) := by
  unfold invAt at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hlt, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  have hall : ∀ l ∈ s ++ t ++ t', l < 26 := fun l hl =>
    of_decide_eq_true (List.all_eq_true.1 hlt l hl)
  have hs : ∀ l ∈ s, l < 26 := fun l hl =>
    hall l (List.mem_append_left _ (List.mem_append_left _ hl))
  have ht : ∀ l ∈ t, l < 26 := fun l hl =>
    hall l (List.mem_append_left _ (List.mem_append_right _ hl))
  have ht' : ∀ l ∈ t', l < 26 := fun l hl => hall l (List.mem_append_right _ hl)
  have hnil : ∀ l ∈ ([] : List ℕ), l < 26 := fun l hl => absurd hl List.not_mem_nil
  have e1 := rkBMFi24_eq_of_eqOnBase (rkBMFi24_append_lt hs hs) hnil h1
  have e2 := rkBMFi24_eq_of_eqOnBase (rkBMFi24_append_lt (rkBMFi24_append_lt hs hr) hs)
    (rkBMFi24_invWord_lt hr) h2
  have e3 := rkBMFi24_eq_of_eqOnBase (rkBMFi24_append_lt ht ht) hnil h3
  have e4 := rkBMFi24_eq_of_eqOnBase (rkBMFi24_append_lt ht' ht') hnil h4
  have e5 := rkBMFi24_eq_of_eqOnBase (rkBMFi24_append_lt ht hr) (rkBMFi24_append_lt hr ht) h5
  have e6 := rkBMFi24_eq_of_eqOnBase (rkBMFi24_append_lt ht' hr) (rkBMFi24_append_lt hr ht') h6
  have htt' := rkBMFi24_append_lt ht ht'
  have e7 := rkBMFi24_eq_of_eqOnBase (rkBMFi24_append_lt (rkBMFi24_append_lt
    (rkBMFi24_append_lt (rkBMFi24_append_lt htt' ht) ht') ht) ht') hnil h7
  simp only [rkBMFi24_wordElt_append, rkBMFi24_wordElt_nil] at e1 e2 e3 e4 e5 e6 e7
  refine ⟨⟨wordElt s, by rw [sq]; exact e1, by rw [e2, Fi24Sylow.wordElt_invWord]⟩, wordElt t,
    wordElt t', by rw [sq]; exact e3, by rw [sq]; exact e4, e5, e6, ?_, ?_⟩
  · rw [show (wordElt t * wordElt t') ^ 3 =
      wordElt t * wordElt t' * wordElt t * wordElt t' * wordElt t * wordElt t' by
        rw [pow_three]; simp only [mul_assoc]]
    exact e7
  · intro h0
    have := rkBMFi24_eqOnBase_of_eq htt' hnil
      (by rw [rkBMFi24_wordElt_append, h0, rkBMFi24_wordElt_nil])
    rw [this] at h8
    exact Bool.noConfusion h8

end Words

section Reps

theorem rkBMInvAt_fi24Rep3 (i : Fin 5) : RkBMInvAt (fi24Rep3 i) := by
  have h : invCheck CFSG.Sporadic.Fi24.orb = true := Certificates.certificate17372
  unfold invCheck at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩ := h
  fin_cases i
  · exact rkBMInvAt_of_invAt (r := [18]) (by decide) h0
  · exact rkBMInvAt_of_invAt (r := [16, 19]) (by decide) h1
  · exact rkBMInvAt_of_invAt (r := [14, 16, 16, 14, 16, 16]) (by decide) h2
  · exact rkBMInvAt_of_invAt (r := [16]) (by decide) h3
  · exact rkBMInvAt_of_invAt (r := [2]) (by decide) h4

theorem rkBMInv_Fi24prime : RkBMInv NativeSporadic.Fi24prime :=
  rkBMInv_Fi24_of_reps rkBMInvAt_fi24Rep3

theorem rkAut_Fi24Prime_cover_holds (hOut : SporadicOuterLeTwo)
    (hSpM : CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers)
    (hBr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) {T : Type} [Group T]
    [Finite T] (hq : CFSG.Open.IsQuasisimple T)
    (e : T ⧸ Subgroup.center T ≃* (TauCeti.CFSGIndex.sporadic .Fi24Prime).Group) : RkAut 3 T :=
  rkAut_Fi24Prime_cover hOut hSpM hBr rkBMInv_Fi24prime hq e

theorem rkSpor_M_three_of_quasisimple (hOut : SporadicOuterLeTwo)
    (hSpM : CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers)
    (hBr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) {T : Type} [Group T]
    [Finite T] (hq : CFSG.Open.IsQuasisimple T)
    (hS : Nonempty (T ⧸ Subgroup.center T ≃* (TauCeti.CFSGIndex.sporadic .Fi24Prime).Group) ∨
      Nonempty (T ⧸ Subgroup.center T ≃* (TauCeti.CFSGIndex.sporadic .Th).Group)) :
    RkSpor 3 [.Fi24Prime, .Th] T := fun _ => by
  rcases hS with h | h
  · obtain ⟨e⟩ := h
    exact rkAut_Fi24Prime_cover_holds hOut hSpM hBr hq e
  · obtain ⟨e⟩ := h
    exact rkAut_Th_three_of_quasisimple hOut hSpM hBr hq e

theorem rkSpor_M_three_pQuot (hOut : SporadicOuterLeTwo)
    (hSpM : CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers)
    (hBr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) {Q : Type} [Group Q]
    [Finite Q] {X J : Subgroup Q} (hJ : CFSG.Open.GLAPComponent 3 X J)
    (hS : Nonempty (CFSG.Yardstones.Md0ec50421ce4.PSimple 3 J ≃*
        (TauCeti.CFSGIndex.sporadic .Fi24Prime).Group) ∨
      Nonempty (CFSG.Yardstones.Md0ec50421ce4.PSimple 3 J ≃*
        (TauCeti.CFSGIndex.sporadic .Th).Group)) :
    RkSpor 3 [.Fi24Prime, .Th] (CFSG.Yardstones.Md0ec50421ce4.PQuot 3 J) :=
  rkSpor_M_three_of_quasisimple hOut hSpM hBr
    (CFSG.LocalAnalysis.GLTheoremA.isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hJ) hS

end Reps

end CFSG.HardMathSupport.Dickson.I271
