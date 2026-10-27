module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Fi22Center

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier CFSG.Sporadic.FischerOddCore
open CFSG.ComponentClassification.M12Cover CFSG.Monster.B.Fischer
open CFSG.EvenSporadicStandard.HypOne.Fi22

theorem card_centralizerIn_fi22_inner
    {a : Equiv.Perm (Fin 3510)} (ha : a ∈ fi22P) (ha2 : orderOf a = 2) :
    Nat.card ↥(centralizerIn fi22P a) = 1769472 ∨ Nat.card ↥(centralizerIn fi22P a) = 53084160 ∨
      Nat.card ↥(centralizerIn fi22P a) = 18393661440 := by
  obtain ⟨r, hr, c, hc, rfl⟩ := cover_P a ha ha2
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hr
  rw [← Nat.card_congr (centralizerInConjEquiv fi22P hc (fi22ExtRep k)).toEquiv]
  have hk3 := List.mem_range.1 hk
  have := card_centralizerIn_P hk3
  interval_cases k <;> simp_all

theorem card_centralizerIn_fi22_outer
    {w : Equiv.Perm (Fin 3510)} (hw : w ∈ fi22R) (hwP : w ∉ fi22P) (hw2 : orderOf w = 2) :
    Nat.card ↥(centralizerIn fi22P w) = 3317760 ∨ Nat.card ↥(centralizerIn fi22P w) = 1045094400 ∨
      Nat.card ↥(centralizerIn fi22P w) = 2903040 := by
  obtain ⟨k, hk3, hk6, g, hg, rfl⟩ := cover_outer hw hw2 hwP
  rw [← Nat.card_congr (centralizerInConjEquiv fi22P hg (fi22ExtRep k)).toEquiv]
  obtain ⟨j, rfl⟩ : ∃ j, k = 3 + j := ⟨k - 3, by omega⟩
  have hj : j < 3 := by omega
  have := card_centralizerIn_P_outer (k := j) hj
  interval_cases j <;> simp_all

theorem fi22_autRowData
    : AutRowData fi22P fi22R where
  model := fi22_autModel
  index := fi22_index_two
  centerInv := centerInv_fi22
  outerLe := by
    intro a ha ha2 w hw hwP hww hall
    have hw1 : w ≠ 1 := fun e => hwP (e ▸ fi22P.one_mem)
    have hw2 : orderOf w = 2 := orderOf_eq_prime (by rw [pow_two]; exact hww) hw1
    have hle : centralizerIn fi22P a ≤ centralizerIn fi22P w := fun y hy => by
      have hy' := mem_centralizerIn.1 hy
      exact mem_centralizerIn.2 ⟨hy'.1, hall y hy'.1 hy'.2⟩
    have hdvd := Subgroup.card_dvd_of_le hle
    rcases card_centralizerIn_fi22_inner ha ha2 with h1 | h1 | h1 <;>
      rcases card_centralizerIn_fi22_outer hw hwP hw2 with h2 | h2 | h2 <;> rw [h1, h2] at hdvd <;>
      norm_num at hdvd

theorem fi22_autCenterCondExc_native :
    AutCenterCondExc ↥fi22P (fun α => Nat.card (fixSubgroup α) = 2903040) :=
  fi22_autRowData.autCenterCondExc fun α w hw hwP hα hww z hz hz2 hzw hall =>
    fi22_outerCentre α w hw hwP hα hww z hz hz2 hzw hall

theorem fi22_card_fixSubgroup_conj_ne
    (a : ↥fi22P) (ha : a * a = 1) :
    Nat.card (fixSubgroup (MulAut.conj a)) ≠ 2903040 := by
  have hfix : fixSubgroup (MulAut.conj a) = centralizer ({a} : Set ↥fi22P) := by
    ext z
    rw [mem_centralizer_singleton_iff]
    show a * z * a⁻¹ = z ↔ z * a = a * z
    constructor
    · intro h
      calc z * a = (a * z * a⁻¹) * a := by rw [h]
        _ = a * z := by group
    · intro h
      rw [← h]
      group
  rw [hfix, Nat.card_congr (centralizerSubgroupEquiv fi22P a).toEquiv]
  by_cases h1 : a = 1
  · subst h1
    have : centralizerIn fi22P ((1 : ↥fi22P) : Equiv.Perm (Fin 3510)) = fi22P := by
      ext x
      simp [centralizerIn, Subgroup.mem_centralizer_iff]
    rw [this, card_fi22P]
    norm_num
  · have hne : (a : Equiv.Perm (Fin 3510)) ≠ 1 := fun e => h1 (Subtype.ext e)
    have hsq : (a : Equiv.Perm (Fin 3510)) * a = 1 := congrArg Subtype.val ha
    have hord : orderOf (a : Equiv.Perm (Fin 3510)) = 2 :=
      orderOf_eq_prime (by rw [pow_two]; exact hsq) hne
    rcases card_centralizerIn_fi22_inner a.2 hord with h | h | h <;> rw [h] <;> norm_num

end CFSG.EvenSporadicStandard.Solomon78
