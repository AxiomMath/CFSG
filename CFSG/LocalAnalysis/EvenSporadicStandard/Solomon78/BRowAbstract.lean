module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Out1SlimConj
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.CenterAt
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Out1Slim
public import CFSG.Monster.GMS.Facts.BabyTables
public import CFSG.Monster.GMS.Graph

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup CFSG.Monster.GMS CFSG.Blueprint.NativeSporadic

@[expose] def BabyCenterW3 : Prop := ∀ a : B, BabyInv 2 a → CenterInvAt a

@[expose] def BabyCenterW4 : Prop := ∀ a : B, BabyInv 3 a → CenterInvAt a

@[expose] def BabyW3W4Commute : Prop := ∃ x y : B, BabyInv 3 x ∧ BabyInv 2 y ∧ x * y = y * x

@[expose] def BabyW1Commute : Prop :=
  ∀ X : B, orderOf X = 2 → ∃ Y : B, BabyInv 0 Y ∧ Y * X = X * Y

@[expose] def BabySylowCenter : Prop :=
  ∃ (T : Sylow 2 B) (Z : B), BabyInv 1 Z ∧ (∀ p ∈ (T : Subgroup B), p * Z = Z * p) ∧
    ∀ z ∈ (T : Subgroup B), (∀ p ∈ (T : Subgroup B), p * z = z * p) → z = 1 ∨ z = Z

theorem not_dvd_babyCentOrder : ∀ k : Fin 4, k ≠ 0 → ¬ 19 ∣ babyCentOrder k := by
  intro k hk
  fin_cases k
  · exact absurd rfl hk
  · norm_num [babyCentOrder]
  · norm_num [babyCentOrder]
  · norm_num [babyCentOrder]

theorem one_lt_babyOrbitSize : ∀ k : Fin 4, 1 < babyOrbitSize k := by
  intro k
  fin_cases k <;> norm_num [babyOrbitSize]

theorem centerInvAt_babyInv_zero (hT3 : BabyTableIII) (hT4 : BabyTableIV) {a : B}
    (ha : BabyInv 0 a) : CenterInvAt a := by
  intro z hzz hzc
  by_contra hne
  rw [not_or] at hne
  obtain ⟨hz1, hza⟩ := hne
  have hz2 : orderOf z = 2 := orderOf_eq_two_of_mul_self_eq_one hzz hz1
  obtain ⟨k, hk⟩ := hT3.1 z hz2
  have hle : centralizer ({a} : Set B) ≤ centralizer ({z} : Set B) := fun y hy =>
    mem_centralizer_singleton_iff.2 (hzc y (mem_centralizer_singleton_iff.1 hy)).symm
  have hdvd := Subgroup.card_dvd_of_le hle
  rw [ha.2, hk.2] at hdvd
  have hk0 : k = 0 := by
    by_contra hk0
    exact not_dvd_babyCentOrder k hk0
      ((Nat.dvd_trans (by norm_num [babyCentOrder] : 19 ∣ babyCentOrder 0) hdvd))
  subst hk0
  obtain ⟨hcov, hconj, hcard⟩ := hT4 a ha
  obtain ⟨j, hj⟩ := hcov z hk hza
  have hsub : {s | BabyInv 0 s ∧ BabyOrbit j a s} ⊆ {z} := by
    rintro s ⟨hs0, hsj⟩
    obtain ⟨g, hg, hgs⟩ := hconj j z s hk hs0 hj hsj
    have hgz : z * g = g * z := hzc g (mem_centralizer_singleton_iff.1 hg)
    have : g * z * g⁻¹ = z := by rw [← hgz]; group
    exact (hgs.symm.trans this)
  have hle1 : babyOrbitSize j ≤ 1 := by
    rw [← hcard j]
    calc {s | BabyInv 0 s ∧ BabyOrbit j a s}.ncard ≤ ({z} : Set B).ncard :=
          Set.ncard_le_ncard hsub (Set.finite_singleton z)
      _ = 1 := Set.ncard_singleton z
  exact absurd hle1 (not_le.2 (one_lt_babyOrbitSize j))

theorem centerInvAt_of_sylow_center [Finite B] (T : Sylow 2 B) {Z : B}
    (hZc : ∀ p ∈ (T : Subgroup B), p * Z = Z * p)
    (hZ : ∀ z ∈ (T : Subgroup B), (∀ p ∈ (T : Subgroup B), p * z = z * p) → z = 1 ∨ z = Z)
    {a : B} (h : IsConj a Z) : CenterInvAt a :=
  CenterInvAt.of_isConj h fun _ hzz hzc =>
    centerInvolutionsAt_of_sylow T hZc hZ hzz hzc

theorem centerInvAt_babyInv_one [Finite B] (hT3 : BabyTableIII) (hS : BabySylowCenter) {a : B}
    (ha : BabyInv 1 a) : CenterInvAt a := by
  obtain ⟨T, Z, hZ1, hZc, hZ⟩ := hS
  exact centerInvAt_of_sylow_center T hZc hZ (hT3.2 1 a Z ha hZ1)

theorem centerInvolutions_baby [Finite B] (hT3 : BabyTableIII) (hT4 : BabyTableIV)
    (hS : BabySylowCenter) (hW3 : BabyCenterW3) (hW4 : BabyCenterW4) : CenterInvolutions B := by
  intro a z ha hzz _ hzc
  obtain ⟨k, hk⟩ := hT3.1 a ha
  fin_cases k
  · exact centerInvAt_babyInv_zero hT3 hT4 hk z hzz hzc
  · exact centerInvAt_babyInv_one hT3 hS hk z hzz hzc
  · exact hW3 a hk z hzz hzc
  · exact hW4 a hk z hzz hzc

theorem conjCommutes_baby_zero [Finite B] (hT3 : BabyTableIII) (hF1 : BabyW1Commute) {u a : B}
    (hu : BabyInv 0 u) (ha : orderOf a = 2) : ConjCommutes u a := by
  obtain ⟨Y', hY', hc⟩ := hF1 a ha
  exact ConjCommutes.congr_left (hT3.2 0 u Y' hu hY') (ConjCommutes.of_commute hc)

theorem conjCommutes_baby_one [Finite B] (hT3 : BabyTableIII) (hS : BabySylowCenter) {u a : B}
    (hu : BabyInv 1 u) (ha : orderOf a = 2) : ConjCommutes u a := by
  obtain ⟨T, Z, hZ1, hZc, -⟩ := hS
  obtain ⟨h, hh⟩ := exists_conj_commute_of_mem_sylow T hZc
    (mul_self_eq_one_of_orderOf_eq_two' ha)
  exact ConjCommutes.congr_left (hT3.2 1 u Z hu hZ1) ⟨h, hh⟩

theorem involutionsCommute_baby [Finite B] (hT3 : BabyTableIII) (hF1 : BabyW1Commute)
    (hS : BabySylowCenter) (hpair : BabyW3W4Commute) : InvolutionsCommute B := by
  refine involutionsCommute_of_conjCommutes fun u a hu ha => ?_
  obtain ⟨k, hk⟩ := hT3.1 u hu
  obtain ⟨l, hl⟩ := hT3.1 a ha
  have hsame : ∀ m : Fin 4, BabyInv m u → BabyInv m a → ConjCommutes u a := fun m h1 h2 =>
    ConjCommutes.of_isConj (hT3.2 m u a h1 h2)
  obtain ⟨x, y, hx, hy, hxy⟩ := hpair
  have h34 : ∀ u a : B, BabyInv 2 u → BabyInv 3 a → ConjCommutes u a := fun u a h1 h2 =>
    ConjCommutes.congr_right (hT3.2 3 a x h2 hx)
      (ConjCommutes.congr_left (hT3.2 2 u y h1 hy) (ConjCommutes.of_commute hxy.symm))
  fin_cases k <;> fin_cases l
  · exact hsame 0 hk hl
  · exact conjCommutes_baby_zero hT3 hF1 hk ha
  · exact conjCommutes_baby_zero hT3 hF1 hk ha
  · exact conjCommutes_baby_zero hT3 hF1 hk ha
  · exact (conjCommutes_baby_zero hT3 hF1 hl hu).symm
  · exact hsame 1 hk hl
  · exact conjCommutes_baby_one hT3 hS hk ha
  · exact conjCommutes_baby_one hT3 hS hk ha
  · exact (conjCommutes_baby_zero hT3 hF1 hl hu).symm
  · exact (conjCommutes_baby_one hT3 hS hl hu).symm
  · exact hsame 2 hk hl
  · exact h34 u a hk hl
  · exact (conjCommutes_baby_zero hT3 hF1 hl hu).symm
  · exact (conjCommutes_baby_one hT3 hS hl hu).symm
  · exact (h34 a u hl hk).symm
  · exact hsame 3 hk hl

end CFSG.EvenSporadicStandard.Solomon78
