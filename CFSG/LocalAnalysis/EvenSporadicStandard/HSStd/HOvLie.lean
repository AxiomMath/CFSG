module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.HOvCent
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.HOvOut
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87P47Rank3
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryModelOuterTwoPart
public import CFSG.Quasithin.Vol2.KGFactInspE16Base
public import CFSG.RankThree.Classical.SteinbergBJUnitaryThreeInvolutions
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.EvenSporadicStandard.HSStd.HOv

open Equiv Equiv.Perm Subgroup CFSG.ComponentClassification.OuterAutomorphisms

theorem statedClassicalModel_of_lieModel {G : Type} [Group G]
    {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n p f : ℕ} (hn : n ≠ 0)
    (h : CFSG.Blueprint.LieModel G t n p f) :
    CFSG.Assembly.LowTwoRank.StatedClassicalModel G t n p f :=
  CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero hn h

theorem not_exists_elemAbelian_sixteen_of_normal {D : Type*} [Group D] [Finite D]
    (hZ : ∀ N : Subgroup D, N.Normal → Odd (Nat.card N) → N = ⊥) {t : D} (ht : orderOf t = 2)
    (e : Nonempty (↥(centralizer ({t} : Set D)) ≃* Multiplicative (ZMod 2) × Perm (Fin 5)))
    (S : Subgroup D) [S.Normal] (h4 : 4 ∣ Nat.card S) (h240 : 240 < Nat.card S)
    (hS : ∀ E : Subgroup ↥S, CFSG.Open.IsElemAbelian 2 E → Nat.card E ≤ 4) (m : ℕ)
    (hm : Nat.card (Outer ↥S) ∣ m) (hm2 : ∀ k : ℕ, 2 ^ k ∣ m → 2 ^ k ≤ 2) :
    ¬ ∃ A : Subgroup D, CFSG.Open.IsElemAbelian 2 A ∧ Nat.card ↥A = 16 := by
  rintro ⟨A, hA, hcard⟩
  have hC := centralizer_eq_bot_of_normal_of_card hZ ht e S h4 h240
  have hA2 : ∀ a ∈ A, a * a = 1 := fun a ha => by simpa [pow_two] using hA.2 a ha
  obtain ⟨r, hr, hrdvd, k, hk⟩ := exists_card_eq_mul_outer S hC hA2
  have hr2 : r ≤ 2 := by rw [hk]; exact hm2 k (hk ▸ hrdvd.trans hm)
  have hAS : Nat.card ↥(A ⊓ S) ≤ 4 := by
    have h1 := hS _ (isElemAbelian_subgroupOf_inf S hA)
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : A ⊓ S ≤ S)).toEquiv] at h1
  have : 16 ≤ 4 * 2 := by rw [← hcard, hr]; exact Nat.mul_le_mul hAS hr2
  omega

theorem not_exists_elemAbelian_sixteen_of_psl_three_five {D : Type} [Group D] [Finite D]
    (hZ : ∀ N : Subgroup D, N.Normal → Odd (Nat.card N) → N = ⊥) {t : D} (ht : orderOf t = 2)
    (e : Nonempty (↥(centralizer ({t} : Set D)) ≃* Multiplicative (ZMod 2) × Perm (Fin 5)))
    (hL : CFSG.Blueprint.LieModel ↥(commutator D) .PSL 3 5 1) :
    ¬ ∃ A : Subgroup D, CFSG.Open.IsElemAbelian 2 A ∧ Nat.card ↥A = 16 := by
  have hM := statedClassicalModel_of_lieModel (by norm_num) hL
  obtain ⟨hcard, -, -, -, hout⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.linear_model_outer_two_part_bound ↥(commutator D) 3 5 1 hM
  have hcard' : Nat.card ↥(commutator D) = 372000 := by rw [hcard]; decide
  refine not_exists_elemAbelian_sixteen_of_normal hZ ht e (commutator D)
    (by rw [hcard']; norm_num) (by rw [hcard']; norm_num)
    (fun E hE => CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_elemAbelian_two_le_four_of_PSL3
      (by norm_num) (by norm_num) hL E hE) 2 ?_ (fun k hk => Nat.le_of_dvd (by norm_num) hk)
  have h := hout le_rfl
  have h2 : 2 * 1 * Nat.gcd 3 (5 ^ 1 - 1) = 2 := by decide
  rwa [h2] at h

theorem exists_normal_commutator_commutator (D : Type*) [Group D] :
    ∃ H : Subgroup D, H.Normal ∧ Nonempty (↥(commutator ↥(commutator D)) ≃* ↥H) := by
  have hHeq : (commutator ↥(commutator D)).map (commutator D).subtype =
      ⁅commutator D, commutator D⁆ := by
    rw [show commutator ↥(commutator D) = ⁅(⊤ : Subgroup ↥(commutator D)), ⊤⁆ from rfl,
      map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  refine ⟨(commutator ↥(commutator D)).map (commutator D).subtype, ?_,
    ⟨Subgroup.equivMapOfInjective _ _ Subtype.val_injective⟩⟩
  rw [hHeq]
  infer_instance

theorem not_exists_elemAbelian_sixteen_of_psu_three_five {D : Type} [Group D] [Finite D]
    (hZ : ∀ N : Subgroup D, N.Normal → Odd (Nat.card N) → N = ⊥) {t : D} (ht : orderOf t = 2)
    (e : Nonempty (↥(centralizer ({t} : Set D)) ≃* Multiplicative (ZMod 2) × Perm (Fin 5)))
    (hL : CFSG.Blueprint.LieModel ↥(commutator ↥(commutator D)) .PSU 3 5 1) :
    ¬ ∃ A : Subgroup D, CFSG.Open.IsElemAbelian 2 A ∧ Nat.card ↥A = 16 := by
  obtain ⟨H, hHn, ⟨eH⟩⟩ := exists_normal_commutator_commutator D
  have hLH : CFSG.Blueprint.LieModel ↥H .PSU 3 5 1 :=
    CFSG.LieType.CurtisTits.lieModel_of_mulEquiv eH hL
  have hM := statedClassicalModel_of_lieModel (by norm_num) hLH
  have hcard := (CFSG.RankThree.Classical.unitary_three_five_model ↥H hM).1
  have hout := (CFSG.LocalAnalysis.ComponentInitial.unitary_model_outer_two_part_bound ↥H 3 5 1
    hM).2.2.1
  have h6 : 2 * 1 * Nat.gcd 3 (5 ^ 1 + 1) = 6 := by decide
  rw [h6] at hout
  refine not_exists_elemAbelian_sixteen_of_normal hZ ht e H
    (by rw [hcard]; norm_num) (by rw [hcard]; norm_num) ?_ 6 (by rw [hout]) ?_
  · intro E hE
    obtain ⟨k, hk, hkr⟩ := CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_le_of_pRank hE
    have := CFSG.Quasithin.H13.KGInsp4316.pRank_two_le_two_of_psu3_odd (by norm_num)
      (by norm_num) hM
    rw [hk]
    exact Nat.pow_le_pow_right (by norm_num) (hkr.trans this) |>.trans (by norm_num)
  · intro k hk
    have h1 : 2 ^ k ≤ 6 := Nat.le_of_dvd (by norm_num) hk
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · interval_cases k <;> norm_num
    · have h2 : 2 ^ 2 ∣ 2 ^ k := pow_dvd_pow 2 hk2
      have h3 := dvd_trans h2 hk
      norm_num at h3

end CFSG.EvenSporadicStandard.HSStd.HOv
