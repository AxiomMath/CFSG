
module


public import CFSG.Certificates.Kernel.SporSch.ThirdDfsBase
import all CFSG.Certificates.Kernel.SporSch.ThirdDfsBase

public import CFSG.Certificates.Kernel.SporSch.ThirdChainH

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Co2Schreier

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.Monster.B.Mathieu CFSG.Sporadic.Co2Cert

section Count

variable (h : ThirdFactsH)
include h

theorem testX_of_comm {g : Equiv.Perm (Fin 2300)} (hc : locU * g = g * locU) : TestX 0 g := by
  intro i _ hi
  exact fix_of_comm' locU g (bpt i) hc (locU_fixH h hi)

theorem mem_stabB_twelve (hu1 : locU ≠ 1) {x : Equiv.Perm (Fin 2300)} (hx : x ∈ stabB 12) :
    x = 1 ∨ x = locU := by
  have hu : locU ∈ stabB 12 := ⟨locU_mem, fun i hi => locU_fixH h hi⟩
  have h12 : Nat.card (stabB 12) = 2 := by
    rw [card_stabBH h (by norm_num : 12 ≤ 13), prod_Ico_succ_self, tsz_eqH h (by norm_num)]
    rfl
  obtain ⟨a, b, hab, hS⟩ := Nat.card_eq_two_iff.1 h12
  have mem : ∀ e : stabB 12, e = a ∨ e = b := fun e => by
    have := hS ▸ Set.mem_univ e
    simpa using this
  have v : ∀ {e e' : stabB 12}, e = e' → (e : Equiv.Perm (Fin 2300)) = e' := fun he => by rw [he]
  rcases mem ⟨1, (stabB 12).one_mem⟩ with e1 | e1 <;> rcases mem ⟨locU, hu⟩ with e2 | e2 <;>
    rcases mem ⟨x, hx⟩ with e3 | e3
  all_goals first
    | exact absurd ((v e2).trans (v e1).symm) hu1
    | exact Or.inl ((v e3).trans (v e1).symm)
    | exact Or.inr ((v e3).trans (v e2).symm)

theorem testX_iff (hu1 : locU ≠ 1) {g : Equiv.Perm (Fin 2300)} (hg : g ∈ co2P) :
    TestX 0 g ↔ locU * g = g * locU := by
  refine ⟨fun ht => ?_, testX_of_comm h⟩
  rcases mem_stabB_twelve h hu1 (conj_mem_twelve hg ht) with e | e
  · exact absurd (one_of_conj e) hu1
  · exact comm_of_conj e

theorem test_iff {pA : Array ℕ} {p : Equiv.Perm (Fin 2300)} (hp : Rep 2300 pA p) {j k : ℕ}
    (hj : j < 13) (hk : k < tsz j) :
    (j < 12 ∧ uArr[pA[(thL[j]!.tr[k]!)[thB[j]!]!]!]! ≠ pA[(thL[j]!.tr[k]!)[thB[j]!]!]!) ↔
      (j < 12 ∧ locU ((p * thT j k) (bpt j)) ≠ (p * thT j k) (bpt j)) := by
  rw [rep_apply_mul h hp hj hk, rep_apply rep_u]
  exact and_congr_right fun _ => not_congr Fin.val_inj

theorem test0_iff {pA : Array ℕ} {p : Equiv.Perm (Fin 2300)} (hp : Rep 2300 pA p) {j : ℕ}
    (hj : j < 13) :
    (j < 12 ∧ uArr[pA[thB[j]!]!]! ≠ pA[thB[j]!]!) ↔
      (j < 12 ∧ locU ((p * thT j 0) (bpt j)) ≠ (p * thT j 0) (bpt j)) := by
  rw [thT_zeroH h hj, mul_one, ← rep_apply_bptH h hp hj, rep_apply rep_u]
  exact and_congr_right fun _ => not_congr Fin.val_inj

theorem card_cosetX : ∀ (f j : ℕ), j + f = 13 → ∀ (p : Equiv.Perm (Fin 2300)) (pA : Array ℕ),
    Rep 2300 pA p → (cosetX j p).card = dfsCnt thL thB uArr 12 f j pA
  | 0, j, hj, p, _, _ => by
    rw [show j = 13 by omega, dfsCnt]
    exact card_cosetX_thirteen h p
  | f + 1, j, hj, p, pA, hp => by
    have hj13 : j < 13 := by omega
    rw [dfsCnt]
    split_ifs with h1 h2 h3
    · have hj12 : j = 12 := by omega
      subst hj12
      exact card_cosetX_twelve h p
    ·
      have h0 : tsz j = 1 := h2
      rw [cover_cosetX h hj13, h0, Finset.range_one, Finset.singleton_biUnion,
        if_pos ((test0_iff h hp hj13).1 h3)]
      rfl
    ·
      have h0 : tsz j = 1 := h2
      rw [cover_cosetX h hj13, h0, Finset.range_one, Finset.singleton_biUnion,
        if_neg (fun ht => h3 ((test0_iff h hp hj13).2 ht)), thT_zeroH h hj13, mul_one]
      exact card_cosetX f (j + 1) (by omega) p pA hp
    ·
      rw [foldl_cond_sum, cover_cosetX h hj13, Finset.card_biUnion (disj_cosetX h hj13 p)]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk' : k < tsz j := Finset.mem_range.1 hk
      by_cases ht : j < 12 ∧ locU ((p * thT j k) (bpt j)) ≠ (p * thT j k) (bpt j)
      · rw [if_pos ht, if_pos ((test_iff h hp hj13 hk').2 ht), Finset.card_empty]
      · rw [if_neg ht, if_neg (fun ht' => ht ((test_iff h hp hj13 hk').1 ht'))]
        exact card_cosetX f (j + 1) (by omega) _ _ (rep_compA hp (rep_thTH h hj13 hk'))

theorem dfsCnt_eq_card (hu1 : locU ≠ 1) :
    dfsCnt thL thB uArr 12 13 0 (idA 2300) = Nat.card locH3 := by
  classical
  rw [← card_cosetX h 13 0 rfl 1 (idA 2300) rep_idA]
  have he : cosetX 0 1 = Finset.univ.filter fun g => g ∈ locH3 := by
    ext g
    rw [mem_cosetX, inv_one, one_mul, stabB_zero, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hg, ht⟩
      exact mem_locH3.2 ⟨hg, (testX_iff h hu1 hg).1 ht⟩
    · intro hg
      have hg' := mem_locH3.1 hg
      exact ⟨hg'.1, (testX_iff h hu1 hg'.1).2 hg'.2⟩
  rw [he, show Nat.card locH3 = Nat.card (Finset.univ.filter fun g => g ∈ locH3) from
    Nat.card_congr (Equiv.subtypeEquivRight fun g => by simp), Nat.card_eq_finsetCard]

end Count

end CFSG.Sporadic.Co2Schreier
