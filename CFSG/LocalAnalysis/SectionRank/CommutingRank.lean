module

public import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.GroupTheory.PLayer.Transfer
import CFSG.GroupTheory.PRankCommutingSup

public section

namespace CFSG.SectionRank

open CFSG.Open

private theorem pRank_option_iSup_eq_add {X : Type} [Group X] [Finite X] {q : ℕ}
    (hq : q.Prime) {ι : Type} [Fintype ι] (L₀ : Subgroup X) (L : ι → Subgroup X)
    (E : Subgroup X) (hEL : E ≤ L₀) (t : ι → X)
    (h₀ : ∀ i, L i ≤ Subgroup.centralizer (L₀ : Set X))
    (hL : ∀ i j, i ≠ j → L i ≤ Subgroup.centralizer (L j : Set X))
    (htL : ∀ i, t i ∈ L i) (hto : ∀ i, orderOf (t i) = q)
    (htZ : ∀ i, t i ∉ Subgroup.centralizer (L i : Set X)) :
    CFSG.Open.pRank q (⨆ o ∈ (Finset.univ : Finset (Option ι)),
        Option.elim o E (fun i => Subgroup.zpowers (t i))) =
      CFSG.Open.pRank q E +
        ∑ i : ι, CFSG.Open.pRank q (Subgroup.zpowers (t i)) := by
  classical
  have htiq : ∀ i, t i ^ q = 1 := fun i => by
    rw [← hto i]
    exact pow_orderOf_eq_one (t i)
  have htne : ∀ i, t i ≠ 1 := by
    intro i hi
    apply hq.ne_one
    rw [← hto i, hi, orderOf_one]
  let B : ι → Subgroup X := fun i => Subgroup.zpowers (t i)
  let A : Option ι → Subgroup X := fun o => Option.elim o E B
  let J : Option ι → Subgroup X := fun o => Option.elim o L₀ L
  have hAJ : ∀ o ∈ (Finset.univ : Finset (Option ι)), A o ≤ J o := by
    intro o _
    cases o with
    | none => exact hEL
    | some i => exact Subgroup.zpowers_le.mpr (htL i)
  have hcomm : ∀ o ∈ (Finset.univ : Finset (Option ι)),
      ∀ o' ∈ (Finset.univ : Finset (Option ι)), o ≠ o' →
        J o ≤ Subgroup.centralizer (J o' : Set X) := by
    intro o _ o' _ hne
    cases o with
    | none =>
        cases o' with
        | none => exact absurd rfl hne
        | some j => exact Subgroup.le_centralizer_iff.mp (h₀ j)
    | some i =>
        cases o' with
        | none => exact h₀ i
        | some j => exact hL i j (fun h => hne (by rw [h]))
  have hZ : ∀ o ∈ (Finset.univ : Finset (Option ι)), o ≠ none →
      A o ⊓ Subgroup.centralizer (J o : Set X) = ⊥ := by
    intro o _ ho
    cases o with
    | none => exact absurd rfl ho
    | some i =>
        exact CFSG.zpowers_inf_eq_bot_of_not_mem hq (htiq i) (htne i) (htZ i)
  have hsum := CFSG.GroupTheory.pRank_iSup_eq_sum_of_inf_centralizer_eq_bot
    (Y := X) (p := q) hq (Finset.univ : Finset (Option ι)) J A none hAJ hcomm hZ
  rw [Fintype.sum_option] at hsum
  simpa [A, B] using hsum

theorem pRank_add_card_le_of_commuting {X : Type} [Group X] [Finite X] {q : ℕ} (hq : q.Prime)
    {ι : Type} [Finite ι] (L₀ : Subgroup X) (L : ι → Subgroup X)
    (h₀ : ∀ i, L i ≤ Subgroup.centralizer (L₀ : Set X))
    (hL : ∀ i j, i ≠ j → L i ≤ Subgroup.centralizer (L j : Set X))
    (E : Subgroup X) (hE : CFSG.Open.IsElemAbelian q E) (hEL : E ≤ L₀) {k : ℕ}
    (hk : Nat.card E = q ^ k) (t : ι → X) (htL : ∀ i, t i ∈ L i)
    (hto : ∀ i, orderOf (t i) = q)
    (htZ : ∀ i, t i ∉ Subgroup.centralizer (L i : Set X)) :
    k + Nat.card ι ≤ CFSG.Open.pRank q (⊤ : Subgroup X) := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  have hsum := pRank_option_iSup_eq_add (X := X) (q := q) hq L₀ L E hEL t h₀ hL htL hto htZ
  have htiq : ∀ i, t i ^ q = 1 := fun i => by
    rw [← hto i]
    exact pow_orderOf_eq_one (t i)
  have hErank : k ≤ CFSG.Open.pRank q E :=
    CFSG.SectionRank.le_pRank hq.one_lt le_rfl hE hk
  have hBrank : ∀ i, 1 ≤ CFSG.Open.pRank q (Subgroup.zpowers (t i)) := by
    intro i
    have hcard : Nat.card ↥(Subgroup.zpowers (t i)) = q ^ 1 := by
      rw [Nat.card_zpowers, hto i, pow_one]
    exact CFSG.SectionRank.le_pRank hq.one_lt le_rfl
      (CFSG.Open.isElemAbelian_zpowers (htiq i)) hcard
  have hBsum : Nat.card ι ≤ ∑ i : ι, CFSG.Open.pRank q (Subgroup.zpowers (t i)) := by
    calc Nat.card ι = Fintype.card ι := Nat.card_eq_fintype_card
      _ = ∑ _i : ι, (1 : ℕ) := by simp
      _ ≤ ∑ i : ι, CFSG.Open.pRank q (Subgroup.zpowers (t i)) :=
          Finset.sum_le_sum fun i _ => hBrank i
  have hjoin : k + Nat.card ι ≤ CFSG.Open.pRank q
      (⨆ o ∈ (Finset.univ : Finset (Option ι)),
        Option.elim o E (fun i => Subgroup.zpowers (t i))) := by
    rw [hsum]
    exact Nat.add_le_add hErank hBsum
  exact hjoin.trans (CFSG.SectionRank.pRank_mono hq.one_lt le_top)

end CFSG.SectionRank
