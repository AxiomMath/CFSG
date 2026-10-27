module

public import Certificates.Data.Y63.Spec
public import Mathlib.Data.Finset.Card

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Y63Chk

theorem y63_crit_eq {n : ℕ} {d : List ℕ} (hd : d.Nodup) {bad : ℕ → ℕ → Prop}
    (h : Crit n d bad) {A : Finset ℕ} (hA : A.card = n) (hsub : ∀ a ∈ A, a ∈ d)
    (hgood : ∀ a ∈ A, ∀ b ∈ A, ¬ bad a b) : False := by
  have hsub' : A ⊆ d.toFinset := fun a ha => List.mem_toFinset.mpr (hsub a ha)
  have hle : A.card ≤ d.length := by
    calc A.card ≤ d.toFinset.card := Finset.card_le_card hsub'
      _ = d.length := List.toFinset_card_of_nodup hd
  rcases h with hlt | ⟨hlen, a, ha, b, hb, hbad⟩
  · omega
  · have hEq : A = d.toFinset :=
      Finset.eq_of_subset_of_card_le hsub' (by rw [List.toFinset_card_of_nodup hd]; omega)
    have ha' : a ∈ A := by rw [hEq]; exact List.mem_toFinset.mpr ha
    have hb' : b ∈ A := by rw [hEq]; exact List.mem_toFinset.mpr hb
    exact hgood a ha' b hb' hbad

theorem y63_idx_M (D : Data) (hM : D.MSpec) {A : Finset ℕ} (hA : A.card = 64)
    (hlt : ∀ a ∈ A, a < 512) (h4 : ∀ a ∈ A, D.pow4 a = 0)
    (hc : ∀ a ∈ A, ∀ b ∈ A, D.mt a b = D.mt b a) : ∀ a ∈ A, a ∈ D.m0 := by
  intro a ha
  by_contra hna
  obtain ⟨-, -, -, -, -, -, hcrit⟩ := hM
  refine y63_crit_eq (List.nodup_range.filter _) (hcrit a (hlt a ha) (h4 a ha) hna) hA
    (fun b hb => ?_) (fun b hb c hc' => ?_)
  · simp only [Data.D4, List.mem_filter, List.mem_range, Bool.and_eq_true, beq_iff_eq]
    exact ⟨hlt b hb, h4 b hb, hc a ha b hb⟩
  · exact not_not.mpr (hc b hb c hc')

theorem y63_idx_U (D : Data) {k : ℕ} (hU : D.USpec k) {A : Finset ℕ} (hA : A.card = 128)
    (hlt : ∀ a ∈ A, a < 1024) (hsq : ∀ a ∈ A, D.sqz k a)
    (hc : ∀ a ∈ A, ∀ b ∈ A, D.cz k a b) : ∀ a ∈ A, a ∈ D.u0 k := by
  intro a ha
  by_contra hna
  obtain ⟨-, -, -, -, -, -, -, -, -, hcrit⟩ := hU
  refine y63_crit_eq (List.nodup_range.filter _) (hcrit a (hlt a ha) (hsq a ha) hna) hA
    (fun b hb => ?_) (fun b hb c hc' => ?_)
  · simp only [Data.Dz, List.mem_filter, List.mem_range, decide_eq_true_eq]
    exact ⟨hlt b hb, hsq b hb, hc a ha b hb⟩
  · exact not_not.mpr (hc b hb c hc')

end CFSG.OddStandard.HigherRank.YamadaG23
