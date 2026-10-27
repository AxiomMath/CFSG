module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1PCatLie
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1PCatSpor
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1POdd
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1PExp
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1PReduction
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCF23Sp44Main

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1P

open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.Open

theorem gomi1P_card_of_catalog
    {T : Type} [Group T] [Finite T] (hcat : Catalog T) (hnab : ∃ a b : T, a * b ≠ b * a)
    (hdvd : 979200 ∣ Nat.card T) (hv : ¬ 2 ^ 9 ∣ Nat.card T)
    (h4 : ∀ (x : T) (k : ℕ), x ^ (2 ^ k) = 1 → x ^ 4 = 1)
    (hE : ∃ E : Subgroup T, Nat.card E = 2 ^ 6 ∧ (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧
      ∀ x ∈ E, x * x = 1) : Nat.card T = 979200 := by
  have hord : ∃ m : ℕ, Odd m ∧ Nat.card T = 2 ^ 8 * m := by
    obtain ⟨k, hk⟩ := hdvd
    refine ⟨3825 * k, ?_, by rw [hk]; ring⟩
    by_contra hnodd
    apply hv
    obtain ⟨j, hj⟩ := Nat.not_odd_iff_even.mp hnodd
    exact ⟨j, by rw [hk]; omega⟩
  have hdvd' : 3 ^ 2 * 5 ^ 2 * 17 ∣ Nat.card T :=
    (show 3 ^ 2 * 5 ^ 2 * 17 ∣ 979200 by norm_num).trans hdvd
  obtain ⟨a, b, hab⟩ := hnab
  rcases hcat with ⟨p, hp, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | hcl | hex | hs
  · exfalso
    apply hab
    apply e.injective
    rw [map_mul, map_mul, mul_comm]
  · exfalso
    have hc : Nat.card T = n.factorial / 2 := by
      have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    rw [hc] at hdvd hv
    exact not_alternating_of_dvd hdvd hv (by omega)
  · obtain ⟨t, n, p, f, h⟩ := hcl
    by_cases hp2 : p = 2
    · subst hp2
      exact classical_two_card h hdvd hv
    · exfalso
      have htc : t ∈ classicalTags := by
        cases t <;> first | decide | exact h.2.elim
      exact gomi1P_not_odd_lie h.1.1 hp2 (Or.inl ⟨htc, h⟩) hord hE hdvd'
  · exfalso
    rcases hex with ⟨t, p, f, ht, h⟩ | ⟨t, p, f, ht, h⟩ | ⟨p, f, h⟩
    · by_cases hp2 : p = 2
      · subst hp2
        exact not_exceptional_two ht h hv
      · exact gomi1P_not_odd_lie h.1.1 hp2 (Or.inr (Or.inl ⟨rfl, ht, h⟩)) hord hE hdvd'
    · cases t
      all_goals first | exact absurd ht (by decide) | skip
      · have hp3 : p = 3 := h.1.2.2.2.1
        exact gomi1P_not_odd_lie h.1.1 (by rw [hp3]; norm_num)
          (Or.inr (Or.inr (Or.inl ⟨rfl, ht, h⟩))) hord hE hdvd'
      · exact not_twistedF4 h hv
      · exact not_tits h hdvd
    · exact not_suzuki h hdvd hv
  · exact (not_sporadic hs ⟨a, b, hab⟩ hdvd hv h4).elim

open Subgroup in
theorem gomi1PIdent_of_catalog
    {X : Type} [Group X] [Finite X] {Y L : Subgroup X}
    (hY : CFSG.Blueprint.LieModel ↥Y .PSp 2 2 2) (hcat : Catalog ↥L) : Gomi1PIdent Y L := by
  intro hF
  obtain ⟨hsimple, hnab, hYL, -, -, -, ⟨U, hUY, hUs, hUc, -, -⟩, ⟨E, hEY, hEc, hEab, hEexp⟩⟩ := hF
  have hYcard : Nat.card Y = 979200 :=
    CFSG.ComponentClassification.GSThmB.CF23I.card_of_lieModel_Sp44 hY
  have hdvd : 979200 ∣ Nat.card L := hYcard ▸ Subgroup.card_dvd_of_le hYL
  have hN0 : Nat.card L ≠ 0 := Nat.card_pos.ne'
  have hv : ¬ 2 ^ 9 ∣ Nat.card L := by
    have h := hUs.card_eq (p := 2)
    rw [hUc] at h
    have hv8 : (Nat.card L).factorization 2 = 8 := (Nat.pow_right_injective le_rfl h).symm
    intro h9
    have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hN0).1 h9
    omega
  have h4 : ∀ (x : L) (k : ℕ), x ^ (2 ^ k) = 1 → x ^ 4 = 1 := fun x k hx =>
    Subtype.ext (by
      simpa using pow_four_eq_one_of_isSylowOf hY hUY hUs x.2
        (by simpa using congrArg Subtype.val hx))
  have hEL : E ≤ L := hEY.trans hYL
  have hE' : ∃ E' : Subgroup L, Nat.card E' = 2 ^ 6 ∧ (∀ x ∈ E', ∀ y ∈ E', x * y = y * x) ∧
      ∀ x ∈ E', x * x = 1 := by
    refine ⟨E.subgroupOf L, ?_, fun x hx y hy => Subtype.ext (hEab _ hx _ hy),
      fun x hx => Subtype.ext (hEexp _ hx)⟩
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv, hEc]
  have hnab' : ∃ a b : L, a * b ≠ b * a := by
    obtain ⟨a, ha, b, hb, hab⟩ := hnab
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, fun h => hab (congrArg Subtype.val h)⟩
  have hL : Nat.card L = 979200 := gomi1P_card_of_catalog hcat hnab' hdvd hv h4 hE'
  exact (Subgroup.eq_of_le_of_card_ge hYL (by rw [hYcard, hL])).symm

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1P
