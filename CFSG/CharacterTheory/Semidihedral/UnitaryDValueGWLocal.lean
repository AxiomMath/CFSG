module

public import CFSG.CharacterTheory.Semidihedral.UnitaryDValueGWCommon
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Classification

public section

open scoped Classical

namespace CFSG.Semidihedral.UnitaryDValue.GW

open CFSG.Semidihedral.UnitaryDValue CFSG.Semidihedral.UnitaryDValue.DValueData

variable {G : Type} [Group G] [Fintype G] (D : DValueData G)

theorem isKleinFour_T : IsKleinFour D.T := by
  refine CFSG.Wreathed.isKleinFour_closure_pair D.x_order D.z_order D.z_comm ?_
  rw [Subgroup.disjoint_def]
  intro g hg1 hg2
  rcases eq_one_or_eq_of_mem_zpowers D.x_order hg1 with h | h
  · exact h
  · rcases eq_one_or_eq_of_mem_zpowers D.z_order hg2 with h' | h'
    · exact h'
    · exact absurd (h'.symm.trans h) D.z_ne

theorem card_T : Nat.card D.T = 4 := (isKleinFour_T D).card_four

theorem U_eq_T (hm : D.m = 2) : D.U = D.T := by
  have hTU : D.T ≤ D.U := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact D.x_mem_U
    · exact D.z_mem_U
  obtain ⟨k₀, hk₀⟩ := D.m_dvd
  rw [hm] at hk₀
  have hk₀odd : Odd k₀ := by
    have h := D.odd_quot
    rw [hk₀, hm, Nat.mul_div_cancel_left _ (by norm_num)] at h
    exact h
  have hUcard : Nat.card D.U = 4 := by
    rw [D.card_primaryPart 2, D.card_C, hm, hk₀]
    have hsplit : 2 * Nat.card D.A * (2 * k₀) = 2 ^ 2 * (Nat.card D.A * k₀) := by ring
    have hodd : Odd (Nat.card D.A * k₀) := D.A_odd.mul hk₀odd
    rw [hsplit, Nat.factorization_mul (by positivity) (by
        rintro h0; rw [h0] at hodd; exact absurd hodd (by decide)),
      Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (fun h => (Nat.not_even_iff_odd.mpr hodd)
        (even_iff_two_dvd.mpr h)), add_zero]
    norm_num
  exact (Subgroup.eq_of_le_of_card_ge hTU (by rw [hUcard, card_T])).symm

theorem U_le_centralizer {w : G} (hwC : w ∈ D.C) : D.U ≤ Subgroup.centralizer {w} :=
  fun u hu => Subgroup.mem_centralizer_singleton_iff.mpr (D.C_comm u hu.1 w hwC)

theorem card_sylowU (hm : D.m = 2) {w : G} (hw : w ∈ D.W) (hw1 : w ≠ 1)
    (htw : D.t * w = w * D.t) :
    Nat.card (D.sylowU (D.W_le hw) (sylowU_hyp D hw hw1 htw) :
      Subgroup (Subgroup.centralizer ({w} : Set G))) = 4 := by
  rw [show ((D.sylowU (D.W_le hw) (sylowU_hyp D hw hw1 htw) :
      Subgroup (Subgroup.centralizer ({w} : Set G)))) =
        D.U.subgroupOf (Subgroup.centralizer {w}) from rfl,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (U_le_centralizer D (D.W_le hw))).toEquiv,
    U_eq_T D hm, card_T]

theorem factorization_two_card_centralizer (hm : D.m = 2) {w : G} (hw : w ∈ D.W) (hw1 : w ≠ 1)
    (htw : D.t * w = w * D.t) :
    (Nat.card (Subgroup.centralizer ({w} : Set G))).factorization 2 = 2 := by
  have h := Sylow.card_eq_multiplicity (D.sylowU (D.W_le hw) (sylowU_hyp D hw hw1 htw))
  rw [card_sylowU D hm hw hw1 htw, show (4 : ℕ) = 2 ^ 2 by norm_num] at h
  exact (Nat.pow_right_injective (le_refl 2) h).symm

theorem hasDihedralSylowTwo (hm : D.m = 2) {w : G} (hw : w ∈ D.W) (hw1 : w ≠ 1)
    (htw : D.t * w = w * D.t) :
    CFSG.GorensteinWalter.HasDihedralSylowTwo (Subgroup.centralizer ({w} : Set G)) := by
  intro S'
  refine ⟨1, le_rfl, ?_⟩
  have : IsKleinFour D.T := isKleinFour_T D
  rw [pow_one]
  obtain ⟨e⟩ := IsKleinFour.nonempty_mulEquiv (G₁ := D.T) (G₂ := DihedralGroup 2)
  exact ⟨((Sylow.equiv S' (D.sylowU (D.W_le hw) (sylowU_hyp D hw hw1 htw))).trans
    ((Subgroup.subgroupOfEquivOfLe (U_le_centralizer D (D.W_le hw))).trans
      (MulEquiv.subgroupCongr (U_eq_T D hm)))).trans e⟩

end CFSG.Semidihedral.UnitaryDValue.GW
