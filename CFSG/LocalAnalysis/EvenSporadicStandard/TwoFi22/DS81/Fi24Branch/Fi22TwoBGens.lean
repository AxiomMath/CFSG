module

public import CFSG.Sporadic.FischerOddCore.Fi22FiveExact
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Fi22TwoBQCheck

public noncomputable section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Fi22TwoB

open CFSG.Sporadic.FischerOddCore CFSG.Monster.B.Fischer

@[expose] def t1 : Equiv.Perm (Fin 3510) := fi22ExtRep 1

@[expose] def Cbar : Subgroup (Equiv.Perm (Fin 3510)) := fi22R ⊓ Subgroup.centralizer {t1}

@[expose] def cGen (h : Fin 10) : Equiv.Perm (Fin 3510) := fi22CentPerm (cLine h)

theorem cLine_lt (h : ℕ) : cLine h < 306 := by
  unfold cLine
  split_ifs <;> omega

theorem cGen_eq_cent (h : Fin 10) (hh : (h : ℕ) < 9) : cGen h = fi22CentPerm (19 + h) := by
  simp [cGen, cLine, hh]

theorem cGen_nine : cGen 9 = fi22CentC := by
  simp [cGen, cLine, fi22CentC, fi22CentOuterLine]

theorem fi22H_one_eq_closure :
    fi22H 1 = Subgroup.closure (Set.range fun h : Fin 9 => fi22CentPerm (19 + h)) := by
  rw [fi22H_eq_closure (c := 1) (by norm_num)]
  have e1 : fi22CentGenCount.getD 1 0 = 9 := rfl
  have e2 : fi22CentStrongStart.getD 1 0 = 19 := rfl
  rw [e1, e2]
  congr 1
  ext g
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨⟨j, hj⟩, rfl⟩
  · rintro ⟨⟨j, hj⟩, rfl⟩
    exact ⟨j, hj, rfl⟩

theorem cGen_mem_fi22H (h : Fin 10) (hh : (h : ℕ) < 9) :
    cGen h ∈ fi22H 1 := by
  rw [fi22H_one_eq_closure, cGen_eq_cent h hh]
  exact Subgroup.subset_closure ⟨⟨h, hh⟩, rfl⟩

theorem cGen_mem_Cbar
    (h : Fin 10) :
    cGen h ∈ Cbar := by
  by_cases hh : (h : ℕ) < 9
  · have hH : fi22H 1 ≤ fi22P ⊓ Subgroup.centralizer {fi22CentT 1} :=
      fi22H_le (c := 1) (by norm_num)
    obtain ⟨hP, hC⟩ := hH (cGen_mem_fi22H h hh)
    exact ⟨fi22P_le_R hP, hC⟩
  · have h9 : h = 9 := by omega
    subst h9
    obtain ⟨-, -, -, -, -, hcR, -, hct⟩ := CTUC_Fi22_involution_relational_graph_bounds
    rw [cGen_nine]
    exact ⟨hcR, Subgroup.mem_centralizer_singleton_iff.2 hct⟩

theorem closure_cGen_le :
    Subgroup.closure (Set.range cGen) ≤ Cbar := by
  rw [Subgroup.closure_le]
  rintro _ ⟨h, rfl⟩
  exact cGen_mem_Cbar h

theorem closure_cGen :
    Subgroup.closure (Set.range cGen) = Cbar := by
  set S := Subgroup.closure (Set.range cGen) with hS
  have hSle : S ≤ Cbar := closure_cGen_le
  obtain ⟨-, hcR, hcP, hct⟩ : fi22R ≤ fi22AutG ∧ fi22CentC ∈ fi22R ∧ fi22CentC ∉ fi22P ∧
      fi22CentC * fi22ExtRep 1 = fi22ExtRep 1 * fi22CentC := by
    obtain ⟨h1, -, -, -, -, h2, h3, h4⟩ := CTUC_Fi22_involution_relational_graph_bounds
    exact ⟨h1, h2, h3, h4⟩
  have hCP : fi22P ⊓ Subgroup.centralizer {fi22ExtRep 1} = fi22H 1 :=
    CTUC_Fi22_five_exact_involution_fixed_subgroups.2.1
  have hHS : fi22H 1 ≤ S := by
    rw [fi22H_one_eq_closure, Subgroup.closure_le]
    rintro _ ⟨⟨j, hj⟩, rfl⟩
    show fi22CentPerm (19 + j) ∈ S
    rw [← cGen_eq_cent ⟨j, by omega⟩ hj]
    exact Subgroup.subset_closure ⟨_, rfl⟩
  have hcS : fi22CentC ∈ S := by
    rw [← cGen_nine]
    exact Subgroup.subset_closure ⟨9, rfl⟩
  have hHP : fi22H 1 ≤ fi22P := by
    rw [← hCP]
    exact inf_le_left
  have hcard : Nat.card Cbar = 2 * Nat.card (fi22H 1) := by
    have := card_inf_centralizer_R hcR hcP hct
    rw [hCP] at this
    exact this
  have hpos : 0 < Nat.card (fi22H 1) := Nat.card_pos
  obtain ⟨a, ha⟩ := Subgroup.card_dvd_of_le hHS
  have hd2 : Nat.card S ∣ 2 * Nat.card (fi22H 1) := hcard ▸ Subgroup.card_dvd_of_le hSle
  have ha2 : a ∣ 2 := by
    have h2 : Nat.card (fi22H 1) * a ∣ Nat.card (fi22H 1) * 2 := by
      rw [← ha, mul_comm _ 2]
      exact hd2
    exact Nat.dvd_of_mul_dvd_mul_left hpos h2
  have ha1 : a ≠ 1 := by
    rintro rfl
    have h1 : Nat.card S ≤ Nat.card (fi22H 1) := by rw [ha, mul_one]
    have heq := Subgroup.eq_of_le_of_card_ge hHS h1
    have : fi22CentC ∈ fi22P := hHP (heq ▸ hcS)
    exact hcP this
  have ha2' : a = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 ha2 with h | h
    · exact absurd h ha1
    · exact h
  refine Subgroup.eq_of_le_of_card_ge hSle ?_
  rw [hcard, ha, ha2', mul_comm]

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Fi22TwoB
