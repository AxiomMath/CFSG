module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Seven
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.Fi7Line
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.PrimePowSeven
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PairConj

public section

namespace CFSG.HardMathSupport.Dickson.I271.Fi7

open CFSG.Open CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native
  CFSG.Blueprint CFSG.Sporadic.Fi24 CFSG.Sporadic.Fi24.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24SevenNative
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Seven
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.CommutingPair
open CFSG.Sporadic.Th hiding J a b closure_ab gA gB rows_B_cube
open scoped commutatorElement

section Base

@[expose] noncomputable def X7 : CFSG.Sporadic.Fi24.J := g7 fi24SevenData.ix
@[expose] noncomputable def Y7 : CFSG.Sporadic.Fi24.J := g7 fi24SevenData.iy
@[expose] noncomputable def C7 : CFSG.Sporadic.Fi24.J := g7 fi24SevenData.ic

instance : Finite CFSG.Sporadic.Fi24.J := Nat.finite_of_card_ne_zero (by rw [card_J]; norm_num)

theorem fi7_cube :
    X7 ^ 7 = 1 ∧ Y7 ^ 7 = 1 ∧ C7 = X7 * Y7 * X7 ^ 6 * Y7 ^ 6 ∧ C7 * X7 = X7 * C7 ∧
      C7 * Y7 = Y7 * C7 ∧
      (∀ i j k i' j' k' : ℕ, i < 7 → j < 7 → k < 7 → i' < 7 → j' < 7 → k' < 7 →
        X7 ^ i * Y7 ^ j * C7 ^ k = X7 ^ i' * Y7 ^ j' * C7 ^ k' → i = i' ∧ j = j' ∧ k = k') :=
  ⟨fi24Seven_parts.pow_x, fi24Seven_parts.pow_y, fi24Seven_parts.comm, fi24Seven_parts.comm_x,
    fi24Seven_parts.comm_y, fi24Seven_parts.inj⟩

@[expose] noncomputable def M7 (t : ℕ) : CFSG.Sporadic.Fi24.J := ((fi24SevenData.conj[t]!).2.map (pairG g7)).prod

@[expose] noncomputable def cube7 (t : ℕ) : CFSG.Sporadic.Fi24.J := X7 ^ (t / 49) * Y7 ^ (t / 7 % 7) * C7 ^ (t % 7)

theorem fi7_conj_rel {t : ℕ} (ht : t ∈ conjTs) :
    M7 t * cube7 t = (if (fi24SevenData.conj[t]!).1 == 0 then Y7 else C7) * M7 t :=
  fi24Seven_parts.rel t ht

theorem conj_letters_lt {t : ℕ} (ht : t ∈ conjTs) :
    ∀ l ∈ (fi24SevenData.conj[t]!).2, l < 2 * 1087 :=
  fi24Seven_parts.conj_lt t ht

@[expose] noncomputable def Q7 : Subgroup CFSG.Sporadic.Fi24.J := Subgroup.closure ({X7, Y7} : Set CFSG.Sporadic.Fi24.J)

theorem fi7_comm_xy : ⁅X7, Y7⁆ = C7 := by
  obtain ⟨hx7, hy7, hc, -⟩ := fi7_cube
  rw [hc, commutatorElement_eq_of_pow (by norm_num) hx7 hy7]

theorem fi7_commute_x : Commute ⁅X7, Y7⁆ X7 := by
  rw [fi7_comm_xy]; exact fi7_cube.2.2.2.1

theorem fi7_commute_y : Commute ⁅X7, Y7⁆ Y7 := by
  rw [fi7_comm_xy]; exact fi7_cube.2.2.2.2.1

theorem card_Q7 : Nat.card Q7 = 7 ^ 3 := by
  obtain ⟨hx7, hy7, -, -, -, hinj⟩ := fi7_cube
  refine CFSG.SectionRank.LocalWitness.card_closure_eq_cube (by norm_num) hx7 hy7 fi7_commute_x
    fi7_commute_y ?_
  rintro ⟨i, j, k⟩ ⟨i', j', k'⟩ h
  simp only [fi7_comm_xy] at h
  obtain ⟨h1, h2, h3⟩ := hinj i j k i' j' k' i.2 j.2 k.2 i'.2 j'.2 k'.2 h
  exact Prod.ext (Fin.ext h1) (Prod.ext (Fin.ext h2) (Fin.ext h3))

theorem X7_mem : X7 ∈ Q7 := Subgroup.subset_closure (by simp)
theorem Y7_mem : Y7 ∈ Q7 := Subgroup.subset_closure (by simp)

theorem C7_mem : C7 ∈ Q7 := by
  rw [← fi7_comm_xy, commutatorElement_def]
  exact Q7.mul_mem (Q7.mul_mem (Q7.mul_mem X7_mem Y7_mem) (Q7.inv_mem X7_mem)) (Q7.inv_mem Y7_mem)

theorem cube7_mem (t : ℕ) : cube7 t ∈ Q7 :=
  Q7.mul_mem (Q7.mul_mem (Q7.pow_mem X7_mem _) (Q7.pow_mem Y7_mem _)) (Q7.pow_mem C7_mem _)

theorem C7_ne_one : C7 ≠ 1 := by
  intro h
  have := fi7_cube.2.2.2.2.2 0 0 0 0 0 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by simp [h])
  omega

theorem C7_pow_seven : C7 ^ 7 = 1 := by
  obtain ⟨hx7, -⟩ := fi7_cube
  rw [← fi7_comm_xy, CFSG.SectionRank.LocalWitness.commutator_pow_eq fi7_commute_x, hx7,
    commutatorElement_one_left]

theorem orderOf_C7 : orderOf C7 = 7 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact orderOf_eq_prime C7_pow_seven C7_ne_one

theorem Q7_le_centralizer_c : Q7 ≤ Subgroup.centralizer ({C7} : Set CFSG.Sporadic.Fi24.J) := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ (rfl | rfl)
  · exact Subgroup.mem_centralizer_singleton_iff.2 fi7_cube.2.2.2.1.symm
  · exact Subgroup.mem_centralizer_singleton_iff.2 fi7_cube.2.2.2.2.1.symm

theorem X7_Y7_noncomm : X7 * Y7 ≠ Y7 * X7 := by
  intro h
  apply C7_ne_one
  rw [← fi7_comm_xy, commutatorElement_def, h]
  group

theorem Q7_center : ∀ x ∈ Q7, (∀ q ∈ Q7, x * q = q * x) → x ∈ Subgroup.zpowers C7 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  refine center_eq_zpowers_of_nonabelian card_Q7 C7_mem orderOf_C7 (fun q hq => ?_)
    ⟨X7, X7_mem, Y7, Y7_mem, X7_Y7_noncomm⟩
  exact (Subgroup.mem_centralizer_singleton_iff.1 (Q7_le_centralizer_c hq)).symm

theorem factorization_card_J_seven : (Nat.card CFSG.Sporadic.Fi24.J).factorization 7 = 3 := by
  rw [card_J, show (1255205709190661721292800 : ℕ) = 7 ^ 3 * 3659491863529626009600 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow (by norm_num : Nat.Prime 7), Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem Q7_sylow : ∃ S : Sylow 7 CFSG.Sporadic.Fi24.J, (S : Subgroup CFSG.Sporadic.Fi24.J) = Q7 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact ⟨Sylow.ofCard Q7 (by rw [card_Q7, factorization_card_J_seven]), rfl⟩

theorem card_centralizer_C7 : Nat.card (Subgroup.centralizer ({C7} : Set CFSG.Sporadic.Fi24.J)) = 7 ^ 3 * 6 :=
  fi24Seven_parts.card_c

theorem card_centralizer_Y7 : Nat.card (Subgroup.centralizer ({Y7} : Set CFSG.Sporadic.Fi24.J)) = 7 ^ 2 * 360 :=
  fi24Seven_parts.card_y

theorem core_C7 : GLAPPrimeCoreOf 7 (Subgroup.centralizer ({C7} : Set CFSG.Sporadic.Fi24.J)) = ⊥ :=
  fi24Seven_parts.core_c

theorem sevenLine_c : SevenLine 7 C7 Q7 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact sevenLine_of_core C7_ne_one C7_pow_seven C7_mem Q7_le_centralizer_c card_Q7
    card_centralizer_C7 (by norm_num) Q7_center core_C7

theorem fi7_conj_class (e : CFSG.Sporadic.Fi24.J) (he : orderOf e = 7) :
    ∃ g : CFSG.Sporadic.Fi24.J, g * e * g⁻¹ = Y7 ∨ g * e * g⁻¹ = C7 :=
  fi24Seven_parts.conj e he

theorem fi7_rankOK (hw4 : ∃ u ∈ Subgroup.centralizer ({Y7} : Set CFSG.Sporadic.Fi24.J), orderOf u = 4) :
    ∀ e : CFSG.Sporadic.Fi24.J, orderOf e = 7 → RankOK 7 (Subgroup.centralizer ({e} : Set CFSG.Sporadic.Fi24.J)) := by
  have hRc : RankOK 7 (Subgroup.centralizer ({C7} : Set CFSG.Sporadic.Fi24.J)) := by
    refine rankOK_of_primePowOK ?_
    have : Nat.card (Subgroup.centralizer ({C7} : Set CFSG.Sporadic.Fi24.J)) = 2058 := by
      rw [card_centralizer_C7]; norm_num
    rw [this]
    exact primePowOK_seven_2058
  have hRy : RankOK 7 (Subgroup.centralizer ({Y7} : Set CFSG.Sporadic.Fi24.J)) :=
    rankOK_of_two_witness (n := 17640) (by rw [card_centralizer_Y7]; norm_num)
      primePowTwo_seven_17640 hw4
  intro e he
  obtain ⟨g, hg | hg⟩ := fi7_conj_class e he
  · have := rankOK_inf_centralizer_of_conj ⊤ (Subgroup.mem_top g) hg
      (by rw [top_inf_eq]; exact hRy)
    rwa [top_inf_eq] at this
  · have := rankOK_inf_centralizer_of_conj ⊤ (Subgroup.mem_top g) hg
      (by rw [top_inf_eq]; exact hRc)
    rwa [top_inf_eq] at this

end Base

end CFSG.HardMathSupport.Dickson.I271.Fi7
