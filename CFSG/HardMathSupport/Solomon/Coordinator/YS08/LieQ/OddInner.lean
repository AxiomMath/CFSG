module

public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.OddExc
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.OddSp
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.OddSU
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.OddOmega
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.OddDispatch

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ

open CFSG.Open CFSG.LieType.BorelTits CFSG.Blueprint CFSG.Assembly.LowTwoRank

set_option linter.unusedSectionVars false

theorem two_ne_zero_of_charP_odd {K : Type} [Field K] {q : ℕ} [Fact q.Prime] [CharP K q]
    (hq2 : q ≠ 2) : (2 : K) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
  have hdvd : q ∣ 2 := (CharP.cast_eq_zero_iff K q 2).1 h'
  exact hq2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : q.Prime) Nat.prime_two).1 hdvd)

theorem radRigidInner_classical_odd {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {S : Type} [Group S]
    {t : StatedLieTag} {n f : ℕ} (ht : t ∈ classicalTags) (h : StatedClassicalModel S t n q f) :
    RadRigidInner q S := by
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨hadm, hmodel⟩ := h
  simp only [classicalTags, Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
  ·
    obtain ⟨-, -, hn2, -, -⟩ := hadm
    obtain ⟨K, _, hfin, hcard, ⟨e⟩⟩ := hmodel
    haveI : CharP K q := charP_of_natCard_eq hcard
    exact (radRigidInner_PSL n (F := K) (q := q)).of_mulEquiv e.symm
  ·
    obtain ⟨-, -, hn3, -⟩ := hadm
    obtain ⟨K, _, hfin, hcard, ⟨e⟩⟩ := hmodel
    haveI : CharP K q := charP_of_natCard_eq (p := q) (f := f * 2) (by rw [hcard, pow_mul])
    exact (radRigidInner_PSU (F := K) (q := q) (f := f) hcard n hn3).of_mulEquiv e.symm
  ·
    obtain ⟨-, -, hn2, -⟩ := hadm
    obtain ⟨K, _, hfin, hcard, ⟨e⟩⟩ := hmodel
    haveI : CharP K q := charP_of_natCard_eq hcard
    exact (radRigidInner_PSp n (F := K) (q := q) hn2).of_mulEquiv e.symm
  ·
    obtain ⟨-, -, hn3, -⟩ := hadm
    obtain ⟨K, _, hfin, hcard, ⟨e⟩⟩ := hmodel
    haveI : CharP K q := charP_of_natCard_eq hcard
    have hι : 6 ≤ Fintype.card (Fin n ⊕ Fin n ⊕ Unit) := by
      simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]
      omega
    exact (radRigidInner_Omega (F := K) (q := q) (quadOddForm n K (two_ne_zero_of_charP_odd hq2)) hι).of_mulEquiv
      e.symm
  ·
    obtain ⟨-, -, hn4⟩ := hadm
    obtain ⟨K, _, hfin, hcard, ⟨e⟩⟩ := hmodel
    haveI : CharP K q := charP_of_natCard_eq hcard
    have hι : 6 ≤ Fintype.card (Fin n ⊕ Fin n) := by
      simp only [Fintype.card_sum, Fintype.card_fin]
      omega
    exact (radRigidInner_Omega (F := K) (q := q) (quadPlusForm n K) hι).of_mulEquiv e.symm
  ·
    obtain ⟨-, -, hn4⟩ := hadm
    obtain ⟨K, _, hfin, hcard, b, c, hirr, ⟨e⟩⟩ := hmodel
    haveI : CharP K q := charP_of_natCard_eq hcard
    have hι : 6 ≤ Fintype.card (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) := by
      simp only [Fintype.card_sum, Fintype.card_fin]
      omega
    exact (radRigidInner_Omega (F := K) (q := q) (quadMinusForm n K b c hirr) hι).of_mulEquiv e.symm

@[expose] def Psl28Inner : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    StatedClassicalModel S .PSL 2 2 3 → RadRigidInner 3 S ∧ Holds S 3

section Assembly


theorem oddFamiliesInner {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (h28 : q = 3 → Psl28Inner) :
    OddFamiliesFor q (fun S _ => RadRigidInner q S) := by
  haveI : Fact q.Prime := ⟨hq⟩
  exact
    { classical := fun S _ _ _ _ t n f ht h _ => radRigidInner_classical_odd hq hq2 ht h
      exceptional := fun S _ _ hs hna t f ht h _ =>
        radRigidInner_of_radRigid (center_eq_bot_of_simple_nonabelian hs hna)
          (radRigid_exceptional_odd hq hq2 ht h)
      ree := fun S _ _ hs hna f h _ =>
        radRigidInner_of_radRigid (center_eq_bot_of_simple_nonabelian hs hna) (radRigid_ree_odd h)
      psl28 := fun hq3 S _ _ hs hna h => by
        subst hq3
        exact h28 rfl S hs hna h }

theorem lieQConstrainedInner_of_ne_three {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hq3 : q ≠ 3) :
    LieQConstrainedInner q :=
  lieQConstrainedInner_of_oddFamilies hq hq2 (oddFamiliesInner hq hq2 fun h => absurd h hq3)

theorem lieQConstrainedInner_three (h28 : Psl28Inner) : LieQConstrainedInner 3 :=
  lieQConstrainedInner_of_oddFamilies Nat.prime_three (by norm_num) (oddFamiliesInner Nat.prime_three
    (by norm_num) fun _ => h28)

end Assembly

end CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ
