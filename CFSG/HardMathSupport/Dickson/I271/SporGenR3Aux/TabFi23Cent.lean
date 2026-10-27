module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabFi23Pts
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabFi23Fi22
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.ConstrainedGen
public import Certificates.Certificate17338

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Dickson.I271.TabFi23

open CFSG.Open CFSG.Sporadic.Fi23 CFSG.Sporadic.Fi23.Native CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23 CFSG.HardMathSupport.Solomon.Coordinator.YS08
open CFSG.Sporadic.Th hiding J a b closure_ab gA gB rows_B_cube

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

local notation "J22" => CFSG.Sporadic.Fi22.J

section Data

theorem fixN_eq_natCard (q : Equiv.Perm (Fin 3510)) :
    Fi22Copy.fixN q = Nat.card {w : Fin 3510 // q w = w} :=
  TabFi22Small.fixN_eq_card q

theorem card_valency_eq (x : CFSG.Sporadic.Fi23.J) (p : Fin 31671) :
    Nat.card {z : CFSG.Sporadic.Fi23.J // z ∈ D23 ∧ z ≠ conjPt p.val ∧ z * conjPt p.val = conjPt p.val * z ∧
        z * x = x * z} =
      Nat.card {r : Fin 31671 // r ≠ p ∧
        conjPt r.val * conjPt p.val = conjPt p.val * conjPt r.val ∧ x • r = r} := by
  symm
  let f : {r : Fin 31671 // r ≠ p ∧
        conjPt r.val * conjPt p.val = conjPt p.val * conjPt r.val ∧ x • r = r} →
      {z : CFSG.Sporadic.Fi23.J // z ∈ D23 ∧ z ≠ conjPt p.val ∧ z * conjPt p.val = conjPt p.val * z ∧
        z * x = x * z} :=
    fun r => ⟨conjPt r.1.val, conjPt_mem_D23 r.1.2,
      fun h => r.2.1 (Fin.ext (conjPt_injOn r.1.2 p.2 h)), r.2.2.1,
      (fix_iff_comm x r.1).1 r.2.2.2⟩
  refine Nat.card_eq_of_bijective f ⟨?_, ?_⟩
  · intro r r' h
    have h2 : conjPt r.1.val = conjPt r'.1.val := congrArg Subtype.val h
    exact Subtype.ext (Fin.ext (conjPt_injOn r.1.2 r'.1.2 h2))
  · intro z
    obtain ⟨i, hi⟩ := (isConj_d_iff z.1).1 z.2.1
    refine ⟨⟨i, ?_, ?_, ?_⟩, Subtype.ext hi⟩
    · intro h
      apply z.2.2.1
      rw [← hi, h]
    · rw [hi]
      exact z.2.2.2.1
    · rw [fix_iff_comm, hi]
      exact z.2.2.2.2

theorem card_cent_of_data {x : CFSG.Sporadic.Fi23.J} (hx : orderOf x = 3) {p : Fin 31671} (hp : x • p = p)
    {N V : ℕ} (hN : Nat.card {r : Fin 31671 // x • r = r} = N)
    (hV : Nat.card {r : Fin 31671 // r ≠ p ∧
      conjPt r.val * conjPt p.val = conjPt p.val * conjPt r.val ∧ x • r = r} = V)
    (htr : ∀ r : Fin 31671, x • r = r → ∃ g ∈ Subgroup.centralizer ({x} : Set CFSG.Sporadic.Fi23.J), g • p = r) :
    ∃ t : J22, orderOf t = 3 ∧ Fi22Copy.fixN (pi22 t) = V ∧
      Nat.card ↥(Subgroup.centralizer ({x} : Set CFSG.Sporadic.Fi23.J)) =
        N * (2 * Nat.card ↥(Subgroup.centralizer ({t} : Set J22))) := by
  have he : conjPt p.val ∈ D23 := conjPt_mem_D23 p.2
  have hxe : x * conjPt p.val = conjPt p.val * x := ((fix_iff_comm x p).1 hp).symm
  obtain ⟨t, ht3, hcard, hfix⟩ := exists_lift_conj he hx hxe
  refine ⟨t, ht3, ?_, ?_⟩
  · rw [fixN_eq_natCard, hfix, card_valency_eq, hV]
  · rw [card_cent_eq_mul_stab hp htr, hN, hcard]

@[expose] def ClassData (x : CFSG.Sporadic.Fi23.J) (N V : ℕ) : Prop :=
  orderOf x = 3 ∧ ∃ p : Fin 31671, x • p = p ∧ Nat.card {r : Fin 31671 // x • r = r} = N ∧
    Nat.card {r : Fin 31671 // r ≠ p ∧
      conjPt r.val * conjPt p.val = conjPt p.val * conjPt r.val ∧ x • r = r} = V ∧
    ∀ r : Fin 31671, x • r = r → ∃ g ∈ Subgroup.centralizer ({x} : Set CFSG.Sporadic.Fi23.J), g • p = r

theorem classData_cent {x : CFSG.Sporadic.Fi23.J} {N V : ℕ} (h : ClassData x N V) :
    ∃ t : J22, orderOf t = 3 ∧ Fi22Copy.fixN (pi22 t) = V ∧
      Nat.card ↥(Subgroup.centralizer ({x} : Set CFSG.Sporadic.Fi23.J)) =
        N * (2 * Nat.card ↥(Subgroup.centralizer ({t} : Set J22))) := by
  obtain ⟨hx, p, hp, hN, hV, htr⟩ := h
  exact card_cent_of_data hx hp hN hV htr

end Data

section Classes

theorem classData_core {x : CFSG.Sporadic.Fi23.J} {N V : ℕ} (h : ClassData x N V) :
    GLAPPrimeCoreOf 3 (Subgroup.centralizer ({x} : Set CFSG.Sporadic.Fi23.J)) = ⊥ := by
  obtain ⟨hx, p, hp, -⟩ := h
  exact gLAPPrimeCoreOf_fi23_eq_bot hx (conjPt_mem_D23 p.2) ((fix_iff_comm x p).1 hp)

theorem t3_classData :
    ClassData (t3 0) 351 126 ∧ ClassData (t3 1) 324 27 ∧ ClassData (t3 2) 135 36 ∧
      ClassData (t3 3) 27 0 :=
  Certificates.certificate17338

theorem finite_J23 : Finite CFSG.Sporadic.Fi23.J := inferInstance

theorem card_cent_t3_one_dvd :
    Nat.card ↥(Subgroup.centralizer ({t3 1} : Set CFSG.Sporadic.Fi23.J)) ∣ 2 ^ 20 * 3 ^ 13 := by
  obtain ⟨t, ht, hf, hc⟩ := classData_cent t3_classData.2.1
  have h := card_cent_dvd_of_fixN ht (Or.inr (Or.inl hf))
  rw [hc]
  have h2 : 324 * (2 * Nat.card ↥(Subgroup.centralizer ({t} : Set J22))) ∣
      324 * (2 * (2 ^ 17 * 3 ^ 9)) := Nat.mul_dvd_mul_left _ (Nat.mul_dvd_mul_left _ h)
  exact h2.trans (by norm_num)

theorem card_cent_t3_three_dvd :
    Nat.card ↥(Subgroup.centralizer ({t3 3} : Set CFSG.Sporadic.Fi23.J)) ∣ 2 ^ 18 * 3 ^ 12 := by
  obtain ⟨t, ht, hf, hc⟩ := classData_cent t3_classData.2.2.2
  have h := card_cent_dvd_of_fixN ht (Or.inl hf)
  rw [hc]
  have h2 : 27 * (2 * Nat.card ↥(Subgroup.centralizer ({t} : Set J22))) ∣
      27 * (2 * (2 ^ 17 * 3 ^ 9)) := Nat.mul_dvd_mul_left _ (Nat.mul_dvd_mul_left _ h)
  exact h2.trans (by norm_num)

theorem pConstrained_t3_one : PConstrainedShape 3 (Subgroup.centralizer ({t3 1} : Set CFSG.Sporadic.Fi23.J)) := by
  haveI := finite_J23
  exact pConstrainedShape_of_solvable Nat.prime_three
    (isSolvable_of_card_dvd_two_three (a := 20) (b := 13) card_cent_t3_one_dvd)
    (classData_core t3_classData.2.1)

theorem pConstrained_t3_three : PConstrainedShape 3 (Subgroup.centralizer ({t3 3} : Set CFSG.Sporadic.Fi23.J)) := by
  haveI := finite_J23
  exact pConstrainedShape_of_solvable Nat.prime_three
    (isSolvable_of_card_dvd_two_three (a := 18) (b := 12) card_cent_t3_three_dvd)
    (classData_core t3_classData.2.2.2)

theorem card_cent_t3_zero :
    Nat.card ↥(Subgroup.centralizer ({t3 0} : Set CFSG.Sporadic.Fi23.J)) = 351 * (2 * (3 * 6531840)) := by
  obtain ⟨t, ht, hf, hc⟩ := classData_cent t3_classData.1
  rw [hc, card_cent_eq_of_fixN ht hf]

end Classes

end CFSG.HardMathSupport.Dickson.I271.TabFi23
