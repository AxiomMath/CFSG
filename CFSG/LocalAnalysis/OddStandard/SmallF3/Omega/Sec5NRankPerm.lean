module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5NRankFin

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

@[expose] def NrPres (σ : Equiv.Perm (Bool × Fin 3)) : Prop :=
  ∀ s t : Bool × Fin 3, NrR (σ s) (σ t) ↔ NrR s t

instance (σ : Equiv.Perm (Bool × Fin 3)) : Decidable (NrPres σ) := by
  unfold NrPres; infer_instance

@[expose] def nrInv : Finset (Equiv.Perm (Bool × Fin 3)) :=
  Finset.univ.filter (fun a => a * a = 1 ∧ NrPres a)

theorem mem_nrInv {a : Equiv.Perm (Bool × Fin 3)} : a ∈ nrInv ↔ a * a = 1 ∧ NrPres a := by
  simp [nrInv]

theorem sec5nr_ff_aux : ∀ a ∈ nrInv, ∀ b ∈ nrInv, a * b = b * a → ∀ c ∈ nrInv,
    a * c = c * a → b * c = c * b →
      a = 1 ∨ b = 1 ∨ b = a ∨ c = 1 ∨ c = a ∨ c = b ∨ c = a * b := by
  decide +kernel

theorem sec5nr_ff {a b c : Equiv.Perm (Bool × Fin 3)} (ha : a * a = 1 ∧ NrPres a)
    (hb : b * b = 1 ∧ NrPres b) (hc : c * c = 1 ∧ NrPres c) (hab : a * b = b * a)
    (hac : a * c = c * a) (hbc : b * c = c * b) :
    a = 1 ∨ b = 1 ∨ b = a ∨ c = 1 ∨ c = a ∨ c = b ∨ c = a * b :=
  sec5nr_ff_aux a (mem_nrInv.mpr ha) b (mem_nrInv.mpr hb) hab c (mem_nrInv.mpr hc) hac hbc

theorem sec5nr_card_le_four (Y : Subgroup (Equiv.Perm (Bool × Fin 3)))
    (hsq : ∀ y ∈ Y, y * y = 1 ∧ NrPres y) (hcomm : ∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x) :
    Nat.card Y ≤ 4 := by
  classical
  by_contra hlt
  push_neg at hlt
  let S : Finset (Equiv.Perm (Bool × Fin 3)) := Finset.univ.filter (· ∈ Y)
  have hcard : S.card = Nat.card Y := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  obtain ⟨a, haS, ha1⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({1} : Finset (Equiv.Perm (Bool × Fin 3)))) (t := S)
    (by rw [Finset.card_singleton, hcard]; omega)
  obtain ⟨b, hbS, hb1⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({1, a} : Finset (Equiv.Perm (Bool × Fin 3)))) (t := S)
    (by
      calc ({1, a} : Finset (Equiv.Perm (Bool × Fin 3))).card ≤ 2 := Finset.card_le_two
        _ < S.card := by rw [hcard]; omega)
  obtain ⟨c, hcS, hc1⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({1, a, b, a * b} : Finset (Equiv.Perm (Bool × Fin 3)))) (t := S)
    (by
      calc ({1, a, b, a * b} : Finset (Equiv.Perm (Bool × Fin 3))).card ≤ 4 := Finset.card_le_four
        _ < S.card := by rw [hcard]; omega)
  have haY : a ∈ Y := (Finset.mem_filter.mp haS).2
  have hbY : b ∈ Y := (Finset.mem_filter.mp hbS).2
  have hcY : c ∈ Y := (Finset.mem_filter.mp hcS).2
  simp only [Finset.mem_singleton, Finset.mem_insert, not_or] at ha1 hb1 hc1
  rcases sec5nr_ff (hsq a haY) (hsq b hbY) (hsq c hcY) (hcomm a haY b hbY) (hcomm a haY c hcY)
    (hcomm b hbY c hcY) with h | h | h | h | h | h | h
  · exact ha1 h
  · exact hb1.1 h
  · exact hb1.2 h
  · exact hc1.1 h
  · exact hc1.2.1 h
  · exact hc1.2.2.1 h
  · exact hc1.2.2.2 h

end CFSG.OddStandard.SmallF3.Omega
