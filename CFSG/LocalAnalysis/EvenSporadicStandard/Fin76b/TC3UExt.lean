
module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC3UExtBase

public import Certificates.Certificate26080

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Certificates CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative CFSG.LieType.Multipliers.U43
  CFSG.EvenSporadicStandard.M24Std.CU43

theorem mem_U43Ext
    {x : Equiv.Perm (Fin 820)} (hx : x ∈ U43Ext) : x ∈ P ∨ ∃ g ∈ P, x = g * rhoPerm := by
  obtain ⟨hn, h2⟩ := rhoOK_spec Certificates.certificate26080.1
  have hle : U43Ext ≤ extSub hn h2 := by
    rw [U43Ext, closure_le]
    rintro _ (⟨z, rfl⟩ | rfl)
    · exact Or.inl (by rw [P_eq_range]; exact ⟨z, rfl⟩)
    · exact Or.inr ⟨1, P.one_mem, by rw [one_mul]⟩
  exact hle hx

theorem sq_mem_P
    {g : Equiv.Perm (Fin 820)} (hg : g ∈ P) : (g * rhoPerm) ^ 2 ∈ P := by
  obtain ⟨hn, h2⟩ := rhoOK_spec Certificates.certificate26080.1
  have hc : rhoPerm * g * rhoPerm⁻¹ ∈ P := (mem_normalizer_iff.1 hn g).1 hg
  have : (g * rhoPerm) ^ 2 = g * (rhoPerm * g * rhoPerm⁻¹) * (rhoPerm * rhoPerm) := by
    rw [pow_two]
    group
  rw [this]
  exact P.mul_mem (P.mul_mem hg hc) h2

section Counts

theorem not_bad_P {g : Equiv.Perm (Fin 820)} (hg : g ∈ P) : ¬ (g ^ 16 = 1 ∧ g ^ 8 ≠ 1) := by
  classical
  intro hbad
  have h := Certificates.certificate26080.2.1
  have hcard : Nat.card {x : P // (x : Equiv.Perm (Fin 820)) ^ 16 = 1 ∧
      (x : Equiv.Perm (Fin 820)) ^ 8 ≠ 1} = 0 := by
    rw [card_eq_countW_P (f := bad16)
      (Pr := fun g => g ^ 16 = 1 ∧ g ^ 8 ≠ 1)]
    · exact h
    · intro w g hw hgP
      exact bad16_iff hw (P.pow_mem hgP _) (P.pow_mem hgP _)
  have hpos : 0 < Nat.card {x : P // (x : Equiv.Perm (Fin 820)) ^ 16 = 1 ∧
      (x : Equiv.Perm (Fin 820)) ^ 8 ≠ 1} :=
    Nat.card_pos_iff.2 ⟨⟨⟨g, hg⟩, hbad⟩, inferInstance⟩
  omega

theorem not_bad_Prho {g : Equiv.Perm (Fin 820)} (hg : g ∈ P) :
    ¬ ((g * rhoPerm) ^ 16 = 1 ∧ (g * rhoPerm) ^ 8 ≠ 1) := by
  classical
  intro hbad
  have h := Certificates.certificate26080.2.2
  have hcard : Nat.card {x : P // ((x : Equiv.Perm (Fin 820)) * rhoPerm) ^ 16 = 1 ∧
      ((x : Equiv.Perm (Fin 820)) * rhoPerm) ^ 8 ≠ 1} = 0 := by
    rw [card_eq_countW_P (f := fun w => bad16 (rhoArr :: w))
      (Pr := fun g => (g * rhoPerm) ^ 16 = 1 ∧ (g * rhoPerm) ^ 8 ≠ 1)]
    · exact h
    · intro w g hw hgP
      have hsq := sq_mem_P hgP
      exact bad16_iff (RepW.cons rep_rhoArr hw)
        (by rw [show (g * rhoPerm) ^ 16 = ((g * rhoPerm) ^ 2) ^ 8 by rw [← pow_mul]]
            exact P.pow_mem hsq _)
        (by rw [show (g * rhoPerm) ^ 8 = ((g * rhoPerm) ^ 2) ^ 4 by rw [← pow_mul]]
            exact P.pow_mem hsq _)
  have hpos : 0 < Nat.card {x : P // ((x : Equiv.Perm (Fin 820)) * rhoPerm) ^ 16 = 1 ∧
      ((x : Equiv.Perm (Fin 820)) * rhoPerm) ^ 8 ≠ 1} :=
    Nat.card_pos_iff.2 ⟨⟨⟨g, hg⟩, hbad⟩, inferInstance⟩
  omega

theorem U43Ext_orderOf_ne_sixteen {x : Equiv.Perm (Fin 820)} (hx : x ∈ U43Ext) :
    orderOf x ≠ 16 := by
  intro h16
  have hx16 : x ^ 16 = 1 := by rw [← h16]; exact pow_orderOf_eq_one x
  have hx8 : x ^ 8 ≠ 1 := pow_ne_one_of_lt_orderOf (by norm_num) (by rw [h16]; norm_num)
  rcases mem_U43Ext hx with hP | ⟨g, hg, rfl⟩
  · exact not_bad_P hP ⟨hx16, hx8⟩
  · exact not_bad_Prho hg ⟨hx16, hx8⟩

end Counts

end CFSG.EvenSporadicStandard.Fin76b
