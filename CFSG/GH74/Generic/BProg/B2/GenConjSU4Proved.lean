module

public import CFSG.GH74.Generic.BProg.B2.ShapeGenS13
public import CFSG.GH74.Generic.BProg.B2.GenLocU4Inner

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74.Generic.BProg CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  Subgroup Matrix

namespace ShapeGenS13

theorem exists_prime_pow_of_card_sq {F : Type} [Field F] [Finite F] {q : ℕ} (hF : Nat.card F = q ^ 2) :
    ∃ p f : ℕ, p.Prime ∧ q = p ^ f := by
  have : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card F = q ^ 2 := by rw [← hF, Nat.card_eq_fintype_card]
  obtain ⟨n, hp, hn⟩ := FiniteField.card F (ringChar F)
  have hdvd : q ∣ (ringChar F) ^ (n : ℕ) := by
    rw [← hn, hcard]
    exact Dvd.intro_left q (by ring)
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  exact ⟨ringChar F, i, hp, hi⟩

theorem genConjSU4_proved : GenConjSU4 := by
  intro q F _ _ hF hq Kt _ _ he B hB hcard
  obtain ⟨e⟩ := he
  obtain ⟨p, f, hp, rfl⟩ := exists_prime_pow_of_card_sq hF
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h1 : Nat.card F ≥ 2 := Nat.succ_le_of_lt (Finite.one_lt_card (α := F))
    rcases Nat.eq_zero_or_pos f with rfl | hf
    · simp at hF
      omega
    · have : 2 ∣ 2 ^ f := dvd_pow_self 2 hf.ne'
      omega
  have h : UnitaryFieldData p f F := GenLocDiagU.unitaryFieldData_of_card hp hF
  let β : ↥B →* ↥(StatedSU 4 (p ^ f) F) := e.toMonoidHom.comp B.subtype
  let α : ↥B →* MulAut ↥(StatedSU 4 (p ^ f) F) :=
    (MulAut.conj : ↥(StatedSU 4 (p ^ f) F) →* MulAut ↥(StatedSU 4 (p ^ f) F)).comp β
  have hEA := hB.1
  have hsq : ∀ a : ↥B, a * a = 1 := fun a => WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hB a
  have key := GenLocU4Basic.gammaAct_su4_of_commuting_squares hp hp2 hF hB α
    (fun a => ((β a : ↥(StatedSU 4 (p ^ f) F)) : GL (Fin 4) F)) ?_ ?_ ?_ ?_
  · exact gammaAct_eq_top_of_equiv e (conjOn B) α (fun a x => by simp [α, β, conjOn_apply, MulAut.conj_apply]) key
  · intro a
    have h1 := (CFSG.ClassicalGroups.UnitaryFlag.mem_unitarySU_iff h).1 (β a).2
    unfold GenLocU4Basic.IsUnitaryU
    convert h1.2 using 3
    ext i j
    simp [UnitaryFieldData.bar_apply]
  · intro a g
    simp [α, MulAut.conj_apply]
  · intro a b
    have : β a * β b = β b * β a := by rw [← map_mul, ← map_mul, mul_comm' a b]
    exact congrArg (fun z : ↥(StatedSU 4 (p ^ f) F) => (z : GL (Fin 4) F)) this
  · intro a
    refine ⟨1, one_pow _, ?_⟩
    have h1 : β a * β a = 1 := by rw [← map_mul, hsq a, map_one]
    have h2 := congrArg (fun z : ↥(StatedSU 4 (p ^ f) F) => ((z : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) h1
    simpa using h2

end ShapeGenS13

theorem genConj_1_proved : GenConj QShape1 8 := ShapeGenS13.genConj_1 ShapeGenS13.genConjSU4_proved

theorem shapeGen_1_proved : ShapeGenFor QShape1 8 := ShapeGenS13.shapeGen_1 ShapeGenS13.genConjSU4_proved

end CFSG.GH74.Generic.BProg.B2
