module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_7FinL3

public section

namespace CFSG.GH74.QTGen4.DSGen4.L34

open CFSG.QuasithinUnique.Fin257.L3
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour

theorem xP_mul_yP_sq {F : Type} [Field F] [CharP F 2] (a b : F) :
    (xP a * yP b) * (xP a * yP b) = wP (a * b) := by
  rw [← commutatorElement_xP_yP, commutatorElement_def, xP_inv, yP_inv]
  simp only [mul_assoc]

theorem xP_mul_wP_inj {F : Type} [Field F] [CharP F 2] {a c a' c' : F}
    (h : xP a * wP c = xP a' * wP c') : a = a' ∧ c = c' := by
  have h1 : xP (a' + a) * wP c = wP c' := by
    calc xP (a' + a) * wP c = xP a' * (xP a * wP c) := by rw [xP_add, mul_assoc]
      _ = xP a' * (xP a' * wP c') := by rw [h]
      _ = wP c' := by rw [← mul_assoc, xP_mul_self, one_mul]
  have h2 : xP (a' + a) * wP c = yP 0 * wP c' := by
    rw [yP_zero, one_mul]
    exact h1
  obtain ⟨hA, -, hc⟩ := xP_wP_eq_yP_wP h2
  exact ⟨by linear_combination hA - CharTwo.add_self_eq_zero a', hc⟩

theorem yP_mul_wP_inj {F : Type} [Field F] [CharP F 2] {b c b' c' : F}
    (h : yP b * wP c = yP b' * wP c') : b = b' ∧ c = c' := by
  have h1 : yP (b' + b) * wP c = wP c' := by
    calc yP (b' + b) * wP c = yP b' * (yP b * wP c) := by rw [yP_add, mul_assoc]
      _ = yP b' * (yP b' * wP c') := by rw [h]
      _ = wP c' := by rw [← mul_assoc, yP_mul_self, one_mul]
  have h2 : xP 0 * wP c' = yP (b' + b) * wP c := by
    rw [xP_zero, one_mul]
    exact h1.symm
  obtain ⟨-, hB, hc⟩ := xP_wP_eq_yP_wP h2
  exact ⟨by linear_combination hB - CharTwo.add_self_eq_zero b', hc.symm⟩

theorem card_V1 {F : Type} [Field F] [CharP F 2] :
    Nat.card (CFSG.QuasithinUnique.Fin257.L3.V1 : Subgroup (projectiveSL 3 F)) =
      Nat.card F ^ 2 := by
  let f : F × F → (CFSG.QuasithinUnique.Fin257.L3.V1 : Subgroup (projectiveSL 3 F)) :=
    fun p => ⟨xP p.1 * wP p.2, mem_V1.mpr ⟨p.1, p.2, rfl⟩⟩
  have hf : Function.Bijective f := by
    refine ⟨?_, ?_⟩
    · rintro ⟨a, c⟩ ⟨a', c'⟩ h
      have h' : xP a * wP c = xP a' * wP c' := congrArg Subtype.val h
      obtain ⟨ha, hc⟩ := xP_mul_wP_inj h'
      rw [ha, hc]
    · rintro ⟨g, hg⟩
      obtain ⟨a, c, rfl⟩ := mem_V1.mp hg
      exact ⟨(a, c), rfl⟩
  rw [← Nat.card_eq_of_bijective f hf, Nat.card_prod, sq]

theorem card_V2 {F : Type} [Field F] [CharP F 2] :
    Nat.card (CFSG.QuasithinUnique.Fin257.L3.V2 : Subgroup (projectiveSL 3 F)) =
      Nat.card F ^ 2 := by
  let f : F × F → (CFSG.QuasithinUnique.Fin257.L3.V2 : Subgroup (projectiveSL 3 F)) :=
    fun p => ⟨yP p.1 * wP p.2, mem_V2.mpr ⟨p.1, p.2, rfl⟩⟩
  have hf : Function.Bijective f := by
    refine ⟨?_, ?_⟩
    · rintro ⟨b, c⟩ ⟨b', c'⟩ h
      have h' : yP b * wP c = yP b' * wP c' := congrArg Subtype.val h
      obtain ⟨hb, hc⟩ := yP_mul_wP_inj h'
      rw [hb, hc]
    · rintro ⟨g, hg⟩
      obtain ⟨b, c, rfl⟩ := mem_V2.mp hg
      exact ⟨(b, c), rfl⟩
  rw [← Nat.card_eq_of_bijective f hf, Nat.card_prod, sq]

theorem involution_mem_V1_or_V2 {F : Type} [Field F] [CharP F 2] (g : projUnitriangular 3 F)
    (hg : g * g = 1) :
    (g : projectiveSL 3 F) ∈ CFSG.QuasithinUnique.Fin257.L3.V1 ∨
      (g : projectiveSL 3 F) ∈ CFSG.QuasithinUnique.Fin257.L3.V2 := by
  obtain ⟨c, a, b, hgab⟩ := mem_Ubar.mp g.2
  have hg2 : (g : projectiveSL 3 F) * (g : projectiveSL 3 F) = 1 := congrArg Subtype.val hg
  rw [hgab] at hg2
  have hwq : wP c * (xP a * yP b) = xP a * yP b * wP c := by
    rw [← mul_assoc, wP_mul_xP c a, mul_assoc (xP a) (wP c) (yP b), wP_mul_yP c b, ← mul_assoc]
  have hsq : (wP c * xP a * yP b) * (wP c * xP a * yP b) = wP (a * b) := by
    calc (wP c * xP a * yP b) * (wP c * xP a * yP b)
        = wP c * (xP a * yP b) * (wP c * (xP a * yP b)) := by simp only [mul_assoc]
      _ = wP c * (xP a * yP b * wP c) * (xP a * yP b) := by simp only [mul_assoc]
      _ = wP c * (wP c * (xP a * yP b)) * (xP a * yP b) := by rw [← hwq]
      _ = wP c * wP c * ((xP a * yP b) * (xP a * yP b)) := by simp only [mul_assoc]
      _ = wP (a * b) := by rw [wP_mul_self, one_mul, xP_mul_yP_sq]
  have h1 : wP (a * b) = 1 := hsq.symm.trans hg2
  have hab : a * b = 0 := (wP_eq_one_iff (a * b)).mp h1
  rcases mul_eq_zero.mp hab with ha | hb
  · right
    refine mem_V2.mpr ⟨b, c, ?_⟩
    rw [hgab, ha, xP_zero, mul_one, wP_mul_yP]
  · left
    refine mem_V1.mpr ⟨a, c, ?_⟩
    rw [hgab, hb, yP_zero, mul_one, wP_mul_xP]

end CFSG.GH74.QTGen4.DSGen4.L34
