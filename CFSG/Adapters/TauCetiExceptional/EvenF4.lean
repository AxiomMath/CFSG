module

public import CFSG.Adapters.TauCetiExceptional.EvenTail
public import CFSG.LieType.Ree.LargeReeExceptionalFullCentralizer

public noncomputable section

namespace CFSG.TauCetiBridge.Even

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree TauCeti
  BigCell

section Frobenius

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]

theorem finiteExceptionalAut_odd_xElement_F4
    (j : ℕ) (i : Fin ReeTag.F4.tag.rank) (c : K) :
    (ReeTag.F4.finiteExceptionalAut K ^ (2 * j + 1)) (xElement i c) =
      xElement (ReeTag.F4.perm i) (c ^ (ReeTag.F4.exponent i * 2 ^ j)) := by
  rw [pow_succ, MulAut.mul_apply, ReeTag.finiteExceptionalAut_xElement,
    finiteExceptionalAut_pow_two_mul, ReeTag.finiteFrobeniusAut_pow_xElement, ← pow_mul]
  rfl

end Frobenius

theorem false_of_conj_odd_F4
    {L : Type} [Field L] (E : Subfield L) [Finite E]
    [CharP E ReeTag.F4.prime] {f : ℕ} (hE : Nat.card E = 2 ^ f) (hf : 3 ≤ f)
    (h' : ModGL ReeTag.F4.tag L) {j : ℕ} (hj : 2 * j + 1 < 2 * f)
    (hconj : ∀ x : adjointGroup ReeTag.F4.tag E,
      h' * baseChangeGL E.subtype (x : ModGL ReeTag.F4.tag E) * h'⁻¹ = baseChangeGL E.subtype
        ((ReeTag.F4.finiteExceptionalAut E ^ (2 * j + 1)) x : ModGL ReeTag.F4.tag E)) :
    False := by
  have hx : ∀ (i : Fin ReeTag.F4.tag.rank) (c : E),
      h' * xUnit ReeTag.F4.tag L i (c : L) * h'⁻¹ =
        xUnit ReeTag.F4.tag L (ReeTag.F4.perm i) ((c : L) ^ (ReeTag.F4.exponent i * 2 ^ j)) := by
    intro i c
    have e := hconj (xElement i c)
    rw [finiteExceptionalAut_odd_xElement_F4] at e
    simpa only [xElement, baseChangeGL_xUnit, Subfield.coe_subtype, SubmonoidClass.coe_pow]
      using e
  have hA3 : ∀ i, xCoeff ReeTag.F4.tag L i 3 = 0 := fun i => xCoeff_three_eq_zero (by decide) i
  have hpow : ∀ a b : ℕ, a < b → 2 ^ a < 2 ^ b := fun a b hab =>
    Nat.pow_lt_pow_right (by norm_num) hab
  have h2j : 1 ≤ 2 ^ j := Nat.one_le_two_pow
  by_cases hjf : j + 1 < f
  ·
    have hexp : ReeTag.F4.exponent ⟨3, by decide⟩ = 2 := by decide
    refine false_of_conj_xUnit_pow (i := ⟨3, by decide⟩) (i' := ReeTag.F4.perm ⟨3, by decide⟩) E h'
      (hA3 _) (m := 2 * 2 ^ j) (by omega) ?_ ?_ fun c => ?_
    · rw [hE, ← pow_succ']
      exact hpow _ _ hjf
    · by_cases hj0 : j = 0
      · refine Or.inr ?_
        rw [hE, hj0]
        calc 2 * (2 * 2 ^ 0) < 2 ^ 3 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
      · refine Or.inl ?_
        have : 2 ≤ 2 ^ j := by
          calc 2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
    · rw [hx, hexp]
  ·
    have hexp : ReeTag.F4.exponent ⟨0, by decide⟩ = 1 := by decide
    have hj2 : 2 ≤ j := by omega
    have h4 : 4 ≤ 2 ^ j := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj2
    refine false_of_conj_xUnit_pow (i := ⟨0, by decide⟩) (i' := ReeTag.F4.perm ⟨0, by decide⟩) E h'
      (hA3 _) (m := 2 ^ j) (by omega) ?_ (Or.inl (by omega)) fun c => ?_
    · rw [hE]
      exact hpow _ _ (by omega)
    · rw [hx, hexp, one_mul]

section Two

variable {p : ℕ} [Fact p.Prime] {L : Type} [Field L] [IsAlgClosed L] [CharP L p]
  [Algebra (ZMod p) L] [Algebra.IsAlgebraic (ZMod p) L]

theorem le_adjointGroup_F4_two'
    (hp : p = 2) (H : Subgroup (ModGL ReeTag.F4.tag L))
    (hCH : adjointGroup ReeTag.F4.tag L ≤ H)
    (hH : ∀ h ∈ H, ∀ P, VanishesOnRat ReeTag.F4.tag P →
      evalMat (natMat ReeTag.F4.tag L (h : Module.End L (RootModule ReeTag.F4.tag L))) P = 0) :
    H ≤ adjointGroup ReeTag.F4.tag L := by
  subst hp
  intro h hh
  obtain ⟨k, hk, ⟨t, ht⟩, α, hα⟩ := exists_conj_mulAut_of_three_le (p := 2) H hCH hH hh
  have : Finite (frobeniusFixedSubfield L 2 k) := finite_frobeniusFixedSubfield L 2 k (by omega)
  have hcard : Nat.card (frobeniusFixedSubfield L 2 k) = 2 ^ k :=
    card_frobeniusFixedSubfield L 2 k (by omega)
  have : CharP (frobeniusFixedSubfield L 2 k) ReeTag.F4.prime :=
    Subfield.charP (frobeniusFixedSubfield L 2 k) 2
  obtain ⟨⟨g, k'⟩, hgk, -⟩ := (even_F4_exact_automorphism_normal_form (by omega)
    (frobeniusFixedSubfield L 2 k) hcard).2.1 α
  rcases Nat.even_or_odd (k' : ℕ) with ⟨j, hj⟩ | ⟨j, hj⟩
  · refine mem_adjointGroup_of_inner_entrywise_two (hasQuadraticNode_of_ne_G2 (by decide)) _
      hcard hk (frobeniusEquiv (frobeniusFixedSubfield L 2 k) 2 ^ j) t ht hCH hH hh g α hα
      fun x => ?_
    rw [hgk, hj, ← two_mul, MulAut.mul_apply, finiteExceptionalAut_pow_two_mul, MulAut.conj_apply,
      Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
      ReeTag.coe_finiteFrobeniusAut_pow (fun c => frobeniusEquiv_def _ 2 c)]
  · exfalso
    set g' : ModGL ReeTag.F4.tag L := baseChangeGL (frobeniusFixedSubfield L 2 k).subtype
      (g : ModGL ReeTag.F4.tag (frobeniusFixedSubfield L 2 k)) with hg'
    refine false_of_conj_odd_F4 (frobeniusFixedSubfield L 2 k) hcard hk (g'⁻¹ * h) (j := j)
      (by have := k'.isLt; omega) fun x => ?_
    have e : g'⁻¹ * h * baseChangeGL (frobeniusFixedSubfield L 2 k).subtype
        (x : ModGL ReeTag.F4.tag (frobeniusFixedSubfield L 2 k)) * (g'⁻¹ * h)⁻¹ =
        g'⁻¹ * (h * baseChangeGL (frobeniusFixedSubfield L 2 k).subtype
          (x : ModGL ReeTag.F4.tag (frobeniusFixedSubfield L 2 k)) * h⁻¹) * g' := by group
    rw [e, ← hα x, hgk, hj, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul,
      Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_mul, map_inv, hg']
    group

theorem le_adjointGroup_F4_two
    (hp : p = 2) (H : Subgroup (ModGL .F4 L))
    (hCH : adjointGroup .F4 L ≤ H)
    (hH : ∀ h ∈ H, ∀ P, VanishesOnRat .F4 P →
      evalMat (natMat .F4 L (h : Module.End L (RootModule .F4 L))) P = 0) :
    H ≤ adjointGroup .F4 L :=
  le_adjointGroup_F4_two' hp H hCH hH

end Two

end CFSG.TauCetiBridge.Even
