module

public import Mathlib.LinearAlgebra.QuadraticForm.Basic


public section

namespace CFSG.ClassicalGroups.Orthogonal

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem ncard_eq_one_of_isCompl (Q : QuadraticForm (ZMod 2) V) {W₁ W₂ : Submodule (ZMod 2) V}
    (hc : IsCompl W₁ W₂) (horth : ∀ w₁ ∈ W₁, ∀ w₂ ∈ W₂, QuadraticMap.polar Q w₁ w₂ = 0) :
    {v | Q v = 1}.ncard =
      {w : W₁ | Q w = 1}.ncard * {w : W₂ | Q w = 0}.ncard +
        {w : W₁ | Q w = 0}.ncard * {w : W₂ | Q w = 1}.ncard := by
  classical
  let e : (↥W₁ × ↥W₂) ≃ₗ[ZMod 2] V := Submodule.prodEquivOfIsCompl W₁ W₂ hc
  have he : ∀ p : ↥W₁ × ↥W₂, e p = (p.1 : V) + (p.2 : V) := fun p =>
    Submodule.coe_prodEquivOfIsCompl' (p := W₁) (q := W₂) hc p
  have hpre : {v : V | Q v = 1} =
      e '' {p : ↥W₁ × ↥W₂ | Q ((p.1 : V) + (p.2 : V)) = 1} := by
    ext v
    constructor
    · intro hv
      obtain ⟨p, rfl⟩ := e.surjective v
      exact ⟨p, by simpa [he p] using hv, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      simpa [he p] using hp
  rw [hpre, Set.ncard_image_of_injective _ e.injective]
  have hsplit : {p : ↥W₁ × ↥W₂ | Q ((p.1 : V) + (p.2 : V)) = 1} =
      ({a : ↥W₁ | Q a = 1} ×ˢ {b : ↥W₂ | Q b = 0}) ∪
        ({a : ↥W₁ | Q a = 0} ×ˢ {b : ↥W₂ | Q b = 1}) := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_prod]
    rw [QuadraticMap.map_add Q (p.1 : V) (p.2 : V),
      horth (p.1 : V) p.1.2 (p.2 : V) p.2.2, add_zero]
    have hsum : ∀ a b : ZMod 2, a + b = 1 ↔ (a = 1 ∧ b = 0) ∨ (a = 0 ∧ b = 1) := by
      decide
    exact hsum (Q (p.1 : V)) (Q (p.2 : V))
  have hdisj : Disjoint ({a : ↥W₁ | Q a = 1} ×ˢ {b : ↥W₂ | Q b = 0})
      ({a : ↥W₁ | Q a = 0} ×ˢ {b : ↥W₂ | Q b = 1}) := by
    rw [Set.disjoint_left]
    rintro ⟨a, b⟩ hp₁ hp₂
    simp only [Set.mem_prod, Set.mem_setOf_eq] at hp₁ hp₂
    exact zero_ne_one (hp₁.2.symm.trans hp₂.2)
  rw [hsplit, Set.ncard_union_eq hdisj, Set.ncard_prod, Set.ncard_prod]

theorem ncard_zero_add_ncard_one (Q : QuadraticForm (ZMod 2) V) (W : Submodule (ZMod 2) V) :
    {w : W | Q w = 0}.ncard + {w : W | Q w = 1}.ncard = Nat.card W := by
  have hcompl : ({w : W | Q w = 0} : Set W)ᶜ = {w : W | Q w = 1} := by
    ext w
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq]
    constructor
    · intro h
      have h01 : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
      rcases h01 (Q (w : V)) with h0 | h1
      · exact absurd h0 h
      · exact h1
    · intro h h0
      exact zero_ne_one (h0.symm.trans h)
  rw [← hcompl]
  exact Set.ncard_add_ncard_compl {w : W | Q w = 0}

theorem three_dvd_ncard_one_of_fixedPointFree (Q : QuadraticForm (ZMod 2) V)
    (W : Submodule (ZMod 2) V) (f : Module.End (ZMod 2) V) (hf3 : f ^ 3 = 1)
    (hfW : ∀ w ∈ W, f w ∈ W) (hfix : ∀ w ∈ W, f w = w → w = 0) (hQf : ∀ v, Q (f v) = Q v) :
    3 ∣ {w : W | Q w = 1}.ncard := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  have hf3' : ∀ v : V, f (f (f v)) = v := by
    intro v
    have h := congrArg (fun g : Module.End (ZMod 2) V => g v) hf3
    rw [pow_three', Module.End.mul_apply, Module.End.mul_apply] at h
    simpa using h
  let g : Function.End {w : W | Q w = 1} := fun w =>
    ⟨⟨f (w : V), hfW (w : V) (w : W).2⟩, by
      show Q (f (w : V)) = 1
      rw [hQf]
      exact w.2⟩
  have hg3 : g ^ 3 = 1 := by
    funext w
    apply Subtype.ext
    apply Subtype.ext
    show f (f (f (w : V))) = (w : V)
    exact hf3' (w : V)
  have hfixpts : Function.fixedPoints g = ∅ := by
    ext w
    simp only [Function.mem_fixedPoints_iff, Set.mem_empty_iff_false]
    constructor
    · intro hw
      have hval : f (w : V) = (w : V) := by
        have h1 : ((g w : {w : W | Q w = 1}) : W) = (w : W) := congrArg Subtype.val hw
        have h2 : ((g w : {w : W | Q w = 1}) : V) = (w : V) :=
          congrArg (fun x : W => (x : V)) h1
        change f (w : V) = (w : V) at h2
        exact h2
      have hzero : (w : V) = 0 := hfix (w : W) (w : W).2 hval
      have hQ : Q (w : V) = 1 := w.2
      rw [hzero] at hQ
      have h01 : (0 : ZMod 2) = 1 := by simpa using hQ
      exact zero_ne_one h01
    · intro h
      exact h.elim
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hmod := Equiv.Perm.card_fixedPoints_modEq (α := {w : W | Q w = 1}) (f := g)
    (p := 3) (n := 1) (by simpa using hg3)
  have hmod0 : Fintype.card {w : W | Q w = 1} ≡ 0 [MOD 3] := by
    simpa [hfixpts, Set.card_empty] using hmod
  have hdvd : 3 ∣ Fintype.card {w : W | Q w = 1} := Nat.modEq_zero_iff_dvd.mp hmod0
  rwa [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]

end CFSG.ClassicalGroups.Orthogonal
