module

public import CFSG.LocalAnalysis.ComponentInitial.BinaryOddQuadraticFiveCommon

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.AlternatingEight

open OddQuadraticFive

section Graph

variable {E : Type} [AddCommGroup E] [Module (ZMod 2) E] {b : LinearMap.BilinForm (ZMod 2) E}
  {Q : QuadraticForm (ZMod 2) E}

variable (Q) in
@[expose] def grV (w : E) : (E × ZMod 2) × ZMod 2 := ((w, Q w), 1)

theorem grV_injective : Function.Injective (grV Q) := fun _ _ h =>
  congrArg (fun x : (E × ZMod 2) × ZMod 2 => x.1.1) h

theorem zmod_two_four_identity :
    ∀ p₁ p₂ p₃ c₁₂ c₁₃ c₂₃ : ZMod 2,
      p₁ + p₂ + p₃ + (p₁ + p₂ + c₁₂ + p₃ + (c₁₃ + c₂₃)) = c₁₂ + c₁₃ + c₂₃ := by
  decide

theorem grV_add_four (hQ : QuadraticMap.polarBilin Q = b) (w₁ w₂ w₃ : E) :
    grV Q w₁ + grV Q w₂ + grV Q w₃ + grV Q (w₁ + w₂ + w₃) =
      ((0, b w₁ w₂ + b w₁ w₃ + b w₂ w₃), 0) := by
  have h1 : w₁ + w₂ + w₃ + (w₁ + w₂ + w₃) = 0 := add_self_eq_zero_zmod_two _
  have h2 : Q w₁ + Q w₂ + Q w₃ + Q (w₁ + w₂ + w₃) = b w₁ w₂ + b w₁ w₃ + b w₂ w₃ := by
    rw [Q_add hQ, Q_add hQ, map_add, LinearMap.add_apply]
    exact zmod_two_four_identity _ _ _ _ _ _
  simp only [grV, Prod.mk_add_mk]
  exact Prod.ext (Prod.ext h1 h2) (show (1 + 1 + 1 + 1 : ZMod 2) = 0 by decide)

theorem zmod_two_decomp_identity : ∀ q t : ZMod 2, q + (t + q) = t := by
  decide

theorem zmod_two_decomp_identity' : ∀ s : ZMod 2, 1 + (s + 1) = s := by
  decide

theorem eq_grV_add (w : E) (t s : ZMod 2) :
    (((w, t), s) : (E × ZMod 2) × ZMod 2) =
      grV Q w + (s + 1) • grV Q 0 + (t + Q w) • (((0, 1), 0) : (E × ZMod 2) × ZMod 2) := by
  simp only [grV, QuadraticMap.map_zero, Prod.smul_mk, smul_zero, smul_eq_mul, mul_zero,
    mul_one, Prod.mk_add_mk, add_zero]
  exact Prod.ext (Prod.ext rfl (zmod_two_decomp_identity _ _).symm)
    (zmod_two_decomp_identity' _).symm

theorem rX_eq_sum (hQ : QuadraticMap.polarBilin Q = b) {p q : E} (hpq : b p q = 1) :
    (((0, 1), 0) : (E × ZMod 2) × ZMod 2) =
      grV Q 0 + grV Q p + grV Q q + grV Q (0 + p + q) := by
  rw [grV_add_four hQ, map_zero, LinearMap.zero_apply, LinearMap.zero_apply, hpq, zero_add,
    zero_add]

theorem hom_ext_grV {M : Type*} [Group M] (hQ : QuadraticMap.polarBilin Q = b) {p q : E}
    (hpq : b p q = 1) {ψ₁ ψ₂ : Multiplicative ((E × ZMod 2) × ZMod 2) →* M}
    (h : ∀ w, ψ₁ (Multiplicative.ofAdd (grV Q w)) = ψ₂ (Multiplicative.ofAdd (grV Q w))) :
    ψ₁ = ψ₂ := by
  have hΓ : ∀ w, Multiplicative.ofAdd (grV Q w) ∈ MonoidHom.eqLocus ψ₁ ψ₂ := h
  have hsmul : ∀ x, Multiplicative.ofAdd x ∈ MonoidHom.eqLocus ψ₁ ψ₂ → ∀ c : ZMod 2,
      Multiplicative.ofAdd (c • x) ∈ MonoidHom.eqLocus ψ₁ ψ₂ := by
    intro x hx c
    rcases BinarySymplecticTransvection.zmod_two_cases c with rfl | rfl
    · rw [zero_smul, ofAdd_zero]
      exact one_mem _
    · rw [one_smul]
      exact hx
  have hr : Multiplicative.ofAdd (((0, 1), 0) : (E × ZMod 2) × ZMod 2) ∈
      MonoidHom.eqLocus ψ₁ ψ₂ := by
    rw [rX_eq_sum hQ hpq, ofAdd_add, ofAdd_add, ofAdd_add]
    exact mul_mem (mul_mem (mul_mem (hΓ _) (hΓ _)) (hΓ _)) (hΓ _)
  refine MonoidHom.ext fun x => ?_
  obtain ⟨⟨⟨w, t⟩, s⟩, rfl⟩ : ∃ y, Multiplicative.ofAdd y = x := ⟨Multiplicative.toAdd x, rfl⟩
  have hx : Multiplicative.ofAdd (((w, t), s) : (E × ZMod 2) × ZMod 2) ∈
      MonoidHom.eqLocus ψ₁ ψ₂ := by
    rw [eq_grV_add (Q := Q) w t s, ofAdd_add, ofAdd_add]
    exact mul_mem (mul_mem (hΓ w) (hsmul _ (hΓ 0) _)) (hsmul _ hr _)
  exact hx

theorem zmod_two_isometry_identity :
    ∀ q₁ q₂ qa c₁ c₂ c₁₂ d : ZMod 2,
      q₁ + qa + c₁ + (q₂ + qa + c₂) + qa + (q₁ + q₂ + c₁₂ + qa + (c₁ + c₂)) = d → c₁₂ = d := by
  decide

theorem zmod_two_eq_add_one_of_ne : ∀ x t : ZMod 2, x ≠ t → t = x + 1 := by
  decide

theorem exists_isometry_of_graph (hQ : QuadraticMap.polarBilin Q = b) (hb : b.IsAlt)
    (hnd : b.Nondegenerate) {p q : E} (hpq : b p q = 1)
    (α β : (E × ZMod 2) × ZMod 2 →+ (E × ZMod 2) × ZMod 2) (hβα : ∀ x, β (α x) = x)
    (hαβ : ∀ x, α (β x) = x) (hα : ∀ w, ∃ w', α (grV Q w) = grV Q w')
    (hβ : ∀ w, ∃ w', β (grV Q w) = grV Q w') :
    α ((0, 1), 0) = ((0, 1), 0) ∧
      ∃ (S : E →+ E) (a : E), (∀ x y, b (S x) (S y) = b x y) ∧
        ∀ w, α (grV Q w) = grV Q (S w + a) := by
  classical
  set f : E → E := fun w => (α (grV Q w)).1.1 with hfdef
  have hf : ∀ w, α (grV Q w) = grV Q (f w) := fun w => by
    obtain ⟨w', hw'⟩ := hα w
    show α (grV Q w) = grV Q (α (grV Q w)).1.1
    rw [hw']
    rfl
  have hfsurj : ∀ u, ∃ v, f v = u := fun u => by
    obtain ⟨v, hv⟩ := hβ u
    refine ⟨v, grV_injective (Q := Q) ?_⟩
    rw [← hf, ← hv, hαβ]
  have hr := rX_eq_sum hQ hpq
  set P := (α ((0, 1), 0)).1.1 with hP
  set T := (α ((0, 1), 0)).1.2 with hT
  have hαr : α ((0, 1), 0) = ((P, T), 0) := by
    refine Prod.ext rfl ?_
    rw [hr, map_add, map_add, map_add, hf, hf, hf, hf]
    simp only [grV, Prod.snd_add]
    decide
  have hmiss : ∀ u, Q (u + P) ≠ Q u + T := by
    intro u hu
    obtain ⟨v, rfl⟩ := hfsurj u
    have h1 : α (grV Q v + ((0, 1), 0)) = grV Q (f v + P) := by
      rw [map_add, hf, hαr]
      simp only [grV, Prod.mk_add_mk, add_zero]
      rw [hu]
    obtain ⟨v', hv'⟩ := hβ (f v + P)
    have h2 : grV Q v + ((0, 1), 0) = grV Q v' := by
      rw [← hv', ← h1, hβα]
    have h3 := congrArg (fun x : (E × ZMod 2) × ZMod 2 => x.1) h2
    simp only [grV, Prod.mk_add_mk, add_zero] at h3
    obtain ⟨rfl, h4⟩ := Prod.mk.inj h3
    exact one_ne_zero (add_eq_left.1 h4)
  have hP0 : P = 0 := by
    by_contra hP0
    obtain ⟨y, hy⟩ : ∃ y, b P y ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hP0 (hnd.1 P hcon)
    have h0 := hmiss 0
    have h1 := hmiss y
    rw [zero_add, QuadraticMap.map_zero, zero_add] at h0
    rw [Q_add hQ, BinarySymplecticTransvection.symm_apply hb] at h1
    rcases BinarySymplecticTransvection.zmod_two_cases (b P y) with h | h
    · exact hy h
    · rw [h] at h1
      apply h1
      rw [zmod_two_eq_add_one_of_ne _ _ h0, add_assoc]
  have hT1 : T = 1 := by
    have h0 := hmiss 0
    rw [hP0, zero_add, QuadraticMap.map_zero, zero_add] at h0
    rcases BinarySymplecticTransvection.zmod_two_cases T with h | h
    · exact absurd h.symm h0
    · exact h
  have hαr' : α ((0, 1), 0) = ((0, 1), 0) := by
    rw [hαr, hP0, hT1]
  have hfour : ∀ w₁ w₂, f (w₁ + w₂) = f w₁ + f w₂ + f 0 ∧
      Q (f w₁) + Q (f w₂) + Q (f 0) + Q (f (w₁ + w₂)) = b w₁ w₂ := by
    intro w₁ w₂
    have e := grV_add_four hQ w₁ w₂ 0
    simp only [add_zero, map_zero] at e
    have e' : (((0, b w₁ w₂), 0) : (E × ZMod 2) × ZMod 2) = b w₁ w₂ • ((0, 1), 0) := by
      simp [Prod.smul_mk]
    rw [e'] at e
    have h := congrArg α e
    rw [ZMod.map_smul, hαr', map_add, map_add, map_add, hf, hf, hf, hf] at h
    simp only [grV, Prod.mk_add_mk, Prod.smul_mk, smul_zero, smul_eq_mul, mul_one,
      mul_zero] at h
    obtain ⟨h1, h2⟩ := Prod.mk.inj (Prod.mk.inj h).1
    refine ⟨?_, h2⟩
    have h3 : f w₁ + f w₂ + f 0 + f (w₁ + w₂) = 0 := h1
    exact (eq_of_add_eq_zero_zmod2 h3).symm
  set a := f 0 with ha
  have hS : ∀ w₁ w₂ : E, f (w₁ + w₂) + a = (f w₁ + a) + (f w₂ + a) := fun w₁ w₂ => by
    rw [(hfour w₁ w₂).1, add_assoc (f w₁ + f w₂) a a, add_self_eq_zero_zmod_two a, add_zero,
      add_add_add_comm, add_self_eq_zero_zmod_two a, add_zero]
  set S : E →+ E := AddMonoidHom.mk' (fun w => f w + a) hS with hSdef
  have hSa : ∀ w, S w + a = f w := fun w => by
    change f w + a + a = f w
    rw [add_assoc, add_self_eq_zero_zmod_two, add_zero]
  refine ⟨hαr', S, a, fun x y => ?_, fun w => by rw [hf, hSa]⟩
  have h := (hfour x y).2
  rw [← hSa x, ← hSa y, ← hSa (x + y), map_add S x y, Q_add hQ (S x + S y) a,
    Q_add hQ (S x) a, Q_add hQ (S y) a, Q_add hQ (S x) (S y), map_add b (S x) (S y),
    LinearMap.add_apply] at h
  exact zmod_two_isometry_identity _ _ _ _ _ _ _ h

end Graph

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.AlternatingEight
