module

public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.Finiteness

public section

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]

private lemma exists_nonzero_quad :
    ∀ p q r : ZMod 3, r ≠ 0 → ∃ s : ZMod 3, p + 2 * s * q + s ^ 2 * r ≠ 0 := by
  decide

private lemma three_mul_sum_le (d : ℕ) (h2 : 2 ≤ d) (h4 : d ≤ 4) :
    3 * (3 ^ d + 3 ^ (6 - d)) ≤ 270 := by
  interval_cases d <;> norm_num

theorem fg_card_le_three_mul_nonisotropic (B : LinearMap.BilinForm (ZMod 3) V)
    (hsymm : ∀ x y, B x y = B y x) {u : V} (hu : B u u ≠ 0) :
    Nat.card V ≤ 3 * Nat.card {v : V // B v v ≠ 0} := by
  haveI : Finite V := Module.finite_of_finite (ZMod 3)
  have hchoose : ∀ w : V, ∃ s : ZMod 3, B (w + s • u) (w + s • u) ≠ 0 := by
    intro w
    have hquad : ∀ s : ZMod 3,
        B (w + s • u) (w + s • u) = B w w + 2 * s * B w u + s ^ 2 * B u u := by
      intro s
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
      rw [hsymm u w]
      ring
    obtain ⟨s, hs⟩ := exists_nonzero_quad (B w w) (B w u) (B u u) hu
    exact ⟨s, by rw [hquad s]; exact hs⟩
  let s : V → ZMod 3 := fun w => Classical.choose (hchoose w)
  have hs : ∀ w, B (w + s w • u) (w + s w • u) ≠ 0 := fun w => Classical.choose_spec (hchoose w)
  let f : V → {v : V // B v v ≠ 0} × ZMod 3 :=
    fun w => (⟨w + s w • u, hs w⟩, s w)
  have hf : Function.Injective f := by
    intro a b hab
    have h1 : s a = s b := congrArg Prod.snd hab
    have h2 : (⟨a + s a • u, hs a⟩ : {v : V // B v v ≠ 0}) = ⟨b + s b • u, hs b⟩ :=
      congrArg Prod.fst hab
    have h3 : a + s a • u = b + s b • u := Subtype.ext_iff.mp h2
    rw [h1] at h3
    exact add_right_cancel h3
  have hcard := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod, Nat.card_zmod] at hcard
  simpa [Nat.mul_comm] using hcard

theorem fg_exists_nonisotropic [Nontrivial V] (B : LinearMap.BilinForm (ZMod 3) V)
    (hB : B.Nondegenerate) (hsymm : ∀ x y, B x y = B y x) : ∃ u : V, B u u ≠ 0 := by
  by_contra h
  push Not at h
  have hzero : ∀ x y : V, B x y = 0 := by
    intro x y
    have hxy : B (x + y) (x + y) = 0 := h (x + y)
    have hexp : B (x + y) (x + y) = 2 * B x y := by
      simp only [map_add, LinearMap.add_apply]
      rw [hsymm y x, h x, h y]
      ring
    rw [hexp] at hxy
    have h2 : (2 : ZMod 3) ≠ 0 := by decide
    exact (mul_eq_zero.mp hxy).resolve_left h2
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  exact hv (hB.1 v (fun y => hzero v y))

theorem fg_exists_nonisotropic_not_mem (B : LinearMap.BilinForm (ZMod 3) V)
    (hB : B.Nondegenerate) (hsymm : ∀ x y, B x y = B y x)
    (hdim : Module.finrank (ZMod 3) V = 6) (Y : Submodule (ZMod 3) V)
    (h2 : 2 ≤ Module.finrank (ZMod 3) Y) (h4 : Module.finrank (ZMod 3) Y ≤ 4) :
    ∃ v : V, B v v ≠ 0 ∧ v ∉ Y ∧ v ∉ B.orthogonal Y := by
  classical
  by_contra h
  have hcover : ∀ v : V, B v v ≠ 0 → v ∈ Y ∨ v ∈ B.orthogonal Y := by
    intro v hv
    by_contra hc
    push Not at hc
    exact h ⟨v, hv, hc.1, hc.2⟩
  haveI : Nontrivial V :=
    Module.nontrivial_of_finrank_pos (R := ZMod 3) (by rw [hdim]; norm_num)
  haveI : Finite V := Module.finite_of_finite (ZMod 3)
  obtain ⟨u, hu⟩ := fg_exists_nonisotropic B hB hsymm
  have hcard_le := fg_card_le_three_mul_nonisotropic B hsymm hu
  let f : {v : V // B v v ≠ 0} → Y ⊕ B.orthogonal Y := fun w =>
    if hw : (w : V) ∈ Y then Sum.inl ⟨w, hw⟩
    else Sum.inr ⟨w, (hcover w w.2).resolve_left hw⟩
  have hgf : ∀ w : {v : V // B v v ≠ 0},
      Sum.elim (fun x : Y => (x : V)) (fun x : B.orthogonal Y => (x : V)) (f w) = (w : V) := by
    intro w
    dsimp only [f]
    split_ifs with hw <;> rfl
  have hf : Function.Injective f := by
    intro a b hab
    have hval : (a : V) = (b : V) := by
      have hcongr := congrArg
        (Sum.elim (fun x : Y => (x : V)) (fun x : B.orthogonal Y => (x : V))) hab
      simpa only [hgf a, hgf b] using hcongr
    exact Subtype.ext hval
  have hbound : Nat.card {v : V // B v v ≠ 0} ≤ Nat.card Y + Nat.card (B.orthogonal Y) := by
    have hle := Nat.card_le_card_of_injective f hf
    rwa [Nat.card_sum] at hle
  have hcardV : Nat.card V = 3 ^ 6 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 3), Nat.card_zmod, hdim]
  have hcardY : Nat.card Y = 3 ^ Module.finrank (ZMod 3) Y := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 3), Nat.card_zmod]
  have hcardO : Nat.card (B.orthogonal Y) = 3 ^ Module.finrank (ZMod 3) (B.orthogonal Y) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 3), Nat.card_zmod]
  have hfinrankO : Module.finrank (ZMod 3) (B.orthogonal Y) =
      6 - Module.finrank (ZMod 3) Y := by
    rw [LinearMap.BilinForm.finrank_orthogonal hB Y, hdim]
  have hmain : 3 ^ 6 ≤
      3 * (3 ^ Module.finrank (ZMod 3) Y + 3 ^ (6 - Module.finrank (ZMod 3) Y)) := by
    calc
      3 ^ 6 = Nat.card V := hcardV.symm
      _ ≤ 3 * Nat.card {v : V // B v v ≠ 0} := hcard_le
      _ ≤ 3 * (Nat.card Y + Nat.card (B.orthogonal Y)) :=
            Nat.mul_le_mul_left 3 hbound
      _ = 3 * (3 ^ Module.finrank (ZMod 3) Y +
            3 ^ Module.finrank (ZMod 3) (B.orthogonal Y)) := by rw [hcardY, hcardO]
      _ = 3 * (3 ^ Module.finrank (ZMod 3) Y + 3 ^ (6 - Module.finrank (ZMod 3) Y)) := by
            rw [hfinrankO]
  have h270 := three_mul_sum_le (Module.finrank (ZMod 3) Y) h2 h4
  have hle : 3 ^ 6 ≤ 270 := le_trans hmain h270
  norm_num at hle

end CFSG.OddStandard.SmallF3.Omega
