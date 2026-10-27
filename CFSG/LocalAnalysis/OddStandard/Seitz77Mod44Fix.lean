module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

public section

namespace CFSG.OddStandard.Seitz77

namespace Mod44

abbrev Mat8 : Type := Matrix (Fin 8) (Fin 8) (ZMod 2)

abbrev Vec8 : Type := Fin 8 → ZMod 2

open Matrix

def fixSp (A : Mat8) : Submodule (ZMod 2) Vec8 :=
  LinearMap.ker (Matrix.mulVecLin (A - 1))

theorem mem_fixSp {A : Mat8} {v : Vec8} : v ∈ fixSp A ↔ A *ᵥ v = v := by
  simp [fixSp, sub_eq_zero]

theorem fixSp_inf_eq_bot {A B : Mat8} (h : ∀ v, (A * B) *ᵥ v = v → v = 0) :
    fixSp A ⊓ fixSp B = ⊥ := by
  rw [eq_bot_iff]
  rintro v ⟨hA, hB⟩
  rw [Submodule.mem_bot]
  apply h
  rw [← Matrix.mulVec_mulVec, mem_fixSp.mp hB, mem_fixSp.mp hA]

theorem mulVec_mem_fixSp {A X : Mat8} (hXA : X * A = A * X) {v : Vec8} (hv : v ∈ fixSp A) :
    X *ᵥ v ∈ fixSp A := by
  rw [mem_fixSp, Matrix.mulVec_mulVec, ← hXA, ← Matrix.mulVec_mulVec, mem_fixSp.mp hv]

theorem map_fixSp {A B T : Mat8} (hT : T * T = 1) (hAB : T * A * T = B) :
    (fixSp A).map (Matrix.mulVecLin T) = fixSp B := by
  have key : ∀ {A B : Mat8}, T * A * T = B → ∀ v ∈ fixSp A, T *ᵥ v ∈ fixSp B := by
    intro A B hAB v hv
    have h1 : B * T = T * A := by
      rw [← hAB, mul_assoc, mul_assoc, hT, mul_one]
    rw [mem_fixSp] at hv ⊢
    rw [Matrix.mulVec_mulVec, h1, ← Matrix.mulVec_mulVec, hv]
  have hBA : T * B * T = A := by
    rw [← hAB, ← mul_assoc, ← mul_assoc, hT, one_mul, mul_assoc, hT, mul_one]
  apply le_antisymm
  · rintro _ ⟨v, hv, rfl⟩
    exact key hAB v hv
  · intro v hv
    refine ⟨T *ᵥ v, key hBA v hv, ?_⟩
    simp [Matrix.mulVec_mulVec, hT]

theorem finrank_fixSp_eq {A B T : Mat8} (hT : T * T = 1) (hAB : T * A * T = B) :
    Module.finrank (ZMod 2) (fixSp A) = Module.finrank (ZMod 2) (fixSp B) := by
  have hinj : Function.Injective (Matrix.mulVecLin T) := by
    intro v w h
    have h' : T *ᵥ v = T *ᵥ w := h
    have := congrArg (fun u => T *ᵥ u) h'
    simpa [Matrix.mulVec_mulVec, hT] using this
  rw [← map_fixSp hT hAB]
  exact LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj (fixSp A))

theorem add_self_vec (x : Vec8) : x + x = 0 := by
  funext i
  exact CharTwo.add_self_eq_zero (x i)

theorem eq_of_add_eq_zero_vec {x y : Vec8} (h : x + y = 0) : x = y := by
  have h2 : x + y + y = y := by rw [h, zero_add]
  rw [add_assoc, add_self_vec, add_zero] at h2
  exact h2

theorem finrank_add_le_eight (F G : Submodule (ZMod 2) Vec8) (h : F ⊓ G = ⊥) :
    Module.finrank (ZMod 2) F + Module.finrank (ZMod 2) G ≤ 8 := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq F G
  rw [h, finrank_bot, add_zero] at h1
  have h2 : Module.finrank (ZMod 2) (F ⊔ G : Submodule (ZMod 2) Vec8) ≤ 8 := by
    calc _ ≤ Module.finrank (ZMod 2) Vec8 := Submodule.finrank_le _
      _ = 8 := Module.finrank_fin_fun (ZMod 2)
  omega

theorem sup_eq_top_of_finrank {F G : Submodule (ZMod 2) Vec8} (h : F ⊓ G = ⊥)
    (hF : Module.finrank (ZMod 2) F = 4) (hG : Module.finrank (ZMod 2) G = 4) : F ⊔ G = ⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  have h1 : Module.finrank (ZMod 2) (F ⊔ G : Submodule (ZMod 2) Vec8) +
      Module.finrank (ZMod 2) (F ⊓ G : Submodule (ZMod 2) Vec8) =
      Module.finrank (ZMod 2) F + Module.finrank (ZMod 2) G :=
    Submodule.finrank_sup_add_finrank_inf_eq F G
  rw [h, finrank_bot, add_zero, hF, hG] at h1
  rw [h1]
  exact (Module.finrank_fin_fun (ZMod 2)).symm

theorem mulVec_cube {A : Mat8} (hA : A ^ 3 = 1) (v : Vec8) :
    A *ᵥ (A *ᵥ (A *ᵥ v)) = v := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  have : A * A * A = 1 := by rw [← hA, pow_succ, pow_two]
  rw [this, Matrix.one_mulVec]

theorem sum_eq_zero_of_fpf {A : Mat8} (hA : A ^ 3 = 1) (hf : ∀ v, A *ᵥ v = v → v = 0)
    (v : Vec8) : v + A *ᵥ v + A *ᵥ (A *ᵥ v) = 0 := by
  apply hf
  rw [Matrix.mulVec_add, Matrix.mulVec_add, mulVec_cube hA]
  abel

theorem eq_of_fpf {A B : Mat8} (hA : A ^ 3 = 1) (hB : B ^ 3 = 1) (hAB : A * B = B * A)
    (hfA : ∀ v, A *ᵥ v = v → v = 0) (hfB : ∀ v, B *ᵥ v = v → v = 0)
    (hfAB : ∀ v, (A * B) *ᵥ v = v → v = 0) : A = B := by
  have hAB3 : (A * B) ^ 3 = 1 := by
    rw [Commute.mul_pow (show Commute A B from hAB), hA, hB, one_mul]
  have rA := sum_eq_zero_of_fpf hA hfA
  have rB := sum_eq_zero_of_fpf hB hfB
  have rC := sum_eq_zero_of_fpf hAB3 hfAB
  rw [Matrix.ext_iff_mulVec]
  intro v
  have eA : ∀ w, A *ᵥ (A *ᵥ w) = w + A *ᵥ w := fun w => (eq_of_add_eq_zero_vec (rA w)).symm
  have eB : B *ᵥ (B *ᵥ v) = v + B *ᵥ v := (eq_of_add_eq_zero_vec (rB v)).symm
  have hsq : (A * B) *ᵥ ((A * B) *ᵥ v) = A *ᵥ (A *ᵥ (B *ᵥ (B *ᵥ v))) := by
    have h1 : A * B * (A * B) = A * (A * (B * B)) := by
      calc A * B * (A * B) = A * (B * A) * B := by simp only [mul_assoc]
        _ = A * (A * B) * B := by rw [← hAB]
        _ = A * (A * (B * B)) := by simp only [mul_assoc]
    rw [Matrix.mulVec_mulVec, h1]
    simp only [Matrix.mulVec_mulVec]
  have h2 : (A * B) *ᵥ ((A * B) *ᵥ v) = (v + A *ᵥ v) + (B *ᵥ v + A *ᵥ (B *ᵥ v)) := by
    rw [hsq, eB, Matrix.mulVec_add, Matrix.mulVec_add, eA v, eA (B *ᵥ v)]
  have h3 : (A * B) *ᵥ v = A *ᵥ (B *ᵥ v) := (Matrix.mulVec_mulVec v A B).symm
  have hv := rC v
  rw [h2, h3] at hv
  apply eq_of_add_eq_zero_vec
  calc A *ᵥ v + B *ᵥ v
      = (v + A *ᵥ (B *ᵥ v) + ((v + A *ᵥ v) + (B *ᵥ v + A *ᵥ (B *ᵥ v)))) - (v + v) -
          (A *ᵥ (B *ᵥ v) + A *ᵥ (B *ᵥ v)) := by abel
    _ = 0 := by rw [hv, add_self_vec, add_self_vec]; simp

theorem invariant_of_comm {A B X : Mat8} (hAB : A * B = B * A) (hXA : X * A = A * X)
    (hsup : fixSp A ⊔ fixSp B = ⊤)
    (hA4 : Module.finrank (ZMod 2) (fixSp A) = 4)
    (hB4 : Module.finrank (ZMod 2) (fixSp B) = 4) :
    ∀ v ∈ fixSp B, X *ᵥ v ∈ fixSp B := by
  have hrange_le : LinearMap.range (Matrix.mulVecLin (A - 1)) ≤ fixSp B := by
    rintro _ ⟨w, rfl⟩
    have hw : w ∈ fixSp A ⊔ fixSp B := hsup ▸ Submodule.mem_top
    obtain ⟨g, hg, f, hf, rfl⟩ := Submodule.mem_sup.mp hw
    have hg0 : (A - 1) *ᵥ g = 0 := by
      rw [Matrix.sub_mulVec, mem_fixSp.mp hg, Matrix.one_mulVec, sub_self]
    have hAf : A *ᵥ f ∈ fixSp B := mulVec_mem_fixSp hAB hf
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_add, hg0, zero_add, Matrix.sub_mulVec,
      Matrix.one_mulVec]
    exact Submodule.sub_mem _ hAf hf
  have hrange_eq : LinearMap.range (Matrix.mulVecLin (A - 1)) = fixSp B := by
    apply Submodule.eq_of_le_of_finrank_eq hrange_le
    have h1 := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin (A - 1))
    have h2 : Module.finrank (ZMod 2) (Fin 8 → ZMod 2) = 8 := Module.finrank_fin_fun (ZMod 2)
    have h3 : Module.finrank (ZMod 2) (LinearMap.ker (Matrix.mulVecLin (A - 1))) = 4 := hA4
    have h4 : Module.finrank (ZMod 2) (LinearMap.range (Matrix.mulVecLin (A - 1))) = 4 := by
      omega
    exact h4.trans hB4.symm
  have hcomm : (A - 1) * X = X * (A - 1) := by
    rw [sub_mul, mul_sub, one_mul, mul_one, hXA]
  intro v hv
  rw [← hrange_eq] at hv ⊢
  obtain ⟨u, rfl⟩ := hv
  refine ⟨X *ᵥ u, ?_⟩
  rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    hcomm]

theorem le_fixSp_of_pow_five_eq_one (g : Mat8) (hg : g ^ 5 = 1) (Y : Submodule (ZMod 2) Vec8)
    (hY : ∀ v ∈ Y, g *ᵥ v ∈ Y) (hd : Module.finrank (ZMod 2) Y ≤ 3) : Y ≤ fixSp g := by
  classical
  let f : Function.End Y := fun y => ⟨g *ᵥ (y : Vec8), hY y y.prop⟩
  have hf : ∀ (n : ℕ) (y : Y), ((f^[n] y : Y) : Vec8) = (g ^ n) *ᵥ (y : Vec8) := by
    intro n
    induction n with
    | zero => intro y; rw [Function.iterate_zero_apply, pow_zero, Matrix.one_mulVec]
    | succ n ih =>
      intro y
      rw [Function.iterate_succ_apply', pow_succ', ← Matrix.mulVec_mulVec, ← ih]
  have hf5 : f ^ 5 ^ 1 = 1 := by
    funext y
    apply Subtype.ext
    change ((f^[5] y : Y) : Vec8) = (y : Vec8)
    rw [hf, hg, Matrix.one_mulVec]
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hmod := Equiv.Perm.card_fixedPoints_modEq hf5
  let Z : Submodule (ZMod 2) Y := (fixSp g).comap Y.subtype
  have hZ : Function.fixedPoints f = (Z : Set Y) := by
    ext y
    simp only [SetLike.mem_coe, Z, Submodule.mem_comap, Submodule.subtype_apply, mem_fixSp]
    constructor
    · intro h
      exact congrArg (fun z : Y => (z : Vec8)) h
    · intro h
      exact Subtype.ext h
  have h1 : Fintype.card Y = 2 ^ Module.finrank (ZMod 2) Y := by
    rw [Fintype.card_eq_nat_card, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have h2 : Fintype.card (Function.fixedPoints f) = 2 ^ Module.finrank (ZMod 2) Z := by
    rw [Fintype.card_eq_nat_card, hZ]
    show Nat.card Z = _
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  rw [h1, h2] at hmod
  have hle : Module.finrank (ZMod 2) Z ≤ Module.finrank (ZMod 2) Y := Submodule.finrank_le Z
  have heq : Module.finrank (ZMod 2) Z = Module.finrank (ZMod 2) Y := by
    generalize Module.finrank (ZMod 2) Z = e at hle hmod ⊢
    generalize Module.finrank (ZMod 2) Y = d at hle hd hmod ⊢
    interval_cases d <;> interval_cases e <;> simp_all [Nat.ModEq]
  have hZtop : Z = ⊤ := Submodule.eq_top_of_finrank_eq heq
  intro y hy
  have : (⟨y, hy⟩ : Y) ∈ Z := hZtop ▸ Submodule.mem_top
  exact this

end Mod44

end CFSG.OddStandard.Seitz77
