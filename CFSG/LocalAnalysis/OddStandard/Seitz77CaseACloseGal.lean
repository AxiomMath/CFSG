module

public import Mathlib.FieldTheory.Finite.GaloisField

public section

namespace CFSG.OddStandard.Seitz77

section Gal

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem ringAut_isCyclic_and_card (hF : Nat.card F = 16) :
    IsCyclic (RingAut F) ∧ Nat.card (RingAut F) = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  have : Fintype F := Fintype.ofFinite F
  let e : RingAut F ≃* (F ≃ₐ[ZMod 2] F) :=
    { toFun := fun f => AlgEquiv.ofRingEquiv (f := f) fun r =>
        RingHom.congr_fun (RingHom.ext_zmod ((f : F →+* F).comp (algebraMap (ZMod 2) F))
          (algebraMap (ZMod 2) F)) r
      invFun := fun g => g.toRingEquiv
      left_inv := fun f => rfl
      right_inv := fun g => rfl
      map_mul' := fun f g => rfl }
  have h2 : Nat.card (F ≃ₐ[ZMod 2] F) = Module.finrank (ZMod 2) F :=
    IsGalois.card_aut_eq_finrank (ZMod 2) F
  have h3 : Nat.card F = 2 ^ Module.finrank (ZMod 2) F := by
    have := Module.card_eq_pow_finrank (K := ZMod 2) (V := F)
    simpa [Nat.card_eq_fintype_card] using this
  have h4 : (2 : ℕ) ^ Module.finrank (ZMod 2) F = 2 ^ 4 := by
    rw [← h3, hF]
    norm_num
  have h5 := Nat.pow_right_injective (le_refl 2) h4
  refine ⟨isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective, ?_⟩
  rw [Nat.card_congr e.toEquiv, h2, h5]

theorem ringAut_pow_four (hF : Nat.card F = 16) (a : RingAut F) : a ^ 4 = 1 := by
  have h := (ringAut_isCyclic_and_card hF).2
  rw [← h]
  exact pow_card_eq_one'

omit [CharP F 2] in
theorem ringAut_finite : Finite (RingAut F) :=
  Finite.of_injective (fun f : RingAut F => (f : F → F)) DFunLike.coe_injective

theorem ringAut_card_sq_eq_one_le (hF : Nat.card F = 16) :
    Set.ncard {a : RingAut F | a * a = 1} ≤ 2 := by
  classical
  have hc := (ringAut_isCyclic_and_card hF).1
  have hfin : Finite (RingAut F) := ringAut_finite
  have hfint : Fintype (RingAut F) := Fintype.ofFinite _
  have h := IsCyclic.card_pow_eq_one_le (α := RingAut F) (n := 2) (by norm_num)
  rw [Set.ncard_eq_toFinset_card']
  simpa [sq] using h

theorem ringAut_eq_of_sq_eq_one (hF : Nat.card F = 16) {a b : RingAut F} (ha : a * a = 1)
    (hb : b * b = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1) : a = b := by
  by_contra hab
  have hfin : Finite (RingAut F) := ringAut_finite
  have hsub : ({1, a, b} : Set (RingAut F)) ⊆ {x : RingAut F | x * x = 1} := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with h | h | h
    · show x * x = 1
      rw [h, mul_one]
    · show x * x = 1
      rw [h]
      exact ha
    · show x * x = 1
      rw [h]
      exact hb
  have h3 : Set.ncard ({1, a, b} : Set (RingAut F)) = 3 :=
    Set.ncard_eq_three.mpr ⟨1, a, b, ha1.symm, hb1.symm, hab, rfl⟩
  have h1 := Set.ncard_le_ncard hsub
  have h2 := ringAut_card_sq_eq_one_le hF
  omega

theorem ringAut_sq_eq_of_sq_ne_one (hF : Nat.card F = 16) {a b : RingAut F} (ha : a * a ≠ 1)
    (hb : b * b = 1) (hb1 : b ≠ 1) : a * a = b := by
  refine ringAut_eq_of_sq_eq_one hF ?_ hb ha hb1
  calc a * a * (a * a) = a ^ (2 + 2) := by rw [pow_add, sq]
    _ = 1 := ringAut_pow_four hF a

omit [CharP F 2] in
theorem card_fix_semilinear_le (hF : Nat.card F = 16) (τ : RingAut F) (hτ : τ ≠ 1) (l : F) :
    Nat.card {b : F // l * τ b = b} ≤ 4 := by
  obtain ⟨K, hK⟩ : ∃ K : Subfield F, ∀ x : F, x ∈ K ↔ τ x = x :=
    ⟨RingHom.eqLocusField (τ : F →+* F) (RingHom.id F), fun x => Iff.rfl⟩
  have hKle : Nat.card K ≤ 4 := by
    have hcard : Nat.card F = Nat.card K ^ Module.finrank K F :=
      Module.natCard_eq_pow_finrank
    have hpos : 0 < Nat.card K := Nat.card_pos
    have hn1 : Module.finrank K F ≠ 1 := by
      intro h1
      rw [h1, pow_one] at hcard
      have hbij : Function.Bijective (Subtype.val : K → F) :=
        Subtype.val_injective.bijective_of_nat_card_le hcard.le
      refine hτ (RingEquiv.ext fun x => ?_)
      obtain ⟨y, rfl⟩ := hbij.2 x
      exact (hK y.1).1 y.2
    have hn0 : Module.finrank K F ≠ 0 := by
      intro h0
      rw [h0, pow_zero, hF] at hcard
      omega
    have hn2 : 2 ≤ Module.finrank K F := by omega
    have hsq : Nat.card K ^ 2 ≤ 16 := by
      calc Nat.card K ^ 2 ≤ Nat.card K ^ Module.finrank K F := Nat.pow_le_pow_right hpos hn2
        _ = 16 := by rw [← hcard, hF]
    by_contra hlt
    have h5 : 5 ≤ Nat.card K := by omega
    have h25 := Nat.pow_le_pow_left h5 2
    omega
  have hinj : ∃ f : {b : F // l * τ b = b} → K, Function.Injective f := by
    by_cases h : ∃ b₀ : F, b₀ ≠ 0 ∧ l * τ b₀ = b₀
    · obtain ⟨b₀, hb₀, hfix₀⟩ := h
      have hτb₀ : τ b₀ ≠ 0 := (map_ne_zero τ).2 hb₀
      have hmem : ∀ b : {b : F // l * τ b = b}, b.1 / b₀ ∈ K := by
        intro b
        rw [hK, map_div₀, div_eq_div_iff hτb₀ hb₀]
        calc τ b.1 * b₀ = τ b.1 * (l * τ b₀) := by rw [hfix₀]
          _ = (l * τ b.1) * τ b₀ := by ring
          _ = b.1 * τ b₀ := by rw [b.2]
      refine ⟨fun b => ⟨b.1 / b₀, hmem b⟩, fun b₁ b₂ hb => ?_⟩
      exact Subtype.ext ((div_left_inj' hb₀).1 (congrArg Subtype.val hb))
    · have h0 : ∀ b : {b : F // l * τ b = b}, b.1 = 0 := fun b =>
        by_contra fun hne => h ⟨b.1, hne, b.2⟩
      exact ⟨fun _ => 1, fun b₁ b₂ _ => Subtype.ext ((h0 b₁).trans (h0 b₂).symm)⟩
  obtain ⟨f, hf⟩ := hinj
  exact (Nat.card_le_card_of_injective f hf).trans hKle

end Gal

end CFSG.OddStandard.Seitz77
