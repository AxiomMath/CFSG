module

public import CFSG.CGT.PushingUpLit.BHS.NaturalDefs

public section

namespace CFSG.CGT.PushingUpLit.BHS

open Matrix

variable {V : Type} [CommGroup V]

theorem isSLNatSection_one [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {G : Subgroup (MulAut V)}
    (hVcard : Nat.card V = 4) (hG : Nat.card G = 6) : IsSLNatSection G ⊤ ⊥ 1 := by
  classical
  set K := GaloisField 2 1 with hK
  have : Fintype K := Fintype.ofFinite K
  have hKcard : Nat.card K = 2 := by simpa using GaloisField.card 2 1 one_ne_zero
  have hKcard' : Fintype.card K = 2 := by rwa [← Nat.card_eq_fintype_card]
  have hK01 : ∀ c : K, c = 0 ∨ c = 1 := by
    intro c
    by_contra hc
    push Not at hc
    have h3 : ({0, 1, c} : Finset K).card = 3 :=
      Finset.card_eq_three.2 ⟨0, 1, c, zero_ne_one, hc.1.symm, hc.2.symm, rfl⟩
    have : ({0, 1, c} : Finset K).card ≤ Fintype.card K := Finset.card_le_univ _
    omega
  have hmod : Module (ZMod 2) (Additive V) := AddCommGroup.zmodModule (n := 2) (fun v => by
    rw [two_nsmul]
    have := hV (Additive.toMul v)
    rw [pow_two] at this
    exact this)
  have hdim : ∀ {M : Type} [AddCommGroup M] [Module (ZMod 2) M] [Finite M],
      Nat.card M = 4 → Module.finrank (ZMod 2) M = 2 := by
    intro M _ _ _ hM
    have : Module.Finite (ZMod 2) M := Module.Finite.of_finite
    have h1 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := M)
    rw [Nat.card_zmod, hM] at h1
    exact Nat.pow_right_injective (le_refl 2)
      (by show 2 ^ Module.finrank (ZMod 2) M = 2 ^ 2; rw [← h1])
  have hKfun : Nat.card (Fin 2 → K) = 4 := by
    rw [Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hKcard]
    norm_num
  have hVadd : Nat.card (Additive V) = 4 := hVcard
  have hfin : Module.finrank (ZMod 2) (Additive V) = Module.finrank (ZMod 2) (Fin 2 → K) := by
    rw [hdim hVadd, hdim hKfun]
  have : Module.Finite (ZMod 2) (Additive V) := Module.Finite.of_finite
  have : Module.Finite (ZMod 2) (Fin 2 → K) := Module.Finite.of_finite
  let b : Additive V ≃ₗ[ZMod 2] (Fin 2 → K) := LinearEquiv.ofFinrankEq _ _ hfin
  let L : MulAut V → ((Fin 2 → K) →ₗ[K] (Fin 2 → K)) := fun g =>
    { toFun := fun w => b (MulEquiv.toAdditive g (b.symm w))
      map_add' := fun w w' => by simp [map_add]
      map_smul' := fun c w => by
        rcases hK01 c with rfl | rfl
        · simp
        · simp }
  have hL_apply : ∀ g w, L g w = b (MulEquiv.toAdditive g (b.symm w)) := fun _ _ => rfl
  have hL_mul : ∀ g h, L (g * h) = (L g).comp (L h) := by
    intro g h
    refine LinearMap.ext fun w => ?_
    rw [LinearMap.comp_apply, hL_apply, hL_apply, hL_apply, LinearEquiv.symm_apply_apply]
    rfl
  have hL_one : L 1 = LinearMap.id := by
    refine LinearMap.ext fun w => ?_
    rw [hL_apply, LinearMap.id_apply]
    show b (b.symm w) = w
    exact b.apply_symm_apply w
  have hdet : ∀ g : MulAut V, (LinearMap.toMatrix' (L g)).det = 1 := by
    intro g
    have h1 : LinearMap.toMatrix' (L g) * LinearMap.toMatrix' (L g⁻¹) = 1 := by
      rw [← LinearMap.toMatrix'_comp, ← hL_mul, mul_inv_cancel, hL_one, LinearMap.toMatrix'_id]
    have hu : IsUnit (LinearMap.toMatrix' (L g)).det := Matrix.isUnit_det_of_right_inverse h1
    rcases hK01 (LinearMap.toMatrix' (L g)).det with h0 | h0
    · exact absurd h0 hu.ne_zero
    · exact h0
  let ρ : ↥G →* SpecialLinearGroup (Fin 2) K :=
    MonoidHom.mk' (fun g => ⟨LinearMap.toMatrix' (L (g : MulAut V)), hdet g⟩) (by
      intro g h
      apply Subtype.ext
      show LinearMap.toMatrix' (L ((g : MulAut V) * (h : MulAut V))) =
        LinearMap.toMatrix' (L (g : MulAut V)) * LinearMap.toMatrix' (L (h : MulAut V))
      rw [hL_mul, LinearMap.toMatrix'_comp])
  have hρ_apply : ∀ g : ↥G, (ρ g : Matrix (Fin 2) (Fin 2) K) =
      LinearMap.toMatrix' (L (g : MulAut V)) := fun _ => rfl
  have hρinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have h1 : LinearMap.toMatrix' (L (g : MulAut V)) = 1 := by
      rw [← hρ_apply, hg]
      rfl
    have h2 : L (g : MulAut V) = LinearMap.id := by
      rw [← LinearMap.toMatrix'_id (R := K) (n := Fin 2)] at h1
      exact LinearMap.toMatrix'.injective h1
    apply Subtype.ext
    apply MulEquiv.ext
    intro v
    have h3 := congrArg (fun f => b.symm (f (b (Additive.ofMul v)))) h2
    simp [hL_apply] at h3
    exact h3
  have hcardSL : Nat.card (SpecialLinearGroup (Fin 2) K) = 6 := by
    rw [Matrix.card_SL_field (𝔽 := K) 2, hKcard']
    decide
  have hbij : Function.Bijective ρ := by
    rw [Nat.bijective_iff_injective_and_card]
    exact ⟨hρinj, by rw [hG, hcardSL]⟩
  let θ : ↥G ≃* SpecialLinearGroup (Fin 2) K := MulEquiv.ofBijective ρ hbij
  let β : ↥(⊤ : Subgroup V) →* Multiplicative (Fin 2 → K) :=
    { toFun := fun p => Multiplicative.ofAdd (b (Additive.ofMul p.1))
      map_one' := by
        show Multiplicative.ofAdd (b (Additive.ofMul (1 : V))) = 1
        have : Additive.ofMul (1 : V) = 0 := rfl
        rw [this, map_zero]
        rfl
      map_mul' := by
        intro p q
        show Multiplicative.ofAdd (b (Additive.ofMul (p.1 * q.1))) =
          Multiplicative.ofAdd (b (Additive.ofMul p.1)) *
            Multiplicative.ofAdd (b (Additive.ofMul q.1))
        have : Additive.ofMul (p.1 * q.1) = Additive.ofMul p.1 + Additive.ofMul q.1 := rfl
        rw [this, map_add]
        rfl }
  refine ⟨fun _ _ _ _ => trivial, θ, β, ?_, ?_, ?_⟩
  · intro y
    refine ⟨⟨Additive.toMul (b.symm (Multiplicative.toAdd y)), Subgroup.mem_top _⟩, ?_⟩
    show Multiplicative.ofAdd (b (Additive.ofMul (Additive.toMul
      (b.symm (Multiplicative.toAdd y))))) = y
    simp
  · ext p
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_bot]
    show Multiplicative.ofAdd (b (Additive.ofMul p.1)) = 1 ↔ p.1 = 1
    constructor
    · intro h0
      have : b (Additive.ofMul p.1) = 0 := h0
      have h1 : Additive.ofMul p.1 = 0 := by
        have := congrArg b.symm this
        simpa using this
      exact h1
    · intro h0
      rw [h0]
      have : Additive.ofMul (1 : V) = 0 := rfl
      rw [this, map_zero]
      rfl
  · intro x p hp
    have hθx : (θ x : Matrix (Fin 2) (Fin 2) K) = LinearMap.toMatrix' (L (x : MulAut V)) := rfl
    show Multiplicative.ofAdd (b (Additive.ofMul ((x : MulAut V) p.1))) =
      Multiplicative.ofAdd ((θ x : Matrix (Fin 2) (Fin 2) K).mulVec
        (b (Additive.ofMul p.1)))
    rw [hθx, ← Matrix.toLin'_apply, Matrix.toLin'_toMatrix', hL_apply]
    simp

end CFSG.CGT.PushingUpLit.BHS
