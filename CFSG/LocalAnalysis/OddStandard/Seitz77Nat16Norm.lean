module

public import CFSG.LocalAnalysis.OddStandard.Seitz77Nat16Natural

public section

namespace CFSG.OddStandard.Seitz77

namespace Nat16

open Matrix MatrixGroups

variable {F : Type*} [Field F]

section Schur

variable (hF : Nat.card F = 16) {ζ : F} (hζ : ζ ^ 4 = ζ + 1)

include hF hζ

theorem schur_coords (S : (F × F) →+ (F × F))
    (hH : ∀ v : F × F, S (ζ * v.1, ζ⁻¹ * v.2) = (ζ * (S v).1, ζ⁻¹ * (S v).2))
    (hU : ∀ v : F × F, S (v.1 + v.2, v.2) = ((S v).1 + (S v).2, (S v).2)) :
    ∃ μ : F, ∀ v, S v = (μ * v.1, μ * v.2) := by
  have hord : orderOf ζ = 15 := Weights16.orderOf_eq_fifteen_of_pow_four hF hζ
  have hinv14 : ζ⁻¹ = ζ ^ 14 := Weights16.inv_eq_pow_fourteen hord
  have hz := zeta_ne_zero hζ
  have hdec : ∀ v : F × F, S v = S (v.1, 0) + S (0, v.2) := by
    intro v
    rw [← map_add]
    congr 1
    ext <;> simp
  have hp_add : ∀ x x', (S (x + x', 0)).1 = (S (x, 0)).1 + (S (x', 0)).1 := by
    intro x x'
    have : (x + x', (0 : F)) = (x, 0) + (x', 0) := by simp
    rw [this, map_add]; rfl
  have hq_add : ∀ x x', (S (x + x', 0)).2 = (S (x, 0)).2 + (S (x', 0)).2 := by
    intro x x'
    have : (x + x', (0 : F)) = (x, 0) + (x', 0) := by simp
    rw [this, map_add]; rfl
  have hs_add : ∀ y y', (S (0, y + y')).1 = (S (0, y)).1 + (S (0, y')).1 := by
    intro y y'
    have : ((0 : F), y + y') = (0, y) + (0, y') := by simp
    rw [this, map_add]; rfl
  have ht_add : ∀ y y', (S (0, y + y')).2 = (S (0, y)).2 + (S (0, y')).2 := by
    intro y y'
    have : ((0 : F), y + y') = (0, y) + (0, y') := by simp
    rw [this, map_add]; rfl
  have hx : ∀ x, S (ζ * x, 0) = (ζ * (S (x, 0)).1, ζ⁻¹ * (S (x, 0)).2) := by
    intro x
    have := hH (x, 0)
    simpa using this
  have hy : ∀ y, S (0, ζ⁻¹ * y) = (ζ * (S (0, y)).1, ζ⁻¹ * (S (0, y)).2) := by
    intro y
    have := hH (0, y)
    simpa using this
  have hq0 : ∀ x, (S (x, 0)).2 = 0 :=
    Weights16.additive_W0_Lambda hF hord (f := fun x => (S (x, 0)).2) hq_add (fun x => by
      have := congrArg Prod.snd (hx x)
      simp only at this
      rw [this, hinv14])
  have hs0 : ∀ y, (S (0, y)).1 = 0 :=
    Weights16.additive_Lambda_W0 hF hord (f := fun y => (S (0, y)).1) hs_add (fun y => by
      have := congrArg Prod.fst (hy y)
      simp only at this
      show (S (0, ζ ^ 14 * y)).1 = ζ * (S (0, y)).1
      rw [← hinv14]
      exact this)
  obtain ⟨p₁, hp⟩ := Weights16.additive_single_of_weight hF hord (a := 1) (b := 1) (i₀ := 0)
    (by decide) (f := fun x => (S (x, 0)).1) hp_add (fun x => by
      have := congrArg Prod.fst (hx x)
      simp only at this
      show (S (ζ ^ 1 * x, 0)).1 = ζ ^ 1 * (S (x, 0)).1
      rw [pow_one]
      exact this)
  obtain ⟨t₁, ht⟩ := Weights16.additive_single_of_weight hF hord (a := 14) (b := 14) (i₀ := 0)
    (by decide) (f := fun y => (S (0, y)).2) ht_add (fun y => by
      have := congrArg Prod.snd (hy y)
      simp only at this
      show (S (0, ζ ^ 14 * y)).2 = ζ ^ 14 * (S (0, y)).2
      rw [← hinv14]
      exact this)
  simp only [Fin.val_zero, pow_zero, pow_one] at hp ht
  have hS : ∀ v : F × F, S v = (p₁ * v.1, t₁ * v.2) := by
    intro v
    rw [hdec v]
    ext
    · simp [hs0, hp]
    · simp [hq0, ht]
  have h1 := hU (0, 1)
  rw [hS, hS] at h1
  have h2 := congrArg Prod.fst h1
  simp at h2
  refine ⟨p₁, fun v => ?_⟩
  rw [hS v, ← h2]

end Schur


section Frobenius

open CFSG.GH74.KGroups

theorem roots_gf16 : ∀ a b : GF16, a ^ 4 = a + 1 → b ^ 4 = b + 1 →
    b = a ∨ b = a ^ 2 ∨ b = a ^ 4 ∨ b = a ^ 8 := by
  decide +kernel

theorem exists_frob_of_root (hF : Nat.card F = 16) {ζ r : F} (hζ : ζ ^ 4 = ζ + 1)
    (hr : r ^ 4 = r + 1) : ∃ j : ℕ, j < 4 ∧ r = ζ ^ 2 ^ j := by
  obtain ⟨φ⟩ := Weights16.exists_ringEquiv hF
  have ha : φ.symm ζ ^ 4 = φ.symm ζ + 1 := by rw [← map_pow, hζ, map_add, map_one]
  have hb : φ.symm r ^ 4 = φ.symm r + 1 := by rw [← map_pow, hr, map_add, map_one]
  have key := roots_gf16 _ _ ha hb
  have hφ : ∀ k : ℕ, φ.symm (ζ ^ k) = φ.symm ζ ^ k := fun k => map_pow _ _ _
  rcases key with h | h | h | h
  · exact ⟨0, by norm_num, φ.symm.injective (by rw [h, hφ]; simp)⟩
  · exact ⟨1, by norm_num, φ.symm.injective (by rw [h, hφ]; simp)⟩
  · exact ⟨2, by norm_num, φ.symm.injective (by rw [h, hφ]; simp)⟩
  · exact ⟨3, by norm_num, φ.symm.injective (by rw [h, hφ]; simp)⟩

theorem ringHom_eq_frob (hF : Nat.card F = 16) (τ : F →+* F) :
    ∃ j : ℕ, j < 4 ∧ ∀ x, τ x = x ^ 2 ^ j := by
  have := charP_two hF
  obtain ⟨ζ, hζ⟩ := Weights16.exists_pow_four_eq hF
  have hτ : τ ζ ^ 4 = τ ζ + 1 := by rw [← map_pow, hζ, map_add, map_one]
  obtain ⟨j, hj, hτζ⟩ := exists_frob_of_root hF hζ hτ
  refine ⟨j, hj, fun x => ?_⟩
  let ψ' : F →+* F :=
    { toFun := fun x => x ^ 2 ^ j
      map_one' := one_pow _
      map_mul' := fun x y => mul_pow x y _
      map_zero' := zero_pow (pow_ne_zero _ two_ne_zero)
      map_add' := fun x y => add_pow_char_pow x y 2 j }
  have := ringHom_ext_zeta hF hζ (ψ := τ) (ψ' := ψ') hτζ
  exact DFunLike.congr_fun this x

end Frobenius


theorem natHom_injective : Function.Injective (natHom : SL(2, F) → AddMonoid.End (F × F)) := by
  intro g g' h
  have h1 := DFunLike.congr_fun h (1, 0)
  have h2 := DFunLike.congr_fun h (0, 1)
  simp only [natHom_apply, mul_one, mul_zero, add_zero, zero_add, Prod.mk.injEq] at h1 h2
  apply sl_eq
  ext i j
  fin_cases i <;> fin_cases j
  · exact h1.1
  · exact h2.1
  · exact h1.2
  · exact h2.2

section Normalizer

variable (hF : Nat.card F = 16)

include hF

theorem normalizer_coords (N : (F × F) ≃+ (F × F))
    (hN : ∀ g : SL(2, F), ∃ g' : SL(2, F), ∀ v, N (natHom g v) = natHom g' (N v)) :
    ∃ j : ℕ, j < 4 ∧ ∀ (a : F) (v : F × F),
      N (a * v.1, a * v.2) = (a ^ 2 ^ j * (N v).1, a ^ 2 ^ j * (N v).2) := by
  have := charP_two hF
  have hFfin : Finite F := Nat.finite_of_card_ne_zero (by omega)
  obtain ⟨ζ, hζ⟩ := Weights16.exists_pow_four_eq hF
  have hz := zeta_ne_zero hζ
  choose ν hν using hN
  have hνinj : Function.Injective ν := by
    intro g g' h
    apply natHom_injective
    refine DFunLike.ext _ _ fun v => ?_
    apply N.injective
    rw [hν, hν, h]
  have hνsurj : Function.Surjective ν := Finite.injective_iff_surjective.1 hνinj
  let mulA : F → (F × F) →+ (F × F) := fun a =>
    AddMonoidHom.mk' (fun v => (a * v.1, a * v.2)) (fun v w => by ext <;> simp [mul_add])
  let S : F → (F × F) →+ (F × F) := fun a =>
    N.toAddMonoidHom.comp ((mulA a).comp N.symm.toAddMonoidHom)
  have hS : ∀ a v, S a v = N (a * (N.symm v).1, a * (N.symm v).2) := fun a v => rfl
  have hcomm : ∀ (a : F) (g' : SL(2, F)) (v : F × F), S a (natHom g' v) = natHom g' (S a v) := by
    intro a g' v
    obtain ⟨g, rfl⟩ := hνsurj g'
    have h1 : natHom g (N.symm v) = N.symm (natHom (ν g) v) := by
      apply N.injective
      rw [hν, N.apply_symm_apply, N.apply_symm_apply]
    have h2 : N.symm (natHom (ν g) v) = natHom g (N.symm v) := h1.symm
    rw [hS, h2, hS, ← hν]
    congr 1
    simp only [natHom_apply]
    ext <;> ring
  have hscalar : ∀ a : F, ∃ μ : F, ∀ v, S a v = (μ * v.1, μ * v.2) := by
    intro a
    refine schur_coords hF hζ (S a) (fun v => ?_) (fun v => ?_)
    · have := hcomm a (tE ζ hz) v
      simpa using this
    · have := hcomm a (uE 1) v
      simpa using this
  choose τ0 hτ0 using hscalar
  have hspec : ∀ (a : F) (u : F × F), N (a * u.1, a * u.2) = (τ0 a * (N u).1, τ0 a * (N u).2) := by
    intro a u
    have := hτ0 a (N u)
    rw [hS, N.symm_apply_apply] at this
    exact this
  let e : F × F := N.symm (1, 0)
  have hτe : ∀ a : F, N (a * e.1, a * e.2) = (τ0 a, 0) := by
    intro a
    rw [hspec a e, N.apply_symm_apply]
    simp
  let τ : F →+* F :=
    { toFun := τ0
      map_one' := by
        have := hτe 1
        simp only [one_mul, Prod.mk.eta] at this
        have h2 : N e = (1, 0) := N.apply_symm_apply _
        rw [h2] at this
        exact (Prod.ext_iff.1 this).1.symm
      map_zero' := by
        have := hτe 0
        simp only [zero_mul] at this
        have h2 : N ((0 : F), (0 : F)) = 0 := map_zero N
        rw [h2] at this
        exact (Prod.ext_iff.1 this).1.symm
      map_add' := fun a b => by
        have h1 := hτe (a + b)
        have h2 : ((a + b) * e.1, (a + b) * e.2) = (a * e.1, a * e.2) + (b * e.1, b * e.2) := by
          ext <;> simp [add_mul]
        rw [h2, map_add, hτe a, hτe b] at h1
        exact (Prod.ext_iff.1 h1).1.symm
      map_mul' := fun a b => by
        have h1 := hτe (a * b)
        have h2 : (a * b * e.1, a * b * e.2) = (a * (b * e.1), a * (b * e.2)) := by
          ext <;> simp [mul_assoc]
        rw [h2, hspec a (b * e.1, b * e.2)] at h1
        simp only [hτe b] at h1
        have := (Prod.ext_iff.1 h1).1
        simpa using this.symm }
  obtain ⟨j, hj, hτ⟩ := ringHom_eq_frob hF τ
  refine ⟨j, hj, fun a v => ?_⟩
  rw [hspec a v]
  have : τ0 a = a ^ 2 ^ j := hτ a
  rw [this]


end Normalizer

@[expose] def IsSemilinear (j : ℕ) (f : (Fin 2 → F) → (Fin 2 → F)) : Prop :=
  ∀ (a : F) (w : Fin 2 → F), f (a • w) = a ^ 2 ^ j • f w

@[expose] def glEquiv (n : GL (Fin 8) (ZMod 2)) : (Fin 8 → ZMod 2) ≃+ (Fin 8 → ZMod 2) where
  toFun v := (n : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ v
  invFun v := ((n⁻¹ : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ v
  left_inv v := by
    simp only [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec]
  right_inv v := by
    simp only [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec]
  map_add' a b := Matrix.mulVec_add _ _ _

theorem glEquiv_apply (n : GL (Fin 8) (ZMod 2)) (v : Fin 8 → ZMod 2) :
    glEquiv n v = (n : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ v := rfl

section Coord

variable {ρ : SL(2, F) →* GL (Fin 8) (ZMod 2)}

@[expose] def coord (Φ : (Fin 8 → ZMod 2) ≃+ (Fin 2 → F)) : (Fin 8 → ZMod 2) ≃+ (F × F) :=
  Φ.trans prodEquivFin.symm

theorem coord_apply (Φ : (Fin 8 → ZMod 2) ≃+ (Fin 2 → F)) (v : Fin 8 → ZMod 2) :
    prodEquivFin (coord Φ v) = Φ v := by
  show prodEquivFin (prodEquivFin.symm (Φ v)) = Φ v
  exact AddEquiv.apply_symm_apply _ _

@[expose] def coordMap (Φ : (Fin 8 → ZMod 2) ≃+ (Fin 2 → F)) (n : GL (Fin 8) (ZMod 2)) :
    (F × F) ≃+ (F × F) :=
  ((coord Φ).symm.trans (glEquiv n)).trans (coord Φ)

theorem coordMap_apply (Φ : (Fin 8 → ZMod 2) ≃+ (Fin 2 → F)) (n : GL (Fin 8) (ZMod 2))
    (v : Fin 8 → ZMod 2) :
    coordMap Φ n (coord Φ v) = coord Φ ((n : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ v) := by
  show coord Φ ((n : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ (coord Φ).symm (coord Φ v)) = _
  rw [AddEquiv.symm_apply_apply]

theorem coord_natural {Φ : (Fin 8 → ZMod 2) ≃+ (Fin 2 → F)}
    (hΦ : ∀ (g : SL(2, F)) (v : Fin 8 → ZMod 2),
      Φ ((ρ g : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ v) = (g : Matrix (Fin 2) (Fin 2) F) *ᵥ Φ v)
    (g : SL(2, F)) (v : Fin 8 → ZMod 2) :
    coord Φ ((ρ g : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ v) = natHom g (coord Φ v) := by
  show prodEquivFin.symm (Φ _) = natHom g (prodEquivFin.symm (Φ v))
  rw [hΦ, prodEquivFin.symm_apply_eq, ← mulVec_prodEquivFin, AddEquiv.apply_symm_apply]

theorem coordMap_natural {Φ : (Fin 8 → ZMod 2) ≃+ (Fin 2 → F)}
    (hΦ : ∀ (g : SL(2, F)) (v : Fin 8 → ZMod 2),
      Φ ((ρ g : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ v) = (g : Matrix (Fin 2) (Fin 2) F) *ᵥ Φ v)
    (n : GL (Fin 8) (ZMod 2)) {g g' : SL(2, F)} (hg : n * ρ g * n⁻¹ = ρ g') (u : F × F) :
    coordMap Φ n (natHom g u) = natHom g' (coordMap Φ n u) := by
  have h1 : (coord Φ).symm (natHom g u) =
      (ρ g : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ (coord Φ).symm u := by
    rw [AddEquiv.symm_apply_eq, coord_natural hΦ, AddEquiv.apply_symm_apply]
  have h2 : (n : Matrix (Fin 8) (Fin 8) (ZMod 2)) * (ρ g : Matrix (Fin 8) (Fin 8) (ZMod 2)) =
      (ρ g' : Matrix (Fin 8) (Fin 8) (ZMod 2)) * (n : Matrix (Fin 8) (Fin 8) (ZMod 2)) := by
    rw [← Units.val_mul, ← Units.val_mul, ← hg, mul_assoc, inv_mul_cancel, mul_one]
  show coord Φ ((n : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ (coord Φ).symm (natHom g u)) =
    natHom g' (coord Φ ((n : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ (coord Φ).symm u))
  rw [h1, Matrix.mulVec_mulVec, h2, ← Matrix.mulVec_mulVec, coord_natural hΦ]

theorem prodEquivFin_smul (a : F) (x : F × F) :
    prodEquivFin (a * x.1, a * x.2) = a • prodEquivFin x := by
  ext i
  fin_cases i <;> simp [prodEquivFin_apply]

theorem isSemilinear_iff_coord (Φ : (Fin 8 → ZMod 2) ≃+ (Fin 2 → F)) (n : GL (Fin 8) (ZMod 2))
    (j : ℕ) :
    IsSemilinear j (fun w => Φ ((n : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ Φ.symm w)) ↔
      ∀ (a : F) (u : F × F), coordMap Φ n (a * u.1, a * u.2) =
        (a ^ 2 ^ j * (coordMap Φ n u).1, a ^ 2 ^ j * (coordMap Φ n u).2) := by
  have hN' : ∀ x : F × F, prodEquivFin (coordMap Φ n x) =
      Φ ((n : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ Φ.symm (prodEquivFin x)) := by
    intro x
    show prodEquivFin (prodEquivFin.symm (Φ ((n : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ
      (Φ.symm (prodEquivFin x))))) = _
    rw [AddEquiv.apply_symm_apply]
  constructor
  · intro h a u
    apply prodEquivFin.injective
    rw [prodEquivFin_smul (a ^ 2 ^ j) (coordMap Φ n u), hN', hN', prodEquivFin_smul a u]
    exact h a (prodEquivFin u)
  · intro h a w
    obtain ⟨u, rfl⟩ := prodEquivFin.surjective w
    show Φ _ = a ^ 2 ^ j • Φ _
    rw [← prodEquivFin_smul a u, ← hN', ← hN', h a u, prodEquivFin_smul]

end Coord

section NormalizerGL

variable (hF : Nat.card F = 16) {ρ : SL(2, F) →* GL (Fin 8) (ZMod 2)}
  {Φ : (Fin 8 → ZMod 2) ≃+ (Fin 2 → F)}
  (hΦ : ∀ (g : SL(2, F)) (v : Fin 8 → ZMod 2),
    Φ ((ρ g : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ v) = (g : Matrix (Fin 2) (Fin 2) F) *ᵥ Φ v)

include hF hΦ

theorem normalizer_semilinear (n : GL (Fin 8) (ZMod 2))
    (hn : ∀ g : SL(2, F), ∃ g' : SL(2, F), n * ρ g * n⁻¹ = ρ g') :
    ∃ j : ℕ, j < 4 ∧ IsSemilinear j (fun w => Φ ((n : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ
      Φ.symm w)) := by
  have hN : ∀ g : SL(2, F), ∃ g' : SL(2, F), ∀ v, coordMap Φ n (natHom g v) =
      natHom g' (coordMap Φ n v) := fun g => by
    obtain ⟨g', hg'⟩ := hn g
    exact ⟨g', coordMap_natural hΦ n hg'⟩
  obtain ⟨j, hj, hjN⟩ := normalizer_coords hF (coordMap Φ n) hN
  exact ⟨j, hj, (isSemilinear_iff_coord Φ n j).2 hjN⟩

end NormalizerGL


section SemilinearAPI

theorem IsSemilinear.comp {j j' : ℕ} {f g : (Fin 2 → F) → (Fin 2 → F)} (hf : IsSemilinear j f)
    (hg : IsSemilinear j' g) : IsSemilinear (j + j') (f ∘ g) := by
  intro a w
  simp only [Function.comp_apply]
  rw [hg, hf, ← pow_mul, ← pow_add, add_comm j j']

theorem IsSemilinear.one : IsSemilinear 0 (id : (Fin 2 → F) → (Fin 2 → F)) := by
  intro a w
  simp

variable (hF : Nat.card F = 16)

include hF

theorem pow_two_pow_four (x : F) : x ^ 2 ^ 4 = x := by
  have : Finite F := Nat.finite_of_card_ne_zero (by omega)
  let _ := Fintype.ofFinite F
  have hq : Fintype.card F = 16 := by rw [← Nat.card_eq_fintype_card]; exact hF
  have := FiniteField.pow_card x
  rwa [hq] at this

theorem IsSemilinear.of_modEq {j j' : ℕ} {f : (Fin 2 → F) → (Fin 2 → F)} (hf : IsSemilinear j f)
    (h : j ≡ j' [MOD 4]) : IsSemilinear j' f := by
  have key : ∀ (k i : ℕ) (a : F), a ^ 2 ^ (i + 4 * k) = a ^ 2 ^ i := by
    intro k i a
    induction k with
    | zero => simp
    | succ k ih =>
      rw [show i + 4 * (k + 1) = (i + 4 * k) + 4 by ring, pow_add, pow_mul, pow_two_pow_four hF]
      exact ih
  have hmod : ∀ (j j' : ℕ), j ≡ j' [MOD 4] → ∀ a : F, a ^ 2 ^ j = a ^ 2 ^ j' := by
    intro j j' h a
    have h4 : j % 4 = j' % 4 := h
    have e1 : j = j % 4 + 4 * (j / 4) := (Nat.mod_add_div j 4).symm
    have e2 : j' = j' % 4 + 4 * (j' / 4) := (Nat.mod_add_div j' 4).symm
    rw [e1, e2, key, key, h4]
  intro a w
  rw [hf a w, hmod j j' h a]

theorem IsSemilinear.unique {j j' : ℕ} (hj : j < 4) (hj' : j' < 4)
    {f : (Fin 2 → F) → (Fin 2 → F)} (hf : IsSemilinear j f) (hf' : IsSemilinear j' f)
    (hnz : ∃ w, f w ≠ 0) : j = j' := by
  obtain ⟨ζ, hζ⟩ := Weights16.exists_pow_four_eq hF
  have hord : orderOf ζ = 15 := Weights16.orderOf_eq_fifteen_of_pow_four hF hζ
  obtain ⟨w, hw⟩ := hnz
  obtain ⟨i, hi⟩ : ∃ i, f w i ≠ 0 := by
    by_contra h
    push Not at h
    exact hw (funext h)
  have h1 : ζ ^ 2 ^ j = ζ ^ 2 ^ j' := by
    have e := (hf ζ w).symm.trans (hf' ζ w)
    have := congrFun e i
    simp only [Pi.smul_apply, smul_eq_mul] at this
    exact mul_right_cancel₀ hi this
  have hfin : IsOfFinOrder ζ := orderOf_pos_iff.1 (by rw [hord]; norm_num)
  have h2 := hfin.pow_eq_pow_iff_modEq.1 h1
  rw [hord] at h2
  have h3 : 2 ^ j % 15 = 2 ^ j' % 15 := h2
  interval_cases j <;> interval_cases j' <;> simp_all


omit hF in
theorem semilin_mul (Φ : (Fin 8 → ZMod 2) ≃+ (Fin 2 → F)) (n n' : GL (Fin 8) (ZMod 2)) :
    (fun w => Φ (((n * n' : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ
      Φ.symm w)) =
      (fun w => Φ ((n : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ Φ.symm w)) ∘
        (fun w => Φ ((n' : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ Φ.symm w)) := by
  funext w
  simp [Matrix.mulVec_mulVec, Units.val_mul]

omit hF in
theorem semilin_exists_ne_zero (Φ : (Fin 8 → ZMod 2) ≃+ (Fin 2 → F)) (n : GL (Fin 8) (ZMod 2)) :
    ∃ w, Φ ((n : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ Φ.symm w) ≠ 0 := by
  let v : Fin 8 → ZMod 2 := Pi.single 0 1
  have hv : v ≠ 0 := by
    intro h
    have := congrFun h 0
    simp [v] at this
  refine ⟨Φ v, ?_⟩
  rw [AddEquiv.symm_apply_apply]
  intro h
  have h1 : (n : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ v = 0 := by
    have := Φ.injective (h.trans (map_zero Φ).symm)
    exact this
  apply hv
  calc v = ((n⁻¹ : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ
        ((n : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ v) := by
        simp [Matrix.mulVec_mulVec]
    _ = 0 := by rw [h1, Matrix.mulVec_zero]

theorem semilinear_unique (Φ : (Fin 8 → ZMod 2) ≃+ (Fin 2 → F)) (n : GL (Fin 8) (ZMod 2))
    {j j' : ℕ} (hj : j < 4) (hj' : j' < 4)
    (h : IsSemilinear j (fun w => Φ ((n : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ Φ.symm w)))
    (h' : IsSemilinear j' (fun w => Φ ((n : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ Φ.symm w))) :
    j = j' :=
  IsSemilinear.unique hF hj hj' h h' (semilin_exists_ne_zero Φ n)

end SemilinearAPI


end Nat16

end CFSG.OddStandard.Seitz77
