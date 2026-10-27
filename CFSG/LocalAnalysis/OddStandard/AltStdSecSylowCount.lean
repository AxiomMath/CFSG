module

public import Mathlib.GroupTheory.RegularWreathProduct

public section

namespace CFSG.OddStandard.AltStdSec.SylowSn

abbrev Z2 := Multiplicative (ZMod 2)

@[expose] def z2 : Z2 := Multiplicative.ofAdd 1

theorem z2_cases (x : Z2) : x = 1 ∨ x = z2 := by
  revert x; decide

theorem z2_ne_one : z2 ≠ 1 := by decide

theorem z2_mul_self : z2 * z2 = 1 := by decide

theorem z2_inv : z2⁻¹ = z2 := by decide

theorem units_aux1 : ∀ u v ε : ℤˣ, u * v = ε → v = ε * u := by decide

theorem units_aux2 : ∀ u v ε : ℤˣ, v = ε * u → u * v = ε := by decide

theorem sum_units (F : ℤˣ → ℕ) : ∑ ε₁ : ℤˣ, F ε₁ = F 1 + F (-1) := by
  have : (Finset.univ : Finset ℤˣ) = {1, -1} := by decide
  rw [this, Finset.sum_pair (by decide)]

section Decomp

variable {A B : Type*} [Finite A] [Finite B]

noncomputable def decompEquiv (sA : A → ℤˣ) (sB : B → ℤˣ) (PA : A → Prop) (PB : B → Prop)
    (ε : ℤˣ) :
    {p : A × B // sA p.1 * sB p.2 = ε ∧ PA p.1 ∧ PB p.2} ≃
      Σ ε₁ : ℤˣ, ({a : A // sA a = ε₁ ∧ PA a} × {b : B // sB b = ε * ε₁ ∧ PB b}) where
  toFun p := ⟨sA p.1.1, ⟨p.1.1, rfl, p.2.2.1⟩,
    ⟨p.1.2, units_aux1 _ _ _ p.2.1, p.2.2.2⟩⟩
  invFun x := ⟨(x.2.1.1, x.2.2.1), by
    have h1 : sA x.2.1.1 = x.1 := x.2.1.2.1
    have h2 : sB x.2.2.1 = ε * x.1 := x.2.2.2.1
    show sA x.2.1.1 * sB x.2.2.1 = ε
    rw [h1, h2]
    exact units_aux2 _ _ _ rfl, x.2.1.2.2, x.2.2.2.2⟩
  left_inv p := rfl
  right_inv x := by
    obtain ⟨ε₁, ⟨a, ha, hPA⟩, ⟨b, hb, hPB⟩⟩ := x
    subst ha
    rfl

theorem card_pairs_sign (sA : A → ℤˣ) (sB : B → ℤˣ) (PA : A → Prop) (PB : B → Prop) (ε : ℤˣ) :
    Nat.card {p : A × B // sA p.1 * sB p.2 = ε ∧ PA p.1 ∧ PB p.2} =
      ∑ ε₁ : ℤˣ, Nat.card {a : A // sA a = ε₁ ∧ PA a} *
        Nat.card {b : B // sB b = ε * ε₁ ∧ PB b} := by
  rw [Nat.card_congr (decompEquiv sA sB PA PB ε), Nat.card_sigma]
  refine Finset.sum_congr rfl fun ε₁ _ => ?_
  rw [Nat.card_prod]

end Decomp

section Counts

variable {D : Type*} [Group D]

@[expose] noncomputable def rootCount (s : D →* ℤˣ) (ε : ℤˣ) (d : D) : ℕ :=
  Nat.card {a : D // s a = ε ∧ a * a = d}

theorem rootCount_prod [Finite D] {E : Type*} [Group E] [Finite E] (s : D →* ℤˣ) (t : E →* ℤˣ)
    (σ : D × E → ℤˣ) (hσ : ∀ p, σ p = s p.1 * t p.2) (ε : ℤˣ) (d : D) (e : E) :
    Nat.card {p : D × E // σ p = ε ∧ p * p = (d, e)} =
      ∑ ε₁ : ℤˣ, rootCount s ε₁ d * rootCount t (ε * ε₁) e := by
  have h := card_pairs_sign (fun a => s a) (fun b => t b) (fun a => a * a = d)
    (fun b => b * b = e) ε
  unfold rootCount
  rw [← h]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun p => ?_)
  rw [hσ, Prod.ext_iff]
  rfl

@[expose] def diag (d : D) : D ≀ᵣ Z2 := ⟨fun _ => d, 1⟩

theorem mul_self_right_one (f : Z2 → D) :
    (⟨f, 1⟩ : D ≀ᵣ Z2) * ⟨f, 1⟩ = ⟨fun z => f z * f z, 1⟩ := by
  rw [RegularWreathProduct.mul_def]
  ext <;> simp

theorem mul_self_right_z2 (f : Z2 → D) :
    (⟨f, z2⟩ : D ≀ᵣ Z2) * ⟨f, z2⟩ = ⟨fun z => f z * f (z2 * z), 1⟩ := by
  rw [RegularWreathProduct.mul_def]
  ext <;> simp [z2_inv, z2_mul_self]

variable (D) in
def pairEquiv : (Z2 → D) ≃ D × D where
  toFun f := (f 1, f z2)
  invFun p x := if x = 1 then p.1 else p.2
  left_inv f := by
    funext x
    rcases z2_cases x with rfl | rfl <;> simp [z2_ne_one]
  right_inv p := by simp [z2_ne_one]

theorem card_wreath_roots [Finite D] (s : D →* ℤˣ) (τ : ℤˣ) (σ : D ≀ᵣ Z2 → ℤˣ)
    (hσ : ∀ x : D ≀ᵣ Z2, σ x = s (x.left 1) * s (x.left z2) * (if x.right = 1 then 1 else τ))
    (d : D) (hd : ∀ a : D, a * d = d * a) (ε : ℤˣ) :
    Nat.card {x : D ≀ᵣ Z2 // σ x = ε ∧ x * x = diag d} =
      (∑ ε₁ : ℤˣ, rootCount s ε₁ d * rootCount s (ε * ε₁) d) +
        (if s d * τ = ε then Nat.card D else 0) := by
  classical
  have h1 : Nat.card {x : D ≀ᵣ Z2 // σ x = ε ∧ x * x = diag d} =
      ∑ q : Z2, Nat.card {f : Z2 → D // σ ⟨f, q⟩ = ε ∧
        (⟨f, q⟩ : D ≀ᵣ Z2) * ⟨f, q⟩ = diag d} := by
    rw [← Nat.card_sigma]
    exact Nat.card_congr ((Equiv.subtypeEquiv ((RegularWreathProduct.equivProd D Z2).trans
      (Equiv.prodComm _ _))
      (p := fun x : D ≀ᵣ Z2 => σ x = ε ∧ x * x = diag d)
      (q := fun y : Z2 × (Z2 → D) => σ ⟨y.2, y.1⟩ = ε ∧
        (⟨y.2, y.1⟩ : D ≀ᵣ Z2) * ⟨y.2, y.1⟩ = diag d)
      (fun x => Iff.rfl)).trans (Equiv.subtypeProdEquivSigmaSubtype
        (fun (q : Z2) (f : Z2 → D) => σ ⟨f, q⟩ = ε ∧
          (⟨f, q⟩ : D ≀ᵣ Z2) * ⟨f, q⟩ = diag d)))
  have hU : (Finset.univ : Finset Z2) = {1, z2} := by decide
  rw [h1, hU, Finset.sum_pair z2_ne_one.symm]
  congr 1
  ·
    have e1 : ∀ f : Z2 → D, (σ ⟨f, 1⟩ = ε ∧ (⟨f, 1⟩ : D ≀ᵣ Z2) * ⟨f, 1⟩ = diag d) ↔
        (s (f 1) * s (f z2) = ε ∧ f 1 * f 1 = d ∧ f z2 * f z2 = d) := by
      intro f
      rw [hσ, mul_self_right_one, diag]
      simp only [ite_true, mul_one, RegularWreathProduct.mk.injEq, and_true]
      refine and_congr Iff.rfl ?_
      constructor
      · intro h
        exact ⟨congrFun h 1, congrFun h z2⟩
      · rintro ⟨h1, h2⟩
        funext z
        rcases z2_cases z with rfl | rfl
        · exact h1
        · exact h2
    rw [Nat.card_congr (Equiv.subtypeEquivRight e1)]
    rw [Nat.card_congr ((pairEquiv D).subtypeEquiv
      (p := fun f : Z2 → D => s (f 1) * s (f z2) = ε ∧ f 1 * f 1 = d ∧ f z2 * f z2 = d)
      (q := fun p : D × D => s p.1 * s p.2 = ε ∧ p.1 * p.1 = d ∧ p.2 * p.2 = d)
      (fun f => Iff.rfl))]
    exact card_pairs_sign (fun a => s a) (fun b => s b) (fun a => a * a = d)
      (fun b => b * b = d) ε
  ·
    have e2 : ∀ f : Z2 → D, (σ ⟨f, z2⟩ = ε ∧ (⟨f, z2⟩ : D ≀ᵣ Z2) * ⟨f, z2⟩ = diag d) ↔
        (s (f 1) * s (f z2) * τ = ε ∧ f 1 * f z2 = d ∧ f z2 * f 1 = d) := by
      intro f
      rw [hσ, mul_self_right_z2, diag]
      simp only [z2_ne_one, ite_false, RegularWreathProduct.mk.injEq, and_true]
      refine and_congr Iff.rfl ?_
      constructor
      · intro h
        have h1 := congrFun h 1
        have h2 := congrFun h z2
        simp only [mul_one, z2_mul_self] at h1 h2
        exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩
        funext z
        rcases z2_cases z with rfl | rfl
        · simpa using h1
        · simpa [z2_mul_self] using h2
    rw [Nat.card_congr (Equiv.subtypeEquivRight e2)]
    rw [Nat.card_congr ((pairEquiv D).subtypeEquiv
      (p := fun f : Z2 → D => s (f 1) * s (f z2) * τ = ε ∧ f 1 * f z2 = d ∧ f z2 * f 1 = d)
      (q := fun p : D × D => s p.1 * s p.2 * τ = ε ∧ p.1 * p.2 = d ∧ p.2 * p.1 = d)
      (fun f => Iff.rfl))]
    by_cases hc : s d * τ = ε
    · simp only [hc, ite_true]
      refine Nat.card_congr ?_
      exact
        { toFun := fun p => p.1.1
          invFun := fun a => ⟨(a, a⁻¹ * d), by
            refine ⟨?_, ?_, ?_⟩
            · rw [map_mul, map_inv, mul_inv_cancel_left]
              exact hc
            · group
            · calc a⁻¹ * d * a = a⁻¹ * (d * a) := by group
                _ = a⁻¹ * (a * d) := by rw [hd a]
                _ = d := by group⟩
          left_inv := fun p => by
            obtain ⟨⟨a, b⟩, h1, h2, h3⟩ := p
            have hb : b = a⁻¹ * d := by
              rw [← h2]; group
            subst hb
            rfl
          right_inv := fun a => rfl }
    · simp only [hc, ite_false]
      refine Nat.card_eq_zero.2 (Or.inl ⟨fun p => hc ?_⟩)
      obtain ⟨⟨a, b⟩, h1, h2, h3⟩ := p
      simp only at h1 h2
      rw [← h1, ← h2, map_mul]

theorem diag_one : diag (1 : D) = 1 := rfl

theorem diag_mul_self (d : D) : diag d * diag d = diag (d * d) := by
  rw [diag, RegularWreathProduct.mul_def]
  ext <;> simp [diag]

theorem diag_central {d : D} (hd : ∀ a : D, a * d = d * a) (x : D ≀ᵣ Z2) :
    x * diag d = diag d * x := by
  rw [diag, RegularWreathProduct.mul_def, RegularWreathProduct.mul_def]
  ext z
  · simp [hd]
  · simp

omit [Group D] in
theorem diag_injective : Function.Injective (diag : D → D ≀ᵣ Z2) := by
  intro a b h
  have := congrFun (congrArg RegularWreathProduct.left h) 1
  simpa [diag] using this

theorem central_wreath (u : D) (hu : u ≠ 1) (y : D ≀ᵣ Z2) (hc : ∀ x : D ≀ᵣ Z2, x * y = y * x) :
    ∃ d : D, (∀ a : D, a * d = d * a) ∧ y = diag d := by
  classical
  obtain ⟨f, q⟩ := y
  have hq : q = 1 := by
    by_contra hq
    have hqz : q = z2 := (z2_cases q).resolve_left hq
    subst hqz
    have h := hc ⟨fun z => if z = 1 then u else 1, 1⟩
    rw [RegularWreathProduct.mul_def, RegularWreathProduct.mul_def] at h
    have h1 := congrFun (congrArg RegularWreathProduct.left h) 1
    simp [z2_ne_one, z2_inv] at h1
    exact hu h1
  subst hq
  have hcent : ∀ z : Z2, ∀ a : D, a * f z = f z * a := by
    intro z a
    have h := hc ⟨fun w => if w = z then a else 1, 1⟩
    rw [RegularWreathProduct.mul_def, RegularWreathProduct.mul_def] at h
    have h1 := congrFun (congrArg RegularWreathProduct.left h) z
    simpa using h1
  have hconst : f z2 = f 1 := by
    have h := hc ⟨fun _ => 1, z2⟩
    rw [RegularWreathProduct.mul_def, RegularWreathProduct.mul_def] at h
    have h1 := congrFun (congrArg RegularWreathProduct.left h) z2
    simpa [z2_inv, z2_ne_one, z2_mul_self] using h1.symm
  refine ⟨f 1, hcent 1, ?_⟩
  rw [diag]
  congr 1
  funext z
  rcases z2_cases z with rfl | rfl
  · rfl
  · exact hconst

end Counts

end CFSG.OddStandard.AltStdSec.SylowSn
