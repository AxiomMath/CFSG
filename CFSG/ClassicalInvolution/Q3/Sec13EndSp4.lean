module

public import CFSG.ClassicalInvolution.Q3.Sec13EndSympForm
public import Mathlib.Algebra.Module.Pi
public import Mathlib.GroupTheory.GroupAction.Jordan

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13.Sp4

open CFSG.ClassicalInvolution.Q3.Sec13.Polar

abbrev V4 : Type := Fin 4 → ZMod 2

@[expose] def symp (x y : V4) : ZMod 2 := x 0 * y 1 + x 1 * y 0 + x 2 * y 3 + x 3 * y 2

@[expose] def cv : Fin 6 → V4 :=
  ![0, ![1, 0, 0, 0], ![0, 1, 0, 0], ![1, 1, 1, 0], ![1, 1, 0, 1], ![1, 1, 1, 1]]

@[expose] def dv (a b : Fin 6) : V4 := cv a + cv b

@[expose] def Even6 (f : Fin 6 → ZMod 2) : Prop := ∑ i, f i = 0

instance : DecidablePred Even6 := fun f => inferInstanceAs (Decidable (∑ i, f i = 0))

@[expose] def ones : Fin 6 → ZMod 2 := fun _ => 1

@[expose] def Sim (f g : Fin 6 → ZMod 2) : Prop := f = g ∨ f = g + ones

instance (f g : Fin 6 → ZMod 2) : Decidable (Sim f g) := inferInstanceAs (Decidable (_ ∨ _))

@[expose] def permVec (σ : Equiv.Perm (Fin 6)) (f : Fin 6 → ZMod 2) : Fin 6 → ZMod 2 :=
  fun i => f (σ.symm i)

@[expose] def dot (f g : Fin 6 → ZMod 2) : ZMod 2 := ∑ i, f i * g i

@[expose] def duadVec (a b : Fin 6) : Fin 6 → ZMod 2 := Pi.single a 1 + Pi.single b 1

@[expose] def lin : (Fin 6 → ZMod 2) →+ V4 where
  toFun f := ∑ a, f a • cv a
  map_zero' := by simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero]
  map_add' f g := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]

theorem lin_apply (f : Fin 6 → ZMod 2) : lin f = ∑ a, f a • cv a := rfl

theorem dv_surj : ∀ x : V4, x ≠ 0 → ∃ a b : Fin 6, a ≠ b ∧ x = dv a b := by
  unfold dv cv; decide

theorem dv_eq_iff : ∀ a b c d : Fin 6, a ≠ b → c ≠ d →
    (dv a b = dv c d ↔ ({a, b} : Finset (Fin 6)) = {c, d}) := by
  unfold dv cv; decide

theorem lin_even_eq_zero_iff : ∀ f : Fin 6 → ZMod 2, Even6 f → (lin f = 0 ↔ f = 0 ∨ f = ones) := by
  unfold Even6 lin ones cv; decide

theorem exists_even_lin_eq : ∀ x : V4, ∃ f : Fin 6 → ZMod 2, Even6 f ∧ lin f = x := by
  unfold Even6 lin cv; decide

theorem lin_eq_iff : ∀ f g : Fin 6 → ZMod 2, Even6 f → Even6 g → (lin f = lin g ↔ Sim f g) := by
  unfold Even6 lin Sim ones cv; decide +kernel

theorem symp_lin : ∀ f g : Fin 6 → ZMod 2, Even6 f → Even6 g →
    symp (lin f) (lin g) = dot f g := by
  unfold Even6 lin symp dot cv; decide +kernel

@[expose] def ovoid (a : Fin 6) : Finset V4 := (Finset.univ.erase a).image (fun b => dv a b)

theorem ovoid_card : ∀ a : Fin 6, (ovoid a).card = 5 := by
  unfold ovoid dv cv; decide +kernel

theorem ovoid_ne_zero : ∀ a : Fin 6, ∀ x ∈ ovoid a, x ≠ 0 := by
  unfold ovoid dv cv; decide +kernel

theorem ovoid_orth : ∀ a : Fin 6, ∀ x ∈ ovoid a, ∀ y ∈ ovoid a, x ≠ y → symp x y = 1 := by
  unfold ovoid dv cv symp; decide +kernel

theorem ovoid_inter : ∀ a b : Fin 6, a ≠ b → ovoid a ∩ ovoid b = {dv a b} := by
  unfold ovoid dv cv; decide +kernel

theorem ovoid_injective : ∀ a b : Fin 6, ovoid a = ovoid b → a = b := by
  unfold ovoid dv cv; decide +kernel

theorem ovoid_classification : ∀ O ∈ Finset.powersetCard 5 (Finset.univ.erase (0 : V4)),
    (∀ x ∈ O, ∀ y ∈ O, x ≠ y → symp x y = 1) → ∃ a, O = ovoid a := by
  unfold ovoid dv cv symp; decide +kernel

theorem dv_self (a : Fin 6) : dv a a = 0 := by
  revert a; unfold dv cv; decide

theorem dv_comm (a b : Fin 6) : dv a b = dv b a := add_comm _ _

theorem mem_ovoid_dv {a b : Fin 6} (h : b ≠ a) : dv a b ∈ ovoid a := by
  unfold ovoid
  exact Finset.mem_image.mpr ⟨b, Finset.mem_erase.mpr ⟨h, Finset.mem_univ _⟩, rfl⟩

theorem even_zero_eq (f : Fin 6 → ZMod 2) (hf : Even6 f) :
    f 0 = f 1 + f 2 + f 3 + f 4 + f 5 := by
  have h : f 0 + f 1 + f 2 + f 3 + f 4 + f 5 = 0 := by
    have := hf
    unfold Even6 at this
    simpa [Fin.sum_univ_succ, add_assoc] using this
  revert h
  generalize f 0 = a0
  generalize f 1 = a1
  generalize f 2 = a2
  generalize f 3 = a3
  generalize f 4 = a4
  generalize f 5 = a5
  revert a0 a1 a2 a3 a4 a5
  decide

theorem isometry_eq_perm (φ : V4 ≃+ V4) (hφ : ∀ x y, symp (φ x) (φ y) = symp x y) :
    ∃ σ : Equiv.Perm (Fin 6), ∀ a b, φ (dv a b) = dv (σ a) (σ b) := by
  have h1 : ∀ a : Fin 6, ∃ a' : Fin 6, (ovoid a).image φ = ovoid a' := by
    intro a
    refine ovoid_classification _ ?_ ?_
    · rw [Finset.mem_powersetCard]
      refine ⟨?_, ?_⟩
      · intro y hy
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
        refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
        intro h0
        exact ovoid_ne_zero a x hx (φ.injective (h0.trans (map_zero φ).symm))
      · rw [Finset.card_image_of_injective _ φ.injective, ovoid_card]
    · intro x hx y hy hxy
      obtain ⟨x', hx', rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hy
      have hne : x' ≠ y' := fun h => hxy (by rw [h])
      rw [hφ]
      exact ovoid_orth a x' hx' y' hy' hne
  choose σ hσ using h1
  have hinj : Function.Injective σ := by
    intro a b hab
    apply ovoid_injective
    apply Finset.image_injective φ.injective
    rw [hσ a, hσ b, hab]
  have hbij : Function.Bijective σ := Finite.injective_iff_bijective.mp hinj
  refine ⟨Equiv.ofBijective σ hbij, fun a b => ?_⟩
  show φ (dv a b) = dv (σ a) (σ b)
  by_cases hab : a = b
  · subst hab
    rw [dv_self, map_zero, dv_self]
  · have hmem1 : φ (dv a b) ∈ ovoid (σ a) := by
      rw [← hσ a]
      exact Finset.mem_image_of_mem φ (mem_ovoid_dv (Ne.symm hab))
    have hmem2 : φ (dv a b) ∈ ovoid (σ b) := by
      rw [← hσ b]
      exact Finset.mem_image_of_mem φ (by rw [dv_comm]; exact mem_ovoid_dv hab)
    have hne : σ a ≠ σ b := fun h => hab (hinj h)
    have hmem : φ (dv a b) ∈ ovoid (σ a) ∩ ovoid (σ b) := Finset.mem_inter.mpr ⟨hmem1, hmem2⟩
    rw [ovoid_inter (σ a) (σ b) hne] at hmem
    exact Finset.mem_singleton.mp hmem

theorem perm_unique {σ τ : Equiv.Perm (Fin 6)} (h : ∀ a b, dv (σ a) (σ b) = dv (τ a) (τ b)) :
    σ = τ := by
  have hex : ∀ a : Fin 6, ∃ b c : Fin 6, b ≠ a ∧ c ≠ a ∧ b ≠ c := by decide
  refine Equiv.ext fun a => ?_
  obtain ⟨b, c, hba, hca, hbc⟩ := hex a
  have key : ∀ b : Fin 6, b ≠ a → σ a = τ a ∨ σ a = τ b := by
    intro b hb
    have h2 : ({σ a, σ b} : Finset (Fin 6)) = {τ a, τ b} :=
      (dv_eq_iff _ _ _ _ (fun e => hb (σ.injective e).symm)
        (fun e => hb (τ.injective e).symm)).mp (h a b)
    have : σ a ∈ ({τ a, τ b} : Finset (Fin 6)) := by
      rw [← h2]; simp
    simpa using this
  by_contra hne
  rcases key b hba with h1 | h1
  · exact hne h1
  rcases key c hca with h2 | h2
  · exact hne h2
  exact hbc (τ.injective (h1.symm.trans h2))

theorem lin_permVec (φ : V4 →+ V4) (σ : Equiv.Perm (Fin 6))
    (hφ : ∀ a b, φ (dv a b) = dv (σ a) (σ b)) (f : Fin 6 → ZMod 2) (hf : Even6 f) :
    φ (lin f) = lin (permVec σ f) := by
  have hlin : lin f =
      f 1 • dv 0 1 + f 2 • dv 0 2 + f 3 • dv 0 3 + f 4 • dv 0 4 + f 5 • dv 0 5 := by
    have h0 : cv 0 = 0 := rfl
    rw [lin_apply, Fin.sum_univ_six]
    simp only [dv, h0, zero_add, smul_zero]
  have hsmul : ∀ (c : ZMod 2) (x : V4), φ (c • x) = c • φ x := by
    intro c x
    have hc : c = 0 ∨ c = 1 := by revert c; decide
    rcases hc with rfl | rfl
    · rw [zero_smul, zero_smul, map_zero]
    · rw [one_smul, one_smul]
  have h1 : φ (lin f) = f 1 • (cv (σ 0) + cv (σ 1)) + f 2 • (cv (σ 0) + cv (σ 2)) +
      f 3 • (cv (σ 0) + cv (σ 3)) + f 4 • (cv (σ 0) + cv (σ 4)) +
        f 5 • (cv (σ 0) + cv (σ 5)) := by
    rw [hlin]
    simp only [map_add, hsmul, hφ]
    rfl
  have h2 : lin (permVec σ f) = ∑ a, f a • cv (σ a) := by
    simp only [lin_apply, permVec]
    rw [← Equiv.sum_comp σ]
    simp
  rw [h1, h2, Fin.sum_univ_six, even_zero_eq f hf]
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

section
variable {W : Type*} [CommGroup W]

def pw (w : W) (c : ZMod 2) : W := if c = 0 then 1 else w

theorem pw_zero (w : W) : pw w 0 = 1 := by simp [pw]
theorem pw_one (w : W) : pw w 1 = w := by simp [pw]

theorem pw_add {w : W} (hw : w * w = 1) (c c' : ZMod 2) : pw w (c + c') = pw w c * pw w c' := by
  have hc : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  rcases hc c with rfl | rfl <;> rcases hc c' with rfl | rfl
  · simp [pw_zero]
  · simp [pw_zero]
  · simp [pw_zero]
  · have : (1 : ZMod 2) + 1 = 0 := by decide
    rw [this, pw_zero, pw_one, hw]

variable {B : W → W → ZMod 2}

theorem B_one_right (hB : SympForm B) (a : W) : B a 1 = 0 := by
  have h := hB.mul_right a 1 1
  rw [mul_one] at h
  have hc : ∀ x : ZMod 2, x = x + x → x = 0 := by decide
  exact hc _ h

theorem B_one_left (hB : SympForm B) (a : W) : B 1 a = 0 := by
  have h := hB.mul_left 1 1 a
  rw [mul_one] at h
  have hc : ∀ x : ZMod 2, x = x + x → x = 0 := by decide
  exact hc _ h

theorem B_pw_right (hB : SympForm B) (a w : W) (c : ZMod 2) : B a (pw w c) = c * B a w := by
  have hc : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  rcases hc c with rfl | rfl
  · rw [pw_zero, B_one_right hB]; simp
  · rw [pw_one]; simp

theorem B_pw_left (hB : SympForm B) (a w : W) (c : ZMod 2) : B (pw w c) a = c * B w a := by
  have hc : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  rcases hc c with rfl | rfl
  · rw [pw_zero, B_one_left hB]; simp
  · rw [pw_one]; simp

end

theorem prod4_mul {W : Type*} [CommGroup W] (A B C D A' B' C' D' : W) :
    (A * B * C * D) * (A' * B' * C' * D') = (A * A') * (B * B') * (C * C') * (D * D') := by
  ac_rfl

theorem exists_symplectic_iso {W : Type*} [CommGroup W] {B : W → W → ZMod 2} (hB : SympForm B)
    (hW : Nat.card W = 16) :
    ∃ θ : W ≃* Multiplicative V4, ∀ a b, symp (Multiplicative.toAdd (θ a))
      (Multiplicative.toAdd (θ b)) = B a b := by
  have hz : ∀ x : ZMod 2, x + x = 0 := by decide
  have hsymm := hB.symm
  have hfin : Finite W := Nat.finite_of_card_ne_zero (by omega)
  obtain ⟨e₁, he₁⟩ : ∃ e₁ : W, e₁ ≠ 1 := by
    have : Nontrivial W := Finite.one_lt_card_iff_nontrivial.mp (by omega)
    exact exists_ne 1
  obtain ⟨f₁, hf₁⟩ : ∃ f₁ : W, B e₁ f₁ = 1 := by
    by_contra hcon
    push Not at hcon
    apply he₁
    apply hB.nondeg
    intro b
    have h1 := hcon b
    revert h1; generalize B e₁ b = c; revert c; decide
  obtain ⟨e₂, he₂1, he₂2, he₂⟩ : ∃ e₂ : W, B e₁ e₂ = 0 ∧ B f₁ e₂ = 0 ∧ e₂ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hinj : Function.Injective (fun x : W => (B e₁ x, B f₁ x)) := by
      intro x y hxy
      have h1 : B e₁ x = B e₁ y := (Prod.mk.inj hxy).1
      have h2 : B f₁ x = B f₁ y := (Prod.mk.inj hxy).2
      have hxy' : x * y = 1 := by
        have a1 : B e₁ (x * y) = 0 := by
          rw [hB.mul_right, h1]; exact hz _
        have a2 : B f₁ (x * y) = 0 := by
          rw [hB.mul_right, h2]; exact hz _
        exact hcon (x * y) a1 a2
      have : y = x⁻¹ := by
        rw [eq_inv_iff_mul_eq_one, mul_comm]; exact hxy'
      rw [this]
      have := hB.sq_eq_one x
      exact (inv_eq_of_mul_eq_one_right this).symm
    have hcard := Nat.card_le_card_of_injective _ hinj
    simp at hcard
    omega
  obtain ⟨y, hy⟩ : ∃ y : W, B e₂ y = 1 := by
    by_contra hcon
    push Not at hcon
    apply he₂
    apply hB.nondeg
    intro b
    have h1 := hcon b
    revert h1; generalize B e₂ b = c; revert c; decide
  set f₂ : W := y * pw e₁ (B f₁ y) * pw f₁ (B e₁ y) with hf₂def
  have g11 : B e₁ e₁ = 0 := hB.alt e₁
  have g22 : B f₁ f₁ = 0 := hB.alt f₁
  have g33 : B e₂ e₂ = 0 := hB.alt e₂
  have g44 : B f₂ f₂ = 0 := hB.alt f₂
  have g21 : B f₁ e₁ = 1 := by rw [hsymm]; exact hf₁
  have g31 : B e₂ e₁ = 0 := by rw [hsymm]; exact he₂1
  have g32 : B e₂ f₁ = 0 := by rw [hsymm]; exact he₂2
  have g13 : B e₁ e₂ = 0 := he₂1
  have g23 : B f₁ e₂ = 0 := he₂2
  have hb : ∀ a, B a f₂ = B a y + B f₁ y * B a e₁ + B e₁ y * B a f₁ := by
    intro a; simp only [hf₂def, hB.mul_right, B_pw_right hB]
  have g14 : B e₁ f₂ = 0 := by
    rw [hb, g11, hf₁]; have := hz (B e₁ y); simpa using this
  have g24 : B f₁ f₂ = 0 := by
    rw [hb, g21, g22]; have := hz (B f₁ y); simpa using this
  have g34 : B e₂ f₂ = 1 := by
    rw [hb, g31, g32, hy]; simp
  have g41 : B f₂ e₁ = 0 := by rw [hsymm]; exact g14
  have g42 : B f₂ f₁ = 0 := by rw [hsymm]; exact g24
  have g43 : B f₂ e₂ = 1 := by rw [hsymm]; exact g34
  let ψ : Multiplicative V4 →* W :=
    { toFun := fun x => pw e₁ (x.toAdd 0) * pw f₁ (x.toAdd 1) * pw e₂ (x.toAdd 2) *
        pw f₂ (x.toAdd 3)
      map_one' := by simp [pw_zero]
      map_mul' := by
        intro x y
        simp only [toAdd_mul, Pi.add_apply, pw_add (hB.sq_eq_one _)]
        exact (prod4_mul _ _ _ _ _ _ _ _).symm }
  have hψ : ∀ x : V4, ψ (Multiplicative.ofAdd x) = pw e₁ (x 0) * pw f₁ (x 1) * pw e₂ (x 2) *
      pw f₂ (x 3) := fun x => rfl
  have hiso : ∀ x y : V4,
      B (ψ (Multiplicative.ofAdd x)) (ψ (Multiplicative.ofAdd y)) = symp x y := by
    intro x y
    rw [hψ, hψ]
    simp only [hB.mul_left, hB.mul_right, B_pw_left hB, B_pw_right hB, g11, g22, g33, g44, g21, g31,
      g32, g13, g23, g14, g24, g34, g41, g42, g43, hf₁]
    unfold symp
    ring
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have : Multiplicative.toAdd x = 0 := by
      have hsy : ∀ y : V4, symp (Multiplicative.toAdd x) y = 0 := by
        intro y
        have := hiso (Multiplicative.toAdd x) y
        rw [ofAdd_toAdd, hx, B_one_left hB] at this
        exact this.symm
      revert hsy
      generalize Multiplicative.toAdd x = x0
      revert x0
      unfold symp
      decide
    exact this
  have hcard : Nat.card (Multiplicative V4) = 16 := by
    simp [Nat.card_eq_fintype_card]
  have hbij : Function.Bijective ψ :=
    (Nat.bijective_iff_injective_and_card ψ).mpr ⟨hinj, by rw [hcard, hW]⟩
  refine ⟨(MulEquiv.ofBijective ψ hbij).symm, fun a b => ?_⟩
  obtain ⟨a', rfl⟩ := hbij.2 a
  obtain ⟨b', rfl⟩ := hbij.2 b
  have hsa : ∀ x, (MulEquiv.ofBijective ψ hbij).symm (ψ x) = x := fun x =>
    (MulEquiv.ofBijective ψ hbij).symm_apply_apply x
  rw [hsa, hsa]
  have := hiso (Multiplicative.toAdd a') (Multiplicative.toAdd b')
  rw [ofAdd_toAdd, ofAdd_toAdd] at this
  exact this.symm

theorem pow_three_of_pow_nine : ∀ x : Equiv.Perm (Fin 6), x ^ 9 = 1 → x ^ 3 = 1 := by
  decide +kernel

theorem support_card_of_fix : ∀ x : Equiv.Perm (Fin 6), x ^ 3 = 1 → x ≠ 1 → ∀ a b : Fin 6,
    a ≠ b → x a = a → x b = b → x.support.card = 3 := by
  decide +kernel

theorem isThreeCycle_of_fix {x : Equiv.Perm (Fin 6)} (h3 : x ^ 3 = 1) (h1 : x ≠ 1)
    {a b : Fin 6} (hab : a ≠ b) (ha : x a = a) (hb : x b = b) : x.IsThreeCycle :=
  card_support_eq_three_iff.mp (support_card_of_fix x h3 h1 a b hab ha hb)

theorem pow_three_of_three_pow {x : Equiv.Perm (Fin 6)} {k : ℕ} (h : x ^ 3 ^ k = 1) :
    x ^ 3 = 1 := by
  have h1 : orderOf x ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one h
  have h2 : orderOf x ∣ 720 := by
    have := orderOf_dvd_card (G := Equiv.Perm (Fin 6)) (x := x)
    have h720 : Nat.factorial 6 = 720 := by decide
    simpa [Fintype.card_perm, h720] using this
  obtain ⟨m, hm, hmk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h1
  have hm2 : m ≤ 2 := by
    by_contra hcon
    have h27 : 27 ∣ 3 ^ m := by
      have : 3 ^ 3 ∣ 3 ^ m := pow_dvd_pow 3 (by omega)
      simpa using this
    rw [← hmk] at h27
    have := h27.trans h2
    omega
  have h9 : orderOf x ∣ 9 := by
    rw [hmk]
    interval_cases m <;> norm_num
  exact pow_three_of_pow_nine x (orderOf_dvd_iff_pow_eq_one.mp h9)

open scoped Pointwise in
theorem eq_alternatingGroup_of_duad_transitive (H : Subgroup (Equiv.Perm (Fin 6)))
    (hperf : commutator H = ⊤)
    (htr : ∀ a b c d : Fin 6, a ≠ b → c ≠ d → ∃ h ∈ H, ({h a, h b} : Finset (Fin 6)) = {c, d})
    (a b : Fin 6) (hab : a ≠ b) {x : Equiv.Perm (Fin 6)} (hx : x ∈ H) (hx1 : x ≠ 1)
    (hx3 : ∃ k : ℕ, x ^ 3 ^ k = 1) (hfix : ({x a, x b} : Finset (Fin 6)) = {a, b}) :
    H = alternatingGroup (Fin 6) := by
  obtain ⟨k, hk⟩ := hx3
  have hx3 : x ^ 3 = 1 := pow_three_of_three_pow hk
  have hle : H ≤ alternatingGroup (Fin 6) := by
    intro h hh
    rw [Equiv.Perm.mem_alternatingGroup]
    have hmem : (⟨h, hh⟩ : H) ∈ commutator H := by rw [hperf]; trivial
    have hker : commutator H ≤ (Equiv.Perm.sign.comp H.subtype).ker := by
      rw [commutator_def]
      refine Subgroup.commutator_le.mpr fun g₁ _ g₂ _ => ?_
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact mul_comm _ _
    simpa using hker hmem
  have hxab : x a = a ∧ x b = b := by
    have ha : x a ∈ ({a, b} : Finset (Fin 6)) := by rw [← hfix]; simp
    have hb : x b ∈ ({a, b} : Finset (Fin 6)) := by rw [← hfix]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with ha | ha
    · rcases hb with hb | hb
      · exact absurd (x.injective (ha.trans hb.symm)) hab
      · exact ⟨ha, hb⟩
    · rcases hb with hb | hb
      · exfalso
        have h3 : (x ^ 3) a = a := by rw [hx3]; rfl
        have h3' : (x ^ 3) a = x (x (x a)) := by simp [pow_succ, Equiv.Perm.mul_apply]
        rw [h3', ha, hb, ha] at h3
        exact hab h3.symm
      · exact absurd (x.injective (ha.trans hb.symm)) hab
  have h3cyc : x.IsThreeCycle := isThreeCycle_of_fix hx3 hx1 hab hxab.1 hxab.2
  have hpre : MulAction.IsPretransitive H (Fin 6) := by
    refine ⟨fun p q => ?_⟩
    by_cases hpq : p = q
    · exact ⟨1, by simp [hpq]⟩
    · obtain ⟨w, hwp, hwq⟩ : ∃ w : Fin 6, w ≠ p ∧ w ≠ q := by
        revert p q; decide
      obtain ⟨h, hh, hset⟩ := htr p w q w (Ne.symm hwp) (Ne.symm hwq)
      have h1 : h p ∈ ({q, w} : Finset (Fin 6)) := by rw [← hset]; simp
      have h2 : h w ∈ ({q, w} : Finset (Fin 6)) := by rw [← hset]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
      have hne : h p ≠ h w := fun e => hwp (h.injective e).symm
      rcases h1 with h1 | h1
      · rcases h2 with h2 | h2
        · exact absurd (h1.trans h2.symm) hne
        · exact ⟨⟨h, hh⟩, h1⟩
      · rcases h2 with h2 | h2
        · exact ⟨⟨h * h, H.mul_mem hh hh⟩, by
            show (h * h) p = q
            rw [Equiv.Perm.mul_apply, h1, h2]⟩
        · exact absurd (h1.trans h2.symm) hne
  have hprim : MulAction.IsPreprimitive H (Fin 6) := by
    refine { toIsPretransitive := hpre, isTrivialBlock_of_isBlock := ?_ }
    intro B hB
    by_contra hnt
    simp only [MulAction.IsTrivialBlock, not_or] at hnt
    obtain ⟨hns, hnu⟩ := hnt
    obtain ⟨p, hp, q, hq, hpq⟩ : ∃ p ∈ B, ∃ q ∈ B, p ≠ q := by
      by_contra hcon
      push Not at hcon
      exact hns (fun p hp q hq => hcon p hp q hq)
    obtain ⟨u, hu⟩ : ∃ u, u ∉ B := by
      by_contra hcon
      push Not at hcon
      exact hnu (Set.eq_univ_of_forall hcon)
    have hpu : p ≠ u := fun e => hu (e ▸ hp)
    obtain ⟨h, hh, hset⟩ := htr p q p u hpq hpu
    have hp' : p ∈ ((⟨h, hh⟩ : H) • B) := by
      have : p ∈ ({h p, h q} : Finset (Fin 6)) := by rw [hset]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with e | e
      · exact Set.mem_smul_set.mpr ⟨p, hp, e.symm⟩
      · exact Set.mem_smul_set.mpr ⟨q, hq, e.symm⟩
    have hu' : u ∈ ((⟨h, hh⟩ : H) • B) := by
      have : u ∈ ({h p, h q} : Finset (Fin 6)) := by rw [hset]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with e | e
      · exact Set.mem_smul_set.mpr ⟨p, hp, e.symm⟩
      · exact Set.mem_smul_set.mpr ⟨q, hq, e.symm⟩
    rcases (MulAction.isBlock_iff_smul_eq_or_disjoint.mp hB) ⟨h, hh⟩ with heq | hdis
    · exact hu (heq ▸ hu')
    · exact Set.disjoint_left.mp hdis hp' hp
  exact le_antisymm hle
    (Equiv.Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hprim h3cyc hx)

end CFSG.ClassicalInvolution.Q3.Sec13.Sp4
