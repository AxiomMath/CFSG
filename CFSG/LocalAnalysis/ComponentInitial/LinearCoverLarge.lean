module

public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverDiagonal
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace LinearCover

open Subgroup Matrix LinearFlag LinearFieldFour

theorem exists_ne_zero_ne_one_sq_add_ne_zero {K : Type*} [Field K] [Finite K] [CharP K 2]
    (hK : 4 < Nat.card K) : ∃ a : K, a ≠ 0 ∧ a ≠ 1 ∧ a ^ 2 + a + 1 ≠ 0 := by
  classical
  have := Fintype.ofFinite K
  obtain ⟨a₀, ha₀0, ha₀1⟩ := exists_ne_zero_ne_one_of_three_le (K := K) (by omega)
  by_contra h
  simp only [not_exists, not_and, not_not] at h
  have hsub : (Finset.univ : Finset K) ⊆ {0, 1, a₀, a₀ + 1} := fun a _ => by
    by_cases h0 : a = 0
    · simp [h0]
    by_cases h1 : a = 1
    · simp [h1]
    have ha := h a h0 h1
    have ha₀ := h a₀ ha₀0 ha₀1
    have hprod : (a + a₀) * (a + a₀ + 1) = 0 := by
      linear_combination ha + ha₀ + (a * a₀ - 1) * (CharP.cast_eq_zero K 2)
    rcases mul_eq_zero.mp hprod with h' | h'
    · simp [show a = a₀ by linear_combination h' - a₀ * (CharP.cast_eq_zero K 2)]
    · simp [show a = a₀ + 1 by linear_combination h' - (a₀ + 1) * (CharP.cast_eq_zero K 2)]
  have hle := Finset.card_le_card hsub
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at hle
  have h4 : ({0, 1, a₀, a₀ + 1} : Finset K).card ≤ 4 := by
    refine (Finset.card_insert_le _ _).trans (Nat.succ_le_succ ?_)
    refine (Finset.card_insert_le _ _).trans (Nat.succ_le_succ ?_)
    exact Finset.card_le_two
  omega

theorem binary_scalar_invariant_biadditive_map_zero {K A : Type*} [Field K] [Finite K]
    [CharP K 2] (hK : 4 < Nat.card K) [AddCommGroup A] (b : K → K → A)
    (hb₁ : ∀ x x' y, b (x + x') y = b x y + b x' y)
    (hb₂ : ∀ x y y', b x (y + y') = b x y + b x y')
    (hinv : ∀ a : K, a ≠ 0 → ∀ x y, b (a * x) (a * y) = b x y) : ∀ x y, b x y = 0 := by
  have h0 : ∀ y, b 0 y = 0 := fun y => by
    have h := hb₁ 0 0 y
    rw [add_zero] at h
    exact left_eq_add.mp h
  have h2 : ∀ x y, b x y + b x y = 0 := fun x y => by
    rw [← hb₁, CharTwo.add_self_eq_zero, h0]
  obtain ⟨a, ha0, ha1, ha2⟩ := exists_ne_zero_ne_one_sq_add_ne_zero hK
  have ha1' : a + 1 ≠ 0 := fun h => ha1 (by linear_combination h - CharP.cast_eq_zero K 2)
  have hkey : ∀ x y, b (a * x) y + b x (a * y) = b x y := fun x y => by
    have h := hinv (a + 1) ha1' x y
    rw [add_mul, add_mul, one_mul, one_mul, hb₁, hb₂, hb₂, hinv a ha0] at h
    have h' : b (a * x) y + b x (a * y) + (b x y + b x y) = b x y := by
      rw [show b (a * x) y + b x (a * y) + (b x y + b x y) =
        b x y + b (a * x) y + (b x (a * y) + b x y) by abel]
      exact h
    rwa [h2, add_zero] at h'
  have hshift : ∀ x y, b (a * x) y = b x (a⁻¹ * y) := fun x y => by
    have h := hinv a ha0 x (a⁻¹ * y)
    rwa [← mul_assoc, mul_inv_cancel₀ ha0, one_mul] at h
  have hc : a + a⁻¹ + 1 ≠ 0 := by
    intro h
    apply ha2
    have h' := congrArg (· * a) h
    simp only [zero_mul, add_mul, inv_mul_cancel₀ ha0, one_mul] at h'
    linear_combination h'
  intro x y
  have hz : b x ((a + a⁻¹ + 1) * ((a + a⁻¹ + 1)⁻¹ * y)) = 0 := by
    set y' := (a + a⁻¹ + 1)⁻¹ * y
    rw [add_mul, add_mul, one_mul, hb₂, hb₂, ← hshift, add_comm (b x (a * y')), hkey, h2]
  rwa [← mul_assoc, mul_inv_cancel₀ hc, one_mul] at hz


theorem exists_units_pow_three_ne_one {K : Type*} [Field K] [Finite K] (hK : 8 ≤ Nat.card K) :
    ∃ t : Kˣ, t ^ 3 ≠ 1 := by
  by_contra h
  simp only [not_exists, not_not] at h
  have hle : (⊤ : Subgroup Kˣ) ≤ rootsOfUnity 3 K := fun t _ => (mem_rootsOfUnity 3 t).mpr (h t)
  have h1 := Subgroup.card_le_of_le hle
  rw [Subgroup.card_top, Nat.card_units] at h1
  have h2 := card_rootsOfUnity K 3
  omega

theorem even_linear_three_large_field_catalog_central_two_cover_trivial {E : Type*} {J : Type}
    [Group E] [Group J] [Finite E] [Finite J] [Group.IsPerfect E] (η : E →* J)
    (hη : Function.Surjective η) (hC : η.ker ≤ center E) (h2 : IsPGroup 2 η.ker) {f : ℕ}
    (hf : 3 ≤ f) (hJ : CFSG.Blueprint.LieModel J .PSL 3 2 f) :
    η.ker = ⊥ ∧ Function.Bijective η := by
  obtain ⟨K, _, _, hcard, ⟨e⟩⟩ := exists_mulEquiv_projectiveSL_of_lieModel hJ
  have := finite_field_prime_power_characteristic (K := K) Nat.prime_two (by omega) hcard
  have hK8 : 8 ≤ Nat.card K := by
    rw [hcard]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  set η' : E →* projectiveSL 3 K := e.toMonoidHom.comp η with hη'def
  have hη' : Function.Surjective η' := e.surjective.comp hη
  have hker' : η'.ker = η.ker := by
    ext z
    exact e.map_eq_one_iff
  obtain ⟨tu, htu⟩ := exists_units_pow_three_ne_one hK8
  set t : K := (tu : K)
  have ht0 : t ≠ 0 := tu.ne_zero
  have ht3 : t ^ 3 ≠ 1 := fun h => htu (Units.ext (by rw [Units.val_pow_eq_pow_val, h]; rfl))
  have hs₁ : ![t, t, t⁻¹ * t⁻¹] 0 * ![t, t, t⁻¹ * t⁻¹] 1 * ![t, t, t⁻¹ * t⁻¹] 2 = 1 := by
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    field_simp
  have hs₂ : ![t⁻¹ * t⁻¹, t, t] 0 * ![t⁻¹ * t⁻¹, t, t] 1 * ![t⁻¹ * t⁻¹, t, t] 2 = 1 := by
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    field_simp
  set h₁ := diagSL ![t, t, t⁻¹ * t⁻¹] hs₁
  set h₂ := diagSL ![t⁻¹ * t⁻¹, t, t] hs₂
  have hv₁0 : ![t, t, t⁻¹ * t⁻¹] 0 = t := rfl
  have hv₁1 : ![t, t, t⁻¹ * t⁻¹] 1 = t := rfl
  have hv₁2 : ![t, t, t⁻¹ * t⁻¹] 2 = t⁻¹ * t⁻¹ := rfl
  have hv₂0 : ![t⁻¹ * t⁻¹, t, t] 0 = t⁻¹ * t⁻¹ := rfl
  have hv₂1 : ![t⁻¹ * t⁻¹, t, t] 1 = t := rfl
  have hv₂2 : ![t⁻¹ * t⁻¹, t, t] 2 = t := rfl
  obtain ⟨g₁, hg₁⟩ := hη' (proj 3 K h₁)
  obtain ⟨g₂, hg₂⟩ := hη' (proj 3 K h₂)
  set φ₁ := MulAut.conj g₁
  set φ₂ := MulAut.conj g₂
  have hφ : ∀ (g e : E), η' (MulAut.conj g e) = η' g * η' e * (η' g)⁻¹ := fun g e => by
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv]
  have hconjC : ∀ (g : E), ∀ z ∈ η'.ker, MulAut.conj g z = z := fun g z hz => by
    rw [MulAut.conj_apply, mem_center_iff.mp (hC (hker' ▸ hz)) g, mul_inv_cancel_right]
  have := Fintype.ofFinite K
  have hm : Odd (Nat.card K - 1) := by
    rw [hcard]
    exact Nat.Even.sub_odd Nat.one_le_two_pow ((Nat.even_pow' (by omega)).mpr even_two) odd_one
  have hφ₂m : φ₂ ^ (Nat.card K - 1) = 1 := by
    have hpow : h₂ ^ (Nat.card K - 1) = 1 := by
      apply Subtype.ext
      change (diagonal ![t⁻¹ * t⁻¹, t, t]) ^ (Nat.card K - 1) = 1
      rw [diagonal_pow, ← diagonal_one]
      congr 1
      funext i
      have hi : ![t⁻¹ * t⁻¹, t, t] i ≠ 0 := diag_ne_zero hs₂ i
      rw [Pi.pow_apply, Nat.card_eq_fintype_card]
      exact FiniteField.pow_card_sub_one_eq_one _ hi
    have hz : g₂ ^ (Nat.card K - 1) ∈ center E := hC (by
      rw [← hker', MonoidHom.mem_ker, map_pow, hg₂, ← map_pow, hpow, map_one])
    rw [← map_pow]
    ext x
    rw [MulAut.conj_apply, ← mem_center_iff.mp hz x, mul_inv_cancel_right, MulAut.one_apply]
  have hS : ∃ P : Sylow 2 (projectiveSL 3 K), (P : Subgroup _) = (projRoots (K := K)).S :=
    exists_sylow_projUnitriangular 2 (n := 3) (by norm_num)
  have hr₁ : t ^ 3 ≠ 1 := ht3
  have hr₂ : (t ^ 3)⁻¹ ≠ 1 := fun h => ht3 (inv_eq_one.mp h)
  have hbot := ker_eq_bot_of_two_weights (r₁ := t ^ 3) (r₂ := (t ^ 3)⁻¹) projRoots hS η' hη'
    (hker' ▸ hC) (hker' ▸ h2) φ₁ φ₂ hr₁ hr₂ (hconjC g₁) (hconjC g₂) hm hφ₂m
    (fun e₀ a he => by
      rw [hφ, hg₁, he]
      change proj 3 K h₁ * xP a * (proj 3 K h₁)⁻¹ = xP a
      rw [projDiag_conj_xP, hv₁0, hv₁1]
      field_simp)
    (fun e₀ c he => by
      rw [hφ, hg₁, he]
      change proj 3 K h₁ * wP c * (proj 3 K h₁)⁻¹ = wP (t ^ 3 * c)
      rw [projDiag_conj_wP, hv₁0, hv₁2]
      field_simp)
    (fun e₀ a he => by
      rw [hφ, hg₂, he]
      change proj 3 K h₂ * xP a * (proj 3 K h₂)⁻¹ = xP ((t ^ 3)⁻¹ * a)
      rw [projDiag_conj_xP, hv₂0, hv₂1]
      field_simp)
    (fun e₀ b he => by
      rw [hφ, hg₂, he]
      change proj 3 K h₂ * yP b * (proj 3 K h₂)⁻¹ = yP b
      rw [projDiag_conj_yP, hv₂1, hv₂2]
      field_simp)
    (fun e₀ c he => by
      rw [hφ, hg₂, he]
      change proj 3 K h₂ * wP c * (proj 3 K h₂)⁻¹ = wP ((t ^ 3)⁻¹ * c)
      rw [projDiag_conj_wP, hv₂0, hv₂2]
      field_simp)
  rw [hker'] at hbot
  exact ⟨hbot, (MonoidHom.ker_eq_bot_iff η).mp hbot, hη⟩

end LinearCover

end CFSG.LocalAnalysis.ComponentInitial
