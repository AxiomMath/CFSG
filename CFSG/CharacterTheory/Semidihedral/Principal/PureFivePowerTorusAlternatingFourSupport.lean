module

public import CFSG.CharacterTheory.Semidihedral.Principal.PureFivePowerTorusColumn
public import CFSG.CharacterTheory.Semidihedral.Principal.SignSymmetricFivePowerInvolutionSum
public import CFSG.CharacterTheory.Semidihedral.Principal.ParameterElevenTorusQuotientSupport

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers CFSG.LyonsUnitaryFour

namespace PureFiveAlternatingFour

theorem alternating_five_column_rational {K : Type*} [Field K] [CharZero K]
    {G c q e a₀ b₀ z₀ : K} (he : e = 1 ∨ e = -1)
    (hq0 : q ≠ 0) (hc : c ≠ 0) (ha0 : a₀ ≠ 0) (hb0 : b₀ ≠ 0) (ha1 : a₀ + 1 ≠ 0)
    (hden : a₀ - e * q ≠ 0) (hbz : b₀ - z₀ ≠ 0) (hsum : 1 + a₀ + b₀ + z₀ = 0)
    (hprod : a₀ * b₀ = q ^ 2 * z₀)
    (hord : G / c ^ 2 = (q - e) / 2 * (a₀ * (a₀ + 1)) / (a₀ - e * q) ^ 2)
    (hcol : G * (-q ^ 2 / b₀ + 1 / z₀ + (1 - e * q) ^ 2 / (b₀ - z₀)) = -c ^ 2 * (q + e) / 6) :
    (2 * q - e) * a₀ = -q ^ 2 * (q - 2 * e) := by
  have h2 : b₀ * (q ^ 2 + a₀) = -q ^ 2 * (1 + a₀) := by linear_combination q ^ 2 * hsum + hprod
  have hqa : q ^ 2 - a₀ ≠ 0 := by
    intro h
    apply hbz
    have h' : q ^ 2 * (b₀ - z₀) = 0 := by linear_combination b₀ * h + hprod
    rcases mul_eq_zero.mp h' with h'' | h''
    · exact absurd (pow_eq_zero_iff two_ne_zero |>.mp h'') hq0
    · exact h''
  have hz : z₀ = a₀ * b₀ / q ^ 2 := by
    rw [eq_div_iff (pow_ne_zero 2 hq0)]
    linear_combination -hprod
  have hG : G = c ^ 2 * ((q - e) / 2 * (a₀ * (a₀ + 1)) / (a₀ - e * q) ^ 2) := by
    rw [div_eq_iff (pow_ne_zero 2 hc)] at hord
    rw [hord]
    ring
  have hbr : -q ^ 2 / b₀ + 1 / z₀ + (1 - e * q) ^ 2 / (b₀ - z₀) =
      q ^ 2 * (a₀ - e * q) ^ 2 / (a₀ * b₀ * (q ^ 2 - a₀)) := by
    have hbz' : b₀ - z₀ = b₀ * (q ^ 2 - a₀) / q ^ 2 := by
      rw [hz]
      field_simp
    rw [hbz', hz]
    rcases he with rfl | rfl <;> field_simp <;> ring
  rw [hG, hbr] at hcol
  have hsimp : c ^ 2 * ((q - e) / 2 * (a₀ * (a₀ + 1)) / (a₀ - e * q) ^ 2) *
      (q ^ 2 * (a₀ - e * q) ^ 2 / (a₀ * b₀ * (q ^ 2 - a₀))) =
      c ^ 2 * ((q - e) * (a₀ + 1) * q ^ 2 / (2 * b₀ * (q ^ 2 - a₀))) := by
    have hden' : a₀ - q * e ≠ 0 := by rwa [mul_comm] at hden
    field_simp
  rw [hsimp] at hcol
  have h1 : (q - e) * (a₀ + 1) * q ^ 2 / (2 * b₀ * (q ^ 2 - a₀)) = -(q + e) / 6 :=
    mul_left_cancel₀ (pow_ne_zero 2 hc) (hcol.trans (by ring))
  rw [div_eq_iff (mul_ne_zero (mul_ne_zero two_ne_zero hb0) hqa)] at h1
  have hstar : 3 * ((q - e) * (a₀ + 1) * q ^ 2) + (q + e) * b₀ * (q ^ 2 - a₀) = 0 := by
    linear_combination 3 * h1
  have hkey : (q ^ 2 * (a₀ + 1)) * (3 * (q - e) * (q ^ 2 + a₀) - (q + e) * (q ^ 2 - a₀)) = 0 := by
    linear_combination (q ^ 2 + a₀) * hstar - (q + e) * (q ^ 2 - a₀) * h2
  have h3 := (mul_eq_zero.mp hkey).resolve_left (mul_ne_zero (pow_ne_zero 2 hq0) ha1)
  linear_combination h3 / 2

theorem two_q_sub_e_false {q e a₀ : ℤ} (hq : 3 < q) (he : e = 1 ∨ e = -1)
    (h : (2 * q - e) * a₀ = -q ^ 2 * (q - 2 * e)) : False := by
  have hcop : IsCoprime (2 * q - e) (q ^ 2) := by
    apply IsCoprime.pow_right
    refine ⟨-e, 2 * e, ?_⟩
    rcases he with rfl | rfl <;> ring
  have hdvd : 2 * q - e ∣ q ^ 2 * (q - 2 * e) := ⟨-a₀, by linear_combination h⟩
  have h2 := hcop.dvd_of_dvd_mul_left hdvd
  have hpos : 0 < q - 2 * e := by rcases he with rfl | rfl <;> omega
  have hle := Int.le_of_dvd hpos h2
  rcases he with rfl | rfl <;> omega

theorem alternating_five_column_false {cardG c q f₁ f₂ f₃ a : ℕ} {e δ₁ δ₂ δ₃ η : ℤ}
    (hq : 3 < q) (he : e = 1 ∨ e = -1) (hη : η = 1 ∨ η = -1)
    (hsigns : (δ₁ = -1 ∧ δ₂ = -1 ∧ δ₃ = 1) ∨ (δ₁ = -1 ∧ δ₂ = 1 ∧ δ₃ = -1) ∨
      (δ₁ = 1 ∧ δ₂ = -1 ∧ δ₃ = -1))
    (hf₁ : 1 < f₁) (hf₂ : 1 < f₂)
    (hsum : 1 + δ₁ * (f₁ : ℤ) + δ₂ * f₂ + δ₃ * f₃ = 0) (hprod : f₁ * f₂ = q ^ 2 * f₃)
    (hBpos : 0 < η * (δ₂ * (f₂ : ℤ) - δ₃ * f₃)) (hden : (f₁ : ℚ) - e * δ₁ * q ≠ 0)
    (hc : c ≠ 0) (hm : 2 * (5 : ℤ) ^ a = q + e)
    (hord : (cardG : ℚ) / (c : ℚ) ^ 2 =
      ((q - e) / 2) * (f₁ * (f₁ + δ₁)) / (f₁ - e * δ₁ * q) ^ 2)
    (hpair : (cardG : ℂ) * (-(δ₂ : ℂ) * ((q : ℂ) ^ 2 / (f₂ : ℂ)) + (δ₃ : ℂ) * (1 / (f₃ : ℂ)) +
        (η : ℂ) * ((1 - (e : ℂ) * q) ^ 2 / ((η : ℂ) * ((δ₂ : ℂ) * f₂ - (δ₃ : ℂ) * f₃)))) =
      (c : ℂ) ^ 2 * (-(5 : ℂ) ^ a / 3)) :
    False := by
  obtain ⟨hδ₁, hδ₂, hδ₃, hδ₁₂⟩ : (δ₁ = 1 ∨ δ₁ = -1) ∧ (δ₂ = 1 ∨ δ₂ = -1) ∧
      (δ₃ = 1 ∨ δ₃ = -1) ∧ δ₁ * δ₂ = δ₃ := by
    rcases hsigns with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> norm_num
  have hsq : ∀ x : ℤ, (x = 1 ∨ x = -1) → (x : ℂ) ^ 2 = 1 := by
    rintro x (rfl | rfl) <;> norm_num
  have hne : ∀ x : ℤ, (x = 1 ∨ x = -1) → (x : ℂ) ≠ 0 := by
    rintro x (rfl | rfl) <;> norm_num
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  have hf₁0 : (f₁ : ℂ) ≠ 0 := by exact_mod_cast (by omega : f₁ ≠ 0)
  have hf₂0 : (f₂ : ℂ) ≠ 0 := by exact_mod_cast (by omega : f₂ ≠ 0)
  have ha1 : (δ₁ : ℂ) * f₁ + 1 ≠ 0 := by
    have h : δ₁ * (f₁ : ℤ) + 1 ≠ 0 := by rcases hδ₁ with rfl | rfl <;> omega
    exact_mod_cast h
  have hbz : (δ₂ : ℂ) * f₂ - δ₃ * f₃ ≠ 0 := by
    have h : δ₂ * (f₂ : ℤ) - δ₃ * f₃ ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hBpos
      exact lt_irrefl 0 hBpos
    exact_mod_cast h
  have hdenC : (f₁ : ℂ) - e * δ₁ * q ≠ 0 := by
    have h : (f₁ : ℤ) - e * δ₁ * q ≠ 0 := by
      intro h0
      apply hden
      exact_mod_cast h0
    exact_mod_cast h
  have hden' : (δ₁ : ℂ) * f₁ - e * q ≠ 0 := by
    have h : (δ₁ : ℂ) * f₁ - e * q = δ₁ * (f₁ - e * δ₁ * q) := by
      linear_combination (e * q : ℂ) * hsq δ₁ hδ₁
    rw [h]
    exact mul_ne_zero (hne δ₁ hδ₁) hdenC
  have heC : (e : ℂ) = 1 ∨ (e : ℂ) = -1 := by rcases he with h | h <;> simp [h]
  have hsumC : 1 + (δ₁ : ℂ) * f₁ + δ₂ * f₂ + δ₃ * f₃ = 0 := by exact_mod_cast hsum
  have hprodC : ((δ₁ : ℂ) * f₁) * (δ₂ * f₂) = (q : ℂ) ^ 2 * (δ₃ * f₃) := by
    have h1 : (f₁ : ℂ) * f₂ = q ^ 2 * f₃ := by exact_mod_cast hprod
    have h2 : (δ₁ : ℂ) * δ₂ = δ₃ := by exact_mod_cast hδ₁₂
    linear_combination (δ₁ * δ₂ : ℂ) * h1 + (q ^ 2 * f₃ : ℂ) * h2
  have hordC : (cardG : ℂ) / (c : ℂ) ^ 2 = ((q : ℂ) - e) / 2 * ((δ₁ * f₁) * (δ₁ * f₁ + 1)) /
      (δ₁ * f₁ - e * q) ^ 2 := by
    have h := congrArg (Rat.cast : ℚ → ℂ) hord
    push_cast at h
    rw [h]
    have h1 : (f₁ : ℂ) * (f₁ + δ₁) = (δ₁ * f₁) * (δ₁ * f₁ + 1) := by
      linear_combination (-(f₁ : ℂ) ^ 2) * hsq δ₁ hδ₁
    have h2 : ((f₁ : ℂ) - e * δ₁ * q) ^ 2 = (δ₁ * f₁ - e * q) ^ 2 := by
      linear_combination ((e * q : ℂ) ^ 2 - (f₁ : ℂ) ^ 2) * hsq δ₁ hδ₁
    rw [h1, h2]
  have T1 : -(δ₂ : ℂ) * ((q : ℂ) ^ 2 / f₂) = -(q : ℂ) ^ 2 / (δ₂ * f₂) := by
    rcases hδ₂ with h | h <;> rw [h] <;> push_cast <;> ring
  have T2 : (δ₃ : ℂ) * (1 / (f₃ : ℂ)) = 1 / (δ₃ * f₃) := by
    rcases hδ₃ with h | h <;> rw [h] <;> push_cast <;> ring
  have T3 : (η : ℂ) * ((1 - e * q) ^ 2 / (η * (δ₂ * f₂ - δ₃ * f₃))) =
      (1 - e * q) ^ 2 / (δ₂ * f₂ - δ₃ * f₃) := by
    rw [mul_div_assoc', mul_div_mul_left _ _ (hne η hη)]
  have hcolC : (cardG : ℂ) * (-(q : ℂ) ^ 2 / (δ₂ * f₂) + 1 / (δ₃ * f₃) +
      (1 - e * q) ^ 2 / (δ₂ * f₂ - δ₃ * f₃)) = -(c : ℂ) ^ 2 * (q + e) / 6 := by
    rw [← T1, ← T2, ← T3, hpair]
    have hmC : (5 : ℂ) ^ a = ((q : ℂ) + e) / 2 := by
      have h : (2 * 5 ^ a : ℂ) = q + e := by exact_mod_cast hm
      linear_combination h / 2
    rw [hmC]
    ring
  have hfinal := alternating_five_column_rational heC hq0 hc0 (mul_ne_zero (hne δ₁ hδ₁) hf₁0)
    (mul_ne_zero (hne δ₂ hδ₂) hf₂0) ha1 hden' hbz hsumC hprodC hordC hcolC
  have hZ : (2 * (q : ℤ) - e) * (δ₁ * f₁) = -(q : ℤ) ^ 2 * (q - 2 * e) := by exact_mod_cast hfinal
  exact two_q_sub_e_false (by exact_mod_cast hq) he hZ

theorem characterPairing_three_left {G : Type*} [Group G] [Fintype G] (f₂ f₃ fB F : G → ℂ)
    (c₂ c₃ cB : ℂ) :
    characterPairing (fun g => c₂ * f₂ g + c₃ * f₃ g + cB * fB g) F =
      c₂ * characterPairing f₂ F + c₃ * characterPairing f₃ F + cB * characterPairing fB F := by
  unfold characterPairing
  have h : ∀ x : G, (c₂ * f₂ x + c₃ * f₃ x + cB * fB x) * F x⁻¹ =
      c₂ * (f₂ x * F x⁻¹) + c₃ * (f₃ x * F x⁻¹) + cB * (fB x * F x⁻¹) := fun x => by ring
  simp_rw [h, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

theorem characterPairing_involution_square_sum {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (t : G) (c : basis.index) :
    characterPairing (basis.representation c).character
      (fun g => ∑ χ, (basis.representation χ).character t * (basis.representation χ).character t *
        (basis.representation χ).character g / (basis.representation χ).character 1) =
    (basis.representation c).character t * (basis.representation c).character t /
      (basis.representation c).character 1 := by
  have hF : (fun g => ∑ χ, (basis.representation χ).character t *
      (basis.representation χ).character t * (basis.representation χ).character g /
        (basis.representation χ).character 1) = fun g => ∑ χ ∈ Finset.univ,
      ((basis.representation χ).character t * (basis.representation χ).character t /
        (basis.representation χ).character 1) * (basis.representation χ).character g := by
    funext g
    refine Finset.sum_congr rfl fun χ _ => ?_
    ring
  rw [hF, characterPairing_finset_expansion_right]
  simp only [characterPairing_basis, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq Finset.univ c, ite_eq_left (Finset.mem_univ c)]

theorem localized_involution_square_sum {G : Type} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (H : Subgroup G)
    (localBasis : FiniteIrreducibleCharacterBasis H) (t : G)
    (hinvol : ∀ x : G, orderOf x = 2 ↔ IsConj x t) (y : H)
    (hy : extendedCentralizer (y : G) ≤ H) :
    (Nat.card G : ℂ) * ∑ χ, (basis.representation χ).character t *
        (basis.representation χ).character t * (basis.representation χ).character y /
          (basis.representation χ).character 1 =
      (Nat.card (Subgroup.centralizer ({t} : Set G)) : ℂ) ^ 2 * (Nat.card H : ℂ) *
        ∑ α, ((Nat.card H : ℂ)⁻¹ * ∑ u ∈ Finset.univ.filter (fun u : H => orderOf u = 2),
          (localBasis.representation α).character u) ^ 2 *
            (localBasis.representation α).character y /
              (localBasis.representation α).character 1 := by
  have ht2 : orderOf t = 2 := (hinvol t).mpr (IsConj.refl t)
  have htt : t * t = 1 := by rw [← sq, ← ht2, pow_orderOf_eq_one]
  have hG := involution_classes_product_character_formula basis t t htt htt (y : G)
  rw [productCount_conjClassFinset_eq H htt htt y hy,
    productCount_classInter H localBasis htt htt y] at hG
  have hcw : ∀ ψ : H → ℂ, classWeight H ψ t =
      (Nat.card H : ℂ)⁻¹ * ∑ x ∈ Finset.univ.filter (fun x : H => orderOf x = 2), ψ x := by
    intro ψ
    rw [classWeight, Finset.sum_filter]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    have hx : IsConj (x : G) t ↔ orderOf x = 2 := by rw [← hinvol, Subgroup.orderOf_coe]
    by_cases h : orderOf x = 2
    · rw [ite_eq_left (hx.mpr h), ite_eq_left h]
    · rw [ite_eq_right (fun h' => h (hx.mp h')), ite_eq_right h]
  simp_rw [hcw] at hG
  rw [← hG]
  simp only [← sq]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  ring

theorem pairing_transfer {G : Type} [Group G] [Fintype G] (K H : Subgroup G) (hKH : K ≤ H)
    (ψ : K → ℂ) (FG : G → ℂ) (FH : H → ℂ) (X : ℂ)
    (hloc : ∀ k : K, ψ k ≠ 0 →
      (Nat.card G : ℂ) * FG ((k⁻¹ : K) : G) = X * FH ⟨((k⁻¹ : K) : G), hKH k⁻¹.2⟩) :
    (Nat.card G : ℂ) * characterPairing ψ (fun k : K => FG k) =
      X * characterPairing ψ (fun k : K => FH ⟨k, hKH k.2⟩) := by
  have h : ∀ k : K, (Nat.card G : ℂ) * (ψ k * FG ((k⁻¹ : K) : G)) =
      X * (ψ k * FH ⟨((k⁻¹ : K) : G), hKH k⁻¹.2⟩) := by
    intro k
    by_cases hk : ψ k = 0
    · rw [hk]
      ring
    · calc (Nat.card G : ℂ) * (ψ k * FG ((k⁻¹ : K) : G)) =
            ψ k * ((Nat.card G : ℂ) * FG ((k⁻¹ : K) : G)) := by ring
        _ = ψ k * (X * FH ⟨((k⁻¹ : K) : G), hKH k⁻¹.2⟩) := by rw [hloc k hk]
        _ = X * (ψ k * FH ⟨((k⁻¹ : K) : G), hKH k⁻¹.2⟩) := by ring
  unfold characterPairing
  rw [mul_left_comm, mul_left_comm X]
  congr 1
  rw [Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => h k

theorem extendedCentralizer_le_normalizer_of_generator {G : Type*} [Group G] (W : Subgroup G)
    {a : ℕ} (hWcard : Nat.card W = 5 ^ a) {w j : G} (hw : Subgroup.zpowers w = W)
    (hwj : Commute w j) (hj : Nat.Coprime 5 (orderOf j)) :
    extendedCentralizer (w * j) ≤ Subgroup.normalizer (W : Set G) := by
  have hwo : orderOf w ∣ 5 ^ a := by rw [← hWcard, ← hw, Nat.card_zpowers]
  obtain ⟨-, -, -, -, -, hext⟩ := involution_product_extended_centralizer_localization (w * j)
    (∅ : Finset G) ∅ (by simp) (by simp)
  refine (hext 5 w j a hwo hwj hj).trans ?_
  rw [← hw]
  exact ParameterElevenTorus.extendedCentralizer_le_normalizer_zpowers w

theorem local_generator_column_pairing {G : Type} [Group G] [Fintype G]
    (W J E H K : Subgroup G) [IsCyclic W] (a : ℕ) (ha : 1 ≤ a) (hWcard : Nat.card W = 5 ^ a)
    (hWH : W ≤ H) [hWn : (W.subgroupOf H).Normal] (hEH : E ≤ H) (hWE : W ⊔ E = H)
    (hWEd : W ⊓ E = ⊥) (hJE : J ≤ E) (hK : W ⊔ J = K) (hKH : K ≤ H)
    (σ : E ≃* Equiv.Perm (Fin 5))
    (hσJ : ∀ x : E, (x : G) ∈ J ↔ σ x ∈ alternatingGroup (Fin 5))
    (hact : ∀ x : E, ∀ w ∈ W,
      (x : G) * w * (x : G)⁻¹ = w ^ ((Equiv.Perm.sign (σ x) : ℤˣ) : ℤ))
    (eJ : J ≃* alternatingGroup (Fin 5)) (t : G) (htJ : t ∈ J) (ht2 : orderOf t = 2)
    (lam : W →* ℂˣ) (hlam : orderOf lam = 5) (ψ : K → ℂ)
    (hψ : ∀ (k : K) (w : W) (j : J), (k : G) = w * j →
      ψ k = ((Nat.card (MulAction.fixedBy (Sylow 5 J) j) : ℂ) - 1) * ((lam w : ℂ) - 1))
    (localBasis : FiniteIrreducibleCharacterBasis H) :
    (Nat.card H : ℂ) * characterPairing ψ (fun k : K => ∑ α : localBasis.index,
      ((Nat.card H : ℂ)⁻¹ * ∑ u ∈ Finset.univ.filter (fun u : H => orderOf u = 2),
        (localBasis.representation α).character u) ^ 2 *
          (localBasis.representation α).character ⟨k, hKH k.2⟩ /
            (localBasis.representation α).character 1) = -(5 ^ a : ℂ) / 3 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set W' : Subgroup H := W.subgroupOf H with hW'def
  set E' : Subgroup H := E.subgroupOf H with hE'def
  set σ' : E' ≃* Equiv.Perm (Fin 5) := (Subgroup.subgroupOfEquivOfLe hEH).trans σ with hσ'def
  have : IsCyclic W' := isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hWH).symm.toMonoidHom
    (Subgroup.subgroupOfEquivOfLe hWH).symm.surjective
  have hW'card : Nat.card W' = 5 ^ a := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWH).toEquiv, hWcard]
  have hW'E' : W' ⊔ E' = ⊤ := by
    rw [hW'def, hE'def, ← Subgroup.subgroupOf_sup hWH hEH, hWE, Subgroup.subgroupOf_self]
  have hdisj' : W' ⊓ E' = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hmem : (x : G) ∈ W ⊓ E := ⟨hx.1, hx.2⟩
    rw [hWEd, Subgroup.mem_bot] at hmem
    exact Subgroup.mem_bot.mpr (Subtype.ext hmem)
  have hact' : ∀ (e' : E'), ∀ w' ∈ W', (e' : H) * w' * (e' : H)⁻¹ =
      w' ^ ((Equiv.Perm.sign (σ' e') : ℤˣ) : ℤ) := by
    intro e' w' hw'
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow]
    exact hact (Subgroup.subgroupOfEquivOfLe hEH e') (w' : G) hw'
  set lam' : W' →* ℂˣ := lam.comp (Subgroup.subgroupOfEquivOfLe hWH).toMonoidHom with hlam'def
  have hlam' : orderOf lam' = 5 := by
    have hlam5 : lam ^ 5 = 1 := hlam ▸ pow_orderOf_eq_one lam
    apply orderOf_eq_prime
    · rw [hlam'def]
      ext w
      simp only [MonoidHom.pow_apply, MonoidHom.comp_apply, MonoidHom.one_apply]
      rw [← MonoidHom.pow_apply, hlam5, MonoidHom.one_apply]
    · intro h1
      have hne : lam ≠ 1 := by
        rintro rfl
        rw [orderOf_one] at hlam
        norm_num at hlam
      apply hne
      ext w
      have h := congrArg (fun φ : W' →* ℂˣ => (φ ((Subgroup.subgroupOfEquivOfLe hWH).symm w) : ℂ))
        h1
      simpa [hlam'def] using h
  obtain ⟨-, -, -, hall⟩ := sign_symmetric_five_power_normalizer_generator_column_involution_sum a
    ha W' E' hW'card hW'E' hdisj' σ' hact' localBasis lam' hlam'
  set J' : Subgroup H := ((alternatingGroup (Fin 5)).comap σ'.toMonoidHom).map E'.subtype
    with hJ'def
  have hJ'mem : ∀ x : H, x ∈ J' ↔ (x : G) ∈ J := by
    intro x
    constructor
    · rintro ⟨e', he', rfl⟩
      have h := (hσJ (Subgroup.subgroupOfEquivOfLe hEH e')).mpr he'
      exact h
    · intro hx
      have hxE : (x : G) ∈ E := hJE hx
      refine ⟨⟨x, hxE⟩, ?_, rfl⟩
      exact (hσJ ⟨(x : G), hxE⟩).mp hx
  have hK'mem : ∀ x : H, x ∈ W' ⊔ J' ↔ (x : G) ∈ K := by
    intro x
    have hmap : (W' ⊔ J').map H.subtype = K := by
      rw [Subgroup.map_sup, ← hK]
      congr 1
      · rw [hW'def, Subgroup.subgroupOf_map_subtype, inf_of_le_left hWH]
      · ext y
        constructor
        · rintro ⟨z, hz, rfl⟩
          exact (hJ'mem z).mp hz
        · intro hy
          exact ⟨⟨y, hEH (hJE hy)⟩, (hJ'mem _).mpr hy, rfl⟩
    rw [← hmap]
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨z, hz, hzx⟩
      rwa [Subtype.ext hzx] at hz
  set ι : (W' ⊔ J' : Subgroup H) → K := fun k' => ⟨((k' : H) : G), (hK'mem k').mp k'.2⟩
    with hιdef
  have hιbij : Function.Bijective ι := by
    constructor
    · intro x y hxy
      have h := congrArg Subtype.val hxy
      exact Subtype.ext (Subtype.ext h)
    · intro k
      refine ⟨⟨⟨k, hKH k.2⟩, (hK'mem ⟨k, hKH k.2⟩).mpr k.2⟩, rfl⟩
  set ψ' : (W' ⊔ J' : Subgroup H) → ℂ := fun k' => ψ (ι k') with hψ'def
  have hψ' : ∀ (k' : (W' ⊔ J' : Subgroup H)) (w' : W') (j' : J'), (k' : H) = w' * j' →
      ψ' k' = ((Nat.card (MulAction.fixedBy (Sylow 5 J') j') : ℂ) - 1) * ((lam' w' : ℂ) - 1) := by
    intro k' w' j' hk'
    have hjJ : ((j' : H) : G) ∈ J := (hJ'mem j').mp j'.2
    have h := hψ (ι k') ⟨((w' : H) : G), w'.2⟩ ⟨((j' : H) : G), hjJ⟩
      (by rw [hιdef]; exact congrArg Subtype.val hk')
    rw [hψ'def]
    simp only at h ⊢
    rw [h]
    have hθ : FiveKernel.sylowAugmentation J ⟨((j' : H) : G), hjJ⟩ =
        FiveKernel.sylowAugmentation J' j' := by
      apply FivePowerColumn.sylowAugmentation_eq_of_orderOf_eq eJ (SignSymmetric.eJ σ')
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    have hθ' := hθ
    unfold FiveKernel.sylowAugmentation at hθ'
    rw [hθ']
    rfl
  have htH : t ∈ H := hEH (hJE htJ)
  have htJ' : (⟨t, htH⟩ : H) ∈ J' := (hJ'mem _).mpr htJ
  have ht2' : orderOf (⟨t, htH⟩ : H) = 2 := by rw [Subgroup.orderOf_mk]; exact ht2
  set x' : E' := (Subgroup.subgroupOfEquivOfLe hEH).symm (σ.symm (Equiv.swap 0 1)) with hx'def
  have hx' : (σ' x').IsSwap := by
    refine ⟨0, 1, by decide, ?_⟩
    rw [hσ'def, hx'def, MulEquiv.trans_apply, MulEquiv.apply_symm_apply,
      MulEquiv.apply_symm_apply]
  obtain ⟨-, -, -, -, -, -, -, -, -, hfinal⟩ := hall ψ' hψ' ⟨t, htH⟩ htJ' ht2' x' hx'
  set FH : H → ℂ := fun h => ∑ α : localBasis.index,
    ((Nat.card H : ℂ)⁻¹ * ∑ u ∈ Finset.univ.filter (fun u : H => orderOf u = 2),
      (localBasis.representation α).character u) ^ 2 *
        (localBasis.representation α).character h / (localBasis.representation α).character 1
    with hFHdef
  have hFHclass : ∀ h c : H, FH (c * h * c⁻¹) = FH h := by
    intro h c
    rw [hFHdef]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [show (localBasis.representation α).character (c * h * c⁻¹) =
      (localBasis.representation α).character h from Representation.char_conj _ h c]
  have hexp : ∑ α : localBasis.index, characterPairing (inducedFunction (W' ⊔ J') ψ')
      (localBasis.representation α).character * ((Nat.card H : ℂ)⁻¹ *
        ∑ u ∈ Finset.univ.filter (fun u : H => orderOf u = 2),
          (localBasis.representation α).character u) ^ 2 /
        (localBasis.representation α).character 1 =
      characterPairing (inducedFunction (W' ⊔ J') ψ') FH := by
    have hFH : FH = fun h => ∑ α ∈ Finset.univ, (((Nat.card H : ℂ)⁻¹ *
        ∑ u ∈ Finset.univ.filter (fun u : H => orderOf u = 2),
          (localBasis.representation α).character u) ^ 2 /
            (localBasis.representation α).character 1) *
        (localBasis.representation α).character h := by
      rw [hFHdef]
      funext h
      refine Finset.sum_congr rfl fun α _ => ?_
      ring
    rw [hFH, characterPairing_finset_expansion_right]
    refine Finset.sum_congr rfl fun α _ => ?_
    ring
  have hfrob := characterPairing_inducedFunction_left (W' ⊔ J') ψ' FH hFHclass
  have htrans : characterPairing ψ' (fun k' : (W' ⊔ J' : Subgroup H) => FH k') =
      characterPairing ψ (fun k : K => FH ⟨k, hKH k.2⟩) := by
    unfold characterPairing
    have hcard : Nat.card (W' ⊔ J' : Subgroup H) = Nat.card K :=
      Nat.card_congr (Equiv.ofBijective ι hιbij)
    rw [hcard]
    congr 1
    exact Fintype.sum_bijective ι hιbij _ _ fun k' => rfl
  rw [← htrans, ← hfrob, ← hexp]
  exact hfinal

section Alternative

open CFSG.Semidihedral.ActualSimpleLayerLocalPackage CFSG.Open

theorem alternating_five_alternative_false
    {G : Type} [Group G] [Fintype G] [Group.IsPerfect G] (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G)
    (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (t : G)
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 3 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (hN : N t = ⊥)
    (hY : (((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).index = 2)
    (a : ℕ) (ha : 1 ≤ a) :
    let q : ℕ := p ^ f
    let e : ℤ := if q % 4 = 1 then 1 else -1
    let s₀ : G := fS (s n)
    let V : Subgroup G := Subgroup.zpowers t ⊔ Subgroup.zpowers s₀
    let D : Subgroup G := Subgroup.centralizer (V : Set G)
    let W : Subgroup G := (CFSG.pPrimeCore 2 D).map D.subtype
    let K : Subgroup G := Subgroup.centralizer (W : Set G)
    ((q : ℤ) + e) / 2 = 5 ^ a →
    ¬ Nonempty ((K ⧸ CFSG.pPrimeCore 2 K) ≃* alternatingGroup (Fin 5)) := by
  intro q e s₀ V D W K hqa hK5
  set H : Subgroup G := Subgroup.normalizer (W : Set G) with hHdef
  set J : Subgroup G := ⁅K, K⁆ with hJdef
  have hq' : 3 < q := hq
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨-, ht2, -, -, -, -⟩ := supplied_t_s_facts hn fS ht
  obtain ⟨basis⟩ := finiteIrreducibleCharacterBasis_exists (G := G)
  obtain ⟨principal, hprincipal⟩ := finiteIrreducibleCharacterBasis_contains_irreducible basis
    (principalFiniteComplexRepresentation G) (principalFiniteComplexRepresentation_isIrreducible G)
  rw [principalFiniteComplexRepresentation_character] at hprincipal
  obtain ⟨⟨ideal₂, hmax₂, h2mem⟩, hchar₂⟩ := CFSG.BlockBasics.residue_prime_existence 2
    Nat.prime_two
  have : ideal₂.IsMaximal := hmax₂
  have : CharP (ComplexAlgebraicIntegers ⧸ ideal₂) 2 := hchar₂ ideal₂ hmax₂ h2mem
  obtain ⟨⟨ideal₅, hmax₅, h5mem⟩, hchar₅⟩ := CFSG.BlockBasics.residue_prime_existence 5
    (by norm_num)
  have : ideal₅.IsMaximal := hmax₅
  have : CharP (ComplexAlgebraicIntegers ⧸ ideal₅) 5 := hchar₅ ideal₅ hmax₅ h5mem
  obtain ⟨hWcyc, hW5, hWJ, hWJd, hcomm, hJiso, htJ, hC, ⟨E, σ, hEH, hJE, hWE, hWEd, hσJ, hact⟩,
      -, -, -, hcol⟩ :=
    perfect_pure_five_power_alternating_five_torus_column_aligns_two_odd_principal_characters n
      hn S fS t ht hnonab hcentral hnc p f hp hpodd hf hq hmodel hN hY a ha basis principal
      hprincipal ideal₂ ideal₅ hqa hK5
  have hWcyc : IsCyclic W := hWcyc
  have hW5 : Nat.card W = 5 ^ a := hW5
  have hWJ : W ⊔ J = K := hWJ
  have hWJd : W ⊓ J = ⊥ := hWJd
  have hcomm : ∀ w ∈ W, ∀ j ∈ J, w * j = j * w := hcomm
  have hJiso : Nonempty (J ≃* alternatingGroup (Fin 5)) := hJiso
  obtain ⟨eJ⟩ := hJiso
  have htJ : t ∈ J := htJ
  have hC : Nat.card (C t) = 2 * q * (q ^ 2 - 1) := hC
  have hEH : E ≤ H := hEH
  have hJE : J ≤ E := hJE
  have hWE : W ⊔ E = H := hWE
  have hWEd : W ⊓ E = ⊥ := hWEd
  have hσJ : ∀ x : E, (x : G) ∈ J ↔ σ x ∈ alternatingGroup (Fin 5) := hσJ
  have hact : ∀ x : E, ∀ w ∈ W,
      (x : G) * w * (x : G)⁻¹ = w ^ ((Equiv.Perm.sign (σ x) : ℤˣ) : ℤ) := hact
  obtain ⟨lam, hlam⟩ := exists_linear_character_orderOf_five W ha hW5
  have hlam5 : lam ^ 5 = 1 := hlam ▸ pow_orderOf_eq_one lam
  obtain ⟨⟨ψ, hψ⟩, hcolψ⟩ := hcol lam hlam
  have hψ : ∀ (k : K) (w : W) (j : J), (k : G) = w * j →
      ψ k = ((Nat.card (MulAction.fixedBy (Sylow 5 J) j) : ℂ) - 1) * ((lam w : ℂ) - 1) := hψ
  obtain ⟨χ₁, χ₂, χ₃, χB, δ₁, δ₂, δ₃, η, -, -, -, -, -, -, -, hf₁, hf₂, -, hsigns, -, -, hη,
      hsum, hprod, -, -, -, -, -, -, -, -, -, -, hA, -, h₂t, h₃t, hBt, hB1, hBpos, hden, hord⟩ :=
    hcolψ ψ hψ
  have hprod : Module.finrank ℂ (basis.representation χ₁).vector *
      Module.finrank ℂ (basis.representation χ₂).vector =
        q ^ 2 * Module.finrank ℂ (basis.representation χ₃).vector := hprod
  have hA : inducedFunction K ψ = fun g => -(δ₂ : ℂ) * (basis.representation χ₂).character g +
      δ₃ * (basis.representation χ₃).character g + η * (basis.representation χB).character g := hA
  have h₂t : (basis.representation χ₂).character t = -(e * δ₂ * q) := h₂t
  have hBt : (basis.representation χB).character t = η * (1 - e * q) := hBt
  have hden : (Module.finrank ℂ (basis.representation χ₁).vector : ℚ) - e * δ₁ * q ≠ 0 := hden
  have hord : (Nat.card G : ℚ) / (Nat.card (C t) : ℚ) ^ 2 =
      ((q - e) / 2) * (Module.finrank ℂ (basis.representation χ₁).vector *
        (Module.finrank ℂ (basis.representation χ₁).vector + δ₁)) /
          (Module.finrank ℂ (basis.representation χ₁).vector - e * δ₁ * q) ^ 2 := hord
  have hinvol : ∀ x : G, orderOf x = 2 ↔ IsConj x t := by
    obtain ⟨-, -, h⟩ :=
      CFSG.Semidihedral.Local.semidihedral_derived_involutions_conjugate n hn S fS
    have hz : (((fS (r n)) ^ 2 ^ (n - 2) : S) : G) = t := by rw [ht, Subgroup.coe_pow]
    intro x
    rw [← hz]
    exact h Group.IsPerfect.commutator_eq_top x
  obtain ⟨localBasis⟩ := finiteIrreducibleCharacterBasis_exists (G := H)
  have hKH : K ≤ H := Subgroup.centralizer_le_normalizer _
  have hWH : W ≤ H := Subgroup.le_normalizer
  have : (W.subgroupOf H).Normal := Subgroup.normal_in_normalizer
  have hlocal := local_generator_column_pairing W J E H K a ha hW5 hWH hEH hWE hWEd hJE hWJ hKH
    σ hσJ hact eJ t htJ ht2 lam hlam ψ hψ localBasis
  have hFGclass : ∀ x c : G, (fun g => ∑ χ, (basis.representation χ).character t *
      (basis.representation χ).character t * (basis.representation χ).character g /
        (basis.representation χ).character 1) (c * x * c⁻¹) =
      (fun g => ∑ χ, (basis.representation χ).character t *
        (basis.representation χ).character t * (basis.representation χ).character g /
          (basis.representation χ).character 1) x := by
    intro x c
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [show (basis.representation χ).character (c * x * c⁻¹) =
      (basis.representation χ).character x from Representation.char_conj _ x c]
  have hglob := characterPairing_three_left (basis.representation χ₂).character
    (basis.representation χ₃).character (basis.representation χB).character
    (fun g => ∑ χ, (basis.representation χ).character t * (basis.representation χ).character t *
      (basis.representation χ).character g / (basis.representation χ).character 1)
    (-(δ₂ : ℂ)) δ₃ η
  rw [characterPairing_involution_square_sum, characterPairing_involution_square_sum,
    characterPairing_involution_square_sum, ← hA,
    characterPairing_inducedFunction_left K ψ _ hFGclass] at hglob
  have hloc : ∀ k : K, ψ k ≠ 0 →
      (Nat.card G : ℂ) * (fun g => ∑ χ, (basis.representation χ).character t *
        (basis.representation χ).character t * (basis.representation χ).character g /
          (basis.representation χ).character 1) ((k⁻¹ : K) : G) =
      ((Nat.card (C t) : ℂ) ^ 2 * (Nat.card H : ℂ)) * (fun h : H => ∑ α : localBasis.index,
        ((Nat.card H : ℂ)⁻¹ * ∑ u ∈ Finset.univ.filter (fun u : H => orderOf u = 2),
          (localBasis.representation α).character u) ^ 2 *
            (localBasis.representation α).character h /
              (localBasis.representation α).character 1) ⟨((k⁻¹ : K) : G), hKH k⁻¹.2⟩ := by
    intro k hk
    obtain ⟨w, j, hkwj⟩ := FivePowerColumn.exists_eq_mul hWJ hWJd k
    rw [hψ k w j hkwj] at hk
    obtain ⟨hθ, hlw⟩ := mul_ne_zero_iff.mp hk
    have hj5 : Nat.Coprime 5 (orderOf j) :=
      FivePowerColumn.coprime_of_sylowAugmentation_ne_zero eJ hθ
    have hlw1 : lam w ≠ 1 := fun h => hlw (by rw [h, Units.val_one, sub_self])
    have hw : Subgroup.zpowers (w : G) = W :=
      FivePowerColumn.zpowers_eq_of_ne_one W a hW5 lam hlam5 w hlw1
    have hcw : Commute (w : G) (j : G) := hcomm _ w.2 _ j.2
    have hE : extendedCentralizer ((k⁻¹ : K) : G) ≤ H := by
      have hkinv : ((k⁻¹ : K) : G) = (w : G)⁻¹ * (j : G)⁻¹ := by
        rw [Subgroup.coe_inv, hkwj, mul_inv_rev]
        exact (hcw.inv_inv).eq.symm
      rw [hkinv]
      apply extendedCentralizer_le_normalizer_of_generator W hW5
        (by rw [Subgroup.zpowers_inv, hw]) hcw.inv_inv
      rw [orderOf_inv, Subgroup.orderOf_coe]
      exact hj5
    exact localized_involution_square_sum basis H localBasis t hinvol
      ⟨((k⁻¹ : K) : G), hKH k⁻¹.2⟩ hE
  have htrans := pairing_transfer K H hKH ψ
    (fun g => ∑ χ, (basis.representation χ).character t * (basis.representation χ).character t *
      (basis.representation χ).character g / (basis.representation χ).character 1)
    (fun h : H => ∑ α : localBasis.index,
      ((Nat.card H : ℂ)⁻¹ * ∑ u ∈ Finset.univ.filter (fun u : H => orderOf u = 2),
        (localBasis.representation α).character u) ^ 2 *
          (localBasis.representation α).character h / (localBasis.representation α).character 1)
    ((Nat.card (C t) : ℂ) ^ 2 * (Nat.card H : ℂ)) hloc
  have hkey : (Nat.card G : ℂ) * (-(δ₂ : ℂ) * ((basis.representation χ₂).character t *
      (basis.representation χ₂).character t / (basis.representation χ₂).character 1) +
      δ₃ * ((basis.representation χ₃).character t * (basis.representation χ₃).character t /
        (basis.representation χ₃).character 1) +
      η * ((basis.representation χB).character t * (basis.representation χB).character t /
        (basis.representation χB).character 1)) =
      (Nat.card (C t) : ℂ) ^ 2 * (-(5 : ℂ) ^ a / 3) := by
    rw [← hglob, htrans, mul_assoc, hlocal]
  have he : e = 1 ∨ e = -1 := by
    show (if q % 4 = 1 then (1 : ℤ) else -1) = 1 ∨ (if q % 4 = 1 then (1 : ℤ) else -1) = -1
    split_ifs <;> simp
  have hsqC : ∀ x : ℤ, (x = 1 ∨ x = -1) → (x : ℂ) ^ 2 = 1 := by
    rintro x (rfl | rfl) <;> norm_num
  obtain ⟨hδ₂, hδ₃⟩ : (δ₂ = 1 ∨ δ₂ = -1) ∧ (δ₃ = 1 ∨ δ₃ = -1) := by
    rcases hsigns with ⟨-, h2, h3⟩ | ⟨-, h2, h3⟩ | ⟨-, h2, h3⟩ <;> simp [h2, h3]
  have v2 : (basis.representation χ₂).character t * (basis.representation χ₂).character t =
      (q : ℂ) ^ 2 := by
    rw [h₂t]
    linear_combination (q : ℂ) ^ 2 * ((e : ℂ) ^ 2 * hsqC δ₂ hδ₂ + hsqC e he)
  have v3 : (basis.representation χ₃).character t * (basis.representation χ₃).character t = 1 := by
    rw [h₃t]
    linear_combination hsqC δ₃ hδ₃
  have vB : (basis.representation χB).character t * (basis.representation χB).character t =
      (1 - e * q) ^ 2 := by
    rw [hBt]
    linear_combination (1 - (e : ℂ) * q) ^ 2 * hsqC η hη
  rw [v2, v3, vB, (basis_character_one basis χ₂).1, (basis_character_one basis χ₃).1, hB1]
    at hkey
  have hm : 2 * (5 : ℤ) ^ a = q + e := by
    have hev : Even ((q : ℤ) + e) := by
      have hqodd : Odd q := hpodd.pow
      obtain ⟨k, hk⟩ := hqodd
      rcases he with h | h <;> rw [h]
      · exact ⟨(k : ℤ) + 1, by rw [hk]; push_cast; ring⟩
      · exact ⟨(k : ℤ), by rw [hk]; push_cast; ring⟩
    rw [← hqa]
    exact Int.mul_ediv_cancel' (even_iff_two_dvd.mp hev)
  exact alternating_five_column_false hq' he hη hsigns hf₁ hf₂ hsum hprod hBpos hden
    Nat.card_pos.ne' hm hord hkey

end Alternative

end PureFiveAlternatingFour

end CFSG.Semidihedral.Principal
