module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryEndingSplitArith

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup
open scoped commutatorElement

namespace SplitComm

variable {G : Type*} [Group G]

theorem mul_right_of_commute {x y c : G} (h : c * y = y * c) :
    ⁅x * c, y⁆ = ⁅x, y⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  calc x * c * y * (x * c)⁻¹ * y⁻¹ = x * (c * y) * c⁻¹ * x⁻¹ * y⁻¹ := by group
    _ = x * (y * c) * c⁻¹ * x⁻¹ * y⁻¹ := by rw [h]
    _ = x * y * x⁻¹ * y⁻¹ := by group

theorem mul_right_of_commute' {x y c : G} (h : c * x = x * c) :
    ⁅x, y * c⁆ = ⁅x, y⁆ := by
  have h' : c * x⁻¹ = x⁻¹ * c := by
    calc c * x⁻¹ = x⁻¹ * (x * c) * x⁻¹ := by group
      _ = x⁻¹ * (c * x) * x⁻¹ := by rw [h]
      _ = x⁻¹ * c := by group
  rw [commutatorElement_def, commutatorElement_def]
  calc x * (y * c) * x⁻¹ * (y * c)⁻¹ = x * y * (c * x⁻¹) * c⁻¹ * y⁻¹ := by group
    _ = x * y * (x⁻¹ * c) * c⁻¹ * y⁻¹ := by rw [h']
    _ = x * y * x⁻¹ * y⁻¹ := by group

theorem mul_left_eq {x x' y : G} (h₁ : ⁅x', y⁆ * x = x * ⁅x', y⁆)
    (h₂ : ⁅x', y⁆ * ⁅x, y⁆ = ⁅x, y⁆ * ⁅x', y⁆) : ⁅x * x', y⁆ = ⁅x, y⁆ * ⁅x', y⁆ := by
  have e : ⁅x * x', y⁆ = x * ⁅x', y⁆ * x⁻¹ * ⁅x, y⁆ := by
    rw [commutatorElement_def, commutatorElement_def, commutatorElement_def]
    group
  have h₁' : x * ⁅x', y⁆ * x⁻¹ = ⁅x', y⁆ := by rw [← h₁, mul_inv_cancel_right]
  rw [e, h₁', h₂]

theorem mul_right_eq {x y y' : G} (h : ⁅x, y'⁆ * y = y * ⁅x, y'⁆) :
    ⁅x, y * y'⁆ = ⁅x, y⁆ * ⁅x, y'⁆ := by
  have e : ⁅x, y * y'⁆ = ⁅x, y⁆ * (y * ⁅x, y'⁆ * y⁻¹) := by
    rw [commutatorElement_def, commutatorElement_def, commutatorElement_def]
    group
  have h' : y * ⁅x, y'⁆ * y⁻¹ = ⁅x, y'⁆ := by rw [← h, mul_inv_cancel_right]
  rw [e, h']

end SplitComm

theorem card_commutator_le_of_weights {G : Type*} [Group G] [Finite G] {K : Type*} [Field K]
    [Fintype K] {f : ℕ} (hf : 2 ≤ f) (hK : Fintype.card K = (2 ^ f) ^ 2) {J R : Subgroup G}
    (hJR : ∀ x ∈ J, ∀ y ∈ J, x * y * x⁻¹ * y⁻¹ ∈ R) (hRc : ∀ x ∈ J, ∀ r ∈ R, x * r = r * x)
    (hRab : ∀ r ∈ R, ∀ r' ∈ R, r * r' = r' * r) (hR2 : ∀ r ∈ R, r ^ 2 = 1)
    (a : G → K) (ha : ∀ x ∈ J, ∀ y ∈ J, a (x * y) = a x + a y)
    (haR : ∀ x ∈ J, a x = 0 → x ∈ R) (hasurj : ∀ z : K, ∃ x ∈ J, a x = z)
    (χ₁ χ₂ : G → K) (hχ₁ : ∀ r ∈ R, ∀ r' ∈ R, χ₁ (r * r') = χ₁ r + χ₁ r')
    (hχ₂ : ∀ r ∈ R, ∀ r' ∈ R, χ₂ (r * r') = χ₂ r + χ₂ r')
    (hχ : ∀ r ∈ R, χ₁ r = 0 → χ₂ r = 0 → r = 1)
    {d : G} {μ : K} (hμ0 : μ ≠ 0) (hμ : orderOf μ = ((2 ^ f) ^ 2 - 1) / Nat.gcd 3 (2 ^ f + 1))
    (hdJ : ∀ x ∈ J, d * x * d⁻¹ ∈ J) (hda : ∀ x ∈ J, a (d * x * d⁻¹) = μ * a x)
    (hdχ₁ : ∀ r ∈ R, χ₁ (d * r * d⁻¹) = μ ^ (2 ^ f + 1) * χ₁ r)
    (hdχ₂ : ∀ r ∈ R, χ₂ (d * r * d⁻¹) = μ ^ (2 ^ f + 1) * χ₂ r) :
    Nat.card (⁅J, J⁆ : Subgroup G) ≤ 2 ^ f := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card K = 2 ^ (2 * f) := by
    rw [Nat.card_eq_fintype_card, hK, ← pow_mul, mul_comm]
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hcard
  have ha1 : a 1 = 0 := by
    have h := ha 1 (one_mem _) 1 (one_mem _)
    rw [mul_one] at h
    linear_combination -h
  have hainv : ∀ x ∈ J, a x⁻¹ = -a x := by
    intro x hx
    have h := ha x hx x⁻¹ (inv_mem hx)
    rw [mul_inv_cancel, ha1] at h
    linear_combination -h
  have hχ₁one : χ₁ 1 = 0 := by
    have h := hχ₁ 1 (one_mem _) 1 (one_mem _)
    rw [mul_one] at h
    linear_combination -h
  have hχ₂one : χ₂ 1 = 0 := by
    have h := hχ₂ 1 (one_mem _) 1 (one_mem _)
    rw [mul_one] at h
    linear_combination -h
  have hcommJ : ∀ x ∈ J, ∀ y ∈ J, ⁅x, y⁆ ∈ R := fun x hx y hy => by
    rw [commutatorElement_def]
    exact hJR x hx y hy
  choose s hsJ hsa using hasurj
  have hdec : ∀ x ∈ J, (s (a x))⁻¹ * x ∈ R := by
    intro x hx
    refine haR _ (mul_mem (inv_mem (hsJ _)) hx) ?_
    rw [ha _ (inv_mem (hsJ _)) _ hx, hainv _ (hsJ _), hsa]
    ring
  have hcomm_eq : ∀ x ∈ J, ∀ y ∈ J, ⁅x, y⁆ = ⁅s (a x), s (a y)⁆ := by
    intro x hx y hy
    have ex : x = s (a x) * ((s (a x))⁻¹ * x) := by group
    have ey : y = s (a y) * ((s (a y))⁻¹ * y) := by group
    have hc₁ := hdec x hx
    have hc₂ := hdec y hy
    have hy' : s (a y) * ((s (a y))⁻¹ * y) ∈ J := mul_mem (hsJ _) (mul_mem (inv_mem (hsJ _)) hy)
    calc ⁅x, y⁆ = ⁅s (a x) * ((s (a x))⁻¹ * x), s (a y) * ((s (a y))⁻¹ * y)⁆ := by
          rw [← ex, ← ey]
      _ = ⁅s (a x), s (a y) * ((s (a y))⁻¹ * y)⁆ :=
          SplitComm.mul_right_of_commute (hRc _ hy' _ hc₁).symm
      _ = ⁅s (a x), s (a y)⁆ :=
          SplitComm.mul_right_of_commute' (hRc _ (hsJ _) _ hc₂).symm
  set Φ : K → K → G := fun z w => ⁅s z, s w⁆ with hΦ
  have hΦR : ∀ z w, Φ z w ∈ R := fun z w => hcommJ _ (hsJ z) _ (hsJ w)
  have hΦl : ∀ z z' w, Φ (z + z') w = Φ z w * Φ z' w := by
    intro z z' w
    have h1 : Φ (z + z') w = ⁅s z * s z', s w⁆ := by
      have := hcomm_eq (s z * s z') (mul_mem (hsJ z) (hsJ z')) (s w) (hsJ w)
      rw [ha _ (hsJ z) _ (hsJ z')] at this
      simp only [hsa] at this
      exact this.symm
    rw [h1]
    exact SplitComm.mul_left_eq (hRc _ (hsJ z) _ (hΦR z' w)).symm
      (hRab _ (hΦR z' w) _ (hΦR z w))
  have hΦr : ∀ z w w', Φ z (w + w') = Φ z w * Φ z w' := by
    intro z w w'
    have h1 : Φ z (w + w') = ⁅s z, s w * s w'⁆ := by
      have := hcomm_eq (s z) (hsJ z) (s w * s w') (mul_mem (hsJ w) (hsJ w'))
      rw [ha _ (hsJ w) _ (hsJ w')] at this
      simp only [hsa] at this
      exact this.symm
    rw [h1]
    exact SplitComm.mul_right_eq (hRc _ (hsJ w) _ (hΦR z w')).symm
  have hΦa : ∀ z, Φ z z = 1 := fun z => by
    simp only [hΦ, commutatorElement_def]
    group
  have hΦd : ∀ z w, d * Φ z w * d⁻¹ = Φ (μ * z) (μ * w) := by
    intro z w
    have h1 : d * Φ z w * d⁻¹ = ⁅d * s z * d⁻¹, d * s w * d⁻¹⁆ := by
      simp only [hΦ, commutatorElement_def]
      group
    rw [h1, hcomm_eq _ (hdJ _ (hsJ z)) _ (hdJ _ (hsJ w)), hda _ (hsJ z), hda _ (hsJ w)]
    simp only [hsa, hΦ]
  have hχr : ∀ χ : G → K, (∀ r ∈ R, ∀ r' ∈ R, χ (r * r') = χ r + χ r') →
      (∀ r ∈ R, χ (d * r * d⁻¹) = μ ^ (2 ^ f + 1) * χ r) →
      ∃ c : K, ∀ z w, χ (Φ z w) = c * (z * w ^ 2 ^ f + z ^ 2 ^ f * w) := by
    intro χ hχadd hχd
    have h0 : χ 1 = 0 := by
      have h := hχadd 1 (one_mem _) 1 (one_mem _)
      rw [mul_one] at h
      linear_combination -h
    let β : K →+ K →+ K := AddMonoidHom.mk' (fun z => AddMonoidHom.mk' (fun w => χ (Φ z w))
      (fun w w' => by rw [hΦr, hχadd _ (hΦR _ _) _ (hΦR _ _)]))
      (fun z z' => AddMonoidHom.ext fun w => by
        simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply]
        rw [hΦl, hχadd _ (hΦR _ _) _ (hΦR _ _)])
    have hβ : ∀ z w, β z w = χ (Φ z w) := fun _ _ => rfl
    obtain ⟨c, hc⟩ := eq_mul_trace_of_alternating_equivariant hf hK β hμ0 hμ
      (fun z w => by rw [hβ, hβ, ← hΦd, hχd _ (hΦR z w)])
      (fun z => by rw [hβ, hΦa, h0])
    exact ⟨c, fun z w => by rw [← hβ, hc]⟩
  obtain ⟨c₁, hc₁⟩ := hχr χ₁ hχ₁ hdχ₁
  obtain ⟨c₂, hc₂⟩ := hχr χ₂ hχ₂ hdχ₂
  have hfrob : ∀ x y : K, (x + y) ^ 2 ^ f = x ^ 2 ^ f + y ^ 2 ^ f := fun x y =>
    add_pow_char_pow x y 2 f
  have hqq : ∀ z : K, (z ^ 2 ^ f) ^ 2 ^ f = z := fun z => by
    rw [← pow_mul, ← sq, ← hK]
    exact FiniteField.pow_card z
  have hτ : ∀ z w : K, (z * w ^ 2 ^ f + z ^ 2 ^ f * w) ^ 2 ^ f =
      z * w ^ 2 ^ f + z ^ 2 ^ f * w := by
    intro z w
    rw [hfrob, mul_pow, mul_pow, hqq, hqq]
    ring
  let S : Subgroup G :=
    { carrier := {r | r ∈ R ∧ ∃ τ : K, τ ^ 2 ^ f = τ ∧ χ₁ r = c₁ * τ ∧ χ₂ r = c₂ * τ}
      one_mem' := ⟨one_mem _, 0, by simp, by rw [hχ₁one, mul_zero], by rw [hχ₂one, mul_zero]⟩
      mul_mem' := by
        rintro r r' ⟨hr, τ, hτ₀, h1, h2⟩ ⟨hr', τ', hτ', h1', h2'⟩
        exact ⟨mul_mem hr hr', τ + τ', by rw [hfrob, hτ₀, hτ'],
          by rw [hχ₁ _ hr _ hr', h1, h1']; ring, by rw [hχ₂ _ hr _ hr', h2, h2']; ring⟩
      inv_mem' := by
        rintro r ⟨hr, τ, hτ₀, h1, h2⟩
        have hinv : r⁻¹ = r := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hR2 r hr)
        exact ⟨inv_mem hr, τ, hτ₀, by rw [hinv]; exact h1, by rw [hinv]; exact h2⟩ }
  have hJS : ⁅J, J⁆ ≤ S := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    rw [hcomm_eq x hx y hy]
    exact ⟨hΦR _ _, _, hτ (a x) (a y), hc₁ _ _, hc₂ _ _⟩
  have hFcard := card_filter_pow_eq_self_le (K := K) (q := 2 ^ f)
    (Nat.one_lt_two_pow (by omega))
  set F := Finset.univ.filter fun x : K => x ^ 2 ^ f = x with hF
  set I := F.image fun τ => (c₁ * τ, c₂ * τ) with hI
  have hmap : ∀ r : S, ((χ₁ r, χ₂ r) : K × K) ∈ I := by
    rintro ⟨r, hr, τ, hτ₀, h1, h2⟩
    rw [hI, Finset.mem_image]
    exact ⟨τ, by rw [hF, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hτ₀⟩,
      Prod.ext h1.symm h2.symm⟩
  let g : S → I := fun r => ⟨(χ₁ r, χ₂ r), hmap r⟩
  have hg : Function.Injective g := by
    intro x y h
    have h' := congrArg Subtype.val h
    simp only [g, Prod.mk.injEq] at h'
    obtain ⟨e1, e2⟩ := h'
    have hx : (x : G) ∈ R := x.2.1
    have hy : (y : G) ∈ R := y.2.1
    have hrr : (x : G) * y = 1 := hχ _ (mul_mem hx hy)
      (by rw [hχ₁ _ hx _ hy, e1, CharTwo.add_self_eq_zero])
      (by rw [hχ₂ _ hx _ hy, e2, CharTwo.add_self_eq_zero])
    have hinv : (y : G)⁻¹ = y := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hR2 _ hy)
    apply Subtype.ext
    rw [← hinv]
    exact eq_inv_of_mul_eq_one_left hrr
  calc Nat.card (⁅J, J⁆ : Subgroup G) ≤ Nat.card S := Subgroup.card_le_of_le hJS
    _ ≤ Nat.card I := Nat.card_le_card_of_injective g hg
    _ = I.card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ ≤ F.card := Finset.card_image_le
    _ ≤ 2 ^ f := hFcard

end CFSG.SeitzReduction.RankOne
