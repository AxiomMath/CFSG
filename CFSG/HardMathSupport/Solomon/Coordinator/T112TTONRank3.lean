module

public import CFSG.Quasithin.H13.L32NLem14324m

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open scoped commutatorElement

theorem three_le_pRank_of_class_two {G : Type} [Group G] [Finite G] (Z : Subgroup G)
    (hZc : ∀ z ∈ Z, ∀ g : G, g * z = z * g) (hZcard : Nat.card Z = 3)
    (hcard : Nat.card G = 81) (hexp : ∀ g : G, g ^ 3 = 1) (hcomm : ∀ g h : G, ⁅g, h⁆ ∈ Z) :
    3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup G) := by
  classical
  have hp3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨z, hz, hz1⟩ : ∃ z ∈ Z, z ≠ 1 := by
    by_contra h
    push Not at h
    have : Z = ⊥ := eq_bot_iff.2 fun g hg => Subgroup.mem_bot.2 (h g hg)
    rw [this, Subgroup.card_bot] at hZcard
    omega
  obtain ⟨x, hx⟩ : ∃ x : G, x ∉ Z := by
    by_contra h
    push Not at h
    have : Z = ⊤ := eq_top_iff.2 fun g _ => h g
    rw [this, Subgroup.card_top] at hZcard
    omega
  have hcentral : ∀ c ∈ Z, ∀ g : G, g * c * g⁻¹ = c := fun c hc g => by
    rw [hZc c hc g, mul_assoc, mul_inv_cancel, mul_one]
  let φ : G →* Z :=
    { toFun := fun y => ⟨⁅x, y⁆, hcomm x y⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun y y' => Subtype.ext (by
        have hc := hZc _ (hcomm x y') y⁻¹
        have e1 : ⁅x, y * y'⁆ = x * y * x⁻¹ * ⁅x, y'⁆ * y⁻¹ := by
          simp only [commutatorElement_def]; group
        have e2 : ⁅x, y⁆ * ⁅x, y'⁆ = x * y * x⁻¹ * y⁻¹ * ⁅x, y'⁆ := by
          simp only [commutatorElement_def, mul_assoc]
        change ⁅x, y * y'⁆ = ⁅x, y⁆ * ⁅x, y'⁆
        rw [e1, e2, mul_assoc (x * y * x⁻¹), ← hc, ← mul_assoc]) }
  have hker : ∀ y, y ∈ φ.ker ↔ Commute x y := fun y => by
    rw [MonoidHom.mem_ker]
    constructor
    · intro h
      have : ⁅x, y⁆ = 1 := congrArg Subtype.val h
      exact commutatorElement_eq_one_iff_commute.1 this
    · intro h
      exact Subtype.ext (commutatorElement_eq_one_iff_commute.2 h)
  have hkercard : 27 ≤ Nat.card φ.ker := by
    have h1 := Subgroup.card_ker_mul_card_range φ
    have h2 : Nat.card φ.range ≤ 3 := hZcard ▸ Nat.card_le_card_of_injective
      (fun r : φ.range => (r : Z)) Subtype.val_injective
    rw [hcard] at h1
    by_contra hlt
    push Not at hlt
    have : Nat.card φ.ker * Nat.card φ.range ≤ 26 * 3 :=
      Nat.mul_le_mul (by omega) h2
    omega
  let S : Finset G := (Finset.univ : Finset (Fin 3 × Fin 3)).image
    (fun p => z ^ (p.1 : ℕ) * x ^ (p.2 : ℕ))
  have hS : S.card ≤ 9 := by
    have := Finset.card_image_le (s := (Finset.univ : Finset (Fin 3 × Fin 3)))
      (f := fun p : Fin 3 × Fin 3 => z ^ (p.1 : ℕ) * x ^ (p.2 : ℕ))
    simpa using this
  obtain ⟨y, hy, hyS⟩ : ∃ y : G, y ∈ φ.ker ∧ y ∉ S := by
    by_contra h
    push Not at h
    have hle : Nat.card φ.ker ≤ Nat.card S := Nat.card_le_card_of_injective
      (fun y : φ.ker => (⟨y, h y y.2⟩ : S))
      (fun a b hab => Subtype.ext (by simpa using congrArg Subtype.val hab))
    have hSc : Nat.card S = S.card := Nat.card_eq_fintype_card.trans (Fintype.card_coe S)
    omega
  have hxy : Commute x y := (hker y).1 hy
  have hmod : ∀ g : G, ∀ m : ℕ, g ^ m = g ^ (m % 3) := fun g m => by
    conv_lhs => rw [← Nat.mod_add_div m 3, pow_add, pow_mul, hexp g, one_pow, mul_one]
  have hyS' : ∀ m n : ℕ, z ^ m * x ^ n ≠ y := by
    intro m n hmn
    apply hyS
    rw [Finset.mem_image]
    refine ⟨(⟨m % 3, Nat.mod_lt _ (by norm_num)⟩, ⟨n % 3, Nat.mod_lt _ (by norm_num)⟩),
      Finset.mem_univ _, ?_⟩
    simp only
    rw [← hmod z m, ← hmod x n, hmn]
  exact CFSG.Quasithin.H13.S8Five.three_le_pRank_of_triple (x := z) (y := x) (z := y)
    (hexp z) (hexp x) (hexp y) (hZc z hz x).symm (hZc z hz y).symm hxy hz1
    (fun n hn => hx (hn ▸ Z.pow_mem hz n)) hyS'

end CFSG.HardMathSupport.Solomon.Coordinator
