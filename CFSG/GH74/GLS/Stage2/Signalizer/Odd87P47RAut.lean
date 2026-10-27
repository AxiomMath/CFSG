module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Grp4cAut

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG.GH74.GLS.Stage1.Main

theorem perm_four_pairwise : ∀ c y₁ y₂ : Equiv.Perm (Fin 4), c ^ 3 = 1 → c ≠ 1 → y₁ * y₁ = 1 →
    y₂ * y₂ = 1 → y₁ * y₂ = y₂ * y₁ → (y₁ * c * y₁⁻¹ = c ∨ y₁ * c * y₁⁻¹ = c⁻¹) →
    (y₂ * c * y₂⁻¹ = c ∨ y₂ * c * y₂⁻¹ = c⁻¹) → y₁ = 1 ∨ y₂ = 1 ∨ y₁ = y₂ := by
  decide +kernel

theorem aut_q8_pairwise {V : Type*} [Group V] (e : V ≃* QuaternionGroup 2) (c y₁ y₂ : MulAut V)
    (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1) (h1 : y₁ * y₁ = 1) (h2 : y₂ * y₂ = 1)
    (h12 : y₁ * y₂ = y₂ * y₁) (hn1 : y₁ * c * y₁⁻¹ = c ∨ y₁ * c * y₁⁻¹ = c⁻¹)
    (hn2 : y₂ * c * y₂⁻¹ = c ∨ y₂ * c * y₂⁻¹ = c⁻¹) : y₁ = 1 ∨ y₂ = 1 ∨ y₁ = y₂ := by
  obtain ⟨θ⟩ := mulAut_equiv_perm_of_quaternion e
  have hθ : ∀ a b : MulAut V, θ (a * b * a⁻¹) = θ a * θ b * (θ a)⁻¹ := fun a b => by
    simp [map_mul, map_inv]
  have key := perm_four_pairwise (θ c) (θ y₁) (θ y₂) (by rw [← map_pow, hc3, map_one])
    (fun h => hc1 (θ.injective (by rw [h, map_one])))
    (by rw [← map_mul, h1, map_one]) (by rw [← map_mul, h2, map_one])
    (by rw [← map_mul, ← map_mul, h12])
    (by rcases hn1 with h | h
        · left; rw [← hθ, h]
        · right; rw [← hθ, h, map_inv])
    (by rcases hn2 with h | h
        · left; rw [← hθ, h]
        · right; rw [← hθ, h, map_inv])
  rcases key with h | h | h
  · left; exact θ.injective (by rw [h, map_one])
  · right; left; exact θ.injective (by rw [h, map_one])
  · right; right; exact θ.injective h

theorem exists_gen_of_card_three {B : Type*} [Group B] (R : Subgroup B) (hR : Nat.card ↥R = 3) :
    ∃ c ∈ R, c ≠ 1 ∧ c ^ 3 = 1 ∧ ∀ a ∈ R, a = 1 ∨ a = c ∨ a = c⁻¹ := by
  classical
  have hfin : Finite ↥R := Nat.finite_of_card_ne_zero (by rw [hR]; norm_num)
  have h1 : Nat.card ↥R ≠ 1 := by rw [hR]; norm_num
  have : Nontrivial ↥R := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    omega
  obtain ⟨c', hc'⟩ := exists_ne (1 : ↥R)
  have hord : orderOf c' ∣ 3 := hR ▸ orderOf_dvd_natCard c'
  have hord3 : orderOf c' = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hord with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hc'
    · exact h
  refine ⟨(c' : B), c'.2, fun h => hc' (Subtype.ext h), ?_, ?_⟩
  · have := pow_orderOf_eq_one c'
    rw [hord3] at this
    exact congrArg Subtype.val this
  · intro a ha
    have hz : (⟨a, ha⟩ : ↥R) ∈ Subgroup.zpowers c' := by
      have hcard : Nat.card (Subgroup.zpowers c') = Nat.card ↥R := by
        rw [Nat.card_zpowers, hord3, hR]
      have : Subgroup.zpowers c' = ⊤ := by
        apply Subgroup.eq_top_of_card_eq
        exact hcard
      rw [this]; exact Subgroup.mem_top _
    rw [mem_zpowers_iff_mem_range_orderOf] at hz
    simp only [Finset.mem_image, Finset.mem_range, hord3] at hz
    obtain ⟨i, hi, hia⟩ := hz
    interval_cases i
    · left; simpa using (congrArg Subtype.val hia).symm
    · right; left; simpa using (congrArg Subtype.val hia).symm
    · right; right
      have h2 : (c' ^ 2 : ↥R) = c'⁻¹ := by
        have h3 : c' ^ 3 = 1 := by rw [← hord3]; exact pow_orderOf_eq_one c'
        calc c' ^ 2 = c' ^ 2 * (c' * c'⁻¹) := by simp
          _ = c' ^ 3 * c'⁻¹ := by group
          _ = c'⁻¹ := by rw [h3, one_mul]
      have := congrArg Subtype.val (hia.symm.trans h2)
      simpa using this

theorem card_le_two_of_pairwise {B : Type*} [Group B] [Finite B] (S : Subgroup B)
    (h : ∀ a ∈ S, ∀ b ∈ S, a = 1 ∨ b = 1 ∨ a = b) : Nat.card ↥S ≤ 2 := by
  by_contra hlt
  push Not at hlt
  have : Fintype ↥S := Fintype.ofFinite _
  have h3 : 2 < Fintype.card ↥S := by rw [← Nat.card_eq_fintype_card]; exact hlt
  obtain ⟨a, b, d, hab, had, hbd⟩ := Fintype.two_lt_card_iff.mp h3
  have hab' : (a : B) ≠ b := fun h => hab (Subtype.ext h)
  have had' : (a : B) ≠ d := fun h => had (Subtype.ext h)
  have hbd' : (b : B) ≠ d := fun h => hbd (Subtype.ext h)
  rcases h a a.2 b b.2 with h1 | h1 | h1
  · rcases h b b.2 d d.2 with h2 | h2 | h2
    · exact hab' (h1.trans h2.symm)
    · exact had' (h1.trans h2.symm)
    · exact hbd' h2
  · rcases h a a.2 d d.2 with h2 | h2 | h2
    · exact hab' (h2.trans h1.symm)
    · exact hbd' (h1.trans h2.symm)
    · exact had' h2
  · exact hab' h1

section Core

variable {A : Type} [Group A] [Finite A]

theorem exists_four_cent_aut {V X E : Subgroup A} (e : ↥V ≃* QuaternionGroup 2)
    (hXV : X ≤ normalizer (V : Set A)) (hEV : E ≤ normalizer (V : Set A))
    (hEX : E ≤ normalizer (X : Set A))
    (hcard : Nat.card (actOnKHom V X hXV).range = 3)
    (hE2 : ∀ g ∈ E, g * g = 1) (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hE8 : 8 ≤ Nat.card ↥E) :
    ∃ K : Subgroup A, K ≤ E ∧ K ≤ centralizer (V : Set A) ∧ Nat.card ↥K = 4 := by
  classical
  obtain ⟨c, hcR, hc1, hc3, hcases⟩ := exists_gen_of_card_three (actOnKHom V X hXV).range hcard
  obtain ⟨x₀, hx₀⟩ := hcR
  set ρE := actOnKHom V E hEV with hρE
  have hconj : ∀ g : ↥E, ρE g * c * (ρE g)⁻¹ = c ∨ ρE g * c * (ρE g)⁻¹ = c⁻¹ := by
    intro g
    have hmemX : (g : A) * (x₀ : A) * (g : A)⁻¹ ∈ X :=
      (Subgroup.mem_normalizer_iff.mp (hEX g.2) (x₀ : A)).mp x₀.2
    have hcomm : ρE g * c = actOnKHom V X hXV ⟨(g : A) * (x₀ : A) * (g : A)⁻¹, hmemX⟩ * ρE g := by
      rw [← hx₀]
      refine MulEquiv.ext fun v => Subtype.ext ?_
      show (g : A) * ((x₀ : A) * (v : A) * (x₀ : A)⁻¹) * (g : A)⁻¹ =
        ((g : A) * (x₀ : A) * (g : A)⁻¹) * ((g : A) * (v : A) * (g : A)⁻¹) *
          ((g : A) * (x₀ : A) * (g : A)⁻¹)⁻¹
      group
    have hmem : ρE g * c * (ρE g)⁻¹ ∈ (actOnKHom V X hXV).range := by
      refine ⟨⟨(g : A) * (x₀ : A) * (g : A)⁻¹, hmemX⟩, ?_⟩
      symm
      rw [mul_inv_eq_iff_eq_mul]
      exact hcomm
    rcases hcases _ hmem with h | h | h
    · exfalso
      apply hc1
      have : c = (ρE g)⁻¹ * 1 * ρE g := by
        rw [← h]; group
      simpa using this
    · exact Or.inl h
    · exact Or.inr h
  have hpair : ∀ g₁ g₂ : ↥E, ρE g₁ = 1 ∨ ρE g₂ = 1 ∨ ρE g₁ = ρE g₂ := by
    intro g₁ g₂
    refine aut_q8_pairwise e c (ρE g₁) (ρE g₂) hc3 hc1 ?_ ?_ ?_ (hconj g₁) (hconj g₂)
    · rw [← map_mul, (show g₁ * g₁ = 1 from Subtype.ext (hE2 _ g₁.2)), map_one]
    · rw [← map_mul, (show g₂ * g₂ = 1 from Subtype.ext (hE2 _ g₂.2)), map_one]
    · rw [← map_mul, ← map_mul, (show g₁ * g₂ = g₂ * g₁ from Subtype.ext (hEc _ g₁.2 _ g₂.2))]
  have hrange : Nat.card ρE.range ≤ 2 := by
    apply card_le_two_of_pairwise
    rintro a ⟨ga, rfl⟩ b ⟨gb, rfl⟩
    exact hpair ga gb
  have hmul : Nat.card ρE.range * Nat.card ρE.ker = Nat.card ↥E := by
    have h := Subgroup.index_mul_card ρE.ker
    rw [Subgroup.index_ker] at h
    exact h
  have hker4 : 4 ≤ Nat.card ρE.ker := by
    by_contra hlt
    push Not at hlt
    have : Nat.card ρE.range * Nat.card ρE.ker ≤ 2 * 3 := Nat.mul_le_mul hrange (by omega)
    omega
  have hEp : IsPGroup 2 ↥E := fun g => ⟨1, by
    rw [pow_one, pow_two]
    exact Subtype.ext (hE2 g g.2)⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := (hEp.to_subgroup ρE.ker).exists_card_eq
  have hm2 : 2 ≤ m := by
    by_contra hlt
    push Not at hlt
    interval_cases m <;> omega
  obtain ⟨K₀, hK₀⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥ρE.ker) 2 (n := 2)
    (by rw [hm]; exact pow_dvd_pow 2 hm2)
  refine ⟨(K₀.map ρE.ker.subtype).map E.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
  · rintro _ ⟨g, hg, rfl⟩
    obtain ⟨⟨g', hgker⟩, -, rfl⟩ := hg
    have hk1 : g' ∈ (centralizer (V : Set A)).subgroupOf E := by
      rw [← actOnKHom_ker V E hEV]; exact hgker
    exact Subgroup.mem_subgroupOf.mp hk1
  · rw [Subgroup.card_map_of_injective E.subtype_injective,
      Subgroup.card_map_of_injective ρE.ker.subtype_injective, hK₀]
    norm_num

end Core

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
