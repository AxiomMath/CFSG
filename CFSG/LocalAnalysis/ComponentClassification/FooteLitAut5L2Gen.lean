module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitAut5L2Fix

public section

namespace CFSG.ComponentClassification.FooteLit.Aut5L2

open CFSG GorensteinWalter Subgroup CFSG.ComponentClassification.Foote5
open CFSG.ComponentClassification.AutL2Facts

theorem exists_two_gen_of_card_le_eight {G : Type*} [Group G] (P : Subgroup G) [Finite P]
    (hP : IsPGroup 2 P) (h8 : Nat.card P ≤ 8) (hE : Nat.card P = 8 → ∃ x ∈ P, x * x ≠ 1) :
    ∃ s : Finset G, s.card ≤ 2 ∧ closure (s : Set G) = P := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP
  rcases P.bot_or_exists_ne_one with hbot | ⟨x₁, hx₁P, hx₁⟩
  · exact ⟨∅, by simp, by simp [hbot]⟩
  have hk3 : k ≤ 3 := by
    by_contra h
    have : 2 ^ 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨x, hxP, hx⟩ : ∃ x ∈ P, Nat.card P ≤ 2 * orderOf x := by
    by_cases h3 : k = 3
    · obtain ⟨x, hxP, hx1⟩ := hE (by rw [hk, h3]; norm_num)
      refine ⟨x, hxP, ?_⟩
      have hd : orderOf x ∣ 2 ^ 3 := by rw [← h3, ← hk]; exact P.orderOf_dvd_natCard hxP
      obtain ⟨j, -, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
      have hj2 : 2 ≤ j := by
        by_contra h
        have hx2 := pow_orderOf_eq_one x
        interval_cases j
        · rw [hj', pow_zero, pow_one] at hx2
          exact hx1 (by rw [hx2, mul_one])
        · rw [hj', pow_one, sq] at hx2
          exact hx1 hx2
      rw [hk, h3, hj']
      calc 2 ^ 3 = 2 * 2 ^ 2 := by norm_num
        _ ≤ 2 * 2 ^ j := Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by norm_num) hj2)
    · refine ⟨x₁, hx₁P, ?_⟩
      have hd : orderOf x₁ ∣ 2 ^ k := by rw [← hk]; exact P.orderOf_dvd_natCard hx₁P
      have hpos : 0 < orderOf x₁ := Nat.pos_of_dvd_of_pos hd (by positivity)
      have h1 : orderOf x₁ ≠ 1 := fun h => hx₁ (orderOf_eq_one_iff.mp h)
      have hk2 : 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [hk]
      omega
  by_cases hz : zpowers x = P
  · refine ⟨{x}, by simp, ?_⟩
    rw [Finset.coe_singleton, ← zpowers_eq_closure, hz]
  have hxle : zpowers x ≤ P := zpowers_le.mpr hxP
  obtain ⟨y, hyP, hyx⟩ : ∃ y ∈ P, y ∉ zpowers x := by
    by_contra h
    push Not at h
    exact hz (le_antisymm hxle h)
  refine ⟨{x, y}, Finset.card_le_two, ?_⟩
  rw [Finset.coe_insert, Finset.coe_singleton]
  have hH : closure ({x, y} : Set G) ≤ P := by
    rw [closure_le]
    intro g hg
    rcases hg with rfl | rfl
    · exact hxP
    · exact hyP
  have : Finite (closure ({x, y} : Set G)) :=
    Finite.of_injective (inclusion hH) (inclusion_injective hH)
  apply eq_of_le_of_card_ge hH
  have h1 : zpowers x ≤ closure ({x, y} : Set G) := zpowers_le.mpr (subset_closure (by simp))
  have h4 : orderOf x ≠ Nat.card (closure ({x, y} : Set G)) := fun h => by
    rw [← Nat.card_zpowers] at h
    exact hyx ((eq_of_le_of_card_ge h1 h.ge) ▸ subset_closure (by simp))
  obtain ⟨c, hc⟩ := card_dvd_of_le h1
  rw [Nat.card_zpowers] at hc
  have hpos : 0 < Nat.card (closure ({x, y} : Set G)) := Nat.card_pos
  have hc2 : 2 ≤ c := by
    by_contra h
    interval_cases c
    · rw [mul_zero] at hc
      omega
    · rw [mul_one] at hc
      exact h4 hc.symm
  rw [hc]
  nlinarith [hx]

variable {F : Type} [Field F] [Finite F]

theorem card_le_eight_of_pgl2 (hodd : IsOddPrimePower (Nat.card F)) (D : Sylow 2 (PSL2 F))
    (hD : Nat.card D = 4) (P₀ : Subgroup (PGL2 F)) (hP₀ : IsPGroup 2 P₀) : Nat.card P₀ ≤ 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Finite (PGL2 F) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  obtain ⟨S, hS⟩ := hP₀.exists_le_sylow
  have h1 := Sylow.card_eq_multiplicity D
  have h2 := Sylow.card_eq_multiplicity S
  have hne : Nat.card (PSL2 F) ≠ 0 := Nat.card_pos.ne'
  rw [pgl2_card_eq_two_mul hodd, Nat.factorization_mul two_ne_zero hne, Finsupp.add_apply,
    Nat.Prime.factorization_self Nat.prime_two, pow_add, pow_one, ← h1, hD] at h2
  calc Nat.card P₀ ≤ Nat.card S := card_le_of_le hS
    _ = 8 := by omega

variable {Y : Type} [Group Y] [Finite Y] (e : Y ≃* PSL2 F)

include e in
theorem two_generated_l2 {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hF : Nat.card F = p ^ f) (R : Sylow 2 Y)
    (hab : ∀ a ∈ (R : Subgroup Y), ∀ b ∈ (R : Subgroup Y), a * b = b * a)
    (P : Subgroup (MulAut Y)) (hP : IsPGroup 2 P) :
    ∃ s : Finset (MulAut Y), s.card ≤ 2 ∧ closure (s : Set (MulAut Y)) = P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd := isOddPrimePower_of hp hp2 hf hF
  let : Finite (PGL2 F) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  obtain ⟨hR4, hfo⟩ := not_even_of_abelian e hp hp2 hf hF R hab
  have hinl : Function.Injective (SemidirectProduct.inl : PGL2 F →* PGammaL2 F) :=
    SemidirectProduct.inl_injective
  have hPr : ∀ x ∈ P, (autEquiv e x).right = 1 := fun x hx => by
    obtain ⟨k, hk⟩ := hP ⟨x, hx⟩
    have hk' : x ^ 2 ^ k = 1 := congrArg Subtype.val hk
    exact right_eq_one_of_odd hp hF hfo (autEquiv e x) (k := k) (by rw [← map_pow, hk', map_one])
  set P₀ : Subgroup (PGL2 F) :=
    (P.map (autEquiv e).toMonoidHom).comap (SemidirectProduct.inl : PGL2 F →* PGammaL2 F)
    with hP₀
  have hmap : P₀.map (SemidirectProduct.inl : PGL2 F →* PGammaL2 F) =
      P.map (autEquiv e).toMonoidHom := by
    apply le_antisymm (map_comap_le _ _)
    rintro _ ⟨x, hx, rfl⟩
    have hx' := eq_inl_of_right_eq_one (hPr x hx)
    refine ⟨(autEquiv e x).left, ?_, hx'.symm⟩
    show SemidirectProduct.inl (autEquiv e x).left ∈ P.map (autEquiv e).toMonoidHom
    rw [← hx']
    exact ⟨x, hx, rfl⟩
  have hcard : Nat.card P₀ = Nat.card P := by
    have h1 := card_map_of_injective (K := P₀) hinl
    have h2 := card_map_of_injective (f := (autEquiv e).toMonoidHom) (K := P)
      (autEquiv e).injective
    rw [hmap] at h1
    rw [← h1, h2]
  have hP₀2 : IsPGroup 2 P₀ := by
    have : Finite P := Nat.finite_of_card_ne_zero (by rw [← hcard]; exact Nat.card_pos.ne')
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP
    exact IsPGroup.of_card (by rw [hcard, hk])
  have h8 := card_le_eight_of_pgl2 hodd (sylowMap e R) (by rw [card_sylowMap, hR4]) P₀ hP₀2
  have hE : Nat.card P = 8 → ∃ x ∈ P, x * x ≠ 1 := by
    intro h8'
    by_contra hall
    push Not at hall
    have hsq : ∀ g ∈ P₀, g * g = 1 := by
      intro g hg
      obtain ⟨x, hx, hxg⟩ := hg
      apply hinl
      rw [map_mul, ← hxg, ← map_mul, hall x hx, map_one, map_one]
    have := pgl2_card_le_four_of_sq hodd P₀ hsq
    omega
  have : Finite P := Nat.finite_of_card_ne_zero (by rw [← hcard]; exact Nat.card_pos.ne')
  exact exists_two_gen_of_card_le_eight P hP (by rw [← hcard]; exact h8) hE

end CFSG.ComponentClassification.FooteLit.Aut5L2
