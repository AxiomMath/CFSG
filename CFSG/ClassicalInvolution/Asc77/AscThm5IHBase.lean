module

public import CFSG.ClassicalInvolution.Asc77.AscE186CentA
public import CFSG.ClassicalInvolution.Asc77.AscIH8Bridge
public import CFSG.ClassicalInvolution.Asc77.WP3Hyp51

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
open scoped commutatorElement MatrixGroups

@[expose] def T5Base (p f : ℕ) [Fact p.Prime] : Prop :=
  p ≠ 2 → 5 ≤ p ^ f →
    ∀ (t : StatedLieTag) (k e : ℕ), IsFundTag t → StatedLieAdmissible t k p e →
      (e = f ∨ (t = .trialityD4 ∧ 3 * e = f)) →
      ∀ (H : Type) [Group H] [Finite H] (ψ : (modelUniv t k p e Fact.out).K →* H),
        ψ.ker ≤ Subgroup.center (modelUniv t k p e Fact.out).K →
        ∀ R ∈ fundamentalSubgroups t (modelUniv t k p e Fact.out).D,
          ∀ R' ∈ fundamentalSubgroups t (modelUniv t k p e Fact.out).D,
            Nonempty (↥(R.map ψ) ≃* SL(2, GaloisField p f)) →
            Nonempty (↥(R'.map ψ) ≃* SL(2, GaloisField p f)) →
            R.map ψ ≠ R'.map ψ → Commutes (R.map ψ) (R'.map ψ) →
            ∀ z : H, IsUniqueInvolution (R.map ψ) z →
              ∀ A : Subgroup H, IsElemAbelian2 A 2 → A ≤ R.map ψ ⊔ R'.map ψ → z ∈ A →
                (∀ a ∈ A, a ≠ 1 → ¬ ∀ x ∈ ψ.range, a * x = x * a) →
                  alphaOf (inducedImage ψ.range A) = ⊥

section Faithful

variable {G : Type} [Group G]

theorem thm5IH_exists_ne {A : Subgroup G} (hA4 : Nat.card A = 4) (x y : G) :
    ∃ u ∈ A, u ≠ x ∧ u ≠ y := by
  by_contra h
  push Not at h
  have hsub : (A : Set G) ⊆ {x, y} := fun u hu => by
    by_cases hux : u = x
    · exact Or.inl hux
    · exact Or.inr (h u hu hux)
  have h1 : (A : Set G).ncard ≤ ({x, y} : Set G).ncard :=
    Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 : ({x, y} : Set G).ncard ≤ 2 :=
    (Set.ncard_insert_le x {y}).trans (by simp)
  have h3 : (A : Set G).ncard = 4 := by rw [← hA4]; exact (Nat.card_coe_set_eq _).symm
  omega

theorem thm5IH_center_of_exact {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F))
    {K : Subgroup G} {z : G} (hz : IsUniqueInvolution K z) (e : ↥K ≃* SL(2, F)) :
    ∀ w ∈ K, (∀ x ∈ K, w * x = x * w) → w = 1 ∨ w = z := by
  intro w hw hc
  have hord : orderOf z = 2 := orderOf_eq_prime (by rw [sq]; exact hz.sq) hz.ne_one
  have hzinv : z = sl2Inv e := eq_sl2Inv_of_orderOf_eq_two hodd e hz.mem hord
  rcases eq_one_or_eq_sl2Inv_of_central e hw hc with h | h
  · exact Or.inl h
  · exact Or.inr (h.trans hzinv.symm)

theorem thm5IH_exists_centralizing {K J L A : Subgroup G} {z : G} (hKJ : Commutes K J)
    (hz : IsUniqueInvolution K z) (hZ : ∀ w ∈ K, (∀ x ∈ K, w * x = x * w) → w = 1 ∨ w = z)
    (hA2 : ∀ a ∈ A, a * a = 1) (hA4 : Nat.card A = 4) (hAKJ : A ≤ K ⊔ J) (hzA : z ∈ A)
    (hAN : A ≤ Subgroup.normalizer (L : Set G)) (hJL : ∀ j ∈ J, ∀ x ∈ L, j * x = x * j) :
    ∃ a ∈ A, a ≠ 1 ∧ ∀ x ∈ L, a * x = x * a := by
  by_cases hzL : ∀ x ∈ L, z * x = x * z
  · exact ⟨z, hzA, hz.ne_one, hzL⟩
  obtain ⟨u, huA, hu1, huz⟩ := thm5IH_exists_ne hA4 1 z
  obtain ⟨k, hk, j, hj, hkj⟩ := AscE186.exists_mul_of_mem_sup_of_commutes hKJ (hAKJ huA)
  have huu : u * u = 1 := hA2 u huA
  have hkjc : k * j = j * k := hKJ k hk j hj
  have hkk : k * k = (j * j)⁻¹ := by
    have h : (k * k) * (j * j) = 1 := by
      calc (k * k) * (j * j) = k * (k * j) * j := by group
        _ = k * (j * k) * j := by rw [hkjc]
        _ = (k * j) * (k * j) := by group
        _ = u * u := by rw [hkj]
        _ = 1 := huu
    exact eq_inv_of_mul_eq_one_left h
  have hkkJ : k * k ∈ J := by
    rw [hkk]
    exact J.inv_mem (J.mul_mem hj hj)
  have hkkc : ∀ x ∈ K, (k * k) * x = x * (k * k) := fun x hx => (hKJ x hx _ hkkJ).symm
  rcases hZ (k * k) (K.mul_mem hk hk) hkkc with h | h
  ·
    rcases hz.unique k hk h with hk1 | hkz
    · have huj : u = j := by rw [← hkj, hk1, one_mul]
      refine ⟨u, huA, hu1, fun x hx => ?_⟩
      rw [huj]
      exact hJL j hj x hx
    · have hzj : z * j = u := by rw [← hkj, hkz]
      have hjzu : j = z * u := by
        calc j = (z * z) * j := by rw [hz.sq, one_mul]
          _ = z * (z * j) := by group
          _ = z * u := by rw [hzj]
      have hjA : j ∈ A := by rw [hjzu]; exact A.mul_mem hzA huA
      have hj1 : j ≠ 1 := by
        intro hj1
        apply huz
        rw [← hzj, hj1, mul_one]
      exact ⟨j, hjA, hj1, fun x hx => hJL j hj x hx⟩
  ·
    exfalso
    apply hzL
    intro x hx
    have hky : ∀ y ∈ L, k * y * k⁻¹ = u * y * u⁻¹ := by
      intro y hy
      have hk' : k = u * j⁻¹ := by rw [← hkj]; group
      have hjy : j⁻¹ * y * j = y := by
        have h1 : j⁻¹ * y = y * j⁻¹ := hJL j⁻¹ (J.inv_mem hj) y hy
        rw [h1]
        group
      calc k * y * k⁻¹ = (u * j⁻¹) * y * (u * j⁻¹)⁻¹ := by rw [← hk']
        _ = u * (j⁻¹ * y * j) * u⁻¹ := by group
        _ = u * y * u⁻¹ := by rw [hjy]
    have huxL : u * x * u⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hAN huA) x).mp hx
    have hzx : z * x * z⁻¹ = x := by
      calc z * x * z⁻¹ = (k * k) * x * (k * k)⁻¹ := by rw [h]
        _ = k * (k * x * k⁻¹) * k⁻¹ := by group
        _ = k * (u * x * u⁻¹) * k⁻¹ := by rw [hky x hx]
        _ = u * (u * x * u⁻¹) * u⁻¹ := hky _ huxL
        _ = (u * u) * x * (u * u)⁻¹ := by group
        _ = x := by rw [huu]; group
    have h2 : z * x * z⁻¹ * z = x * z := by rw [hzx]
    simpa using h2

end Faithful

end CFSG.ClassicalInvolution.Asc77
