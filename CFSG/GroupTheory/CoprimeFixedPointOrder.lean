module

public import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting

public section

namespace CFSG.GroupTheory

open CFSG.Semidihedral.Principal.CoprimeFixedPoint

variable {H : Type} {X : Type} [Group H] [Finite H] [Group X]

theorem exists_orderOf_eq_fixed_of_coprime_ker (φ : H →* X) (hφ : Function.Surjective φ)
    (ρ : MulAut H) (θ : MulAut X) (hcomm : ∀ h : H, φ (ρ h) = θ (φ h)) {p : ℕ} (hp : p.Prime)
    (hρ : orderOf ρ ∣ p) (hcop : ¬ p ∣ Nat.card φ.ker) {n : ℕ} {x : X} (hxn : orderOf x = n)
    (hxfix : θ x = x) : ∃ y : H, orderOf y = n ∧ ρ y = y := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨h₀, hh₀⟩ := hφ x
  let S : Set H := {h | φ h = x}
  let K : Subgroup (MulAut H) :=
    { carrier := {a | ∀ h ∈ S, a h ∈ S}
      one_mem' := by intro h hh; simpa using hh
      mul_mem' := by intro a b ha hb h hh; exact ha _ (hb h hh)
      inv_mem' := by
        intro a ha h hh
        have hsub : a '' S ⊆ S := by rintro _ ⟨y, hy, rfl⟩; exact ha y hy
        have hcard : (a '' S).ncard = S.ncard := Set.ncard_image_of_injective S a.injective
        have heq : a '' S = S := Set.eq_of_subset_of_ncard_le hsub (le_of_eq hcard.symm)
        obtain ⟨y, hy, hyh⟩ := heq.symm ▸ hh
        have hinv : a⁻¹ h = y := by
          rw [← hyh]
          simp
        rwa [hinv] }
  have hρK : ρ ∈ K := by
    intro h hh
    show φ (ρ h) = x
    rw [hcomm, show φ h = x from hh, hxfix]
  have hAle : Subgroup.zpowers ρ ≤ K := Subgroup.zpowers_le.mpr hρK
  have hS : ∀ a : ↥(Subgroup.zpowers ρ), ∀ h ∈ S, (a : MulAut H) h ∈ S :=
    fun a h hh => hAle a.2 h hh
  have hcardS : Nat.card S = Nat.card φ.ker :=
    Nat.card_congr
      { toFun := fun h => ⟨h.1 * h₀⁻¹, by
          show φ (h.1 * h₀⁻¹) = 1
          rw [map_mul, map_inv, h.2, hh₀, mul_inv_cancel]⟩
        invFun := fun k => ⟨(k : H) * h₀, by
          show φ ((k : H) * h₀) = x
          rw [map_mul, MonoidHom.mem_ker.mp k.2, one_mul, hh₀]⟩
        left_inv := fun h => Subtype.ext (by group)
        right_inv := fun k => Subtype.ext (by group) }
  have hA : IsPGroup p ↥(Subgroup.zpowers ρ) := by
    have hcard : Nat.card ↥(Subgroup.zpowers ρ) = orderOf ρ := Nat.card_zpowers ρ
    rcases (Nat.dvd_prime hp).mp hρ with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [hcard, h]; simp)
    · exact IsPGroup.of_card (n := 1) (by rw [hcard, h]; simp)
  obtain ⟨c, hcS, hcfix⟩ :=
    exists_fixed_of_invariant p hA (Subgroup.zpowers ρ).subtype S hS
      (by rw [hcardS]; exact hcop)
  have hcρ : ρ c = c := hcfix ⟨ρ, Subgroup.mem_zpowers ρ⟩
  have hcφ : φ c = x := hcS
  have hn : n ∣ orderOf c := by
    have h := orderOf_map_dvd φ c
    rw [hcφ, hxn] at h
    exact h
  refine ⟨c ^ (orderOf c / n), orderOf_pow_orderOf_div (orderOf_pos c).ne' hn, ?_⟩
  rw [map_pow, hcρ]

end CFSG.GroupTheory

end
