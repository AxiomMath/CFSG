module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.KC.SupPow

open Subgroup

theorem mem_normalizer_of_conj_mem {G : Type*} [Group G] {A : Subgroup G} [Finite A] {g : G}
    (h : ∀ a ∈ A, g * a * g⁻¹ ∈ A) : g ∈ normalizer (A : Set G) := by
  rw [mem_normalizer_iff]
  intro b
  refine ⟨h b, fun hb => ?_⟩
  let f : A → A := fun a => ⟨g * a * g⁻¹, h a a.2⟩
  have hf : Function.Injective f := fun a a' e => by
    have e' : g * (a : G) * g⁻¹ = g * (a' : G) * g⁻¹ := congrArg Subtype.val e
    exact Subtype.ext (by simpa using e')
  obtain ⟨a, ha⟩ := (Finite.injective_iff_surjective.1 hf) ⟨_, hb⟩
  have e : g * (a : G) * g⁻¹ = g * b * g⁻¹ := congrArg Subtype.val ha
  have e2 : (a : G) = b := by simpa using e
  exact e2 ▸ a.2

theorem pow_succ_dvd_card_sup {G : Type*} [Group G] [Finite G] {p k : ℕ} [hp : Fact p.Prime]
    (A : Subgroup G) (hA : Nat.card A = p ^ k) {g : G} (hn : ∀ a ∈ A, g * a * g⁻¹ ∈ A)
    (hg : g ∉ A) (hgp : g ^ p = 1) : p ^ (k + 1) ∣ Nat.card ↥(A ⊔ zpowers g) := by
  have hAp : IsPGroup p A := IsPGroup.of_card hA
  have hg1 : g ≠ 1 := fun e => hg (e ▸ A.one_mem)
  have hord : orderOf g = p := orderOf_eq_prime hgp hg1
  have hZ : IsPGroup p (zpowers g) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
  have hle : zpowers g ≤ normalizer (A : Set G) := zpowers_le.2 (mem_normalizer_of_conj_mem hn)
  have hK : IsPGroup p ↥(A ⊔ zpowers g) := IsPGroup.to_sup_of_normal_left' hAp hZ hle
  obtain ⟨m, hm⟩ := hK.exists_card_eq
  have hAK : A ≤ A ⊔ zpowers g := le_sup_left
  have hdvd : Nat.card A ∣ Nat.card ↥(A ⊔ zpowers g) := Subgroup.card_dvd_of_le hAK
  have hne : Nat.card A ≠ Nat.card ↥(A ⊔ zpowers g) := by
    intro e
    have hEq := Subgroup.eq_of_le_of_card_ge hAK e.symm.le
    exact hg (hEq ▸ (le_sup_right : zpowers g ≤ A ⊔ zpowers g) (mem_zpowers g))
  rw [hA, hm] at hdvd hne
  rw [hm]
  have hkm : k ≤ m := (Nat.pow_dvd_pow_iff_le_right hp.out.one_lt).1 hdvd
  have hkm' : k ≠ m := fun e => hne (e ▸ rfl)
  exact Nat.pow_dvd_pow p (by omega)

end CFSG.KC.SupPow

end
