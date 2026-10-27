module

public import Mathlib.GroupTheory.Perm.Cycle.Type

public section

namespace CFSG.EvenSporadicStandard.RuStd

open Subgroup

theorem commute_of_normalizing_order_thirteen {G : Type*} [Group G] [Finite G] {R : Subgroup G}
    {f : G} (hf : orderOf f = 13) (hnorm : ∀ r ∈ R, f * r * f⁻¹ ∈ R)
    (hcard : Nat.card R ∣ 256) : ∀ r ∈ R, f * r = r * f := by
  classical
  have : Fact (Nat.Prime 13) := ⟨by decide⟩
  have := Fintype.ofFinite R
  let σ₀ : R → R := fun r => ⟨f * r * f⁻¹, hnorm r r.2⟩
  have hinj : Function.Injective σ₀ := fun r s h => by
    apply Subtype.ext
    have := congrArg Subtype.val h
    simpa [σ₀] using this
  let σ : Equiv.Perm R := Equiv.ofBijective σ₀ (Finite.injective_iff_bijective.1 hinj)
  have hσ : ∀ (n : ℕ) (r : R), ((σ ^ n) r : G) = f ^ n * r * (f ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro r; simp
    | succ n ih =>
      intro r
      rw [pow_succ', Equiv.Perm.mul_apply]
      show f * ((σ ^ n) r : G) * f⁻¹ = _
      rw [ih]
      group
  have hf13 : f ^ 13 = 1 := by rw [← hf]; exact pow_orderOf_eq_one f
  have hσ13 : σ ^ 13 ^ 1 = 1 := by
    rw [pow_one]
    ext r
    rw [hσ, hf13]
    simp
  have hmod := Equiv.Perm.card_compl_support_modEq hσ13
  let e : {x : R // σ x = x} ≃ ↥(R ⊓ centralizer ({f} : Set G)) :=
    { toFun := fun x => ⟨(x.1 : G), x.1.2, mem_centralizer_singleton_iff.2 (by
        have h := congrArg Subtype.val x.2
        change f * (x.1 : G) * f⁻¹ = (x.1 : G) at h
        calc (x.1 : G) * f = (f * (x.1 : G) * f⁻¹) * f := by rw [h]
          _ = f * (x.1 : G) := by group)⟩
      invFun := fun y => ⟨⟨y.1, y.2.1⟩, Subtype.ext (by
        have h := mem_centralizer_singleton_iff.1 y.2.2
        change f * (y.1 : G) * f⁻¹ = (y.1 : G)
        calc f * (y.1 : G) * f⁻¹ = ((y.1 : G) * f) * f⁻¹ := by rw [h]
          _ = (y.1 : G) := by group)⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }
  have hfix : (σ.supportᶜ).card = Nat.card ↥(R ⊓ centralizer ({f} : Set G)) := by
    have hs : (σ.supportᶜ : Finset R) = Finset.univ.filter (fun x => σ x = x) := by
      ext x
      simp [Equiv.Perm.mem_support]
    rw [hs, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card, Nat.card_congr e]
  rw [hfix, ← Nat.card_eq_fintype_card] at hmod
  have hdvd : Nat.card ↥(R ⊓ centralizer ({f} : Set G)) ∣ Nat.card R :=
    Subgroup.card_dvd_of_le inf_le_left
  have key : ∀ n ∈ Nat.divisors 256, ∀ c ∈ Nat.divisors n, c ≡ n [MOD 13] → c = n := by decide
  have heq : Nat.card ↥(R ⊓ centralizer ({f} : Set G)) = Nat.card R :=
    key _ (Nat.mem_divisors.2 ⟨hcard, by norm_num⟩) _
      (Nat.mem_divisors.2 ⟨hdvd, Nat.card_pos.ne'⟩) hmod
  have hRC : R ⊓ centralizer ({f} : Set G) = R :=
    Subgroup.eq_of_le_of_card_ge inf_le_left heq.ge
  intro r hr
  have : r ∈ R ⊓ centralizer ({f} : Set G) := by rw [hRC]; exact hr
  exact (mem_centralizer_singleton_iff.1 this.2).symm

end CFSG.EvenSporadicStandard.RuStd
