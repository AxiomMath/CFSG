module

public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.GroupTheory.FT63ChII

open Subgroup CFSG.HallHigman
open scoped commutatorElement Pointwise

universe u

variable {p : ℕ} [hp : Fact p.Prime]

section Solvability

theorem card_eq_of_isSimpleGroup_of_isPGroup {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hG : IsPGroup p G) : Nat.card G = p := by
  have : Nontrivial G := IsSimpleGroup.toNontrivial
  have hZ : Nontrivial (center G) := hG.center_nontrivial
  obtain ⟨k, hk⟩ := (hG.to_subgroup (center G)).exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    exact (Finite.one_lt_card_iff_nontrivial.2 hZ).ne' hk
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := center G) p (hk ▸ dvd_pow_self p hk0)
  have hZle : zpowers (z : G) ≤ center G := (zpowers_le (G := G)).2 z.2
  have hnorm : (zpowers (z : G)).Normal := ⟨fun x hx g => by
    rw [(mem_center_iff.1 (hZle hx) g), mul_inv_cancel_right]
    exact hx⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (zpowers (z : G)) with h | h
  · exfalso
    have hz1 : (z : G) = 1 := by
      have := mem_zpowers (z : G)
      rwa [h, mem_bot] at this
    have : orderOf z = 1 := by rw [← Subgroup.orderOf_coe, hz1, orderOf_one]
    rw [this] at hz
    exact hp.out.one_lt.ne hz
  · rw [← card_top (G := G), ← h, Nat.card_zpowers, Subgroup.orderOf_coe, hz]

theorem isPSolvable_of_isPiSeparable {X : Type*} [Group X] [Finite X]
    (hX : IsPiSeparable {q : Nat.Primes | q.val = p} X) : IsPSolvable p X := by
  intro H hH T _ hs
  rcases hX H hH T hs with h | h
  · left
    have hp' : IsPGroup p (H ⧸ T) := by
      rw [IsPGroup.iff_card]
      exact ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' fun {d} hd hdvd =>
        h ⟨d, hd⟩ hdvd⟩
    exact card_eq_of_isSimpleGroup_of_isPGroup hp'
  · right
    exact (Nat.Prime.coprime_iff_not_dvd hp.out).2 fun hdvd => h ⟨p, hp.out⟩ hdvd rfl

theorem isPiSeparable_of_le {X : Type u} [Group X] [Finite X] {π : Set Nat.Primes}
    {K L : Subgroup X} (hKL : K ≤ L) (hL : IsPiSeparable π L) : IsPiSeparable π K :=
  fun H _ T _ hs => IsPiSeparable.section_index _ rfl hL ((Subgroup.inclusion hKL).comp H.subtype)
    ((Subgroup.inclusion_injective hKL).comp H.subtype_injective) T hs

end Solvability

section Commutators

variable {Y : Type*} [Group Y]

theorem le_normalizer_commutator {H₁ H₂ K : Subgroup Y} (h₁ : K ≤ normalizer (H₁ : Set Y))
    (h₂ : K ≤ normalizer (H₂ : Set Y)) : K ≤ normalizer ((⁅H₁, H₂⁆ : Subgroup Y) : Set Y) := by
  have key : ∀ g ∈ K, ∀ x ∈ ⁅H₁, H₂⁆, g * x * g⁻¹ ∈ ⁅H₁, H₂⁆ := by
    intro g hg x hx
    have : (⁅H₁, H₂⁆).map (MulAut.conj g).toMonoidHom ≤ ⁅H₁, H₂⁆ := by
      rw [map_commutator]
      apply commutator_mono
      · rintro _ ⟨y, hy, rfl⟩
        exact (mem_normalizer_iff.1 (h₁ hg) y).1 hy
      · rintro _ ⟨y, hy, rfl⟩
        exact (mem_normalizer_iff.1 (h₂ hg) y).1 hy
    exact this ⟨x, hx, rfl⟩
  intro g hg
  rw [mem_normalizer_iff]
  intro x
  refine ⟨key g hg x, fun hx => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hx
  simpa [mul_assoc] using this

theorem commutator_le_of_le_normalizer {V A : Subgroup Y} (h : A ≤ normalizer (V : Set Y)) :
    ⁅V, A⁆ ≤ V := by
  rw [commutator_le]
  intro v hv a ha
  have := (mem_normalizer_iff.1 (h ha) v⁻¹).1 (inv_mem hv)
  simpa [commutatorElement_def, mul_assoc] using mul_mem hv this

theorem eq_bot_of_commutator_eq [Finite Y] {V A : Subgroup Y} (hV : IsPGroup p V)
    (hA : IsPGroup p A) (hAV : A ≤ normalizer (V : Set Y)) (h : ⁅V, A⁆ = V) : V = ⊥ := by
  have hT : IsPGroup p ↥(V ⊔ A) := hV.to_sup_of_normal_left' hA hAV
  obtain ⟨n, hn⟩ := (isNilpotent_iff_lowerCentralSeries (V ⊔ A)).1 hT.isNilpotent
  have hle : ∀ k, V ≤ (V ⊔ A).lowerCentralSeries k := by
    intro k
    induction k with
    | zero => exact le_sup_left
    | succ k ih =>
      rw [Subgroup.lowerCentralSeries_succ]
      calc V = ⁅V, A⁆ := h.symm
        _ ≤ ⁅(V ⊔ A).lowerCentralSeries k, V ⊔ A⁆ := commutator_mono ih le_sup_right
  exact le_bot_iff.1 (hn ▸ hle n)

theorem le_normalizer_inf_of_le {H₁ H₂ K : Subgroup Y}
    (h₁ : K ≤ normalizer (H₁ : Set Y)) (h₂ : K ≤ normalizer (H₂ : Set Y)) :
    K ≤ normalizer ((H₁ ⊓ H₂ : Subgroup Y) : Set Y) := fun g hg => mem_normalizer_iff.2 fun x => by
  rw [mem_inf, mem_inf, mem_normalizer_iff.1 (h₁ hg) x, mem_normalizer_iff.1 (h₂ hg) x]

end Commutators

end CFSG.GroupTheory.FT63ChII
