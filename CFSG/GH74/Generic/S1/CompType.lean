module

public import CFSG.GH74.Generic.S1.QuatRank
public import CFSG.GH74.KGH
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorQuaternion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalSmallSourceUnitary

public section

open Subgroup CFSG CFSG.GH74 CFSG.Assembly.LowTwoRank CFSG.GH74.Filter.ClassicalOdd
  CFSG.ComponentClassification

namespace CFSG.GH74.Generic.S1

theorem card_quot_center_le {Y : Type} [Group Y] [Finite Y] {M A : Subgroup Y} (hAM : A ≤ M) :
    Nat.card (↥A ⧸ center ↥A) ≤ Nat.card (↥M ⧸ center ↥M) := by
  let g : ↥A →* ↥M ⧸ center ↥M := (QuotientGroup.mk' (center ↥M)).comp (Subgroup.inclusion hAM)
  have hker : g.ker ≤ center ↥A := by
    intro a ha
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at ha
    rw [Subgroup.mem_center_iff]
    intro b
    apply Subgroup.inclusion_injective hAM
    have := Subgroup.mem_center_iff.1 ha (Subgroup.inclusion hAM b)
    simpa using this
  let q : ↥A ⧸ g.ker →* ↥A ⧸ center ↥A := QuotientGroup.map g.ker (center ↥A) (MonoidHom.id _) hker
  have hq : Function.Surjective q := by
    intro x
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    exact ⟨a, rfl⟩
  calc Nat.card (↥A ⧸ center ↥A) ≤ Nat.card (↥A ⧸ g.ker) := Nat.card_le_card_of_surjective _ hq
    _ = Nat.card g.range := Nat.card_congr (QuotientGroup.quotientKerEquivRange g).toEquiv
    _ ≤ Nat.card (↥M ⧸ center ↥M) := Nat.card_le_card_of_injective (Subtype.val) Subtype.val_injective


theorem component_type_of_gen4
    {Y : Type} [Group Y] [Finite Y] (hY : Gen4 Y) {M A : Subgroup Y} (hM : IsQuasisimple ↥M)
    (φ : Q8 →* Y) (hφ : Function.Injective φ) (hcent : ∀ a : Q8, ∀ m ∈ M, φ a * m = m * φ a)
    (hAM : A ≤ M) (hAodd : ∀ z ∈ A, (∀ w ∈ A, z * w = w * z) → Odd (orderOf z))
    (ψ : Q8 →* Y) (hψ : Function.Injective ψ) (hψA : ∀ g, ψ g ∈ A)
    (hbig : 62400 < Nat.card (↥A ⧸ center ↥A)) :
    (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ StatedClassicalModel (↥M ⧸ center ↥M) .PSL 3 p f) ∨
      (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ StatedClassicalModel (↥M ⧸ center ↥M) .PSU 3 p f) := by
  have : IsSimpleGroup (↥M ⧸ center ↥M) := hM.2.1
  have hnonab : ∃ a b : ↥M ⧸ center ↥M, a * b ≠ b * a := hM.2.2
  have heven := even_card_of_nonabelian_simple hnonab
  have hlow : 2 ≤ CFSG.Open.twoRank (↥M ⧸ center ↥M) :=
    CFSG.Milestones.lr_nonabelian_simple_two_rank_lower_bound (↥M ⧸ center ↥M) hnonab heven
  have hup := twoRank_le_two_of_quaternion_centralizer hY φ hφ hcent
  have hrank : CFSG.Open.twoRank (↥M ⧸ center ↥M) = 2 := le_antisymm hup hlow
  have hbigS : 62400 < Nat.card (↥M ⧸ center ↥M) :=
    lt_of_lt_of_le hbig (card_quot_center_le hAM)
  rcases CFSG.Milestones.lr_rank_two_isomorphism_types (↥M ⧸ center ↥M) hnonab hrank with
    ⟨p, f, hp, hp2, hf, h⟩ | ⟨p, f, hp, hp2, hf, h⟩ | ⟨p, f, hp, hp2, hf, h⟩ | h | h | h
  · exfalso
    have hψM : ∀ g, ψ g ∈ M := fun g => hAM (hψA g)
    let ψM : Q8 →* ↥M := ψ.codRestrict M hψM
    let τ : Q8 →* ↥M ⧸ center ↥M := (QuotientGroup.mk' (center ↥M)).comp ψM
    have ha2 : orderOf (QuaternionGroup.a 2 : Q8) = 2 :=
      orderOf_eq_prime (by decide) (by decide)
    have hord : orderOf (ψ (QuaternionGroup.a 2)) = 2 := by
      rw [orderOf_injective ψ hψ, ha2]
    have hτ : τ (QuaternionGroup.a 2) ≠ 1 := by
      intro h1
      have h2 : ψM (QuaternionGroup.a 2) ∈ center ↥M := (QuotientGroup.eq_one_iff _).1 h1
      have hc : ∀ w ∈ A, ψ (QuaternionGroup.a 2) * w = w * ψ (QuaternionGroup.a 2) := by
        intro w hw
        have := Subgroup.mem_center_iff.1 h2 ⟨w, hAM hw⟩
        exact (congrArg Subtype.val this).symm
      have hodd := hAodd _ (hψA _) hc
      rw [hord] at hodd
      exact absurd hodd (by decide)
    have hτinj : Function.Injective τ :=
      OddSelector.injective_of_quaternion τ hτ
    exact OddSelector.not_psl_two_odd_of_quaternion τ hτinj hp2 h
  · exact Or.inl ⟨p, f, hp, hp2, hf, h⟩
  · exact Or.inr ⟨p, f, hp, hp2, hf, h⟩
  · exfalso
    obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
    have : Nat.card (↥M ⧸ center ↥M) = 62400 := by
      rw [Nat.card_congr e.toEquiv]
      exact UnbalancingLocal.card_psu_three_four hK
    omega
  · exfalso
    obtain ⟨e⟩ := h
    have : Nat.card (↥M ⧸ center ↥M) = 2520 := by
      rw [Nat.card_congr e.toEquiv]
      exact UnbalancingLocal.card_alternating_seven
    omega
  · exfalso
    obtain ⟨e⟩ := h
    have : Nat.card (↥M ⧸ center ↥M) = 7920 := by
      rw [Nat.card_congr e.toEquiv]
      exact Semidihedral.GL2Recognition.card_lowTwoRankStatedM11
    omega

end CFSG.GH74.Generic.S1
