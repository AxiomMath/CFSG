module

public import CFSG.LocalAnalysis.OddStandard.ThmCTFacts

public section

namespace CFSG.OddStandard.ThmC.T

open CFSG.GH74.GLS.Bg.TwoGroups CFSG.GH74.GLS.Bg.TwoGroups.L23

theorem solve_commuting : ∀ xa xb ya yb ga gb : F4c, xa * yb ≠ ya * xb →
    ga * xb = xa * gb → ga * yb = ya * gb → ga = 0 ∧ gb = 0 := by decide +kernel

theorem mem_center_of_commute_noncommuting {x y g : Tc} (hxy : x * y ≠ y * x)
    (hgx : g * x = x * g) (hgy : g * y = y * g) : g ∈ Subgroup.center Tc := by
  rw [mem_center_iff]
  rw [Ne, commute_iff] at hxy
  rw [commute_iff] at hgx hgy
  exact solve_commuting x.a x.b y.a y.b g.a g.b hxy hgx hgy

theorem IsT.mem_center_of_commute_noncommuting {P : Type*} [Group P] (hT : IsT P) {x y g : P}
    (hxy : x * y ≠ y * x) (hgx : g * x = x * g) (hgy : g * y = y * g) :
    g ∈ Subgroup.center P := by
  obtain ⟨e⟩ := hT.nonempty_equiv
  rw [mem_center_equiv_iff e]
  refine CFSG.OddStandard.ThmC.T.mem_center_of_commute_noncommuting (x := e x) (y := e y) ?_ ?_ ?_
  · intro h
    exact hxy (e.injective (by rw [map_mul, map_mul, h]))
  · rw [← map_mul, ← map_mul, hgx]
  · rw [← map_mul, ← map_mul, hgy]

theorem isPGroup_q8_prod : IsPGroup 2 (QuaternionGroup 2 × QuaternionGroup 2) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine IsPGroup.of_card (n := 6) ?_
  rw [Nat.card_prod, Nat.card_eq_fintype_card, QuaternionGroup.card]
  norm_num

theorem q8_noncomm : (QuaternionGroup.a 1 : QuaternionGroup 2) * QuaternionGroup.xa 0 ≠
    QuaternionGroup.xa 0 * QuaternionGroup.a 1 := by decide

theorem not_isT_of_q8_pair {K : Type} [Group K] [Finite K] (T : Sylow 2 K)
    (hT : IsT (T : Subgroup K)) (α₁ α₂ : QuaternionGroup 2 →* K)
    (hc : ∀ a b, Commute (α₁ a) (α₂ b)) (h₁ : Function.Injective α₁)
    (h₂ : Function.Injective α₂) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set α : QuaternionGroup 2 × QuaternionGroup 2 →* K := MonoidHom.noncommCoprod α₁ α₂ hc with hα
  have hN : IsPGroup 2 α.range :=
    isPGroup_q8_prod.of_surjective α.rangeRestrict α.rangeRestrict_surjective
  obtain ⟨T', hNT'⟩ := hN.exists_le_sylow
  have hT' : IsT (T' : Subgroup K) := hT.map fun e => (Sylow.equiv T' T).trans e
  have hα1 : ∀ a, α₁ a ∈ (T' : Subgroup K) := fun a =>
    hNT' ⟨(a, 1), by rw [hα, MonoidHom.noncommCoprod_apply, map_one, mul_one]⟩
  have hα2 : ∀ b, α₂ b ∈ (T' : Subgroup K) := fun b =>
    hNT' ⟨(1, b), by rw [hα, MonoidHom.noncommCoprod_apply, map_one, one_mul]⟩
  have hnc : (⟨α₁ (QuaternionGroup.a 1), hα1 _⟩ : (T' : Subgroup K)) *
      ⟨α₁ (QuaternionGroup.xa 0), hα1 _⟩ ≠ ⟨α₁ (QuaternionGroup.xa 0), hα1 _⟩ *
      ⟨α₁ (QuaternionGroup.a 1), hα1 _⟩ := by
    intro h
    apply q8_noncomm
    apply h₁
    have := congrArg Subtype.val h
    rw [map_mul, map_mul]
    exact this
  have hcent : ∀ b, (⟨α₂ b, hα2 b⟩ : (T' : Subgroup K)) ∈ Subgroup.center (T' : Subgroup K) := by
    intro b
    refine hT'.mem_center_of_commute_noncommuting hnc ?_ ?_
    · exact Subtype.ext (hc _ _).eq.symm
    · exact Subtype.ext (hc _ _).eq.symm
  apply q8_noncomm
  apply h₂
  have := Subgroup.mem_center_iff.1 (hcent (QuaternionGroup.a 1)) ⟨α₂ (QuaternionGroup.xa 0), hα2 _⟩
  have h3 := congrArg Subtype.val this
  rw [map_mul, map_mul]
  exact h3.symm

end CFSG.OddStandard.ThmC.T
