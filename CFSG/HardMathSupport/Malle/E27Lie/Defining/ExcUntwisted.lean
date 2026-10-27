module

public import CFSG.HardMathSupport.Malle.Proving.E27CommutatorQuotient
public import CFSG.HardMathSupport.Foote.E27.SporSylowBound
public import CFSG.HardMathSupport.Foote.E27.SporKill
public import CFSG.LieType.Chevalley.SylowOpposition
public import CFSG.LieType.Chevalley.GraphFixedOrbitCollection

public section

namespace CFSG.HardMathSupport.Malle.E27Lie

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Foote.E27


theorem false_of_adjointGroup_char_three {X : Type} [Group X] [Finite X] {K R T : Subgroup X}
    {z : X} (h : E27Config X K R T z) (hz : z ∈ K) (τ : Tag) (F : Type) [Field F] [Finite F]
    [CharP F 3] (e : ↥K ≃* adjointGroup τ F)
    (hroots : {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α ∧ 2 ≤ height α}.ncard + τ.rank =
      {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α ∧ 1 ≤ height α}.ncard)
    (h81 : 81 ≤ Nat.card F ^ τ.rank) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (adjointGroup τ F) := Finite.of_equiv _ e.toEquiv
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element τ
  obtain ⟨⟨P, hP⟩, -⟩ := exceptional_ordinary_Sylow_opposition τ F 3 w₀ hw₀
  obtain ⟨h1, -, hle, hcomm, -, -, hcard⟩ := positive_root_height_series τ F
  have hUG : posUnipotent τ F ≤ (adjointGroup τ F) := rootSpan_le_adjointGroup F _
  have hU2G : heightSeries τ F 2 ≤ (adjointGroup τ F) :=
    (hle 2 (by norm_num)).1.trans hUG
  let N : Subgroup (adjointGroup τ F) := (heightSeries τ F 2).subgroupOf (adjointGroup τ F)
  have hPc : ⁅(P : Subgroup (adjointGroup τ F)), (P : Subgroup (adjointGroup τ F))⁆ ≤ N := by
    rw [hP]
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    have hmap := Subgroup.map_commutator ((posUnipotent τ F).subgroupOf (adjointGroup τ F))
      ((posUnipotent τ F).subgroupOf (adjointGroup τ F)) (adjointGroup τ F).subtype
    have hsub : ((posUnipotent τ F).subgroupOf (adjointGroup τ F)).map
        (adjointGroup τ F).subtype = posUnipotent τ F :=
      Subgroup.map_subgroupOf_eq_of_le hUG
    rw [hsub] at hmap
    have hx' : (x : ModGL τ F) ∈ (⁅(posUnipotent τ F).subgroupOf (adjointGroup τ F),
        (posUnipotent τ F).subgroupOf (adjointGroup τ F)⁆).map (adjointGroup τ F).subtype :=
      ⟨x, hx, rfl⟩
    rw [hmap] at hx'
    have hc := hcomm 1 1 le_rfl le_rfl
    rw [h1] at hc
    exact hc hx'
  have hcardP : Nat.card (P : Subgroup (adjointGroup τ F)) =
      Nat.card F ^ {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α ∧ 1 ≤ height α}.ncard := by
    rw [hP, ← hcard 1 le_rfl, ← h1]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (h1 ▸ hUG)).toEquiv
  have hcardN : Nat.card N =
      Nat.card F ^ {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α ∧ 2 ≤ height α}.ncard := by
    rw [← hcard 2 (by norm_num)]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hU2G).toEquiv
  have h81' : 81 * Nat.card N ≤ Nat.card (P : Subgroup (adjointGroup τ F)) := by
    rw [hcardP, hcardN, ← hroots, pow_add, mul_comm]
    exact Nat.mul_le_mul_left _ h81
  obtain ⟨S₀⟩ := (inferInstance : Nonempty (Sylow 3 ↥K))
  refine h.false_of_sylow_kill hz S₀ fun s hs hs3 => Or.inl ?_
  exact dvd81_card_sylow_inf_centralizer_of_equiv e (P : Subgroup (adjointGroup τ F))
    P.card_eq_multiplicity
    (fun w hw _ => Proving.eighty_one_dvd_inf_centralizer_of_commutator_le P N hPc h81' hw)
    S₀ hs hs3

end CFSG.HardMathSupport.Malle.E27Lie
