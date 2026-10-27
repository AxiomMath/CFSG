module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Broad
public import CFSG.Sporadic.McL.Simple
public import CFSG.Sporadic.Ly.Primitive

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG

theorem center_eq_bot_of_isSimpleGroup_of_not_prime {Q : Type} [Group Q] [IsSimpleGroup Q]
    (hp : ¬ (Nat.card Q).Prime) : center Q = ⊥ := by
  rcases (inferInstance : (center Q).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    have hcomm : ∀ a b : Q, a * b = b * a := fun a b =>
      Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a
    let _ : CommGroup Q := { ‹Group Q› with mul_comm := hcomm }
    exact hp IsSimpleGroup.prime_card

theorem mcLLyCenterFree :
    McLLyCenterFree := by
  intro Q _ hQ
  rcases hQ with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · have h : IsSimpleGroup Blueprint.NativeSporadic.McL := Sporadic.McL.isSimpleGroup_McL
    have : IsSimpleGroup Q := @MulEquiv.isSimpleGroup _ _ _ _ h e
    refine center_eq_bot_of_isSimpleGroup_of_not_prime ?_
    rw [Nat.card_congr e.toEquiv, Sporadic.McL.card_McL]
    norm_num
  · have h : IsSimpleGroup Blueprint.NativeSporadic.Ly := Sporadic.Ly.isSimpleGroup_Ly
    have : IsSimpleGroup Q := @MulEquiv.isSimpleGroup _ _ _ _ h e
    refine center_eq_bot_of_isSimpleGroup_of_not_prime ?_
    rw [Nat.card_congr e.toEquiv, Sporadic.Ly.card_Ly']
    norm_num

theorem solLemma31 : SolLemma31 :=
  solLemma31_of_centerFree mcLLyCenterFree

end CFSG.OddStandard.Solomon75
