module

public import CFSG.LocalAnalysis.EvenBN.Common.Diagonal
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.NotCentral

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem exists_mul_ne_mul_of_mem_L (h : Setup G L f t) : ∃ x ∈ L, ∃ y ∈ L, x * y ≠ y * x := by
  by_contra hcon
  push Not at hcon
  have hab : ⁅L, L⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.2 fun x hx =>
    mem_centralizer_iff.2 fun y hy => hcon y hy x hx
  apply h.not_normal
  rw [← h.commutator_L, hab]
  infer_instance

theorem chevalleyExceptionalModel_L (h : Setup G L f t) :
    ChevalleyExceptionalModel L .trialityD4 2 f := by
  have hm := h.model
  simp only [LieModel, classicalTags, chevalleyExceptionalTags, reeTitsTags, Finset.mem_insert,
    Finset.mem_singleton, reduceCtorEq, false_and, false_or, or_false, and_false, true_and,
    or_true] at hm
  exact hm

theorem odd_card_ker_diagonalHom (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    {G₀ : Subgroup G} (hcomm : ⁅G₀, G₀.map (MulAut.conj t⁻¹).toMonoidHom⁆ = ⊥)
    (hL : (Common.diagonalHom G₀ t hcomm).range = L) :
    Odd (Nat.card (Common.diagonalHom G₀ t hcomm).ker) :=
  Common.odd_card_ker_diagonalHom_of_centralizer_le hcomm h.t_mul_t
    (by rw [hL]; exact (h.centralizer_L_inf_of_data d).le)
    (by rw [hL]; exact h.exists_mul_ne_mul_of_mem_L)

section Cover

theorem yamada_7_25 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) {G₀ : Subgroup G}
    (hcomm : ⁅G₀, G₀.map (MulAut.conj t⁻¹).toMonoidHom⁆ = ⊥) [Group.IsPerfect G₀]
    (hL : (Common.diagonalHom G₀ t hcomm).range = L) :
    G₀ ⊓ G₀.map (MulAut.conj t⁻¹).toMonoidHom = ⊥ ∧
      ∃ e : G₀ ≃* L, ∀ a : G₀, (e a : G) = (a : G) * (t⁻¹ * a * t) :=
  Common.diagonal_identification hcomm hL h.center_eq (h.odd_card_ker_diagonalHom d hcomm hL)
    fun _ _ _ _ π hπ hC hodd =>
      CFSG.SectionRank.triality_even_perfect_odd_cover_trivial h.chevalleyExceptionalModel_L π
        hπ hC hodd

end Cover

end Setup

end CFSG.LocalAnalysis.EvenBN.TrialityD4
