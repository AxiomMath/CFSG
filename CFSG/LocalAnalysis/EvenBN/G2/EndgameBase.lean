module

public import CFSG.LocalAnalysis.EvenBN.G2.NotCentral
public import CFSG.LocalAnalysis.EvenBN.Common.Diagonal

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem isPerfect (h : Setup G L f t) : Group.IsPerfect G := by
  have := h.simple
  refine ⟨?_⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator G) with hb | ht
  · exfalso
    obtain ⟨a, b, hab⟩ := h.nonab
    have h1 := commutator_mem_commutator (mem_top a) (mem_top b)
    rw [← _root_.commutator_def, hb, mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact hab h1
  · exact ht

theorem exists_mul_ne_mul_of_mem_L (h : Setup G L f t) : ∃ x ∈ L, ∃ y ∈ L, x * y ≠ y * x := by
  by_contra hcon
  push Not at hcon
  have hab : ⁅L, L⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.2 fun x hx =>
    mem_centralizer_iff.2 fun y hy => hcon y hy x hx
  apply h.not_normal
  rw [← h.commutator_L, hab]
  infer_instance

theorem chevalleyExceptionalModel_L (h : Setup G L f t) :
    ChevalleyExceptionalModel L .G2 2 f := by
  have hm := h.model
  simp only [LieModel, classicalTags, chevalleyExceptionalTags, reeTitsTags, Finset.mem_insert,
    Finset.mem_singleton, reduceCtorEq, false_and, false_or, or_false, and_false, true_and,
    or_true] at hm
  exact hm

section Cert

theorem odd_card_ker_diagonalHom (h : Setup G L f t) {G₀ : Subgroup G}
    (hcomm : ⁅G₀, G₀.map (MulAut.conj t⁻¹).toMonoidHom⁆ = ⊥)
    (hL : (Common.diagonalHom G₀ t hcomm).range = L) :
    Odd (Nat.card (Common.diagonalHom G₀ t hcomm).ker) :=
  Common.odd_card_ker_diagonalHom_of_centralizer_le hcomm h.t_mul_t
    (by rw [hL]; exact (h.centralizer_L_inf).le)
    (by rw [hL]; exact h.exists_mul_ne_mul_of_mem_L)

theorem yamada_7_20 (h : Setup G L f t) {G₀ : Subgroup G}
    (hcomm : ⁅G₀, G₀.map (MulAut.conj t⁻¹).toMonoidHom⁆ = ⊥) [Group.IsPerfect G₀]
    (hL : (Common.diagonalHom G₀ t hcomm).range = L) :
    G₀ ⊓ G₀.map (MulAut.conj t⁻¹).toMonoidHom = ⊥ ∧
      ∃ e : G₀ ≃* L, ∀ a : G₀, (e a : G) = (a : G) * (t⁻¹ * a * t) :=
  Common.diagonal_identification hcomm hL h.center_eq (h.odd_card_ker_diagonalHom hcomm hL)
    fun _ _ _ _ π hπ hC hodd =>
      CFSG.SectionRank.g2_even_perfect_odd_cover_trivial h.chevalleyExceptionalModel_L π hπ hC hodd

end Cert

end Setup

end CFSG.LocalAnalysis.EvenBN.G2
