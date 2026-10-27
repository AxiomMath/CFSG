module

import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.LocalAnalysis.GLTheoremB.BarXTools
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Tools

public section

namespace CFSG.LocalAnalysis.GLTheoremB

open CFSG.Open

@[expose] def Lemma911Type : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m p : ℕ), GLStanding G m p →
    ∀ B M : Subgroup G, IsBOneMax p B → IsPreUniquenessTwoLocal p B M → p = 3 →
      ∀ b ∈ B, b ≠ 1 → ∀ J : Subgroup G,
        IsTwoPrimeComp (alphaOf p M ⊓ Subgroup.centralizer ({b} : Set G)) J →
          (Nonempty ((↥J ⧸ CFSG.pCore 2 ↥J) ≃* ↥(alternatingGroup (Fin 7))) ∨
            IsHatSeven (↥J ⧸ CFSG.pCore 2 ↥J))

section Tools

theorem nonempty_quot_center_alt7_of_equiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : Nonempty (X ≃* ↥(alternatingGroup (Fin 7))) ∨ IsHatSeven X) :
    Nonempty ((Y ⧸ Subgroup.center Y) ≃* ↥(alternatingGroup (Fin 7))) := by
  rcases h with h | h
  · obtain ⟨e₁⟩ := h
    have e₂ : Y ≃* ↥(alternatingGroup (Fin 7)) := e.symm.trans e₁
    have hc : Subgroup.center Y = ⊥ := by
      have h1 := Subgroup.map_center_eq e₂
      rw [alternatingGroup.center_eq_bot
        (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)] at h1
      exact (Subgroup.map_eq_bot_iff_of_injective _ e₂.injective).1 h1
    exact ⟨((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).trans e₂⟩
  · exact (IsHatSeven.of_mulEquiv e h).2.2

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_pCore_two_iff {J : Subgroup G} (j : ↥J) :
    j ∈ CFSG.pCore 2 ↥J ↔ (j : G) ∈ pCoreOf 2 J := (CFSG.mem_openPCoreOf_iff j).symm

@[expose] noncomputable def quotEquivTwoImage {X J : Subgroup G} (hJX : J ≤ X)
    (hsn : IsSubnormal J X) :
    (↥J ⧸ CFSG.pCore 2 ↥J) ≃*
      ↥((J.subgroupOf X).map (QuotientGroup.mk' (CFSG.pCore 2 ↥X))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hker : CFSG.pCore 2 ↥J = (imageHom J X hJX).ker := by
    ext j
    rw [mem_ker_imageHom, mem_pCore_two_iff, ← inf_pCoreOf_eq_of_isSubnormal 2 hsn hJX,
      Subgroup.mem_inf]
    exact ⟨fun h => h.2, fun h => ⟨j.2, h⟩⟩
  exact (QuotientGroup.quotientMulEquivOfEq hker).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (imageHom_surjective J X hJX))

end Tools

end CFSG.LocalAnalysis.GLTheoremB
