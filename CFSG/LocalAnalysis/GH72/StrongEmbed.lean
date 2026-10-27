module

public import CFSG.LocalAnalysis.GH72.Vocabulary
import CFSG.Monster.B.Recog.GenericStrongEmbedding
public import CFSG.LocalAnalysis.ComponentClassification.Sol78NoStrongEmb

public section

namespace CFSG.GH72

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem stronglyEmbedded_of_centralizers (K : Subgroup G) (hK : K ≠ ⊤) (S : Sylow 2 G)
    (hSK : (S : Subgroup G) ≤ K) (hN : normalizer ((S : Subgroup G) : Set G) ≤ K)
    (hC : ∀ t ∈ K, orderOf t = 2 → C t ≤ K) : CFSG.IsStronglyEmbedded K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have heven : Even (Nat.card K) := by
    by_cases h2G : 2 ∣ Nat.card G
    · have h2S : 2 ∣ Nat.card (S : Subgroup G) := by
        rcases S.isPGroup'.card_eq_or_dvd with h | h
        · exact absurd (Subgroup.card_eq_one.1 h) (S.ne_bot_of_dvd_card h2G)
        · exact h
      exact even_iff_two_dvd.2 (h2S.trans (Subgroup.card_dvd_of_le hSK))
    · exfalso
      have hS : (S : Subgroup G) = ⊥ := by
        rcases S.isPGroup'.card_eq_or_dvd with h | h
        · exact Subgroup.card_eq_one.1 h
        · exact absurd (h.trans (Subgroup.card_subgroup_dvd_card _)) h2G
      apply hK
      rw [eq_top_iff]
      refine le_trans ?_ hN
      rw [hS]
      intro g _
      rw [mem_normalizer_iff]
      intro x
      simp only [SetLike.mem_coe, mem_bot]
      constructor
      · rintro rfl
        group
      · intro hx
        calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
          _ = 1 := by rw [hx]; group
  have h := CFSG.Monster.B.Recog.isStronglyEmbeddedOrder_of_centralizer_le hK heven hC S hN
  refine ⟨h.1, h.2.1, fun g hg => ?_⟩
  have := h.2.2 g⁻¹ (fun hginv => hg (K.inv_mem_iff.mp hginv))
  simpa only [CFSG.conjugate, inv_inv] using this

theorem not_stronglyEmbedded_of_productFusion {S S₁ S₂ : Subgroup G} (hd : DDDecomp S S₁ S₂)
    (hpf : HasProductFusion S₁ S₂) (K : Subgroup G) : ¬ CFSG.IsStronglyEmbedded K := by
  intro hK
  obtain ⟨a, -, ⟨e₁⟩⟩ := hd.dih₁
  obtain ⟨b, -, ⟨e₂⟩⟩ := hd.dih₂
  set x : G := ((e₁.symm (DihedralGroup.sr 0) : S₁) : G) with hxdef
  set y : G := ((e₂.symm (DihedralGroup.sr 0) : S₂) : G) with hydef
  have hx : orderOf x = 2 := by
    rw [hxdef, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, DihedralGroup.orderOf_sr]
  have hy : orderOf y = 2 := by
    rw [hydef, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, DihedralGroup.orderOf_sr]
  have hx₁ : x ∈ S₁ := (e₁.symm (DihedralGroup.sr 0)).2
  have hy₂ : y ∈ S₂ := (e₂.symm (DihedralGroup.sr 0)).2
  have hxy : IsConj x y :=
    CFSG.ComponentClassification.Sol78.isConj_of_isStronglyEmbedded hK hx hy
  have hy₁ : y ∈ S₁ := (hpf.separate x (le_sup_left (a := S₁) hx₁) y
    (le_sup_right (b := S₂) hy₂) hx hxy).1.mp hx₁
  have hy1 : y = 1 := by
    have : y ∈ S₁ ⊓ S₂ := ⟨hy₁, hy₂⟩
    rwa [hd.inf_eq, mem_bot] at this
  rw [hy1, orderOf_one] at hy
  exact absurd hy (by norm_num)

end CFSG.GH72
