module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InS2F2

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ} {t : G}
  {M₀ : Subgroup G} {x₀ : G} {q : ℕ} {W : Subgroup G}

namespace S2Ok

variable {D₁ D₂ : Subgroup G} (O : S2Ok T M H S L D n t M₀ x₀ q W D₁ D₂)
include O

theorem R_decomp' {r : G} (hr : r ∈ thompsonJ S) :
    ∃ r₁ ∈ thompsonJ S ⊓ L, ∃ r₂ ∈ thompsonJ S ⊓ conjR L t, r = r₁ * r₂ := by
  obtain ⟨r₁, h₁, r₂, h₂, c, hc, rfl⟩ := O.base.R_decomp r hr
  rw [O.hC, Subgroup.mem_bot] at hc
  exact ⟨r₁, h₁, r₂, h₂, by rw [hc, mul_one]⟩

theorem R_perm_S {g : G} (hg : g ∈ S) :
    (conjR (thompsonJ S ⊓ L) g = thompsonJ S ⊓ L ∧
        conjR (thompsonJ S ⊓ conjR L t) g = thompsonJ S ⊓ conjR L t) ∨
      (conjR (thompsonJ S ⊓ L) g = thompsonJ S ⊓ conjR L t ∧
        conjR (thompsonJ S ⊓ conjR L t) g = thompsonJ S ⊓ L) := by
  have hR : conjR (thompsonJ S) g = thompsonJ S := thompsonJ_normalized (Subgroup.le_normalizer hg)
  rcases O.base.dbl.conjR_L₂_cases hg with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    exact ⟨by rw [conjR_inf, hR, h1], by rw [conjR_inf, hR, h2]⟩
  · right
    exact ⟨by rw [conjR_inf, hR, h1], by rw [conjR_inf, hR, h2]⟩

theorem R_perm_M₀ {a : G} (ha : a ∈ M₀) :
    (conjR (thompsonJ S ⊓ L) a = thompsonJ S ⊓ L ∧
        conjR (thompsonJ S ⊓ conjR L t) a = thompsonJ S ⊓ conjR L t) ∨
      (conjR (thompsonJ S ⊓ L) a = thompsonJ S ⊓ conjR L t ∧
        conjR (thompsonJ S ⊓ conjR L t) a = thompsonJ S ⊓ L) := by
  have hB := O.base
  rcases CFSG.QuasithinUnique.mem_or_inv_mul_mem_of_relIndex_two hB.h2 hB.hx₀ hB.hx₀S ha with h | h
  · exact O.R_perm_S h
  · have key : ∀ X : Subgroup G, conjR X a = conjR (conjR X x₀) (x₀⁻¹ * a) := fun X => by
      rw [conjR_conjR, mul_inv_cancel_left]
    rcases O.R_perm_S h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      exact ⟨by rw [key, O.conjR_R₁, h1], by rw [key, O.conjR_R₂, h2]⟩
    · right
      exact ⟨by rw [key, O.conjR_R₁, h1], by rw [key, O.conjR_R₂, h2]⟩

theorem conjR_Q_eq {a : G} (ha : a ∈ M₀) (haS : a ∉ S) :
    conjR (pCoreOf 2 H) a = conjR (pCoreOf 2 H) x₀ := by
  have hB := O.base
  have hs : x₀⁻¹ * a ∈ S :=
    CFSG.QuasithinUnique.inv_mul_mem_of_relIndex_two hB.h2 hB.hx₀ hB.hx₀S ha haS
  have hQN : S ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    hB.S_le_H.trans (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H)
  have key : conjR (pCoreOf 2 H) a = conjR (conjR (pCoreOf 2 H) x₀) (x₀⁻¹ * a) := by
    rw [conjR_conjR, mul_inv_cancel_left]
  rw [key]
  have hxs : x₀ * (x₀⁻¹ * a) * x₀⁻¹ ∈ S :=
    (Subgroup.mem_normalizer_iff.1 hB.su.hxN (x₀⁻¹ * a)).1 hs
  refine conjR_eq_self_iff.2 ?_
  rw [conjR_normalizer, mem_conjR]
  exact hQN hxs

theorem pCore_inf_L : pCoreOf 2 H ⊓ L = blockU L := by
  have hB := O.base
  rw [hB.pCore_eq_UU O.hC]
  exact sup_inf_left_of_commute hB.comm_elem hB.L_inf_L₂ (blockU_le L)
    (conjR_mono (blockU_le L) t)

theorem pCore_inf_L₂ : pCoreOf 2 H ⊓ conjR L t = conjR (blockU L) t := by
  have hB := O.base
  rw [hB.pCore_eq_UU O.hC]
  exact sup_inf_right_of_commute hB.comm_elem hB.L_inf_L₂ (blockU_le L)
    (conjR_mono (blockU_le L) t)

theorem blockU₁_eq : blockU L = pCoreOf 2 H ⊓ (thompsonJ S ⊓ L) := by
  have hB := O.base
  apply le_antisymm
  · exact le_inf (by rw [← O.pCore_inf_L]; exact inf_le_left)
      (le_inf hB.U₁_le_R (blockU_le L))
  · rintro x ⟨hxQ, hxR, hxL⟩
    rw [← O.pCore_inf_L]
    exact ⟨hxQ, hxL⟩

theorem blockU₂_eq : conjR (blockU L) t = pCoreOf 2 H ⊓ (thompsonJ S ⊓ conjR L t) := by
  have hB := O.base
  apply le_antisymm
  · refine le_inf (by rw [← O.pCore_inf_L₂]; exact inf_le_left)
      (le_inf ?_ (conjR_mono (blockU_le L) t))
    rw [← DoubleA3.blockU_conjR]
    exact hB.U₂_le_R
  · rintro x ⟨hxQ, hxR, hxL⟩
    rw [← O.pCore_inf_L₂]
    exact ⟨hxQ, hxL⟩

theorem conjR_U₁_of_nonswap {a : G} (ha : a ∈ M₀) (haS : a ∉ S)
    (hR₁ : conjR (thompsonJ S ⊓ L) a = thompsonJ S ⊓ L) :
    conjR (blockU L) a = conjR (blockU L) x₀ := by
  have e1 := O.blockU₁_eq
  calc conjR (blockU L) a = conjR (pCoreOf 2 H ⊓ (thompsonJ S ⊓ L)) a := by rw [← e1]
    _ = conjR (pCoreOf 2 H) a ⊓ conjR (thompsonJ S ⊓ L) a := conjR_inf _ _ _
    _ = conjR (pCoreOf 2 H) x₀ ⊓ conjR (thompsonJ S ⊓ L) x₀ := by
        rw [O.conjR_Q_eq ha haS, hR₁, O.conjR_R₁]
    _ = conjR (pCoreOf 2 H ⊓ (thompsonJ S ⊓ L)) x₀ := (conjR_inf _ _ _).symm
    _ = conjR (blockU L) x₀ := by rw [← e1]

theorem conjR_U₂_of_nonswap {a : G} (ha : a ∈ M₀) (haS : a ∉ S)
    (hR₂ : conjR (thompsonJ S ⊓ conjR L t) a = thompsonJ S ⊓ conjR L t) :
    conjR (conjR (blockU L) t) a = conjR (conjR (blockU L) t) x₀ := by
  have e1 := O.blockU₂_eq
  calc conjR (conjR (blockU L) t) a
      = conjR (pCoreOf 2 H ⊓ (thompsonJ S ⊓ conjR L t)) a := by rw [← e1]
    _ = conjR (pCoreOf 2 H) a ⊓ conjR (thompsonJ S ⊓ conjR L t) a := conjR_inf _ _ _
    _ = conjR (pCoreOf 2 H) x₀ ⊓ conjR (thompsonJ S ⊓ conjR L t) x₀ := by
        rw [O.conjR_Q_eq ha haS, hR₂, O.conjR_R₂]
    _ = conjR (pCoreOf 2 H ⊓ (thompsonJ S ⊓ conjR L t)) x₀ := (conjR_inf _ _ _).symm
    _ = conjR (conjR (blockU L) t) x₀ := by rw [← e1]

end S2Ok

end CFSG.QuasithinUnique.Lin2
