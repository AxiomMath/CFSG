module

public import CFSG.CGT.PushingUpLit.A78.Cfg
public import CFSG.CGT.PushingUpLit.T2K.Sylow
public import CFSG.RankThree.PartOne.S12.Sec15Final

public section

namespace CFSG.CGT.PushingUpLit.A78

open CFSG CFSG.CGT.PushingUpLit CFSG.RankThree.PartOne

variable {G : Type} [Group G] [Finite G]

namespace A78Side

variable {L T J : Subgroup G} {e : ℕ}

theorem sup_le_normalizer (h : A78Side G L T J e) : L ⊔ T ≤ Subgroup.normalizer (L : Set G) :=
  sup_le Subgroup.le_normalizer h.sylow.le

theorem sylow_sup (h : A78Side G L T J e) : CFSG.ABGLocalTools.IsSylowOf 2 T (L ⊔ T) :=
  h.sylow.of_le le_sup_right h.sup_le_normalizer

theorem sup_le_normalizer_V (h : A78Side G L T J e) :
    L ⊔ T ≤ Subgroup.normalizer ((oTwoIn (L ⊔ T) : Subgroup G) : Set G) := by
  have _ := h
  exact (Subgroup.le_normalizer (H := L ⊔ T)).trans (normalizer_le_normalizer_oTwoIn (L ⊔ T))

theorem V_le_T (h : A78Side G L T J e) : oTwoIn (L ⊔ T) ≤ T :=
  T2K.NatBlock.oTwoIn_le_sylow le_rfl Subgroup.le_normalizer h.sylow_sup

theorem V_ne_bot (h : A78Side G L T J e) : oTwoIn (L ⊔ T) ≠ ⊥ := by
  intro hV
  obtain ⟨_, ψ, _, _, hψs, _, _⟩ := h.nat
  obtain ⟨⟨x, hx⟩, hw⟩ := hψs (Multiplicative.ofAdd (Pi.single 0 (1 : GaloisField 2 e) :
    Fin 2 → GaloisField 2 e))
  have hx' := hx
  rw [hV] at hx'
  have hx1 : x = 1 := Subgroup.mem_bot.mp hx'
  have hw2 : (⟨x, hx⟩ : ↥(oTwoIn (L ⊔ T))) = 1 := Subtype.ext hx1
  rw [hw2, map_one] at hw
  have h0 := congrFun (Multiplicative.ofAdd.injective hw) 0
  simp at h0

theorem normalizer_V_le (h : A78Side G L T J e) :
    Subgroup.normalizer ((oTwoIn (L ⊔ T) : Subgroup G) : Set G) ≤
      Subgroup.normalizer (L : Set G) := by
  refine Sec15Final.normalizer_le_of_forall_maximal (X := L ⊔ T) h.V_ne_bot
    (isPGroup_oTwoIn _) h.sup_le_normalizer_V ?_
  intro M hM
  rw [h.unique] at hM
  exact (Set.mem_singleton_iff.mp hM).le

theorem sylow_normalizer_V (h : A78Side G L T J e) :
    CFSG.ABGLocalTools.IsSylowOf 2 T
      (Subgroup.normalizer ((oTwoIn (L ⊔ T) : Subgroup G) : Set G)) :=
  h.sylow.of_le (le_sup_right.trans h.sup_le_normalizer_V) h.normalizer_V_le

end A78Side

namespace A78Cfg

variable {L₁ L₂ T : Subgroup G} {e : ℕ}

theorem J_le_T (h : A78Cfg G L₁ L₂ T e) : oTwoIn (L₁ ⊔ T) ⊔ oTwoIn (L₂ ⊔ T) ≤ T :=
  sup_le h.side₁.V_le_T h.side₂.V_le_T

theorem oTwoIn_sup_eq_bot (h : A78Cfg G L₁ L₂ T e) : oTwoIn (L₁ ⊔ L₂ ⊔ T) = ⊥ := by
  by_contra hP
  have hX : L₁ ⊔ L₂ ⊔ T ≤ Subgroup.normalizer ((oTwoIn (L₁ ⊔ L₂ ⊔ T) : Subgroup G) : Set G) :=
    (Subgroup.le_normalizer (H := L₁ ⊔ L₂ ⊔ T)).trans
      (normalizer_le_normalizer_oTwoIn (L₁ ⊔ L₂ ⊔ T))
  obtain ⟨M, hle, hmax⟩ := Sec15Final.exists_isMaximalTwoLocal_ge
    (L := Subgroup.normalizer ((oTwoIn (L₁ ⊔ L₂ ⊔ T) : Subgroup G) : Set G))
    ⟨oTwoIn (L₁ ⊔ L₂ ⊔ T), hP, isPGroup_oTwoIn _, rfl⟩
  have hX₁ : L₁ ⊔ T ≤ L₁ ⊔ L₂ ⊔ T := sup_le (le_sup_left.trans le_sup_left) le_sup_right
  have hX₂ : L₂ ⊔ T ≤ L₁ ⊔ L₂ ⊔ T := sup_le (le_sup_right.trans le_sup_left) le_sup_right
  have h1 : M ∈ maximalTwoLocalsContaining ((L₁ ⊔ T : Subgroup G) : Set G) :=
    ⟨hmax, fun x hx => hle (hX (hX₁ hx))⟩
  have h2 : M ∈ maximalTwoLocalsContaining ((L₂ ⊔ T : Subgroup G) : Set G) :=
    ⟨hmax, fun x hx => hle (hX (hX₂ hx))⟩
  rw [h.side₁.unique] at h1
  rw [h.side₂.unique] at h2
  exact h.ne_norm ((Set.mem_singleton_iff.mp h1).symm.trans (Set.mem_singleton_iff.mp h2))

end A78Cfg

structure A78Hyg (G : Type) [Group G] [Finite G] (L₁ L₂ T : Subgroup G) (e : ℕ) : Prop where
  V₁_le : oTwoIn (L₁ ⊔ T) ≤ T
  V₂_le : oTwoIn (L₂ ⊔ T) ≤ T
  J_le : oTwoIn (L₁ ⊔ T) ⊔ oTwoIn (L₂ ⊔ T) ≤ T
  V₁_ne : oTwoIn (L₁ ⊔ T) ≠ ⊥
  V₂_ne : oTwoIn (L₂ ⊔ T) ≠ ⊥
  sup₁ : L₁ ⊔ T ≤ Subgroup.normalizer ((oTwoIn (L₁ ⊔ T) : Subgroup G) : Set G)
  sup₂ : L₂ ⊔ T ≤ Subgroup.normalizer ((oTwoIn (L₂ ⊔ T) : Subgroup G) : Set G)
  sylow₁ : CFSG.ABGLocalTools.IsSylowOf 2 T
    (Subgroup.normalizer ((oTwoIn (L₁ ⊔ T) : Subgroup G) : Set G))
  sylow₂ : CFSG.ABGLocalTools.IsSylowOf 2 T
    (Subgroup.normalizer ((oTwoIn (L₂ ⊔ T) : Subgroup G) : Set G))
  nl₁ : Subgroup.normalizer ((oTwoIn (L₁ ⊔ T) : Subgroup G) : Set G) ≤
    Subgroup.normalizer (L₁ : Set G)
  nl₂ : Subgroup.normalizer ((oTwoIn (L₂ ⊔ T) : Subgroup G) : Set G) ≤
    Subgroup.normalizer (L₂ : Set G)
  O2_top : oTwoIn (L₁ ⊔ L₂ ⊔ T) = ⊥

theorem A78Cfg.hyg {L₁ L₂ T : Subgroup G} {e : ℕ} (h : A78Cfg G L₁ L₂ T e) :
    A78Hyg G L₁ L₂ T e where
  V₁_le := h.side₁.V_le_T
  V₂_le := h.side₂.V_le_T
  J_le := h.J_le_T
  V₁_ne := h.side₁.V_ne_bot
  V₂_ne := h.side₂.V_ne_bot
  sup₁ := h.side₁.sup_le_normalizer_V
  sup₂ := h.side₂.sup_le_normalizer_V
  sylow₁ := h.side₁.sylow_normalizer_V
  sylow₂ := h.side₂.sylow_normalizer_V
  nl₁ := h.side₁.normalizer_V_le
  nl₂ := h.side₂.normalizer_V_le
  O2_top := h.oTwoIn_sup_eq_bot

end CFSG.CGT.PushingUpLit.A78
