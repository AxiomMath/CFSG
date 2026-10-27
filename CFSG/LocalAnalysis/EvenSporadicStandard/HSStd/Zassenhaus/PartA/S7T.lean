module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S7Data2
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S7Kernel

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

set_option linter.unusedSectionVars false

open Subgroup

section Basic

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G} {E W : Subgroup G} {z : G}

@[expose] def PA5.s7_F (a : PA5 L t E z) : Subgroup ↥a.s7_N₁ := a.F₀.subgroupOf a.s7_N₁

theorem PA5.s7_mem_F (a : PA5 L t E z) (x : ↥a.s7_N₁) : x ∈ a.s7_F ↔ (x : G) ∈ a.F₀ := Iff.rfl

instance PA5.s7_F_normal (a : PA5 L t E z) : a.s7_F.Normal :=
  ⟨fun n hn g => by
    rw [PA5.s7_mem_F] at hn ⊢
    exact ((a.s7_mem_N₁).1 g.2).1 n |>.1 hn⟩

@[expose] def PA5.s7_κ (a : PA5 L t E z) :
    ↥a.s7_N₁ →* (↥a.s7_N₁ ⧸ a.s7_F) ⧸ Open.fusionOddCore (↥a.s7_N₁ ⧸ a.s7_F) :=
  xhatMap a.s7_F

@[expose] def PA5.s7_tT (hb : PAB G L t E W z) (a : PA5 L t E z) : ↥a.s7_N₁ :=
  ⟨t, a.s7_t_mem_N₁ hb⟩

@[expose] def PA5.s7_ubT (hb : PAB G L t E W z) (a : PA5 L t E z) : ↥a.s7_N₁ :=
  ⟨a.ub, a.s7_F₀_le_N₁ hb (a.s7_ub_mem_F₀ hb)⟩

@[expose] def PA5.s7_yT (hb : PAB G L t E W z) (a : PA5 L t E z) : ↥a.s7_N₁ :=
  ⟨a.y, a.s7_J_le_N₁ hb a.y_J⟩

theorem PA5.s7_F_pgroup (hb : PAB G L t E W z) (a : PA5 L t E z) : IsPGroup 2 ↥a.s7_F :=
  IsPGroup.of_injective (a.s7_F₀_isPGroup hb)
    (subgroupOfEquivOfLe (a.s7_F₀_le_N₁ hb)).toMonoidHom
    (subgroupOfEquivOfLe (a.s7_F₀_le_N₁ hb)).injective

theorem PA5.s7_F_card_le (hb : PAB G L t E W z) (a : PA5 L t E z) : Nat.card ↥a.s7_F ≤ 4 := by
  have : Nat.card ↥a.s7_F = Nat.card ↥a.F₀ :=
    Nat.card_congr (subgroupOfEquivOfLe (a.s7_F₀_le_N₁ hb)).toEquiv
  rw [this]
  exact a.s7_card_F₀_le hb

theorem PA5.s7_F_comm_core (hb : PAB G L t E W z) (a : PA5 L t E z) :
    ∀ f ∈ a.s7_F, ∀ x ∈ Open.fusionOddCore ↥a.s7_N₁, f * x = x * f :=
  oddCore_comm_of_pGroup a.s7_F (a.s7_F_pgroup hb)

theorem PA5.s7_F_disj_core (hb : PAB G L t E W z) (a : PA5 L t E z) :
    ∀ f ∈ a.s7_F, f ∈ Open.fusionOddCore ↥a.s7_N₁ → f = 1 :=
  oddCore_disjoint_of_pGroup a.s7_F (a.s7_F_pgroup hb)

theorem PA5.s7_ker_le (hb : PAB G L t E W z) (a : PA5 L t E z) :
    (xhatMap a.s7_F).ker ≤ a.s7_F ⊔ Open.fusionOddCore ↥a.s7_N₁ := by
  refine ker_xhatMap_le_sup a.s7_F (a.s7_F_pgroup hb) ?_
  intro g hg f hf
  have hg' : Odd (orderOf (g : G)) := by rwa [Subgroup.orderOf_coe]
  exact Subtype.ext (a.s7_odd_cent_F₀ hb g.2 hg' f.1 hf)

end Basic

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
