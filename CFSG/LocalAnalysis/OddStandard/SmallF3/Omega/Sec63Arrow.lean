module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63ArrowAux
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63TwoGroup
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63Quot
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Suzuki
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Orders
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Facts3

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint
open scoped commutatorElement

variable {G : Type} [Group G]

theorem sec63_caseA [Finite G] {T H : Subgroup G} {x y : G}
    (hT : IsPGroup 2 T) (hy : orderOf y = 2) (hyT : y ∈ T) (hyH : y ∈ H) (hxT : x ∈ T)
    (hxy : x * y = y * x) (hxH : x ∉ H)
    (hU : IsCyclic ↥(T ⊓ centralizer ({y} : Set G) ⊓ H))
    (hrel : H.relIndex (T ⊓ centralizer ({y} : Set G)) ≤ 2) :
    CFSG.Open.pRank 2 T ≤ 2 := by
  have hRT : T ⊓ centralizer ({y} : Set G) ≤ T := inf_le_left
  have hU2 : IsPGroup 2 ↥(T ⊓ centralizer ({y} : Set G) ⊓ H) := hT.to_le (inf_le_left.trans hRT)
  have hyR : y ∈ T ⊓ centralizer ({y} : Set G) :=
    ⟨hyT, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hyU : y ∈ T ⊓ centralizer ({y} : Set G) ⊓ H := ⟨hyR, hyH⟩
  by_cases hc : Nat.card ↥(T ⊓ centralizer ({y} : Set G) ⊓ H) = 2
  · have hxR : x ∈ T ⊓ centralizer ({y} : Set G) :=
      ⟨hxT, Subgroup.mem_centralizer_singleton_iff.mpr hxy⟩
    exact sec6_suzuki_four hT hyT hy (sec63_card_four hrel hc hxR hxH)
  · have h4 := sec63_card_ge_four hU2 hy hyU hc
    exact (sec63_rank_of_power hT hRT
      (fun r hr hcomm => ⟨hr, Subgroup.mem_centralizer_singleton_iff.mpr hcomm⟩) hy hU
      inf_le_left hyU (Or.inl rfl) (sec63_pow_two_mem hrel) (by omega)
      (sec63_elem_le_of_relIndex hU hrel)).2

theorem sec63_not_om6m [Finite G] {Y : Subgroup G} (hq : IsQuasisimple ↥Y)
    (h : IsOmega6Plus Y ∨ IsOmega5 Y ∨ IsL281 Y) (hm : IsOmega6Minus Y) : False := by
  have h3 := ctrQ_of_u43 hq hm
  rcases h with h | h | h
  · rw [ctrQ_of_l43 hq h] at h3
    omega
  · rw [ctrQ_of_psp4 hq h] at h3
    omega
  · rw [ctrQ_of_l281 hq h] at h3
    omega

theorem sec63_arrow_cases [Finite G] (hF : Asc82AutFacts) (hHyp : Asc82Hyp62 G) {x y : G}
    {X Y R : Subgroup G} (hx : orderOf x = 2) (hy : orderOf y = 2)
    (hxN : x ∈ normalizer (Y : Set G)) (hXc : IsComponentIn X (centralizer ({x} : Set G)))
    (hYc : IsComponentIn Y (centralizer ({y} : Set G))) (hXY : X ≤ Y) (hXF : InFStar X)
    (hYs : IsOmega6Plus Y ∨ IsOmega5 Y ∨ IsL281 Y) (hR : IsPGroup 2 ↥R)
    (hRN : R ≤ normalizer (Y : Set G) ⊓ centralizer (X : Set G)) :
    (centralizer (Y : Set G)).relIndex R ≤ 2 ∨
      (IsL29 X ∧ IsOmega6Plus Y ∧
        QuotEquivTo R (R ⊓ centralizer (Y : Set G)) (Multiplicative (ZMod 4))) := by
  have hYq : IsQuasisimple ↥Y := hYc.isQuasisimple
  have hshape : IsOm6P Y ∨ IsOm6M Y ∨ IsOm5Q Y ∨ (IsQuasisimple Y ∧ IsL281 Y) := by
    rcases hYs with h | h | h
    · exact Or.inl ⟨hYq, h⟩
    · exact Or.inr (Or.inr (Or.inl ⟨hYq, h⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hYq, h⟩))
  have hXin : IsComponentIn X (Y ⊓ centralizer ({x} : Set G)) :=
    hXc.mono (le_inf hXY hXc.le) inf_le_right
  have hH : IsOm6P Y → Hyp62At Y := fun hP => hHyp Y ⟨y, hy, hYc⟩ hP.2
  rcases hF.aut_cent G Y x X hshape hx hxN hXin hXF hH R hR hRN with h | h | h | h
  · exact Or.inl h
  · exact (sec63_not_om6m hYq hYs h.2.1.2).elim
  · exact (sec63_not_om6m hYq hYs h.2.1.2).elim
  · exact Or.inr ⟨h.1, h.2.1.2, h.2.2⟩

end CFSG.OddStandard.SmallF3.Omega
