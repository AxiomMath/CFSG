module

public import CFSG.CGT.PushingUpLit.BlocksCommuteCore

public section

namespace CFSG.CGT.PushingUpLit

open CFSG CFSG.RankThree.PartOne
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def barImg (X : Subgroup G) : Subgroup (G ⧸ pCore 2 G) :=
  X.map (QuotientGroup.mk' (pCore 2 G))

@[expose] noncomputable def barHom (X : Subgroup G) : ↥X →* G ⧸ pCore 2 G :=
  (QuotientGroup.mk' (pCore 2 G)).comp X.subtype

omit [Finite G] in
theorem range_barHom (X : Subgroup G) : (barHom X).range = barImg X := by
  unfold barHom barImg
  rw [MonoidHom.range_comp, Subgroup.range_subtype]

theorem ker_barHom {X : Subgroup G} (hX : IsBlockOf X) : (barHom X).ker = pCore 2 ↥X := by
  ext x
  rw [MonoidHom.mem_ker]
  have h1 : barHom X x = 1 ↔ (x : G) ∈ pCore 2 G := QuotientGroup.eq_one_iff _
  rw [h1]
  constructor
  · intro h
    have : (x : G) ∈ oTwoIn X := by
      rw [oTwoIn_eq_inf_pCore hX.1]
      exact ⟨x.2, h⟩
    obtain ⟨y, hy, hyx⟩ := this
    have : y = x := Subtype.ext hyx
    rwa [← this]
  · intro h
    exact oTwoIn_le_pCore hX.1 ⟨x, h, rfl⟩

noncomputable def barEquiv {X : Subgroup G} (hX : IsBlockOf X) :
    (↥X ⧸ pCore 2 ↥X) ≃* ↥(barImg X) :=
  ((QuotientGroup.quotientMulEquivOfEq (ker_barHom hX).symm).trans
    (QuotientGroup.quotientKerEquivRange (barHom X))).trans
      (MulEquiv.subgroupCongr (range_barHom X))

omit [Finite G] in
theorem barImg_subnormal {X : Subgroup G} (hX : X.IsSubnormal) : (barImg X).IsSubnormal :=
  hX.map (QuotientGroup.mk'_surjective _)

theorem card_barImg {X : Subgroup G} (hX : IsBlockOf X) :
    Nat.card ↥(barImg X) = Nat.card (↥X ⧸ pCore 2 ↥X) :=
  (Nat.card_congr (barEquiv hX).toEquiv).symm

theorem isComponent_barImg {X : Subgroup G} (hX : IsBlockOf X)
    (hq : IsQuasisimple (↥X ⧸ pCore 2 ↥X)) : IsComponent (barImg X) :=
  ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (barEquiv hX) hq, barImg_subnormal hX.1⟩

omit [Finite G] in
theorem le_sup_pCore_of_barImg_le {X Y : Subgroup G} (h : barImg X ≤ barImg Y) :
    X ≤ Y ⊔ pCore 2 G := by
  intro b hb
  obtain ⟨y, hy, hyb⟩ := h (Subgroup.mem_map_of_mem (QuotientGroup.mk' (pCore 2 G)) hb)
  have hq : y⁻¹ * b ∈ pCore 2 G := QuotientGroup.eq.1 hyb
  have : b = y * (y⁻¹ * b) := by group
  rw [this]
  exact Subgroup.mul_mem_sup hy hq

omit [Finite G] in
theorem commutator_mem_pCore_of_barImg {X Y : Subgroup G}
    (h : ⁅barImg X, barImg Y⁆ = ⊥) : ∀ x ∈ X, ∀ y ∈ Y, ⁅x, y⁆ ∈ pCore 2 G := by
  intro x hx y hy
  unfold barImg at h
  have hc := Subgroup.commutator_mem_commutator
    (Subgroup.mem_map_of_mem (QuotientGroup.mk' (pCore 2 G)) hx)
    (Subgroup.mem_map_of_mem (QuotientGroup.mk' (pCore 2 G)) hy)
  rw [h, Subgroup.mem_bot, ← map_commutatorElement] at hc
  exact (QuotientGroup.eq_one_iff _).1 hc

theorem false_of_le_of_commutator_eq_bot {Γ : Type} [Group Γ] {K U : Subgroup Γ}
    (hK : IsQuasisimple ↥K) (hKU : K ≤ U) (h : ⁅K, U⁆ = ⊥) : False := by
  have h1 : ⁅K, K⁆ = ⊥ := le_bot_iff.mp (h ▸ Subgroup.commutator_mono le_rfl hKU)
  have h2 : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.mp hK.1
  have h3 : K = ⊥ := h2.symm.trans h1
  have : Nontrivial ↥K := CFSG.LocalCores.isQuasisimple_nontrivial hK
  exact (Subgroup.nontrivial_iff_ne_bot K).mp this h3

end CFSG.CGT.PushingUpLit
