module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotNonsplit
public import CFSG.RankThree.PartOne.KF.LayerGen

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint.Chevalley

theorem mul_mul_inv_mul_inv_eq_of_commute {G : Type*} [Group G] {y₁ y₂ d₁ d₂ : G}
    (hy : Commute y₁ y₂) (h₁₁ : Commute y₁ d₁) (h₁₂ : Commute y₁ d₂) (h₂₁ : Commute y₂ d₁)
    (h₂₂ : Commute y₂ d₂) :
    y₁ * d₁ * (y₂ * d₂) * (y₁ * d₁)⁻¹ * (y₂ * d₂)⁻¹ = d₁ * d₂ * d₁⁻¹ * d₂⁻¹ := by
  have e1 : y₁ * d₁ * (y₂ * d₂) = y₁ * y₂ * (d₁ * d₂) := h₂₁.symm.mul_mul_mul_comm y₁ d₂
  have e2 : y₂ * d₂ * (y₁ * d₁) = y₂ * y₁ * (d₂ * d₁) := h₁₂.symm.mul_mul_mul_comm y₂ d₁
  have hY : Commute (y₁ * y₂) (d₁ * d₂ * (d₂ * d₁)⁻¹) := by
    have h1 : Commute (y₁ * y₂) d₁ := h₁₁.mul_left h₂₁
    have h2 : Commute (y₁ * y₂) d₂ := h₁₂.mul_left h₂₂
    exact (h1.mul_right h2).mul_right (h2.mul_right h1).inv_right
  calc y₁ * d₁ * (y₂ * d₂) * (y₁ * d₁)⁻¹ * (y₂ * d₂)⁻¹
      = (y₁ * d₁ * (y₂ * d₂)) * (y₂ * d₂ * (y₁ * d₁))⁻¹ := by group
    _ = (y₁ * y₂) * (d₁ * d₂ * (d₂ * d₁)⁻¹) * (y₁ * y₂)⁻¹ := by
        rw [e1, e2, ← hy.eq]
        group
    _ = d₁ * d₂ * (d₂ * d₁)⁻¹ := by rw [hY.eq, mul_inv_cancel_right]
    _ = d₁ * d₂ * d₁⁻¹ * d₂⁻¹ := by group


variable {K : Type} [Field K] [Finite K] [CharP K 2] {X : Subgroup (adjointGroup .F4 K)}

theorem mul_mul_inv_mem_C3Levi_of_mem_centralizer_nonsplit
    (hXJ : X ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K)) (hcyc : IsCyclic X)
    (hX : Nat.card X = Nat.card K + 1) {c d : adjointGroup .F4 K}
    (hc : c ∈ centralizer (X : Set (adjointGroup .F4 K))) (hd : d ∈ C3Levi K) :
    c * d * c⁻¹ ∈ C3Levi K := by
  obtain ⟨y, hy, d', hd', rfl⟩ := exists_mul_of_mem_centralizer_nonsplit hXJ hcyc hX hc
  have hw : d' * d * d'⁻¹ ∈ C3Levi K := mul_mem (mul_mem hd' hd) (inv_mem hd')
  have hyw := commute_of_mem_highestRootRankOne_of_mem_C3Levi (hXJ hy) hw
  have e : y * d' * d * (y * d')⁻¹ = d' * d * d'⁻¹ := by
    calc y * d' * d * (y * d')⁻¹ = y * (d' * d * d'⁻¹) * y⁻¹ := by group
      _ = d' * d * d'⁻¹ := by rw [hyw, mul_inv_cancel_right]
  rw [e]
  exact hw

theorem commutator_mem_C3Levi_of_mem_centralizer_nonsplit
    (hXJ : X ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K)) (hcyc : IsCyclic X)
    (hX : Nat.card X = Nat.card K + 1) {c₁ c₂ : adjointGroup .F4 K}
    (hc₁ : c₁ ∈ centralizer (X : Set (adjointGroup .F4 K)))
    (hc₂ : c₂ ∈ centralizer (X : Set (adjointGroup .F4 K))) :
    c₁ * c₂ * c₁⁻¹ * c₂⁻¹ ∈ C3Levi K := by
  obtain ⟨y₁, hy₁, d₁, hd₁, rfl⟩ := exists_mul_of_mem_centralizer_nonsplit hXJ hcyc hX hc₁
  obtain ⟨y₂, hy₂, d₂, hd₂, rfl⟩ := exists_mul_of_mem_centralizer_nonsplit hXJ hcyc hX hc₂
  have hXX : X ≤ centralizer (X : Set (adjointGroup .F4 K)) := by
    rw [(centralizer_nonsplit hXJ hcyc hX).1]
    exact le_sup_left
  have hy : Commute y₁ y₂ := (Subgroup.mem_centralizer_iff.1 (hXX hy₂) y₁ hy₁)
  have hc : ∀ {y d : adjointGroup .F4 K}, y ∈ X → d ∈ C3Levi K → Commute y d := fun hy hd =>
    commute_of_mem_highestRootRankOne_of_mem_C3Levi (hXJ hy) hd
  rw [mul_mul_inv_mul_inv_eq_of_commute hy (hc hy₁ hd₁) (hc hy₁ hd₂) (hc hy₂ hd₁) (hc hy₂ hd₂)]
  exact mul_mem (mul_mem (mul_mem hd₁ hd₂) (inv_mem hd₁)) (inv_mem hd₂)

theorem inSubgroup_layer_inf_centralizer_nonsplit {G : Type} [Group G] {L : Subgroup G}
    (e : L ≃* adjointGroup .F4 K)
    (hXJ : X ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K)) (hcyc : IsCyclic X)
    (hX : Nat.card X = Nat.card K + 1) :
    inSubgroup layer
        (L ⊓ centralizer (((X.map e.symm.toMonoidHom).map L.subtype : Subgroup G) : Set G)) =
      ((C3Levi K).map e.symm.toMonoidHom).map L.subtype := by
  set XG : Subgroup G := (X.map e.symm.toMonoidHom).map L.subtype
  set DG : Subgroup G := ((C3Levi K).map e.symm.toMonoidHom).map L.subtype
  set H : Subgroup G := L ⊓ centralizer (XG : Set G) with hH
  have hHL : H ≤ L := inf_le_left
  set ψ : H →* adjointGroup .F4 K := e.toMonoidHom.comp (Subgroup.inclusion hHL)
  have hψ_apply : ∀ h : H, ψ h = e (Subgroup.inclusion hHL h) := fun h => rfl
  have hmemH : ∀ h : L, (h : G) ∈ H ↔ e h ∈ centralizer (X : Set (adjointGroup .F4 K)) := by
    intro h
    rw [hH, Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
    refine ⟨fun hz x hx => ?_, fun hx => ⟨h.2, fun z hz => ?_⟩⟩
    · have h1 := hz.2 ((e.symm x : L) : G)
        (Subgroup.mem_map_of_mem L.subtype (Subgroup.mem_map_of_mem e.symm.toMonoidHom hx))
      have h2 : e.symm x * h = h * e.symm x := Subtype.ext h1
      have h3 := congrArg e h2
      rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h3
    · obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hz
      obtain ⟨x, hx', rfl⟩ := Subgroup.mem_map.1 hw
      have h3 := congrArg e.symm (hx x hx')
      rw [map_mul, map_mul, MulEquiv.symm_apply_apply] at h3
      exact congrArg Subtype.val h3
  have hψX : ∀ h : H, ψ h ∈ centralizer (X : Set (adjointGroup .F4 K)) := fun h =>
    (hmemH (Subgroup.inclusion hHL h)).1 h.2
  have hDX : C3Levi K ≤ centralizer (X : Set (adjointGroup .F4 K)) := by
    rw [(centralizer_nonsplit hXJ hcyc hX).1]
    exact le_sup_right
  have hDH : DG ≤ H := by
    intro g hg
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hg
    obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.1 hw
    rw [Subgroup.coe_subtype, hmemH]
    change e (e.symm d) ∈ _
    rw [MulEquiv.apply_symm_apply]
    exact hDX hd
  set KD : Subgroup H := DG.subgroupOf H with hKD
  have hmemKD : ∀ n : H, n ∈ KD ↔ ψ n ∈ C3Levi K := by
    intro n
    rw [hKD, Subgroup.mem_subgroupOf, hψ_apply]
    constructor
    · intro hn
      obtain ⟨w, hw, hwn⟩ := Subgroup.mem_map.1 hn
      obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.1 hw
      have hinc : Subgroup.inclusion hHL n = e.symm d := Subtype.ext hwn.symm
      rw [hinc]
      change e (e.symm d) ∈ _
      rw [MulEquiv.apply_symm_apply]
      exact hd
    · intro hn
      refine Subgroup.mem_map.2 ⟨Subgroup.inclusion hHL n, Subgroup.mem_map.2
        ⟨e (Subgroup.inclusion hHL n), hn, ?_⟩, rfl⟩
      change e.symm (e (Subgroup.inclusion hHL n)) = _
      rw [MulEquiv.symm_apply_apply]
  have hnormal : KD.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [hmemKD] at hn ⊢
    rw [map_mul, map_mul, map_inv]
    exact mul_mul_inv_mem_C3Levi_of_mem_centralizer_nonsplit hXJ hcyc hX (hψX g) hn
  have hq : CFSG.IsQuasisimple KD := by
    have e1 : C3Levi K ≃* (C3Levi K).map e.symm.toMonoidHom :=
      (C3Levi K).equivMapOfInjective e.symm.toMonoidHom e.symm.injective
    have e2 : (C3Levi K).map e.symm.toMonoidHom ≃* DG :=
      ((C3Levi K).map e.symm.toMonoidHom).equivMapOfInjective L.subtype L.subtype_injective
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((e1.trans e2).trans (Subgroup.subgroupOfEquivOfLe hDH).symm) isQuasisimple_C3Levi
  have hsolv : Group.IsSolvable (H ⧸ KD) := by
    refine Group.isSolvable_of_comm fun a b => ?_
    induction a using QuotientGroup.induction_on with
    | H a =>
      induction b using QuotientGroup.induction_on with
      | H b =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, hmemKD]
        have h := commutator_mem_C3Levi_of_mem_centralizer_nonsplit hXJ hcyc hX (hψX b⁻¹)
          (hψX a⁻¹)
        have hab : (a * b)⁻¹ * (b * a) = b⁻¹ * a⁻¹ * (b⁻¹)⁻¹ * (a⁻¹)⁻¹ := by group
        rw [hab, map_mul, map_mul, map_mul, map_inv ψ b⁻¹, map_inv ψ a⁻¹]
        exact h
  rw [inSubgroup, CFSG.RankThree.PartOne.KFU.layer_eq_of_normal hnormal hq hsolv,
    Subgroup.subgroupOf_map_subtype, inf_of_le_left hDH]

end CFSG.SeitzReduction.F4Pilot
