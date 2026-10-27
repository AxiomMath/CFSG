module

public import CFSG.Assembly.Defs
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BrLift

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG
open scoped commutatorElement

section Index

variable {A M Γ₀ : Type*} [Group A] [Group M] [Group Γ₀]

theorem mem_normalizer_of_map_conj_eq {J : Subgroup M} {u v : M}
    (h : J.map (MulAut.conj u).toMonoidHom = J.map (MulAut.conj v).toMonoidHom) :
    v⁻¹ * u ∈ normalizer (J : Set M) := by
  have key : ∀ u v : M, J.map (MulAut.conj u).toMonoidHom = J.map (MulAut.conj v).toMonoidHom →
      ∀ x ∈ J, (v⁻¹ * u) * x * (v⁻¹ * u)⁻¹ ∈ J := by
    intro u v h x hx
    have h1 : u * x * u⁻¹ ∈ J.map (MulAut.conj u).toMonoidHom := ⟨x, hx, by simp⟩
    rw [h] at h1
    obtain ⟨y, hy, hyx⟩ := h1
    have hyx' : v * y * v⁻¹ = u * x * u⁻¹ := by simpa using hyx
    have : (v⁻¹ * u) * x * (v⁻¹ * u)⁻¹ = y :=
      calc (v⁻¹ * u) * x * (v⁻¹ * u)⁻¹ = v⁻¹ * (u * x * u⁻¹) * v := by group
        _ = v⁻¹ * (v * y * v⁻¹) * v := by rw [hyx']
        _ = y := by group
    rw [this]
    exact hy
  refine mem_normalizer_of_conj_mem (key u v h) (fun x hx => ?_)
  have h2 := key v u h.symm x hx
  have e : (v⁻¹ * u)⁻¹ * x * (v⁻¹ * u) = (u⁻¹ * v) * x * (u⁻¹ * v)⁻¹ := by group
  rw [e]
  exact h2

theorem index_le_two [Finite Γ₀] (ν : A →* M) (π : A →* Γ₀) (hπ : Function.Surjective π)
    {K : Subgroup Γ₀} {J : Subgroup M} (hJ : IsComponent J) {Dl : Subgroup A}
    (hnorm : ∀ h : A, ν h ∈ normalizer (J : Set M) → h ∈ normalizer (Dl : Set A))
    (hDl : Dl.map π = K)
    (hC : ∀ J₁ J₂ J₃ : Subgroup M, IsComponent J₁ → IsComponent J₂ → IsComponent J₃ →
      J₁ ≠ J₂ → J₁ ≠ J₃ → J₂ ≠ J₃ → False) :
    (normalizer (K : Set Γ₀)).index ≤ 2 := by
  by_contra hlt
  have h3 : 2 < Nat.card (Γ₀ ⧸ normalizer (K : Set Γ₀)) := not_le.mp hlt
  have := Fintype.ofFinite (Γ₀ ⧸ normalizer (K : Set Γ₀))
  rw [Nat.card_eq_fintype_card] at h3
  obtain ⟨q₁, q₂, q₃, h12, h13, h23⟩ := Fintype.two_lt_card_iff.mp h3
  obtain ⟨c₁, rfl⟩ := QuotientGroup.mk_surjective q₁
  obtain ⟨c₂, rfl⟩ := QuotientGroup.mk_surjective q₂
  obtain ⟨c₃, rfl⟩ := QuotientGroup.mk_surjective q₃
  obtain ⟨x₁, rfl⟩ := hπ c₁
  obtain ⟨x₂, rfl⟩ := hπ c₂
  obtain ⟨x₃, rfl⟩ := hπ c₃
  have hJc : ∀ x : A, IsComponent (J.map (MulAut.conj (ν x)).toMonoidHom) :=
    fun x => LocalCores.isComponent_map_mulEquiv _ hJ
  have key : ∀ x y : A,
      J.map (MulAut.conj (ν x)).toMonoidHom = J.map (MulAut.conj (ν y)).toMonoidHom →
      (QuotientGroup.mk (π x) : Γ₀ ⧸ normalizer (K : Set Γ₀)) = QuotientGroup.mk (π y) := by
    intro x y h
    have h1 : (ν y)⁻¹ * ν x ∈ normalizer (J : Set M) := mem_normalizer_of_map_conj_eq h
    have h2 : y⁻¹ * x ∈ normalizer (Dl : Set A) := hnorm _ (by simpa using h1)
    have h4 := mem_normalizer_map_br π h2
    rw [hDl] at h4
    apply QuotientGroup.eq.mpr
    have h5 := (normalizer (K : Set Γ₀)).inv_mem h4
    simpa using h5
  exact hC _ _ _ (hJc x₁) (hJc x₂) (hJc x₃) (fun h => h12 (key _ _ h)) (fun h => h13 (key _ _ h))
    (fun h => h23 (key _ _ h))

theorem normal_of_index_le_two {G : Type*} [Group G] [Finite G] {H : Subgroup G}
    (h : H.index ≤ 2) : H.Normal := by
  have hpos : 0 < H.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  rcases (by omega : H.index = 1 ∨ H.index = 2) with h1 | h2
  · have := Subgroup.index_eq_one.mp h1
    subst this
    infer_instance
  · exact Subgroup.normal_of_index_eq_two h2

end Index

section Transport

variable {Γ₀ : Type*} [Group Γ₀]

theorem isPGroup_subgroupOf {p : ℕ} {P : Subgroup Γ₀} (hP : IsPGroup p ↥P) (N : Subgroup Γ₀) :
    IsPGroup p ↥(P.subgroupOf N) := by
  intro x
  obtain ⟨k, hk⟩ := hP ⟨((x : ↥N) : Γ₀), x.2⟩
  exact ⟨k, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hk))⟩

theorem isSylowOf_subgroupOf {p : ℕ} [Fact p.Prime] [Finite Γ₀] {N X Y : Subgroup Γ₀}
    (hX : X ≤ N) (hY : Y ≤ N) (h : CFSG.ABGLocalTools.IsSylowOf p X Y) :
    CFSG.ABGLocalTools.IsSylowOf p (X.subgroupOf N) (Y.subgroupOf N) := by
  rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff N, Subgroup.subgroupOf_map_subtype,
    Subgroup.subgroupOf_map_subtype, inf_of_le_left hX, inf_of_le_left hY]
  exact h

theorem centralQuot_equiv {N K : Subgroup Γ₀} (h : K ≤ N) :
    Nonempty ((↥(K.subgroupOf N) ⧸ center ↥(K.subgroupOf N)) ≃* (↥K ⧸ center ↥K)) := by
  let e : ↥(K.subgroupOf N) ≃* ↥K := Subgroup.subgroupOfEquivOfLe h
  exact ⟨QuotientGroup.congr (center ↥(K.subgroupOf N)) (center ↥K) e
    (Subgroup.map_center_eq e)⟩

end Transport

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
