module

public import CFSG.GH74.GLS.C3.Layer1.St1EndNFam

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)

open Subgroup CFSG CFSG.ABGLocalTools Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)

namespace Lem711Cfg

variable {X : Type} [Group X] [Finite X] {L K : Subgroup X} {x y : X}

theorem card_mulAut_eq_card_outer_mul (h : Lem711Cfg X L K x y) :
    Nat.card (MulAut ↥L) = Nat.card (Outer ↥L) * Nat.card ↥L := by
  have hc : Function.Injective (MulAut.conj : ↥L →* MulAut ↥L) :=
    IVK.GHInv.conj_injective_of_center_eq_bot h.center_L_eq_bot
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (inner ↥L)
  have h2 : Nat.card ↥(inner ↥L) = Nat.card ↥L :=
    (Nat.card_congr (MonoidHom.ofInjective hc).toEquiv).symm
  rw [h2] at h1
  exact h1

theorem index_le_of_card_outer_le (h : Lem711Cfg X L K x y) {c : ℕ}
    (hc : Nat.card (Outer ↥L) ≤ c) : L.index ≤ c := by
  refine h.index_le_of_card_mulAut_le ?_
  rw [h.card_mulAut_eq_card_outer_mul]
  exact Nat.mul_le_mul_right _ hc

theorem card_dvd_centralizer_L (h : Lem711Cfg X L K x y) (hxL : x ∈ L) :
    360 ∣ Nat.card ↥(centralizer ({(⟨x, hxL⟩ : ↥L)} : Set ↥L)) := by
  have h1 : Nat.card (↥K ⧸ pPrimeCore 2 ↥K) ∣ Nat.card ↥K := Subgroup.card_quotient_dvd_card _
  have hle : K.subgroupOf L ≤ centralizer ({(⟨x, hxL⟩ : ↥L)} : Set ↥L) :=
    (h.isCompIn_centralizer_L hxL).1
  have h2 : Nat.card ↥(K.subgroupOf L) ∣ Nat.card ↥(centralizer ({(⟨x, hxL⟩ : ↥L)} : Set ↥L)) :=
    Subgroup.card_dvd_of_le hle
  have h3 : Nat.card ↥(K.subgroupOf L) = Nat.card ↥K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.K_le).toEquiv
  rw [h3] at h2
  rw [← h.card_K_bar]
  exact h1.trans h2

end Lem711Cfg

theorem lem711_empty_of_cent_card {P : (X : Type) → [Group X] → Prop}
    (hOut : ∀ (L : Type) [Group L] [Finite L], P L → Nat.card (Outer L) ≤ 2)
    (hcard : ∀ (L : Type) [Group L] [Finite L], P L → ∀ y : L, y * y = 1 → y ≠ 1 →
      ¬ 360 ∣ Nat.card ↥(centralizer ({y} : Set L))) :
    Lem711Empty P := by
  intro X _ _ L K x y h hL
  have hxL : x ∈ L := h.x_mem_L_of_index_le_two (h.index_le_of_card_outer_le (hOut ↥L hL))
  have hxx : x * x = 1 := by
    have := pow_orderOf_eq_one x
    rwa [h.hx, pow_two] at this
  have hy2 : (⟨x, hxL⟩ : ↥L) * ⟨x, hxL⟩ = 1 := Subtype.ext hxx
  have hy1 : (⟨x, hxL⟩ : ↥L) ≠ 1 := by
    intro h1
    have : x = 1 := congrArg Subtype.val h1
    have h3 := h.hx
    rw [this, orderOf_one] at h3
    omega
  exact hcard ↥L hL _ hy2 hy1 (h.card_dvd_centralizer_L hxL)

theorem lem711_empty_of_comp_top {P : (X : Type) → [Group X] → Prop}
    (hOut : ∀ (L : Type) [Group L] [Finite L], P L → Nat.card (Outer L) ≤ 2)
    (htop : ∀ (L : Type) [Group L] [Finite L], P L → ∀ y : L, y * y = 1 → y ≠ 1 →
      ∃ (C₀ : Type) (_ : Group C₀) (_ : Finite C₀) (_ : ↥(centralizer ({y} : Set L)) ≃* C₀),
        ∀ K : Subgroup C₀, IsComponent K → K = ⊤) :
    Lem711Empty P := by
  intro X _ _ L K x y h hL
  have hxL : x ∈ L := h.x_mem_L_of_index_le_two (h.index_le_of_card_outer_le (hOut ↥L hL))
  refine h.false_of_comp_mem_of_mem hxL fun y hy2 hy1 B hB => ?_
  obtain ⟨C₀, _, _, φ, hC₀⟩ := htop ↥L hL y hy2 hy1
  have hmap := hC₀ _ (LocalCores.isComponent_map_mulEquiv φ hB.2)
  have htop' : B.subgroupOf (centralizer ({y} : Set ↥L)) = ⊤ := by
    apply Subgroup.map_injective (f := φ.toMonoidHom) φ.injective
    rw [hmap, Subgroup.map_top_of_surjective _ φ.surjective]
  have hy : (⟨y, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩ : ↥(centralizer ({y} : Set ↥L))) ∈
      B.subgroupOf (centralizer ({y} : Set ↥L)) := by
    rw [htop']
    exact Subgroup.mem_top _
  exact hy

theorem isMulCommutative_of_mulEquiv' {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (hB : IsMulCommutative B) : IsMulCommutative A :=
  ⟨⟨fun a b => e.injective (by rw [map_mul, map_mul]; exact hB.is_comm.comm _ _)⟩⟩

theorem lem711_empty_of_cent_card_comm {P : (X : Type) → [Group X] → Prop}
    (hOut : ∀ (L : Type) [Group L] [Finite L], P L → IsMulCommutative (Outer L))
    (hcard : ∀ (L : Type) [Group L] [Finite L], P L → ∀ y : L, y * y = 1 → y ≠ 1 →
      ¬ 360 ∣ Nat.card ↥(centralizer ({y} : Set L))) :
    Lem711Empty P := by
  intro X _ _ L K x y h hL
  have hxL : x ∈ L := h.x_mem_L_of_outer_comm (hOut ↥L hL)
  have hxx : x * x = 1 := by
    have := pow_orderOf_eq_one x
    rwa [h.hx, pow_two] at this
  have hy2 : (⟨x, hxL⟩ : ↥L) * ⟨x, hxL⟩ = 1 := Subtype.ext hxx
  have hy1 : (⟨x, hxL⟩ : ↥L) ≠ 1 := by
    intro h1
    have : x = 1 := congrArg Subtype.val h1
    have h3 := h.hx
    rw [this, orderOf_one] at h3
    omega
  exact hcard ↥L hL _ hy2 hy1 (h.card_dvd_centralizer_L hxL)

end CFSG.GH74.GLS
