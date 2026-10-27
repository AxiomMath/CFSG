module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YF3A3
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTdict2

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private theorem mem_sup_zpowers_normal {H : Type*} [Group H] {c : H} {Z : Subgroup H}
    (hZ : Subgroup.zpowers c ⊔ Z ≤ Subgroup.normalizer (Z : Set H)) {x : H}
    (hx : x ∈ Subgroup.zpowers c ⊔ Z) :
    ∃ k : ℤ, ∃ z ∈ Z, c ^ k * z = x := by
  let L : Subgroup H := Subgroup.zpowers c ⊔ Z
  haveI : (Z.subgroupOf L).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hZ
  have htop : (⊤ : Subgroup ↥L) = (Subgroup.zpowers c).subgroupOf L ⊔ Z.subgroupOf L := by
    rw [← Subgroup.subgroupOf_sup (show Subgroup.zpowers c ≤ L from le_sup_left)
      (show Z ≤ L from le_sup_right), Subgroup.subgroupOf_self]
  have hxtop : (⟨x, hx⟩ : ↥L) ∈ (⊤ : Subgroup ↥L) := trivial
  rw [htop] at hxtop
  obtain ⟨y, hy, z, hz, hyz⟩ :=
    (Subgroup.mem_sup_of_normal_right (s := (Subgroup.zpowers c).subgroupOf L)
      (t := Z.subgroupOf L) (x := (⟨x, hx⟩ : ↥L))).mp hxtop
  have hy' : (y : H) ∈ Subgroup.zpowers c := hy
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy'
  refine ⟨k, (z : H), hz, ?_⟩
  rw [hk]
  exact congrArg Subtype.val hyz

theorem f3_P_le_X0 (s : Setting3 G L) : f3P s ≤ f3X0 s :=
  le_inf (f3_P_le_H s) (f3_P_le_cent_V s)

theorem f3_X0_inf_M {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∀ a ∈ f3X0 s, a ∈ L ⊔ centIn s.H L → a ∈ f3P s := by
  intro a ha hM
  rw [f3_centIn_H_L hH, sup_comm] at hM
  have hnorm : Subgroup.zpowers s.t ⊔ L ≤ Subgroup.normalizer (L : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr
      (Subgroup.centralizer_le_normalizer (L : Set G) s.t_mem))
      (Subgroup.le_normalizer (H := L))
  obtain ⟨k, z, hzL, hkz⟩ := mem_sup_zpowers_normal hnorm hM
  have haC : a ∈ Subgroup.centralizer (cen s.fr.B : Set G) := ha.2
  have hle : (cen s.fr.B : Set G) ⊆ (L : Set G) :=
    fun x hx => f3_B_le_L s (Subgroup.mem_inf.mp hx).1
  have htC : s.t ∈ Subgroup.centralizer (cen s.fr.B : Set G) :=
    Subgroup.centralizer_le hle s.t_mem
  have htkC : s.t ^ k ∈ Subgroup.centralizer (cen s.fr.B : Set G) :=
    Subgroup.zpow_mem _ htC k
  have hzC : z ∈ Subgroup.centralizer (cen s.fr.B : Set G) := by
    have hz : z = (s.t ^ k)⁻¹ * a := by
      rw [← hkz]
      group
    rw [hz]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ htkC) haC
  have hzB : z ∈ s.fr.B := by
    have hzV : z ∈ centIn L (cen s.fr.B) := Subgroup.mem_inf.mpr ⟨hzL, hzC⟩
    rwa [f3_centIn_L_V hH] at hzV
  rw [← hkz]
  show s.t ^ k * z ∈ s.fr.B ⊔ Subgroup.zpowers s.t
  rw [sup_comm]
  exact Subgroup.mul_mem_sup (Subgroup.zpow_mem _ (Subgroup.mem_zpowers s.t) k) hzB

theorem f3_X0_cosets {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∀ a ∈ f3X0 s, ∀ b ∈ f3X0 s, a ∈ f3P s ∨ b ∈ f3P s ∨ a⁻¹ * b ∈ f3P s := by
  intro a ha b hb
  by_cases haP : a ∈ f3P s
  · exact Or.inl haP
  by_cases hbP : b ∈ f3P s
  · exact Or.inr (Or.inl hbP)
  refine Or.inr (Or.inr ?_)
  have haH : a ∈ s.H := ha.1
  have hbH : b ∈ s.H := hb.1
  have haM : a ∉ L ⊔ centIn s.H L := fun hM => haP (f3_X0_inf_M hH a ha hM)
  have hbM : b ∉ L ⊔ centIn s.H L := fun hM => hbP (f3_X0_inf_M hH b hb hM)
  have haN : a ∈ normalizer (L : Set G) := s3_H_le_N s hH.hS haH
  have hbN : b ∈ normalizer (L : Set G) := s3_H_le_N s hH.hS hbH
  let α : MulAut (L ⧸ center L) := jHom L ⟨a, haN⟩
  let β : MulAut (L ⧸ center L) := jHom L ⟨b, hbN⟩
  have hα : ActsAs L a α := jHom_actsAs L ⟨a, haN⟩
  have hβ : ActsAs L b β := jHom_actsAs L ⟨b, hbN⟩
  have hαOut : α ∉ innerAut (L ⧸ center L) :=
    s3_outer_of_not_mem_M s hH.hS haH haM hα
  have hβOut : β ∉ innerAut (L ⧸ center L) :=
    s3_outer_of_not_mem_M s hH.hS hbH hbM hβ
  have hαinvOut : α⁻¹ ∉ innerAut (L ⧸ center L) :=
    fun h => hαOut (by simpa using Subgroup.inv_mem _ h)
  have hinner : α⁻¹ * β ∈ innerAut (L ⧸ center L) := by
    rw [Subgroup.mul_mem_iff_of_index_two hH.hOut]
    exact iff_of_false hαinvOut hβOut
  have hActs : ActsAs L (a⁻¹ * b) (α⁻¹ * β) :=
    actsAs_mul L (actsAs_inv L hα) hβ
  have habH : a⁻¹ * b ∈ s.H := Subgroup.mul_mem s.H (Subgroup.inv_mem s.H haH) hbH
  have habX0 : a⁻¹ * b ∈ f3X0 s :=
    Subgroup.mul_mem (f3X0 s) (Subgroup.inv_mem (f3X0 s) ha) hb
  by_contra habP
  have habM : a⁻¹ * b ∉ L ⊔ centIn s.H L :=
    fun hM => habP (f3_X0_inf_M hH (a⁻¹ * b) habX0 hM)
  exact (s3_outer_of_not_mem_M s hH.hS habH habM hActs) hinner

theorem f3_extCtx {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ExtCtx (f3P s) (f3X0 s) (f3Y s) (f3N s) := by
  refine ⟨f3_P_le_X0 s, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    exact ⟨(f3_X0_le_N hH).trans (f3_N_le_X s) ha, ha.2⟩
  · intro n hn y hy
    exact f3_Y_normal hH n (f3_N_le_X s hn) y hy
  · intro y hy p hp
    exact (Subgroup.mem_normalizer_iff.mp (show y ∈ s.X from hy.1) p).mp hp
  · intro n hn p hp
    exact (Subgroup.mem_normalizer_iff.mp (f3_N_le_X s hn) p).mp hp
  · intro y hy a ha
    exact f3_X0_normal hH y hy.1 a ha
  · intro n hn a ha
    exact f3_X0_normal hH n (f3_N_le_X s hn) a ha
  · exact f3_X0_cosets hH

end CFSG.OddStandard.HigherRank.YamadaG23
