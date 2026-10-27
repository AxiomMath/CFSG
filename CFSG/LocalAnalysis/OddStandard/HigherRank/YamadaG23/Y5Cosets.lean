module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YF3A1
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTdict2

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y5_H_cosets {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∀ a ∈ s.H, ∀ b ∈ s.H, a ∈ L ⊔ centIn s.H L ∨ b ∈ L ⊔ centIn s.H L ∨
      a⁻¹ * b ∈ L ⊔ centIn s.H L := by
  intro a ha b hb
  by_cases haM : a ∈ L ⊔ centIn s.H L
  · exact Or.inl haM
  by_cases hbM : b ∈ L ⊔ centIn s.H L
  · exact Or.inr (Or.inl hbM)
  refine Or.inr (Or.inr ?_)
  have haN : a ∈ normalizer (L : Set G) := s3_H_le_N s hH.hS ha
  have hbN : b ∈ normalizer (L : Set G) := s3_H_le_N s hH.hS hb
  let α : MulAut (L ⧸ center L) := jHom L ⟨a, haN⟩
  let β : MulAut (L ⧸ center L) := jHom L ⟨b, hbN⟩
  have hα : ActsAs L a α := jHom_actsAs L ⟨a, haN⟩
  have hβ : ActsAs L b β := jHom_actsAs L ⟨b, hbN⟩
  have hαOut : α ∉ innerAut (L ⧸ center L) :=
    s3_outer_of_not_mem_M s hH.hS ha haM hα
  have hβOut : β ∉ innerAut (L ⧸ center L) :=
    s3_outer_of_not_mem_M s hH.hS hb hbM hβ
  have hαinvOut : α⁻¹ ∉ innerAut (L ⧸ center L) :=
    fun h => hαOut (by simpa using Subgroup.inv_mem _ h)
  have hinner : α⁻¹ * β ∈ innerAut (L ⧸ center L) := by
    rw [Subgroup.mul_mem_iff_of_index_two hH.hOut]
    exact iff_of_false hαinvOut hβOut
  have hActs : ActsAs L (a⁻¹ * b) (α⁻¹ * β) :=
    actsAs_mul L (actsAs_inv L hα) hβ
  have habH : a⁻¹ * b ∈ s.H := Subgroup.mul_mem s.H (Subgroup.inv_mem s.H ha) hb
  by_contra habM
  exact (s3_outer_of_not_mem_M s hH.hS habH habM hActs) hinner

theorem y5_T_cosets {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∀ a ∈ s.T, ∀ b ∈ s.T, a ∈ s.R ∨ b ∈ s.R ∨ a⁻¹ * b ∈ s.R := by
  intro a ha b hb
  have hT : s.T ≤ s.H := s.sylow_T.1
  rw [s3_R_eq s hH.hS]
  rcases y5_H_cosets hH a (hT ha) b (hT hb) with hM | hM | hM
  · exact Or.inl ⟨ha, hM⟩
  · exact Or.inr (Or.inl ⟨hb, hM⟩)
  · exact Or.inr (Or.inr ⟨Subgroup.mul_mem s.T (Subgroup.inv_mem s.T ha) hb, hM⟩)

private theorem y5_mem_sup_zpowers_normal {H : Type*} [Group H] {c : H} {Z : Subgroup H}
    (hZ : Subgroup.zpowers c ⊔ Z ≤ Subgroup.normalizer (Z : Set H)) {x : H}
    (hx : x ∈ Subgroup.zpowers c ⊔ Z) :
    ∃ k : ℤ, ∃ z ∈ Z, c ^ k * z = x := by
  let M : Subgroup H := Subgroup.zpowers c ⊔ Z
  haveI : (Z.subgroupOf M).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hZ
  have htop : (⊤ : Subgroup ↥M) = (Subgroup.zpowers c).subgroupOf M ⊔ Z.subgroupOf M := by
    rw [← Subgroup.subgroupOf_sup (show Subgroup.zpowers c ≤ M from le_sup_left)
      (show Z ≤ M from le_sup_right), Subgroup.subgroupOf_self]
  have hxtop : (⟨x, hx⟩ : ↥M) ∈ (⊤ : Subgroup ↥M) := trivial
  rw [htop] at hxtop
  obtain ⟨y, hy, z, hz, hyz⟩ :=
    (Subgroup.mem_sup_of_normal_right (s := (Subgroup.zpowers c).subgroupOf M)
      (t := Z.subgroupOf M) (x := (⟨x, hx⟩ : ↥M))).mp hxtop
  have hy' : (y : H) ∈ Subgroup.zpowers c := hy
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy'
  refine ⟨k, (z : H), hz, ?_⟩
  rw [hk]
  exact congrArg Subtype.val hyz

theorem y5_mem_L_sup_t (s : Setting3 G L) {x : G} (hx : x ∈ L ⊔ zpowers s.t) :
    ∃ ℓ ∈ L, ∃ i : ℤ, x = ℓ * s.t ^ i := by
  rw [sup_comm] at hx
  have hnorm : Subgroup.zpowers s.t ⊔ L ≤ Subgroup.normalizer (L : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr
      (Subgroup.centralizer_le_normalizer (L : Set G) s.t_mem))
      (Subgroup.le_normalizer (H := L))
  obtain ⟨k, ℓ, hℓL, hkℓ⟩ := y5_mem_sup_zpowers_normal hnorm hx
  refine ⟨ℓ, hℓL, k, ?_⟩
  rw [← hkℓ]
  exact (Subgroup.mem_centralizer_iff.mp (Subgroup.zpow_mem _ s.t_mem k) ℓ hℓL).symm

theorem y5_cent_inf_M {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e)
    {V : Subgroup G} (hV : V ≤ L) :
    ∀ a ∈ centIn s.H V, a ∈ L ⊔ centIn s.H L → a ∈ centIn L V ⊔ zpowers s.t := by
  intro a ha hM
  rw [f3_centIn_H_L hH] at hM
  obtain ⟨ℓ, hℓL, i, rfl⟩ := y5_mem_L_sup_t s hM
  have htC : s.t ∈ Subgroup.centralizer (V : Set G) :=
    Subgroup.centralizer_le hV s.t_mem
  have htiC : s.t ^ i ∈ Subgroup.centralizer (V : Set G) := Subgroup.zpow_mem _ htC i
  have haC : ℓ * s.t ^ i ∈ Subgroup.centralizer (V : Set G) := ha.2
  have hℓC : ℓ ∈ Subgroup.centralizer (V : Set G) := by
    have h : ℓ = (ℓ * s.t ^ i) * (s.t ^ i)⁻¹ := by group
    rw [h]
    exact Subgroup.mul_mem _ haC (Subgroup.inv_mem _ htiC)
  exact Subgroup.mul_mem_sup (Subgroup.mem_inf.mpr ⟨hℓL, hℓC⟩)
    (Subgroup.zpow_mem _ (Subgroup.mem_zpowers s.t) i)

theorem y5_cent_cosets {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e)
    {V : Subgroup G} (hV : V ≤ L) :
    ∀ a ∈ centIn s.H V, ∀ b ∈ centIn s.H V,
      a ∈ centIn L V ⊔ zpowers s.t ∨ b ∈ centIn L V ⊔ zpowers s.t ∨
        a⁻¹ * b ∈ centIn L V ⊔ zpowers s.t := by
  intro a ha b hb
  by_cases haP : a ∈ centIn L V ⊔ zpowers s.t
  · exact Or.inl haP
  by_cases hbP : b ∈ centIn L V ⊔ zpowers s.t
  · exact Or.inr (Or.inl hbP)
  refine Or.inr (Or.inr ?_)
  have haH : a ∈ s.H := ha.1
  have hbH : b ∈ s.H := hb.1
  have haM : a ∉ L ⊔ centIn s.H L := fun hM => haP (y5_cent_inf_M hH hV a ha hM)
  have hbM : b ∉ L ⊔ centIn s.H L := fun hM => hbP (y5_cent_inf_M hH hV b hb hM)
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
  have habC : a⁻¹ * b ∈ centIn s.H V :=
    Subgroup.mul_mem (centIn s.H V) (Subgroup.inv_mem (centIn s.H V) ha) hb
  have habM : a⁻¹ * b ∈ L ⊔ centIn s.H L := by
    by_contra h
    exact (s3_outer_of_not_mem_M s hH.hS habH h hActs) hinner
  exact y5_cent_inf_M hH hV (a⁻¹ * b) habC habM

end CFSG.OddStandard.HigherRank.YamadaG23
