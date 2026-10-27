module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4TowerHyp
public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4GL62Defs
public import Mathlib.GroupTheory.SemidirectProduct

public section

namespace CFSG.OddStandard.AltStdSmall4.Tower

open Subgroup Matrix

@[expose] def vecAut (A : GL (Fin 6) (ZMod 2)) : MulAut (Multiplicative (Fin 6 → ZMod 2)) where
  toFun v := Multiplicative.ofAdd ((A : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ v.toAdd)
  invFun v := Multiplicative.ofAdd
    (((A⁻¹ : GL (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ v.toAdd)
  left_inv v := by
    simp only [toAdd_ofAdd, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, ofAdd_toAdd]
  right_inv v := by
    simp only [toAdd_ofAdd, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec, ofAdd_toAdd]
  map_mul' v w := by
    simp only [toAdd_mul, Matrix.mulVec_add, ofAdd_add]

@[simp] theorem vecAut_apply (A : GL (Fin 6) (ZMod 2)) (v : Multiplicative (Fin 6 → ZMod 2)) :
    vecAut A v = Multiplicative.ofAdd ((A : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ v.toAdd) := rfl

@[expose] def vecHom : GL (Fin 6) (ZMod 2) →* MulAut (Multiplicative (Fin 6 → ZMod 2)) where
  toFun := vecAut
  map_one' := by
    ext v
    simp only [vecAut_apply, Units.val_one, Matrix.one_mulVec, ofAdd_toAdd, MulAut.one_apply]
  map_mul' A B := by
    ext v
    simp only [vecAut_apply, Units.val_mul, ← Matrix.mulVec_mulVec, MulAut.mul_apply, toAdd_ofAdd]

@[expose] def affAct (S : Subgroup (GL (Fin 6) (ZMod 2))) :
    S →* MulAut (Multiplicative (Fin 6 → ZMod 2)) :=
  vecHom.comp S.subtype

@[simp] theorem affAct_apply (S : Subgroup (GL (Fin 6) (ZMod 2))) (s : S)
    (v : Multiplicative (Fin 6 → ZMod 2)) :
    affAct S s v =
      Multiplicative.ofAdd (((s : GL (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ
        v.toAdd) := rfl

abbrev Grp (S : Subgroup (GL (Fin 6) (ZMod 2))) : Type :=
  Multiplicative (Fin 6 → ZMod 2) ⋊[affAct S] S

@[expose] def t₀ (S : Subgroup (GL (Fin 6) (ZMod 2))) (h : GL62.z₀ ∈ S) : Grp S :=
  ⟨1, ⟨GL62.z₀, h⟩⟩

theorem t₀_left (S : Subgroup (GL (Fin 6) (ZMod 2))) (h : GL62.z₀ ∈ S) : (t₀ S h).left = 1 :=
  rfl

theorem t₀_right (S : Subgroup (GL (Fin 6) (ZMod 2))) (h : GL62.z₀ ∈ S) :
    (t₀ S h).right = ⟨GL62.z₀, h⟩ :=
  rfl

@[expose] def e12 : GL (Fin 3) (ZMod 2) :=
  ⟨!![1, 1, 0; 0, 1, 0; 0, 0, 1], !![1, 1, 0; 0, 1, 0; 0, 0, 1], by decide, by decide⟩

@[expose] def e23 : GL (Fin 3) (ZMod 2) :=
  ⟨!![1, 0, 0; 0, 1, 1; 0, 0, 1], !![1, 0, 0; 0, 1, 1; 0, 0, 1], by decide, by decide⟩

@[expose] def cyc3 : GL (Fin 3) (ZMod 2) :=
  ⟨!![0, 0, 1; 1, 0, 0; 0, 1, 0], !![0, 1, 0; 0, 0, 1; 1, 0, 0], by decide, by decide⟩

theorem z0_mem_B₀ : GL62.z₀ ∈ GL62.B₀ := mem_sup_right (mem_zpowers _)

theorem dg_mem_B₀ (A : GL (Fin 3) (ZMod 2)) : GL62.dg A ∈ GL62.B₀ :=
  mem_sup_left (MonoidHom.mem_range.2 ⟨A, rfl⟩)

theorem z0_mem_MW : GL62.z₀ ∈ GL62.MW := mem_sup_left z0_mem_B₀

theorem dg_mem_MW (A : GL (Fin 3) (ZMod 2)) : GL62.dg A ∈ GL62.MW := mem_sup_left (dg_mem_B₀ A)

theorem gW_mem_MW : GL62.gW ∈ GL62.MW := mem_sup_right (mem_zpowers _)

theorem z0_mem_MS : GL62.z₀ ∈ GL62.MS := mem_sup_left z0_mem_B₀

theorem dg_mem_MS (A : GL (Fin 3) (ZMod 2)) : GL62.dg A ∈ GL62.MS := mem_sup_left (dg_mem_B₀ A)

theorem gS_mem_MS : GL62.gS ∈ GL62.MS := mem_sup_right (mem_zpowers _)

@[expose] def wrH₁ : GL (Fin 6) (ZMod 2) :=
  GL62.dg cyc3 * GL62.gW * GL62.dg e12 * GL62.gW * (GL62.dg cyc3)⁻¹

@[expose] def wrH₂ : GL (Fin 6) (ZMod 2) :=
  (GL62.dg cyc3)⁻¹ * GL62.gW * GL62.dg cyc3 * GL62.dg e12 * (GL62.dg cyc3)⁻¹ * GL62.gW *
    GL62.dg cyc3

@[expose] def wrS : Subgroup (GL (Fin 6) (ZMod 2)) :=
  closure {GL62.z₀, GL62.dg e12, GL62.dg e23, wrH₁, wrH₂}

theorem z0_mem_wrS : GL62.z₀ ∈ wrS := subset_closure (by simp)

theorem dg_e12_mem_wrS : GL62.dg e12 ∈ wrS := subset_closure (by simp)

theorem dg_e23_mem_wrS : GL62.dg e23 ∈ wrS := subset_closure (by simp)

theorem wrH₁_mem_wrS : wrH₁ ∈ wrS := subset_closure (by simp)

theorem wrH₂_mem_wrS : wrH₂ ∈ wrS := subset_closure (by simp)

theorem wrH₁_mem_MW : wrH₁ ∈ GL62.MW := by
  unfold wrH₁
  exact mul_mem (mul_mem (mul_mem (mul_mem (dg_mem_MW _) gW_mem_MW) (dg_mem_MW _)) gW_mem_MW)
    (inv_mem (dg_mem_MW _))

theorem wrH₂_mem_MW : wrH₂ ∈ GL62.MW := by
  unfold wrH₂
  exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (inv_mem (dg_mem_MW _))
    gW_mem_MW) (dg_mem_MW _)) (dg_mem_MW _)) (inv_mem (dg_mem_MW _))) gW_mem_MW) (dg_mem_MW _)

theorem wrS_le_MW : wrS ≤ GL62.MW := by
  refine closure_le _ |>.2 ?_
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact z0_mem_MW
  · exact dg_mem_MW _
  · exact dg_mem_MW _
  · exact wrH₁_mem_MW
  · exact wrH₂_mem_MW

@[expose] def slH₁ : GL (Fin 6) (ZMod 2) :=
  GL62.gS * (GL62.dg cyc3)⁻¹ * GL62.dg e12 * GL62.dg cyc3 * GL62.gS

@[expose] def slH₂ : GL (Fin 6) (ZMod 2) :=
  GL62.gS * GL62.z₀ * GL62.gS * GL62.dg cyc3 * GL62.dg e12 * (GL62.dg cyc3)⁻¹ * GL62.z₀ *
    GL62.gS * (GL62.dg cyc3)⁻¹

@[expose] def slS : Subgroup (GL (Fin 6) (ZMod 2)) :=
  closure {GL62.z₀, GL62.dg e12, GL62.dg e23, slH₁, slH₂}

theorem z0_mem_slS : GL62.z₀ ∈ slS := subset_closure (by simp)

theorem dg_e12_mem_slS : GL62.dg e12 ∈ slS := subset_closure (by simp)

theorem dg_e23_mem_slS : GL62.dg e23 ∈ slS := subset_closure (by simp)

theorem slH₁_mem_slS : slH₁ ∈ slS := subset_closure (by simp)

theorem slH₂_mem_slS : slH₂ ∈ slS := subset_closure (by simp)

theorem slH₁_mem_MS : slH₁ ∈ GL62.MS := by
  unfold slH₁
  exact mul_mem (mul_mem (mul_mem (mul_mem gS_mem_MS (inv_mem (dg_mem_MS _))) (dg_mem_MS _))
    (dg_mem_MS _)) gS_mem_MS

theorem slH₂_mem_MS : slH₂ ∈ GL62.MS := by
  unfold slH₂
  exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem gS_mem_MS
    z0_mem_MS) gS_mem_MS) (dg_mem_MS _)) (dg_mem_MS _)) (inv_mem (dg_mem_MS _))) z0_mem_MS)
    gS_mem_MS) (inv_mem (dg_mem_MS _))

theorem slS_le_MS : slS ≤ GL62.MS := by
  refine closure_le _ |>.2 ?_
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact z0_mem_MS
  · exact dg_mem_MS _
  · exact dg_mem_MS _
  · exact slH₁_mem_MS
  · exact slH₂_mem_MS

@[expose] def WrFalse : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    ∀ t : G, CentHyp t → ∀ ι : Grp wrS →* G, Function.Injective ι →
      ι (t₀ wrS z0_mem_wrS) = t → False

@[expose] def SlFalse : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    ∀ t : G, CentHyp t → ∀ ι : Grp slS →* G, Function.Injective ι →
      ι (t₀ slS z0_mem_slS) = t → False

end CFSG.OddStandard.AltStdSmall4.Tower
