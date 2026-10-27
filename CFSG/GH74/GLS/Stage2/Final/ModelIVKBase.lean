module

public import CFSG.GH74.GLS.Stage2.Final.ModelSupp
public import CFSG.GH74.GLS.Stage2.Final.ModelComps

public section

namespace CFSG.GH74.GLS.Stage2.Final.ModelBlock

open CFSG.Assembly.LowTwoRank CFSG.GH74.L5U5 Matrix Subgroup CFSG.GH74.GLS
  CFSG.GH74.GLS.Stage1.Thm3.Sec7

variable {F : Type} [Field F]

theorem Ez_yP [Finite F] {M : ModelData F} (hG : GoodModel M) :
    IVK.Ez (yP M) = K1 M ⊔ K2 M := by
  have h := Ez_map_eq hG (MulEquiv.refl (PG M)) (yP M) rfl
  simpa using h

theorem K1_inf_K2 [Finite F] {M : ModelData F} (hG : GoodModel M) :
    K1 M ⊓ K2 M = zpowers (yP M) := by
  apply le_antisymm
  · rintro x ⟨hx1, hx2⟩
    have hc := cen_range hG (iota1 M) (iota1_injective M) (iota1_negOne M)
    rw [← hc]
    refine ⟨⟨x, hx1⟩, Subgroup.mem_center_iff.2 ?_, rfl⟩
    rintro ⟨g, hg⟩
    exact Subtype.ext (K1_K2_comm M hg hx2)
  · rw [Subgroup.zpowers_le]
    exact ⟨⟨⟨-1, M.neg_one_mem_H2⟩, iota1_negOne M⟩, ⟨⟨-1, M.neg_one_mem_H2⟩, iota2_negOne M⟩⟩

theorem pair_mul_aux {G : Type*} [Group G] {a b : G} (hab : a * b = b * a) (ha : a * a = 1)
    (hb : b * b = 1) {x y : G} (hx : x = 1 ∨ x = a ∨ x = b ∨ x = a * b)
    (hy : y = 1 ∨ y = a ∨ y = b ∨ y = a * b) : x * y = 1 ∨ x * y = a ∨ x * y = b ∨ x * y = a * b := by
  have aab : a * (a * b) = b := by rw [← mul_assoc, ha, one_mul]
  have bab : b * (a * b) = a := by rw [hab, ← mul_assoc, hb, one_mul]
  have aba : a * b * a = b := by rw [hab, mul_assoc, ha, mul_one]
  have abb : a * b * b = a := by rw [mul_assoc, hb, mul_one]
  have abab : a * b * (a * b) = 1 := by rw [mul_assoc, bab, ha]
  rcases hx with hx | hx | hx | hx <;> rcases hy with hy | hy | hy | hy <;> rw [hx, hy]
  · left; exact one_mul 1
  · right; left; exact one_mul a
  · right; right; left; exact one_mul b
  · right; right; right; exact one_mul _
  · right; left; exact mul_one a
  · left; exact ha
  · right; right; right; rfl
  · right; right; left; exact aab
  · right; right; left; exact mul_one b
  · right; right; right; exact hab.symm
  · left; exact hb
  · right; left; exact bab
  · right; right; right; exact mul_one _
  · right; right; left; exact aba
  · right; left; exact abb
  · left; exact abab

theorem mem_sup_pair_of_comm {G : Type*} [Group G] {a b : G} (hab : a * b = b * a) (ha : a * a = 1)
    (hb : b * b = 1) {x : G} (hx : x ∈ zpowers a ⊔ zpowers b) :
    x = 1 ∨ x = a ∨ x = b ∨ x = a * b := by
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  let V : Subgroup G :=
    { carrier := {x | x = 1 ∨ x = a ∨ x = b ∨ x = a * b}
      mul_mem' := fun hx hy => pair_mul_aux hab ha hb hx hy
      one_mem' := Or.inl rfl
      inv_mem' := by
        intro x hx
        rcases hx with hx | hx | hx | hx
        · left; rw [hx, inv_one]
        · right; left; rw [hx, hai]
        · right; right; left; rw [hx, hbi]
        · right; right; right; rw [hx, _root_.mul_inv_rev, hai, hbi, ← hab] }
  have haV : a ∈ V := Or.inr (Or.inl rfl)
  have hbV : b ∈ V := Or.inr (Or.inr (Or.inl rfl))
  exact sup_le (Subgroup.zpowers_le.2 haV) (Subgroup.zpowers_le.2 hbV) hx

end CFSG.GH74.GLS.Stage2.Final.ModelBlock
