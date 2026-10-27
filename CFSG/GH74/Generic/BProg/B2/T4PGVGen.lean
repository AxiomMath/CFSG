module

public import CFSG.GH74.Generic.BProg.B2.ShapeGenS13
public import CFSG.GH74.Generic.BProg.B2.GenLocU4Inner
public import CFSG.GH74.Generic.BProg.B3.S3Sec29H

public section

namespace CFSG.GH74.Generic.BProg.B2.T4.PGV

open CFSG CFSG.GH74.Generic.BProg CFSG.Assembly.LowTwoRank Subgroup
open scoped MatrixGroups

section Four

variable {G : Type} [Group G]

theorem mem_zpowers_invol {v h : G} (hv : v * v = 1) (hh : h ∈ zpowers v) : h = 1 ∨ h = v := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
  have hv2 : v ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hv
  obtain ⟨j, rfl | rfl⟩ := Int.even_or_odd' k
  · left; rw [zpow_mul, hv2, one_zpow]
  · right; rw [zpow_add, zpow_mul, hv2, one_zpow, one_mul, zpow_one]

theorem comm_of_mem_zpowers {v₁ v₂ : G} (h₁ : v₁ * v₁ = 1) (h₁₂ : v₁ * v₂ = v₂ * v₁) :
    ∀ h ∈ zpowers v₁, h * v₂ = v₂ * h := by
  intro h hh
  rcases mem_zpowers_invol h₁ hh with rfl | rfl
  · simp
  · exact h₁₂

theorem mem_four {v₁ v₂ x : G} (h₁ : v₁ * v₁ = 1) (h₂ : v₂ * v₂ = 1) (h₁₂ : v₁ * v₂ = v₂ * v₁)
    (hx : x ∈ zpowers v₁ ⊔ zpowers v₂) : x = 1 ∨ x = v₁ ∨ x = v₂ ∨ x = v₁ * v₂ := by
  obtain ⟨h, hh, rfl | rfl⟩ :=
    B3.S3Sec29H.mem_sup_zpowers h₂ (comm_of_mem_zpowers h₁ h₁₂) hx
  · rcases mem_zpowers_invol h₁ hh with rfl | rfl
    · left; rfl
    · right; left; rfl
  · rcases mem_zpowers_invol h₁ hh with rfl | rfl
    · right; right; left; simp
    · right; right; right; rfl

theorem isElementaryAbelian_four {v₁ v₂ : G} (h₁ : v₁ * v₁ = 1) (h₂ : v₂ * v₂ = 1)
    (h₁₂ : v₁ * v₂ = v₂ * v₁) : CFSG.IsElementaryAbelian 2 ↥(zpowers v₁ ⊔ zpowers v₂) :=
  B3.S3Sec29H.isElementaryAbelian_sup_zpowers (B3.S3Sec29H.isElementaryAbelian_zpowers h₁) h₂
    (comm_of_mem_zpowers h₁ h₁₂)

theorem card_four {v₁ v₂ : G} (h₁ : v₁ * v₁ = 1) (h₂ : v₂ * v₂ = 1) (h₁₂ : v₁ * v₂ = v₂ * v₁)
    (h₁1 : v₁ ≠ 1) (h₂1 : v₂ ≠ 1) (hne : v₁ ≠ v₂) : Nat.card ↥(zpowers v₁ ⊔ zpowers v₂) = 4 := by
  have hnot : v₂ ∉ zpowers v₁ := by
    intro h
    rcases mem_zpowers_invol h₁ h with h | h
    · exact h₂1 h
    · exact hne h.symm
  rw [B3.S3Sec29H.card_sup_zpowers h₂ hnot (comm_of_mem_zpowers h₁ h₁₂), Nat.card_zpowers,
    orderOf_eq_prime (by rw [sq]; exact h₁) h₁1]

variable [Finite G]

theorem sup_centralizer_eq_top_of_gammaAct {v₁ v₂ : G} (h₁ : v₁ * v₁ = 1) (h₂ : v₂ * v₂ = 1)
    (h₁₂ : v₁ * v₂ = v₂ * v₁) (hc₁ : v₁ ∉ center G) (hc₂ : v₂ ∉ center G)
    (hc₁₂ : v₁ * v₂ ∉ center G)
    (hγ : gammaAct (ShapeGenS13.conjOn (zpowers v₁ ⊔ zpowers v₂)) = ⊤) :
    centralizer ({v₁} : Set G) ⊔ centralizer ({v₂} : Set G) ⊔ centralizer ({v₁ * v₂} : Set G) =
      ⊤ := by
  set E : Subgroup G := zpowers v₁ ⊔ zpowers v₂ with hE
  have h₁1 : v₁ ≠ 1 := fun h => hc₁ (h ▸ Subgroup.one_mem _)
  have h₂1 : v₂ ≠ 1 := fun h => hc₂ (h ▸ Subgroup.one_mem _)
  have hne : v₁ ≠ v₂ := fun h => hc₁₂ (by rw [h, h₂]; exact Subgroup.one_mem _)
  have hEel := isElementaryAbelian_four h₁ h₂ h₁₂
  have hrank : pRank 2 ↥E = 2 := by
    have h1 := WeakSigGen.card_eq_two_pow_pRank hEel
    rw [card_four h₁ h₂ h₁₂ h₁1 h₂1 hne] at h1
    have h2 : 2 ^ pRank 2 ↥E = 2 ^ 2 := by rw [← h1]; norm_num
    exact Nat.pow_right_injective (le_refl 2) h2
  have hnc : ∀ E' : Subgroup ↥E, pRank 2 ↥E - 1 ≤ pRank 2 ↥E' → ∃ b ∈ E', (b : G) ∉ center G := by
    intro E' hE'
    obtain ⟨b, hbE', hb1⟩ := ShapeGenS13.exists_ne_one_of_one_le_pRank (E := E') (by omega)
    refine ⟨b, hbE', ?_⟩
    rcases mem_four h₁ h₂ h₁₂ b.2 with h | h | h | h
    · exact absurd (Subtype.ext h) hb1
    · rw [h]; exact hc₁
    · rw [h]; exact hc₂
    · rw [h]; exact hc₁₂
  have hsup := ShapeGenS13.shapeGen_of_gammaAct hnc hγ
  refine eq_top_iff.2 (hsup.symm.le.trans ?_)
  refine iSup₂_le fun b hb => ?_
  obtain ⟨hbE, hbZ⟩ := hb
  rcases mem_four h₁ h₂ h₁₂ hbE with rfl | rfl | rfl | rfl
  · exact absurd (Subgroup.one_mem _) hbZ
  · exact le_sup_left.trans le_sup_left
  · exact le_sup_right.trans le_sup_left
  · exact le_sup_right

end Four

theorem sup_centralizer_eq_top_sl4 {F : Type} [Field F] [Finite F] (hF : ringChar F ≠ 2)
    {v₁ v₂ : SL(4, F)} (h₁ : v₁ * v₁ = 1) (h₂ : v₂ * v₂ = 1) (h₁₂ : v₁ * v₂ = v₂ * v₁)
    (hc₁ : v₁ ∉ center SL(4, F)) (hc₂ : v₂ ∉ center SL(4, F))
    (hc₁₂ : v₁ * v₂ ∉ center SL(4, F)) :
    centralizer ({v₁} : Set SL(4, F)) ⊔ centralizer ({v₂} : Set SL(4, F)) ⊔
      centralizer ({v₁ * v₂} : Set SL(4, F)) = ⊤ := by
  set E : Subgroup SL(4, F) := zpowers v₁ ⊔ zpowers v₂ with hE
  have hEel := isElementaryAbelian_four h₁ h₂ h₁₂
  refine sup_centralizer_eq_top_of_gammaAct h₁ h₂ h₁₂ hc₁ hc₂ hc₁₂ ?_
  refine GenLocL4Inner.gammaAct_of_commuting_squares hF hEel (ShapeGenS13.conjOn E)
    (fun a => Matrix.SpecialLinearGroup.toGL (a : SL(4, F))) (fun a g => rfl) ?_ ?_
  · intro a b
    rw [← map_mul, ← map_mul]
    congr 1
    exact (WeakSigGen.forall_of_isElementaryAbelian hEel).1 _ a.2 _ b.2
  · intro a
    refine ⟨1, one_ne_zero, ?_⟩
    have ha : (a : SL(4, F)) * a = 1 :=
      congrArg Subtype.val (WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hEel a)
    have h1 := congrArg (fun z : SL(4, F) => (z : Matrix (Fin 4) (Fin 4) F)) ha
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] at h1
    rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, h1, mul_one, one_smul]

theorem sup_centralizer_eq_top_su4 {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2) {v₁ v₂ : ↥(StatedSU 4 (p ^ f) K)}
    (h₁ : v₁ * v₁ = 1) (h₂ : v₂ * v₂ = 1) (h₁₂ : v₁ * v₂ = v₂ * v₁)
    (hc₁ : v₁ ∉ center ↥(StatedSU 4 (p ^ f) K)) (hc₂ : v₂ ∉ center ↥(StatedSU 4 (p ^ f) K))
    (hc₁₂ : v₁ * v₂ ∉ center ↥(StatedSU 4 (p ^ f) K)) :
    centralizer ({v₁} : Set ↥(StatedSU 4 (p ^ f) K)) ⊔
        centralizer ({v₂} : Set ↥(StatedSU 4 (p ^ f) K)) ⊔
      centralizer ({v₁ * v₂} : Set ↥(StatedSU 4 (p ^ f) K)) = ⊤ := by
  have h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K :=
    GenLocDiagU.unitaryFieldData_of_card hp hK
  set E : Subgroup ↥(StatedSU 4 (p ^ f) K) := zpowers v₁ ⊔ zpowers v₂ with hE
  have hEel := isElementaryAbelian_four h₁ h₂ h₁₂
  refine sup_centralizer_eq_top_of_gammaAct h₁ h₂ h₁₂ hc₁ hc₂ hc₁₂ ?_
  refine GenLocU4Basic.gammaAct_su4_of_commuting_squares hp hp2 hK hEel (ShapeGenS13.conjOn E)
    (fun a => (((a : ↥(StatedSU 4 (p ^ f) K)) : GL (Fin 4) K))) ?_ (fun a g => rfl) ?_ ?_
  · intro a
    have h1 := (CFSG.ClassicalGroups.UnitaryFlag.mem_unitarySU_iff h).1
      (a : ↥(StatedSU 4 (p ^ f) K)).2
    unfold GenLocU4Basic.IsUnitaryU
    convert h1.2 using 3
    ext i j
    simp [CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.bar_apply]
  · intro a b
    have hab : (a : ↥(StatedSU 4 (p ^ f) K)) * b = b * a :=
      (WeakSigGen.forall_of_isElementaryAbelian hEel).1 _ a.2 _ b.2
    exact congrArg (fun z : ↥(StatedSU 4 (p ^ f) K) => (z : GL (Fin 4) K)) hab
  · intro a
    refine ⟨1, one_pow _, ?_⟩
    have ha : (a : ↥(StatedSU 4 (p ^ f) K)) * a = 1 :=
      congrArg Subtype.val (WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hEel a)
    have h2 := congrArg
      (fun z : ↥(StatedSU 4 (p ^ f) K) => ((z : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) ha
    simpa using h2

end CFSG.GH74.Generic.BProg.B2.T4.PGV
