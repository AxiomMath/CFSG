module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888LSC
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888LSD
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888LSE

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem l515S_sq_of_orderOf_two {d : G} (hd : orderOf d = 2) : d * d = 1 := by
  rw [← pow_two, ← hd, pow_orderOf_eq_one]

theorem l515S_ne_one_of_orderOf_two {d : G} (hd : orderOf d = 2) : d ≠ 1 := by
  rintro rfl
  rw [orderOf_one] at hd
  omega

section Reduced

variable [Finite G] {t : G} {L S : Subgroup G} {z r : G} {B A K₁ K₂ : Subgroup G} {h : G}

theorem l515S_reduced (h36 : Asc82Lemma36) (h37 : Asc82Lemma37) (h514 : Asc82Lemma514)
    (h52a : Asc82Lemma52a) (hM1 : Asc82FactRhoStar)
    (c : Sec5HCtx G t L S z r B A K₁ K₂ h) {i i' j j' : Fin 4}
    (hi : (i = 0 ∧ i' = 1) ∨ (i = 1 ∧ i' = 0)) (hj : (j = 2 ∧ j' = 3) ∨ (j = 3 ∧ j' = 2))
    {α β : G} (hα : α ∈ Kfam5 K₁ K₂ h i) (hβ : β ∈ Kfam5 K₁ K₂ h j) (hα2 : α * α = z)
    (hβ2 : β * β = z) (hdt : (α * β) * t = t * (α * β))
    (hds : (α * β) * (h⁻¹ * t * h) = (h⁻¹ * t * h) * (α * β)) (hβt : β * t = t * β)
    (hαs : α * (h⁻¹ * t * h) = (h⁻¹ * t * h) * α) :
    ∃ I : Subgroup G, IsComponentIn I (centralizer ({α * β} : Set G)) ∧ InFStar I ∧
      (InF I ∨ IsL3Eps3 I) ∧ Kfam5 K₁ K₂ h i' ≤ I ∧ Kfam5 K₁ K₂ h j' ≤ I ∧
      LieModel ↥(layerCent L (α * β)) .PSU 3 3 1 ∧ layerCent L (α * β) ≤ I ∧
      LieModel ↥(layerCent (CFSG.conjugate L h) (α * β)) .PSU 3 3 1 ∧
      layerCent (CFSG.conjugate L h) (α * β) ≤ I := by
  have hq : Sec5B517Quad (Kfam5 K₁ K₂ h) z := sec5b517_quad h514 c
  obtain ⟨hij, -, -, -, -, -⟩ := l515S_idx hi hj
  have hK0 : Kfam5 K₁ K₂ h 0 = K₁ := by simp [Kfam5]
  have hK1 : Kfam5 K₁ K₂ h 1 = K₂ := by simp [Kfam5]
  have hK2 : Kfam5 K₁ K₂ h 2 = CFSG.conjugate K₁ h := by simp [Kfam5]
  have hK3 : Kfam5 K₁ K₂ h 3 = CFSG.conjugate K₂ h := by simp [Kfam5]
  have hβα : β * α = α * β := (hq.comm i j hij α hα β hβ).symm
  obtain ⟨hd2', hd1, -⟩ := hq.mul_invol hij hα hβ hα2 hβ2
  have hd2 : orderOf (α * β) = 2 := l515S_orderOf_eq_two hd2' hd1
  obtain ⟨hs2, hs1, -⟩ := l515S_s_facts h37 c
  have hs : orderOf (h⁻¹ * t * h) = 2 := l515S_orderOf_eq_two hs2 hs1
  have hj0 : j ≠ 0 ∧ j ≠ 1 := by
    rcases hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  have hi0 : i ≠ 2 ∧ i ≠ 3 := by
    rcases hi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  have hP₁ : (Kfam5 K₁ K₂ h i = K₁ ∧ Kfam5 K₁ K₂ h i' = K₂) ∨
      (Kfam5 K₁ K₂ h i = K₂ ∧ Kfam5 K₁ K₂ h i' = K₁) := by
    rcases hi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨hK0, hK1⟩
    · exact Or.inr ⟨hK1, hK0⟩
  have hwK₁ : K₁ ⊔ K₂ ≤ centralizer ({β} : Set G) := by
    refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact hq.comm 0 j hj0.1.symm x (by rw [hK0]; exact hx) β hβ
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact hq.comm 1 j hj0.2.symm x (by rw [hK1]; exact hx) β hβ
  obtain ⟨hM₁, hP₁le, hC₁⟩ := l515S_half h52a hM1 c hP₁ hα hα2 hβ2 hβt hwK₁
  have hhz : h * z = z * h := Subgroup.mem_centralizer_singleton_iff.mp c.h_z
  have c₂ : Sec5HCtx G (h⁻¹ * t * h) (CFSG.conjugate L h) (CFSG.conjugate S h) z (h⁻¹ * r * h)
      (CFSG.conjugate B h) (CFSG.conjugate A h) (CFSG.conjugate K₁ h) (CFSG.conjugate K₂ h) h := by
    have := sec5HCtx_conj c h
    rwa [l515S_conj_eq_of_comm hhz, show h⁻¹ * h * h = h by group] at this
  have hP₂ : (Kfam5 K₁ K₂ h j = CFSG.conjugate K₁ h ∧ Kfam5 K₁ K₂ h j' = CFSG.conjugate K₂ h) ∨
      (Kfam5 K₁ K₂ h j = CFSG.conjugate K₂ h ∧ Kfam5 K₁ K₂ h j' = CFSG.conjugate K₁ h) := by
    rcases hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨hK2, hK3⟩
    · exact Or.inr ⟨hK3, hK2⟩
  have hwK₂ : CFSG.conjugate K₁ h ⊔ CFSG.conjugate K₂ h ≤ centralizer ({α} : Set G) := by
    refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact hq.comm 2 i hi0.1.symm x (by rw [hK2]; exact hx) α hα
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact hq.comm 3 i hi0.2.symm x (by rw [hK3]; exact hx) α hα
  obtain ⟨hM₂, hP₂le, hC₂⟩ := l515S_half h52a hM1 c₂ hP₂ hβ hβ2 hα2 hαs hwK₂
  rw [hβα] at hM₂ hP₂le hC₂
  obtain ⟨I₁, hI₁, hF₁, hpk₁, hE₁I, huniq₁⟩ :=
    l515S_m3 h36 c.toSec5Setting.toSec3SettingLB c.involution hd2 hdt.symm hC₁ hM₁
  obtain ⟨I₂, hI₂, hF₂, -, hE₂I, -⟩ :=
    l515S_m3 h36 c.toSec5Setting.toSec3SettingLB hs hd2 hds.symm hC₂ hM₂
  have hI₂₁ : I₂ = I₁ := huniq₁ I₂ hI₂ hF₂
  rw [hI₂₁] at hE₂I
  exact ⟨I₁, hI₁, hF₁, hpk₁, hP₁le.trans hE₁I, hP₂le.trans hE₂I, hM₁, hE₁I, hM₂, hE₂I⟩

end Reduced

end CFSG.OddStandard.SmallF3.Omega
