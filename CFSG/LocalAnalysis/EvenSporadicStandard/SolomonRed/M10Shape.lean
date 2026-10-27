module

public import CFSG.LocalAnalysis.EvenSporadicStandard.SolomonRed.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.Basic

public section

namespace CFSG.EvenSporadicStandard.SolomonRed

open Subgroup
open scoped commutatorElement

variable {D : Type*} [Group D]

theorem commutator_eq_self_of_simple {B : Subgroup D} (hB : IsSimpleGroup ↥B)
    (hnab : ∃ a ∈ B, ∃ b ∈ B, a * b ≠ b * a) : ⁅B, B⁆ = B := by
  have h1 : commutator ↥B = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator ↥B) with h | h
    · exfalso
      obtain ⟨a, ha, b, hb, hab⟩ := hnab
      apply hab
      have h2 : ⁅(⟨a, ha⟩ : ↥B), (⟨b, hb⟩ : ↥B)⁆ ∈ commutator ↥B :=
        Subgroup.commutator_mem_commutator (mem_top _) (mem_top _)
      rw [h, mem_bot, commutatorElement_eq_one_iff_mul_comm] at h2
      exact congrArg Subtype.val h2
    · exact h
  rw [← map_subtype_commutator, h1, Subgroup.map_top, range_subtype]

theorem commutator_mul_central_left {a b z : D} (h : ∀ x, x * z = z * x) :
    ⁅a * z, b⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  have hz : z * b * z⁻¹ = b := by rw [← h b]; group
  calc a * z * b * (a * z)⁻¹ * b⁻¹ = a * (z * b * z⁻¹) * a⁻¹ * b⁻¹ := by group
    _ = a * b * a⁻¹ * b⁻¹ := by rw [hz]

theorem commutator_mul_central_right {a b z : D} (h : ∀ x, x * z = z * x) :
    ⁅a, b * z⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  have hz : z * a⁻¹ * z⁻¹ = a⁻¹ := by rw [← h a⁻¹]; group
  calc a * (b * z) * a⁻¹ * (b * z)⁻¹ = a * b * (z * a⁻¹ * z⁻¹) * b⁻¹ := by group
    _ = a * b * a⁻¹ * b⁻¹ := by rw [hz]

variable {c : D} {A : Subgroup D}

theorem central_of_mem_zpowers (hcc : ∀ x, x * c = c * x) {w : D} (hw : w ∈ zpowers c)
    (x : D) : x * w = w * x := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hw
  exact (Commute.zpow_right (show Commute x c from hcc x) k).eq

theorem zpowers_le_centralizer_of_central (hcc : ∀ x, x * c = c * x) :
    zpowers c ≤ centralizer (A : Set D) := by
  intro w hw
  rw [mem_centralizer_iff]
  intro a _
  exact central_of_mem_zpowers hcc hw a

theorem m10_normal (hcc : ∀ x, x * c = c * x) (hA : IsSimpleGroup ↥A)
    (hnab : ∃ a ∈ A, ∃ b ∈ A, a * b ≠ b * a) (hidx : (A ⊔ zpowers c).index = 2) :
    A.Normal := by
  have hW : (A ⊔ zpowers c).Normal := normal_of_index_eq_two hidx
  have hdecomp := fun {w : D} (hw : w ∈ A ⊔ zpowers c) =>
    exists_mul_of_mem_sup_of_le_centralizer (zpowers_le_centralizer_of_central (A := A) hcc) hw
  have h1 : ⁅A ⊔ zpowers c, A ⊔ zpowers c⁆ ≤ A := by
    rw [commutator_le]
    intro w₁ hw₁ w₂ hw₂
    obtain ⟨a₁, ha₁, u₁, hu₁, rfl⟩ := hdecomp hw₁
    obtain ⟨a₂, ha₂, u₂, hu₂, rfl⟩ := hdecomp hw₂
    rw [commutator_mul_central_left (central_of_mem_zpowers hcc hu₁),
      commutator_mul_central_right (central_of_mem_zpowers hcc hu₂), commutatorElement_def]
    exact A.mul_mem (A.mul_mem (A.mul_mem ha₁ ha₂) (A.inv_mem ha₁)) (A.inv_mem ha₂)
  have h2 : A ≤ ⁅A ⊔ zpowers c, A ⊔ zpowers c⁆ :=
    calc A = ⁅A, A⁆ := (commutator_eq_self_of_simple hA hnab).symm
      _ ≤ _ := commutator_mono le_sup_left le_sup_left
  have h3 : ⁅A ⊔ zpowers c, A ⊔ zpowers c⁆ = A := le_antisymm h1 h2
  rw [← h3]
  infer_instance

theorem m10_cent (hcc : ∀ x, x * c = c * x) (hA : IsSimpleGroup ↥A)
    (hnab : ∃ a ∈ A, ∃ b ∈ A, a * b ≠ b * a) (hidx : (A ⊔ zpowers c).index = 2)
    (hsq : ∀ h : D, h * h ∈ zpowers c → h ∈ A ⊔ zpowers c) :
    ∀ d : D, (∀ a ∈ A, d * a = a * d) → d ∈ zpowers c := by
  have hdecomp := fun {w : D} (hw : w ∈ A ⊔ zpowers c) =>
    exists_mul_of_mem_sup_of_le_centralizer (zpowers_le_centralizer_of_central (A := A) hcc) hw
  have step1 : ∀ d ∈ A ⊔ zpowers c, (∀ a ∈ A, d * a = a * d) → d ∈ zpowers c := by
    intro d hd hdc
    obtain ⟨a, ha, u, hu, rfl⟩ := hdecomp hd
    have h1 : a = 1 := by
      refine eq_one_of_commute_of_simple hA hnab ha fun b hb => ?_
      have h2 := hdc b hb
      have h3 : a * u * b = a * b * u := by
        rw [mul_assoc, ← central_of_mem_zpowers hcc hu b, mul_assoc]
      have h4 : b * (a * u) = b * a * u := by rw [mul_assoc]
      rw [h3, h4] at h2
      exact (mul_right_cancel h2).symm
    rw [h1, one_mul]
    exact hu
  intro d hdc
  by_contra hd
  have hdW : d ∉ A ⊔ zpowers c := fun h => hd (step1 d h hdc)
  have h2 : d * d ∈ A ⊔ zpowers c := mul_self_mem_of_index_two hidx d
  have h3 : d * d ∈ zpowers c := by
    refine step1 _ h2 fun a ha => ?_
    calc d * d * a = d * (d * a) := by group
      _ = d * (a * d) := by rw [hdc a ha]
      _ = (d * a) * d := by group
      _ = (a * d) * d := by rw [hdc a ha]
      _ = a * (d * d) := by group
  exact hdW (hsq d h3)

end CFSG.EvenSporadicStandard.SolomonRed
