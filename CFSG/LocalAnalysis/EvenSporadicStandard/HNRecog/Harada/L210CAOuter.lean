module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup CFSG.Open

variable {X : Type} [Group X]

theorem L210_card_centralizer_le_of_coset {A : Subgroup X} (hA : IsElemAbelian 2 A)
    (hcard : Nat.card A = 2 ^ 8) {i v : X} (hi : i ∈ normalizer (A : Set X))
    (hv : v ∈ normalizer (A : Set X)) (hi2 : i * i = 1) (hv2 : v * v = 1)
    (hiv : i * v⁻¹ ∈ A) (hCv : Nat.card ↥(A ⊓ centralizer ({v} : Set X)) ≤ 16) :
    Nat.card ↥(A ⊓ centralizer ({i} : Set X)) ≤ 16 := by
  have hcomm : ∀ {x y : X}, x ∈ A → y ∈ A → x * y = y * x := by
    haveI : IsMulCommutative A := hA.1
    intro x y hx hy
    simpa using congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : A) (⟨y, hy⟩ : A))
  have hi_decomp : i = (i * v⁻¹) * v := by group
  have h1 : ∀ {y : X}, y ∈ A → y * i = (i * v⁻¹) * (y * v) := by
    intro y hyA
    calc y * i = y * ((i * v⁻¹) * v) := congrArg (fun z => y * z) hi_decomp
      _ = (y * (i * v⁻¹)) * v := by group
      _ = ((i * v⁻¹) * y) * v := by rw [hcomm hyA hiv]
      _ = (i * v⁻¹) * (y * v) := by group
  have h2 : ∀ {y : X}, y ∈ A → i * y = (i * v⁻¹) * (v * y) := by
    intro y _
    calc i * y = ((i * v⁻¹) * v) * y := congrArg (fun z => z * y) hi_decomp
      _ = (i * v⁻¹) * (v * y) := by group
  have hset : A ⊓ centralizer ({i} : Set X) = A ⊓ centralizer ({v} : Set X) := by
    apply le_antisymm
    · intro y hy
      rw [Subgroup.mem_inf] at hy ⊢
      obtain ⟨hyA, hyi⟩ := hy
      refine ⟨hyA, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hyi ⊢
      have key : (i * v⁻¹) * (y * v) = (i * v⁻¹) * (v * y) := by
        rw [← h1 hyA, hyi, h2 hyA]
      exact mul_left_cancel key
    · intro y hy
      rw [Subgroup.mem_inf] at hy ⊢
      obtain ⟨hyA, hyv⟩ := hy
      refine ⟨hyA, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hyv ⊢
      rw [h1 hyA, h2 hyA, hyv]
  rw [hset]
  exact hCv

end CFSG.EvenSporadicStandard.HNRecog.Harada
