module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AGen

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

namespace S4A

variable {G : Type} [Group G] [Finite G]

theorem sq_mem_centralizer_of_four_le_card_fixed {A : Subgroup G} (hA : ∀ a ∈ A, a * a = 1)
    (hcard : Nat.card A = 8) {g : G} (hg : g ∈ normalizer (A : Set G))
    (hC : 4 ≤ Nat.card (A ⊓ centralizer ({g} : Set G) : Subgroup G)) :
    ∀ a ∈ A, a * (g * g) = g * g * a := by
  intro a₀ ha₀
  set C : Subgroup G := A ⊓ centralizer ({g} : Set G) with hCdef
  have hCA : C ≤ A := inf_le_left
  have hmem_C : ∀ c, c ∈ C ↔ c ∈ A ∧ g * c = c * g := by
    intro c
    rw [hCdef, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    simp
  have hmul := Subgroup.relIndex_mul_card (H := C) (K := A)
  rw [inf_eq_left.mpr hCA, hcard] at hmul
  have hr0 : C.relIndex A ≠ 0 := by
    intro h0
    rw [h0] at hmul
    omega
  have hr_le : C.relIndex A ≤ 2 := by
    by_contra hgt
    push Not at hgt
    have : 3 * 4 ≤ C.relIndex A * Nat.card C := Nat.mul_le_mul hgt hC
    omega
  have hr : C.relIndex A = 1 ∨ C.relIndex A = 2 := by omega
  rcases hr with hr | hr
  · have hAC : A ≤ C := Subgroup.relIndex_eq_one.mp hr
    have hcomm : g * a₀ = a₀ * g := ((hmem_C a₀).mp (hAC ha₀)).2
    calc a₀ * (g * g) = a₀ * g * g := by rw [mul_assoc]
      _ = g * a₀ * g := by rw [← hcomm]
      _ = g * (a₀ * g) := by rw [mul_assoc]
      _ = g * (g * a₀) := by rw [← hcomm]
      _ = g * g * a₀ := by rw [mul_assoc]
  · have hmem2 : ∀ {a b : G}, a ∈ A → b ∈ A → a ∈ C ∨ b ∈ C ∨ a * b ∈ C :=
      fun ha hb => mem_or_mem_or_mul_mem_of_relIndex_two hCA hr ha hb
    have hconjA : ∀ a ∈ A, g * a * g⁻¹ ∈ A := fun a ha =>
      ((Subgroup.mem_set_normalizer_iff).mp hg a).mp ha
    have hkey : ∀ a ∈ A, g * (g * a * g⁻¹) * g⁻¹ = a := by
      intro a ha
      by_cases haC : a ∈ C
      · have hga : g * a = a * g := ((hmem_C a).mp haC).2
        have h1 : g * a * g⁻¹ = a := by rw [hga]; group
        rw [h1, h1]
      · have hca : g * a * g⁻¹ ∉ C := by
          intro hc
          apply haC
          have hcg : g * (g * a * g⁻¹) = (g * a * g⁻¹) * g := ((hmem_C _).mp hc).2
          have h1 : g * a * g⁻¹ = a := by
            calc g * a * g⁻¹ = g⁻¹ * (g * (g * a * g⁻¹)) := by group
              _ = g⁻¹ * ((g * a * g⁻¹) * g) := by rw [hcg]
              _ = a := by group
          rw [← h1]
          exact hc
        have hk : a⁻¹ * (g * a * g⁻¹) ∈ C := by
          rcases hmem2 (A.inv_mem ha) (hconjA a ha) with h1 | h1 | h1
          · exact absurd (by simpa using C.inv_mem h1) haC
          · exact absurd h1 hca
          · exact h1
        obtain ⟨k, hkdef⟩ : ∃ k, k = a⁻¹ * (g * a * g⁻¹) := ⟨_, rfl⟩
        rw [← hkdef] at hk
        have hkA : k ∈ A := hCA hk
        have hkg : g * k = k * g := ((hmem_C k).mp hk).2
        have hk2 : k * k = 1 := hA k hkA
        have hca_eq : g * a * g⁻¹ = a * k := by rw [hkdef]; group
        calc g * (g * a * g⁻¹) * g⁻¹ = g * (a * k) * g⁻¹ := by rw [hca_eq]
          _ = (g * a * g⁻¹) * (g * k * g⁻¹) := by group
          _ = (a * k) * k := by rw [hca_eq, hkg]; group
          _ = a := by rw [mul_assoc, hk2, mul_one]
    have h1 := hkey a₀ ha₀
    calc a₀ * (g * g) = (g * (g * a₀ * g⁻¹) * g⁻¹) * (g * g) := by rw [h1]
      _ = g * g * a₀ := by group

theorem card_le_two_mul_inf_of_sq_dihedral {V W B : Subgroup G} (hBV : B ≤ V)
    (φ : ↥V →* DihedralGroup 4) (hker : φ.ker = W.subgroupOf V)
    (hsq : ∀ b ∈ B, ∃ v ∈ V, b = v * v) :
    Nat.card B ≤ 2 * Nat.card (B ⊓ W : Subgroup G) := by
  have hsqD : ∀ x : DihedralGroup 4, x * x = 1 ∨ x * x = DihedralGroup.r 2 := by decide
  have hkerW : ∀ (v : G) (hv : v ∈ V), φ ⟨v, hv⟩ = 1 → v ∈ W := by
    intro v hv h1
    have hmem : (⟨v, hv⟩ : ↥V) ∈ φ.ker := h1
    rw [hker] at hmem
    exact Subgroup.mem_subgroupOf.mp hmem
  have hsq' : ∀ (b : G) (hb : b ∈ B),
      φ ⟨b, hBV hb⟩ = 1 ∨ φ ⟨b, hBV hb⟩ = DihedralGroup.r 2 := by
    intro b hb
    obtain ⟨v, hv, rfl⟩ := hsq b hb
    have hm : φ ⟨v * v, hBV hb⟩ = φ ⟨v, hv⟩ * φ ⟨v, hv⟩ := by
      rw [← map_mul]
      rfl
    rw [hm]
    exact hsqD _
  have hidx : (B ⊓ W).relIndex B ≤ 2 := by
    by_cases hex : ∃ (a : G) (ha : a ∈ B), φ ⟨a, hBV ha⟩ = DihedralGroup.r 2
    · obtain ⟨a, ha, haφ⟩ := hex
      refine relIndex_le_two_of_forall inf_le_left a ha ?_
      intro n hn
      rcases hsq' n hn with h1 | h1
      · exact Or.inl (Subgroup.mem_inf.mpr ⟨hn, hkerW n (hBV hn) h1⟩)
      · refine Or.inr (Subgroup.mem_inf.mpr ⟨B.mul_mem (B.inv_mem ha) hn, ?_⟩)
        refine hkerW _ (hBV (B.mul_mem (B.inv_mem ha) hn)) ?_
        have hm : φ ⟨a⁻¹ * n, hBV (B.mul_mem (B.inv_mem ha) hn)⟩ =
            (φ ⟨a, hBV ha⟩)⁻¹ * φ ⟨n, hBV hn⟩ := by
          rw [← map_inv, ← map_mul]
          rfl
        rw [hm, haφ, h1]
        exact inv_mul_cancel _
    · push Not at hex
      have hBW : B ≤ W := fun b hb =>
        hkerW b (hBV hb) ((hsq' b hb).resolve_right (hex b hb))
      have : (B ⊓ W) = B := inf_eq_left.mpr hBW
      rw [this, Subgroup.relIndex_self]
      norm_num
  have hmul := Subgroup.relIndex_mul_card (H := B ⊓ W) (K := B)
  rw [inf_eq_left.mpr (inf_le_left : B ⊓ W ≤ B)] at hmul
  calc Nat.card B = (B ⊓ W).relIndex B * Nat.card (B ⊓ W : Subgroup G) := hmul.symm
    _ ≤ 2 * Nat.card (B ⊓ W : Subgroup G) := Nat.mul_le_mul_right _ hidx

end S4A

end CFSG.OddStandard.SmallF3.HarrisU33
