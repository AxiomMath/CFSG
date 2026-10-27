module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1CtrB

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] {A V P3 D : Subgroup G} {a₁ b₁ a₂ b₂ z : G}

theorem y7a_b1b2_notin (hrel : Y6ARel a₁ b₁ a₂ b₂ z) (hz : z ≠ 1)
    (hA32 : Nat.card ↥(closure {a₁, b₁, a₂, b₂} : Subgroup G) = 32) :
    b₁ * b₂ ∉ (closure {a₁, b₁} : Set G) ∧ b₁ * b₂ ∉ (closure {a₂, b₂} : Set G) := by
  have hUW := (y6q8_card_UW hrel hz hA32).2.2
  have hz2 : z ^ 2 = 1 := hrel.z_sq
  have hb1U : b₁ ∈ (closure {a₁, b₁} : Subgroup G) := Subgroup.subset_closure (by simp)
  have hb2W : b₂ ∈ (closure {a₂, b₂} : Subgroup G) := Subgroup.subset_closure (by simp)
  constructor
  · intro h
    have hm : b₁ * b₂ ∈ (closure {a₁, b₁} : Subgroup G) := by
      simpa only [SetLike.mem_coe] using h
    have hb2U : b₂ ∈ (closure {a₁, b₁} : Subgroup G) := by
      have h' := (closure {a₁, b₁} : Subgroup G).mul_mem
        ((closure {a₁, b₁} : Subgroup G).inv_mem hb1U) hm
      simpa using h'
    rcases (hUW b₂).mp ⟨hb2U, hb2W⟩ with h1 | h1
    · exact hz (by rw [← hrel.b2_sq, h1]; simp)
    · exact hz (by rw [← hrel.b2_sq, h1, hz2])
  · intro h
    have hm : b₁ * b₂ ∈ (closure {a₂, b₂} : Subgroup G) := by
      simpa only [SetLike.mem_coe] using h
    have hb1W : b₁ ∈ (closure {a₂, b₂} : Subgroup G) := by
      have h' := (closure {a₂, b₂} : Subgroup G).mul_mem hm
        ((closure {a₂, b₂} : Subgroup G).inv_mem hb2W)
      simpa using h'
    rcases (hUW b₁).mp ⟨hb1U, hb1W⟩ with h1 | h1
    · exact hz (by rw [← hrel.b1_sq, h1]; simp)
    · exact hz (by rw [← hrel.b1_sq, h1, hz2])

theorem y7a_inv_top (hA : A = closure {a₁, b₁, a₂, b₂}) (hrel : Y6ARel a₁ b₁ a₂ b₂ z)
    (hz : z ≠ 1) (hA32 : Nat.card ↥A = 32) (hP3z : ∀ k ∈ P3, k * z * k⁻¹ = z)
    (hU : IsOrbitMod P3 (zpowers z) ((closure {a₁, b₁} : Set G) \ (zpowers z : Set G)))
    (hW : IsOrbitMod P3 (zpowers z) ((closure {a₂, b₂} : Set G) \ (zpowers z : Set G)))
    (h9 : IsOrbitMod P3 (zpowers z) ((A : Set G) \
      ((closure {a₁, b₁} : Set G) ∪ (closure {a₂, b₂} : Set G))))
    (hVA : A ⊓ V = zpowers z) (hVc : ∀ a ∈ A, ∀ v ∈ V, a * v = v * a)
    (hVD : V ≤ D) (hDA : D ≤ A ⊔ V) (hDinv : ∀ k ∈ P3, ∀ x ∈ D, k * x * k⁻¹ ∈ D)
    (hex : ∃ x ∈ D, x ∈ A ∧ x ∉ (closure {a₁, b₁} : Set G) ∧
      x ∉ (closure {a₂, b₂} : Set G)) :
    A ≤ D := by
  have hz2 : z ^ 2 = 1 := hrel.z_sq
  have hzV : z ∈ V := by
    have h : z ∈ A ⊓ V := by
      rw [hVA]
      exact Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩
    exact h.2
  have hUA : (closure {a₁, b₁} : Subgroup G) ≤ A := by
    rw [hA]; exact y6q8_U_le_A
  have hWA : (closure {a₂, b₂} : Subgroup G) ≤ A := by
    rw [hA]; exact y6q8_W_le_A
  have hzU : z ∈ (closure {a₁, b₁} : Subgroup G) := by
    rw [← hrel.a1_sq]
    exact pow_mem (Subgroup.subset_closure (by simp)) 2
  have hzW : z ∈ (closure {a₂, b₂} : Subgroup G) := by
    rw [← hrel.a2_sq]
    exact pow_mem (Subgroup.subset_closure (by simp)) 2
  obtain ⟨x, hxD, hxA, hxU, hxW⟩ := hex
  have hxA' : x ∈ (closure {a₁, b₁, a₂, b₂} : Subgroup G) := by rw [← hA]; exact hxA
  have hxV : x ∉ V := by
    intro hxVin
    have hxZp : x ∈ Subgroup.zpowers z := by
      have h : x ∈ A ⊓ V := ⟨hxA, hxVin⟩
      rwa [hVA] at h
    exact hxU ((Subgroup.zpowers_le.mpr hzU) hxZp)
  rcases y7a_inv_UW hA hrel hz hA32 hP3z hU hW h9 hVA hVc hVD hDA hDinv
      ⟨x, hxD, hxV⟩ with hUD | hWD
  · obtain ⟨u, huU, w, hwW, hxuw⟩ := y6q8_A_elems hrel x hxA'
    have hwD : w ∈ D := by
      have h : u⁻¹ * x ∈ D := D.mul_mem (D.inv_mem (hUD huU)) hxD
      rw [hxuw] at h
      simpa using h
    have hwZp : w ∉ Subgroup.zpowers z := by
      intro hwz
      have hwU : w ∈ (closure {a₁, b₁} : Subgroup G) := (Subgroup.zpowers_le.mpr hzU) hwz
      have hx : x ∈ (closure {a₁, b₁} : Subgroup G) := by
        rw [hxuw]
        exact (closure {a₁, b₁} : Subgroup G).mul_mem huU hwU
      exact hxU hx
    have hwV : w ∉ V := by
      intro hwVin
      have h : w ∈ A ⊓ V := ⟨hWA hwW, hwVin⟩
      exact hwZp (by rwa [hVA] at h)
    have hWV : (closure {a₂, b₂} : Subgroup G) ⊓ V = zpowers z := by
      apply le_antisymm
      · intro y hy
        have h : y ∈ A ⊓ V := ⟨hWA hy.1, hy.2⟩
        rwa [hVA] at h
      · intro y hy
        exact ⟨(Subgroup.zpowers_le.mpr hzW) hy, (Subgroup.zpowers_le.mpr hzV) hy⟩
    have hWD' : (closure {a₂, b₂} : Subgroup G) ≤ D :=
      y7a_inv_W hrel hz hP3z hW hzV hVD hDinv
        (fun w' hw' v hv => hVc w' (hWA hw') v hv) hWV
        ⟨w, hwD, Subgroup.mem_sup_left hwW, hwV⟩
    rw [hA]
    refine (Subgroup.closure_le D).mpr ?_
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · exact hUD (Subgroup.subset_closure (by simp))
    · exact hUD (Subgroup.subset_closure (by simp))
    · exact hWD' (Subgroup.subset_closure (by simp))
    · exact hWD' (Subgroup.subset_closure (by simp))
  · obtain ⟨u, huU, w, hwW, hxuw⟩ := y6q8_A_elems hrel x hxA'
    have huD : u ∈ D := by
      have h : x * w⁻¹ ∈ D := D.mul_mem hxD (D.inv_mem (hWD hwW))
      rw [hxuw] at h
      simpa using h
    have huZp : u ∉ Subgroup.zpowers z := by
      intro huz
      have huW : u ∈ (closure {a₂, b₂} : Subgroup G) := (Subgroup.zpowers_le.mpr hzW) huz
      have hx : x ∈ (closure {a₂, b₂} : Subgroup G) := by
        rw [hxuw]
        exact (closure {a₂, b₂} : Subgroup G).mul_mem huW hwW
      exact hxW hx
    have huV : u ∉ V := by
      intro huVin
      have h : u ∈ A ⊓ V := ⟨hUA huU, huVin⟩
      exact huZp (by rwa [hVA] at h)
    have hUV : (closure {a₁, b₁} : Subgroup G) ⊓ V = zpowers z := by
      apply le_antisymm
      · intro y hy
        have h : y ∈ A ⊓ V := ⟨hUA hy.1, hy.2⟩
        rwa [hVA] at h
      · intro y hy
        exact ⟨(Subgroup.zpowers_le.mpr hzU) hy, (Subgroup.zpowers_le.mpr hzV) hy⟩
    have hUD' : (closure {a₁, b₁} : Subgroup G) ≤ D :=
      y7a_inv_U hrel hz hP3z hU hzV hVD hDinv
        (fun u' hu' v hv => hVc u' (hUA hu') v hv) hUV
        ⟨u, huD, Subgroup.mem_sup_left huU, huV⟩
    rw [hA]
    refine (Subgroup.closure_le D).mpr ?_
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · exact hUD' (Subgroup.subset_closure (by simp))
    · exact hUD' (Subgroup.subset_closure (by simp))
    · exact hWD (Subgroup.subset_closure (by simp))
    · exact hWD (Subgroup.subset_closure (by simp))

end CFSG.OddStandard.HigherRank.YamadaG23
