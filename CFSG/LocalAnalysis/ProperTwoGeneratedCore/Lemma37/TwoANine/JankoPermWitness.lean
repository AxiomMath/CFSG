module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoPermMaximal
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoTypesWitness

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoPerm

open Equiv Subgroup
open Janko (Ebar Fbar sbar₁ ebar₂ ebar₃)

theorem gens_subset_Ebar : ({sbar₁, ebar₂, ebar₃} : Set (alternatingGroup (Fin 9))) ⊆ Ebar :=
  subset_closure

theorem exists_mem_Ebar_apply_ne (i : Fin 9) : ∃ g ∈ Ebar, (g : Perm (Fin 9)) i ≠ i := by
  have h1 := gens_subset_Ebar (by simp : sbar₁ ∈ ({sbar₁, ebar₂, ebar₃} : Set _))
  have h2 := gens_subset_Ebar (by simp : ebar₂ ∈ ({sbar₁, ebar₂, ebar₃} : Set _))
  have h3 := gens_subset_Ebar (by simp : ebar₃ ∈ ({sbar₁, ebar₂, ebar₃} : Set _))
  fin_cases i
  · exact ⟨_, h1, by decide⟩
  · exact ⟨_, h1, by decide⟩
  · exact ⟨_, h1, by decide⟩
  · exact ⟨_, h2, by decide⟩
  · exact ⟨_, h2, by decide⟩
  · exact ⟨_, h2, by decide⟩
  · exact ⟨_, h3, by decide⟩
  · exact ⟨_, h3, by decide⟩
  · exact ⟨_, h3, by decide⟩

theorem Ebar_le_centralizer :
    Ebar ≤ centralizer ({sbar₁, ebar₂, ebar₃} : Set (alternatingGroup (Fin 9))) := by
  rw [Ebar, closure_le]
  intro x hx
  rw [SetLike.mem_coe, mem_centralizer_iff]
  intro y hy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
    exact Subtype.ext (by decide)

theorem apply_apply_eq_of_commute {g c : Perm (Fin 9)} (h : g * c = c * g) {x : Fin 9}
    (hx : g x = x) : g (c x) = c x := by
  rw [← Perm.mul_apply, h, Perm.mul_apply, hx]

theorem eq_one_of_mem_Ebar {g : alternatingGroup (Fin 9)} (hg : g ∈ Ebar)
    (h0 : (g : Perm (Fin 9)) 0 = 0) (h3 : (g : Perm (Fin 9)) 3 = 3)
    (h6 : (g : Perm (Fin 9)) 6 = 6) : g = 1 := by
  have hc := mem_centralizer_iff.mp (Ebar_le_centralizer hg)
  have c1 : (g : Perm (Fin 9)) * sbar₁ = sbar₁ * g :=
    congrArg Subtype.val (hc sbar₁ (by simp)).symm
  have c2 : (g : Perm (Fin 9)) * ebar₂ = ebar₂ * g :=
    congrArg Subtype.val (hc ebar₂ (by simp)).symm
  have c3 : (g : Perm (Fin 9)) * ebar₃ = ebar₃ * g :=
    congrArg Subtype.val (hc ebar₃ (by simp)).symm
  have h1 := apply_apply_eq_of_commute c1 h0
  have h2 := apply_apply_eq_of_commute c1 h1
  have h4 := apply_apply_eq_of_commute c2 h3
  have h5 := apply_apply_eq_of_commute c2 h4
  have h7 := apply_apply_eq_of_commute c3 h6
  have h8 := apply_apply_eq_of_commute c3 h7
  have e : ((sbar₁ : Perm (Fin 9)) 0 = 1 ∧ (sbar₁ : Perm (Fin 9)) 1 = 2) ∧
      ((ebar₂ : Perm (Fin 9)) 3 = 4 ∧ (ebar₂ : Perm (Fin 9)) 4 = 5) ∧
      ((ebar₃ : Perm (Fin 9)) 6 = 7 ∧ (ebar₃ : Perm (Fin 9)) 7 = 8) := by decide
  rw [e.1.1] at h1 h2
  rw [e.1.2] at h2
  rw [e.2.1.1] at h4 h5
  rw [e.2.1.2] at h5
  rw [e.2.2.1] at h7 h8
  rw [e.2.2.2] at h8
  refine Subtype.ext (Equiv.ext fun i => ?_)
  fin_cases i <;> assumption

theorem apply_mem_of_mem_Ebar {g : alternatingGroup (Fin 9)} (hg : g ∈ Ebar) :
    ((g : Perm (Fin 9)) 0, (g : Perm (Fin 9)) 3, (g : Perm (Fin 9)) 6) ∈
      ({0, 1, 2} ×ˢ {3, 4, 5} ×ˢ {6, 7, 8} : Finset (Fin 9 × Fin 9 × Fin 9)) := by
  have hc := mem_centralizer_iff.mp (Ebar_le_centralizer hg)
  have hmove : ∀ c ∈ ({sbar₁, ebar₂, ebar₃} : Set (alternatingGroup (Fin 9))), ∀ x : Fin 9,
      (c : Perm (Fin 9)) x ≠ x →
        (c : Perm (Fin 9)) ((g : Perm (Fin 9)) x) ≠ (g : Perm (Fin 9)) x := by
    intro c hcm x hx h
    have hgc : (c : Perm (Fin 9)) ((g : Perm (Fin 9)) x) =
        (g : Perm (Fin 9)) ((c : Perm (Fin 9)) x) := by
      rw [← Perm.mul_apply, ← Perm.mul_apply]
      exact congrFun (congrArg DFunLike.coe (congrArg Subtype.val (hc c hcm))) x
    exact hx ((g : Perm (Fin 9)).injective (hgc.symm.trans h))
  have k1 := hmove sbar₁ (by simp) 0 (by decide)
  have k2 := hmove ebar₂ (by simp) 3 (by decide)
  have k3 := hmove ebar₃ (by simp) 6 (by decide)
  have s1 : ∀ x, (sbar₁ : Perm (Fin 9)) x ≠ x → x ∈ ({0, 1, 2} : Finset (Fin 9)) := by decide
  have s2 : ∀ x, (ebar₂ : Perm (Fin 9)) x ≠ x → x ∈ ({3, 4, 5} : Finset (Fin 9)) := by decide
  have s3 : ∀ x, (ebar₃ : Perm (Fin 9)) x ≠ x → x ∈ ({6, 7, 8} : Finset (Fin 9)) := by decide
  exact Finset.mem_product.mpr ⟨s1 _ k1, Finset.mem_product.mpr ⟨s2 _ k2, s3 _ k3⟩⟩

theorem card_Ebar : Nat.card Ebar = 27 := by
  apply le_antisymm
  · let S : Finset (Fin 9 × Fin 9 × Fin 9) := {0, 1, 2} ×ˢ {3, 4, 5} ×ˢ {6, 7, 8}
    let f : Ebar → S := fun g => ⟨_, apply_mem_of_mem_Ebar g.2⟩
    have hf : Function.Injective f := by
      intro g h hgh
      simp only [f, Subtype.mk.injEq, Prod.mk.injEq] at hgh
      obtain ⟨h0, h3, h6⟩ := hgh
      have hk := eq_one_of_mem_Ebar (g := (g : alternatingGroup (Fin 9))⁻¹ * h)
        (mul_mem (inv_mem g.2) h.2)
        (by rw [coe_mul, Perm.mul_apply, ← h0, coe_inv]; exact Perm.inv_eq_iff_eq.mpr rfl)
        (by rw [coe_mul, Perm.mul_apply, ← h3, coe_inv]; exact Perm.inv_eq_iff_eq.mpr rfl)
        (by rw [coe_mul, Perm.mul_apply, ← h6, coe_inv]; exact Perm.inv_eq_iff_eq.mpr rfl)
      exact Subtype.ext (inv_mul_eq_one.mp hk)
    calc Nat.card Ebar ≤ Nat.card S := Nat.card_le_card_of_injective f hf
      _ = 27 := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]; rfl
  · let ψ : Fin 3 × Fin 3 × Fin 3 → Ebar := fun v =>
      ⟨sbar₁ ^ (v.1 : ℕ) * ebar₂ ^ (v.2.1 : ℕ) * ebar₃ ^ (v.2.2 : ℕ),
        mul_mem (mul_mem (pow_mem (gens_subset_Ebar (by simp)) _)
          (pow_mem (gens_subset_Ebar (by simp)) _)) (pow_mem (gens_subset_Ebar (by simp)) _)⟩
    have hval : ∀ v : Fin 3 × Fin 3 × Fin 3,
        (((sbar₁ : Perm (Fin 9)) ^ (v.1 : ℕ) * (ebar₂ : Perm (Fin 9)) ^ (v.2.1 : ℕ) *
          (ebar₃ : Perm (Fin 9)) ^ (v.2.2 : ℕ)) (0 : Fin 9) : ℕ) = v.1 ∧
        (((sbar₁ : Perm (Fin 9)) ^ (v.1 : ℕ) * (ebar₂ : Perm (Fin 9)) ^ (v.2.1 : ℕ) *
          (ebar₃ : Perm (Fin 9)) ^ (v.2.2 : ℕ)) (3 : Fin 9) : ℕ) = v.2.1 + 3 ∧
        (((sbar₁ : Perm (Fin 9)) ^ (v.1 : ℕ) * (ebar₂ : Perm (Fin 9)) ^ (v.2.1 : ℕ) *
          (ebar₃ : Perm (Fin 9)) ^ (v.2.2 : ℕ)) (6 : Fin 9) : ℕ) = v.2.2 + 6 := by decide
    have hψ : Function.Injective ψ := by
      intro v w hvw
      have h := congrArg (fun g : Ebar => (g : Perm (Fin 9))) hvw
      simp only [ψ, coe_mul, coe_pow] at h
      have h0 := congrArg Fin.val (DFunLike.congr_fun h (0 : Fin 9))
      have h3 := congrArg Fin.val (DFunLike.congr_fun h (3 : Fin 9))
      have h6 := congrArg Fin.val (DFunLike.congr_fun h (6 : Fin 9))
      rw [(hval v).1, (hval w).1] at h0
      rw [(hval v).2.1, (hval w).2.1] at h3
      rw [(hval v).2.2, (hval w).2.2] at h6
      obtain ⟨v1, v2, v3⟩ := v
      obtain ⟨w1, w2, w3⟩ := w
      revert h0 h3 h6
      revert v1 v2 v3 w1 w2 w3
      decide
    calc 27 = Nat.card (Fin 3 × Fin 3 × Fin 3) := by simp
      _ ≤ Nat.card Ebar := Nat.card_le_card_of_injective ψ hψ

theorem le_normalizer_Ebar_of_odd {Y : Subgroup (alternatingGroup (Fin 9))}
    (hY : Odd (Nat.card Y)) (hEY : Ebar ≤ Y) :
    Y ≤ normalizer (Ebar : Set (alternatingGroup (Fin 9))) :=
  le_normalizer_of_odd_alt card_Ebar exists_mem_Ebar_apply_ne hY hEY

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoPerm
