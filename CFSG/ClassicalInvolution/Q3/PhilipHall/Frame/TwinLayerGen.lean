module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf9Lie
public import CFSG.ClassicalInvolution.Asc77.AscMuTabNonab

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinLayerGen

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc


section Gen

variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)} {n : ℕ}

theorem transitive_of_twin_nbr (h4 : Thm4RTwinBelow 3 n) (hlt : Nat.card X < n)
    (hS : Q8Section X Φ) (hno : NoExit X Φ) {A A' : Subgroup X} (hA : A ∈ Φ) (hA' : A' ∈ Φ)
    {z : X} (hzA : IsUniqueInvolution A z) (hzA' : IsUniqueInvolution A' z)
    (hnb : ∀ M ∈ Φ, M ∈ omegaNbr Φ A → M = A')
    (hnb' : ∀ M ∈ Φ, M ∈ omegaNbr Φ A' → M = A) :
    ∀ K ∈ Φ, ∀ L ∈ Φ, ∃ g : X, conjSub g K = L := by
  have h4' := h4 X hlt Φ hS.hyp hS.two hS.q8 hS.aEmpty hS.oddFree
  have hcA : ∀ M ∈ Φ, (¬ ∃ g : X, conjSub g A = M) → M = A' := by
    intro M hM hnot
    have hMA : M ≠ A := fun h => hnot ⟨1, by rw [conjSub_one, h]⟩
    exact hnb M hM (MuTab.mem_omegaNbr_of_commutes hM hMA (h4' A hA M hM hnot))
  have hcA' : ∀ M ∈ Φ, (¬ ∃ g : X, conjSub g A' = M) → M = A := by
    intro M hM hnot
    have hMA : M ≠ A' := fun h => hnot ⟨1, by rw [conjSub_one, h]⟩
    exact hnb' M hM (MuTab.mem_omegaNbr_of_commutes hM hMA (h4' A' hA' M hM hnot))
  have hAA' : ∃ g : X, conjSub g A = A' := by
    by_contra hnot
    have hall : ∀ M ∈ Φ, M = A ∨ M = A' := by
      intro M hM
      by_cases hM1 : ∃ g : X, conjSub g A = M
      · left
        obtain ⟨g, hg⟩ := hM1
        refine hcA' M hM ?_
        rintro ⟨g', hg'⟩
        exact hnot ⟨g'⁻¹ * g, by rw [conjSub_mul, hg, ← hg', conjSub_inv_conjSub]⟩
      · right
        exact hcA M hM hM1
    have hcz : ∀ L ∈ Φ, L ≤ Subgroup.centralizer ({z} : Set X) := by
      intro L hL x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      have key : ∀ {J : Subgroup X}, IsUniqueInvolution J z → x ∈ J → x * z = z * x := by
        intro J hJ hxJ
        have := hJ.conj_eq (conjSub_eq_self_of_mem hxJ)
        calc x * z = (x * z * x⁻¹) * x := by group
          _ = z * x := by rw [this]
      rcases hall L hL with rfl | rfl
      · exact key hzA hx
      · exact key hzA' hx
    have hzC : (⊤ : Subgroup X) ≤ Subgroup.centralizer ({z} : Set X) := by
      rw [← hS.gen]
      exact iSup₂_le hcz
    have hcentral : ∀ g : X, g * z * g⁻¹ = z := by
      intro g
      have := Subgroup.mem_centralizer_singleton_iff.mp (hzC (Subgroup.mem_top g))
      calc g * z * g⁻¹ = (g * z) * g⁻¹ := rfl
        _ = (z * g) * g⁻¹ := by rw [this]
        _ = z := by group
    refine (hno A hA z hzA).2.1 ⟨Subgroup.zpowers z, ⟨fun a ha g => ?_⟩, ?_, Subgroup.mem_zpowers z⟩
    · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      rw [← conj_zpow, hcentral g]
      exact Subgroup.zpow_mem_zpowers z k
    · exact CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hzA.sq
  have hcl : ∀ M ∈ Φ, ∃ g : X, conjSub g A = M := by
    intro M hM
    by_cases h : ∃ g : X, conjSub g A = M
    · exact h
    · obtain ⟨g, hg⟩ := hAA'
      exact ⟨g, hg.trans (hcA M hM h).symm⟩
  intro K hK L hL
  obtain ⟨x, hx⟩ := hcl K hK
  obtain ⟨y, hy⟩ := hcl L hL
  exact ⟨y * x⁻¹, by rw [conjSub_mul, ← hx, conjSub_inv_conjSub, hy]⟩

theorem closure_of_twin_nbr (h4 : Thm4RTwinBelow 3 n) (hlt : Nat.card X < n)
    (hS : Q8Section X Φ) (hno : NoExit X Φ) {A A' : Subgroup X} (hA : A ∈ Φ) (hA' : A' ∈ Φ)
    {z : X} (hzA : IsUniqueInvolution A z) (hzA' : IsUniqueInvolution A' z)
    (hnb : ∀ M ∈ Φ, M ∈ omegaNbr Φ A → M = A')
    (hnb' : ∀ M ∈ Φ, M ∈ omegaNbr Φ A' → M = A) :
    ∀ M ∈ Φ, M ≤ ⨆ x : X, conjSub x A := by
  intro M hM
  obtain ⟨g, rfl⟩ := transitive_of_twin_nbr h4 hlt hS hno hA hA' hzA hzA' hnb hnb' A hA M hM
  exact le_iSup (fun x : X => conjSub x A) g

end Gen

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinLayerGen
