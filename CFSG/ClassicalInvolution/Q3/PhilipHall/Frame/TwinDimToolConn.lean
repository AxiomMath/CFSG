module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.LiftTransfer
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscData
public import CFSG.ClassicalInvolution.Q3.Q3T7P25B00

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDimTool

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Q3.Q3NL


section Conn

variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem not_dConnected_liftFam (hΩ : HypOmegaGen Φ) (h2 : ∀ J ∈ Φ, IsPGroup 2 J) (hl : HasLifts Φ)
    (hex : ExactSylow Φ) {A₀ A₀' B₀ : Subgroup X} (hA₀ : A₀ ∈ Φ) (hA₀' : A₀' ∈ Φ) (hB₀ : B₀ ∈ Φ)
    (hnb : ∀ M ∈ Φ, M ∈ omegaNbr Φ A₀ → M = A₀')
    (hnb' : ∀ M ∈ Φ, M ∈ omegaNbr Φ A₀' → M = A₀) (hBA : B₀ ≠ A₀) (hBA' : B₀ ≠ A₀') :
    ¬ DConnected (liftFam Φ) := by
  intro hconn
  have hΛ : HypOmegaModU (.sl2 3 1) (liftFam Φ) := hypOmegaModU_liftFam hΩ.conjInvariant
  obtain ⟨LA, uA, hLA⟩ := hl A₀ hA₀
  obtain ⟨LA', uA', hLA'⟩ := hl A₀' hA₀'
  obtain ⟨LB, uB, hLB⟩ := hl B₀ hB₀
  have hMA := satU_mem_liftFam hA₀ hLA
  have hMA' := satU_mem_liftFam hA₀' hLA'
  have hMB := satU_mem_liftFam hB₀ hLB
  have hsymm : ∀ {M N : Subgroup X}, M ∈ liftFam Φ → N ∈ liftFam Φ →
      dAdj (liftFam Φ) M N → N ∈ omegaNbr (liftFam Φ) M := by
    intro M N hM hN hadj
    rcases hadj with h | h
    · exact h
    · exact Q3CL.T3.omegaNbr_symm (Q3T8.Asc77.l6_2) hΛ hN hM h
  have hpath : ∀ N, Relation.ReflTransGen (fun M N : Subgroup X =>
      N ∈ liftFam Φ ∧ dAdj (liftFam Φ) M N) (satU (.sl2 3 1) LA uA) N →
      N = satU (.sl2 3 1) LA uA ∨ N = satU (.sl2 3 1) LA' uA' := by
    intro N hN
    induction hN with
    | refl => exact Or.inl rfl
    | tail hpre hstep ih =>
      rename_i M N'
      obtain ⟨hN'Φ, hadj⟩ := hstep
      have hMΦ : M ∈ liftFam Φ := by
        rcases ih with rfl | rfl
        · exact hMA
        · exact hMA'
      have hnbr := hsymm hMΦ hN'Φ hadj
      obtain ⟨J, hJΦ, hJN⟩ := exists_core_of_mem_liftFam hN'Φ
      rcases ih with rfl | rfl
      · have hJ := (hex.mem_omegaNbr_liftFam_iff hΩ h2 hl hMA hA₀ hLA.le_sat hN'Φ hJΦ hJN).mp hnbr
        have hJeq := hnb J hJΦ hJ
        subst hJeq
        exact Or.inr (liftFam_eq_of_le hΩ hN'Φ hMA' hJΦ hJN hLA'.le_sat)
      · have hJ := (hex.mem_omegaNbr_liftFam_iff hΩ h2 hl hMA' hA₀' hLA'.le_sat hN'Φ hJΦ hJN).mp
          hnbr
        have hJeq := hnb' J hJΦ hJ
        subst hJeq
        exact Or.inl (liftFam_eq_of_le hΩ hN'Φ hMA hJΦ hJN hLA.le_sat)
  rcases hpath _ (hconn _ hMA _ hMB) with h | h
  · exact hBA (hex.core_unique hΩ h2 hMA hB₀ hA₀ (h ▸ hLB.le_sat) hLA.le_sat)
  · exact hBA' (hex.core_unique hΩ h2 hMA' hB₀ hA₀' (h ▸ hLB.le_sat) hLA'.le_sat)

end Conn

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDimTool
