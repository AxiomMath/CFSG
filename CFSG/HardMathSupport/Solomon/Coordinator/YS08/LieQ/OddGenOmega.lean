module

public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.OddGenForm
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.OddOmega
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailModelTransport

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ

open CFSG.Open CFSG.LieType.BorelTits CFSG.GH74.GLS.Stage2.OddAut CFSG.Assembly.LowTwoRank
  CFSG.ClassicalGroups.Orthogonal
  CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel
  CFSG.ComponentClassification.CatalogueBOrthogonalPointAction


section Omega

variable {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F] [Finite F] {q : ℕ} [Fact q.Prime]
  [CharP F q]

theorem subspStab_natRep_eq_derived (Q0 : (ι → F) → F) (W : Submodule F (ι → F)) :
    subspStab (natRep (StatedOmega Q0)) W = statedDerivedSubspaceStabilizer Q0 W := by
  ext g
  rw [mem_subspStab, mem_statedDerivedSubspaceStabilizer]
  have happ : ∀ (h : StatedOmega Q0) (v : ι → F),
      (toLinEquiv ι F h.val).toLinearMap v = natRep (StatedOmega Q0) h v := fun h v => by
    rw [natRep_apply]
    rfl
  constructor
  · rintro hg
    refine le_antisymm ?_ ?_
    · rintro _ ⟨v, hv, rfl⟩
      rw [happ]
      exact (hg v hv).1
    · intro v hv
      refine ⟨natRep (StatedOmega Q0) g⁻¹ v, (hg v hv).2, ?_⟩
      rw [happ, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  · intro hg v hv
    have hfw : ∀ v ∈ W, natRep (StatedOmega Q0) g v ∈ W := by
      intro v hv
      have : natRep (StatedOmega Q0) g v ∈ W.map (toLinEquiv ι F g.val).toLinearMap :=
        ⟨v, hv, happ g v⟩
      rwa [hg] at this
    refine ⟨hfw v hv, ?_⟩
    have hv' : v ∈ W.map (toLinEquiv ι F g.val).toLinearMap := by rw [hg]; exact hv
    obtain ⟨w, hw, hwv⟩ := hv'
    rw [happ] at hwv
    rw [← hwv, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    exact hw

theorem twoParabolics_Omega (Φ : QuadForm F (ι → F)) (hι : 6 ≤ Fintype.card ι)
    {x₁ x₂ : ι → F} (hx₁0 : x₁ ≠ 0) (hQ₁ : Φ.Q x₁ = 0) (hQ₂ : Φ.Q x₂ = 0)
    (h12 : Φ.polar.β x₁ x₂ = 0) (hind : x₂ ∉ Submodule.span F {x₁})
    (U : Sylow q (StatedProj (StatedOmega Φ.Q)))
    (hc : IsCoatom (statedProjectiveSubspaceStabilizer Φ.Q (Submodule.span F {x₁})))
    (hU₁ : (U : Subgroup (StatedProj (StatedOmega Φ.Q))) ≤
      statedProjectiveSubspaceStabilizer Φ.Q (Submodule.span F {x₁}))
    (hU₂ : (U : Subgroup (StatedProj (StatedOmega Φ.Q))) ≤
      statedProjectiveSubspaceStabilizer Φ.Q (Submodule.span F {x₁} ⊔ Submodule.span F {x₂})) :
    TwoParabolics q (StatedProj (StatedOmega Φ.Q)) := by
  have hι5 : 5 ≤ Fintype.card ι := by omega
  have h11 : Φ.polar.β x₁ x₁ = 0 := by rw [Φ.polar_self, hQ₁, mul_zero]
  have h22 : Φ.polar.β x₂ x₂ = 0 := by rw [Φ.polar_self, hQ₂, mul_zero]
  have hmap : ∀ W : Submodule F (ι → F),
      (subspStab (natRep (StatedOmega Φ.Q)) W).map
        (QuotientGroup.mk' ((StatedScalars ι F).subgroupOf (StatedOmega Φ.Q))) =
      statedProjectiveSubspaceStabilizer Φ.Q W := fun W => by
    rw [subspStab_natRep_eq_derived]
    exact statedDerivedSubspaceStabilizer_map Φ.Q W
  exact twoParabolics_of_form Φ.polar (natRep (StatedOmega Φ.Q)) (natRep_injective _)
    (isIsometric_natRep_statedOmega Φ) ((StatedScalars ι F).subgroupOf (StatedOmega Φ.Q))
    (fun z hz => exists_smul_of_mem_scalars (g := z) hz) (-1) (neg_ne_zero.2 one_ne_zero)
    (fun v => Φ.Q v = 0) (ea1_Omega Φ hι5) hx₁0 hQ₁ hQ₂ h11 h22 h12 hind U hc
    (le_of_eq (hmap _).symm) hU₁ (by rw [hmap]; exact hU₂)

theorem stabilizer_line_ne_top (Φ : QuadForm F (ι → F)) (hι : 6 ≤ Fintype.card ι)
    {x₁ x₂ : ι → F} (hx₁0 : x₁ ≠ 0) (hQ₂ : Φ.Q x₂ = 0) (h12 : Φ.polar.β x₁ x₂ = 0)
    (hind : x₂ ∉ Submodule.span F {x₁}) :
    statedProjectiveSubspaceStabilizer Φ.Q (Submodule.span F {x₁}) ≠ ⊤ := by
  have hι5 : 5 ≤ Fintype.card ι := by omega
  rw [← statedDerivedSubspaceStabilizer_map, ← subspStab_natRep_eq_derived]
  exact map_subspStab_ne_top Φ.polar (natRep (StatedOmega Φ.Q))
    ((StatedScalars ι F).subgroupOf (StatedOmega Φ.Q))
    (fun z hz => exists_smul_of_mem_scalars (g := z) hz) (-1) (neg_ne_zero.2 one_ne_zero)
    (fun v => Φ.Q v = 0) (ea1_Omega Φ hι5) hx₁0 hQ₂ (Φ.polar.refl _ _ h12) hind

theorem twoParabolics_Omega_of_borel (Φ : QuadForm F (ι → F)) (hι : 6 ≤ Fintype.card ι) {r : ℕ}
    (Fl : Fin r → Submodule F (ι → F))
    (hBI : CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail.BorelInterface q Φ.Q Fl) (i₀ i₁ : Fin r) (hi₀ : (i₀ : ℕ) = 0) (hi₁ : (i₁ : ℕ) = 1)
    {x₁ x₂ : ι → F} (hx₁0 : x₁ ≠ 0) (hind : x₂ ∉ Submodule.span F {x₁})
    (h₀ : Fl i₀ = Submodule.span F {x₁})
    (h₁ : Fl i₁ = Submodule.span F {x₁} ⊔ Submodule.span F {x₂}) :
    TwoParabolics q (StatedProj (StatedOmega Φ.Q)) := by
  obtain ⟨hdim, ⟨U, hU⟩, -, hmax, hidx⟩ := hBI
  have hx₁mem : x₁ ∈ Fl i₀ := by rw [h₀]; exact Submodule.mem_span_singleton_self x₁
  have hx₂mem : x₂ ∈ Fl i₁ := by
    rw [h₁]; exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self x₂)
  have hx₁₂mem : x₁ + x₂ ∈ Fl i₁ := by
    rw [h₁]
    exact add_mem (Submodule.mem_sup_left (Submodule.mem_span_singleton_self x₁))
      (Submodule.mem_sup_right (Submodule.mem_span_singleton_self x₂))
  have hQ₁ : Φ.Q x₁ = 0 := (hdim i₀).1 x₁ hx₁mem
  have hQ₂ : Φ.Q x₂ = 0 := (hdim i₁).1 x₂ hx₂mem
  have hQ₁₂ : Φ.Q (x₁ + x₂) = 0 := (hdim i₁).1 _ hx₁₂mem
  have h12 : Φ.polar.β x₁ x₂ = 0 := by
    have := Φ.Q_add x₁ x₂
    rw [hQ₁₂, hQ₁, hQ₂] at this
    linear_combination -this
  have hflag : ∀ i, statedProjectiveFlagStabilizer Φ.Q Fl ≤
      statedProjectiveSubspaceStabilizer Φ.Q (Fl i) := fun i => iInf_le _ i
  have hUle : (U : Subgroup (StatedProj (StatedOmega Φ.Q))) ≤
      statedProjectiveFlagStabilizer Φ.Q Fl := by
    rw [hU]
    exact Subgroup.le_normalizer
  have hP₀ : IsCoatom (statedProjectiveSubspaceStabilizer Φ.Q (Fl i₀)) := by
    refine isCoatom_of_overgroups (hflag i₀) ?_ ?_
    · rw [h₀]
      exact stabilizer_line_ne_top Φ hι hx₁0 hQ₂ h12 hind
    · intro M hM hBM hPM
      obtain ⟨i, rfl⟩ := hmax M hM hBM
      by_contra hne
      have hi : i ≠ i₀ := fun h => hne (h ▸ rfl)
      have hlt := hidx (Fl i) (Fl i₀) (hdim i).1 (by
        have := (hdim i).2
        have h0 : (i : ℕ) ≠ 0 := fun h => hi (Fin.ext (by omega))
        omega) (hdim i₀).1 (by rw [(hdim i₀).2, hi₀])
      have hle := index_le_of_le hPM
      omega
  rw [h₀] at hP₀
  have hU₁ := hUle.trans (hflag i₀)
  have hU₂ := hUle.trans (hflag i₁)
  rw [h₀] at hU₁
  rw [h₁] at hU₂
  exact twoParabolics_Omega Φ hι hx₁0 hQ₁ hQ₂ h12 hind U hP₀ hU₁ hU₂


end Omega

end CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ
