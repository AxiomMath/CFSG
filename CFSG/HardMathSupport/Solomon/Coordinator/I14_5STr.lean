module

public import CFSG.LocalAnalysis.GLTheoremB.PCompLift
public import CFSG.HardMathSupport.Solomon.Proving.LBLayerConj
public import CFSG.LocalAnalysis.GLTheoremB.PCompBasics

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

section Map

variable {G G' : Type*} [Group G] [Group G'] [Finite G]

theorem i145s_primeCoreOf_map {p : ℕ} (hp : p.Prime) (ψ : G →* G') (A : Subgroup G)
    (hker : Nat.Coprime p (Nat.card ↥(A ⊓ ψ.ker))) :
    (GLAPPrimeCoreOf p A).map ψ = GLAPPrimeCoreOf p (A.map ψ) := by
  unfold GLAPPrimeCoreOf
  rw [← glaPPrimeCore_map_subgroupMap hp ψ A hker, Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem i145s_layer_map {p : ℕ} (hp : p.Prime) (ψ : G →* G') {A : Subgroup G}
    (hker : Nat.Coprime p (Nat.card ↥(A ⊓ ψ.ker))) :
    GLAPLayer p (A.map ψ) = (GLAPLayer p A).map ψ := by
  refine le_antisymm ?_ ?_
  · refine sSup_le fun K' hK' => ?_
    obtain ⟨K, hK, rfl⟩ := exists_glaPComponent_map_eq hp ψ hker hK'
    exact Subgroup.map_mono (le_sSup hK)
  · rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun K hK => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_sSup (glaPComponent_map hp ψ hker hK)

theorem i145s_bad_map {p : ℕ} (hp : p.Prime) (ψ : G →* G') (A : Subgroup G)
    (hker : Nat.Coprime p (Nat.card ↥(A ⊓ ψ.ker))) :
    ⁅GLAPLayer p (A.map ψ), GLAPPrimeCoreOf p (A.map ψ)⁆ =
      (⁅GLAPLayer p A, GLAPPrimeCoreOf p A⁆).map ψ := by
  rw [i145s_layer_map hp ψ hker, ← i145s_primeCoreOf_map hp ψ A hker, Subgroup.map_commutator]

end Map

section Gen

variable {G G' : Type} [Group G] [Group G'] [Finite G] [Finite G']

theorem i145s_map_bad_le {p : ℕ} (hp : p.Prime) (ψ : G →* G') {D : Subgroup G} {E : Subgroup G'}
    (hDE : D.map ψ ≤ E) (hn : ((D.map ψ).subgroupOf E).Normal)
    (hcomp : ∀ J, GLAPComponent p D J → GLAPComponent p (D.map ψ) (J.map ψ)) :
    (⁅GLAPLayer p D, GLAPPrimeCoreOf p D⁆).map ψ ≤
      ⁅GLAPLayer p E, GLAPPrimeCoreOf p E⁆ := by
  rw [Subgroup.map_commutator]
  refine Subgroup.commutator_mono ?_ ?_
  · rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun J hJ => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_sSup (CFSG.HardMathSupport.Solomon.Proving.glaPComponent_of_normal_overgroup hp hDE
      hn (hcomp J hJ))
  ·
    have hSD : (GLAPPrimeCoreOf p D).map ψ ≤ D.map ψ :=
      Subgroup.map_mono (CFSG.HardMathSupport.Timmesfeld.Proving.GLAPPrimeCoreOf_le D)
    have hS : ∀ g ∈ D.map ψ, ∀ x ∈ (GLAPPrimeCoreOf p D).map ψ,
        g * x * g⁻¹ ∈ (GLAPPrimeCoreOf p D).map ψ := by
      rintro _ ⟨d, hd, rfl⟩ _ ⟨w, hw, rfl⟩
      exact ⟨d * w * d⁻¹,
        CFSG.HardMathSupport.Timmesfeld.Proving.GLAPPrimeCoreOf_conj_mem d hd w hw, by simp⟩
    have hcop : Nat.Coprime p (Nat.card ((GLAPPrimeCoreOf p D).map ψ)) :=
      (CFSG.HardMathSupport.Timmesfeld.Proving.coprime_card_GLAPPrimeCoreOf hp D).coprime_dvd_right
        (Subgroup.card_map_dvd _ ψ)
    have h1 : (GLAPPrimeCoreOf p D).map ψ ≤ GLAPPrimeCoreOf p (D.map ψ) :=
      CFSG.HardMathSupport.Timmesfeld.Proving.le_GLAPPrimeCoreOf_of_normal hSD hS hcop
    have hsub : IsSubnormal (D.map ψ) E := IsSubnormal.step hDE hn (IsSubnormal.refl E)
    have h2 := glaPPrimeCoreOf_inf_eq_of_isSubnormal hp hsub
    exact h1.trans (h2.symm.le.trans inf_le_right)

end Gen

end CFSG.HardMathSupport.Solomon.Coordinator
