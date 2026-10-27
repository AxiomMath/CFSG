module

public import CFSG.GH74.GLS.Stage2.Local.P27.FullStmt
import CFSG.LocalAnalysis.ComponentInitial.QTNQRLinearUnitaryOuterDerivedLinear
import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.GH74.GLS.Stage2.Local.P27

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12

@[expose] def OutAbel (X : Type) [Group X] : Prop :=
  ∀ σ τ : MulAut X, ∃ j : X, σ * τ * σ⁻¹ * τ⁻¹ = MulAut.conj j

theorem OutAbel.of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (h : OutAbel X) :
    OutAbel Y := by
  intro σ τ
  obtain ⟨j, hj⟩ := h (MulAut.congr e.symm σ) (MulAut.congr e.symm τ)
  refine ⟨e j, ?_⟩
  have h1 := congrArg (MulAut.congr e) hj
  have h2 : ∀ ρ : MulAut Y, MulAut.congr e (MulAut.congr e.symm ρ) = ρ := fun ρ => by
    ext y
    simp
  simp only [map_mul, map_inv, h2] at h1
  rw [h1]
  ext y
  simp

theorem outAbel_psl2 (F : Type) [Field F] [Finite F] : OutAbel (CFSG.GorensteinWalter.PSL2 F) := by
  intro σ τ
  have h := CFSG.LocalAnalysis.ComponentInitial.OuterDerived.outer_psl2_mul_comm F
    (σ : CFSG.ComponentClassification.OuterAutomorphisms.Outer (CFSG.GorensteinWalter.PSL2 F)) τ
  have h1 : ((σ * τ * σ⁻¹ * τ⁻¹ : MulAut (CFSG.GorensteinWalter.PSL2 F)) :
      CFSG.ComponentClassification.OuterAutomorphisms.Outer (CFSG.GorensteinWalter.PSL2 F)) =
        1 := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_inv, h]
    group
  obtain ⟨j, hj⟩ := (QuotientGroup.eq_one_iff _).mp h1
  exact ⟨j, hj.symm⟩

theorem outAbel_of_isL2 {X : Type} [Group X] {P : ℕ → Prop} (h : IVK.IsL2 X P) : OutAbel X := by
  obtain ⟨F, _, _, -, ⟨e⟩⟩ := h
  exact OutAbel.of_mulEquiv (e.trans (IVK.L2.equivPSL F)).symm (outAbel_psl2 F)

theorem outAbel_alternatingGroup_seven : OutAbel (alternatingGroup (Fin 7)) := by
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7
    (by norm_num) (by norm_num)
  intro σ τ
  obtain ⟨s, rfl⟩ := hbij.2 σ
  obtain ⟨t, rfl⟩ := hbij.2 τ
  have hc : s * t * s⁻¹ * t⁻¹ ∈ alternatingGroup (Fin 7) := by
    rw [Equiv.Perm.mem_alternatingGroup]
    simp only [map_mul, map_inv]
    rw [mul_comm (Equiv.Perm.sign s) (Equiv.Perm.sign t)]
    group
  refine ⟨⟨_, hc⟩, ?_⟩
  rw [← MulAut.conjNormal_val (h := ⟨_, hc⟩)]
  simp only [map_mul, map_inv]

theorem outAbel_of_alt7 {X : Type} [Group X] (e : X ≃* alternatingGroup (Fin 7)) : OutAbel X :=
  OutAbel.of_mulEquiv e.symm outAbel_alternatingGroup_seven

theorem outAbel_of_fullCL4 {G : Type} [Group G] [Finite G] {x : G} {q : ℕ} (h : FullCL4 x q) :
    OutAbel (↥(Jx x) ⧸ pPrimeCore 2 ↥(Jx x)) := by
  rcases h with h | ⟨-, ⟨e⟩⟩
  · exact outAbel_of_isL2 h
  · exact outAbel_of_alt7 e

end CFSG.GH74.GLS.Stage2.Local.P27
