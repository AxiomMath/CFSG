module

public import CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherGeneration
public import CFSG.RankThree.PartTwo.KFacts.AutKinds

public section

namespace CFSG.AGLEmbedding.KFactProofs.Sp62Local

open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.Assembly.LowTwoRank
open CFSG.RankThree.PartTwo.KFacts (isInnerAut_congr congr_mulAutConj IsInnerAut)

noncomputable def eProj : StatedProj (StatedSp 3 (ZMod 2)) ≃* H6 :=
  (QuotientGroup.quotientMulEquivOfEq
    CFSG.RankThree.PartTwo.Census.statedScalars_subgroupOf_sp6).trans QuotientGroup.quotientBot

theorem isInnerAut_statedProj (α : MulAut (StatedProj (StatedSp 3 (ZMod 2)))) :
    ∃ g : StatedProj (StatedSp 3 (ZMod 2)), α = MulAut.conj g := by
  obtain ⟨-, hform⟩ := automorphism_generation (K := ZMod 2) (r := 3) le_rfl
  obtain ⟨A, σ, hα⟩ := hform α
  have hσ : fieldAut 3 (ZMod 2) σ = 1 := by
    rw [show σ = 1 from Subsingleton.elim _ _, map_one]
  have hA : (A : GL (Fin 3 ⊕ Fin 3) (ZMod 2)) ∈ StatedSp 3 (ZMod 2) := by
    obtain ⟨μ, hμ⟩ := A.2
    have hμ1 : μ = 1 := Subsingleton.elim _ _
    subst hμ1
    rw [Units.val_one, one_smul] at hμ
    exact SymplecticTorusWeyl.mem_statedSp_iff.2 hμ
  refine ⟨SymplecticFlag.proj 3 (ZMod 2) ⟨A, hA⟩, ?_⟩
  rw [hα, hσ, mul_one, ← conjAut_statedSp]

theorem all_inner_H6 (α : MulAut H6) : ∃ g : H6, α = MulAut.conj g := by
  obtain ⟨g, hg⟩ := isInnerAut_statedProj (MulAut.congr eProj.symm α)
  refine ⟨eProj g, ?_⟩
  have h1 : MulAut.congr eProj (MulAut.congr eProj.symm α) = α := by
    ext x
    simp [MulAut.congr_apply]
  rw [← h1, hg, congr_mulAutConj]

theorem top_of_centralizer_eq_bot {Y : Type} [Group Y] (K : Subgroup Y) [K.Normal]
    (e : K ≃* H6) (hC : Subgroup.centralizer (K : Set Y) = ⊥) : K = ⊤ := by
  rw [eq_top_iff]
  intro y _
  obtain ⟨h, hh⟩ := all_inner_H6 (MulAut.congr e (MulAut.conjNormal (H := K) y))
  set k : K := e.symm h with hk
  have hkey : ∀ k' : K, y * k' * y⁻¹ = (k : Y) * k' * (k : Y)⁻¹ := by
    intro k'
    have h2 : e (MulAut.conjNormal (H := K) y k') = h * e k' * h⁻¹ := by
      have := congrArg (fun β : MulAut H6 => β (e k')) hh
      simpa [MulAut.congr_apply, MulAut.conj_apply] using this
    have h3 : MulAut.conjNormal (H := K) y k' = k * k' * k⁻¹ := by
      apply e.injective
      rw [h2, map_mul, map_mul, map_inv, hk, MulEquiv.apply_symm_apply]
    have h4 := congrArg Subtype.val h3
    simpa [MulAut.conjNormal_apply] using h4
  have hc : (k : Y)⁻¹ * y ∈ Subgroup.centralizer (K : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k' hk'
    have h5 : y * k' * y⁻¹ = (k : Y) * k' * (k : Y)⁻¹ := hkey ⟨k', hk'⟩
    have h4 : y * k' = (k : Y) * k' * (k : Y)⁻¹ * y := mul_inv_eq_iff_eq_mul.1 h5
    calc k' * ((k : Y)⁻¹ * y) = (k : Y)⁻¹ * ((k : Y) * k' * (k : Y)⁻¹ * y) := by group
      _ = (k : Y)⁻¹ * (y * k') := by rw [← h4]
      _ = (k : Y)⁻¹ * y * k' := by group
  rw [hC, Subgroup.mem_bot, inv_mul_eq_one] at hc
  rw [← hc]
  exact k.2

end CFSG.AGLEmbedding.KFactProofs.Sp62Local
