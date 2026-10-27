module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic.Basic
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeAbstract
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public noncomputable section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.AGLEmbedding.ParabPrime (perfectJoin perfectJoin_le perfectJoin_perfect le_perfectJoin)
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic
open scoped commutatorElement

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Solvable

variable {G S : Type*} [Group G] [Group S]

theorem map_perfectJoin_eq_one [Group.IsSolvable S] {J : Subgroup G} (f : ↥J →* S) {v : G}
    (hv : v ∈ perfectJoin J) : ∃ hvJ : v ∈ J, f ⟨v, hvJ⟩ = 1 := by
  have hvJ : v ∈ J := perfectJoin_le J hv
  refine ⟨hvJ, ?_⟩
  set P : Subgroup ↥J := (perfectJoin J).subgroupOf J with hP
  have hPmap : P.map J.subtype = perfectJoin J :=
    Subgroup.map_subgroupOf_eq_of_le (perfectJoin_le J)
  have hPP : ⁅P, P⁆ = P := by
    apply Subgroup.map_injective J.subtype_injective
    rw [Subgroup.map_commutator, hPmap, perfectJoin_perfect]
  set H : Subgroup S := P.map f with hH
  have hHH : ⁅H, H⁆ = H := by
    rw [hH, ← Subgroup.map_commutator, hPP]
  have hbot : H = ⊥ := by
    by_contra hne
    exact (Group.IsSolvable.commutator_lt_of_ne_bot hne).ne hHH
  have hvP : (⟨v, hvJ⟩ : ↥J) ∈ P := hv
  have : f ⟨v, hvJ⟩ ∈ H := Subgroup.mem_map_of_mem _ hvP
  rwa [hbot, Subgroup.mem_bot] at this

end Solvable

section Section

variable {r : ℕ}

@[expose] def secLin (A B : Submodule (ZMod 2) (Fin r ⊕ Fin r → ZMod 2))
    (g : StatedSp r (ZMod 2)) (hA : ∀ x ∈ A, spMat g *ᵥ x ∈ A)
    (hB : ∀ x ∈ B, spMat g *ᵥ x ∈ B) :
    (↥B ⧸ A.comap B.subtype) →ₗ[ZMod 2] (↥B ⧸ A.comap B.subtype) :=
  Submodule.mapQ _ _ ((Matrix.mulVecLin (spMat g)).restrict hB) (fun x hx => hA x.1 hx)

theorem secLin_mk (A B : Submodule (ZMod 2) (Fin r ⊕ Fin r → ZMod 2))
    (g : StatedSp r (ZMod 2)) (hA : ∀ x ∈ A, spMat g *ᵥ x ∈ A)
    (hB : ∀ x ∈ B, spMat g *ᵥ x ∈ B) (x : ↥B) :
    secLin A B g hA hB (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ⟨spMat g *ᵥ x.1, hB x.1 x.2⟩ := rfl

@[expose] def secPerm (A B : Submodule (ZMod 2) (Fin r ⊕ Fin r → ZMod 2))
    (J : Subgroup (StatedSp r (ZMod 2))) (hA : ∀ g ∈ J, ∀ x ∈ A, spMat g *ᵥ x ∈ A)
    (hB : ∀ g ∈ J, ∀ x ∈ B, spMat g *ᵥ x ∈ B) :
    ↥J →* Equiv.Perm (↥B ⧸ A.comap B.subtype) :=
  MonoidHom.mk'
    (fun g =>
      { toFun := secLin A B g.1 (hA g g.2) (hB g g.2)
        invFun := secLin A B g.1⁻¹ (hA _ (J.inv_mem g.2)) (hB _ (J.inv_mem g.2))
        left_inv := fun q => by
          induction q using Submodule.Quotient.induction_on with
          | H x =>
            simp only [secLin_mk, Matrix.mulVec_mulVec, spMat_inv_mul, Matrix.one_mulVec]
        right_inv := fun q => by
          induction q using Submodule.Quotient.induction_on with
          | H x =>
            simp only [secLin_mk, Matrix.mulVec_mulVec, spMat_mul_inv, Matrix.one_mulVec] })
    (fun g h => by
      ext q
      induction q using Submodule.Quotient.induction_on with
      | H x =>
        simp only [Equiv.Perm.mul_apply, Equiv.coe_fn_mk, secLin_mk, Subgroup.coe_mul,
          spMat_mul, Matrix.mulVec_mulVec])

theorem section_trivial (A B : Submodule (ZMod 2) (Fin r ⊕ Fin r → ZMod 2))
    (J : Subgroup (StatedSp r (ZMod 2))) (hA : ∀ g ∈ J, ∀ x ∈ A, spMat g *ᵥ x ∈ A)
    (hB : ∀ g ∈ J, ∀ x ∈ B, spMat g *ᵥ x ∈ B)
    (hcard : Nat.card (↥B ⧸ A.comap B.subtype) ≤ 4) {v : StatedSp r (ZMod 2)}
    (hv : v ∈ perfectJoin J) : ∀ x ∈ B, spMat v *ᵥ x - x ∈ A := by
  have hfin : Finite (↥B ⧸ A.comap B.subtype) :=
    Finite.of_surjective (Submodule.Quotient.mk (p := A.comap B.subtype))
      (Submodule.Quotient.mk_surjective _)
  have hsol : Group.IsSolvable (Equiv.Perm (↥B ⧸ A.comap B.subtype)) :=
    Equiv.Perm.isSolvable hcard
  obtain ⟨hvJ, h1⟩ := map_perfectJoin_eq_one (secPerm A B J hA hB) hv
  intro x hx
  have h2 := congrArg (fun p => p (Submodule.Quotient.mk ⟨x, hx⟩)) h1
  simp only [secPerm, MonoidHom.mk'_apply, Equiv.coe_fn_mk, secLin_mk, Equiv.Perm.coe_one,
    id_eq] at h2
  rw [Submodule.Quotient.eq] at h2
  exact h2

end Section

end CFSG.HardMathSupport.Curtis.UnitaryLevi
