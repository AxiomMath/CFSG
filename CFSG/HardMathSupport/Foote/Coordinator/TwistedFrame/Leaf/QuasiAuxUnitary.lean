module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.QuasiAuxBridge
public import CFSG.RankThree.PartOne.KF4.A2Frame
public import CFSG.RankThree.PartOne.KE.SLnFamily
public import CFSG.RankThree.PartOne.KE.SLnShape

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KF4
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Chevalley
open scoped MatrixGroups

set_option linter.unusedSectionVars false


namespace LangLevi

variable {τ : Tag} {K : Type} [Field K] [Finite K] {w : WeylGroup τ} (D : LangLevi τ K w)

theorem isQuasisimple_fixedRoot_unitary {ν : ℕ} (hν : 3 ≤ ν) (hq2 : ν ≠ 3 ∨ 2 < Nat.card K)
    {S : Set (Fin τ.rank → ℤ)} (hS : ∀ r ∈ S, IsRoot τ r)
    (ρ : SL(ν, D.L) →* ModGL τ D.L) (hρinj : Function.Injective ρ)
    (hrange : ρ.range = rootSpan τ D.L S)
    (htor : ∀ b : Fin τ.rank → (D.L)ˣ, ∃ d : Fin ν → (D.L)ˣ, ∀ A : SL(ν, D.L),
      rootDiagUnit τ b * ρ A * (rootDiagUnit τ b)⁻¹ = ρ (conjDiagn d A))
    (hdiag : ∀ A : SL(ν, D.L), (∀ i j, i ≠ j → (A : Matrix (Fin ν) (Fin ν) D.L) i j = 0) →
      ρ A ∈ torusGroup τ D.L)
    (r : Fin ν → Fin ν → (Fin τ.rank → ℤ)) (hrS : ∀ i j, i ≠ j → IsRoot τ (r i j))
    (ε : Fin ν → Fin ν → (D.L)ˣ)
    (hgen : ∀ (i j : Fin ν) (hij : i ≠ j) (t : D.L),
      ρ (Matrix.SpecialLinearGroup.transvection hij t) =
        pinnedX τ D.L (r i j) ((ε i j : D.L) * t))
    (π : Equiv.Perm (Fin ν)) (hπ : ∀ i j, i ≠ j → w • r i j = r (π j) (π i)) :
    CFSG.IsQuasisimple ↥(D.fixedRoot S) := by
  classical
  haveI : IsAlgClosed D.L := IsAlgClosure.isAlgClosed K
  obtain ⟨p, hpK⟩ := CharP.exists K
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨m, hpp, hcard⟩ := FiniteField.card K p
  haveI : Fact p.Prime := ⟨hpp⟩
  have hcard' : Nat.card K = p ^ (m : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  have hFr : ∀ c, D.Fr c = c ^ (p ^ (m : ℕ)) := fun c => by rw [D.hFr, hcard']
  have hnm : D.nW ∈ monomialSubgroup τ D.L := canonicalRep_mem_monomialSubgroup D.L w
  have hconj : ∀ i j : Fin ν, i ≠ j → ∃ b : (D.L)ˣ, ∀ c : D.L,
      D.nW * pinnedX τ D.L (r i j) c * D.nW⁻¹ =
        pinnedX τ D.L (r (π j) (π i)) ((b : D.L) * c) := by
    intro i j hij
    obtain ⟨μ, hμ⟩ := monomial_conj_pinnedX hnm (hrS i j hij)
    refine ⟨μ, fun c => ?_⟩
    rw [hμ c, weylQuotientHom_eq (mapsRootLines_canonicalRep w), hπ i j hij]
  obtain ⟨Φ', hΦ', b, hshape⟩ := exists_aut_of_rootData_n (τ := τ) (ν := ν) ρ hρinj r ε hgen
    D.Fr D.Fr_bijective D.nW (fun i j => (π j, π i))
    (fun i j hij => (π.injective.ne hij).symm)
    (fun i j hij => ⟨π.symm j, π.symm i, (π.symm.injective.ne hij).symm, by simp⟩) hconj
  have hshape' : ∀ (i j : Fin ν) (hij : i ≠ j) (t : D.L),
      ((Φ' (Matrix.SpecialLinearGroup.transvection hij t) : SL(ν, D.L)) :
        Matrix (Fin ν) (Fin ν) D.L) =
        1 + Matrix.single (π j) (π i) ((b i j : D.L) * t ^ p ^ (m : ℕ)) :=
    fun i j hij t => by rw [hshape i j hij t, hFr]
  have hq2' : ν ≠ 3 ∨ 2 < p ^ (m : ℕ) := by rw [← hcard']; exact hq2
  obtain ⟨P, hP, hP1, -⟩ := an_family_unitary hpp m.pos hcard' hq2' hν hS ρ hρinj hrange htor
    hdiag D.Fr D.nW Φ' hΦ' π b hshape'
  have hheq : P () = D.fixedRoot S := by
    rw [hP1, hrange]
    rfl
  rw [← hheq]
  exact hP.2.1 ()

theorem isQuasisimple_fixedRoot_A2Frame (hK : 3 ≤ Nat.card K) {S : Set (Fin τ.rank → ℤ)}
    {ρ : SL(3, D.L) →* ModGL τ D.L} {σ : Fin 3 → Fin 3 → Fin τ.rank → ℤ} (h : IsA2Frame ρ σ)
    (hS : S = {r | ∃ i j : Fin 3, i ≠ j ∧ r = σ i j})
    (π : Equiv.Perm (Fin 3)) (hπ : ∀ i j, i ≠ j → w • σ i j = σ (π j) (π i)) :
    CFSG.IsQuasisimple ↥(D.fixedRoot S) := by
  choose! ε hε using h.transv
  subst hS
  refine D.isQuasisimple_fixedRoot_unitary (ν := 3) le_rfl (Or.inr (by omega))
    (fun r ⟨i, j, hij, hr⟩ => hr ▸ h.isRoot i j hij) ρ h.injective h.range
    (fun b => ⟨fun i => rootChar b (σ i 0), fun A => h.torus b A⟩) h.diag σ
    (fun i j hij => h.isRoot i j hij) ε (fun i j hij t => hε i j hij t) π hπ

end LangLevi

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
