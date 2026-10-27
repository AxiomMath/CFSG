module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerOrthLeaf
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerGUMain

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG CFSG.Open Subgroup CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal
open Polynomial Module

section SelfDual

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type*} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

theorem oddPCoreInClosure_supportedBlock_selfDual (hx : OddOrderIsometry Q p x) (hp : p.Prime)
    (hp2 : p ≠ 2) {h : K[X]} [Fact (Irreducible h)] (hh : h ∈ primaryFactors x.toLinearMap)
    (hne1 : h ≠ X - 1) (hself : h = reciprocalPolynomial h) :
    OddPCoreInClosure p ↥(supportedBlock Q x h) := by
  classical
  have hp2' : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨d, H, hdeg, hroot, hH, hadd1, hadd2, hleft, hright, hsymm⟩ :=
    hx.exists_selfDual_hermitian hp2' hh hne1 hself
  have hirr := irreducible_of_mem_primaryFactors hh
  have hd : finrank K (AdjoinRoot h) = 2 * d := by
    rw [(AdjoinRoot.powerBasis hirr.ne_zero).finrank, AdjoinRoot.powerBasis_dim, hdeg]
  obtain ⟨ℓ, f, hU, hq, hbar⟩ := exists_unitaryFieldData K (AdjoinRoot h) hd
  have hbar' : ∀ z, frobPow K (AdjoinRoot h) d z = hU.bar z := fun z => by
    rw [hbar, frobPow_apply]
  let B : primaryComponent x.toLinearMap h →ₛₗ[hU.bar]
      primaryComponent x.toLinearMap h →ₗ[AdjoinRoot h] AdjoinRoot h :=
    LinearMap.mk₂'ₛₗ hU.bar (RingHom.id _) H hadd1
      (fun c u w => by rw [hleft, smul_eq_mul, hbar']) hadd2
      (fun c u w => by rw [hright, smul_eq_mul, RingHom.id_apply])
  have hBH : ∀ u w, B u w = H u w := fun u w => rfl
  have hBsymm : B.IsSymm := ⟨fun u w => by rw [hBH, hBH, hsymm u w, hbar']⟩
  have hBl : B.SeparatingLeft := by
    intro u hu
    refine Subtype.ext (hx.eq_zero_of_polar_selfdual hh hself u.2 fun w hw => ?_)
    have h1 := hH u ⟨w, hw⟩ 1
    rw [mul_one, one_smul] at h1
    have h2 : H u ⟨w, hw⟩ = 0 := by rw [← hBH]; exact hu _
    rw [h2, map_zero] at h1
    exact h1.symm
  have hrange : (blockGL Q x h).range = sesqUnitaryGroup B := by
    ext γ
    rw [hx.mem_range_blockGL_selfDual_iff hh hne1 hself H hH, mem_sesqUnitaryGroup]
    exact Iff.rfl
  let e₁ : ↥(supportedBlock Q x h) ≃* ↥(sesqUnitaryGroup B) :=
    (MonoidHom.ofInjective (hx.blockGL_injective hh)).trans (MulEquiv.subgroupCongr hrange)
  haveI : CharP (AdjoinRoot h) 2 := charP_of_injective_ringHom (AdjoinRoot.of h).injective 2
  have hℓ : ℓ = 2 := CharP.eq (AdjoinRoot h) hU.charP inferInstance
  haveI : Finite (AdjoinRoot h) := Module.finite_of_finite K
  exact OddPCoreInClosure.of_mulEquiv e₁.symm
    (oddPCoreInClosure_sesqUnitaryGroup hp hp2 hℓ hBsymm hBl)

end SelfDual

section Centralizer

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

theorem oddPCoreInClosure_isometryCentralizer (hx : OddOrderIsometry Q p x) (hp : p.Prime)
    (hp2 : p ≠ 2) : OddPCoreInClosure p ↥(isometryCentralizer Q x) := by
  classical
  obtain ⟨Rep, hRep⟩ := hx.exists_orbitRepresentatives
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have hprod := OddPCoreInClosure.of_noncommPiCoprod hp
    (fun i : ↥Rep => supportedBlock Q x i) (hx.blocks_commute hRep) (hx.blocks_iSupIndep hRep) ?_
  · exact OddPCoreInClosure.of_mulEquiv (MulEquiv.subgroupCongr (hx.blocks_iSup_eq hRep)) hprod
  · rintro ⟨h, hmem⟩
    have hhf : h ∈ primaryFactors x.toLinearMap := hRep.1 hmem
    haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hhf⟩
    haveI : Finite (AdjoinRoot h) := Module.finite_of_finite K
    haveI : CharP (AdjoinRoot h) 2 := charP_of_injective_ringHom (AdjoinRoot.of h).injective 2
    by_cases h1 : h = X - 1
    · subst h1
      exact OddPCoreInClosure.of_mulEquiv (fixedBlockEquiv hx).symm
        (oddPCoreInClosure_orthogonalGroup (Q.comp (fixedSpace x).subtype)
          hx.polarBilin_fixed_nondegenerate hp hp2)
    · by_cases hself : h = reciprocalPolynomial h
      · exact oddPCoreInClosure_supportedBlock_selfDual hx hp hp2 hhf h1 hself
      · exact OddPCoreInClosure.of_mulEquiv (pairedBlockEquiv hx hhf hself).symm
          (oddPCoreInClosure_generalLinearGroup hp hp2)

end Centralizer

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
