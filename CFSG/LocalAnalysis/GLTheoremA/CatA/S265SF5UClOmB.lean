module

public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent
import all CFSG.HardMathSupport.Solomon.Coordinator.LieComp.OrthInnerExport
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF5UClOmFix
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompAlgOrthogonal
import CFSG.RankThree.PartOne.S11d.LieCentralizerOrth

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265.SF5U

open Polynomial Module CFSG.Open CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.ClassicalGroups.Orthogonal
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.RankThree.Classical2 (ProjOrthDerived orthDerived)
open CFSG.LocalAnalysis.ComponentInitial (sesqSpecialUnitaryGroup)

theorem false_of_component_orthDerived_five {K : Type} [Field K] [Finite K] {f e : ℕ}
    (hK : Nat.card K = 2 ^ f) {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, Module.finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    {x : ↥(orthDerived Q)} (hx : x ^ 5 = 1) {J : Subgroup (ProjOrthDerived Q)}
    (hJ : IsComponentOf J (Subgroup.centralizer {(QuotientGroup.mk x : ProjOrthDerived Q)}))
    (hZ : Subgroup.center ↥J = ⊥) (h5 : 5 ∣ 2 ^ e + 1)
    (hcard : Nat.card J = ordTwistedA 4 (2 ^ e)) : False := by
  classical
  haveI : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hK
  have hchar : ringChar K = 2 := ringChar.eq K 2
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | hf
    · have := Finite.one_lt_card (α := K)
      rw [hK] at this
      norm_num at this
    · exact hf
  have he : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with rfl | he
    · norm_num at h5
    · exact he
  haveI : Nontrivial V := by
    obtain ⟨U, hU, -⟩ := hT
    exact Module.nontrivial_of_finrank_pos (R := K) (by have := Submodule.finrank_le U; omega)
  set ρ : ↥(orthDerived Q) →* ProjOrthDerived Q :=
    QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))
  have hρinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    exact Subtype.ext (CFSG.RankThree.PartOne.eq_one_of_mem_scalars_of_mem_orthDerived hQ g.2
      (Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff g).mp hg)))
  set xe : V ≃ₗ[K] V := (x : V ≃ₗ[K] V) with hxe
  have hx' : OddOrderIsometry Q 5 xe :=
    oddOrderIsometry_of_pow_eq_one (by norm_num) (by rw [hchar]; norm_num) hQ x hx
  have hN : Subgroup.centralizer {(QuotientGroup.mk x : ProjOrthDerived Q)} =
      centralizerImage Q xe := by
    rw [← CFSG.RankThree.PartOne.map_centralizer_eq_centralizerImage x]
    ext g
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective ((scalars K V).subgroupOf (orthDerived Q)) g
    rw [Subgroup.mem_map_iff_mem hρinj, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff, show (QuotientGroup.mk x : ProjOrthDerived Q) = ρ x
        from rfl, ← map_mul, ← map_mul, hρinj.eq_iff]
  rw [hN] at hJ
  have hSL : ∀ (m k : ℕ) (E : Type) [Field E] [Finite E], 2 ≤ m → 1 ≤ k → Nat.card E = 2 ^ k →
      (Matrix.SpecialLinearGroup (Fin m) E ≃* ↥J) → False := by
    intro m k E _ _ hm hk hE φ
    exact card_ne_ordTwistedA_four_of_sl hm hk hE he φ.toMonoidHom φ.surjective
      (by rw [(MonoidHom.ker_eq_bot_iff _).2 φ.injective]; exact bot_le) hZ hcard
  obtain ⟨h, hh, hne1, hq, hJeq⟩ | ⟨-, F, hFq, hFle, hFn, hJeq⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.KD264Lie.exists_component_dichotomy (p := 5) (by norm_num)
      (by norm_num) hQ hT (by rw [hchar]; norm_num) hx' J hJ
  ·
    haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
    have hspecΩ : specialBlock Q xe h ≤ orthDerived Q :=
      specialBlock_le_orthDerived_of_perfect hq.1
        ((specialBlock_le_isometryCentralizer h).trans (fun _ hg => (Subgroup.mem_inf.mp hg).1))
    let eJ : ↥(specialBlock Q xe h) ≃* ↥J :=
      (Subgroup.subgroupOfEquivOfLe hspecΩ).symm.trans
        ((((specialBlock Q xe h).subgroupOf (orthDerived Q)).equivMapOfInjective ρ hρinj).trans
          (MulEquiv.subgroupCongr hJeq.symm))
    have hm : 2 ≤ primaryMultiplicity xe.toLinearMap h := by
      by_contra hlt
      have h1 : primaryMultiplicity xe.toLinearMap h = 1 := by
        have := hx'.primaryMultiplicity_pos hh
        omega
      exact ne_bot_of_isQuasisimple hq (hx'.specialBlock_eq_bot_of_finrank_eq_one hh h1)
    rcases eq_or_ne h (reciprocalPolynomial h) with hself | hne
    ·
      obtain ⟨ℓ, k, hU, B, hBs, hBl, hrange⟩ :=
        CFSG.LocalAnalysis.GLTheoremA.KD264Lie.exists_selfDual_unitary_of_odd hx' (by decide) hh
          hne1 hself
      haveI := hU.finite
      haveI : Fact ℓ.Prime := ⟨hU.prime⟩
      haveI := hU.charP
      have hℓ2 : ℓ = 2 := (ringChar.eq (AdjoinRoot h) ℓ).symm.trans
        ((Algebra.ringChar_eq K (AdjoinRoot h)).symm.trans hchar)
      subst hℓ2
      let e₁ : ↥(specialBlock Q xe h) ≃* ↥(sesqSpecialUnitaryGroup B) :=
        (MonoidHom.ofInjective (hx'.specialBlockGL_injective hh)).trans
          (MulEquiv.subgroupCongr hrange)
      rcases Nat.lt_or_ge (primaryMultiplicity xe.toLinearMap h) 3 with hm3 | hm3
      ·
        obtain ⟨φ⟩ := CFSG.RankThree.Classical.nonempty_sesqSpecialUnitaryGroup_mulEquiv_SL2 hU
          hBs hBl (show primaryMultiplicity xe.toLinearMap h = 2 by omega)
        exact hSL 2 k hU.fixedField le_rfl hU.one_le hU.card_fixedField
          ((φ.symm.trans e₁.symm).trans eJ)
      ·
        obtain ⟨e₀, he₀⟩ := hU.exists_orthonormal_basis hBs hBl
        obtain ⟨e₂⟩ :=
          CFSG.RankThree.CentralLiftU.nonempty_sesqSpecialUnitaryGroup_mulEquiv_SUid hU e₀ he₀
        have hS : CFSG.LieType.Universal.Unitary.SUid hU.barEquiv
            (primaryMultiplicity xe.toLinearMap h) =
            StatedSU (primaryMultiplicity xe.toLinearMap h) (2 ^ k) (AdjoinRoot h) := by
          rw [CFSG.RankThree.CentralLiftU.barEquiv_eq_unitaryInvolution hU]
          exact CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hU.card_eq_sq _
        let e₃ : ↥J ≃* ↥(StatedSU (primaryMultiplicity xe.toLinearMap h) (2 ^ k) (AdjoinRoot h)) :=
          eJ.symm.trans (e₁.trans (e₂.trans (MulEquiv.subgroupCongr hS)))
        refine card_statedSU_ne_ordTwistedA_four hm3 hU.one_le hU.card_eq_sq ?_ h5 ?_
        · rw [← Subgroup.map_center_eq e₃, hZ, Subgroup.map_bot]
        · rw [← hcard]
          exact Nat.card_congr e₃.symm.toEquiv
    ·
      let bb : Module.Basis (Fin (primaryMultiplicity xe.toLinearMap h)) (AdjoinRoot h)
          (primaryComponent xe.toLinearMap h) := Module.finBasisOfFinrankEq _ _ rfl
      let eSL : ↥(specialBlock Q xe h) ≃*
          Matrix.SpecialLinearGroup (Fin (primaryMultiplicity xe.toLinearMap h)) (AdjoinRoot h) :=
        (MulEquiv.ofBijective (specialToSL Q xe h)
          ⟨hx'.specialToSL_injective hh, hx'.specialToSL_surjective_paired hh hne⟩).trans
          (Matrix.SpecialLinearGroup.toLin_equiv bb).symm
      haveI : Finite (AdjoinRoot h) := Module.finite_of_finite K
      exact hSL _ (f * h.natDegree) (AdjoinRoot h) hm
        (Nat.mul_pos hf (Fact.out : Irreducible h).natDegree_pos)
        (by rw [CFSG.RankThree.PartOne.KCLinPlane.natCard_adjoinRoot h, hK, ← pow_mul])
        (eSL.symm.trans eJ)
  ·
    letI : Fintype K := Fintype.ofFinite K
    have hFΩ : F ≤ orthDerived Q := hFle.trans hx'.supportedFixedDerived_le_orthDerived
    let eF : ↥F ≃* ↥J :=
      (Subgroup.subgroupOfEquivOfLe hFΩ).symm.trans
        (((F.subgroupOf (orthDerived Q)).equivMapOfInjective ρ hρinj).trans
          (MulEquiv.subgroupCongr hJeq.symm))
    obtain ⟨X, _, _, g, hX, hg, hgk⟩ : OrthCompData (OrthFactorRank 2 (Nat.card K)) ↥F :=
      orthCompData_fixedFactor_of (P := OrthFactorRank 2 (Nat.card K)) hx'
        (fun L hLn hLq => by
          obtain ⟨X, _, _, -, hRank, fX, hfX, hkX⟩ := omegaFactorRank_holds K (fixedSpace xe)
            (Q.comp (fixedSpace xe).subtype) hx'.polarBilin_fixed_nondegenerate L hLn hLq
          exact ⟨X, inferInstance, inferInstance, by rwa [hchar] at hRank, fX, hfX, hkX⟩)
        F hFq hFle hFn
    rw [hK] at hX
    exact card_ne_ordTwistedA_four_of_orthFactorRank hf he hX (eF.toMonoidHom.comp g)
      (eF.surjective.comp hg)
      (fun z hz => hgk (MonoidHom.mem_ker.2 ((MulEquiv.map_eq_one_iff eF).1 hz))) hZ hcard

end CFSG.LocalAnalysis.GLTheoremA.S265.SF5U

end
