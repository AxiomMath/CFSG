module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamTriDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamTriActKernel
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxTriality

import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.InnerTw
import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.TriD4InnerAux.SteinbergD4
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompAlgExcCore

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.RootAut
  CFSG.HardMathSupport.Timmesfeld.Steinberg CFSG.HardMathSupport.Dickson.Sec6.Up34Exc
  CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
  CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.ComponentClassification.PerfectAutomorphisms CFSG.GroupActions
  CFSG.LocalAnalysis.GLTheoremA.RationalModel
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie
open scoped MatrixGroups Pointwise


private theorem triWStab {K : Type} [Field K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {a : Fin Tag.D4.rank → Kˣ} (ha : ∀ i, a i ^ p = 1) :
    rootCharStabilizerSubgroup a ≤ kernelReflectionGroup a := by
  by_cases hp3 : p = 3
  · subst hp3
    exact (rootCharStabilizerSubgroup_eq_kernelReflectionGroup_D4_three a ha).le
  · intro w hw
    refine mem_kernelReflectionGroup_of_coprime hp ha hw ?_
    have hnd : ¬ p ∣ Nat.card (WeylGroup Tag.D4) :=
      CFSG.RankThree.PartOne.KGD.not_dvd_card_weylGroup_D4 hp (by have := hp.two_le; omega)
    exact Nat.coprime_comm.2 ((hp.coprime_iff_not_dvd).2 fun h =>
      hnd (h.trans (orderOf_dvd_natCard w)))

theorem triCompAction_holds : TriCompAction := by
  intro f K _ _ σ hdata p hp hp2 x w hxp hx1 hxw J hJ hw
  classical
  obtain ⟨hf1, hK, hσ⟩ := hdata
  let q : TauCeti.PrimePower := ⟨2, f, Nat.prime_two, hf1⟩
  haveI : Finite (TriGrp K σ) := Subtype.finite
  have hKq : Nat.card K = (q.p ^ q.exponent) ^ 3 := hK
  have hσq : ∀ c, σ c = c ^ (q.p ^ q.exponent) := hσ
  have hpq : p ≠ q.p := hp2
  have hmon : MonomialToralAt Tag.D4 p := by
    by_cases hp3 : p = 3
    · subst hp3
      exact monomialToralAt_three_of_block a2BlockToral_D4
    · exact monomialToralAt_of_not_dvd hp
        (CFSG.RankThree.PartOne.KGD.not_dvd_card_weylGroup_D4 hp
          (by have := hp.two_le; omega))
  obtain ⟨p₀, hp₀, hp₀ℓ, hq₀⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.exists_setup_prime
      q.prime_p q.exponent_pos hp hp2 hpq
  obtain ⟨S, a, ι, hSq, -, hT, hap, h1, hinj, hrange, hconj⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.exists_langSetup_of_inner_triD4_of_prime
      q.prime_p q.exponent_pos hKq σ hσq hp hpq hp₀ hp₀ℓ hq₀ hmon x hxp hx1
  have hpL : ((p : ℕ) : AlgebraicClosure K) ≠ 0 :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.natCast_ne_zero_algebraicClosure_of_ne
      q.prime_p hp hKq hpq
  have hTame :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.langSetup_hTame_of_prime
      S hp hpL (fun h => absurd h (by decide)) hT hap h1
  have hJ' : CFSG.Open.IsComponentOf J
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.conj x)) :=
    (CFSG.Assembly.isComponentOf_iff_open).1 hJ
  obtain ⟨i, hqs, hJR⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.components_of_langSetup
      S hp ι hinj hrange (MulAut.conj x) hconj hT hap h1 hTame hJ'
  have hTp := rootDiagUnit_pow_eq_one_of_forall hap
  have hA := CFSG.LocalAnalysis.GLTheoremA.KD264Lie.typeAShape_d4Class S hp hpL hTp h1 i
  have hAC : ringChar (AlgebraicClosure K) = 2 := by
    rw [ringChar_algebraicClosure]
    exact ringChar_eq_of_card_eq_pow (n := q.exponent * 3) q.prime_p
      (by have := q.exponent_pos; omega) (by rw [hK, ← pow_mul])
  haveI : CharP (AlgebraicClosure K) 2 := hAC ▸ ringChar.charP (AlgebraicClosure K)
  let R := rationalComponent S.ρ S.Γ (rootCharHom a) i
  let eJ : ↥J ≃* ↥R := (J.equivMapOfInjective ι hinj).trans (MulEquiv.subgroupCongr hJR)
  have heJ : ∀ k : J, (eJ k : ModGL Tag.D4 (AlgebraicClosure K)) = ι k := fun k => rfl
  set y : ModGL Tag.D4 (AlgebraicClosure K) := ι w with hydef
  have hyΓ : y ∈ S.Γ := by
    rw [hydef, ← hrange]
    exact ⟨w, rfl⟩
  have hyF : S.D.step y = y := ((Subgroup.commutator_le_self S.D.model) hyΓ).2
  have hyG : y ∈ adjointGroup Tag.D4 (AlgebraicClosure K) :=
    ((Subgroup.commutator_le_self S.D.model) hyΓ).1
  have hγconj : ∀ c, rootDiagUnit Tag.D4 a * ι c * (rootDiagUnit Tag.D4 a)⁻¹ =
      ι x * ι c * (ι x)⁻¹ := by
    intro c
    rw [← hconj c]
    change ι ((MulAut.conj x) c) = ι x * ι c * (ι x)⁻¹
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv]
  have hιxw : ι x * y * (ι x)⁻¹ = y := by
    have hxwx : x * w * x⁻¹ = w := by rw [hxw, mul_inv_cancel_right]
    have h1' : ι (x * w * x⁻¹) = ι w := by rw [hxwx]
    rw [hydef]
    simpa only [map_mul, map_inv] using h1'
  have hyd : rootDiagUnit Tag.D4 a * y * (rootDiagUnit Tag.D4 a)⁻¹ = y := by
    rw [hydef, hγconj w]
    exact hιxw
  have hφy : ∀ c, ι ((MulAut.conj w) c) = y * ι c * y⁻¹ := by
    intro c
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv, hydef]
  have hyC : y ∈ toralCentralizer Tag.D4 (AlgebraicClosure K) a :=
    mem_toralCentralizer.2 ⟨hyG, hyd⟩
  have hyZ : y ∈ torusGroup Tag.D4 (AlgebraicClosure K) ⊔
      rootSpan Tag.D4 (AlgebraicClosure K) (kernelRoots (rootCharHom a)) := by
    have hW := triWStab hp hp2 hap
    have hZeq := toralCentralizer_eq_toralRootGroup_of_stabilizer_le Tag.D4
      (AlgebraicClosure K) a hW
    rwa [hZeq] at hyC
  have hyR : MulAut.conj y ∈ subgroupStabAut R := by
    change R.map (MulAut.conj y).toMonoidHom = R
    have hcomp : (MulAut.conj y).toMonoidHom.comp ι =
        ι.comp (MulAut.conj w).toMonoidHom := by
      apply MonoidHom.ext
      intro c
      change MulAut.conj y (ι c) = ι ((MulAut.conj w) c)
      rw [MulAut.conj_apply]
      exact (hφy c).symm
    have hwJ : J.map (MulAut.conj w).toMonoidHom = J := hw
    have hJR' : J.map ι = R := hJR
    rw [← hJR', Subgroup.map_map, hcomp, ← Subgroup.map_map, hwJ]
  have hmain : centerQuotientHom ↥R (subgroupStabRestrict R ⟨MulAut.conj y, hyR⟩) ∈
      innAutDerived (↥R ⧸ Subgroup.center ↥R) :=
    triKernelCompAction S hp hT hap h1 i hA hqs hyZ hyF hyR
  refine centerQuotientHom_mem_innAutDerived_of_mulEquiv_kd264alg eJ ?_ hmain
  intro k
  apply Subtype.ext
  rw [heJ, subgroupStabRestrict_apply, subgroupStabRestrict_apply, heJ, MulAut.conj_apply]
  exact hφy k

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
