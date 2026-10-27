module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.Bal209TwoSLOBIn
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.TwE6InnerCompClass
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.TwE6UniqRat
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcTamePrime

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.I2610

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerAbs
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6UniqAbs

section Certificates


theorem exists_component_of_perfect_le_twE6 {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 4) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2)
    {s : twistedE6RootGroup K σ} (hs : orderOf s = 3)
    {P : Subgroup (twistedE6RootGroup K σ)} (hPs : P ≤ fixSubgroup (MulAut.conj s))
    (hP : ⁅P, P⁆ = P) (hP1 : P ≠ ⊥) :
    ∃ L : Subgroup (twistedE6RootGroup K σ), L ≤ fixSubgroup (MulAut.conj s) ∧
      CFSG.Open.IsQuasisimple ↥L ∧ P ≤ L ∧ IsLieQuot ↥L TwE6TwoInnerCompIndex ∧
        ∀ ω : MulAut (twistedE6RootGroup K σ), ω * MulAut.conj s = MulAut.conj s * ω →
          L.map ω.toMonoidHom = L := by
  classical
  have hs3 : s ^ 3 = 1 := by rw [← hs]; exact pow_orderOf_eq_one s
  have hs1 : s ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hs
    exact absurd hs (by norm_num)
  haveI : Fintype K := Fintype.ofFinite K
  haveI hcK : CharP K 2 := charP_of_card_eq_prime_pow (f := 2)
    (by rw [← Nat.card_eq_fintype_card, hK]; norm_num)
  haveI hcL : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  obtain ⟨S, a, ι, hq, hρ, hT, hap, h1, hin, hinj, hrange, hιs⟩ :=
    exists_stdSetup_of_inner hK σ hσ hs3 hs1
  have h3 : ((3 : ℕ) : AlgebraicClosure K) ≠ 0 := natCast_three_ne_zero_of_charTwo
  have hTame := langSetup_hTame_of_prime S Nat.prime_three h3
    (fun h => absurd h (by decide)) hT hap h1
  set d : ModGL Tag.E6 (AlgebraicClosure K) := rootDiagUnit Tag.E6 a with hd
  have hβ : ∀ c, ι (MulAut.conj s c) = d * ι c * d⁻¹ := by
    intro c
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv, hιs]
  have hfix : (fixSubgroup (MulAut.conj s)).map ι = S.Γ ⊓ Subgroup.centralizer {d} := by
    rw [map_fixSubgroup_eq_of_conj ι hinj (MulAut.conj s) d hβ, hrange]
  have hcomapfix : (S.Γ ⊓ Subgroup.centralizer {d}).comap ι = fixSubgroup (MulAut.conj s) := by
    rw [← hfix]
    exact Subgroup.comap_map_eq_self_of_injective hinj _
  have hCdrange : S.Γ ⊓ Subgroup.centralizer {d} ≤ ι.range := fun x hx => by
    rw [hrange]
    exact (Subgroup.mem_inf.1 hx).1
  haveI : Finite (KernelComponent (rootCharHom a)) :=
    (root_character_kernel_orthogonal_central_product Tag.E6 (AlgebraicClosure K)
      (rootCharHom a)).2.1
  have hcompR : ∀ i : KernelComponent (rootCharHom a),
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) →
        IsComponentOf (rationalComponent S.ρ S.Γ (rootCharHom a) i)
          (S.Γ ⊓ Subgroup.centralizer {d}) := by
    intro i hi
    obtain ⟨hle, hsub⟩ := langSubnormal_of_mem_torus S hT i
    exact ⟨hle, (CFSG.Open.IsSubnormal.iff_subgroupOf hle).2 hsub, open_isQuasisimple hi⟩
  have hU := ratQuasiEq_holds (AlgebraicClosure K) 5 S a hq hT hap h1
  have hmain : ∀ Q : Subgroup (twistedE6RootGroup K σ), Q ≤ fixSubgroup (MulAut.conj s) →
      ⁅Q, Q⁆ = Q → Q ≠ ⊥ → ∃ i : KernelComponent (rootCharHom a),
        CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) ∧
          Q ≤ (rationalComponent S.ρ S.Γ (rootCharHom a) i).comap ι := by
    intro Q hQ hQperf hQne
    have hQmap : Q.map ι ≤ S.Γ ⊓ Subgroup.centralizer {d} := by
      rw [← hfix]
      exact Subgroup.map_mono hQ
    have hperfmap : ⁅Q.map ι, Q.map ι⁆ = Q.map ι := by
      rw [← Subgroup.map_commutator, hQperf]
    have h2 := perfect_le_iSup_rationalComponent_of_prime S Nat.prime_three hT hap h1 hTame
      (Q.map ι) hQmap hperfmap
    obtain ⟨i₀, hi₀⟩ : ∃ i, CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
      by_contra hcon
      push Not at hcon
      haveI : IsEmpty {i : KernelComponent (rootCharHom a) //
          CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i)} :=
        ⟨fun ⟨i, hi⟩ => hcon i hi⟩
      rw [iSup_of_empty] at h2
      exact hQne ((Subgroup.map_eq_bot_iff_of_injective _ hinj).1 (le_bot_iff.1 h2))
    exact ⟨i₀, hi₀, (Subgroup.map_le_iff_le_comap).1
      (h2.trans (iSup_le fun i => (hU i.1 i₀ i.2 hi₀).le))⟩
  obtain ⟨i₀, hi₀q, hPL⟩ := hmain P hPs hP hP1
  set R₀ : Subgroup (ModGL Tag.E6 (AlgebraicClosure K)) :=
    rationalComponent S.ρ S.Γ (rootCharHom a) i₀ with hR₀
  have hR₀range : R₀ ≤ ι.range := (hcompR i₀ hi₀q).1.trans hCdrange
  have hcomp₀ : IsComponentOf (R₀.comap ι) (fixSubgroup (MulAut.conj s)) := by
    have h := isComponentOf_comap_of_injective ι hinj hR₀range hCdrange (hcompR i₀ hi₀q)
    rwa [hcomapfix] at h
  have hLle : ∀ Q : Subgroup (twistedE6RootGroup K σ), Q ≤ fixSubgroup (MulAut.conj s) →
      ⁅Q, Q⁆ = Q → Q ≤ R₀.comap ι := by
    intro Q hQ hQperf
    by_cases hQ0 : Q = ⊥
    · rw [hQ0]
      exact bot_le
    · obtain ⟨j, hjq, hQj⟩ := hmain Q hQ hQperf hQ0
      rwa [hU j i₀ hjq hi₀q] at hQj
  have hfixMap : ∀ (ν : MulAut (twistedE6RootGroup K σ)),
      ν * MulAut.conj s = MulAut.conj s * ν →
        (R₀.comap ι).map ν.toMonoidHom ≤ fixSubgroup (MulAut.conj s) := by
    intro ν hν
    rintro _ ⟨x, hx, rfl⟩
    have hx' : MulAut.conj s x = x := hcomp₀.1 hx
    have hmul : MulAut.conj s (ν x) = ν (MulAut.conj s x) := by
      have h := congrArg (fun m : MulAut (twistedE6RootGroup K σ) => m x) hν.symm
      simpa only [MulAut.mul_apply] using h
    show MulAut.conj s (ν x) = ν x
    rw [hmul, hx']
  have hLL : ⁅R₀.comap ι, R₀.comap ι⁆ = R₀.comap ι :=
    Subgroup.isPerfect_iff.mp ((Group.isPerfect_def).2 hcomp₀.2.2.1)
  have hperfMap : ∀ (ν : MulAut (twistedE6RootGroup K σ)),
      ⁅(R₀.comap ι).map ν.toMonoidHom, (R₀.comap ι).map ν.toMonoidHom⁆ =
        (R₀.comap ι).map ν.toMonoidHom := by
    intro ν
    rw [← Subgroup.map_commutator, hLL]
  refine ⟨R₀.comap ι, hcomp₀.1, hcomp₀.2.2, hPL, ?_, ?_⟩
  · have hmap : (R₀.comap ι).map ι = R₀ := Subgroup.map_comap_eq_self hR₀range
    let e : ↥(R₀.comap ι) ≃* ↥R₀ :=
      (Subgroup.equivMapOfInjective _ ι hinj).trans (MulEquiv.subgroupCongr hmap)
    exact Bal209F4Aux.isLieQuot_mulEquiv e.symm
      (class_isLieQuot_of_inner S hq hρ hT hap h1 hin i₀ hi₀q)
  · intro ω hω
    have hcomm : Commute ω (MulAut.conj s) := hω
    have hω' : ω⁻¹ * MulAut.conj s = MulAut.conj s * ω⁻¹ := hcomm.inv_left.eq
    refine le_antisymm (hLle _ (hfixMap ω hω) (hperfMap ω)) ?_
    intro x hx
    refine Subgroup.mem_map.2 ⟨ω⁻¹ x, ?_, ?_⟩
    · exact hLle _ (hfixMap ω⁻¹ hω') (hperfMap ω⁻¹) (Subgroup.mem_map.2 ⟨x, hx, rfl⟩)
    · show ω (ω⁻¹ x) = x
      simp

end Certificates

end CFSG.LocalAnalysis.GLTheoremA.CatB.I2610
