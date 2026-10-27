module

public import CFSG.HardMathSupport.Dickson.Bal207.OrthD4Loc

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.S172B.Cent

open Polynomial Module QuadraticMap CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V}

private theorem comp_cases_orthDerived_aux1 {G G' : Type} [Group G] [Group G'] (φ : G →* G')
    (hφ : Function.Injective φ) {L K : Subgroup G} (h : CFSG.Open.IsComponentOf L K) :
    CFSG.Open.IsComponentOf (L.map φ) (K.map φ) :=
  ⟨Subgroup.map_mono h.1, CFSG.Open.IsSubnormal.map φ h.2.1,
    CFSG.Open.IsQuasisimple.of_mulEquiv (Subgroup.equivMapOfInjective L φ hφ).symm h.2.2⟩

theorem comp_cases_orthDerived (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {x : ↥(orthDerived Q)} (hx3 : orderOf x = 3) {L : Subgroup ↥(orthDerived Q)}
    (hL : CFSG.Open.IsComponentOf L (Subgroup.centralizer ({x} : Set ↥(orthDerived Q)))) :
    ((X ^ 2 + X + 1 : (ZMod 2)[X]) ∈ primaryFactors (x : V ≃ₗ[ZMod 2] V).toLinearMap ∧
        CFSG.IsQuasisimple ↥(specialBlock Q (x : V ≃ₗ[ZMod 2] V) (X ^ 2 + X + 1)) ∧
        L = (specialBlock Q (x : V ≃ₗ[ZMod 2] V) (X ^ 2 + X + 1)).subgroupOf (orthDerived Q)) ∨
      ∃ F : Subgroup (V ≃ₗ[ZMod 2] V), CFSG.IsQuasisimple ↥F ∧
        F ≤ supportedFixedDerived Q (x : V ≃ₗ[ZMod 2] V) ∧
        (F.subgroupOf (supportedFixedDerived Q (x : V ≃ₗ[ZMod 2] V))).Normal ∧
        (finrank (ZMod 2) (fixedSpace (x : V ≃ₗ[ZMod 2] V)) ≤ 4 ∨
          F = supportedFixedDerived Q (x : V ≃ₗ[ZMod 2] V)) ∧
        L = F.subgroupOf (orthDerived Q) := by
  classical
  have hV : Nontrivial V := by
    by_contra hV
    rw [not_nontrivial_iff_subsingleton] at hV
    haveI := hV
    have h1 : x = 1 := Subtype.ext (LinearEquiv.ext fun v => Subsingleton.elim _ _)
    rw [h1, orderOf_one] at hx3
    omega
  haveI := hV
  have hinj : Function.Injective (piOrth Q) := piOrth_injective hQ
  have hL' : CFSG.Open.IsComponentOf (L.map (piOrth Q))
      (Subgroup.centralizer ({piOrth Q x} : Set (ProjOrthDerived Q))) := by
    have h := comp_cases_orthDerived_aux1 (piOrth Q) hinj hL
    rwa [map_centralizer_eq_centralizerImage x, centralizerImage_eq hQ x] at h
  rcases CFSG.HardMathSupport.Dickson.Bal207.OrthFix.inner_comp_cases (K := ZMod 2)
      (Or.inl (Nat.card_zmod 2)) hQ x hx3 hL' with
    ⟨hmem, hqs, hLmap⟩ | ⟨F, hFq, hFle, hFnorm, hFdim, hLmap⟩
  · left
    refine ⟨hmem, hqs, ?_⟩
    refine Subgroup.map_injective hinj ?_
    rw [hLmap]
    rfl
  · right
    exact ⟨F, hFq, hFle, hFnorm, hFdim, Subgroup.map_injective hinj hLmap⟩

private theorem apply_eq_of_mem_specialBlock_aux1 :
    (X - 1 : (ZMod 2)[X]) ≠ X ^ 2 + X + 1 := by
  intro h
  have := congrArg (fun p : (ZMod 2)[X] => p.eval 1) h
  simp only [eval_sub, eval_X, eval_one, eval_pow, eval_add] at this
  exact absurd this (by decide)

private theorem apply_eq_of_mem_specialBlock_aux2 :
    (X - 1 : (ZMod 2)[X]) ≠ reciprocalPolynomial (X ^ 2 + X + 1) := by
  intro h
  have hdeg := congrArg Polynomial.natDegree h
  have h0 : (X ^ 2 + X + 1 : (ZMod 2)[X]).coeff 0 ≠ 0 := by simp
  rw [natDegree_reciprocalPolynomial h0] at hdeg
  have h1 : (X - 1 : (ZMod 2)[X]).natDegree = 1 := by compute_degree!
  have h2 : (X ^ 2 + X + 1 : (ZMod 2)[X]).natDegree = 2 := by compute_degree!
  rw [h1, h2] at hdeg
  exact absurd hdeg (by norm_num)

theorem apply_eq_of_mem_specialBlock (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {x : V ≃ₗ[ZMod 2] V} (hxO : x ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hx3 : x ^ 3 = 1)
    {g : V ≃ₗ[ZMod 2] V} (hg : g ∈ specialBlock Q x (X ^ 2 + X + 1)) {v : V} (hv : x v = v) :
    g v = v := by
  have hgS : g ∈ supportedBlock Q x (X ^ 2 + X + 1) :=
    specialBlock_le_supportedBlock _ hg
  have hfix := (mem_supportedBlock.mp hgS).2
  by_cases hv0 : v = 0
  · rw [hv0, map_zero]
  · have hvW : v ∈ fixedSpace x := mem_fixedSpace.mpr hv
    have hX : (X - 1 : (ZMod 2)[X]) ∈ primaryFactors x.toLinearMap := by
      by_contra hnot
      rw [fixedSpace_eq_bot_of_not_mem hnot, Submodule.mem_bot] at hvW
      exact hv0 hvW
    rw [fixedSpace_eq_primaryComponent] at hvW
    exact hfix v (Submodule.mem_iSup_of_mem (X - 1)
      (Submodule.mem_iSup_of_mem ⟨hX, apply_eq_of_mem_specialBlock_aux1,
        apply_eq_of_mem_specialBlock_aux2⟩ hvW))

private theorem apply_eq_of_mem_supportedFixedDerived_aux1 {x : Module.End (ZMod 2) V}
    {a : (ZMod 2)[X]} (ha : Irreducible a) (ham : a.Monic) {v : V}
    (hv : aeval x a v = 0) (hv0 : v ≠ 0) : a ∈ primaryFactors x := by
  refine mem_primaryFactors.mpr ⟨ha, ham, ?_⟩
  by_contra hnd
  obtain ⟨u, r, hur⟩ := ha.coprime_iff_not_dvd.mpr hnd
  have h1 : aeval x (u * a + r * minpoly (ZMod 2) x) v = v := by
    rw [hur, map_one]
    rfl
  rw [map_add, map_mul, map_mul, minpoly.aeval, mul_zero, add_zero, Module.End.mul_apply, hv,
    map_zero] at h1
  exact hv0 h1.symm

theorem apply_eq_of_mem_supportedFixedDerived (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {x : V ≃ₗ[ZMod 2] V} (hxO : x ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hx3 : x ^ 3 = 1)
    {g : V ≃ₗ[ZMod 2] V} (hg : g ∈ supportedFixedDerived Q x) {v : V}
    (hv : x (x v) + x v + v = 0) : g v = v := by
  have _hx : OddOrderIsometry Q 3 x :=
    ⟨hxO, hx3, by decide, fun v hv => hQ.1 v fun w => by simpa using hv w⟩
  by_cases hv0 : v = 0
  · rw [hv0, map_zero]
  have hgB : g ∈ supportedBlock Q x (X - 1) := supportedFixedDerived_le_supportedBlock hg
  refine (mem_supportedBlock.mp hgB).2 v ?_
  have hdeg : (X ^ 2 + X + 1 : (ZMod 2)[X]).natDegree = 2 := by compute_degree!
  have hirr : Irreducible (X ^ 2 + X + 1 : (ZMod 2)[X]) := by
    refine irreducible_of_degree_le_three_of_not_isRoot (by rw [hdeg]; decide) fun y hy => ?_
    rw [IsRoot, eval_add, eval_add, eval_pow, eval_X, eval_one] at hy
    revert y hy
    decide
  have hmon : (X ^ 2 + X + 1 : (ZMod 2)[X]).Monic := by monicity!
  have hvΦ : v ∈ primaryComponent x.toLinearMap (X ^ 2 + X + 1 : (ZMod 2)[X]) := by
    rw [mem_primaryComponent]
    simpa [pow_two, Module.End.mul_apply] using hv
  have hmem : (X ^ 2 + X + 1 : (ZMod 2)[X]) ∈ primaryFactors x.toLinearMap :=
    apply_eq_of_mem_supportedFixedDerived_aux1 hirr hmon (mem_primaryComponent.mp hvΦ) hv0
  have hdeg1 : (X - 1 : (ZMod 2)[X]).natDegree = 1 := by compute_degree!
  have hne : (X ^ 2 + X + 1 : (ZMod 2)[X]) ≠ X - 1 := by
    intro heq
    have h2 : (X ^ 2 + X + 1 : (ZMod 2)[X]).natDegree = (X - 1 : (ZMod 2)[X]).natDegree := by
      rw [heq]
    rw [hdeg, hdeg1] at h2
    omega
  exact Submodule.mem_iSup_of_mem (X ^ 2 + X + 1 : (ZMod 2)[X])
    (Submodule.mem_iSup_of_mem ⟨hmem, hne, by rwa [reciprocalPolynomial_X_sub_one]⟩ hvΦ)

end CFSG.LocalAnalysis.GLTheoremA.S172B.Cent

end
