module

public import CFSG.RankThree.PartOne.KC.OrthogonalFixedRestrict
public import CFSG.RankThree.PartOne.KC.OrthogonalFactorization
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddOrthAll
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddInnerModels

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.SsOrth

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.ComponentClassification.CatLeafProof (OddLieCentralQuotient
  oddLieCentralQuotient_of_component_equiv oddLieCentralQuotient_of_mulEquiv
  orthogonal_component_oddLieCentralQuotient not_isComponent_of_isSolvable)
open CFSG.ComponentClassification.CatLeafProof.OddInner (oddLie_GL oddLie_unitary)

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V} {ℓ f : ℕ}

theorem oddLie_fixedBlock (hx : OddOrderIsometry Q p x) (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) {L : Subgroup ↥(supportedBlock Q x (X - 1))}
    (hL : CFSG.IsComponent L) : OddLieCentralQuotient ℓ ↥L :=
  oddLieCentralQuotient_of_component_equiv (fixedBlockEquiv hx)
    (fun M hM => orthogonal_component_oddLieCentralQuotient hℓ hℓ2 K (fixedSpace x) f hf hK
      (Q.comp (fixedSpace x).subtype) hx.polarBilin_fixed_nondegenerate M hM) hL

theorem oddLie_pairedBlock (hx : OddOrderIsometry Q p x) (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) {r : K[X]} (hr : r ∈ primaryFactors x.toLinearMap)
    (hne : r ≠ reciprocalPolynomial r) {L : Subgroup ↥(supportedBlock Q x r)}
    (hL : CFSG.IsComponent L) : OddLieCentralQuotient ℓ ↥L := by
  haveI : Fact (Irreducible r) := ⟨irreducible_of_mem_primaryFactors hr⟩
  have hm : 1 ≤ primaryMultiplicity x.toLinearMap r := hx.primaryMultiplicity_pos hr
  let b : Module.Basis (Fin (primaryMultiplicity x.toLinearMap r)) (AdjoinRoot r)
      (primaryComponent x.toLinearMap r) := Module.finBasisOfFinrankEq _ _ rfl
  let e1 : BlockGL x r ≃* GL (Fin (primaryMultiplicity x.toLinearMap r)) (AdjoinRoot r) :=
    (Matrix.GeneralLinearGroup.toLin' b).symm
  have hE : Nat.card (AdjoinRoot r) = ℓ ^ (f * finrank K (AdjoinRoot r)) := by
    rw [Module.natCard_eq_pow_finrank (K := K), hK, ← pow_mul]
  have hfpos : 1 ≤ f * finrank K (AdjoinRoot r) := Nat.mul_pos hf Module.finrank_pos
  exact oddLieCentralQuotient_of_component_equiv ((pairedBlockEquiv hx hr hne).trans e1)
    (fun M hM => oddLie_GL hℓ hfpos hE hm hM) hL

theorem not_isComponent_supportedBlock_of_multiplicity_one (hx : OddOrderIsometry Q p x)
    {r : K[X]} [Fact (Irreducible r)] (hr : r ∈ primaryFactors x.toLinearMap)
    (h1 : primaryMultiplicity x.toLinearMap r = 1) {L : Subgroup ↥(supportedBlock Q x r)}
    (hL : CFSG.IsComponent L) : False := by
  have hcomm : ∀ g g' : ↥(supportedBlock Q x r), g * g' = g' * g := by
    intro g g'
    apply hx.blockGL_injective hr
    rw [map_mul, map_mul]
    apply Units.ext
    obtain ⟨c, hc, -⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one h1
      ((blockGL Q x r g : BlockGL x r) : Module.End (AdjoinRoot r) (primaryComponent x.toLinearMap r))
    obtain ⟨c', hc', -⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one h1
      ((blockGL Q x r g' : BlockGL x r) : Module.End (AdjoinRoot r) (primaryComponent x.toLinearMap r))
    simp only [Units.val_mul, hc, hc']
    ext v
    simp [mul_comm, smul_smul]
  haveI : IsMulCommutative ↥(supportedBlock Q x r) := ⟨⟨hcomm⟩⟩
  exact not_isComponent_of_isSolvable hL

theorem oddLie_selfDualBlock (hx : OddOrderIsometry Q p x) (hp2 : Odd p) (hℓ : ℓ.Prime)
    (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) {r : K[X]}
    (hr : r ∈ primaryFactors x.toLinearMap) (hne1 : r ≠ X - 1)
    (hself : r = reciprocalPolynomial r) {L : Subgroup ↥(supportedBlock Q x r)}
    (hL : CFSG.IsComponent L) : OddLieCentralQuotient ℓ ↥L := by
  classical
  haveI : Fact (Irreducible r) := ⟨irreducible_of_mem_primaryFactors hr⟩
  obtain ⟨d, H, hdeg, -, hH, hadd1, hadd2, hleft, hright, hsymm⟩ :=
    hx.exists_selfDual_hermitian hp2 hr hne1 hself
  by_cases hm1 : primaryMultiplicity x.toLinearMap r = 1
  · exact (not_isComponent_supportedBlock_of_multiplicity_one hx hr hm1 hL).elim
  have hm : 2 ≤ finrank (AdjoinRoot r) (primaryComponent x.toLinearMap r) := by
    have := hx.primaryMultiplicity_pos hr
    change 2 ≤ primaryMultiplicity x.toLinearMap r
    omega
  have hd : finrank K (AdjoinRoot r) = 2 * d := by
    rw [(AdjoinRoot.powerBasis (irreducible_of_mem_primaryFactors hr).ne_zero).finrank,
      AdjoinRoot.powerBasis_dim, hdeg]
  have hd0 : 1 ≤ d := by
    have : 0 < finrank K (AdjoinRoot r) := Module.finrank_pos
    omega
  let σ : AdjoinRoot r ≃+* AdjoinRoot r := (frobPow K (AdjoinRoot r) d).toRingEquiv
  have hσ : ∀ z, σ z = z ^ (ℓ ^ (f * d)) := fun z => by
    change frobPow K (AdjoinRoot r) d z = _
    rw [frobPow_apply, hK, ← pow_mul]
  have hσσ : ∀ z, σ (σ z) = z := frobPow_frobPow K (AdjoinRoot r) hd
  have hEcard : Nat.card (AdjoinRoot r) = (ℓ ^ (f * d)) ^ 2 := by
    rw [Module.natCard_eq_pow_finrank (K := K), hK, hd, ← pow_mul, ← pow_mul]
    congr 1
    ring
  have hfd : 1 ≤ f * d := Nat.mul_pos hf hd0
  have hσ2 : σ ^ 2 = 1 := by
    ext z
    change σ (σ z) = z
    exact hσσ z
  have hσ1 : σ ≠ 1 := by
    obtain ⟨c, hc⟩ := (show CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData ℓ (f * d)
      (AdjoinRoot r) from ⟨hℓ, hfd, by rw [hEcard, ← pow_mul]; congr 1; ring⟩).exists_bar_ne
    intro h
    apply hc
    have h1 : σ c = c := congrArg (fun τ : AdjoinRoot r ≃+* AdjoinRoot r => τ c) h
    rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.bar_apply, ← hσ c]
    exact h1
  let B : primaryComponent x.toLinearMap r →ₛₗ[σ.toRingHom]
      primaryComponent x.toLinearMap r →ₗ[AdjoinRoot r] AdjoinRoot r :=
    LinearMap.mk₂'ₛₗ σ.toRingHom (RingHom.id _) H hadd1
      (fun c u w => by rw [hleft, smul_eq_mul]; rfl) hadd2
      (fun c u w => by rw [hright, smul_eq_mul, RingHom.id_apply])
  have hBH : ∀ u w, B u w = H u w := fun u w => rfl
  have hBsymm : B.IsSymm := ⟨fun u w => by rw [hBH, hBH, hsymm u w]; rfl⟩
  have hBl : B.SeparatingLeft := by
    intro u hu
    refine Subtype.ext (hx.eq_zero_of_polar_selfdual hr hself u.2 fun w hw => ?_)
    have h1 := hH u ⟨w, hw⟩ 1
    rw [mul_one, one_smul] at h1
    have h2 : H u ⟨w, hw⟩ = 0 := by rw [← hBH]; exact hu _
    rw [h2, map_zero] at h1
    exact h1.symm
  have hBr : B.SeparatingRight := by
    intro w hw
    apply hBl w
    intro u
    have := hw u
    rw [← hBsymm.eq, this, map_zero]
  let Φ : ↥(supportedBlock Q x r) →*
      ↥(CFSG.ComponentClassification.CatalogueBUnitaryIsometry.isometryGroup B) :=
    (((LinearMap.GeneralLinearGroup.generalLinearEquiv (AdjoinRoot r)
      (primaryComponent x.toLinearMap r)).toMonoidHom.comp (blockGL Q x r)).codRestrict _
      fun g => by
        have hg : (blockGL Q x r g : BlockGL x r) ∈ (blockGL Q x r).range := ⟨g, rfl⟩
        rw [hx.mem_range_blockGL_selfDual_iff hr hne1 hself H hH] at hg
        intro u w
        exact hg u w)
  have hΦinj : Function.Injective Φ := by
    intro g g' h
    apply hx.blockGL_injective hr
    have := congrArg Subtype.val h
    exact (LinearMap.GeneralLinearGroup.generalLinearEquiv (AdjoinRoot r)
      (primaryComponent x.toLinearMap r)).injective this
  have hΦsurj : Function.Surjective Φ := by
    rintro ⟨y, hy⟩
    set γ : BlockGL x r := (LinearMap.GeneralLinearGroup.generalLinearEquiv (AdjoinRoot r)
      (primaryComponent x.toLinearMap r)).symm y with hγ
    have hγr : γ ∈ (blockGL Q x r).range := by
      rw [hx.mem_range_blockGL_selfDual_iff hr hne1 hself H hH]
      intro u w
      exact hy u w
    obtain ⟨g, hg⟩ := hγr
    refine ⟨g, Subtype.ext ?_⟩
    change (LinearMap.GeneralLinearGroup.generalLinearEquiv (AdjoinRoot r)
      (primaryComponent x.toLinearMap r)) (blockGL Q x r g) = y
    rw [hg, hγ, MulEquiv.apply_symm_apply]
  let Ψ := MulEquiv.ofBijective Φ ⟨hΦinj, hΦsurj⟩
  refine oddLieCentralQuotient_of_component_equiv Ψ (fun M hM => ?_) hL
  exact oddLie_unitary (E := AdjoinRoot r) (W := primaryComponent x.toLinearMap r) hℓ hℓ2 hfd
    hEcard hm B hBsymm ⟨hBl, hBr⟩ hσ2 hσ1 hσ hM

theorem oddLie_supportedBlock (hx : OddOrderIsometry Q p x) (hp2 : Odd p) (hℓ : ℓ.Prime)
    (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) {r : K[X]}
    (hr : r ∈ primaryFactors x.toLinearMap) {L : Subgroup ↥(supportedBlock Q x r)}
    (hL : CFSG.IsComponent L) : OddLieCentralQuotient ℓ ↥L := by
  by_cases h1 : r = X - 1
  · subst h1
    exact oddLie_fixedBlock hx hℓ hℓ2 hf hK hL
  · by_cases hself : r = reciprocalPolynomial r
    · exact oddLie_selfDualBlock hx hp2 hℓ hℓ2 hf hK hr h1 hself hL
    · exact oddLie_pairedBlock hx hℓ hf hK hr hself hL

end CFSG.HardMathSupport.Dickson.Sec6.SsOrth
