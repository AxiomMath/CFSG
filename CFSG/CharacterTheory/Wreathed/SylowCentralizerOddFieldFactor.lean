module

public import CFSG.CharacterTheory.Wreathed.SylowCentralizerOddFieldFactorSupport
public import CFSG.CharacterTheory.Semidihedral.CoreResidual
public import CFSG.CharacterTheory.Semidihedral.Local.CoprimeCentralizerQuotient
public import CFSG.CharacterTheory.Wreathed.BaseFourCentralizerStructure
public import CFSG.CharacterTheory.Wreathed.CentralTwoPowerFieldLift

public section

namespace CFSG.Wreathed.SylowCentralizerOddField

universe u v

open CFSG.Semidihedral.OddFieldLift

theorem original_sylow_centralizer_sees_entire_odd_field_factor {N : Type v} [Group N]
    [Finite N] (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 N) (e : S ≃* Wreath (2 ^ n))
    (R : Subgroup N) [R.Normal] (hR : Odd (Nat.card R)) (p f : ℕ) (hp : p.Prime)
    (hpodd : Odd p) (hf : 1 ≤ f) (F : Type u) [Field F] [Finite F]
    (hcard : Nat.card F = p ^ f) (Sigma : Subgroup (F ≃+* F)) (hd : Odd (Nat.card Sigma))
    (φ : N ⧸ R →* Gamma F Sigma) (hφ : Function.Surjective φ)
    (hcentral : φ.ker ≤ Subgroup.center (N ⧸ R)) (hkernel : ∃ k : ℕ, Nat.card φ.ker = 2 ^ k)
    (ν : Gamma F Sigma →* Sigma)
    (hν : ∀ g : Gamma F Sigma, g ∈ gammaLinear F Sigma → ∀ σ : Sigma,
      ν (g * ((gammaFieldEquiv F Sigma).symm σ : Gamma F Sigma)) = σ) :
    let π := QuotientGroup.mk' R
    let C := Subgroup.centralizer (S : Set N)
    let Sbar := (S : Subgroup N).map π
    let CH := Subgroup.centralizer (Sbar : Set (N ⧸ R))
    let E := (CFSG.oddCore C).map C.subtype
    let ω := ν.comp (φ.comp π)
    C.map π = CH ∧ (π.comp C.subtype).ker = R.subgroupOf C ∧
      E.map π = (CFSG.oddCore CH).map CH.subtype ∧ E.map ω = ⊤ ∧
      ω.ker.relIndex E = Nat.card Sigma := by
  intro π C Sbar CH E ω
  have hR2 : ¬ 2 ∣ Nat.card R :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp (Nat.coprime_two_left.mpr hR)
  obtain ⟨hCmap, hcore, hker, -⟩ :=
    CFSG.Semidihedral.Local.coprime_centralizer_prime_complement_core_quotient 2 R hR2
      (S : Subgroup N) S.isPGroup'
  have hEmap : E.map π = (CFSG.oddCore CH).map CH.subtype := by
    change ((CFSG.oddCore C).map C.subtype).map π = (CFSG.oddCore CH).map CH.subtype
    rw [CFSG.Semidihedral.CoreResidual.oddCore_eq_twoPrimeCore,
      CFSG.Semidihedral.CoreResidual.oddCore_eq_twoPrimeCore]
    exact hcore
  obtain ⟨-, -, -, -, -, ⟨eE, heE⟩, -, -, -, -, -, -, -, -, -, -, -, ⟨P, -, hPC⟩⟩ :=
    CentralTwoPowerFieldLift.central_two_kernel_odd_field_complement_and_fixed_centralizer
      p f hp hpodd hf F hcard Sigma hd φ hφ hcentral hkernel
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective R
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq (N ⧸ R) P (S.mapSurjective hπsurj)
  have hSbar : Sbar = (P : Subgroup (N ⧸ R)).map (MulAut.conj h).toMonoidHom := by
    change ((S.mapSurjective hπsurj : Sylow 2 (N ⧸ R)) : Subgroup (N ⧸ R)) = _
    rw [← hh, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  have hcyc : IsCyclic (F ≃+* F) :=
    CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic F
  have hSigcomm : ∀ a b : Sigma, a * b = b * a := fun a b =>
    Subtype.ext (IsCyclic.commGroup.mul_comm (a : F ≃+* F) b)
  have hsurjC : ∀ σ : Sigma, ∃ c ∈ C, ω c = σ := by
    intro σ
    let x := eE.symm ((gammaFieldEquiv F Sigma).symm σ)
    have hφx : φ x = ((gammaFieldEquiv F Sigma).symm σ : Gamma F Sigma) := by
      rw [← heE x, MulEquiv.apply_symm_apply]
    have hνx : ν (φ x) = σ := by
      rw [hφx]
      have h1 := hν 1 (Subgroup.one_mem _) σ
      rwa [one_mul] at h1
    have hw : h * (x : N ⧸ R) * h⁻¹ ∈ CH := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [hSbar] at hz
      obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hz
      have hxq : (x : N ⧸ R) * q = q * x := Subgroup.mem_centralizer_iff.mp (hPC hq) x x.2
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc h * q * h⁻¹ * (h * (x : N ⧸ R) * h⁻¹) = h * (q * x) * h⁻¹ := by group
        _ = h * (x * q) * h⁻¹ := by rw [hxq]
        _ = h * (x : N ⧸ R) * h⁻¹ * (h * q * h⁻¹) := by group
    have hw' : h * (x : N ⧸ R) * h⁻¹ ∈
        (Subgroup.centralizer (((S : Subgroup N) : Set N))).map (QuotientGroup.mk' R) := by
      rw [hCmap]
      exact hw
    obtain ⟨c, hc, hcw⟩ := Subgroup.mem_map.mp hw'
    refine ⟨c, hc, ?_⟩
    change ν (φ (π c)) = σ
    rw [hcw, map_mul, map_mul, map_mul, map_mul, map_inv, map_inv, hνx, hSigcomm _ σ,
      mul_inv_cancel_right]
  have : Finite Sigma := Nat.finite_of_card_ne_zero hd.pos.ne'
  have hstr :=
    CFSG.Wreathed.BaseFourCentralizerStructure.sylow_and_base_four_group_centralizer_structure
      n hn S e
  have hsplit := hstr.centralizer_split
  have hZE := hstr.centralizer_commuting
  have hZS : CFSG.Wreathed.modelCenter S e ≤ (S : Subgroup N) := by
    rw [← CFSG.Wreathed.wreathModelHom_range S e]
    exact Subgroup.map_le_range _ _
  have hZnorm : CFSG.Wreathed.modelCenter S e ≤ Subgroup.normalizer (E : Set N) :=
    hZE.trans (Subgroup.centralizer_le_normalizer _)
  have hEtop : E.map ω = ⊤ := by
    refine eq_top_iff.mpr fun σ _ => ?_
    obtain ⟨c, hc, hcσ⟩ := hsurjC σ
    have hc' : c ∈ ((CFSG.Wreathed.modelCenter S e ⊔ E : Subgroup N) : Set N) := by
      have h1 : c ∈ Subgroup.centralizer (S : Set N) := hc
      rw [hsplit] at h1
      exact h1
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hZnorm] at hc'
    obtain ⟨z, hz, k, hk, rfl⟩ := Set.mem_mul.mp hc'
    obtain ⟨j, hj⟩ := S.isPGroup' ⟨z, hZS hz⟩
    have hz1 : ω z = 1 := map_eq_one_of_pow_two_pow hd ω (k := j) (congrArg Subtype.val hj)
    refine ⟨k, hk, ?_⟩
    rw [map_mul, hz1, one_mul] at hcσ
    exact hcσ
  refine ⟨hCmap, hker, hEmap, hEtop, ?_⟩
  rw [Subgroup.relIndex, ← MonoidHom.ker_domRestrict, Subgroup.index_ker,
    MonoidHom.domRestrict_range, hEtop, Subgroup.card_top]

end CFSG.Wreathed.SylowCentralizerOddField
