module

public import CFSG.LocalAnalysis.AGLEmbedding.ThreeCentLieTwoOFix
public import CFSG.RankThree.PartOne.KC.OrthogonalSelfDualBlock
public import CFSG.RankThree.PartOne.KC.OrthogonalFixedBlock
public import CFSG.RankThree.PartOne.KC.OrthogonalBlockProduct
import CFSG.RankThree.PartOne.KC.OrthogonalFixedRestrict
import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LocalAnalysis.AGLEmbedding.ThreeCentLieTwoBlocks

public section

namespace CFSG.AGLEmbedding

open Polynomial Module QuadraticMap CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal

variable {K : Type} [Field K]

theorem reciprocalPolynomial_X_sq_add_X_add_one :
    reciprocalPolynomial (X ^ 2 + X + 1 : K[X]) = X ^ 2 + X + 1 := by
  have hd : (X ^ 2 + X + 1 : K[X]).natDegree = 2 := by compute_degree!
  have hX : reflect 2 (X : K[X]) = X := by
    rw [← pow_one (X : K[X]), reflect_monomial]
    rfl
  have h0 : (X ^ 2 + X + 1 : K[X]).coeff 0 = 1 := by simp
  have hrev : (X ^ 2 + X + 1 : K[X]).reverse = X ^ 2 + X + 1 := by
    rw [Polynomial.reverse, hd]
    simp [reflect_add, reflect_monomial, hX]
    ring
  rw [reciprocalPolynomial, h0, hrev, inv_one, map_one, one_mul]

theorem eq_X_sq_add_X_add_one_of_dvd (hK : Nat.card K = 2) {h : K[X]} (hirr : Irreducible h)
    (hmon : h.Monic) (hdvd : h ∣ X ^ 3 - C 1) (hX : h ≠ X - 1) : h = X ^ 2 + X + 1 := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 1)
    (by rw [← Nat.card_eq_fintype_card, hK, pow_one])
  have h01 : ∀ μ : K, μ = 0 ∨ μ = 1 := fun μ => by
    by_contra hμ
    push Not at hμ
    have hsub : ({0, 1, μ} : Finset K).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [Ne.symm hμ.1]),
        Finset.card_pair (Ne.symm hμ.2)]
    have := Finset.card_le_univ ({0, 1, μ} : Finset K)
    rw [hsub, ← Nat.card_eq_fintype_card, hK] at this
    omega
  have hdeg : (X ^ 2 + X + 1 : K[X]).natDegree = 2 := by compute_degree!
  have hqirr : Irreducible (X ^ 2 + X + 1 : K[X]) := by
    refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot (by rw [hdeg]; simp)
      fun μ hμ => ?_
    have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
    rcases h01 μ with rfl | rfl
    · simp at hμ
    · simp only [IsRoot, eval_add, eval_pow, eval_X, eval_one] at hμ
      have : (1 : K) ^ 2 + 1 + 1 = 1 := by
        rw [one_pow, add_assoc, ← two_mul, h2, mul_one, add_zero]
      rw [this] at hμ
      exact one_ne_zero hμ
  have h1 : h ∣ (X - C 1) * (X ^ 2 + X + 1) := by
    convert hdvd using 1
    simp only [map_one]
    ring
  rcases hirr.prime.dvd_or_dvd h1 with h2 | h2
  · exact absurd (eq_of_monic_of_associated hmon (monic_X_sub_C 1)
      (hirr.associated_of_dvd (irreducible_X_sub_C 1) h2) |>.trans (by rw [map_one])) hX
  · exact eq_of_monic_of_associated hmon (by monicity!) (hirr.associated_of_dvd hqirr h2)

variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem exists_perfect_of_selfDual_orth [Finite K] (hK : Nat.card K = 2)
    {Q : QuadraticForm K V} {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q 3 x) {h : K[X]}
    [Fact (Irreducible h)] (hh : h ∈ primaryFactors x.toLinearMap) (hX : h ≠ X - 1)
    (hq : h = X ^ 2 + X + 1) {g : V ≃ₗ[K] V} (hg : g ∈ supportedBlock Q x h) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hgp : g ^ p = 1) (hg1 : g ≠ 1) :
    ∃ P : Subgroup (V ≃ₗ[K] V), P ≤ isometryCentralizer Q x ∧ ⁅P, P⁆ = P ∧ P ≠ ⊥ := by
  have hself : h = reciprocalPolynomial h := by rw [hq, reciprocalPolynomial_X_sq_add_X_add_one]
  obtain ⟨d, H, hdeg, -, htr, haddl, haddr, hsmull, hsmulr, hsymm⟩ :=
    hx.exists_selfDual_hermitian (by decide) hh hX hself
  have h2 : h.natDegree = 2 := by rw [hq]; compute_degree!
  have hd : d = 1 := by omega
  have hirr := irreducible_of_mem_primaryFactors hh
  have hE4 : Nat.card (AdjoinRoot h) = 2 ^ (2 * 1) := by
    have : Module.Finite K (AdjoinRoot h) := (AdjoinRoot.powerBasis hirr.ne_zero).finite
    rw [Module.natCard_eq_pow_finrank (K := K), (AdjoinRoot.powerBasis hirr.ne_zero).finrank,
      AdjoinRoot.powerBasis_dim, h2, hK]
  have hE : UnitaryFieldData 2 1 (AdjoinRoot h) := ⟨Nat.prime_two, le_rfl, hE4⟩
  have hbar : ∀ c : AdjoinRoot h, hE.bar c = frobPow K (AdjoinRoot h) d c := fun c => by
    rw [UnitaryFieldData.bar_apply, frobPow_apply, hK, hd]
  let Hf : primaryComponent x.toLinearMap h →ₛₗ[hE.bar] primaryComponent x.toLinearMap h →ₗ[
      AdjoinRoot h] AdjoinRoot h :=
    LinearMap.mk₂'ₛₗ hE.bar (RingHom.id _) H haddl (fun c u w => by
      rw [hsmull, hbar, smul_eq_mul]) haddr (fun c u w => by rw [hsmulr]; rfl)
  have hHf : Hf.IsSymm := ⟨fun u w => by
    change hE.bar (H u w) = H w u
    rw [hsymm u w, hbar]⟩
  have hHfl : Hf.SeparatingLeft := fun u hu => by
    refine Subtype.ext (hx.eq_zero_of_polar_selfdual hh hself u.2 fun w hw => ?_)
    have h1 := htr u ⟨w, hw⟩ 1
    rw [mul_one, one_smul] at h1
    rw [← h1]
    change Algebra.trace K (AdjoinRoot h) (Hf u ⟨w, hw⟩) = 0
    rw [hu, map_zero]
  have hrange : ∀ γ : BlockGL x h, γ ∈ (blockGL Q x h).range ↔ γ ∈ sesqUnitaryGroup Hf :=
    fun γ => (hx.mem_range_blockGL_selfDual_iff hh hX hself H htr γ).trans (by
      rw [mem_sesqUnitaryGroup]
      exact Iff.rfl)
  have hinj := hx.blockGL_injective hh
  let g' : supportedBlock Q x h := ⟨g, hg⟩
  have hγU : blockGL Q x h g' ∈ sesqUnitaryGroup Hf := (hrange _).mp ⟨g', rfl⟩
  have hq' := isQuasisimple_sesqSU_of_prime_order hE (Or.inl rfl) hHf hHfl
    (g := ⟨blockGL Q x h g', hγU⟩) hp hp5
    (Subtype.ext (by
      rw [Subgroup.coe_pow, ← map_pow, show g' ^ p = 1 from Subtype.ext (by simpa using hgp),
        map_one, Subgroup.coe_one]))
    (fun h1 => hg1 (congrArg Subtype.val (hinj ((congrArg Subtype.val h1).trans
      (map_one (blockGL Q x h)).symm))))
  have hSU : sesqSpecialUnitaryGroup Hf ≤ (blockGL Q x h).range := fun γ hγ =>
    (hrange γ).mpr (sesqSpecialUnitaryGroup_le Hf hγ)
  set L := (sesqSpecialUnitaryGroup Hf).comap (blockGL Q x h)
  have hLmap : L.map (blockGL Q x h) = sesqSpecialUnitaryGroup Hf :=
    Subgroup.map_comap_eq_self hSU
  have hL : CFSG.IsQuasisimple L := CFSG.LocalCores.isQuasisimple_of_mulEquiv
    ((Subgroup.equivMapOfInjective L _ hinj).trans (MulEquiv.subgroupCongr hLmap)).symm hq'
  obtain ⟨h1, h2⟩ := perfect_map_of_isQuasisimple (Subgroup.subtype_injective _) hL
  refine ⟨_, ?_, h1, h2⟩
  rintro _ ⟨s, -, rfl⟩
  exact supportedBlock_le_isometryCentralizer _ s.2

open scoped _root_.Classical in
theorem exists_perfect_of_isometryCentralizer_orth (hK : Nat.card K = 2)
    {Q : QuadraticForm K V} (hQ : (polarBilin Q).Nondegenerate) {x : V ≃ₗ[K] V}
    (hxO : x ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hx3 : x ^ 3 = 1)
    {y : V ≃ₗ[K] V} (hy : y ∈ isometryCentralizer Q x) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hyp : y ^ p = 1) (hy1 : y ≠ 1) :
    ∃ P : Subgroup (V ≃ₗ[K] V), P ≤ isometryCentralizer Q x ∧ ⁅P, P⁆ = P ∧ P ≠ ⊥ := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 1)
    (by rw [← Nat.card_eq_fintype_card (α := K), hK, pow_one])
  have h3K : ((3 : ℕ) : K) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff K 2]
    norm_num
  have hx : OddOrderIsometry Q 3 x := ⟨hxO, hx3, h3K, fun v hv => hQ.1 v hv⟩
  obtain ⟨Rep, hRep⟩ := hx.exists_orbitRepresentatives
  rw [← hx.blocks_iSup_eq hRep] at hy
  obtain ⟨⟨h, hhR⟩, g, hg, hgp, hg1⟩ := exists_ne_one_mem_of_iSupIndep
    (hx.blocks_commute hRep) (hx.blocks_iSupIndep hRep) hy hyp hy1
  have hh : h ∈ primaryFactors x.toLinearMap := hRep.1 hhR
  have : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  by_cases hX : h = X - 1
  · subst hX
    let g' : supportedBlock Q x (X - 1) := ⟨g, hg⟩
    have hg'p : g' ^ p = 1 := Subtype.ext (by simpa using hgp)
    have hg'1 : g' ≠ 1 := fun h1 => hg1 (congrArg Subtype.val h1)
    set φ := fixedBlockEquiv hx
    obtain ⟨P, hP, hP1⟩ := exists_perfect_of_prime_order_orth hK
      hx.polarBilin_fixed_nondegenerate (g := φ g') hp hp5
      (by rw [← map_pow, hg'p, map_one])
      (fun h1 => hg'1 (φ.injective (h1.trans (map_one φ).symm)))
    let ψ := (supportedBlock Q x (X - 1)).subtype.comp φ.symm.toMonoidHom
    have hψ : Function.Injective ψ := (Subgroup.subtype_injective _).comp φ.symm.injective
    refine ⟨P.map ψ, ?_, by rw [← Subgroup.map_commutator, hP], fun h0 => hP1
      ((Subgroup.map_eq_bot_iff_of_injective P hψ).mp h0)⟩
    rintro _ ⟨q, -, rfl⟩
    exact supportedBlock_le_isometryCentralizer _ (φ.symm q).2
  · have hdvd : h ∣ X ^ 3 - C 1 := (mem_primaryFactors.mp hh).2.2.trans
      (minpoly.dvd K _ (by
        rw [map_sub, map_pow, aeval_X, map_one, map_one, sub_eq_zero]
        change (x ^ 3 : V ≃ₗ[K] V).toLinearMap = 1
        rw [hx3]
        rfl))
    exact exists_perfect_of_selfDual_orth hK hx hh hX (eq_X_sq_add_X_add_one_of_dvd hK
      (irreducible_of_mem_primaryFactors hh) (monic_of_mem_primaryFactors hh) hdvd hX) hg hp hp5
      hgp hg1

end CFSG.AGLEmbedding
