module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxSymplectic
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompAlgCore
public import CFSG.RankThree.PartOne.KFOUT3.CycUnits
import all CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SympInnerExport
public import CFSG.GroupTheory.CenterlessInnerCentralizer
public import CFSG.LieType.SeitzGeneration.OuterSpData
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusCentSp

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open Polynomial CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCUnitary
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.RankThree.PartOne.KCOrthogonal (reciprocalPolynomial)
open CFSG.ComponentClassification.OuterAutomorphisms

theorem exists_conj_proj_of_mem_innAutDerived_statedSp {p r ℓ f : ℕ} {K : Type} [Field K]
    [Finite K] (hp : p.Prime) (hp2 : p ≠ 2) (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (hr : 2 ≤ r) (hne : ¬ (r = 2 ∧ ℓ ^ f = 2))
    {β : MulAut (StatedProj (StatedSp r K))}
    (hβ : β ∈ innAutDerived (StatedProj (StatedSp r K))) (hβp : β ^ p = 1) :
    ∃ x : StatedSp r K, β = MulAut.conj (proj r K x) ∧ x ^ p = 1 := by
  have hinn : β ∈ inner (StatedProj (StatedSp r K)) :=
    mem_inner_of_mem_innAutDerived_statedSp hp hp2 hℓ hf hK hr hne hβ hβp
  obtain ⟨t, ht⟩ := hinn
  have hZ : Subgroup.center (StatedProj (StatedSp r K)) = ⊥ :=
    CFSG.LieType.SeitzGeneration.center_statedProj_statedSp_eq_bot (k := K) hr
  have ht_p : t ^ p = 1 := by
    apply mulAutConj_injective_of_center_eq_bot hZ
    rw [map_pow, ht, hβp, map_one]
  obtain ⟨x, hx, hxp⟩ := LieSemisimple.exists_proj_eq_pow_eq_one_sp (r := r) (K := K)
    (by omega) hp hp2 ht_p
  exact ⟨x, by rw [← ht, ← hx], hxp⟩

theorem commute_of_conj_proj_commute {r : ℕ} {K : Type} [Field K] [Finite K] (hr : 2 ≤ r)
    {x y : StatedSp r K} (hx : x ^ 3 = 1) (hy : y ^ 3 = 1)
    (h : Commute (MulAut.conj (proj r K x)) (MulAut.conj (proj r K y))) : Commute x y := by
  have hZc : (proj r K).ker ≤ Subgroup.center (StatedSp r K) := by
    rw [SymplecticHigher.ker_proj]
    exact SymplecticHigher.spScalars_le_center
  have hcop : Nat.Coprime (Nat.card (proj r K).ker) 3 := by
    rw [SymplecticHigher.ker_proj, card_spScalars_eq_gcd K (by omega : 1 ≤ r)]
    exact Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left 2 _) (by norm_num)
  have hmap : MulAut.conj (proj r K x * proj r K y) =
      MulAut.conj (proj r K y * proj r K x) := by
    rw [map_mul, map_mul]
    exact h.eq
  have hcomm : Commute (proj r K x) (proj r K y) :=
    mulAutConj_injective_of_center_eq_bot
      (CFSG.LieType.SeitzGeneration.center_statedProj_statedSp_eq_bot (k := K) hr) hmap
  exact commute_of_map_commute (proj r K) hZc hcop hy hcomm

section Eight

variable {r : ℕ} {K : Type} [Field K] [Finite K]

private theorem charP_two_of_card_eq_eight (hK8 : Nat.card K = 8) : CharP K 2 := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact charP_of_card_eq_prime_pow (p := 2) (f := 3)
    (by rw [Fintype.card_eq_nat_card, hK8]; norm_num)

private theorem three_ne_zero_of_card_eq_eight (hK8 : Nat.card K = 8) : (3 : K) ≠ 0 := by
  haveI := charP_two_of_card_eq_eight hK8
  intro h
  have hd : 2 ∣ 3 := (CharP.cast_eq_zero_iff K 2 3).1 h
  norm_num at hd

theorem eq_X_sub_one_or_X_sq_add_X_add_one_of_mem_primaryFactors (hK8 : Nat.card K = 8)
    {x : StatedSp r K} (hx3 : x ^ 3 = 1) {h : K[X]}
    (hh : h ∈ primaryFactors (spEnd x)) :
    h = X - 1 ∨ h = X ^ 2 + X + 1 := by
  have hirr := irreducible_of_mem_primaryFactors hh
  have hmon := monic_of_mem_primaryFactors hh
  have hdvd := CFSG.AGLEmbedding.ToralCensus.dvd_of_mem_primaryFactors hx3 hh
  by_cases hX : h = X - 1
  · exact Or.inl hX
  · right
    have hdvd2 := CFSG.AGLEmbedding.ToralCensus.dvd_X_sq_add_X_add_one hirr hmon hdvd hX
    haveI : CharP K 2 := charP_two_of_card_eq_eight hK8
    exact CFSG.AGLEmbedding.ToralCensus.eq_of_dvd_of_natDegree_eq_two
      (CFSG.RankThree.PartOne.KFOUT3.irreducible_quad (by rw [hK8]; norm_num))
      CFSG.AGLEmbedding.ToralCensus.monic_X_sq_add_X_add_one (dvd_refl _)
      CFSG.AGLEmbedding.ToralCensus.natDegree_X_sq_add_X_add_one hirr hmon hdvd2

theorem reciprocalPolynomial_eq_self_of_mem_primaryFactors (hK8 : Nat.card K = 8)
    {x : StatedSp r K} (hx3 : x ^ 3 = 1)
    (H : AltPrimaryData (spForm r K) (spLin r K x)) {h : K[X]}
    (hh : h ∈ primaryFactors (spEnd x)) : reciprocalPolynomial h = h := by
  rcases eq_X_sub_one_or_X_sq_add_X_add_one_of_mem_primaryFactors hK8 hx3 hh with h1 | h1
  · subst h1
    exact CFSG.RankThree.PartOne.KCOrthogonal.reciprocalPolynomial_X_sub_one
  · subst h1
    have hmem := H.reciprocal_mem hh
    rcases eq_X_sub_one_or_X_sq_add_X_add_one_of_mem_primaryFactors hK8 hx3 hmem with h2 | h2
    · exfalso
      have h0 : (X ^ 2 + X + 1 : K[X]).coeff 0 ≠ 0 := by
        simp [Polynomial.coeff_add, Polynomial.coeff_X_pow]
      have hdeg := CFSG.RankThree.PartOne.KCOrthogonal.natDegree_reciprocalPolynomial h0
      rw [h2, CFSG.AGLEmbedding.ToralCensus.natDegree_X_sq_add_X_add_one] at hdeg
      rw [show (X - 1 : K[X]) = X - C 1 by simp, natDegree_X_sub_C] at hdeg
      norm_num at hdeg
    · exact h2

theorem reciprocalOrbits_eq_X_sub_one_or_X_sq_add_X_add_one (hK8 : Nat.card K = 8)
    {x : StatedSp r K} (hx3 : x ^ 3 = 1)
    (H : AltPrimaryData (spForm r K) (spLin r K x)) {O : Set K[X]}
    (hO : O ∈ reciprocalOrbits (spEnd x)) :
    O = {X - 1} ∨ O = {X ^ 2 + X + 1} := by
  rw [reciprocalOrbits] at hO
  obtain ⟨h, hh, rfl⟩ := hO
  change ({h, reciprocalPolynomial h} : Set K[X]) = {X - 1} ∨
    ({h, reciprocalPolynomial h} : Set K[X]) = {X ^ 2 + X + 1}
  have hrec := reciprocalPolynomial_eq_self_of_mem_primaryFactors hK8 hx3 H hh
  rw [hrec, Set.pair_eq_singleton]
  rcases eq_X_sub_one_or_X_sq_add_X_add_one_of_mem_primaryFactors hK8 hx3 hh with h1 | h1
  · exact Or.inl (by rw [h1])
  · exact Or.inr (by rw [h1])

end Eight

section Components

variable {r : ℕ} {K : Type} [Field K] [Finite K]

theorem exists_component_eq_fixed_or_unitary (hK8 : Nat.card K = 8) (hr : 2 ≤ r)
    {x : StatedSp r K} (hx3 : x ^ 3 = 1) (hx1 : proj r K x ≠ 1)
    (T : Subgroup (StatedProj (StatedSp r K)))
    (hT : IsComponentOf T (fixSubgroup (MulAut.conj (proj r K x)))) :
    (T = (spSupported x {X - 1}).map (proj r K) ∧
        Group.IsPerfect ↥(spSupported x {X - 1})) ∨
      T = (⁅spSupported x {X ^ 2 + X + 1}, spSupported x {X ^ 2 + X + 1}⁆).map (proj r K) := by
  classical
  have hK3 : Nat.card K = 2 ^ 3 := by rw [hK8]; norm_num
  have hne' : ¬ (r = 2 ∧ 2 ^ 3 = 2) := by rintro ⟨-, h⟩; norm_num at h
  have h3 := three_ne_zero_of_card_eq_eight (K := K) hK8
  have H : AltPrimaryData (spForm r K) (spLin r K x) := altPrimaryData_spLin h3 hx3
  have hxne : x ≠ 1 := fun h => hx1 (by rw [h, map_one])
  have hxord : orderOf x = 3 := orderOf_eq_prime hx3 hxne
  let a : StatedProj (StatedSp r K) := proj r K x
  have ha : orderOf a = 3 := orderOf_eq_prime (by rw [← map_pow, hx3, map_one]) hx1
  have blocks : SpPrimaryBlocks 2 3 3 x a :=
    (symplectic_cross_prime_primary_centralizer_blocks (K := K) (r := r) (ℓ := 2) (f := 3)
      (p := 3) Nat.prime_two (by norm_num) hK3 Nat.prime_three (by norm_num) (by norm_num)
      (by omega) a ha).2 x rfl hxord
  have hZc : (proj r K).ker ≤ Subgroup.center (StatedSp r K) := by
    rw [SymplecticHigher.ker_proj]
    exact SymplecticHigher.spScalars_le_center
  haveI : Finite ↥(reciprocalOrbits (spEnd x)) :=
    (Set.Finite.image _ (Finset.finite_toSet _)).to_subtype
  haveI : Fintype ↥(reciprocalOrbits (spEnd x)) := Fintype.ofFinite _
  obtain ⟨hcomm, -, hjoin⟩ := blocks.directProduct
  have hcomp := components_conj_of_orbit_family (proj r K) SymplecticHigher.proj_surjective hZc x
    (fun O : ↥(reciprocalOrbits (spEnd x)) => spSupported x (O : Set K[X]))
    (fun i j hij p hp q hq => hcomm i.1 i.2 j.1 j.2 (fun h => hij (Subtype.ext h)) p hp q hq)
    hjoin
    (fun O => LieSemisimple.quasisimple_or_solvable_spSupported (by norm_num) (by norm_num)
      H.squarefree blocks O)
  obtain ⟨O, -, hTeq⟩ := hcomp T hT
  have hclass := reciprocalOrbits_eq_X_sub_one_or_X_sq_add_X_add_one hK8 hx3 H O.2
  rcases hclass with hO | hO
  ·
    left
    obtain ⟨h, hh, hpair⟩ : ∃ h ∈ primaryFactors (spEnd x),
        ({h, reciprocalPolynomial h} : Set K[X]) = (O : Set K[X]) := O.2
    have hmem : h ∈ ({X - 1} : Set K[X]) := by
      rw [← hO, ← hpair]
      exact Set.mem_insert h _
    have hhX : h = X - 1 := by simpa using hmem
    subst hhX
    obtain ⟨φ, -⟩ := blocks.fixedFactor hh
    haveI : Nontrivial (primaryComponent (spEnd x) (X - 1)) :=
      Submodule.nontrivial_iff_ne_bot.mpr (primaryComponent_ne_bot H.squarefree hh)
    obtain ⟨s, hs, ⟨e⟩⟩ :=
      CFSG.RankThree.PartOne.KCSpIsotypic.exists_mulEquiv_sesqUnitaryGroup_statedSp
        (B := (spForm r K).restrict (primaryComponent (spEnd x) (X - 1)))
        (fun v => spForm_isAlt (v : Fin r ⊕ Fin r → K)) blocks.fixed_nondegenerate
    have hs1 : 1 ≤ s := by
      have := Module.finrank_pos (R := K) (M := primaryComponent (spEnd x) (X - 1))
      omega
    haveI : Group.IsPerfect ↥(StatedSp s K) :=
      (CFSG.LieType.Universal.Symplectic.isQuasisimple s K hs1
        (Or.inl (Or.inr (by rw [hK8]; norm_num)))).1
    have hperf : Group.IsPerfect ↥(spSupported x {X - 1}) :=
      Group.IsPerfect.ofSurjective (f := (φ.trans e).symm.toMonoidHom) (φ.trans e).symm.surjective
    refine ⟨?_, hperf⟩
    rw [hTeq, hO, Subgroup.commutator_eq_self]
  ·
    right
    rw [hTeq, hO]

end Components

section Decomposition

variable {r : ℕ} {K : Type} [Field K] {ℓ f p : ℕ} {x y : StatedSp r K}
  {a : StatedProj (StatedSp r K)}

theorem exists_mem_spSupported_commute_of_commute (blocks : SpPrimaryBlocks ℓ f p x a)
    (hy : Commute y x) (O : ↥(reciprocalOrbits (spEnd x))) :
    ∃ yO ∈ spSupported x (O : Set K[X]),
      ∀ g ∈ spSupported x (O : Set K[X]), Commute (yO⁻¹ * y) g := by
  classical
  haveI : Finite ↥(reciprocalOrbits (spEnd x)) :=
    (Set.Finite.image _ (Finset.finite_toSet _)).to_subtype
  haveI : Fintype ↥(reciprocalOrbits (spEnd x)) := Fintype.ofFinite _
  obtain ⟨hcomm, -, hjoin⟩ := blocks.directProduct
  let H : ↥(reciprocalOrbits (spEnd x)) → Subgroup (StatedSp r K) :=
    fun O => spSupported x (O : Set K[X])
  have hpair : Pairwise fun i j : ↥(reciprocalOrbits (spEnd x)) =>
      ∀ u v : StatedSp r K, u ∈ H i → v ∈ H j → Commute u v := by
    intro i j hij u v hu hv
    exact hcomm i.1 i.2 j.1 j.2 (fun h => hij (Subtype.ext h)) u hu v hv
  have hyc : y ∈ Subgroup.centralizer ({x} : Set (StatedSp r K)) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hy
  have hyrange : y ∈ (Subgroup.noncommPiCoprod hpair).range := by
    rw [Subgroup.noncommPiCoprod_range, hjoin]
    exact hyc
  obtain ⟨f, hf⟩ := hyrange
  refine ⟨(f O : StatedSp r K), (f O).2, ?_⟩
  have hmain := Finset.noncommProd_erase_mul
    (Finset.univ : Finset ↥(reciprocalOrbits (spEnd x))) (Finset.mem_univ O)
    (fun i => (f i : StatedSp r K))
    (fun i _ j _ hij => hpair hij (f i) (f j) (f i).2 (f j).2)
  have hy : y = (Finset.univ.erase O).noncommProd (fun i => (f i : StatedSp r K))
      (fun i _ j _ hij => hpair hij (f i) (f j) (f i).2 (f j).2) *
      (f O : StatedSp r K) := by
    rw [← hf, Subgroup.noncommPiCoprod_apply, ← hmain]
  have hcommFO : Commute (f O : StatedSp r K)
      ((Finset.univ.erase O).noncommProd (fun i => (f i : StatedSp r K))
        (fun i _ j _ hij => hpair hij (f i) (f j) (f i).2 (f j).2)) := by
    apply Finset.noncommProd_commute
    intro i hi
    have hne : i ≠ O := (Finset.mem_erase.mp hi).1
    exact hpair (Ne.symm hne) (f O) (f i) (f O).2 (f i).2
  have hz : (f O : StatedSp r K)⁻¹ * y =
      (Finset.univ.erase O).noncommProd (fun i => (f i : StatedSp r K))
        (fun i _ j _ hij => hpair hij (f i) (f j) (f i).2 (f j).2) := by
    rw [hy, ← hcommFO.eq]
    group
  intro g hg
  rw [hz]
  exact (Finset.noncommProd_commute (Finset.univ.erase O) (fun i => (f i : StatedSp r K)) _
    g (fun i hi => by
      have hne : i ≠ O := (Finset.mem_erase.mp hi).1
      exact hpair (Ne.symm hne) g (f i) hg (f i).2)).symm

end Decomposition

section InnerCase

variable {r : ℕ} {K : Type} [Field K] [Finite K]

private theorem spSupported_singleton_eq_bot_of_not_mem {h : K[X]} {x : StatedSp r K}
    (H : AltPrimaryData (spForm r K) (spLin r K x))
    (hX : h ∉ primaryFactors (spEnd x)) :
    spSupported x {(h : K[X])} = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  refine Subgroup.mem_bot.mpr ?_
  have hfix : ∀ k ∈ primaryFactors (spEnd x), ∀ v ∈ primaryComponent (spEnd x) k,
      spEnd (g : StatedSp r K) v = v := by
    intro k hk v hv
    exact (mem_spSupported.mp hg).2 k hk (by rintro rfl; exact hX hk) v hv
  have hsp : spEnd (g : StatedSp r K) = 1 := by
    apply ext_primaryComponent H.squarefree
    intro k hk v hv
    rw [hfix k hk v hv, Module.End.one_apply]
  have hgl : spLin r K (g : StatedSp r K) = 1 := by
    apply Units.val_injective
    simpa [spEnd] using hsp
  exact spLin_injective (by rw [hgl, map_one])

theorem exists_conj_subgroupStabRestrict_of_fixedComponent (hK8 : Nat.card K = 8)
    {x y : StatedSp r K} (hx3 : x ^ 3 = 1) (hcomm : Commute x y)
    {a : StatedProj (StatedSp r K)} (blocks : SpPrimaryBlocks 2 3 3 x a)
    (T : Subgroup (StatedProj (StatedSp r K)))
    (hT : IsComponentOf T (fixSubgroup (MulAut.conj (proj r K x))))
    (hTfix : T = (spSupported x {X - 1}).map (proj r K))
    (hTy : (MulAut.conj (proj r K y)) ∈ CFSG.GroupActions.subgroupStabAut T) :
    ∃ t : ↥T, CFSG.GroupActions.subgroupStabRestrict T
      ⟨MulAut.conj (proj r K y), hTy⟩ = MulAut.conj t := by
  classical
  have h3 := three_ne_zero_of_card_eq_eight (K := K) hK8
  have H : AltPrimaryData (spForm r K) (spLin r K x) := altPrimaryData_spLin h3 hx3
  haveI : Nontrivial ↥T := CFSG.LocalCores.isQuasisimple_nontrivial
    (CFSG.Fischer.Classification.Recognition.localCores_isQuasisimple hT.2.2)
  have hTne : T ≠ ⊥ := T.nontrivial_iff_ne_bot.mp inferInstance
  have hAne : spSupported x {X - 1} ≠ ⊥ := by
    intro hbot
    exact hTne (by rw [hTfix, hbot, Subgroup.map_bot])
  have hh : (X - 1 : K[X]) ∈ primaryFactors (spEnd x) := by
    by_contra hX
    exact hAne (spSupported_singleton_eq_bot_of_not_mem (h := X - 1) H hX)
  have hO : ({X - 1} : Set K[X]) ∈ reciprocalOrbits (spEnd x) := by
    rw [reciprocalOrbits]
    exact ⟨X - 1, hh, by
      change ({X - 1, reciprocalPolynomial (X - 1)} : Set K[X]) = {X - 1}
      rw [CFSG.RankThree.PartOne.KCOrthogonal.reciprocalPolynomial_X_sub_one,
        Set.pair_eq_singleton]⟩
  obtain ⟨y₁, hy₁mem, hy₁comm⟩ :=
    exists_mem_spSupported_commute_of_commute blocks hcomm.symm ⟨{X - 1}, hO⟩
  have hconj_eq : ∀ g ∈ spSupported x {X - 1},
      y * g * y⁻¹ = (y₁ : StatedSp r K) * g * (y₁ : StatedSp r K)⁻¹ := by
    intro g hg
    have hc : Commute ((y₁ : StatedSp r K)⁻¹ * y) g := hy₁comm g hg
    calc y * g * y⁻¹
        = (y₁ : StatedSp r K) * (((y₁ : StatedSp r K)⁻¹ * y) * g *
            ((y₁ : StatedSp r K)⁻¹ * y)⁻¹) * (y₁ : StatedSp r K)⁻¹ := by group
      _ = (y₁ : StatedSp r K) * g * (y₁ : StatedSp r K)⁻¹ := by rw [hc.mul_inv_cancel]
  refine ⟨⟨proj r K (y₁ : StatedSp r K), ?_⟩, ?_⟩
  · rw [hTfix]
    exact Subgroup.mem_map_of_mem (proj r K) hy₁mem
  · refine MulEquiv.ext fun t => ?_
    have hmem : (t : StatedProj (StatedSp r K)) ∈
        (spSupported x {X - 1}).map (proj r K) := by rw [← hTfix]; exact t.2
    obtain ⟨g, hg, hgt⟩ := hmem
    have hmemT : (proj r K g) ∈ T := by
      rw [hTfix]
      exact Subgroup.mem_map_of_mem (proj r K) hg
    have ht : t = ⟨proj r K g, hmemT⟩ := Subtype.ext hgt.symm
    subst ht
    apply Subtype.ext
    rw [CFSG.GroupActions.subgroupStabRestrict_apply]
    simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk]
    simpa only [map_mul, map_inv] using congrArg (proj r K) (hconj_eq g hg)

theorem centerQuotientHom_mem_innAutDerived_of_fixedComponent (hK8 : Nat.card K = 8)
    {x y : StatedSp r K} (hx3 : x ^ 3 = 1) (hcomm : Commute x y)
    {a : StatedProj (StatedSp r K)} (blocks : SpPrimaryBlocks 2 3 3 x a)
    (T : Subgroup (StatedProj (StatedSp r K)))
    (hT : IsComponentOf T (fixSubgroup (MulAut.conj (proj r K x))))
    (hTfix : T = (spSupported x {X - 1}).map (proj r K))
    (hTy : (MulAut.conj (proj r K y)) ∈ CFSG.GroupActions.subgroupStabAut T) :
    CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥T
      (CFSG.GroupActions.subgroupStabRestrict T
      ⟨MulAut.conj (proj r K y), hTy⟩) ∈ innAutDerived (↥T ⧸ Subgroup.center ↥T) := by
  obtain ⟨t, ht⟩ := exists_conj_subgroupStabRestrict_of_fixedComponent hK8 hx3 hcomm blocks T hT
    hTfix hTy
  rw [ht, CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_conj]
  exact inner_le_innAutDerived (↥T ⧸ Subgroup.center ↥T) ⟨_, rfl⟩

end InnerCase

section UnitaryComponent

variable {r : ℕ} {K : Type} [Field K] [Finite K]

private theorem sesqSpecialUnitaryGroup_commutator_eq_top {E W : Type} [Field E]
    [AddCommGroup W] [Module E W] [FiniteDimensional E W] {f : ℕ}
    {hE : UnitaryFieldData 2 f E} (Hf : W →ₛₗ[hE.bar] W →ₗ[E] E)
    (hHf : Hf.IsSymm) (hHfl : Hf.SeparatingLeft) (hf : 3 ≤ f)
    (hm : 2 ≤ Module.finrank E W) :
    commutator ↥(sesqSpecialUnitaryGroup Hf) = ⊤ := by
  refine Group.isPerfect_def.mp
    (CFSG.RankThree.PartOne.KCUnitary.isQuasisimple_sesqSpecialUnitaryGroup_of_two_le
      hE hHf hHfl hm ⟨?_, ?_⟩).1
  · intro _
    calc 4 ≤ 2 ^ 3 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  · intro _
    calc 3 ≤ 2 ^ 3 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf

end UnitaryComponent

section UnitaryBlock

variable {r : ℕ} {K : Type} [Field K] [Finite K]

private theorem unitaryComponent_conjLaw {E W : Type*} [Field E] [AddCommGroup W] [Module E W]
    {σ : E →+* E} {Hf : W →ₛₗ[σ] W →ₗ[E] E} {A : Subgroup (StatedSp r K)}
    {T0 : Subgroup (StatedProj (StatedSp r K))}
    {y : StatedSp r K} (φ : A ≃* ↥(sesqUnitaryGroup Hf)) {g : ↥(sesqUnitaryGroup Hf)}
    {y_h : StatedSp r K}
    (hy_h_mem : y_h ∈ A) (hy_h_comm : ∀ g' ∈ A, Commute (y_h⁻¹ * y) g')
    {ψ : ↥(sesqSpecialUnitaryGroup Hf) →* StatedSp r K}
    (hψ_spec : ∀ s, ψ s =
      (φ.symm (Subgroup.inclusion (sesqSpecialUnitaryGroup_le Hf) s) : ↥A))
    (hψ_mem : ∀ s, ψ s ∈ A)
    (hTy0 : (MulAut.conj (proj r K y)) ∈ CFSG.GroupActions.subgroupStabAut T0)
    {π' : ↥(sesqSpecialUnitaryGroup Hf) →* ↥T0}
    (hπ' : ∀ s, ((π' s : ↥T0) : StatedProj (StatedSp r K)) = proj r K (ψ s))
    (hg : g = φ ⟨y_h, hy_h_mem⟩) :
    ∀ s : ↥(sesqSpecialUnitaryGroup Hf),
      CFSG.GroupActions.subgroupStabRestrict T0 ⟨MulAut.conj (proj r K y), hTy0⟩
          (π' s) = π' (sesqSUConj (B := Hf) g s) := by
  intro s
  have hψ_conj : ψ (sesqSUConj (B := Hf) g s) = y_h * ψ s * y_h⁻¹ := by
    have h1 : (φ.symm (Subgroup.inclusion (sesqSpecialUnitaryGroup_le Hf)
          (sesqSUConj (B := Hf) g s)) : ↥A) =
        (⟨y_h, hy_h_mem⟩ : ↥A) *
          (φ.symm (Subgroup.inclusion (sesqSpecialUnitaryGroup_le Hf) s) : ↥A) *
          (⟨y_h, hy_h_mem⟩ : ↥A)⁻¹ := by
      apply φ.injective
      rw [MulEquiv.apply_symm_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
      rw [show φ ⟨y_h, hy_h_mem⟩ = g from hg.symm]
      apply Subtype.ext
      rw [Subgroup.coe_inclusion, sesqSUConj_apply]
      simp only [Subgroup.coe_inclusion, Subgroup.coe_mul, Subgroup.coe_inv,
        Subgroup.coe_mk]
    rw [hψ_spec (sesqSUConj (B := Hf) g s), hψ_spec s, h1]
    rfl
  have hy_conj : y * ψ s * y⁻¹ = y_h * ψ s * y_h⁻¹ := by
    have hc : Commute (y_h⁻¹ * y) (ψ s) := hy_h_comm (ψ s) (hψ_mem s)
    calc y * ψ s * y⁻¹
        = y_h * ((y_h⁻¹ * y) * ψ s * (y_h⁻¹ * y)⁻¹) * y_h⁻¹ := by group
      _ = y_h * ψ s * y_h⁻¹ := by rw [hc.mul_inv_cancel]
  apply Subtype.ext
  rw [CFSG.GroupActions.subgroupStabRestrict_apply]
  simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk]
  rw [hπ' s, hπ' (sesqSUConj (B := Hf) g s), hψ_conj]
  simpa only [map_mul, map_inv] using congrArg (proj r K) hy_conj

private theorem unitaryBlock_perfect {E W : Type} [Field E] [AddCommGroup W] [Module E W]
    [FiniteDimensional E W] {f : ℕ} {hE : UnitaryFieldData 2 f E}
    {Hf : W →ₛₗ[hE.bar] W →ₗ[E] E} {A : Subgroup (StatedSp r K)}
    (φ : A ≃* ↥(sesqUnitaryGroup Hf)) (hHf : Hf.IsSymm) (hHfl : Hf.SeparatingLeft)
    (hf : 3 ≤ f)
    (hTne : (⁅A, A⁆).map (proj r K) ≠ ⊥) :
    2 ≤ Module.finrank E W ∧ commutator ↥(sesqSpecialUnitaryGroup Hf) = ⊤ := by
  have hm2 : 2 ≤ Module.finrank E W := by
    by_contra hlt
    have hle : Module.finrank E W ≤ 1 := by omega
    have hUcomm : ∀ u v : ↥(sesqUnitaryGroup Hf), u * v = v * u := by
      intro u v
      apply Subtype.ext
      apply Units.ext
      exact (CFSG.RankThree.PartOne.KCUnitary.End_commute_of_finrank_le_one hle _ _).eq
    haveI : IsMulCommutative ↥(sesqUnitaryGroup Hf) := ⟨⟨hUcomm⟩⟩
    have hUbot : commutator ↥(sesqUnitaryGroup Hf) = ⊥ := by
      rw [commutator_eq_bot_iff_center_eq_top, Subgroup.center_eq_top]
    haveI : IsMulCommutative ↥A :=
      ⟨⟨fun a b => φ.injective (by
        rw [map_mul, map_mul]
        exact hUcomm (φ a) (φ b))⟩⟩
    have hAbot : ⁅A, A⁆ = ⊥ := by
      rw [Subgroup.commutator_self_eq_bot_iff]
      exact inferInstance
    exact hTne (by rw [hAbot]; simp)
  exact ⟨hm2, sesqSpecialUnitaryGroup_commutator_eq_top (E := E) (W := W) (f := f)
    (hE := hE) Hf hHf hHfl hf hm2⟩

private theorem centerQuotientHom_mem_innAutDerived_of_unitaryComponent_literal
    (hK8 : Nat.card K = 8)
    {x y : StatedSp r K} (hr : 2 ≤ r) (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1)
    (hcomm : Commute x y)
    {a : StatedProj (StatedSp r K)} (blocks : SpPrimaryBlocks 2 3 3 x a)
    (hT : IsComponentOf ((⁅spSupported x {X ^ 2 + X + 1},
      spSupported x {X ^ 2 + X + 1}⁆).map (proj r K))
      (fixSubgroup (MulAut.conj (proj r K x))))
    (hTy : (MulAut.conj (proj r K y)) ∈ CFSG.GroupActions.subgroupStabAut
      ((⁅spSupported x {X ^ 2 + X + 1},
        spSupported x {X ^ 2 + X + 1}⁆).map (proj r K))) :
    CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom
      ↥((⁅spSupported x {X ^ 2 + X + 1},
        spSupported x {X ^ 2 + X + 1}⁆).map (proj r K))
      (CFSG.GroupActions.subgroupStabRestrict
        ((⁅spSupported x {X ^ 2 + X + 1},
          spSupported x {X ^ 2 + X + 1}⁆).map (proj r K))
        ⟨MulAut.conj (proj r K y), hTy⟩) ∈
      innAutDerived (↥((⁅spSupported x {X ^ 2 + X + 1},
        spSupported x {X ^ 2 + X + 1}⁆).map (proj r K)) ⧸
        Subgroup.center ↥((⁅spSupported x {X ^ 2 + X + 1},
          spSupported x {X ^ 2 + X + 1}⁆).map (proj r K))) := by
  classical
  let T0 : Subgroup (StatedProj (StatedSp r K)) :=
    (⁅spSupported x {X ^ 2 + X + 1}, spSupported x {X ^ 2 + X + 1}⁆).map (proj r K)
  have hT0 : IsComponentOf T0 (fixSubgroup (MulAut.conj (proj r K x))) := hT
  have hTy0 : (MulAut.conj (proj r K y)) ∈ CFSG.GroupActions.subgroupStabAut T0 := hTy
  have h3 := three_ne_zero_of_card_eq_eight (K := K) hK8
  have H : AltPrimaryData (spForm r K) (spLin r K x) := altPrimaryData_spLin h3 hx3
  have hTne : T0 ≠ ⊥ := by
    refine (Subgroup.nontrivial_iff_ne_bot T0).mp ?_
    exact CFSG.LocalCores.isQuasisimple_nontrivial
      (CFSG.Fischer.Classification.Recognition.localCores_isQuasisimple hT0.2.2)
  have hh : (X ^ 2 + X + 1 : K[X]) ∈ primaryFactors (spEnd x) := by
    by_contra hX
    have hbot : spSupported x {X ^ 2 + X + 1} = ⊥ :=
      spSupported_singleton_eq_bot_of_not_mem (h := X ^ 2 + X + 1) H hX
    refine hTne ?_
    change (⁅spSupported x {X ^ 2 + X + 1},
      spSupported x {X ^ 2 + X + 1}⁆).map (proj r K) = ⊥
    rw [hbot]
    simp
  let h : primaryFactors (spEnd x) := ⟨X ^ 2 + X + 1, hh⟩
  let A : Subgroup (StatedSp r K) := spSupported x {(h : K[X])}
  have hself : reciprocalPolynomial (h : K[X]) = h :=
    reciprocalPolynomial_eq_self_of_mem_primaryFactors hK8 hx3 H hh
  have hXne : (h : K[X]) ≠ X - 1 := by
    intro e
    have hdeg := congrArg Polynomial.natDegree e
    rw [show (h : K[X]) = X ^ 2 + X + 1 from rfl,
      CFSG.AGLEmbedding.ToralCensus.natDegree_X_sq_add_X_add_one,
      show (X - 1 : K[X]) = X - C 1 by simp, natDegree_X_sub_C] at hdeg
    norm_num at hdeg
  obtain ⟨d, hdeg, _, σ, hσpow, _, hσσ, hσroot, hσadj, hE, hbar,
    Hf, hHf, hHfl, _, ⟨basis, _⟩, φ, hφ⟩ :=
    (blocks.selfDual h hXne hself).exists_half
  have hd1 : d = 1 := by
    change (h : K[X]).natDegree = 2 * d at hdeg
    have h2 : (h : K[X]).natDegree = 2 := by
      rw [show (h : K[X]) = X ^ 2 + X + 1 from rfl]
      exact CFSG.AGLEmbedding.ToralCensus.natDegree_X_sq_add_X_add_one
    omega
  subst hd1
  haveI : CharP K 2 := charP_two_of_card_eq_eight hK8
  haveI : Fact (Irreducible (h : K[X])) :=
    ⟨CFSG.RankThree.PartOne.KFOUT3.irreducible_quad (K := K) (by rw [hK8]; norm_num)⟩
  haveI : Finite (AdjoinRoot (h : K[X])) := hE.finite
  haveI : FiniteDimensional (AdjoinRoot (h : K[X])) (primaryComponent (spEnd x) (h : K[X])) :=
    Module.Basis.finiteDimensional_of_finite basis
  obtain ⟨hm2, hperf⟩ := unitaryBlock_perfect (hE := hE) (Hf := Hf) φ hHf hHfl
    (by norm_num : 3 ≤ 3 * 1) hTne
  have hO : ({X ^ 2 + X + 1} : Set K[X]) ∈ reciprocalOrbits (spEnd x) := by
    rw [reciprocalOrbits]
    exact ⟨X ^ 2 + X + 1, hh, by
      change ({X ^ 2 + X + 1, reciprocalPolynomial (X ^ 2 + X + 1)} : Set K[X]) =
        {X ^ 2 + X + 1}
      rw [show reciprocalPolynomial (X ^ 2 + X + 1) = X ^ 2 + X + 1 from hself,
        Set.pair_eq_singleton]⟩
  obtain ⟨y_h, hy_h_mem, hy_h_comm⟩ :=
    exists_mem_spSupported_commute_of_commute blocks hcomm.symm ⟨{X ^ 2 + X + 1}, hO⟩
  let g : ↥(sesqUnitaryGroup Hf) := φ ⟨y_h, hy_h_mem⟩
  let θ : ↥(sesqSpecialUnitaryGroup Hf) →* ↥(sesqUnitaryGroup Hf) :=
    Subgroup.inclusion (sesqSpecialUnitaryGroup_le Hf)
  let ψ : ↥(sesqSpecialUnitaryGroup Hf) →* StatedSp r K :=
    A.subtype.comp (φ.symm.toMonoidHom.comp θ)
  have hψ_inj : Function.Injective ψ :=
    Subtype.val_injective.comp (φ.symm.injective.comp
      (Subgroup.inclusion_injective (sesqSpecialUnitaryGroup_le Hf)))
  have hψ_range : ψ.range = ⁅A, A⁆ := by
    obtain ⟨-, -, -, -, hker, -⟩ :=
      CFSG.LinearGroups.unitary_full_group_order hE hHf hHfl rfl (by omega)
    have hθ : θ.range = commutator ↥(sesqUnitaryGroup Hf) := by
      refine range_eq_commutator_of_perfect θ hperf (CFSG.LinearGroups.unitaryDet Hf)
        fun u hu => ?_
      rw [hker] at hu
      exact ⟨⟨u, hu⟩, Subtype.ext rfl⟩
    exact range_comp_eq_commutator φ θ hθ
  let ψ' : ↥(sesqSpecialUnitaryGroup Hf) →* ↥⁅A, A⁆ :=
    ψ.codRestrict ⁅A, A⁆ (fun s => by
      rw [← hψ_range]
      exact ⟨s, rfl⟩)
  let π' : ↥(sesqSpecialUnitaryGroup Hf) →* ↥T0 :=
    (proj r K).subgroupMap ⁅A, A⁆ |>.comp ψ'
  have hπ'_surj : Function.Surjective π' := by
    have hψ'_surj : Function.Surjective ψ' := by
      intro u
      have hu : (u : StatedSp r K) ∈ ψ.range := by rw [hψ_range]; exact u.2
      obtain ⟨s, hs⟩ := hu
      exact ⟨s, Subtype.ext hs⟩
    exact ((proj r K).subgroupMap_surjective ⁅A, A⁆).comp hψ'_surj
  have hproj_inj : Function.Injective (proj r K) := by
    rw [← MonoidHom.ker_eq_bot_iff, SymplecticHigher.ker_proj, ← Subgroup.card_eq_one,
      card_spScalars_eq_gcd K (by omega : 1 ≤ r)]
    rw [hK8]
    norm_num
  have hπ'_inj : Function.Injective π' := by
    intro u v huv
    exact hψ_inj (hproj_inj (congrArg Subtype.val huv))
  have hker : π'.ker ≤ Subgroup.center ↥(sesqSpecialUnitaryGroup Hf) := by
    rw [(MonoidHom.ker_eq_bot_iff π').mpr hπ'_inj]
    exact bot_le
  have hψ_mem : ∀ s : ↥(sesqSpecialUnitaryGroup Hf), ψ s ∈ A := by
    intro s
    have hs : ψ s ∈ ψ.range := ⟨s, rfl⟩
    rw [hψ_range] at hs
    exact (Subgroup.commutator_le_self A) hs
  have hψ_spec : ∀ s : ↥(sesqSpecialUnitaryGroup Hf),
      ψ s = (φ.symm
        (Subgroup.inclusion (sesqSpecialUnitaryGroup_le Hf) s) : ↥A) := fun s => rfl
  have hγ : ∀ s : ↥(sesqSpecialUnitaryGroup Hf),
      CFSG.GroupActions.subgroupStabRestrict T0 ⟨MulAut.conj (proj r K y), hTy0⟩
          (π' s) = π' (sesqSUConj (B := Hf) g s) :=
    unitaryComponent_conjLaw (y := y) φ hy_h_mem hy_h_comm hψ_spec hψ_mem hTy0
      (π' := π') (fun s => rfl) rfl
  have hγp : CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥T0
      (CFSG.GroupActions.subgroupStabRestrict T0
        ⟨MulAut.conj (proj r K y), hTy0⟩) ^ 3 = 1 := by
    have hsub : (⟨MulAut.conj (proj r K y), hTy0⟩ :
        CFSG.GroupActions.subgroupStabAut T0) ^ 3 = 1 := by
      apply Subtype.ext
      change (MulAut.conj (proj r K y)) ^ 3 = 1
      rw [← map_pow, ← map_pow, hy3, map_one, map_one]
    have hγ3 : (CFSG.GroupActions.subgroupStabRestrict T0
        ⟨MulAut.conj (proj r K y), hTy0⟩) ^ 3 = 1 := by
      rw [← map_pow, hsub, map_one]
    rw [← map_pow, hγ3, map_one]
  exact centerQuotientHom_mem_innAutDerived_of_sesqSUConj
    (hE := hE) (hH := hHf) (hHl := hHfl) (hperf := hperf) (hp := Nat.prime_three)
    (hp2 := by norm_num) (g := g) (π := π') hπ'_surj hker hγ hγp

theorem centerQuotientHom_mem_innAutDerived_of_unitaryComponent (hK8 : Nat.card K = 8)
    {x y : StatedSp r K} (hr : 2 ≤ r) (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1)
    (hcomm : Commute x y)
    {a : StatedProj (StatedSp r K)} (blocks : SpPrimaryBlocks 2 3 3 x a)
    (T : Subgroup (StatedProj (StatedSp r K)))
    (hT : IsComponentOf T (fixSubgroup (MulAut.conj (proj r K x))))
    (hTuni : T = (⁅spSupported x {X ^ 2 + X + 1},
      spSupported x {X ^ 2 + X + 1}⁆).map (proj r K))
    (hTy : (MulAut.conj (proj r K y)) ∈ CFSG.GroupActions.subgroupStabAut T) :
    CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥T
      (CFSG.GroupActions.subgroupStabRestrict T
        ⟨MulAut.conj (proj r K y), hTy⟩) ∈ innAutDerived (↥T ⧸ Subgroup.center ↥T) := by
  subst hTuni
  exact centerQuotientHom_mem_innAutDerived_of_unitaryComponent_literal hK8 hr hx3 hy3 hcomm
    blocks hT hTy

end UnitaryBlock

section Assembly

variable {r : ℕ} {K : Type} [Field K] [Finite K]

theorem symplecticCompAlgEight_holds : SymplecticCompAlgEight := by
  intro r K _ _ hr hne hK8 β hβ hβ3 hβ1 J hJ e _ _ x hxmem hx3 hβx hxstab
  classical
  have hK3 : Nat.card K = 2 ^ 3 := by rw [hK8]; norm_num
  have hne' : ¬ (r = 2 ∧ 2 ^ 3 = 2) := by rintro ⟨-, h⟩; norm_num at h
  obtain ⟨a, hβeq, ha3⟩ := exists_conj_proj_of_mem_innAutDerived_statedSp
    (p := 3) (r := r) (K := K) (ℓ := 2) (f := 3) Nat.prime_three (by norm_num)
    Nat.prime_two (by norm_num) hK3 hr hne' hβ hβ3
  obtain ⟨y, hxeq, hy3⟩ := exists_conj_proj_of_mem_innAutDerived_statedSp
    (p := 3) (r := r) (K := K) (ℓ := 2) (f := 3) Nat.prime_three (by norm_num)
    Nat.prime_two (by norm_num) hK3 hr hne' hxmem hx3
  rw [hβeq] at hβ1 hβx hJ
  subst hxeq
  have hcomm : Commute a y :=
    commute_of_conj_proj_commute hr ha3 hy3 hβx
  have ha1 : proj r K a ≠ 1 := by
    intro h
    exact hβ1 (by rw [h, map_one])
  have hane : a ≠ 1 := fun h => ha1 (by rw [h, map_one])
  have haord : orderOf a = 3 := orderOf_eq_prime ha3 hane
  have haord' : orderOf (proj r K a) = 3 :=
    orderOf_eq_prime (by rw [← map_pow, ha3, map_one]) ha1
  have blocks : SpPrimaryBlocks 2 3 3 a (proj r K a) :=
    (symplectic_cross_prime_primary_centralizer_blocks (K := K) (r := r) (ℓ := 2) (f := 3)
      (p := 3) Nat.prime_two (by norm_num) hK3 Nat.prime_three (by norm_num) (by norm_num)
      (by omega) (proj r K a) haord').2 a rfl haord
  rcases exists_component_eq_fixed_or_unitary hK8 hr ha3 ha1 J hJ
      with ⟨hJfix, -⟩ | hJuni
  · exact centerQuotientHom_mem_innAutDerived_of_fixedComponent hK8 ha3 hcomm blocks J hJ
      hJfix hxstab
  · exact centerQuotientHom_mem_innAutDerived_of_unitaryComponent hK8 hr ha3 hy3 hcomm blocks
      J hJ hJuni hxstab

theorem lieCompAlg_symplectic : LieCompAlg isSymplecticIdx := fun d hd hf =>
  compAlgAt_psp symplecticCompAlgEight_holds hd hf

end Assembly

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
