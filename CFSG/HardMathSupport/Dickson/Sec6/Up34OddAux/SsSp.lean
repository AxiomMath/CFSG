module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.SsSpAux.Good
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.SsSpAux.Orbit

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG CFSG.Open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.UniquenessMaximal
  CFSG.ComponentClassification.CatLeaf CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.RankThree.PartOne.Sec66T (lieModel_classical_iff)
open CFSG.HardMathSupport.Dickson.Sec6.I923 (congr_mem_inner_iff_of_equiv)
open scoped commutatorElement

namespace SsSp

private theorem commutator_le_self' {X : Type*} [Group X] (K : Subgroup X) : ⁅K, K⁆ ≤ K := by
  refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
  rw [commutatorElement_def]
  exact K.mul_mem (K.mul_mem (K.mul_mem ha hb) (K.inv_mem ha)) (K.inv_mem hb)

theorem dich_of_layerGood {X : Type} [Group X] (A : Subgroup X) (h : LayerGood ↥A) :
    (CFSG.IsQuasisimple ↥⁅A, A⁆ ∧ ¬ IsLThreeFour (↥⁅A, A⁆ ⧸ Subgroup.center ↥⁅A, A⁆)) ∨
      Group.IsSolvable ↥A := by
  rcases h with ⟨hq, hno⟩ | hs
  · left
    let e : ↥(commutator ↥A) ≃* ↥⁅A, A⁆ :=
      ((commutator ↥A).equivMapOfInjective A.subtype A.subtype_injective).trans
        (MulEquiv.subgroupCongr (Subgroup.map_subtype_commutator A))
    refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e hq, fun hL => hno ?_⟩
    exact IsLThreeFour.of_mulEquiv (QuotientGroup.congr _ _ e.symm
      (Subgroup.map_center_eq e.symm)) hL
  · right
    exact hs

theorem tame_of_layerGood {X : Type} [Group X] (A : Subgroup X) (h : LayerGood ↥A) :
    CFSG.IsQuasisimple ↥⁅A, A⁆ ∨ Group.IsSolvable ↥A :=
  (dich_of_layerGood A h).imp And.left id

theorem not_isLThreeFour_of_layerGood {X : Type} [Group X] (A : Subgroup X) (h : LayerGood ↥A)
    (hq : CFSG.IsQuasisimple ↥⁅A, A⁆) :
    ¬ IsLThreeFour (↥⁅A, A⁆ ⧸ Subgroup.center ↥⁅A, A⁆) := by
  rcases dich_of_layerGood A h with ⟨-, hno⟩ | hs
  · exact hno
  · exfalso
    haveI : Group.IsSolvable ↥⁅A, A⁆ := Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion (commutator_le_self' A)) (Subgroup.inclusion_injective _)
    haveI : Group.IsPerfect ↥⁅A, A⁆ := hq.1
    haveI : Nontrivial ↥⁅A, A⁆ := CFSG.LocalCores.isQuasisimple_nontrivial hq
    exact Group.IsPerfect.not_isSolvable _ ‹_›

section Blocks

open Polynomial CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCSpIsotypic
open CFSG.RankThree.PartOne.KCOrthogonal (reciprocalPolynomial)

variable {r : ℕ} {K : Type} [Field K]

theorem layerGood_spSupported_of_factor (hO : LieOrderFormulasInput) [Finite K] {ℓ f p : ℕ}
    (hℓ : ℓ.Prime) (hℓ5 : 5 ≤ ℓ) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f)
    {x : StatedSp r K} {a : StatedProj (StatedSp r K)}
    (hsq : Squarefree (minpoly K (spEnd x))) (blocks : SpPrimaryBlocks ℓ f p x a)
    (h : primaryFactors (spEnd x)) :
    LayerGood ↥(spSupported x {(h : K[X]), reciprocalPolynomial (h : K[X])}) := by
  by_cases hself : reciprocalPolynomial (h : K[X]) = h
  · have hO' : ({(h : K[X]), reciprocalPolynomial (h : K[X])} : Set K[X]) = {(h : K[X])} := by
      rw [hself, Set.pair_eq_singleton]
    rw [hO']
    by_cases h1 : (h : K[X]) = X - 1
    · obtain ⟨h0, hm⟩ := h
      change h0 = X - 1 at h1
      subst h1
      obtain ⟨φ, -⟩ := blocks.fixedFactor hm
      have : Nontrivial (primaryComponent (spEnd x) (X - 1)) :=
        Submodule.nontrivial_iff_ne_bot.mpr (primaryComponent_ne_bot hsq hm)
      obtain ⟨s, hs, ⟨e⟩⟩ := exists_mulEquiv_sesqUnitaryGroup_statedSp
        (B := (spForm r K).restrict (primaryComponent (spEnd x) (X - 1)))
        (fun v => spForm_isAlt (v : Fin r ⊕ Fin r → K)) blocks.fixed_nondegenerate
      have hs1 : 1 ≤ s := by
        have := Module.finrank_pos (R := K) (M := primaryComponent (spEnd x) (X - 1))
        omega
      exact LayerGood.of_mulEquiv (φ.trans e) (layerGood_statedSp hO hℓ hℓ5 hf hK hs1)
    · obtain ⟨d, -, hpd, σ, -, -, -, -, -, hE, -, Hf, hHf, hHfl, -, -, φ, hφ⟩ :=
        (blocks.selfDual h h1 hself).exists_half
      exact LayerGood.of_mulEquiv φ (layerGood_sesqUnitaryGroup hO hℓ5 hE hHf hHfl)
  · have hP := blocks.paired h (fun e => hself e.symm)
    obtain ⟨φ⟩ := hP.matrixFactor
    have hdeg : 1 ≤ (h : K[X]).natDegree :=
      Irreducible.natDegree_pos (irreducible_of_mem_primaryFactors h.2)
    exact LayerGood.of_mulEquiv φ (layerGood_matrixGL hO hℓ hℓ5 (Nat.mul_pos hf hdeg)
      (by rw [hP.card_field, pow_mul]) _)

theorem noL34Layer_conj_sp_of_prime (hO : LieOrderFormulasInput) {ℓ f p : ℕ} (hℓ : ℓ.Prime)
    (hℓ5 : 5 ≤ ℓ) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) (hr : 1 ≤ r) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ) (x : StatedSp r K) (hx : x ^ p = 1) :
    NoL34Layer (MulAut.conj (SymplecticFlag.proj r K x)) := by
  classical
  have hq0 : ℓ ^ f ≠ 0 := pow_ne_zero f hℓ.ne_zero
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact hq0)
  haveI : Fact p.Prime := ⟨hp⟩
  have hZc : (SymplecticFlag.proj r K).ker ≤ Subgroup.center (StatedSp r K) := by
    rw [SymplecticHigher.ker_proj]
    exact SymplecticHigher.spScalars_le_center
  by_cases hx1 : x = 1
  · subst hx1
    have hgood : LayerGood ↥(⊤ : Subgroup (StatedSp r K)) :=
      LayerGood.of_mulEquiv Subgroup.topEquiv (layerGood_statedSp hO hℓ hℓ5 hf hK hr)
    refine noL34Layer_conj_of_orbit_family (SymplecticFlag.proj r K)
      SymplecticHigher.proj_surjective hZc 1 (fun _ : Unit => (⊤ : Subgroup (StatedSp r K)))
      (fun i j hij => absurd (Subsingleton.elim i j) hij) ?_
      (fun _ => tame_of_layerGood _ hgood)
      (fun _ hq => not_isLThreeFour_of_layerGood _ hgood hq)
    ext g
    simp [Subgroup.mem_centralizer_iff]
  · have hZp : Nat.Coprime (Nat.card (SymplecticFlag.proj r K).ker) p := by
      rw [SymplecticHigher.ker_proj, card_spScalars_eq_gcd K hr]
      exact Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left 2 _)
        ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
    have ha1 : SymplecticFlag.proj r K x ≠ 1 := fun h =>
      hx1 (CFSG.RankThree.Classical.eq_of_map_eq_of_pow_eq_one_of_coprime (a := 1) (b := 0)
        (SymplecticFlag.proj r K) hZc hZp (by rwa [pow_one]) (by simp)
        (by rw [h, map_one]))
    have ha : orderOf (SymplecticFlag.proj r K x) = p :=
      orderOf_eq_prime (by rw [← map_pow, hx, map_one]) ha1
    have hxp : orderOf x = p := orderOf_eq_prime hx hx1
    have blocks := (CFSG.RankThree.Classical.symplectic_cross_prime_primary_centralizer_blocks hℓ
      hf hK hp hp2 hpℓ hr _ ha).2 x rfl hxp
    have hpK : (p : K) ≠ 0 := by
      have := Fintype.ofFinite K
      have hcardK : Fintype.card K = ℓ ^ f := by rw [Fintype.card_eq_nat_card, hK]
      have : Fact ℓ.Prime := ⟨hℓ⟩
      have : CharP K ℓ := charP_of_card_eq_prime_pow (f := f) hcardK
      intro h
      rw [CharP.cast_eq_zero_iff K ℓ] at h
      exact hpℓ ((Nat.prime_dvd_prime_iff_eq hℓ hp).mp h).symm
    have hsq := (CFSG.RankThree.Classical.altPrimaryData_spLin hpK hx).squarefree
    haveI : Finite (reciprocalOrbits (spEnd x)) :=
      (Set.Finite.image _ (Finset.finite_toSet _)).to_subtype
    obtain ⟨hcomm, -, hjoin⟩ := blocks.directProduct
    have hgood : ∀ O : reciprocalOrbits (spEnd x), LayerGood ↥(spSupported x (O : Set K[X])) := by
      rintro ⟨O, h, hh, rfl⟩
      exact layerGood_spSupported_of_factor hO hℓ hℓ5 hf hK hsq blocks ⟨h, hh⟩
    exact noL34Layer_conj_of_orbit_family (SymplecticFlag.proj r K)
      SymplecticHigher.proj_surjective hZc x
      (fun O : reciprocalOrbits (spEnd x) => spSupported x (O : Set K[X]))
      (fun i j hij a ha b hb => hcomm i.1 i.2 j.1 j.2 (fun h => hij (Subtype.ext h)) a ha b hb)
      hjoin (fun O => tame_of_layerGood _ (hgood O))
      (fun O hq => not_isLThreeFour_of_layerGood _ (hgood O) hq)

end Blocks

end SsSp

open SsSp in
theorem noL34Layer_conj_sp (hO : LieOrderFormulasInput) {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ5 : 5 ≤ ℓ)
    (hf : 1 ≤ f) {K : Type} [Field K] (hK : Nat.card K = ℓ ^ f) {r : ℕ} (hr : 2 ≤ r)
    (x : StatedSp r K) (hx : x ^ 3 = 1) :
    NoL34Layer (MulAut.conj (SymplecticFlag.proj r K x)) :=
  noL34Layer_conj_sp_of_prime hO hℓ hℓ5 hf hK (by omega) Nat.prime_three (by omega) (by omega) x hx

theorem noL34InnAt_psp (hO : LieOrderFormulasInput) :
    NoL34InnAt (fun t n _ _ => t = .PSp ∧ 2 ≤ n) := by
  intro P _ _ t n p f hadm ht hF hp5 hm ψ hψ3 hψ
  obtain ⟨rfl, hn2⟩ := hF
  have hC : StatedClassicalModel P .PSp n p f := (lieModel_classical_iff (by decide)).mp hm
  obtain ⟨-, K, _, _, hK, ⟨e0⟩⟩ := hC
  haveI : Finite (StatedProj (StatedSp n K)) := Finite.of_equiv P e0.toEquiv
  refine noL34Layer_congr e0 ?_
  have hψ3' : MulAut.congr e0 ψ ^ 3 = 1 := by rw [← map_pow, hψ3, map_one]
  obtain ⟨g, hg⟩ := (congr_mem_inner_iff_of_equiv e0 ψ).mpr hψ
  obtain ⟨x, rfl⟩ := SymplecticHigher.proj_surjective g
  have hc3 : SymplecticFlag.proj n K x ^ 3 ∈ Subgroup.center (StatedProj (StatedSp n K)) := by
    rw [Subgroup.mem_center_iff]
    intro h
    have h1 : (MulAut.conj (SymplecticFlag.proj n K x ^ 3)) h = h := by
      rw [map_pow, hg, hψ3']
      rfl
    rw [MulAut.conj_apply] at h1
    calc h * SymplecticFlag.proj n K x ^ 3
        = (SymplecticFlag.proj n K x ^ 3 * h * (SymplecticFlag.proj n K x ^ 3)⁻¹) *
            SymplecticFlag.proj n K x ^ 3 := by rw [h1]
      _ = SymplecticFlag.proj n K x ^ 3 * h := by group
  have hq4 : 4 ≤ Nat.card K := by
    rw [hK]
    exact le_trans (by omega) (Nat.le_self_pow (by have := hadm.2.1; omega) p)
  have hqs := CFSG.LieType.Universal.Symplectic.isQuasisimple n K (by omega)
    (Or.inl (Or.inr hq4))
  let eP := CFSG.LieType.Universal.Symplectic.centerQuotientEquiv n K
  haveI : IsSimpleGroup (StatedSp n K ⧸ Subgroup.center (StatedSp n K)) := hqs.2.1
  haveI : IsSimpleGroup (StatedProj (StatedSp n K)) := eP.symm.isSimpleGroup
  have hcenter : Subgroup.center (StatedProj (StatedSp n K)) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.center (StatedProj (StatedSp n K))) with h' | h'
    · exact h'
    · exfalso
      obtain ⟨a, b, hab⟩ := hqs.2.2
      have ha : eP a ∈ Subgroup.center (StatedProj (StatedSp n K)) := h' ▸ Subgroup.mem_top _
      exact hab (eP.injective (by simpa using (Subgroup.mem_center_iff.1 ha (eP b)).symm))
  have hg3 : SymplecticFlag.proj n K x ^ 3 = 1 := by
    rw [hcenter] at hc3
    exact Subgroup.mem_bot.1 hc3
  have hxk : x ^ 3 ∈ (SymplecticFlag.proj n K).ker := by
    rw [MonoidHom.mem_ker, map_pow]
    exact hg3
  have hcard : Nat.card (SymplecticFlag.proj n K).ker ∣ 2 := by
    rw [SymplecticHigher.ker_proj, card_spScalars_eq_gcd K (by omega : 1 ≤ n)]
    exact Nat.gcd_dvd_left 2 _
  have hx6 : (x ^ 3) ^ 2 = 1 := by
    obtain ⟨c, hc⟩ := hcard
    have h1 : (x ^ 3) ^ Nat.card (SymplecticFlag.proj n K).ker = 1 :=
      congrArg Subtype.val (pow_card_eq_one' (x := (⟨x ^ 3, hxk⟩ : (SymplecticFlag.proj n K).ker)))
    rw [hc, pow_mul, h1, one_pow]
  have hy3 : (x ^ 4) ^ 3 = 1 := by
    calc (x ^ 4) ^ 3 = ((x ^ 3) ^ 2) ^ 2 := by group
      _ = 1 := by rw [hx6, one_pow]
  have hyg : SymplecticFlag.proj n K (x ^ 4) = SymplecticFlag.proj n K x := by
    rw [map_pow, pow_succ, hg3, one_mul]
  rw [← hg, ← hyg]
  exact noL34Layer_conj_sp hO hadm.1 hp5 hadm.2.1 hK hn2 (x ^ 4) hy3

theorem noL34InnAt_famPsp (hO : LieOrderFormulasInput) : NoL34InnAt I923.FamPsp :=
  fun P _ _ t n p f hadm ht hF hp5 hm ψ hψ3 hψ =>
    noL34InnAt_psp hO P t n p f hadm ht ⟨hF.1, hF.2.1⟩ hp5 hm ψ hψ3 hψ

end CFSG.HardMathSupport.Dickson.Sec6
