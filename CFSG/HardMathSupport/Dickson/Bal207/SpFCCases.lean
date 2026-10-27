module

public import CFSG.HardMathSupport.Dickson.Bal207.SpFCFrame
import all CFSG.HardMathSupport.Dickson.Bal207.SpShape
import all CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SympInnerExport
import all CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SympFieldExport
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSp
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.SympAut
import CFSG.LocalAnalysis.AGLEmbedding.ThreeCentLieTwoOBlocks
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogQuadraticDescent
public import CFSG.Timmesfeld.Orders.ClassicalLinear
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.HardMathSupport.Dickson.Bal207.FirstClaim

open Polynomial Matrix CFSG.Open CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCSpFull
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.HardMathSupport.Dickson.I271 CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Dickson.Bal207.Uni
open CFSG.ComponentClassification.UnbalancedCatalog (descentField)
open CFSG.RankThree.PartOne.KCOrthogonal (reciprocalPolynomial)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

@[expose] def IsPspQuot {Y : Type} [Group Y] (J : Subgroup Y) : Prop :=
  ∃ (s k : ℕ) (F' : Type) (_ : Field F') (_ : Finite F'), Nat.card F' = 2 ^ k ∧
    (k = 1 ∨ k = 3) ∧ 2 ≤ s ∧ ¬(s = 2 ∧ k = 1) ∧
      Nonempty ((↥J ⧸ Subgroup.center ↥J) ≃* StatedProj (StatedSp s F'))

section General

theorem bracket_le_self {G : Type*} [Group G] (A : Subgroup G) : ⁅A, A⁆ ≤ A :=
  Subgroup.commutator_le.mpr fun g hg g' hg' => by
    rw [commutatorElement_def]
    exact A.mul_mem (A.mul_mem (A.mul_mem hg hg') (A.inv_mem hg)) (A.inv_mem hg')

theorem bracket_eq_self_of_equiv {G T : Type*} [Group G] [Group T] {A : Subgroup G}
    (φ : A ≃* T) (hT : commutator T = ⊤) : ⁅A, A⁆ = A := by
  have h1 : commutator ↥A = ⊤ := by
    have hm : (⊤ : Subgroup T).map φ.symm.toMonoidHom = ⊤ := by
      rw [← MonoidHom.range_eq_map]
      exact MonoidHom.range_eq_top_of_surjective _ φ.symm.surjective
    rw [commutator_def, ← hm, ← Subgroup.map_commutator, ← commutator_def, hT]
  rw [← Subgroup.map_subtype_commutator, h1, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

variable {Y : Type} [Group Y] {K J : Subgroup Y} {S : Type} [Group S]
  (e : (↥K ⧸ Subgroup.center ↥K) ≃* S)

theorem card_centerQuot_dvd_card_image (hJK : J ≤ K) :
    Nat.card (↥J ⧸ Subgroup.center ↥J) ∣ Nat.card ((J.comap K.subtype).map (uniMap e)) := by
  have h1 := Subgroup.index_dvd_of_le (ker_uniRestr_le_center e hJK)
  rw [Subgroup.index_ker, MonoidHom.range_eq_top_of_surjective _ (uniRestr_surjective e hJK),
    Subgroup.card_top] at h1
  exact h1

theorem card_centerQuot_dvd_of_eq_map (hJK : J ≤ K) {G : Type*} [Group G] {A : Subgroup G}
    {π : G →* S} (hψ : (J.comap K.subtype).map (uniMap e) = (⁅A, A⁆).map π) {N : ℕ}
    (hA : Nat.card A ∣ N) : Nat.card (↥J ⧸ Subgroup.center ↥J) ∣ N := by
  refine (card_centerQuot_dvd_card_image e hJK).trans ?_
  rw [hψ]
  exact ((Subgroup.card_map_dvd _ π).trans (Subgroup.card_dvd_of_le (bracket_le_self A))).trans hA

theorem nonempty_centerQuot_of_image (hJK : J ≤ K) (hJ : commutator ↥J = ⊤) {T : Type*}
    [Group T] (eψ : ↥((J.comap K.subtype).map (uniMap e)) ≃* T) :
    Nonempty ((↥J ⧸ Subgroup.center ↥J) ≃* (T ⧸ Subgroup.center T)) :=
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp.nonempty_centralQuotient_mulEquiv hJ
    (eψ.toMonoidHom.comp (uniRestr e hJK)) (eψ.surjective.comp (uniRestr_surjective e hJK))
    fun j hj => ker_uniRestr_le_center e hJK ((MulEquiv.map_eq_one_iff eψ).mp hj)

end General

theorem card_statedSp_dvd_of_small {s f : ℕ} {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ f) (hf : f = 1 ∨ f = 3) (hs1 : 1 ≤ s)
    (hs : ¬(2 ≤ s ∧ ¬(s = 2 ∧ f = 1))) : Nat.card (StatedSp s F) ∣ 16511040 := by
  have hcases : s = 1 ∨ (s = 2 ∧ f = 1) := by
    by_contra hc
    exact hs ⟨by omega, fun h => hc (Or.inr h)⟩
  rcases hcases with rfl | ⟨rfl, rfl⟩
  · rw [SymplecticFlag.card_statedSp, hF, Finset.Icc_self, Finset.prod_singleton]
    rcases hf with rfl | rfl <;> norm_num
  · rw [SymplecticFlag.card_statedSp_two, hF]
    norm_num

section Inner

variable {Y : Type} [Group Y] {K J : Subgroup Y} {r f : ℕ} {F : Type} [Field F] [Finite F]

theorem spComp_fixed (hF : Nat.card F = 2 ^ f) (hf : f = 1 ∨ f = 3)
    (e : (↥K ⧸ Subgroup.center ↥K) ≃* StatedProj (StatedSp r F)) {x : StatedSp r F}
    {a : StatedProj (StatedSp r F)} (blocks : SpPrimaryBlocks 2 f 3 x a)
    (hsq : Squarefree (minpoly F (spEnd x))) (hk : (X - 1 : F[X]) ∈ primaryFactors (spEnd x))
    (hπ : Function.Injective (SymplecticFlag.proj r F)) (hJK : J ≤ K)
    (hJq : CFSG.Open.IsQuasisimple ↥J)
    (hψ : (J.comap K.subtype).map (uniMap e) =
      (⁅spSupported x {X - 1}, spSupported x {X - 1}⁆).map (SymplecticFlag.proj r F)) :
    IsPspQuot J ∨ Nat.card (↥J ⧸ Subgroup.center ↥J) ∣ 16511040 := by
  classical
  obtain ⟨φ, -⟩ := blocks.fixedFactor hk
  haveI : Nontrivial (primaryComponent (spEnd x) (X - 1)) :=
    Submodule.nontrivial_iff_ne_bot.mpr (primaryComponent_ne_bot hsq hk)
  obtain ⟨s, hs, ⟨e'⟩⟩ :=
    CFSG.RankThree.PartOne.KCSpIsotypic.exists_mulEquiv_sesqUnitaryGroup_statedSp
    (B := (spForm r F).restrict (primaryComponent (spEnd x) (X - 1)))
    (fun v => spForm_isAlt (v : Fin r ⊕ Fin r → F)) blocks.fixed_nondegenerate
  have hs1 : 1 ≤ s := by
    have := Module.finrank_pos (R := F) (M := primaryComponent (spEnd x) (X - 1))
    omega
  have ψ' : spSupported x {(X - 1 : F[X])} ≃* StatedSp s F := φ.trans e'
  by_cases hsg : 2 ≤ s ∧ ¬(s = 2 ∧ f = 1)
  · left
    haveI := Fintype.ofFinite F
    have hne' : (s, Fintype.card F) ≠ (2, 2) := fun h => by
      have h1 := congrArg Prod.fst h
      have h2 := congrArg Prod.snd h
      simp only at h1 h2
      rw [Fintype.card_eq_nat_card, hF] at h2
      refine hsg.2 ⟨h1, ?_⟩
      rcases hf with rfl | rfl
      · rfl
      · norm_num at h2
    have hAA := bracket_eq_self_of_equiv ψ'
      (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.spFactorFacts_holds F s hsg.1 hne').perfect
    have hL : (J.comap K.subtype).map (uniMap e) =
        (spSupported x {(X - 1 : F[X])}).map (SymplecticFlag.proj r F) := by
      rw [hψ, hAA]
    obtain ⟨eq⟩ := nonempty_centerQuot_of_image e hJK hJq.1 ((MulEquiv.subgroupCongr hL).trans
      (((spSupported x {(X - 1 : F[X])}).equivMapOfInjective _ hπ).symm.trans ψ'))
    exact ⟨s, f, F, inferInstance, inferInstance, hF, hf, hsg.1, hsg.2,
      ⟨eq.trans (CFSG.LieType.Universal.Symplectic.centerQuotientEquiv s F)⟩⟩
  · right
    refine card_centerQuot_dvd_of_eq_map e hJK hψ ?_
    rw [Nat.card_congr ψ'.toEquiv]
    exact card_statedSp_dvd_of_small hF hf hs1 hsg

theorem eq_two_of_not_small {m q : ℕ} (hq : q = 2 ∨ q = 8)
    (h1 : ¬(m ≤ 1 ∨ ¬((m = 2 → 4 ≤ q) ∧ (m = 3 → 3 ≤ q))))
    (h2 : ¬(3 ≤ m ∧ ¬(m = 3 ∧ q = 2))) : m = 2 ∧ q = 8 := by
  omega

open CFSG.HardMathSupport.Solomon.Coordinator.LieComp in
theorem spComp_phi3_small (hF : Nat.card F = 2 ^ f) (hf : f = 1 ∨ f = 3)
    (e : (↥K ⧸ Subgroup.center ↥K) ≃* StatedProj (StatedSp r F)) {x : StatedSp r F}
    {g : primaryFactors (spEnd x)} (hg : (g : F[X]) = X ^ 2 + X + 1)
    (hS : SpSelfDualBlock 2 f 3 x g)
    (hm : ¬(3 ≤ primaryMultiplicity (spEnd x) (g : F[X]) ∧
      ¬(primaryMultiplicity (spEnd x) (g : F[X]) = 3 ∧ 2 ^ f = 2)))
    (hJK : J ≤ K)
    (hQ : CFSG.IsQuasisimple ↥⁅spSupported x {(g : F[X])}, spSupported x {(g : F[X])}⁆)
    (hψ : (J.comap K.subtype).map (uniMap e) =
      (⁅spSupported x {(g : F[X])}, spSupported x {(g : F[X])}⁆).map (SymplecticFlag.proj r F)) :
    Nat.card (↥J ⧸ Subgroup.center ↥J) ∣ 16511040 := by
  classical
  obtain ⟨d, hd, -, -, -, -, -, -, -, hE, -, Hf, hHf, hHfl, -, ⟨e₀, -⟩, φ, -⟩ :=
    hS.exists_half
  have hdeg : (X ^ 2 + X + 1 : F[X]).natDegree = 2 := by compute_degree!
  have hd1 : d = 1 := by
    rw [hg, hdeg] at hd
    omega
  subst hd1
  haveI : FiniteDimensional (AdjoinRoot (g : F[X])) (primaryComponent (spEnd x) (g : F[X])) :=
    Module.Finite.of_basis e₀
  have hfin : Module.finrank (AdjoinRoot (g : F[X])) (primaryComponent (spEnd x) (g : F[X])) =
      primaryMultiplicity (spEnd x) (g : F[X]) := by
    rw [Module.finrank_eq_card_basis e₀, Fintype.card_fin]
  have hsmall : ¬(primaryMultiplicity (spEnd x) (g : F[X]) ≤ 1 ∨
      ¬((primaryMultiplicity (spEnd x) (g : F[X]) = 2 → 4 ≤ 2 ^ (f * 1)) ∧
        (primaryMultiplicity (spEnd x) (g : F[X]) = 3 → 3 ≤ 2 ^ (f * 1)))) := fun hsm => by
    rw [← hfin] at hsm
    haveI := isSolvable_sesqUnitaryGroup_of_small hE hHf hHfl hsm
    exact not_isSolvable_of_isQuasisimple_commutator hQ
      (Group.isSolvable_of_isSolvable_injective (f := φ.toMonoidHom) φ.injective)
  rw [mul_one] at hsmall
  have hq : 2 ^ f = 2 ∨ 2 ^ f = 8 := by rcases hf with rfl | rfl <;> norm_num
  obtain ⟨hm2, hq8⟩ := eq_two_of_not_small hq hsmall hm
  have hf3 : f = 3 := by
    rcases hf with rfl | rfl
    · norm_num at hq8
    · rfl
  subst hf3
  refine card_centerQuot_dvd_of_eq_map e hJK hψ ?_
  haveI := hE.finite
  haveI := Fintype.ofFinite (AdjoinRoot (g : F[X]))
  have hq64 : Fintype.card (AdjoinRoot (g : F[X])) = 64 := by
    rw [Fintype.card_eq_nat_card, hE.card_eq_sq]
    norm_num
  rw [Nat.card_congr φ.toEquiv]
  refine (Subgroup.card_subgroup_dvd_card _).trans ?_
  rw [← Nat.card_congr (Matrix.GeneralLinearGroup.toLin' e₀).toEquiv]
  have key : ∀ n : ℕ, n = 2 → Nat.card (GL (Fin n) (AdjoinRoot (g : F[X]))) ∣ 16511040 := by
    rintro n rfl
    rw [Matrix.card_GL_field, Fin.prod_univ_two, hq64]
    norm_num
  exact key _ hm2

open CFSG.HardMathSupport.Solomon.Coordinator in
theorem spComp_cases_inner {B : Subgroup Y} (hB : IsSCp 3 ⊤ B)
    (hBK : B ≤ Subgroup.normalizer (K : Set Y)) (hF : Nat.card F = 2 ^ f) (hf : f = 1 ∨ f = 3)
    (hr : 2 ≤ r) (e : (↥K ⧸ Subgroup.center ↥K) ≃* StatedProj (StatedSp r F)) {a : Y}
    (ha : a ∈ B) {x : StatedSp r F} (hx : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hax : uniAut e ⟨a, hBK ha⟩ = MulAut.conj (SymplecticFlag.proj r F x)) (hJK : J ≤ K)
    (hJq : CFSG.Open.IsQuasisimple ↥J)
    (hJc : IsComponentOf ((J.comap K.subtype).map (uniMap e))
      (fixSubgroup (MulAut.conj (SymplecticFlag.proj r F x)))) :
    IsPspQuot J ∨ Nat.card (↥J ⧸ Subgroup.center ↥J) ∣ 16511040 ∨ BlockFrame e B J hBK := by
  classical
  have hf1 : 1 ≤ f := by omega
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := Fintype.ofFinite F
  have hcardF : Fintype.card F = 2 ^ f := by rw [Fintype.card_eq_nat_card, hF]
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (f := f) hcardF
  have hq : 2 ≤ 2 ^ f := Nat.le_self_pow (by omega) 2
  have hker := ker_proj_eq_bot_of_two (r := r) (by omega) hF hf
  have hπ : Function.Injective (SymplecticFlag.proj r F) := (MonoidHom.ker_eq_bot_iff _).1 hker
  have hZc : (SymplecticFlag.proj r F).ker ≤ Subgroup.center (StatedSp r F) := by
    rw [hker]
    exact bot_le
  have hxp : orderOf x = 3 := orderOf_eq_prime hx hx1
  have ha1 : SymplecticFlag.proj r F x ≠ 1 := fun h => hx1 (hπ (by rw [h, map_one]))
  have hap : orderOf (SymplecticFlag.proj r F x) = 3 :=
    orderOf_eq_prime (by rw [← map_pow, hx, map_one]) ha1
  have blocks := (symplectic_cross_prime_primary_centralizer_blocks Nat.prime_two hf1 hF
    Nat.prime_three (by norm_num) (by norm_num) (by omega) _ hap).2 x rfl hxp
  have hpK : ((3 : ℕ) : F) ≠ 0 := by
    intro h3
    rw [CharP.cast_eq_zero_iff F 2] at h3
    norm_num at h3
  have hsq := (altPrimaryData_spLin hpK hx).squarefree
  have hX3 : spEnd x ^ 3 = 1 := spEnd_pow hx
  haveI : Finite (reciprocalOrbits (spEnd x)) :=
    (Set.Finite.image _ (Finset.finite_toSet _)).to_subtype
  obtain ⟨hcomm, -, hjoin⟩ := blocks.directProduct
  have hcomp := LieComp.components_conj_of_orbit_family (SymplecticFlag.proj r F)
    SymplecticHigher.proj_surjective hZc x
    (fun O : reciprocalOrbits (spEnd x) => spSupported x (O : Set F[X]))
    (fun i j hij u hu v hv => hcomm i.1 i.2 j.1 j.2 (fun h => hij (Subtype.ext h)) u hu v hv)
    hjoin (fun O => LieSemisimple.quasisimple_or_solvable_spSupported (by norm_num) hq hsq
      blocks O)
  obtain ⟨⟨O, k, hk, rfl⟩, hQ, hψ⟩ := hcomp _ hJc
  have hcases := primaryFactor_cases_of_card hF hf hX3 hk
  have hpair : ({k, reciprocalPolynomial k} : Set F[X]) = {k} := by
    rw [reciprocal_eq_of_cases hcases, Set.pair_eq_singleton]
  have hQ' : CFSG.IsQuasisimple ↥⁅spSupported x {k}, spSupported x {k}⁆ := by
    rw [← hpair]
    exact hQ
  have hψ' : (J.comap K.subtype).map (uniMap e) =
      (⁅spSupported x {k}, spSupported x {k}⁆).map (SymplecticFlag.proj r F) := by
    rw [← hpair]
    exact hψ
  clear hQ hψ hcomp
  rcases hcases with rfl | hΦ
  · exact (spComp_fixed hF hf e blocks hsq hk hπ hJK hJq hψ').imp_right Or.inl
  · obtain ⟨g, hg⟩ : ∃ g : primaryFactors (spEnd x), (g : F[X]) = X ^ 2 + X + 1 := ⟨⟨k, hk⟩, hΦ⟩
    have hgk : (g : F[X]) = k := hg.trans hΦ.symm
    rw [← hgk] at hQ' hψ'
    have h1 : (g : F[X]) ≠ X - 1 := by
      rw [hg]
      exact X_sq_add_X_add_one_ne
    have hS := blocks.selfDual g h1
      (by rw [hg]; exact CFSG.AGLEmbedding.reciprocalPolynomial_X_sq_add_X_add_one)
    by_cases hm : 3 ≤ primaryMultiplicity (spEnd x) (g : F[X]) ∧
        ¬(primaryMultiplicity (spEnd x) (g : F[X]) = 3 ∧ 2 ^ f = 2)
    · exact Or.inr (Or.inr
        (blockFrame_of_selfDual hB hBK hF hf hr e ha hx hax hg hS hm.1 hm.2 hψ'))
    · exact Or.inr (Or.inl (spComp_phi3_small hF hf e hg hS hm hJK hQ' hψ'))

end Inner

open CFSG.HardMathSupport.Solomon.Coordinator.LieComp in
theorem spComp_cases_outer {Y : Type} [Group Y] {K J : Subgroup Y} {r f : ℕ} {F : Type}
    [Field F] [Finite F] (hF : Nat.card F = 2 ^ f) (hf : f = 1 ∨ f = 3) (hr : 2 ≤ r)
    (e : (↥K ⧸ Subgroup.center ↥K) ≃* StatedProj (StatedSp r F))
    {β h : MulAut (StatedProj (StatedSp r F))} {σ : F ≃+* F} (hσ : orderOf σ = 3)
    (hβ : β = h * SymplecticHigher.fieldAut r F σ * h⁻¹) (hJK : J ≤ K)
    (hJq : CFSG.Open.IsQuasisimple ↥J)
    (hJc : IsComponentOf ((J.comap K.subtype).map (uniMap e)) (fixSubgroup β)) :
    IsPspQuot J ∨ Nat.card (↥J ⧸ Subgroup.center ↥J) ∣ 16511040 := by
  have hσ3 : σ ^ 3 = 1 := by
    rw [← hσ]
    exact pow_orderOf_eq_one σ
  haveI : NeZero r := ⟨by omega⟩
  have hk2 : Nat.card ↥(descentField σ) = 2 := by
    have h := card_descentField_pow σ
    rw [hσ, hF] at h
    have hlt : Nat.card ↥(descentField σ) < 3 := by
      by_contra hn
      push Not at hn
      have h27 : 3 ^ 3 ≤ Nat.card ↥(descentField σ) ^ 3 := Nat.pow_le_pow_left hn 3
      rw [h] at h27
      rcases hf with rfl | rfl <;> norm_num at h27
    have h1 : 1 < Nat.card ↥(descentField σ) := Finite.one_lt_card
    omega
  obtain ⟨eσ⟩ := nonempty_fixSubgroup_equiv (r := r) (by decide : Odd 3) hσ3
  have hfix : fixSubgroup β = (fixSubgroup (SymplecticHigher.fieldAut r F σ)).map
      (h : StatedProj (StatedSp r F) →* StatedProj (StatedSp r F)) := by
    rw [hβ, ← congr_self_eq', fixSubgroup_mulAutCongr]
  have eβ : ↥(fixSubgroup β) ≃* StatedProj (StatedSp r (descentField σ)) :=
    (MulEquiv.subgroupCongr hfix).trans (((fixSubgroup _).equivMapOfInjective
      (h : StatedProj (StatedSp r F) →* StatedProj (StatedSp r F)) h.injective).symm.trans eσ)
  by_cases hr2 : r = 2
  · right
    subst hr2
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI := Fintype.ofFinite ↥(descentField σ)
    haveI : CharP ↥(descentField σ) 2 :=
      charP_of_card_eq_prime_pow (f := 1) (by rw [Fintype.card_eq_nat_card, hk2]; norm_num)
    have h720 : Nat.card ↥(fixSubgroup β) = 720 := by
      rw [Nat.card_congr eβ.toEquiv,
        CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSp_of_charTwo, hk2]
      decide
    refine (card_centerQuot_dvd_card_image e hJK).trans
      ((Subgroup.card_dvd_of_le hJc.1).trans ?_)
    rw [h720]
    norm_num
  · left
    have hex : ¬(r = 2 ∧ Nat.card ↥(descentField σ) = 2) := fun h' => hr2 h'.1
    obtain ⟨hs, -⟩ :=
      CFSG.RankThree.PartOne.KCSpComm.simple_perfect_statedProj (k := descentField σ) hr hex
    haveI : IsSimpleGroup ↥(fixSubgroup β) := eβ.isSimpleGroup
    have hL : (J.comap K.subtype).map (uniMap e) = fixSubgroup β :=
      eq_of_isComponentOf_of_simple le_rfl inferInstance (bracket_le_self _) hJc
    obtain ⟨eq⟩ := nonempty_centerQuot_of_image e hJK hJq.1 ((MulEquiv.subgroupCongr hL).trans eβ)
    have hZ := center_statedProj_eq_bot (F := ↥(descentField σ)) hr hex
    exact ⟨r, 1, ↥(descentField σ), inferInstance, inferInstance, by rw [hk2]; norm_num,
      Or.inl rfl, hr, fun h' => hr2 h'.1,
      ⟨eq.trans ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)⟩⟩

theorem spComp_cases {Y : Type} [Group Y] {K B J : Subgroup Y} (hB : IsSCp 3 ⊤ B)
    (hBK : B ≤ Subgroup.normalizer (K : Set Y)) {r f : ℕ} {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ f) (hf : f = 1 ∨ f = 3) (hr : 2 ≤ r) (hne : ¬(r = 2 ∧ f = 1))
    (e : (↥K ⧸ Subgroup.center ↥K) ≃* StatedProj (StatedSp r F)) {a : Y} (ha : a ∈ B)
    (ha1 : uniAut e ⟨a, hBK ha⟩ ≠ 1) (hJK : J ≤ K) (hJq : CFSG.Open.IsQuasisimple ↥J)
    (hJc : IsComponentOf ((J.comap K.subtype).map (uniMap e))
      (fixSubgroup (uniAut e ⟨a, hBK ha⟩))) :
    IsPspQuot J ∨ Nat.card (↥J ⧸ Subgroup.center ↥J) ∣ 16511040 ∨ BlockFrame e B J hBK := by
  have hf1 : 1 ≤ f := by omega
  have hβ3 : uniAut e ⟨a, hBK ha⟩ ^ 3 = 1 := by
    have h3 : (⟨a, hBK ha⟩ : ↥(Subgroup.normalizer (K : Set Y))) ^ 3 = 1 :=
      Subtype.ext (hB.2.1.2 a ha)
    rw [← map_pow, h3, map_one]
  have hO := CFSG.RankThree.PartOne.KCSpComm.spOuter (K := F) Nat.prime_two hf1 hr hF
  have hE := mem_spSemilinearAutGroup_of_pow_three hF hf1 hr hβ3
  by_cases hD : uniAut e ⟨a, hBK ha⟩ ∈ spLinearAutGroup r F
  ·
    have : (CFSG.ComponentClassification.OuterAutomorphisms.inner
        (StatedProj (StatedSp r F))).Normal :=
      CFSG.ComponentClassification.OuterAutomorphisms.inner_normal _
    have hrel : (CFSG.ComponentClassification.OuterAutomorphisms.inner
        (StatedProj (StatedSp r F))).relIndex (spLinearAutGroup r F) ∣ 2 :=
      hO.relIndex_dvd.trans (Nat.gcd_dvd_left 2 _)
    obtain ⟨t, ht⟩ := CFSG.RankThree.PartOne.KCSpComm.mem_of_pow_eq_one_of_relIndex_dvd_two hrel
      Nat.prime_three (by norm_num) hD hβ3
    have hinj := conj_injective_of_center_eq_bot
      (center_statedProj_eq_bot (F := F) hr (not_two_two hF hf hne))
    have ht3 : t ^ 3 = 1 := hinj (by rw [map_pow, ht, hβ3, map_one])
    obtain ⟨x, hx, hx3⟩ :=
      CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.exists_proj_eq_pow_eq_one_sp
        (by omega) Nat.prime_three (by norm_num) ht3
    have hax : uniAut e ⟨a, hBK ha⟩ = MulAut.conj (SymplecticFlag.proj r F x) := by
      rw [hx, ht]
    have hx1 : x ≠ 1 := by
      rintro rfl
      apply ha1
      rw [hax, map_one, map_one]
    rw [hax] at hJc
    exact spComp_cases_inner hB hBK hF hf hr e ha hx3 hx1 hax hJK hJq hJc
  ·
    have hord : orderOf (uniAut e ⟨a, hBK ha⟩) = 3 := orderOf_eq_prime hβ3 ha1
    obtain ⟨-, σ, hσ, h, -, hβeq⟩ := hO.descent 3 Nat.prime_three _ hE hD hord
    exact (spComp_cases_outer hF hf hr e hσ hβeq hJK hJq hJc).imp_right Or.inl

end CFSG.HardMathSupport.Dickson.Bal207.FirstClaim

end
