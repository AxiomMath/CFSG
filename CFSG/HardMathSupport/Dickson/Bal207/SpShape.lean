module

public import CFSG.HardMathSupport.Dickson.Bal207.SpShapeIdx
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherAutomorphismData
import all CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SympInnerExport
import all CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SympFieldExport
import all CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSp
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSL
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSU
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.SympAut
import CFSG.LocalAnalysis.AGLEmbedding.ThreeCentLieTwoOBlocks
import CFSG.RankThree.PartOne.KC.SymplecticFullCentralizerSemi
import CFSG.RankThree.PartOne.KC.SymplecticSubfieldOuter
public import CFSG.LocalAnalysis.ComponentClassification.PresentationLocalSymplecticSix
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogQuadraticDescent
public import CFSG.RankThree.CentralLift.DefiningUnitary
public import CFSG.RankThree.Classical.SteinbergBJUnitaryTwoBlock
public import CFSG.RankThree.PartOne.KC.PrimaryDecomposition
public import CFSG.RankThree.PartOne.S11d.OutAbstract

public section

namespace CFSG.HardMathSupport.Dickson.Bal207

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

section Generic

variable {S : Type} [Group S]

theorem map_fixSubgroup_of_commute {β ω : MulAut S} (h : ω * β = β * ω) :
    (fixSubgroup β).map ω.toMonoidHom = fixSubgroup β := by
  have hc : MulAut.congr ω β = β := by
    ext y
    rw [MulAut.congr_apply]
    have := congrArg (fun φ : MulAut S => φ (ω.symm y)) h
    simp only [MulAut.mul_apply, MulEquiv.apply_symm_apply] at this
    exact this
  have h1 := fixSubgroup_mulAutCongr ω β
  rw [hc] at h1
  exact h1.symm

theorem isComponentOf_map_of_commute {β ω : MulAut S} (h : ω * β = β * ω) {L : Subgroup S}
    (hL : IsComponentOf L (fixSubgroup β)) :
    IsComponentOf (L.map ω.toMonoidHom) (fixSubgroup β) := by
  have h1 := CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map ω hL
  have h2 : (fixSubgroup β).map (ω : S →* S) = fixSubgroup β := map_fixSubgroup_of_commute h
  rw [h2] at h1
  exact h1

theorem norm_of_subsingleton {β : MulAut S}
    (h : ∀ L L' : Subgroup S, IsComponentOf L (fixSubgroup β) →
      IsComponentOf L' (fixSubgroup β) → L = L') :
    ∀ ω : MulAut S, ω * β = β * ω → ∀ L : Subgroup S, IsComponentOf L (fixSubgroup β) →
      L.map ω.toMonoidHom = L :=
  fun _ hω _ hL => h _ _ (isComponentOf_map_of_commute hω hL) hL

theorem spCompType_of_cover {Y L : Type} [Group Y] [Group L] (hY : commutator Y = ⊤)
    (ψ : Y →* L) (hψ : Function.Surjective ψ) (hk : ψ.ker ≤ Subgroup.center Y)
    (hT : SpCompType (Y ⧸ Subgroup.center Y)) : SpCompType (L ⧸ Subgroup.center L) := by
  obtain ⟨e⟩ := nonempty_centralQuotient_mulEquiv hY ψ hψ hk
  exact isoInvariant_spCompType _ _ e hT

theorem center_eq_bot_of_simple {T : Type*} [Group T] [IsSimpleGroup T] [Group.IsPerfect T] :
    Subgroup.center T = ⊥ := by
  rcases (inferInstance : (Subgroup.center T).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exact absurd (Subgroup.center_eq_top_iff.1 h) (Group.IsPerfect.not_isMulCommutative _)

theorem spCompType_centerQuot {Q : Type} [Group Q] (hc : Subgroup.center Q = ⊥)
    (h : SpCompType Q) : SpCompType (Q ⧸ Subgroup.center Q) :=
  isoInvariant_spCompType _ _
    ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).symm h

theorem conj_injective_of_center_eq_bot {T : Type*} [Group T] (h : Subgroup.center T = ⊥) :
    Function.Injective (MulAut.conj : T →* MulAut T) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← h]
  intro t ht
  rw [Subgroup.mem_center_iff]
  intro g
  have h1 := congrArg (fun φ : MulAut T => φ g) ((MonoidHom.mem_ker).1 ht)
  simp only [MulAut.conj_apply, MulAut.one_apply] at h1
  calc g * t = t * g * t⁻¹ * t := by rw [h1]
    _ = t * g := by group

private theorem congr_self_eq' (ϕ x : MulAut S) : MulAut.congr (ϕ : S ≃* S) x = ϕ * x * ϕ⁻¹ := by
  ext y
  rfl

end Generic

section CharTwo

variable {r : ℕ} {F : Type} [Field F] [Finite F] {f : ℕ}

theorem ker_proj_eq_bot_of_two (hr : 1 ≤ r) (hF : Nat.card F = 2 ^ f) (hf : f = 1 ∨ f = 3) :
    (SymplecticFlag.proj r F).ker = ⊥ := by
  rw [SymplecticHigher.ker_proj, ← Subgroup.card_eq_one, card_spScalars_eq_gcd F hr, hF]
  rcases hf with rfl | rfl <;> norm_num

theorem center_statedProj_eq_bot (hr : 2 ≤ r) (hne : ¬(r = 2 ∧ Nat.card F = 2)) :
    Subgroup.center (StatedProj (StatedSp r F)) = ⊥ := by
  obtain ⟨hs, hp⟩ := CFSG.RankThree.PartOne.KCSpComm.simple_perfect_statedProj (k := F) hr hne
  exact center_eq_bot_of_simple

private theorem not_two_two (hF : Nat.card F = 2 ^ f) (hf : f = 1 ∨ f = 3)
    (hne : ¬(r = 2 ∧ f = 1)) : ¬(r = 2 ∧ Nat.card F = 2) := by
  rintro ⟨rfl, h2⟩
  rcases hf with rfl | rfl
  · exact hne ⟨rfl, rfl⟩
  · rw [hF] at h2
    norm_num at h2

end CharTwo

section Factors

variable {r : ℕ} {F : Type} [Field F]

private def SpGood (H : Subgroup (StatedSp r F)) : Prop :=
  ∃ (Y : Type) (_ : Group Y) (ψ : Y →* StatedSp r F), Function.Injective ψ ∧ ψ.range = H ∧
    commutator Y = ⊤ ∧ SpCompType (Y ⧸ Subgroup.center Y)

open CFSG.ComponentClassification.PresentationLocal (sympFour isSimpleGroup_commutator_sympFour
  isPerfect_commutator_sympFour commutatorEquivAlternating) in
private theorem spGood_sp [Finite F] {f : ℕ} (hF : Nat.card F = 2 ^ f) (hf : f = 1 ∨ f = 3)
    {A : Subgroup (StatedSp r F)} {s : ℕ} (hs : 1 ≤ s) (φ : A ≃* StatedSp s F)
    (hQ : CFSG.IsQuasisimple ↥⁅A, A⁆) : SpGood ⁅A, A⁆ := by
  classical
  haveI := Fintype.ofFinite F
  have hcard : Fintype.card F = 2 ^ f := by rw [Fintype.card_eq_nat_card, hF]
  by_cases hs1 : s = 1
  · subst hs1
    let e1 : Matrix.SpecialLinearGroup (Fin 2) F ≃* StatedSp 1 F :=
      CFSG.ClassicalInvolution.Models.SymplecticPairs.longBlockEquivOne F
    have h4 : 4 ≤ Fintype.card F := four_le_card_of_equiv_sl_two (φ.trans e1.symm) hQ
    have hF8 : Nat.card F = 8 := by
      rcases hf with rfl | rfl
      · rw [hcard] at h4
        norm_num at h4
      · rw [hF]
        norm_num
    have hX := slFactorFacts_holds F 2 le_rfl (fun _ => h4)
    exact ⟨Matrix.SpecialLinearGroup (Fin 2) F, inferInstance,
      A.subtype.comp (φ.symm.toMonoidHom.comp e1.toMonoidHom),
      Subtype.val_injective.comp (φ.symm.injective.comp e1.injective),
      range_comp_eq_commutator φ _ (range_equiv_eq_commutator e1 hX.perfect), hX.perfect,
      spCompType_psl2 hF8⟩
  · have hs2 : 2 ≤ s := by omega
    by_cases hsp : s = 2 ∧ f = 1
    · obtain ⟨rfl, rfl⟩ := hsp
      have hk : Nat.card F = 2 := by rw [hF]; norm_num
      have hX := spFourTwoFacts_holds F (by rw [hcard]; norm_num)
      refine ⟨↥(commutator ↥(StatedSp 2 F)), inferInstance,
        A.subtype.comp (φ.symm.toMonoidHom.comp (commutator ↥(StatedSp 2 F)).subtype),
        Subtype.val_injective.comp (φ.symm.injective.comp Subtype.val_injective),
        range_comp_eq_commutator φ _ (Subgroup.range_subtype _), hX.perfect, Or.inl ?_⟩
      let e : ↥(commutator ↥(StatedSp 2 F)) ≃* ↥(commutator sympFour) := commutatorSpFourEquiv hk
      haveI : IsSimpleGroup ↥(commutator sympFour) := isSimpleGroup_commutator_sympFour
      haveI : Group.IsPerfect ↥(commutator sympFour) := isPerfect_commutator_sympFour
      haveI : IsSimpleGroup ↥(commutator ↥(StatedSp 2 F)) := e.isSimpleGroup
      haveI : Group.IsPerfect ↥(commutator ↥(StatedSp 2 F)) :=
        Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
      exact ⟨(QuotientGroup.quotientMulEquivOfEq center_eq_bot_of_simple).trans
        (QuotientGroup.quotientBot.trans (e.trans commutatorEquivAlternating))⟩
    · have hne' : (s, Fintype.card F) ≠ (2, 2) := by
        intro h
        have h1 := congrArg Prod.fst h
        have h2 := congrArg Prod.snd h
        simp only at h1 h2
        rw [hcard] at h2
        refine hsp ⟨h1, ?_⟩
        rcases hf with rfl | rfl
        · rfl
        · norm_num at h2
      have hX := spFactorFacts_holds F s hs2 hne'
      have hθ : (MonoidHom.id ↥(StatedSp s F)).range = commutator ↥(StatedSp s F) := by
        rw [MonoidHom.range_eq_top.2 Function.surjective_id, hX.perfect]
      exact ⟨↥(StatedSp s F), inferInstance,
        A.subtype.comp (φ.symm.toMonoidHom.comp (MonoidHom.id _)),
        Subtype.val_injective.comp (φ.symm.injective.comp Function.injective_id),
        range_comp_eq_commutator φ _ hθ, hX.perfect,
        isoInvariant_spCompType _ _ (CFSG.LieType.Universal.Symplectic.centerQuotientEquiv s F).symm
          (spCompType_psp hF hf hs2 hsp)⟩

open CFSG.RankThree.CentralLift CFSG.RankThree.Classical CFSG.ClassicalGroups.UnitaryFlag in
private theorem spGood_gu {g : ℕ} (hg : g = 1 ∨ g = 3) {E : Type} [Field E]
    (hE : UnitaryFieldData 2 g E) {V : Type} [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    {Hf : V →ₛₗ[hE.bar] V →ₗ[E] E} (hHf : Hf.IsSymm) (hHfl : Hf.SeparatingLeft) {m : ℕ}
    (b : Module.Basis (Fin m) E V) (hb : ∀ i j, Hf (b i) (b j) = if i = j then 1 else 0)
    {A : Subgroup (StatedSp r F)} (φ : A ≃* sesqUnitaryGroup Hf)
    (hQ : CFSG.IsQuasisimple ↥⁅A, A⁆) : SpGood ⁅A, A⁆ := by
  classical
  have hfin : Module.finrank E V = m := by rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  have hsolv : ¬ (Module.finrank E V ≤ 1 ∨ ¬ ((Module.finrank E V = 2 → 4 ≤ 2 ^ g) ∧
      (Module.finrank E V = 3 → 3 ≤ 2 ^ g))) := fun h => by
    haveI := isSolvable_sesqUnitaryGroup_of_small hE hHf hHfl h
    exact not_isSolvable_of_isQuasisimple_commutator hQ
      (Group.isSolvable_of_isSolvable_injective (f := φ.toMonoidHom) φ.injective)
  rw [hfin] at hsolv
  push Not at hsolv
  obtain ⟨hm, hq2, hq3⟩ := hsolv
  haveI := hE.finite
  haveI := Fintype.ofFinite E
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP E 2 := hE.charP
  have hEcard : Fintype.card E = (2 ^ g) ^ 2 := by
    rw [Fintype.card_eq_nat_card]
    exact hE.card_eq_sq
  rcases Nat.lt_or_ge m 3 with hm3 | hm3
  · obtain rfl : m = 2 := by omega
    obtain ⟨e⟩ := nonempty_sesqSpecialUnitaryGroup_mulEquiv_SL2 hE hHf hHfl hfin
    haveI : Fintype ↥hE.fixedField := Fintype.ofFinite _
    have hFcard : Fintype.card ↥hE.fixedField = 2 ^ g := by
      rw [Fintype.card_eq_nat_card]
      exact hE.card_fixedField
    have h4 : 4 ≤ Fintype.card ↥hE.fixedField := by rw [hFcard]; exact hq2 rfl
    have h8 : Nat.card ↥hE.fixedField = 8 := by
      rw [hE.card_fixedField]
      rcases hg with rfl | rfl
      · have := hq2 rfl
        norm_num at this
      · norm_num
    have hX := slFactorFacts_holds ↥hE.fixedField 2 le_rfl (fun _ => h4)
    obtain ⟨ψ, hψi, hψ⟩ := exists_range_of_special_equiv hE hHf hHfl (by omega) φ hX.perfect e
    exact ⟨Matrix.SpecialLinearGroup (Fin 2) ↥hE.fixedField, inferInstance, ψ, hψi, hψ,
      hX.perfect, spCompType_psl2 h8⟩
  · have hnq : (m, 2 ^ g) ≠ (3, 2) := by
      intro h
      have h1 := congrArg Prod.fst h
      have h2 := congrArg Prod.snd h
      simp only at h1 h2
      have := hq3 h1
      omega
    have hX := suFactorFacts_holds E m (2 ^ g) hEcard hm3 hnq
    obtain ⟨e⟩ := nonempty_sesqSpecialUnitaryGroup_mulEquiv_gramSU hE b
      (G := (1 : Matrix (Fin m) (Fin m) E)) (fun i j => by rw [hb i j, Matrix.one_apply])
    have hSUeq : StatedSU m (2 ^ g) E = gramSU hE (1 : Matrix (Fin m) (Fin m) E) :=
      unitarySU_eq_gramSU hE m
    let e' : ↥(sesqSpecialUnitaryGroup Hf) ≃* ↥(StatedSU m (2 ^ g) E) :=
      e.trans (MulEquiv.subgroupCongr hSUeq.symm)
    obtain ⟨ψ, hψi, hψ⟩ := exists_range_of_special_equiv hE hHf hHfl (by omega) φ hX.perfect e'
    exact ⟨↥(StatedSU m (2 ^ g) E), inferInstance, ψ, hψi, hψ, hX.perfect,
      spCompType_psu hE.card_eq_sq hg hm3 hnq⟩

end Factors

section Poly

open Polynomial

variable {F : Type} [Field F] [Finite F] {f : ℕ}

theorem irreducible_X_sq_add_X_add_one_of_card (hF : Nat.card F = 2 ^ f) (hf : f = 1 ∨ f = 3) :
    Irreducible (X ^ 2 + X + 1 : F[X]) := by
  classical
  haveI := Fintype.ofFinite F
  have hcard : Fintype.card F = 2 ^ f := by rw [Fintype.card_eq_nat_card, hF]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (f := f) hcard
  have hdeg : (X ^ 2 + X + 1 : F[X]).natDegree = 2 := by compute_degree!
  refine irreducible_of_degree_le_three_of_not_isRoot (by rw [hdeg]; decide) fun μ hμ => ?_
  rw [IsRoot, eval_add, eval_add, eval_pow, eval_X, eval_one] at hμ
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    simp at hμ
  have hμ3 : μ ^ 3 = 1 := by linear_combination (μ - 1) * hμ
  have hμq : μ ^ (Fintype.card F - 1) = 1 := FiniteField.pow_card_sub_one_eq_one μ hμ0
  have hμ1 : μ = 1 := by
    rw [hcard] at hμq
    rcases hf with rfl | rfl
    · simpa using hμq
    · have h7 : μ ^ 7 = 1 := by norm_num at hμq; exact hμq
      calc μ = (μ ^ 3) ^ 2 * μ := by rw [hμ3, one_pow, one_mul]
        _ = μ ^ 7 := by ring
        _ = 1 := h7
  subst hμ1
  have h10 : (1 : F) = 0 := by linear_combination hμ - h2
  exact one_ne_zero h10

theorem primaryFactor_cases_of_card (hF : Nat.card F = 2 ^ f) (hf : f = 1 ∨ f = 3)
    {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V] {y : Module.End F V}
    (hy : y ^ 3 = 1) {k : F[X]} (hk : k ∈ CFSG.RankThree.PartOne.KCPrimary.primaryFactors y) :
    k = X - 1 ∨ k = X ^ 2 + X + 1 := by
  obtain ⟨hki, hkm, hkd⟩ := CFSG.RankThree.PartOne.KCPrimary.mem_primaryFactors.mp hk
  have hdvd : minpoly F y ∣ (X - 1) * (X ^ 2 + X + 1) := by
    refine minpoly.dvd F y ?_
    have : ((X - 1) * (X ^ 2 + X + 1) : F[X]) = X ^ 3 - 1 := by ring
    rw [this, map_sub, map_pow, aeval_X, map_one, hy, sub_self]
  rcases hki.prime.dvd_or_dvd (hkd.trans hdvd) with h | h
  · left
    exact eq_of_monic_of_associated hkm CFSG.RankThree.Classical.monic_X_sub_one
      (hki.associated_of_dvd CFSG.RankThree.Classical.irreducible_X_sub_one h)
  · right
    exact eq_of_monic_of_associated hkm (by monicity!)
      (hki.associated_of_dvd (irreducible_X_sq_add_X_add_one_of_card hF hf) h)

omit [Finite F] in
theorem map_ringEquiv_of_cases (σ : F ≃+* F) {k : F[X]} (hk : k = X - 1 ∨ k = X ^ 2 + X + 1) :
    k.map (σ : F →+* F) = k := by
  rcases hk with rfl | rfl <;> simp [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_pow]

omit [Finite F] in
theorem X_sq_add_X_add_one_ne : (X ^ 2 + X + 1 : F[X]) ≠ X - 1 := by
  intro h
  have h1 := congrArg natDegree h
  have h2 : (X ^ 2 + X + 1 : F[X]).natDegree = 2 := by compute_degree!
  have h3 : (X - 1 : F[X]).natDegree = 1 := by compute_degree!
  omega

end Poly

section Semilinear

open Polynomial CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCSpFull
  CFSG.RankThree.PartOne.KCPrimary
open scoped Matrix

variable {r : ℕ} {F : Type} [Field F]

private theorem spEnd_semiConj_semilinMap (A : gsp r F) (σ : F ≃+* F) (g : StatedSp r F)
    (v : Fin r ⊕ Fin r → F) :
    spEnd (semiConj A σ g) (semilinMap A σ v) = semilinMap A σ (spEnd g v) := by
  have hσv : ⇑σ ∘ (((g : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) *ᵥ v) =
      ((g : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F).map σ *ᵥ
        (⇑σ ∘ v) := by
    ext i
    exact RingHom.map_mulVec (σ : F →+* F) _ v i
  unfold semilinMap
  rw [spEnd_apply, spEnd_apply, coe_semiConj, hσv, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  simp only [Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]

private theorem semilinMap_pow_comm (A : gsp r F) (σ : F ≃+* F) {x : StatedSp r F}
    (hx : semiConj A σ x = x) (n : ℕ) (v : Fin r ⊕ Fin r → F) :
    semilinMap A σ ((spEnd x ^ n) v) = (spEnd x ^ n) (semilinMap A σ v) := by
  induction n generalizing v with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, semilinMap_comm A σ hx]

private theorem semilinMap_aeval (A : gsp r F) (σ : F ≃+* F) {x : StatedSp r F}
    (hx : semiConj A σ x = x) (P : F[X]) (v : Fin r ⊕ Fin r → F) :
    semilinMap A σ (aeval (spEnd x) P v) =
      aeval (spEnd x) (P.map (σ : F →+* F)) (semilinMap A σ v) := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, LinearMap.add_apply, semilinMap_add, hp, hq, Polynomial.map_add, map_add,
      LinearMap.add_apply]
  | monomial n c =>
    simp only [aeval_monomial, Polynomial.map_monomial, Module.End.mul_apply,
      Module.algebraMap_end_apply, semilinMap_smul, semilinMap_pow_comm A σ hx,
      RingEquiv.coe_toRingHom]

private theorem semilinMap_mem_primaryComponent_iff (A : gsp r F) (σ : F ≃+* F)
    {x : StatedSp r F} (hx : semiConj A σ x = x) {k : F[X]} (hk : k.map (σ : F →+* F) = k)
    (v : Fin r ⊕ Fin r → F) :
    semilinMap A σ v ∈ primaryComponent (spEnd x) k ↔ v ∈ primaryComponent (spEnd x) k := by
  rw [mem_primaryComponent, mem_primaryComponent]
  have h1 := semilinMap_aeval A σ hx k v
  rw [hk] at h1
  rw [← h1]
  constructor
  · intro h
    exact semilinMap_injective A σ (h.trans (semilinMap_zero A σ).symm)
  · intro h
    rw [h, semilinMap_zero]

private theorem semiConj_mem_spSupported [Finite F] (A : gsp r F) (σ : F ≃+* F)
    {x : StatedSp r F} (hx : semiConj A σ x = x)
    (hσ : ∀ k ∈ primaryFactors (spEnd x), k.map (σ : F →+* F) = k) {O : Set F[X]}
    {g : StatedSp r F} (hg : g ∈ spSupported x O) : semiConj A σ g ∈ spSupported x O := by
  obtain ⟨hgx, hfix⟩ := mem_spSupported.mp hg
  refine mem_spSupported.mpr ⟨?_, fun k hk hkO v hv => ?_⟩
  · calc semiConj A σ g * x = semiConj A σ g * semiConj A σ x := by rw [hx]
      _ = semiConj A σ (g * x) := (map_mul _ _ _).symm
      _ = semiConj A σ (x * g) := by rw [hgx]
      _ = semiConj A σ x * semiConj A σ g := map_mul _ _ _
      _ = x * semiConj A σ g := by rw [hx]
  · obtain ⟨w, rfl⟩ := Finite.surjective_of_injective (semilinMap_injective A σ) v
    have hw : w ∈ primaryComponent (spEnd x) k :=
      (semilinMap_mem_primaryComponent_iff A σ hx (hσ k hk) w).mp hv
    rw [spEnd_semiConj_semilinMap, hfix k hk hkO w hw]

end Semilinear

section Inner

open Polynomial CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCSpIsotypic
open CFSG.RankThree.PartOne.KCOrthogonal (reciprocalPolynomial)

variable {r : ℕ} {F : Type} [Field F] [Finite F] {f : ℕ}

omit [Finite F] in
private theorem reciprocal_eq_of_cases {k : F[X]} (hk : k = X - 1 ∨ k = X ^ 2 + X + 1) :
    reciprocalPolynomial k = k := by
  rcases hk with rfl | rfl
  · exact CFSG.RankThree.PartOne.KCOrthogonal.reciprocalPolynomial_X_sub_one
  · exact CFSG.AGLEmbedding.reciprocalPolynomial_X_sq_add_X_add_one

private theorem spGood_orbit (hF : Nat.card F = 2 ^ f) (hf : f = 1 ∨ f = 3) {x : StatedSp r F}
    (hx : x ^ 3 = 1) {a : StatedProj (StatedSp r F)} (hsq : Squarefree (minpoly F (spEnd x)))
    (blocks : SpPrimaryBlocks 2 f 3 x a) (h : primaryFactors (spEnd x))
    (hQ : CFSG.IsQuasisimple ↥⁅spSupported x {(h : F[X]), reciprocalPolynomial (h : F[X])},
      spSupported x {(h : F[X]), reciprocalPolynomial (h : F[X])}⁆) :
    SpGood ⁅spSupported x {(h : F[X]), reciprocalPolynomial (h : F[X])},
      spSupported x {(h : F[X]), reciprocalPolynomial (h : F[X])}⁆ := by
  have hX3 : spEnd x ^ 3 = 1 := spEnd_pow hx
  have hcases := primaryFactor_cases_of_card hF hf hX3 h.2
  have hself : reciprocalPolynomial (h : F[X]) = h := reciprocal_eq_of_cases hcases
  rw [hself, Set.pair_eq_singleton] at hQ ⊢
  by_cases h1 : (h : F[X]) = X - 1
  · obtain ⟨h0, hm⟩ := h
    change h0 = X - 1 at h1
    subst h1
    obtain ⟨φ, -⟩ := blocks.fixedFactor hm
    haveI : Nontrivial (primaryComponent (spEnd x) (X - 1)) :=
      Submodule.nontrivial_iff_ne_bot.mpr (primaryComponent_ne_bot hsq hm)
    obtain ⟨s, hs, ⟨e⟩⟩ := exists_mulEquiv_sesqUnitaryGroup_statedSp
      (B := (spForm r F).restrict (primaryComponent (spEnd x) (X - 1)))
      (fun v => spForm_isAlt (v : Fin r ⊕ Fin r → F)) blocks.fixed_nondegenerate
    have hs1 : 1 ≤ s := by
      have := Module.finrank_pos (R := F) (M := primaryComponent (spEnd x) (X - 1))
      omega
    exact spGood_sp hF hf hs1 (φ.trans e) hQ
  · have h3 : (h : F[X]) = X ^ 2 + X + 1 := hcases.resolve_left h1
    obtain ⟨d, hd, -, σ, -, -, -, -, -, hE, -, Hf, hHf, hHfl, -, ⟨e, he⟩, φ, -⟩ :=
      (blocks.selfDual h h1 hself).exists_half
    have hdeg : (X ^ 2 + X + 1 : F[X]).natDegree = 2 := by compute_degree!
    have hd1 : d = 1 := by
      rw [h3, hdeg] at hd
      omega
    subst hd1
    exact spGood_gu (by rw [mul_one]; exact hf) hE hHf hHfl e he φ hQ

private theorem two_le_primaryMultiplicity {x : StatedSp r F} {a : StatedProj (StatedSp r F)}
    (blocks : SpPrimaryBlocks 2 f 3 x a) (hh : (X ^ 2 + X + 1 : F[X]) ∈ primaryFactors (spEnd x))
    (hQ : CFSG.IsQuasisimple ↥⁅spSupported x {X ^ 2 + X + 1, reciprocalPolynomial (X ^ 2 + X + 1)},
      spSupported x {X ^ 2 + X + 1, reciprocalPolynomial (X ^ 2 + X + 1)}⁆) :
    2 ≤ primaryMultiplicity (spEnd x) (X ^ 2 + X + 1) := by
  have hself : reciprocalPolynomial (X ^ 2 + X + 1 : F[X]) = X ^ 2 + X + 1 :=
    CFSG.AGLEmbedding.reciprocalPolynomial_X_sq_add_X_add_one
  rw [hself, Set.pair_eq_singleton] at hQ
  obtain ⟨g, hg⟩ : ∃ g : primaryFactors (spEnd x), (g : F[X]) = X ^ 2 + X + 1 := ⟨⟨_, hh⟩, rfl⟩
  rw [← hg] at hQ hself ⊢
  have h1 : (g : F[X]) ≠ X - 1 := by
    rw [hg]
    exact X_sq_add_X_add_one_ne
  obtain ⟨d, -, -, σ, -, -, -, -, -, hE, -, Hf, hHf, hHfl, -, ⟨e, -⟩, φ, -⟩ :=
    (blocks.selfDual g h1 hself).exists_half
  by_contra hlt
  have hfin := Module.finrank_eq_card_basis e
  rw [Fintype.card_fin] at hfin
  haveI := isSolvable_sesqUnitaryGroup_of_small hE hHf hHfl (Or.inl (by rw [hfin]; omega))
  exact not_isSolvable_of_isQuasisimple_commutator hQ
    (Group.isSolvable_of_isSolvable_injective (f := φ.toMonoidHom) φ.injective)

open scoped Classical in
private theorem three_le_rank {x : StatedSp r F} {a : StatedProj (StatedSp r F)}
    (blocks : SpPrimaryBlocks 2 f 3 x a) (hsq : Squarefree (minpoly F (spEnd x)))
    (h1 : (X - 1 : F[X]) ∈ primaryFactors (spEnd x))
    (h3 : (X ^ 2 + X + 1 : F[X]) ∈ primaryFactors (spEnd x))
    (hm : 2 ≤ primaryMultiplicity (spEnd x) (X ^ 2 + X + 1)) : 3 ≤ r := by
  obtain ⟨s, hs, ⟨P, hP⟩, hrank⟩ := blocks.rank
  have hr := hrank P hP
  have hs1 : 1 ≤ s := by
    haveI : Nontrivial (primaryComponent (spEnd x) (X - 1)) :=
      Submodule.nontrivial_iff_ne_bot.mpr (primaryComponent_ne_bot hsq h1)
    have := Module.finrank_pos (R := F) (M := primaryComponent (spEnd x) (X - 1))
    omega
  have hmem : (X ^ 2 + X + 1 : F[X]) ∈ (primaryFactors (spEnd x)).filter
      (fun h => reciprocalPolynomial h = h ∧ h ≠ X - 1) :=
    Finset.mem_filter.mpr ⟨h3, CFSG.AGLEmbedding.reciprocalPolynomial_X_sq_add_X_add_one,
      X_sq_add_X_add_one_ne⟩
  have hle := Finset.single_le_sum
    (f := fun h : F[X] => h.natDegree / 2 * primaryMultiplicity (spEnd x) h)
    (fun _ _ => Nat.zero_le _) hmem
  have hdeg : (X ^ 2 + X + 1 : F[X]).natDegree = 2 := by compute_degree!
  simp only [hdeg] at hle
  omega

theorem compShape_conj_sp (hr : 2 ≤ r) (hF : Nat.card F = 2 ^ f) (hf : f = 1 ∨ f = 3)
    (hne : ¬(r = 2 ∧ f = 1)) (x : StatedSp r F) (hx : x ^ 3 = 1) (hx1 : x ≠ 1) :
    CompShape SpCompType (MulAut.conj (SymplecticFlag.proj r F x)) := by
  classical
  have hf1 : 1 ≤ f := by omega
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := Fintype.ofFinite F
  have hcardF : Fintype.card F = 2 ^ f := by rw [Fintype.card_eq_nat_card, hF]
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (f := f) hcardF
  have hq : 2 ≤ 2 ^ f := Nat.le_self_pow (by omega) 2
  have hlayer := LieSemisimple.perfectInLayer_conj_sp Nat.prime_two hf1 hF (by omega)
    Nat.prime_three (by norm_num) (by norm_num) x hx
  have hker := ker_proj_eq_bot_of_two (r := r) (by omega) hF hf
  have hZc : (SymplecticFlag.proj r F).ker ≤ Subgroup.center (StatedSp r F) := by
    rw [hker]
    exact bot_le
  have ha1 : SymplecticFlag.proj r F x ≠ 1 := fun h =>
    hx1 ((MonoidHom.ker_eq_bot_iff _).1 hker (by rw [h, map_one]))
  have ha : orderOf (SymplecticFlag.proj r F x) = 3 :=
    orderOf_eq_prime (by rw [← map_pow, hx, map_one]) ha1
  have hxp : orderOf x = 3 := orderOf_eq_prime hx hx1
  have blocks := (symplectic_cross_prime_primary_centralizer_blocks Nat.prime_two hf1 hF
    Nat.prime_three (by norm_num) (by norm_num) (by omega) _ ha).2 x rfl hxp
  have hpK : ((3 : ℕ) : F) ≠ 0 := by
    intro h
    rw [CharP.cast_eq_zero_iff F 2] at h
    norm_num at h
  have hsq := (altPrimaryData_spLin hpK hx).squarefree
  have hX3 : spEnd x ^ 3 = 1 := spEnd_pow hx
  haveI : Finite (reciprocalOrbits (spEnd x)) :=
    (Set.Finite.image _ (Finset.finite_toSet _)).to_subtype
  obtain ⟨hcomm, -, hjoin⟩ := blocks.directProduct
  have hcomp := components_conj_of_orbit_family (SymplecticFlag.proj r F)
    SymplecticHigher.proj_surjective hZc x
    (fun O : reciprocalOrbits (spEnd x) => spSupported x (O : Set F[X]))
    (fun i j hij a ha b hb => hcomm i.1 i.2 j.1 j.2 (fun h => hij (Subtype.ext h)) a ha b hb)
    hjoin (fun O => LieSemisimple.quasisimple_or_solvable_spSupported (by norm_num) hq hsq
      blocks O)
  refine ⟨hlayer, fun L hL => ?_, ?_⟩
  ·
    obtain ⟨⟨O, h, hh, rfl⟩, hO, rfl⟩ := hcomp L hL
    obtain ⟨Y, _, ψ, hψ, hrange, hperf, hT⟩ := spGood_orbit hF hf hx hsq blocks ⟨h, hh⟩ hO
    obtain ⟨φ, hφ, hφk⟩ := exists_cover_of_range (SymplecticFlag.proj r F) hZc ψ hψ hrange
    exact spCompType_of_cover hperf φ hφ hφk hT
  · by_cases hr2 : r = 2
    ·
      refine norm_of_subsingleton fun L L' hL hL' => ?_
      obtain ⟨⟨O, h, hh, rfl⟩, hO, rfl⟩ := hcomp L hL
      obtain ⟨⟨O', h', hh', rfl⟩, hO', rfl⟩ := hcomp L' hL'
      have hcase := primaryFactor_cases_of_card hF hf hX3 hh
      have hcase' := primaryFactor_cases_of_card hF hf hX3 hh'
      rcases hcase with rfl | rfl <;> rcases hcase' with rfl | rfl
      · rfl
      · exact absurd (three_le_rank blocks hsq hh hh' (two_le_primaryMultiplicity blocks hh' hO'))
          (by omega)
      · exact absurd (three_le_rank blocks hsq hh' hh (two_le_primaryMultiplicity blocks hh hO))
          (by omega)
      · rfl
    ·
      intro ω hω L hL
      obtain ⟨⟨O, h, hh, rfl⟩, hO, rfl⟩ := hcomp L hL
      obtain ⟨A, σ, rfl⟩ := CFSG.RankThree.PartOne.KCSpComm.mem_spSemilinearAutGroup_iff.mp
        (CFSG.RankThree.PartOne.KCSpComm.mem_spSemilinearAutGroup_of_ne_exceptional
          Nat.prime_two hf1 hr hF (fun h => hr2 h.2) ω)
      have hinj := conj_injective_of_center_eq_bot
        (center_statedProj_eq_bot (F := F) hr (not_two_two hF hf hne))
      have hfix := (CFSG.RankThree.PartOne.KCSpFull.commute_conj_iff hinj _ _).mp hω
      rw [CFSG.RankThree.PartOne.KCSpFull.alpha_apply_proj] at hfix
      have hsx : CFSG.RankThree.PartOne.KCSpFull.semiConj A σ x = x :=
        (MonoidHom.ker_eq_bot_iff _).mp hker hfix
      have hσk : ∀ k ∈ primaryFactors (spEnd x), k.map (σ : F →+* F) = k := fun k hk =>
        map_ringEquiv_of_cases σ (primaryFactor_cases_of_card hF hf hX3 hk)
      set A₀ := spSupported x {h, reciprocalPolynomial h} with hA₀
      have hA : A₀.map (CFSG.RankThree.PartOne.KCSpFull.semiConj A σ) ≤ A₀ :=
        Subgroup.map_le_iff_le_comap.mpr fun g hg => semiConj_mem_spSupported A σ hsx hσk hg
      have hcompω : (conjAut r F A * fieldAut r F σ).toMonoidHom.comp (SymplecticFlag.proj r F) =
          (SymplecticFlag.proj r F).comp (CFSG.RankThree.PartOne.KCSpFull.semiConj A σ) :=
        MonoidHom.ext fun g => CFSG.RankThree.PartOne.KCSpFull.alpha_apply_proj A σ g
      have hle : ((⁅A₀, A₀⁆).map (SymplecticFlag.proj r F)).map
          (conjAut r F A * fieldAut r F σ).toMonoidHom ≤
          (⁅A₀, A₀⁆).map (SymplecticFlag.proj r F) := by
        rw [Subgroup.map_map, hcompω, ← Subgroup.map_map]
        refine Subgroup.map_mono ?_
        rw [Subgroup.map_commutator]
        exact Subgroup.commutator_mono hA hA
      exact Subgroup.eq_of_le_of_card_ge hle
        (Subgroup.card_map_of_injective (f := (conjAut r F A * fieldAut r F σ).toMonoidHom)
          (conjAut r F A * fieldAut r F σ).injective).ge

end Inner

section Field

open CFSG.ComponentClassification.UnbalancedCatalog (descentField)
open CFSG.ComponentClassification.PresentationLocal (sympFour isSimpleGroup_commutator_sympFour
  isPerfect_commutator_sympFour commutatorEquivAlternating)

variable {r : ℕ} {F : Type} [Field F] [Finite F] {f : ℕ}

theorem compShape_fieldAut_sp (hr : 2 ≤ r) (hF : Nat.card F = 2 ^ f) (hf : f = 1 ∨ f = 3)
    (σ : F ≃+* F) (hσ : orderOf σ = 3) :
    CompShape SpCompType (SymplecticHigher.fieldAut r F σ) := by
  have hσ3 : σ ^ 3 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  have hodd : Odd 3 := by decide
  have hlayer := LieSemisimple.perfectInLayer_fieldAut_sp hr Nat.prime_three (by norm_num) σ hσ3
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
  haveI : Fintype ↥(descentField σ) := Fintype.ofFinite _
  obtain ⟨e⟩ := nonempty_fixSubgroup_equiv (r := r) hodd hσ3
  by_cases hr2 : r = 2
  · subst hr2
    have hE : ↥(fixSubgroup (SymplecticHigher.fieldAut 2 F σ)) ≃* sympFour :=
      e.trans (CFSG.RankThree.PartOne.KCSpComm.statedProjEquivSympFour hk2)
    set C := fixSubgroup (SymplecticHigher.fieldAut 2 F σ) with hC
    have huniq : ∀ L, IsComponentOf L C → L = (commutator ↥C).map C.subtype := fun L hL =>
      eq_map_commutator_of_isComponentOf hE isSimpleGroup_commutator_sympFour hL
    refine ⟨hlayer, fun L hL => ?_,
      norm_of_subsingleton fun L L' hL hL' => (huniq L hL).trans (huniq L' hL').symm⟩
    obtain rfl := huniq L hL
    have hmap : (commutator ↥C).map hE.toMonoidHom = commutator sympFour := by
      rw [commutator_def, commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
        hE.toMonoidHom.range_eq_top_of_surjective hE.surjective]
    let e₁ : ↥((commutator ↥C).map C.subtype) ≃* ↥(commutator sympFour) :=
      ((commutator ↥C).equivMapOfInjective C.subtype C.subtype_injective).symm.trans
        (((commutator ↥C).equivMapOfInjective hE.toMonoidHom hE.injective).trans
          (MulEquiv.subgroupCongr hmap))
    haveI : IsSimpleGroup ↥(commutator sympFour) := isSimpleGroup_commutator_sympFour
    haveI : Group.IsPerfect ↥(commutator sympFour) := isPerfect_commutator_sympFour
    haveI : IsSimpleGroup ↥((commutator ↥C).map C.subtype) := e₁.isSimpleGroup
    haveI : Group.IsPerfect ↥((commutator ↥C).map C.subtype) :=
      Group.IsPerfect.ofSurjective (f := e₁.symm.toMonoidHom) e₁.symm.surjective
    exact Or.inl ⟨(QuotientGroup.quotientMulEquivOfEq center_eq_bot_of_simple).trans
      (QuotientGroup.quotientBot.trans (e₁.trans commutatorEquivAlternating))⟩
  · have hex : ¬(r = 2 ∧ Nat.card ↥(descentField σ) = 2) := fun h => hr2 h.1
    obtain ⟨hs, hp⟩ :=
      CFSG.RankThree.PartOne.KCSpComm.simple_perfect_statedProj (k := descentField σ) hr hex
    haveI : IsSimpleGroup ↥(fixSubgroup (SymplecticHigher.fieldAut r F σ)) := e.isSimpleGroup
    haveI : Group.IsPerfect ↥(fixSubgroup (SymplecticHigher.fieldAut r F σ)) :=
      Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
    have huniq : ∀ L, IsComponentOf L (fixSubgroup (SymplecticHigher.fieldAut r F σ)) →
        L = fixSubgroup (SymplecticHigher.fieldAut r F σ) := fun L hL =>
      eq_of_isComponentOf_of_simple le_rfl inferInstance (commutator_le_self' _) hL
    refine ⟨hlayer, fun L hL => ?_,
      norm_of_subsingleton fun L L' hL hL' => (huniq L hL).trans (huniq L' hL').symm⟩
    obtain rfl := huniq L hL
    exact spCompType_centerQuot center_eq_bot_of_simple
      (isoInvariant_spCompType _ _ e.symm
        (spCompType_psp (k := 1) (by rw [hk2]; norm_num) (Or.inl rfl) hr (fun h => hr2 h.1)))

end Field

theorem compShape_psp {r : ℕ} {F : Type} [Field F] [Finite F] {f : ℕ} (hF : Nat.card F = 2 ^ f)
    (hf : f = 1 ∨ f = 3) (hr : 2 ≤ r) (hne : ¬(r = 2 ∧ f = 1))
    (β : MulAut (StatedProj (StatedSp r F))) (hβ : β ^ 3 = 1) (hβ1 : β ≠ 1) :
    CompShape SpCompType β := by
  have hf1 : 1 ≤ f := by omega
  have hO := CFSG.RankThree.PartOne.KCSpComm.spOuter (K := F) Nat.prime_two hf1 hr hF
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hodd : Odd (orderOf β) :=
    (Nat.prime_three.odd_of_ne_two (by norm_num)).of_dvd_nat (orderOf_dvd_of_pow_eq_one hβ)
  have hE : β ∈ spSemilinearAutGroup r F :=
    CFSG.RankThree.PartOne.KCSpComm.mem_of_odd_orderOf_of_index_dvd_two _ hO.index_dvd hodd
  by_cases hD : β ∈ spLinearAutGroup r F
  ·
    have : (CFSG.ComponentClassification.OuterAutomorphisms.inner
        (StatedProj (StatedSp r F))).Normal :=
      CFSG.ComponentClassification.OuterAutomorphisms.inner_normal _
    have hrel : (CFSG.ComponentClassification.OuterAutomorphisms.inner
        (StatedProj (StatedSp r F))).relIndex (spLinearAutGroup r F) ∣ 2 :=
      hO.relIndex_dvd.trans (Nat.gcd_dvd_left 2 _)
    obtain ⟨t, rfl⟩ := CFSG.RankThree.PartOne.KCSpComm.mem_of_pow_eq_one_of_relIndex_dvd_two hrel
      Nat.prime_three (by norm_num) hD hβ
    have hinj := conj_injective_of_center_eq_bot
      (center_statedProj_eq_bot (F := F) hr (not_two_two hF hf hne))
    have ht : t ^ 3 = 1 := hinj (by rw [map_pow, hβ, map_one])
    obtain ⟨x, hx, hx3⟩ := LieSemisimple.exists_proj_eq_pow_eq_one_sp (by omega)
      Nat.prime_three (by norm_num) ht
    have hx1 : x ≠ 1 := by
      rintro rfl
      apply hβ1
      rw [← hx, map_one, map_one]
    rw [← hx]
    exact compShape_conj_sp hr hF hf hne x hx3 hx1
  ·
    have hord : orderOf β = 3 := orderOf_eq_prime hβ hβ1
    obtain ⟨-, σ, hσ, h, -, hβeq⟩ := hO.descent 3 Nat.prime_three β hE hD hord
    refine CompShape.of_congr isoInvariant_spCompType (h⁻¹ : MulAut _) ?_
    rw [congr_self_eq', hβeq]
    have : h⁻¹ * (h * fieldAut r F σ * h⁻¹) * h⁻¹⁻¹ = fieldAut r F σ := by group
    rw [this]
    exact compShape_fieldAut_sp hr hF hf σ hσ

end CFSG.HardMathSupport.Dickson.Bal207
