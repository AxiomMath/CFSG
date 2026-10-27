module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.NormalizerAuxE6
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.NormalizerAuxBridge
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.NormalizerAuxGrp
public import CFSG.RankThree.PartOne.KE6.Phi6A2A2
public import CFSG.RankThree.Classical.SteinbergBYExchangedSL3
public import CFSG.RankThree.Classical2.TwistedE6Phi3A2A2
public import CFSG.LieType.Chevalley.GraphFixedCoordinateDetection
public import CFSG.Assembly.QuasithinDefs
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Families
public import CFSG.HardMathSupport.Timmesfeld.Proving.ExistsOrderPCentralizer
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPrimeCoreCentralizer
public import CFSG.LieType.Chevalley.OrdinaryRootHyperplaneGeneration
public import CFSG.LieType.Chevalley.ParabolicRadicalNormalizer
public import CFSG.LieType.Chevalley.ParabolicRadicalsOpposite
public import CFSG.LieType.Ree.LargeReeSylowOpposition
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.GLTheoremB.QuotientTools
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical
public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerExcBruhat
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.KD4T.Certs
public import CFSG.RankThree.PartOne.KE.A1Action
public import CFSG.RankThree.PartOne.KE.A1Levi
public import CFSG.RankThree.PartOne.KE.A1Torus
public import CFSG.RankThree.PartOne.KE.A1TwistedE6
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted
public import CFSG.RankThree.PartOne.KGD.D4Frame
public import CFSG.RankThree.PartOne.KLCE.Sector
public import CFSG.RankThree.PartOne.S9.Sylow.ExclusionBasic
public import CFSG.RankThree.Theta.ThreeComponentOrbitCover

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.NormalizerAux

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.PartOne.KE (wordProd_smul_eq_wordMat_mulVec)
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.RankThree.Lattice
open CFSG.RankThree.E6 (chain13 chain56 support13 support56 supportA2A2 e6Index chainRoot)
open CFSG.RankThree.Classical2 (isRoot_chainRoot56 chainRoot13_mem_parabolicRoots fixSubgroup
  twoA2MulSup twoA2MulSup_surjective twoA2MulSup_eq_one_iff rootSpan_supportA2A2)
open Matrix
open scoped MatrixGroups Matrix
open CFSG.ComponentClassification.OuterAutomorphisms (Outer solvable_of_equiv)

set_option linter.unusedSectionVars false


abbrev c13 (i j : Fin 3) : Fin TwClass.e6Six.tag.rank → ℤ := chainRoot chain13 i j

abbrev c56 (i j : Fin 3) : Fin TwClass.e6Six.tag.rank → ℤ := chainRoot chain56 i j

abbrev Q12 (L : Type) [Field L] : Subgroup (ModGL TwClass.e6Six.tag L) :=
  subsystemGroup Tag.E6 L support13 ⊔ subsystemGroup Tag.E6 L support56

theorem w_e6Six_13 : ∀ i j : Fin 3, i ≠ j →
    wordMat Tag.E6 TwClass.wordE6 *ᵥ chainRoot chain13 i j = chainRoot chain56 i j := by
  decide +kernel

theorem w_e6Six_56 : ∀ i j : Fin 3, i ≠ j →
    wordMat Tag.E6 TwClass.wordE6 *ᵥ chainRoot chain56 i j = chainRoot chain13 i j := by
  decide +kernel

theorem w_e6Six_smul_13 (i j : Fin 3) (hij : i ≠ j) :
    TwClass.w TwClass.e6Six • c13 i j = c56 i j := by
  show (coxeterSystem Tag.E6).wordProd TwClass.wordE6 • chainRoot chain13 i j = chainRoot chain56 i j
  rw [wordProd_smul_eq_wordMat_mulVec]
  exact w_e6Six_13 i j hij

theorem w_e6Six_smul_56 (i j : Fin 3) (hij : i ≠ j) :
    TwClass.w TwClass.e6Six • c56 i j = c13 i j := by
  show (coxeterSystem Tag.E6).wordProd TwClass.wordE6 • chainRoot chain56 i j = chainRoot chain13 i j
  rw [wordProd_smul_eq_wordMat_mulVec]
  exact w_e6Six_56 i j hij

theorem e6Six_twist_13 {K : Type} [Field K] [Finite K]
    (D : LangLevi TwClass.e6Six.tag K TwClass.e6Six.w) (i j : Fin 3) (hij : i ≠ j) :
    ∃ e : D.L, e * e = 1 ∧ ∀ c : D.L,
      ((MulAut.conj (nW D)).toMonoidHom.comp (frobGL D))
          (pinnedX Tag.E6 D.L (chainRoot chain13 i j) c) =
        pinnedX Tag.E6 D.L (chainRoot chain56 i j) (e * D.Fr c) := by
  have hroot : IsRoot TwClass.e6Six.tag (c13 i j) := (chainRoot13_mem_parabolicRoots hij).1
  obtain ⟨ε, hε, h⟩ := exists_canonicalRep_mul_pinnedX_mul_inv D.L TwClass.e6Six.w hroot
  refine ⟨ε, hε, fun c => ?_⟩
  have h' := h (D.Fr c)
  rw [w_e6Six_smul_13 i j hij] at h'
  have e1 : frobGL D (pinnedX Tag.E6 D.L (chainRoot chain13 i j) c) =
      pinnedX Tag.E6 D.L (chainRoot chain13 i j) (D.Fr c) :=
    CFSG.RankThree.PartOne.KE.units_map_entrywiseHom_pinnedX D.Fr _ c
  show nW D * frobGL D (pinnedX Tag.E6 D.L (chainRoot chain13 i j) c) * (nW D)⁻¹ = _
  rw [e1]
  exact h'

theorem e6Six_twist_56 {K : Type} [Field K] [Finite K]
    (D : LangLevi TwClass.e6Six.tag K TwClass.e6Six.w) (i j : Fin 3) (hij : i ≠ j) :
    ∃ e : D.L, e * e = 1 ∧ ∀ c : D.L,
      ((MulAut.conj (nW D)).toMonoidHom.comp (frobGL D))
          (pinnedX Tag.E6 D.L (chainRoot chain56 i j) c) =
        pinnedX Tag.E6 D.L (chainRoot chain13 i j) (e * D.Fr c) := by
  have hroot : IsRoot TwClass.e6Six.tag (c56 i j) := isRoot_chainRoot56 hij
  obtain ⟨ε, hε, h⟩ := exists_canonicalRep_mul_pinnedX_mul_inv D.L TwClass.e6Six.w hroot
  refine ⟨ε, hε, fun c => ?_⟩
  have h' := h (D.Fr c)
  rw [w_e6Six_smul_56 i j hij] at h'
  have e1 : frobGL D (pinnedX Tag.E6 D.L (chainRoot chain56 i j) c) =
      pinnedX Tag.E6 D.L (chainRoot chain56 i j) (D.Fr c) :=
    CFSG.RankThree.PartOne.KE.units_map_entrywiseHom_pinnedX D.Fr _ c
  show nW D * frobGL D (pinnedX Tag.E6 D.L (chainRoot chain56 i j) c) * (nW D)⁻¹ = _
  rw [e1]
  exact h'

theorem e6Six_exchange {K : Type} [Field K] [Finite K]
    (D : LangLevi TwClass.e6Six.tag K TwClass.e6Six.w) :
    ∃ θ : ↥(Q12 D.L) ≃* ↥(Q12 D.L),
      (∀ g, (θ g : ModGL TwClass.e6Six.tag D.L) =
        ((MulAut.conj (nW D)).toMonoidHom.comp (frobGL D)) (g : ModGL TwClass.e6Six.tag D.L)) ∧
      ∃ a b : SL(3, D.L), ∀ A B : SL(3, D.L), θ (twoA2MulSup (A, B)) =
        twoA2MulSup (a * Matrix.SpecialLinearGroup.map D.Fr B * a⁻¹,
          b * Matrix.SpecialLinearGroup.map D.Fr A * b⁻¹) := by
  haveI : IsAlgClosed D.L := IsAlgClosure.isAlgClosed K
  exact CFSG.RankThree.PartOne.KE6.exists_exchanged_layer_pos (Fr := D.Fr)
    (Fr_bijective D).2 ((MulAut.conj (nW D)).toMonoidHom.comp (frobGL D))
    (IsSLFrame.conj_entrywise_injective (nW D) D.Fr) 1 1 (e6Six_twist_13 D) (e6Six_twist_56 D)

theorem S₂_e6Six_eq : TwClass.S₂ TwClass.e6Six = parabolicRoots Tag.E6 supportA2A2 := by
  have hiff : ∀ i : Fin Tag.E6.rank,
      i ∈ CFSG.RankThree.E6.supportA2A2 ↔ i.val ∈ TwClass.J₂ TwClass.e6Six := by
    intro i
    rw [CFSG.RankThree.E6.mem_supportA2A2]
    have key : ∀ k : Fin 6, i = e6Index k ↔ i.val = k.val := fun k => Fin.ext_iff
    rw [key 0, key 2, key 4, key 5]
    simp only [TwClass.J₂, Finset.mem_insert, Finset.mem_singleton]
    exact Iff.rfl
  ext α
  constructor
  · rintro ⟨hr, hs⟩
    exact ⟨hr, fun i hi => hs i fun h => hi ((hiff i).2 h)⟩
  · rintro ⟨hr, hs⟩
    exact ⟨hr, fun i hi => hs i fun h => hi ((hiff i).1 h)⟩

theorem rootSpan_S₂_e6Six (L : Type) [Field L] :
    rootSpan TwClass.e6Six.tag L (TwClass.S₂ TwClass.e6Six) = Q12 L := by
  rw [S₂_e6Six_eq]
  exact rootSpan_supportA2A2 (Ω := L)

theorem e6Six_X₂_outer {K : Type} [Field K] [Finite K]
    (D : LangLevi TwClass.e6Six.tag K TwClass.e6Six.w)
    (hperf : Group.IsPerfect ↥(D.frame (TwClass.S₂ TwClass.e6Six))) :
    Group.IsSolvable (Outer ↥(D.frame (TwClass.S₂ TwClass.e6Six))) := by
  classical
  haveI : IsAlgClosed D.L := IsAlgClosure.isAlgClosed K
  obtain ⟨p, hpK⟩ := CharP.exists K
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨m, hpp, hcard⟩ := FiniteField.card K p
  haveI : Fact p.Prime := ⟨hpp⟩
  have hcard' : Nat.card K = p ^ (m : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  have hFr : ∀ c, D.Fr c = c ^ (p ^ (m : ℕ)) := fun c => by rw [D.hFr, hcard']
  haveI : CharP D.L p := charP_of_injective_algebraMap (algebraMap K D.L).injective p
  obtain ⟨θ, hθΨ, a, b, hθ⟩ := e6Six_exchange D
  obtain ⟨k₂, hk₂, h₁, h₂, ρ, hρ, hρfix, hρnorm, hρqs, hρker, hρkerc, hρiso, hρcen, hfin, hind,
    hder⟩ := CFSG.RankThree.Classical.SteinbergBY.exchanged_sl3_central_product_frobenius_full_fixed_layer
      (k := K) (Ω := D.L) (Q := ↥(Q12 D.L)) hpp m.pos hcard' D.Fr hFr twoA2MulSup
      twoA2MulSup_surjective
      (fun x => twoA2MulSup_eq_one_iff x.1 x.2) θ a b hθ
  set S₂ := TwClass.S₂ TwClass.e6Six with hS₂
  have hspan : rootSpan TwClass.e6Six.tag D.L S₂ = Q12 D.L := rootSpan_S₂_e6Six D.L
  have hΦ : fixedRoot D S₂ = (fixSubgroup θ).map (Q12 D.L).subtype := by
    ext y
    constructor
    · intro hy
      obtain ⟨hy1, hy2⟩ := (mem_fixedRoot D).1 hy
      have hyQ : y ∈ Q12 D.L := by rw [← hspan]; exact hy1
      refine ⟨⟨y, hyQ⟩, ?_, rfl⟩
      show θ ⟨y, hyQ⟩ = ⟨y, hyQ⟩
      apply Subtype.ext
      rw [hθΨ]
      exact hy2
    · rintro ⟨x, hx, rfl⟩
      have hx' : θ x = x := hx
      have hx2 := congrArg Subtype.val hx'
      rw [hθΨ] at hx2
      exact (mem_fixedRoot D).2 ⟨by rw [hspan]; exact x.2, hx2⟩
  set P' : Subgroup (ModGL TwClass.e6Six.tag D.L) := ρ.range.map (Q12 D.L).subtype with hP'
  have hP'le : P' ≤ fixedRoot D S₂ := by
    rw [hΦ]
    exact Subgroup.map_mono hρfix
  have hcomm : ⁅fixedRoot D S₂, fixedRoot D S₂⁆ = P' := by
    have h1 : ⁅fixSubgroup θ, fixSubgroup θ⁆ = ρ.range := by
      have e := congrArg (Subgroup.map (fixSubgroup θ).subtype) hder
      rw [Subgroup.map_subgroupOf_eq_of_le hρfix] at e
      rw [← e, commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
    rw [hΦ, ← Subgroup.map_commutator, h1]
  have hP'perf : ⁅P', P'⁆ = P' := by
    haveI : Group.IsPerfect ↥ρ.range := hρqs.1
    rw [hP', ← Subgroup.map_commutator, Subgroup.commutator_eq_self]
  have hfr : frameImage D S₂ = P' := by
    refine le_antisymm ?_ (le_frameImage_of_perfect D hP'le hP'perf)
    haveI := hperf
    haveI : Group.IsPerfect ↥(frameImage D S₂) :=
      Group.IsPerfect.ofSurjective (f := (frameEquivImage D S₂).toMonoidHom)
        (frameEquivImage D S₂).surjective
    have h2 : ⁅frameImage D S₂, frameImage D S₂⁆ = frameImage D S₂ := Subgroup.commutator_eq_self
    calc frameImage D S₂ = ⁅frameImage D S₂, frameImage D S₂⁆ := h2.symm
      _ ≤ ⁅fixedRoot D S₂, fixedRoot D S₂⁆ :=
          Subgroup.commutator_mono (frameImage_le_fixedRoot D S₂) (frameImage_le_fixedRoot D S₂)
      _ = P' := hcomm
  let e₁ : ↥(D.frame S₂) ≃* ↥ρ.range :=
    (frameEquivImage D S₂).trans ((MulEquiv.subgroupCongr hfr).trans
      (Subgroup.equivMapOfInjective ρ.range (Q12 D.L).subtype (Q12 D.L).subtype_injective).symm)
  obtain ⟨e₂⟩ := hρiso
  have hker_le : ρ.ker ≤ Subgroup.center SL(3, ↥k₂) := by
    intro A hA
    obtain ⟨c, hc3, hAc⟩ := (hρker A).1 hA
    have hent : ∀ i j : Fin 3, (((A : Matrix (Fin 3) (Fin 3) ↥k₂) i j : ↥k₂) : D.L) =
        (Matrix.scalar (Fin 3) (algebraMap K D.L c) : Matrix (Fin 3) (Fin 3) D.L) i j :=
      fun i j => congrArg (fun M : Matrix (Fin 3) (Fin 3) D.L => M i j) hAc
    have hdiag : ∀ i : Fin 3, (((A : Matrix (Fin 3) (Fin 3) ↥k₂) i i : ↥k₂) : D.L) =
        algebraMap K D.L c := fun i => by rw [hent i i]; simp
    have hoff : ∀ i j : Fin 3, i ≠ j → (((A : Matrix (Fin 3) (Fin 3) ↥k₂) i j : ↥k₂) : D.L) = 0 :=
      fun i j hij => by rw [hent i j]; simp [Matrix.scalar_apply, Matrix.diagonal_apply, hij]
    rw [Matrix.SpecialLinearGroup.mem_center_iff]
    refine ⟨(A : Matrix (Fin 3) (Fin 3) ↥k₂) 0 0, ?_, ?_⟩
    · apply Subtype.ext
      rw [Fintype.card_fin, SubmonoidClass.coe_pow, hdiag 0, ← map_pow, hc3, map_one]
      rfl
    · ext i j
      by_cases hij : i = j
      · subst hij
        simp only [Matrix.scalar_apply, Matrix.diagonal_apply_eq]
        rw [hdiag i, hdiag 0]
      · rw [hoff i j hij]
        simp [Matrix.scalar_apply, Matrix.diagonal_apply, hij]
  have hq2 : (p ^ (m : ℕ)) ^ 2 = p ^ (2 * (m : ℕ)) := by rw [← pow_mul, mul_comm]
  have hFcard : Nat.card k₂ = (p ^ (m : ℕ)) ^ 2 := by
    rw [hq2, ← CFSG.RankThree.Classical2.natCard_setOf_pow_eq_self (Ω := D.L) (ℓ := p)
      (by have := m.pos; omega : 2 * (m : ℕ) ≠ 0)]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun c => by rw [hk₂, hq2, Set.mem_setOf_eq])
  haveI : Finite k₂ := Nat.finite_of_card_ne_zero (by
    rw [hFcard]
    exact (pow_pos (pow_pos hpp.pos _) 2).ne')
  haveI : Group.IsSolvable (Outer (SL(3, ↥k₂) ⧸ ρ.ker)) :=
    outer_solvable_SL_quotient (K := ↥k₂) (n := 3) le_rfl hker_le
  exact solvable_of_equiv (e₁.trans e₂.symm).symm

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.NormalizerAux
