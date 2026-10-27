module

public import CFSG.LocalAnalysis.GLTheoremA.S3.KData
public import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterA
public import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterE
public import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterTwisted
public import CFSG.HardMathSupport.Timmesfeld.DefChar.OuterF4G2
public import CFSG.HardMathSupport.Timmesfeld.DefChar.OuterTwisted
public import CFSG.HardMathSupport.Timmesfeld.DefChar.OuterReeG2
public import CFSG.Adapters.LinearCatalog
public import CFSG.RankThree.PartOne.KA.AlternatingPlaneInner
public import CFSG.Quasithin.SteinbergOuterPrimeControl
public import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterTwistedAC
public import CFSG.RankThree.PartTwo.Sec19.Step1919EndProof
public import CFSG.RankThree.PartOne.S12.ModelTransport
public import CFSG.Quasithin.Background.A3Structure36BPrime
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.Dihedral.DihedralFusionPrefixes
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma32
public import CFSG.HardMathSupport.Solomon.LocalBalance.PartIInputs
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Interface
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
public import CFSG.LocalAnalysis.ComponentClassification.KProper
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.PerfectOuterInjection
public import CFSG.LocalAnalysis.GLTheoremA.P55.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I1412Levels
public import CFSG.LocalAnalysis.GLTheoremA.PartI.KD26
public import CFSG.LocalAnalysis.GLTheoremA.S3.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4.Lemma41
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.LargeEvenClassification.TopScalarLiftSquare
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Permutation.AlternatingAutomorphism
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBasic
public import CFSG.RankThree.PartTwo.Sec19.Item194Used
public import CFSG.RankThree.PartTwo.Sec19.Step1914E
public import CFSG.RankThree.PartTwo.Sec19.Steps195
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open CFSG.HardMathSupport.Timmesfeld.DefChar (exists_inner_of_elemAbelian_psl2_all)

private theorem kd76c_U42_model (c f : ℕ) [Fact c.Prime] (hc : c = 2) (hf : f = 1) :
    Nonempty (StatedProj (StatedSU 4 (c ^ f) (GaloisField c (2 * f))) ≃*
      CFSG.Assembly.RankThreeEven.projSU 4 2 1) := by
  subst hc
  subst hf
  exact ⟨(CFSG.Adapters.RankTwoModelTransports.statedProjEquivMapMk _).trans
    (MulEquiv.subgroupCongr (CFSG.RankThree.PartOne.projImage_statedSU_eq_projSU 4 2 1))⟩

@[expose] def KD76cLieP (p : ℕ) (P : TauCeti.LieTypeIndex → Prop) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ idx : TauCeti.ValidLieTypeIndex, P idx.1 → idx.1.characteristic = p →
      Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group) →
      ∀ D : Subgroup (MulAut S), IsElemAbelian p D → Nat.card D = p ^ 2 →
        D ⊓ inner S = ⊥ → p = 3 ∧ isD4ThreePowThree idx.1

@[expose] def KDOpenFam : TauCeti.LieTypeIndex → Prop
  | .B _ _ | .D _ _ | .twistedD _ _ => True
  | _ => False

private theorem kd76c_absurd {S : Type} [Group S] {D : Subgroup (MulAut S)}
    (hDI : D ⊓ inner S = ⊥) {x : MulAut S} (hx : x ∈ D ⊓ inner S) (hx1 : x ≠ 1) : False :=
  hx1 (Subgroup.mem_bot.1 (hDI ▸ hx))

private theorem kd76c_transport {S C : Type} [Group S] [Group C] (e : S ≃* C) {p : ℕ}
    (D : Subgroup (MulAut S)) (hexp : ∀ a ∈ D, a ^ p = 1) (hlt : p < Nat.card D)
    (H : ∀ D' : Subgroup (MulAut C), (∀ a ∈ D', a ^ p = 1) → p < Nat.card D' →
      ∃ x ∈ D' ⊓ inner C, x ≠ 1) :
    ∃ x ∈ D ⊓ inner S, x ≠ 1 := by
  set φ : MulAut S ≃* MulAut C := MulAut.congr e with hφ
  have hcardD : Nat.card (D.map φ.toMonoidHom) = Nat.card D :=
    Subgroup.card_map_of_injective φ.injective
  obtain ⟨x', ⟨hx'D, hx'I⟩, hx'1⟩ := H (D.map φ.toMonoidHom)
    (by
      rintro _ ⟨a, ha, rfl⟩
      change φ a ^ p = 1
      rw [← map_pow, hexp a ha, map_one])
    (by rw [hcardD]; exact hlt)
  obtain ⟨x, hxD, rfl⟩ := hx'D
  obtain ⟨g, hg⟩ := hx'I
  refine ⟨x, ⟨hxD, e.symm g, ?_⟩, fun h => hx'1 (by simp [h])⟩
  apply φ.injective
  change _ = φ.toMonoidHom x
  rw [← hg]
  ext s
  simp [hφ, MulAut.congr_apply]

private theorem kd76c_lt_sq {p : ℕ} (hp : p.Prime) : p < p ^ 2 := by
  nlinarith [hp.two_le]

private theorem kd76c_card_map_eq {A Q : Type} [Group A] [Group Q] (ψ : A →* Q)
    (S : Subgroup A) : Nat.card S = Nat.card ↥(S ⊓ ψ.ker) * Nat.card ↥(S.map ψ) := by
  have h := Subgroup.card_ker_mul_card_range (ψ.comp S.subtype)
  have hr : (ψ.comp S.subtype).range = S.map ψ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  let e : ↥(ψ.comp S.subtype).ker ≃ ↥(S ⊓ ψ.ker) :=
    { toFun := fun x => ⟨(x.1 : A), x.1.2, x.2⟩
      invFun := fun y => ⟨⟨y.1, y.2.1⟩, y.2.2⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }
  rw [hr] at h
  rw [← h, Nat.card_congr e]

private theorem kd76c_card_le_outer {S : Type} [Group S] [Finite S] {D : Subgroup (MulAut S)}
    (hDI : D ⊓ inner S = ⊥) : Nat.card D ≤ Nat.card (Outer S) := by
  haveI : Finite (MulAut S) := MulEquiv.finite_left
  have h1 := kd76c_card_map_eq (QuotientGroup.mk' (inner S)) D
  rw [QuotientGroup.ker_mk' (inner S), hDI, Subgroup.card_bot, one_mul] at h1
  rw [h1]
  exact Subgroup.card_le_card_group _

private theorem kd76c_card_eq_map {S : Type} [Group S] [Finite S] {D : Subgroup (MulAut S)}
    (hDI : D ⊓ inner S = ⊥) :
    Nat.card D = Nat.card ↥(D.map (QuotientGroup.mk' (inner S))) := by
  haveI : Finite (MulAut S) := MulEquiv.finite_left
  have h1 := kd76c_card_map_eq (QuotientGroup.mk' (inner S)) D
  rw [QuotientGroup.ker_mk' (inner S), hDI, Subgroup.card_bot, one_mul] at h1
  exact h1

section AType

open Matrix CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.UnbalancedCatalog.EvenLinearSL (mem_semilinearAutGroup_of_odd)
open CFSG.HardMathSupport.Timmesfeld.DefChar (card_le_mul_card_ker conjAut_mem_inner_of_det_mem)

theorem kd76c_card_linearQuot_dvd {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n) :
    Nat.card (linearAutGroup n K ⧸
      (CFSG.ComponentClassification.OuterAutomorphisms.inner (projectiveSL n K)).subgroupOf
        (linearAutGroup n K)) ∣ Nat.card Kˣ := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  set P : Subgroup Kˣ := (powMonoidHom n : Kˣ →* Kˣ).range with hP
  let θ : GL (Fin n) K →* Kˣ ⧸ P := (QuotientGroup.mk' P).comp GeneralLinearGroup.det
  have hθ : Function.Surjective θ :=
    (QuotientGroup.mk'_surjective P).comp GeneralLinearGroup.det_surjective
  let ψ : GL (Fin n) K →* linearAutGroup n K ⧸
      (CFSG.ComponentClassification.OuterAutomorphisms.inner (projectiveSL n K)).subgroupOf
        (linearAutGroup n K) :=
    (QuotientGroup.mk' _).comp
      ((conjAut n K).codRestrict (linearAutGroup n K) conjAut_mem_linearAutGroup)
  have hψ : Function.Surjective ψ := by
    intro y
    obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨A, rfl⟩ := mem_linearAutGroup_iff.1 hx
    exact ⟨A, rfl⟩
  have hker : θ.ker ≤ ψ.ker := by
    intro A hA
    have hA' : GeneralLinearGroup.det A ∈ P := (QuotientGroup.eq_one_iff _).1 hA
    change QuotientGroup.mk _ = 1
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact conjAut_mem_inner_of_det_mem hn A hA'
  let e := QuotientGroup.quotientKerEquivOfSurjective θ hθ
  let φ := (QuotientGroup.lift θ.ker ψ hker).comp e.symm.toMonoidHom
  have hφ : Function.Surjective φ := by
    intro y
    obtain ⟨A, rfl⟩ := hψ y
    refine ⟨θ A, ?_⟩
    have h1 : e.symm (θ A) = QuotientGroup.mk A := e.symm_apply_eq.2 rfl
    simp only [φ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h1, QuotientGroup.lift_mk]
  exact (Subgroup.card_dvd_of_surjective hφ).trans (Subgroup.card_quotient_dvd_card P)

theorem kd76c_coprime_linearQuot {p : ℕ} (hp : p.Prime) {K : Type} [Field K] [Finite K]
    [CharP K p] {n : ℕ} (hn : 1 ≤ n) :
    Nat.Coprime p (Nat.card (linearAutGroup n K ⧸
      (CFSG.ComponentClassification.OuterAutomorphisms.inner (projectiveSL n K)).subgroupOf
        (linearAutGroup n K))) := by
  refine Nat.Coprime.coprime_dvd_right (kd76c_card_linearQuot_dvd hn) ?_
  rw [Nat.Prime.coprime_iff_not_dvd hp]
  intro hdvd
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hxp : x ^ p = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hK : (x : K) ^ p = 1 := by
    have := congrArg Units.val hxp
    simpa using this
  have hsub : ((x : K) - 1) ^ p = 0 := by rw [sub_pow_char, hK, one_pow, sub_self]
  have h1 : (x : K) = 1 := sub_eq_zero.1 ((pow_eq_zero_iff hp.ne_zero).1 hsub)
  have h2 : x = 1 := Units.ext h1
  rw [h2, orderOf_one] at hx
  exact hp.one_lt.ne hx

theorem kd76c_pow_inner {p : ℕ} (hp : p.Prime) {K : Type} [Field K] [Finite K] [CharP K p]
    {n : ℕ} (hn : 1 ≤ n) (g : MulAut (projectiveSL n K)) (hg : g ∈ linearAutGroup n K)
    (hgp : g ^ p = 1) :
    g ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (projectiveSL n K) := by
  have h1 : (QuotientGroup.mk ⟨g, hg⟩ :
      linearAutGroup n K ⧸ (CFSG.ComponentClassification.OuterAutomorphisms.inner
        (projectiveSL n K)).subgroupOf (linearAutGroup n K)) ^ p = 1 := by
    rw [← QuotientGroup.mk_pow]
    have h2 : (⟨g, hg⟩ : linearAutGroup n K) ^ p = 1 := Subtype.ext hgp
    rw [h2, QuotientGroup.mk_one]
  have hord := orderOf_dvd_of_pow_eq_one h1
  have hdvd := orderOf_dvd_natCard (QuotientGroup.mk ⟨g, hg⟩ :
      linearAutGroup n K ⧸ (CFSG.ComponentClassification.OuterAutomorphisms.inner
        (projectiveSL n K)).subgroupOf (linearAutGroup n K))
  have h2 := Nat.dvd_gcd hord hdvd
  rw [Nat.Coprime.gcd_eq_one (kd76c_coprime_linearQuot hp hn), Nat.dvd_one] at h2
  have h3 := orderOf_eq_one_iff.1 h2
  exact (Subgroup.mem_subgroupOf).1 ((QuotientGroup.eq_one_iff _).1 h3)

theorem kd76c_exists_inner_projectiveSL {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K : Type} [Field K]
    [Finite K] [CharP K p] {n : ℕ} (hn : 3 ≤ n) (D : Subgroup (MulAut (projectiveSL n K)))
    (hexp : ∀ a ∈ D, a ^ p = 1) (hcard : p < Nat.card D) :
    ∃ x ∈ D ⊓ (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range, x ≠ 1 := by
  classical
  have : Finite D := Nat.finite_of_card_ne_zero (by omega)
  set Dl := linearAutGroup n K with hDl
  set Es := semilinearAutGroup n K with hEs
  have hgen := (automorphism_generation (K := K) hn).1
  obtain ⟨hID, -, hDnorm, -, -, ⟨g, hgE, hg⟩, -⟩ := standard_outer_quotients (n := n) (K := K)
  rw [hgen] at hDnorm
  have hDlN : Dl.Normal := ⟨fun d hd x =>
    hDnorm.conj_mem ⟨d, Subgroup.mem_top d⟩ hd ⟨x, Subgroup.mem_top x⟩⟩
  have hcyc : IsCyclic (Es ⧸ Dl.subgroupOf Es) := by
    refine ⟨⟨QuotientGroup.mk ⟨g, hgE⟩, fun y => ?_⟩⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨k, hk⟩ := hg x x.2
    refine ⟨-k, ?_⟩
    change (QuotientGroup.mk (⟨g, hgE⟩ : Es) : Es ⧸ Dl.subgroupOf Es) ^ (-k) = QuotientGroup.mk x
    rw [← QuotientGroup.mk_zpow, QuotientGroup.eq, Subgroup.mem_subgroupOf, _root_.zpow_neg,
      inv_inv, Subgroup.coe_mul, Subgroup.coe_zpow]
    exact hk
  have hDE : D ≤ Es := fun x hx => by
    have hdvd : orderOf x ∣ p := orderOf_dvd_of_pow_eq_one (hexp x hx)
    refine mem_semilinearAutGroup_of_odd hn ?_
    rcases (Nat.dvd_prime hp).1 hdvd with h | h
    · rw [h]; exact odd_one
    · rw [h]; exact hp.odd_of_ne_two hp2
  let α : D →* Es ⧸ Dl.subgroupOf Es :=
    (QuotientGroup.mk' (Dl.subgroupOf Es)).comp (Subgroup.inclusion hDE)
  have hle1 := card_le_mul_card_ker hp (fun h : D => Subtype.ext (hexp h h.2)) α
  have hk1 : 1 < Nat.card α.ker := by
    by_contra hle'
    have : Nat.card D ≤ p * 1 := hle1.trans (Nat.mul_le_mul_left _ (by omega))
    omega
  have : Finite α.ker := Finite.of_injective _ α.ker.subtype_injective
  have : Nontrivial α.ker := Finite.one_lt_card_iff_nontrivial.1 hk1
  have hmemDl : ∀ k : α.ker, ((k : D) : MulAut (projectiveSL n K)) ∈ Dl := by
    intro ⟨d, hd⟩
    have h : α d = 1 := hd
    change QuotientGroup.mk (Subgroup.inclusion hDE d) = (1 : Es ⧸ Dl.subgroupOf Es) at h
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h
    exact h
  obtain ⟨⟨d, hdα⟩, hd1⟩ := exists_ne (1 : α.ker)
  have hd1' : d ≠ 1 := fun h => hd1 (Subtype.ext h)
  have hdI : ((d : D) : MulAut (projectiveSL n K)) ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner (projectiveSL n K) :=
    kd76c_pow_inner hp (by omega) _ (hmemDl ⟨d, hdα⟩) (hexp _ d.2)
  exact ⟨d, ⟨d.2, hdI⟩, fun h => hd1' (Subtype.ext h)⟩

end AType

theorem kd76cLieP_A {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    KD76cLieP p (fun d => ∃ r q, d = .A r q) := by
  intro S _ _ _ _ idx hP hchar hiso D hD hcard hDI
  obtain ⟨r, q, hq⟩ := hP
  obtain ⟨d, hv⟩ := idx
  simp only at hq
  subst hq
  exfalso
  have hr1 : 1 ≤ r :=
    ((TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1).1
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hchar' : (TauCeti.LieTypeIndex.A r q).characteristic = p := hchar
  rw [TauCeti.LieTypeIndex.characteristic_A] at hchar'
  subst hchar'
  obtain ⟨e0⟩ := hiso
  have hlt : q.p < Nat.card D := by rw [hcard]; exact kd76c_lt_sq hp
  rcases Nat.lt_or_ge r 2 with h1 | h2
  · have hr : r = 1 := by omega
    subst hr
    let e : S ≃* Matrix.ProjectiveSpecialLinearGroup (Fin (1 + 1))
        (GaloisField q.p q.exponent) :=
      e0.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 q hv)
    obtain ⟨x, hx, hx1⟩ := kd76c_transport e D (fun a ha => hD.2 a ha) hlt
      (fun D' hexp hc => exists_inner_of_elemAbelian_psl2_all hp hp2 D' hexp hc)
    exact kd76c_absurd hDI hx hx1
  · let e : S ≃* Matrix.ProjectiveSpecialLinearGroup (Fin (r + 1))
        (GaloisField q.p q.exponent) :=
      e0.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL r q hv)
    let e' : S ≃* CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL (r + 1)
        (GaloisField q.p q.exponent) :=
      e.trans (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
        (r + 1) _)
    obtain ⟨x, hx, hx1⟩ := kd76c_transport e' D (fun a ha => hD.2 a ha) hlt
      (fun D' hexp hc => kd76c_exists_inner_projectiveSL hp hp2 (by omega) D' hexp hc)
    exact kd76c_absurd hDI hx hx1

theorem kd76c_cover (d : TauCeti.LieTypeIndex) (hv : d.Valid) (h : ¬ KDOpenFam d) :
    (∃ r q, d = .A r q) ∨ (∃ r q, d = .twistedA r q) ∨ (∃ r q, d = .C r q) ∨ (∃ q, d = .E6 q) ∨ (∃ q, d = .E7 q) ∨ (∃ q, d = .E8 q) ∨ (∃ q, d = .twistedE6 q) ∨ (∃ q, d = .F4 q) ∨ (∃ q, d = .G2 q) ∨ (∃ m, d = .reeG2 m) ∨ (∃ q, d = .trialityD4 q) ∨ (d.characteristic = 2) := by
  cases d with
  | A r q => exact Or.inl (⟨r, q, rfl⟩)
  | twistedA r q => exact Or.inr (Or.inl (⟨r, q, rfl⟩))
  | C r q => exact Or.inr (Or.inr (Or.inl (⟨r, q, rfl⟩)))
  | E6 q => exact Or.inr (Or.inr (Or.inr (Or.inl (⟨q, rfl⟩))))
  | E7 q => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨q, rfl⟩)))))
  | E8 q => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨q, rfl⟩))))))
  | twistedE6 q => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨q, rfl⟩)))))))
  | F4 q => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨q, rfl⟩))))))))
  | G2 q => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨q, rfl⟩)))))))))
  | reeG2 m => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨m, rfl⟩))))))))))
  | trialityD4 q => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨q, rfl⟩)))))))))))
  | B _ _ | D _ _ | twistedD _ _ => exact (h trivial).elim
  | suzuki _ => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by simp)))))))))))
  | reeF4 _ => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by simp)))))))))))
  | tits => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by simp)))))))))))

theorem kd76c_U42 (S : Type) [Group S] [Finite S] (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA 3 q).Valid) (hq : q.card = 2)
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨.twistedA 3 q, hv⟩).Group)
    (D : Subgroup (MulAut S)) (hD : IsElemAbelian 3 D) (hcard : Nat.card D = 3 ^ 2)
    (hDI : D ⊓ inner S = ⊥) : False := by
  have hpq : q.p ^ q.exponent = 2 := by rw [← TauCeti.PrimePower.card_def]; exact hq
  have hf : q.exponent = 1 := by
    have := q.exponent_pos
    by_contra hf
    have h2 : q.p ^ 2 ≤ q.p ^ q.exponent := Nat.pow_le_pow_right q.prime_p.pos (by omega)
    have := q.prime_p.two_le
    nlinarith
  have hc : q.p = 2 := by
    rw [hf, pow_one] at hpq
    exact hpq
  have hchar : TauCeti.ValidLieTypeIndex.characteristic (⟨.twistedA 3 q, hv⟩ :
      TauCeti.ValidLieTypeIndex) = 2 := by
    simp only [TauCeti.ValidLieTypeIndex.characteristic,
      TauCeti.LieTypeIndex.characteristic_twistedA, hc]
  have hfe : TauCeti.ValidLieTypeIndex.fieldExponent (⟨.twistedA 3 q, hv⟩ :
      TauCeti.ValidLieTypeIndex) = 1 := by
    simp only [TauCeti.ValidLieTypeIndex.fieldExponent,
      TauCeti.LieTypeIndex.fieldExponent_twistedA, hf]
  haveI : Fact (TauCeti.ValidLieTypeIndex.characteristic (⟨.twistedA 3 q, hv⟩ :
      TauCeti.ValidLieTypeIndex)).Prime :=
    ⟨TauCeti.ValidLieTypeIndex.characteristic_prime _⟩
  obtain ⟨eM⟩ := kd76c_U42_model _ _ hchar hfe
  let eT := CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj 3 q hv
  let e' : S ≃* CFSG.Assembly.RankThreeEven.projSU 4 2 1 := e.trans (eT.trans eM)
  have hOut : Nat.card (Outer S) = Nat.card (Outer (CFSG.Assembly.RankThreeEven.projSU 4 2 1)) :=
    Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e').toEquiv
  have hdiv := Subgroup.card_subgroup_dvd_card (D.map (QuotientGroup.mk' (inner S)))
  rw [← kd76c_card_eq_map hDI, hcard, hOut] at hdiv
  exact CFSG.RankThree.PartTwo.Sec19.Step1919EndProof.not_nine_dvd_card_outer_projSU_four_two
    (by norm_num at hdiv; exact hdiv)

theorem kd76c_ambiguous {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (S : Type) [Group S] [Finite S] (hS : catalogIs S (ambiguousChev p))
    (D : Subgroup (MulAut S)) (hD : IsElemAbelian p D) (hcard : Nat.card D = p ^ 2)
    (hDI : D ⊓ inner S = ⊥) : False := by
  obtain ⟨i, hi, ⟨e⟩⟩ := hS
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have h9 : 9 ≤ p ^ 2 := by nlinarith
  have hlt : p < Nat.card D := by rw [hcard]; exact kd76c_lt_sq hp
  cases i with
  | cyclic r hr => simp [ambiguousChev] at hi
  | alternating n hn =>
    simp only [ambiguousChev] at hi
    have hout : Nat.card (Outer S) ≤ 4 := by
      rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv]
      rcases hi with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, h8⟩
      · exact CFSG.RankThree.PartOne.card_outer_alternating_le_four (by norm_num)
      · exact CFSG.RankThree.PartOne.card_outer_alternating_le_four (by norm_num)
      · exact absurd h8 hp2
    have hle := kd76c_card_le_outer hDI
    rw [hcard] at hle
    linarith
  | sporadic s => simp [ambiguousChev] at hi
  | lie idx =>
    obtain ⟨d, hv⟩ := idx
    cases d with
    | A r q =>
      rcases (show r = 0 ∨ r = 1 ∨ 2 ≤ r by omega) with rfl | rfl | h2r
      · exact absurd ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
          ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1).1 (by norm_num)
      ·
        simp only [ambiguousChev] at hi
        rcases hi with ⟨-, h2⟩ | ⟨h8, h3⟩
        · exact absurd h2 hp2
        · have : Fact q.p.Prime := ⟨q.prime_p⟩
          have hq8 : Nat.card (GaloisField q.p q.exponent) = 8 := by
            rw [GaloisField.card _ _ q.exponent_pos.ne', ← TauCeti.PrimePower.card_def, h8]
          have hcyc : IsCyclic (Outer (Matrix.ProjectiveSpecialLinearGroup (Fin (1 + 1))
              (GaloisField q.p q.exponent))) :=
            CFSG.Quasithin.OuterPrimeControl.outer_psl2_isCyclic _ (Or.inl (by rw [hq8]; decide))
          let e' : S ≃* Matrix.ProjectiveSpecialLinearGroup (Fin (1 + 1))
              (GaloisField q.p q.exponent) :=
            e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 q hv)
          obtain ⟨x, hx, hx1⟩ := kd76c_transport e' D (fun a ha => hD.2 a ha) hlt
            (fun D' hexp hc => CFSG.HardMathSupport.Timmesfeld.DefChar.exists_inner_of_cyclic_hom
              (Q := Outer (Matrix.ProjectiveSpecialLinearGroup (Fin (1 + 1))
                (GaloisField q.p q.exponent)))
              (QuotientGroup.mk' (inner _)) hp (fun x hx _ => (QuotientGroup.eq_one_iff x).1 hx)
              D' hexp hc)
          exact kd76c_absurd hDI hx hx1
      · obtain ⟨k, rfl⟩ : ∃ k, r = k + 2 := ⟨r - 2, by omega⟩
        simp [ambiguousChev] at hi
    | twistedA r q =>
      rcases (show r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ 4 ≤ r by omega) with rfl | rfl | rfl | rfl | h4
      · simp [ambiguousChev] at hi
      · simp [ambiguousChev] at hi
      · simp only [ambiguousChev] at hi
        exact absurd hi.2 hp2
      ·
        simp only [ambiguousChev] at hi
        obtain ⟨hq2, hp3'⟩ := hi
        subst hp3'
        exact kd76c_U42 S q hv hq2 e D hD hcard hDI
      · obtain ⟨k, rfl⟩ : ∃ k, r = k + 4 := ⟨r - 4, by omega⟩
        simp [ambiguousChev] at hi
    | _ => simp [ambiguousChev] at hi

section Generic

theorem kd76c_card_dvd_of_ker_le {G Q M : Type} [Group G] [Group Q] [Group M] [Finite M]
    (f : G →* Q) (hf : Function.Surjective f) (N : G →* M) (hker : N.ker ≤ f.ker) :
    Nat.card Q ∣ Nat.card M := by
  let g : N.range →* Q :=
    (QuotientGroup.lift N.ker f hker).comp
      (QuotientGroup.quotientKerEquivRange N).symm.toMonoidHom
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨a, rfl⟩ := hf y
    refine ⟨QuotientGroup.quotientKerEquivRange N (QuotientGroup.mk a), ?_⟩
    simp [g]
  exact (Subgroup.card_dvd_of_surjective hg).trans (Subgroup.card_subgroup_dvd_card _)

theorem kd76c_coprime_units {p : ℕ} (hp : p.Prime) {K : Type} [Field K] [Finite K] [CharP K p] :
    Nat.Coprime p (Nat.card Kˣ) := by
  rw [Nat.Prime.coprime_iff_not_dvd hp]
  intro hdvd
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hxp : x ^ p = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hK : (x : K) ^ p = 1 := by
    have := congrArg Units.val hxp
    simpa using this
  have hsub : ((x : K) - 1) ^ p = 0 := by rw [sub_pow_char, hK, one_pow, sub_self]
  have h1 : (x : K) = 1 := sub_eq_zero.1 ((pow_eq_zero_iff hp.ne_zero).1 hsub)
  have h2 : x = 1 := Units.ext h1
  rw [h2, orderOf_one] at hx
  exact hp.one_lt.ne hx

theorem kd76c_mem_of_pow_coprime {G : Type} [Group G] {p : ℕ} (hp : p.Prime) (Dl I : Subgroup G)
    [I.Normal] (hcop : Nat.Coprime p (Nat.card (Dl ⧸ I.subgroupOf Dl))) (x : G) (hx : x ∈ Dl)
    (hxp : x ^ p = 1) : x ∈ I := by
  have h1 : (QuotientGroup.mk ⟨x, hx⟩ : Dl ⧸ I.subgroupOf Dl) ^ p = 1 := by
    rw [← QuotientGroup.mk_pow]
    have h2 : (⟨x, hx⟩ : Dl) ^ p = 1 := Subtype.ext hxp
    rw [h2, QuotientGroup.mk_one]
  have hord := orderOf_dvd_of_pow_eq_one h1
  have hdvd := orderOf_dvd_natCard (QuotientGroup.mk ⟨x, hx⟩ : Dl ⧸ I.subgroupOf Dl)
  have h2 := Nat.dvd_gcd hord hdvd
  rw [Nat.Coprime.gcd_eq_one hcop, Nat.dvd_one] at h2
  have h3 := orderOf_eq_one_iff.1 h2
  exact (Subgroup.mem_subgroupOf).1 ((QuotientGroup.eq_one_iff _).1 h3)

theorem kd76c_exists_of_cyclic {E : Type} [Group E] [Finite E] {p : ℕ} (hp : p.Prime)
    {Q : Type} [Group Q] [IsCyclic Q] (F : E →* Q) (I : Subgroup E)
    (hI : ∀ x ∈ F.ker, x ^ p = 1 → x ∈ I) (D : Subgroup E) (hexp : ∀ a ∈ D, a ^ p = 1)
    (hcard : p < Nat.card D) : ∃ x ∈ D ⊓ I, x ≠ 1 := by
  classical
  let α : D →* Q := F.comp D.subtype
  have hexp' : ∀ x : D, x ^ p = 1 := fun x => Subtype.ext (hexp x x.2)
  have h1 := CFSG.HardMathSupport.Timmesfeld.DefChar.card_le_mul_card_ker hp hexp' α
  have hk1 : 1 < Nat.card α.ker := by
    by_contra hle
    have : Nat.card D ≤ p * 1 := h1.trans (Nat.mul_le_mul_left _ (by omega))
    omega
  have : Nontrivial α.ker := Finite.one_lt_card_iff_nontrivial.1 hk1
  obtain ⟨⟨⟨d, hdD⟩, hdα⟩, hd1⟩ := exists_ne (1 : α.ker)
  have hFd : d ∈ F.ker := hdα
  have hd1' : d ≠ 1 := fun h => hd1 (Subtype.ext (Subtype.ext h))
  exact ⟨d, ⟨hdD, hI d hFd (hexp d hdD)⟩, hd1'⟩

end Generic

section TypeCChar

open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.Assembly.LowTwoRank

theorem kd76c_card_spQuot_dvd {K : Type} [Field K] [Finite K] {r : ℕ} (hr : 1 ≤ r) :
    Nat.card (spLinearAutGroup r K ⧸
      (CFSG.ComponentClassification.OuterAutomorphisms.inner
        (StatedProj (StatedSp r K))).subgroupOf (spLinearAutGroup r K)) ∣ Nat.card Kˣ := by
  have : NeZero r := ⟨by omega⟩
  let c : gsp r K →* spLinearAutGroup r K :=
    (conjAut r K).codRestrict (spLinearAutGroup r K) fun A => conjAut_mem_spLinearAutGroup A
  let f' : gsp r K →* spLinearAutGroup r K ⧸
      (CFSG.ComponentClassification.OuterAutomorphisms.inner
        (StatedProj (StatedSp r K))).subgroupOf (spLinearAutGroup r K) :=
    (QuotientGroup.mk' _).comp c
  have hcs : Function.Surjective c := by
    rintro ⟨y, hy⟩
    obtain ⟨A, rfl⟩ := mem_spLinearAutGroup_iff.mp hy
    exact ⟨A, rfl⟩
  have hs : Function.Surjective f' := (QuotientGroup.mk'_surjective _).comp hcs
  have hker : (multiplier r K).ker ≤ f'.ker := by
    intro A hA
    rw [ker_multiplier, Subgroup.mem_subgroupOf] at hA
    rw [MonoidHom.mem_ker]
    change QuotientGroup.mk (c A) = (1 : spLinearAutGroup r K ⧸
      (CFSG.ComponentClassification.OuterAutomorphisms.inner
        (StatedProj (StatedSp r K))).subgroupOf (spLinearAutGroup r K))
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    have h2 : A = ⟨((⟨_, hA⟩ : StatedSp r K) : GL (Fin r ⊕ Fin r) K), statedSp_le_gsp hA⟩ := rfl
    have h3 : (c A : MulAut (StatedProj (StatedSp r K))) = conjAut r K A := rfl
    rw [h3, h2, conjAut_statedSp]
    exact ⟨_, rfl⟩
  exact kd76c_card_dvd_of_ker_le f' hs (multiplier r K) hker

theorem kd76c_coprime_spQuot {p : ℕ} (hp : p.Prime) {K : Type} [Field K] [Finite K] [CharP K p]
    {r : ℕ} (hr : 1 ≤ r) :
    Nat.Coprime p (Nat.card (spLinearAutGroup r K ⧸
      (CFSG.ComponentClassification.OuterAutomorphisms.inner
        (StatedProj (StatedSp r K))).subgroupOf (spLinearAutGroup r K))) :=
  Nat.Coprime.coprime_dvd_right (kd76c_card_spQuot_dvd hr) (kd76c_coprime_units hp)

theorem kd76c_exists_inner_projectiveSp {p : ℕ} (hp : p.Prime) {K : Type} [Field K] [Finite K]
    [CharP K p] {r : ℕ} (hr : 3 ≤ r) (D : Subgroup (MulAut (StatedProj (StatedSp r K))))
    (hexp : ∀ a ∈ D, a ^ p = 1) (hcard : p < Nat.card D) :
    ∃ x ∈ D ⊓ (MulAut.conj : StatedProj (StatedSp r K) →*
      MulAut (StatedProj (StatedSp r K))).range, x ≠ 1 := by
  classical
  have : NeZero r := ⟨by omega⟩
  set Dl := spLinearAutGroup r K with hDl
  set Es := spSemilinearAutGroup r K with hEs
  set I := (MulAut.conj : StatedProj (StatedSp r K) →*
      MulAut (StatedProj (StatedSp r K))).range with hI
  have hIN : I.Normal := CFSG.ComponentClassification.OuterAutomorphisms.inner_normal _
  have hgen := (automorphism_generation (K := K) hr).1
  obtain ⟨-, -, hDnorm, -, ⟨g, hgE, hg⟩, -⟩ :=
    standard_outer_quotient (K := K) (r := r) (by omega)
  have hDE : D ≤ Es := fun x hx => by rw [hEs, hgen]; exact Subgroup.mem_top x
  have hcyc : IsCyclic (Es ⧸ Dl.subgroupOf Es) := by
    refine ⟨⟨QuotientGroup.mk ⟨g, hgE⟩, fun y => ?_⟩⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨k, hk⟩ := hg x x.2
    refine ⟨-k, ?_⟩
    change (QuotientGroup.mk (⟨g, hgE⟩ : Es) : Es ⧸ Dl.subgroupOf Es) ^ (-k) = QuotientGroup.mk x
    rw [← QuotientGroup.mk_zpow, QuotientGroup.eq, Subgroup.mem_subgroupOf, zpow_neg, inv_inv,
      Subgroup.coe_mul, Subgroup.coe_zpow]
    exact hk
  have hcop : Nat.Coprime p (Nat.card (Dl ⧸ I.subgroupOf Dl)) :=
    kd76c_coprime_spQuot hp (K := K) (r := r) (by omega)
  let F : Es →* Es ⧸ Dl.subgroupOf Es := QuotientGroup.mk' (Dl.subgroupOf Es)
  have hFker : F.ker = Dl.subgroupOf Es := QuotientGroup.ker_mk' _
  have hD' : ∀ a ∈ D.subgroupOf Es, a ^ p = 1 := fun a ha => Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hexp _ ((Subgroup.mem_subgroupOf).1 ha))
  have hcardD' : p < Nat.card (D.subgroupOf Es) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDE).toEquiv]
    exact hcard
  haveI : Finite Es := Finite.of_injective (fun y : Es => (y : MulAut (StatedProj (StatedSp r K))))
    Subtype.coe_injective
  obtain ⟨x, hx, hx1⟩ := kd76c_exists_of_cyclic (E := Es) hp F (I.subgroupOf Es)
    (fun y hy hyp => by
      rw [hFker] at hy
      have hyDl : (y : MulAut (StatedProj (StatedSp r K))) ∈ Dl := hy
      have hyp' : (y : MulAut (StatedProj (StatedSp r K))) ^ p = 1 := by
        rw [← Subgroup.coe_pow, hyp, Subgroup.coe_one]
      exact (Subgroup.mem_subgroupOf).2
        (kd76c_mem_of_pow_coprime hp Dl I hcop _ hyDl hyp'))
    (D.subgroupOf Es) hD' hcardD'
  have hxD : (x : MulAut (StatedProj (StatedSp r K))) ∈ D :=
    (Subgroup.mem_subgroupOf).1 (Subgroup.mem_inf.1 hx).1
  have hxI : (x : MulAut (StatedProj (StatedSp r K))) ∈ I :=
    (Subgroup.mem_subgroupOf).1 (Subgroup.mem_inf.1 hx).2
  exact ⟨(x : MulAut (StatedProj (StatedSp r K))), Subgroup.mem_inf.2 ⟨hxD, hxI⟩,
    fun h => hx1 (Subtype.ext h)⟩

end TypeCChar

theorem kd76cLieP_C {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    KD76cLieP p (fun d => ∃ r q, d = .C r q) := by
  intro S _ _ _ _ idx hP hchar hiso D hD hcard hDI
  obtain ⟨r, q, hq⟩ := hP
  obtain ⟨d, hv⟩ := idx
  simp only at hq
  subst hq
  exfalso
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hchar' : (TauCeti.LieTypeIndex.C r q).characteristic = p := hchar
  rw [TauCeti.LieTypeIndex.characteristic_C] at hchar'
  subst hchar'
  obtain ⟨e0⟩ := hiso
  have hfin := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField
    (⟨.C r q, hv⟩ : TauCeti.ValidLieTypeIndex)
  let K := ↥(TauCeti.ValidLieTypeIndex.fixedField (⟨.C r q, hv⟩ : TauCeti.ValidLieTypeIndex))
  have hKch : CharP K q.p := by
    have h := (inferInstance : CharP K (TauCeti.ValidLieTypeIndex.characteristic
      (⟨.C r q, hv⟩ : TauCeti.ValidLieTypeIndex)))
    have hq : TauCeti.ValidLieTypeIndex.characteristic (⟨.C r q, hv⟩ : TauCeti.ValidLieTypeIndex) =
        q.p := by
      simp only [TauCeti.ValidLieTypeIndex.characteristic, TauCeti.LieTypeIndex.characteristic_C]
    exact (fun (c : ℕ) (hc : CharP K c) (hcp : c = q.p) => hcp ▸ hc) _ h hq
  let e : S ≃* StatedProj (StatedSp r K) :=
    e0.trans (CFSG.QuasithinUnique.SQTK.typeCGroupEquivStatedProj r q hv)
  have hlt : q.p < Nat.card D := by rw [hcard]; exact kd76c_lt_sq hp
  obtain ⟨x, hx, hx1⟩ := kd76c_transport e D (fun a ha => hD.2 a ha) hlt
    (fun D' hexp hc => kd76c_exists_inner_projectiveSp hp (K := K) (r := r) hrange.1 D' hexp hc)
  exact kd76c_absurd hDI hx hx1

theorem kd76c_charP_of_card {K : Type} [Field K] [Finite K] {ℓ m : ℕ} (hℓ : ℓ.Prime)
    (hK : Nat.card K = ℓ ^ m) (hm : m ≠ 0) : CharP K ℓ := by
  haveI := Fintype.ofFinite K
  obtain ⟨c, hc, n, hcp, hcard⟩ := FiniteField.card' K
  rw [Nat.card_eq_fintype_card] at hK
  have hdvd : c ∣ ℓ ^ m := by
    rw [← hK, hcard]
    exact dvd_pow_self c (PNat.ne_zero n)
  have hc_eq : c = ℓ := (Nat.prime_dvd_prime_iff_eq hcp hℓ).1 (hcp.dvd_of_dvd_pow hdvd)
  exact hc_eq ▸ hc

section TwistedAChar

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.Open

theorem kd76c_exists_inner_primeFormP {p : ℕ} (hp : p.Prime) {ℓ f n : ℕ} {K : Type} [Field K]
    [Finite K] [CharP K p] (h : UnitaryFieldData ℓ f K) (hn : 3 ≤ n)
    (hq : ¬(n = 3 ∧ ℓ ^ f = 2))
    (D : Subgroup (MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))))
    (hexp : ∀ a ∈ D, a ^ p = 1) (hcard : p < Nat.card D) :
    ∃ x ∈ D ⊓ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)), x ≠ 1 := by
  classical
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  obtain ⟨-, -, -, -, -, -, -, hFker, -, -, -⟩ :=
    unitary_prime_form_full_semilinear_realization h hC hn hq
  set T := primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hT
  set Dl := primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hDl
  set IT : Subgroup (MulAut T) :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner T with hIT
  have hIN : IT.Normal := CFSG.ComponentClassification.OuterAutomorphisms.inner_normal _
  set F := primeFormFieldFactor h hC hn hq with hF
  have hcyc : IsCyclic (K ≃+* K) :=
    CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic K
  have hcop : Nat.Coprime p (Nat.card (Dl ⧸ IT.subgroupOf Dl)) := by
    let c : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) →* Dl :=
      (primeFormConjHom h _).rangeRestrict
    let f' : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) →*
        Dl ⧸ IT.subgroupOf Dl :=
      (QuotientGroup.mk' (IT.subgroupOf Dl)).comp c
    have hs : Function.Surjective f' :=
      (QuotientGroup.mk'_surjective _).comp (MonoidHom.rangeRestrict_surjective _)
    let δ : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) →* Kˣ :=
      Matrix.GeneralLinearGroup.det.comp
        (primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).subtype
    have hδ : ∀ A, (δ A : K) = ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det :=
      fun _ => rfl
    have hker : δ.ker ≤ f'.ker := by
      intro A hA
      have hdet : ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = 1 := by
        have h1 : δ A = 1 := hA
        have h2 := congrArg Units.val h1
        rw [hδ] at h2
        exact h2
      rw [MonoidHom.mem_ker]
      have hAS : (A : GL (Fin n) K) ∈ gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
        (mem_gramSU_iff_unitary h).2 ⟨A.2, hdet⟩
      have : (c A : MulAut T) = primeFormConjHom h _ A := rfl
      change QuotientGroup.mk (c A) = (1 : Dl ⧸ IT.subgroupOf Dl)
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, this, mem_inner_primeFormP]
      exact ⟨⟨A, hAS⟩, rfl⟩
    exact Nat.Coprime.coprime_dvd_right (kd76c_card_dvd_of_ker_le f' hs δ hker)
      (kd76c_coprime_units hp)
  have hI : ∀ x ∈ F.ker, x ^ p = 1 → x ∈ IT := by
    intro x hx hxp
    rw [hFker] at hx
    exact kd76c_mem_of_pow_coprime hp Dl IT hcop x hx hxp
  exact kd76c_exists_of_cyclic hp F IT hI D hexp hcard

theorem kd76cLieP_twistedA {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    KD76cLieP p (fun d => ∃ r q, d = .twistedA r q) := by
  intro S _ _ _ _ idx hP hchar hiso D hD hcard hDI
  obtain ⟨r, q, hr⟩ := hP
  obtain ⟨d, hv⟩ := idx
  simp only at hr
  subst hr
  exfalso
  have hr2 : 2 ≤ r :=
    ((TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1).1
  have hchar' : (TauCeti.LieTypeIndex.twistedA r q).characteristic = p := hchar
  rw [TauCeti.LieTypeIndex.characteristic_twistedA] at hchar'
  subst hchar'
  obtain ⟨e0⟩ := hiso
  have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e0
  obtain ⟨⟨hℓ, hf, hn, hq⟩, K, _, _, hK, ⟨eT⟩⟩ := hm
  have h : UnitaryFieldData q.p q.exponent K := ⟨hℓ, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have hfin : Finite K := h.finite
  haveI : CharP K q.p :=
    kd76c_charP_of_card (m := 2 * q.exponent) hℓ h.card (by have := q.exponent_pos; omega)
  have hq' : ¬(r + 1 = 3 ∧ q.p ^ q.exponent = 2) := fun ⟨h1, h2⟩ => hq (by rw [h1, h2])
  obtain ⟨eP⟩ := nonempty_primeFormP_mulEquiv h (isPrimeFormGram_one (n := r + 1) (K := K))
  let e : S ≃* primeFormP h ((1 : GL (Fin (r + 1)) K) : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :=
    (eT.trans (unitaryPSUEquiv h (by omega)).symm).trans eP.symm
  have hlt : q.p < Nat.card D := by rw [hcard]; exact kd76c_lt_sq hp
  obtain ⟨x, hx, hx1⟩ := kd76c_transport e D (fun a ha => hD.2 a ha) hlt
    (fun D' hexp hc => kd76c_exists_inner_primeFormP hp h (by omega) hq' D' hexp hc)
  exact kd76c_absurd hDI hx hx1

end TwistedAChar

theorem kd76c_no_p_torsion {G H : Type} [Group G] [Group H] {p : ℕ} (f : G →* H)
    (hG : Nat.Coprime p (Nat.card G)) {y : H} (hy : y ∈ f.range) (hyp : y ^ p = 1) : y = 1 := by
  obtain ⟨x, rfl⟩ := hy
  have h1 : orderOf (f x) ∣ p := orderOf_dvd_of_pow_eq_one hyp
  have h2 : orderOf (f x) ∣ orderOf x := orderOf_map_dvd f x
  have h3 : orderOf x ∣ Nat.card G := orderOf_dvd_natCard x
  have h4 : orderOf (f x) ∣ Nat.gcd p (Nat.card G) := Nat.dvd_gcd h1 (h2.trans h3)
  rw [hG.gcd_eq_one, Nat.dvd_one] at h4
  exact orderOf_eq_one_iff.1 h4

theorem kd76c_coprime_pi_units {p : ℕ} (hp : p.Prime) {ι : Type} [Fintype ι] (F : ι → Type)
    [∀ i, Field (F i)] [∀ i, Finite (F i)] [∀ i, CharP (F i) p] :
    Nat.Coprime p (Nat.card ((i : ι) → (F i)ˣ)) := by
  rw [Nat.card_pi]
  exact Nat.Coprime.prod_right (fun i _ => kd76c_coprime_units hp)

theorem kd76c_two_step_coprime {M : Type} [Group M] [Finite M] (I : Subgroup M) [I.Normal]
    {Q : Type} [Group Q] [IsCyclic Q] (Θ : M →* Q) {p : ℕ} (hp : p.Prime)
    (hN : ∀ y ∈ (Θ.ker).map (QuotientGroup.mk' I), y ^ p = 1 → y = 1)
    (D : Subgroup M) (hexp : ∀ a ∈ D, a ^ p = 1) (hcard : p < Nat.card D) :
    ∃ x ∈ D ⊓ I, x ≠ 1 := by
  classical
  let α : D →* Q := Θ.comp D.subtype
  have h1 := CFSG.HardMathSupport.Timmesfeld.DefChar.card_le_mul_card_ker hp
    (fun x : D => Subtype.ext (hexp x x.2)) α
  have hk : 1 < Nat.card α.ker := by
    by_contra h
    have : Nat.card D ≤ p * 1 := h1.trans (Nat.mul_le_mul_left _ (by omega))
    omega
  have : Nontrivial α.ker := Finite.one_lt_card_iff_nontrivial.1 hk
  obtain ⟨⟨⟨d, hdD⟩, hdα⟩, hd1⟩ := exists_ne (1 : α.ker)
  have hdΘ : d ∈ Θ.ker := hdα
  have hπ : QuotientGroup.mk' I d ∈ (Θ.ker).map (QuotientGroup.mk' I) := ⟨d, hdΘ, rfl⟩
  have hπd : QuotientGroup.mk' I d = 1 :=
    hN _ hπ (by rw [← map_pow, hexp d hdD, map_one])
  have hdI : d ∈ I := (QuotientGroup.eq_one_iff d).1 hπd
  exact ⟨d, ⟨hdD, hdI⟩, fun h => hd1 (Subtype.ext (Subtype.ext h))⟩

section Exceptional

open CFSG.HardMathSupport.Timmesfeld.DefChar
open CFSG.Blueprint CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Solomon.LocalBalance (innerAut)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.LieType.Ree (ReeTag)
open CFSG.ComponentClassification.LiteratureLocal.SmallRee (frobeniusΓ
  exists_eq_conj_mul_frobeniusΓ_pow)

theorem kd76cLieP_F4 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    KD76cLieP p (fun d => ∃ q, d = .F4 q) := by
  intro S _ _ _ _ idx hP hchar hiso D hD hcard hDI
  obtain ⟨q, hq⟩ := hP
  obtain ⟨d, hv⟩ := idx
  simp only at hq
  subst hq
  exfalso
  have hchar' : (TauCeti.LieTypeIndex.F4 q).characteristic = p := hchar
  rw [TauCeti.LieTypeIndex.characteristic_F4] at hchar'
  have hodd : ¬ q.p = 2 := by rw [hchar']; exact hp2
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  obtain ⟨e0⟩ := hiso
  obtain ⟨e⟩ := nonempty_mulEquiv_adjoint_of_bridge
    CFSG.TauCetiBridge.Even.chevalleyBridgesAll.f4 q hv e0
  have hlt : p < Nat.card D := by rw [hcard]; exact kd76c_lt_sq hp
  set K := GaloisField q.p q.exponent with hKdef
  have hK : Nat.card K = q.p ^ q.exponent := GaloisField.card _ _ q.exponent_pos.ne'
  have hfin : Finite (K ≃+* K) :=
    Finite.of_injective (fun σ : K ≃+* K => (σ : K → K)) DFunLike.coe_injective
  have hcyc : IsCyclic (K ≃+* K) :=
    CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic K
  obtain ⟨-, Θ, -, -, hker, -⟩ := odd_F4_and_nonexceptional_G2_automorphism_normal_form
    q.prime_p hodd q.exponent_pos K hK .F4 (Or.inl rfl)
  obtain ⟨x, hx, hx1⟩ := exists_inner_of_cyclic_quotient e Θ hker hp D hD.2 hlt
  exact kd76c_absurd hDI hx hx1

theorem kd76cLieP_G2 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    KD76cLieP p (fun d => ∃ q, d = .G2 q) := by
  intro S _ _ _ _ idx hP hchar hiso D hD hcard hDI
  obtain ⟨q, hq⟩ := hP
  obtain ⟨d, hv⟩ := idx
  simp only at hq
  subst hq
  exfalso
  have hchar' : (TauCeti.LieTypeIndex.G2 q).characteristic = p := hchar
  rw [TauCeti.LieTypeIndex.characteristic_G2] at hchar'
  have hodd : ¬ q.p = 2 := by rw [hchar']; exact hp2
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  obtain ⟨e0⟩ := hiso
  obtain ⟨e⟩ := nonempty_mulEquiv_adjoint_of_bridge
    CFSG.TauCetiBridge.Even.chevalleyBridgesAll.g2 q hv e0
  have hlt : p < Nat.card D := by rw [hcard]; exact kd76c_lt_sq hp
  set K := GaloisField q.p q.exponent with hKdef
  have hK : Nat.card K = q.p ^ q.exponent := GaloisField.card _ _ q.exponent_pos.ne'
  have hfin : Finite (K ≃+* K) :=
    Finite.of_injective (fun σ : K ≃+* K => (σ : K → K)) DFunLike.coe_injective
  have hcyc : IsCyclic (K ≃+* K) :=
    CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic K
  by_cases h3 : q.p = 3
  · have hK3 : Nat.card K = 3 ^ q.exponent := by rw [hK, h3]
    have hchar3 : CharP K 3 := by
      have : CharP K q.p := inferInstance
      rw [← h3]
      exact this
    obtain ⟨-, -, ⟨Θ, -, -, hker⟩, -⟩ :=
      G2_three_exact_automorphism_normal_form q.exponent_pos K hK3
    have : NeZero (2 * q.exponent) := ⟨by have := q.exponent_pos; omega⟩
    have : IsCyclic (Multiplicative (ZMod (2 * q.exponent))) := inferInstance
    obtain ⟨x, hx, hx1⟩ := exists_inner_of_cyclic_quotient
      (A := Multiplicative (ZMod (2 * q.exponent))) e Θ hker hp D hD.2 hlt
    exact kd76c_absurd hDI hx hx1
  · obtain ⟨-, Θ, -, -, hker, -⟩ := odd_F4_and_nonexceptional_G2_automorphism_normal_form
      q.prime_p hodd q.exponent_pos K hK .G2 (Or.inr ⟨rfl, h3⟩)
    obtain ⟨x, hx, hx1⟩ := exists_inner_of_cyclic_quotient e Θ hker hp D hD.2 hlt
    exact kd76c_absurd hDI hx hx1

theorem kd76cLieP_reeG2 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    KD76cLieP p (fun d => ∃ m, d = .reeG2 m) := by
  intro S _ _ _ _ idx hP hchar hiso D hD hcard hDI
  obtain ⟨m, hm⟩ := hP
  obtain ⟨d, hv⟩ := idx
  simp only at hm
  subst hm
  exfalso
  have hchar' : (TauCeti.LieTypeIndex.reeG2 m).characteristic = p := hchar
  rw [TauCeti.LieTypeIndex.characteristic_reeG2] at hchar'
  subst hchar'
  obtain ⟨e0⟩ := hiso
  have hm1 : 1 ≤ m :=
    (TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK : Nat.card (GaloisField 3 (2 * m + 1)) = 3 ^ (2 * m + 1) :=
    GaloisField.card 3 (2 * m + 1) (by omega)
  obtain ⟨b⟩ := CFSG.TauCetiBridge.reeG2Bridge m hv (GaloisField 3 (2 * m + 1)) hK
  have hgamma : ReeTag.G2.reeGamma (GaloisField 3 (2 * m + 1)) m =
      reeFixedGroup .G2 (GaloisField 3 (2 * m + 1)) reeG2Perm
        (fun i => if i ∈ reeG2Long then 3 ^ m else 3 ^ (m + 1)) :=
    ReeTag.reeGamma_eq_reeFixedGroup
  have e1 : DerivedCentralQuotient (reeFixedGroup .G2 (GaloisField 3 (2 * m + 1)) reeG2Perm
      fun i => if i ∈ reeG2Long then 3 ^ m else 3 ^ (m + 1)) ≃*
        DerivedCentralQuotient (ReeTag.G2.reeGamma (GaloisField 3 (2 * m + 1)) m) := by
    rw [hgamma]
    exact MulEquiv.refl _
  obtain ⟨E⟩ := ReeTag.nonempty_derivedCentralQuotient_mulEquiv_reeGamma_G2
    (K := GaloisField 3 (2 * m + 1)) hm1 hK
  let e : S ≃* ReeTag.G2.reeGamma (GaloisField 3 (2 * m + 1)) m :=
    ((e0.trans b.symm).trans e1).trans E
  have hlt : 3 < Nat.card D := by rw [hcard]; exact kd76c_lt_sq hp
  obtain ⟨x, hx, hx1⟩ := kd76c_transport e D (fun a ha => hD.2 a ha) hlt
    (fun D' hexp hc => exists_inner_of_elemAbelian_of_outerCyclic
      (frobeniusΓ : MulAut (ReeTag.G2.reeGamma (GaloisField 3 (2 * m + 1)) m))
      (exists_eq_conj_mul_frobeniusΓ_pow hm1 hK) hp D' hexp hc)
  exact kd76c_absurd hDI hx hx1

theorem kd76cLieP_trialityD4 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    KD76cLieP p (fun d => ∃ q, d = .trialityD4 q) := by
  intro S _ _ _ _ idx hP hchar hiso D hD hcard hDI
  obtain ⟨q, hr⟩ := hP
  obtain ⟨d, hv⟩ := idx
  simp only at hr
  subst hr
  exfalso
  have hchar' : (TauCeti.LieTypeIndex.trialityD4 q).characteristic = p := hchar
  rw [TauCeti.LieTypeIndex.characteristic_trialityD4] at hchar'
  have hodd : ¬ q.p = 2 := by rw [hchar']; exact hp2
  obtain ⟨e0⟩ := hiso
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  let K := GaloisField q.p (3 * q.exponent)
  have hf : 1 ≤ q.exponent := q.exponent_pos
  have hKc : Nat.card K = (q.p ^ q.exponent) ^ TwistTag.D4.order := by
    change Nat.card (GaloisField q.p (3 * q.exponent)) = _
    rw [GaloisField.card _ _ (by have := q.exponent_pos; omega)]
    change _ = (q.p ^ q.exponent) ^ 3
    rw [← pow_mul, mul_comm]
  have hfin : Finite (K ≃+* K) :=
    Finite.of_injective (fun σ : K ≃+* K => (σ : K → K)) DFunLike.coe_injective
  have hcyc : IsCyclic (K ≃+* K) :=
    CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic K
  obtain ⟨σ, hσ, -⟩ := finite_graph_field_parameter_fields TwistTag.D4 q.prime_p hf K hKc
  have hK3 : Nat.card K = (q.p ^ q.exponent) ^ 3 := hKc
  obtain ⟨-, -, ⟨Θ, -, -, hΘker, -⟩, -, -, -, -, heC⟩ :=
    odd_triality_exact_automorphism_normal_form q.prime_p hodd hf K hK3 σ hσ
  obtain ⟨eC⟩ := heC
  have hqc : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  obtain ⟨eB⟩ := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.trialityD4 q hv K
    (by rw [hqc]; exact hK3) σ.toRingHom (fun x => by rw [hqc]; exact hσ x)
  have e : S ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    e0.trans (eB.symm.trans eC)
  have hlt : p < Nat.card D := by rw [hcard]; exact kd76c_lt_sq hp
  obtain ⟨x, hx, hx1⟩ := kd76c_transport e D (fun a ha => hD.2 a ha) hlt
    (fun D' hexp hc => exists_inner_of_cyclic_hom Θ hp
      (fun x hx _ => by
        have : x ∈ Θ.ker := hx
        rw [hΘker] at this
        exact this)
      D' hexp hc)
  exact kd76c_absurd hDI hx hx1



theorem kd76c_exists_inner_adjointE_charp {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {p : ℕ} {K : Type} [Field K] [Finite K] [CharP K p] (hp : p.Prime) (hp2 : p ≠ 2)
    (D : Subgroup (MulAut (adjointGroup τ K)))
    (hexp : ∀ a ∈ D, a ^ p = 1) (hcard : p < Nat.card D) :
    ∃ x ∈ D ⊓ inner (adjointGroup τ K), x ≠ 1 := by
  classical
  by_contra hno
  push Not at hno
  obtain ⟨Φ, -, hΦker, -⟩ := exists_outer_hom_E (K := K) (τ := τ) hτ
  have hE2 : exactE τ ∣ 2 := by
    rcases hτ with rfl | rfl | rfl <;> simp [exactE]
  have hΦ : ∀ y ∈ Φ.ker, y ^ p = 1 → y = 1 := by
    intro y hy hyp
    rw [hΦker] at hy
    refine kd76c_no_p_torsion _ ?_ hy hyp
    rw [Nat.card_pi]
    exact Nat.Coprime.prod_right (fun i _ => kd76c_coprime_units hp)
  let ρ : D →* Outer (adjointGroup τ K) :=
    (QuotientGroup.mk' (inner (adjointGroup τ K))).comp D.subtype
  have hρinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxin : (x : MulAut (adjointGroup τ K)) ∈ inner (adjointGroup τ K) :=
      (QuotientGroup.eq_one_iff (N := inner (adjointGroup τ K)) _).1 hx
    exact Subtype.ext (hno x ⟨x.2, hxin⟩)
  let α : D →* RingAut K := (MonoidHom.fst _ _).comp (Φ.comp ρ)
  have hexpD : ∀ x : D, x ^ p = 1 := fun x => Subtype.ext (hexp x x.2)
  have : IsCyclic (K ≃+* K) :=
    CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic K
  have : Finite (K ≃+* K) :=
    Finite.of_injective (fun σ : K ≃+* K => (σ : K → K)) DFunLike.coe_injective
  have hrange : Nat.card α.range ≤ p := card_range_le_of_cyclic α hp hexpD
  have hmem : ∀ x : α.ker, ρ x ∈ Φ.ker := by
    intro x
    have hx1 : (Φ (ρ x)).1 = 1 := x.2
    have hyp : (Φ (ρ x)) ^ p = 1 := by
      rw [← map_pow, ← map_pow, hexpD, map_one, map_one]
    have h1 : (Φ (ρ x)).2 ^ p = 1 := by
      have := congrArg Prod.snd hyp
      simpa using this
    have h2 : orderOf (Φ (ρ x)).2 ∣ exactE τ := by
      have := orderOf_dvd_natCard (Φ (ρ x)).2
      have hne : exactE τ ≠ 0 := by rcases hτ with rfl | rfl | rfl <;> simp [exactE]
      have h3 : Nat.card (Multiplicative (ZMod (exactE τ))) = exactE τ := by
        have : NeZero (exactE τ) := ⟨hne⟩
        rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
      rwa [h3] at this
    have h4 : orderOf (Φ (ρ x)).2 ∣ p := orderOf_dvd_of_pow_eq_one h1
    have h6 : orderOf (Φ (ρ x)).2 ∣ Nat.gcd p 2 := Nat.dvd_gcd h4 (h2.trans hE2)
    have h7 : Nat.gcd p 2 = 1 := by
      rw [Nat.gcd_comm]
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 (fun h =>
        hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h).symm)
    rw [h7] at h6
    have hz : (Φ (ρ x)).2 = 1 := orderOf_eq_one_iff.1 (Nat.dvd_one.1 h6)
    exact Prod.ext hx1 hz
  have hker1 : ∀ x : α.ker, x = 1 := by
    intro x
    have hρp : ρ (x : D) ^ p = 1 := by rw [← map_pow, hexpD, map_one]
    have hρ1 : ρ (x : D) = 1 := hΦ _ (hmem x) hρp
    exact Subtype.ext (hρinj (hρ1.trans (map_one ρ).symm))
  have hk : Nat.card α.ker = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    exact ⟨⟨fun a b => (hker1 a).trans (hker1 b).symm⟩, ⟨1⟩⟩
  have hsplit : Nat.card D = Nat.card α.range * Nat.card α.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup α.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange α).toEquiv]
  have hD' : Nat.card D ≤ p := by
    rw [hsplit, hk, mul_one]
    exact hrange
  omega

theorem kd76c_bridge_E_charp {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {c : TauCeti.PrimePower → TauCeti.LieTypeIndex}
    (hbr : CFSG.TauCetiBridge.Even.UntwistedBridgeAll τ c)
    (q : TauCeti.PrimePower) (hv : (c q).Valid) (S : Type) [Group S]
    (e0 : S ≃* TauCeti.ValidLieTypeIndex.Group ⟨c q, hv⟩) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : q.p = p) (D : Subgroup (MulAut S)) (hD : IsElemAbelian p D)
    (hcard : p < Nat.card D) : ∃ x ∈ D ⊓ innerAut S, x ≠ 1 := by
  subst hpq
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  obtain ⟨e⟩ := nonempty_mulEquiv_adjoint_of_bridge hbr q hv e0
  set φ : MulAut S ≃* MulAut (adjointGroup τ (GaloisField q.p q.exponent)) :=
    MulAut.congr e with hφ
  have hcardD : Nat.card (D.map φ.toMonoidHom) = Nat.card D :=
    Subgroup.card_map_of_injective φ.injective
  obtain ⟨x', ⟨hx'D, hx'I⟩, hx'1⟩ := kd76c_exists_inner_adjointE_charp hτ hp hp2
    (D.map φ.toMonoidHom)
    (by
      rintro _ ⟨a, ha, rfl⟩
      change φ a ^ q.p = 1
      rw [← map_pow, hD.2 a ha, map_one])
    (by rw [hcardD]; exact hcard)
  obtain ⟨x, hxD, rfl⟩ := hx'D
  obtain ⟨g, hg⟩ := hx'I
  refine ⟨x, ⟨hxD, e.symm g, ?_⟩, fun h => hx'1 (by simp [h])⟩
  apply φ.injective
  change _ = φ.toMonoidHom x
  rw [← hg]
  ext s
  simp [hφ, MulAut.congr_apply]

theorem kd76cLieP_E6 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    KD76cLieP p (fun d => ∃ q, d = .E6 q) := by
  intro S _ _ _ _ idx hP hchar hiso D hD hcard hDI
  obtain ⟨q, hq⟩ := hP
  obtain ⟨d, hv⟩ := idx
  simp only at hq
  subst hq
  exfalso
  have hchar' : (TauCeti.LieTypeIndex.E6 q).characteristic = p := hchar
  rw [TauCeti.LieTypeIndex.characteristic_E6] at hchar'
  obtain ⟨e0⟩ := hiso
  obtain ⟨x, hx, hx1⟩ := kd76c_bridge_E_charp (Or.inl rfl)
    CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6 q hv S e0 hp hp2 hchar' D hD
    (by rw [hcard]; exact kd76c_lt_sq hp)
  exact kd76c_absurd hDI hx hx1

theorem kd76cLieP_E7 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    KD76cLieP p (fun d => ∃ q, d = .E7 q) := by
  intro S _ _ _ _ idx hP hchar hiso D hD hcard hDI
  obtain ⟨q, hq⟩ := hP
  obtain ⟨d, hv⟩ := idx
  simp only at hq
  subst hq
  exfalso
  have hchar' : (TauCeti.LieTypeIndex.E7 q).characteristic = p := hchar
  rw [TauCeti.LieTypeIndex.characteristic_E7] at hchar'
  obtain ⟨e0⟩ := hiso
  obtain ⟨x, hx, hx1⟩ := kd76c_bridge_E_charp (Or.inr (Or.inl rfl))
    CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e7 q hv S e0 hp hp2 hchar' D hD
    (by rw [hcard]; exact kd76c_lt_sq hp)
  exact kd76c_absurd hDI hx hx1

theorem kd76cLieP_E8 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    KD76cLieP p (fun d => ∃ q, d = .E8 q) := by
  intro S _ _ _ _ idx hP hchar hiso D hD hcard hDI
  obtain ⟨q, hq⟩ := hP
  obtain ⟨d, hv⟩ := idx
  simp only at hq
  subst hq
  exfalso
  have hchar' : (TauCeti.LieTypeIndex.E8 q).characteristic = p := hchar
  rw [TauCeti.LieTypeIndex.characteristic_E8] at hchar'
  obtain ⟨e0⟩ := hiso
  obtain ⟨x, hx, hx1⟩ := kd76c_bridge_E_charp (Or.inr (Or.inr rfl))
    CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e8 q hv S e0 hp hp2 hchar' D hD
    (by rw [hcard]; exact kd76c_lt_sq hp)
  exact kd76c_absurd hDI hx hx1

theorem kd76cLieP_twistedE6 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    KD76cLieP p (fun d => ∃ q, d = .twistedE6 q) := by
  intro S _ _ _ _ idx hP hchar hiso D hD hcard hDI
  obtain ⟨q, hr⟩ := hP
  obtain ⟨d, hv⟩ := idx
  simp only at hr
  subst hr
  exfalso
  have hchar' : (TauCeti.LieTypeIndex.twistedE6 q).characteristic = p := hchar
  rw [TauCeti.LieTypeIndex.characteristic_twistedE6] at hchar'
  subst hchar'
  obtain ⟨e0⟩ := hiso
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  let K := GaloisField q.p (2 * q.exponent)
  have hf : 1 ≤ q.exponent := q.exponent_pos
  have hKc : Nat.card K = (q.p ^ q.exponent) ^ TwistTag.E6.order := by
    change Nat.card (GaloisField q.p (2 * q.exponent)) = _
    rw [GaloisField.card _ _ (by have := q.exponent_pos; omega)]
    change _ = (q.p ^ q.exponent) ^ 2
    rw [← pow_mul, mul_comm]
  obtain ⟨σ, hσ, -⟩ := finite_graph_field_parameter_fields TwistTag.E6 q.prime_p hf K hKc
  have hK2 : Nat.card K = (q.p ^ q.exponent) ^ 2 := hKc
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, -, -, hΘker, -, -, -⟩, -, -, -, ⟨eC⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form q.prime_p hf K hK2 σ hσ
  have hqc : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  obtain ⟨eB⟩ := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.twistedE6 q hv K
    (by rw [hqc]; exact hK2) σ.toRingHom (fun x => by rw [hqc]; exact hσ x)
  have e : S ≃* graphFixedRootGroup TwistTag.E6 K σ.toRingHom :=
    e0.trans (eB.symm.trans eC)
  have hcyc : IsCyclic (K ≃+* K) :=
    CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic K
  have hinn : (inner (twistedE6RootGroup K σ)).Normal :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner_normal _
  have hψ := lot_card_range_diag_outer_le_three hK2 σ hσ
  have hN1 : (Θ.ker).map (QuotientGroup.mk' (inner (twistedE6RootGroup K σ))) ≤
      ((QuotientGroup.mk' (twistedE6Inn K σ)).comp
        (compatDiagAutHom TwistTag.E6 K σ.toRingHom)).range := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hΘker] at hx
    obtain ⟨y, hy, z, ⟨u, rfl⟩, hyz⟩ := Subgroup.mem_sup_of_normal_left.1 hx
    refine ⟨u, ?_⟩
    change QuotientGroup.mk' (twistedE6Inn K σ) (compatDiagAutHom TwistTag.E6 K σ.toRingHom u) = _
    have hy1 : QuotientGroup.mk' (inner (twistedE6RootGroup K σ)) y = 1 :=
      (QuotientGroup.eq_one_iff y).2 hy
    rw [← hyz, map_mul, hy1, one_mul]
  have hfin : Finite ((QuotientGroup.mk' (twistedE6Inn K σ)).comp
        (compatDiagAutHom TwistTag.E6 K σ.toRingHom)).range := inferInstance
  have hNfin : Finite ((Θ.ker).map (QuotientGroup.mk' (inner (twistedE6RootGroup K σ)))) :=
    Finite.of_injective (Subgroup.inclusion hN1) (Subgroup.inclusion_injective hN1)
  have hcopDom := kd76c_coprime_pi_units hp
    (fun a => ↥(CFSG.LieType.Chevalley.orbitField TwistTag.E6 K σ.toRingHom a))
  have hNp : ∀ y ∈ (Θ.ker).map (QuotientGroup.mk' (inner (twistedE6RootGroup K σ))),
      y ^ q.p = 1 → y = 1 :=
    fun y hy hyp => kd76c_no_p_torsion _ hcopDom (hN1 hy) hyp
  have hlt : q.p < Nat.card D := by rw [hcard]; exact kd76c_lt_sq hp
  obtain ⟨x, hx, hx1⟩ := kd76c_transport e D (fun a ha => hD.2 a ha) hlt
    (fun D' hexp hc => kd76c_two_step_coprime (inner (twistedE6RootGroup K σ)) Θ hp hNp
      D' hexp hc)
  exact kd76c_absurd hDI hx hx1

theorem kd76c_holds {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hOpen : KD76cLieP p KDOpenFam) : KD76c p := by
  intro S _ _ hS hnab hChev D hD hcard hDI
  unfold IsChevSimple at hChev
  rcases hChev with ⟨i, hi, ⟨e⟩⟩ | hamb
  · cases i with
    | cyclic r hr => simp [onLie] at hi
    | alternating n hn => simp [onLie] at hi
    | sporadic s => simp [onLie] at hi
    | lie idx =>
      have hchar : idx.1.characteristic = p := hi
      by_cases hO : KDOpenFam idx.1
      · obtain ⟨h1, h2⟩ := hOpen S hS hnab idx hO hchar ⟨e⟩ D hD hcard hDI
        exact ⟨h1, TauCeti.CFSGIndex.lie idx, h2, ⟨e⟩⟩
      · rcases kd76c_cover idx.1 idx.2 hO with ⟨r, q, hq⟩ | ⟨r, q, hq⟩ | ⟨r, q, hq⟩ |
          ⟨q, hq⟩ | ⟨q, hq⟩ | ⟨q, hq⟩ | ⟨q, hq⟩ | ⟨q, hq⟩ | ⟨q, hq⟩ | ⟨m, hm⟩ | ⟨q, hq⟩ | hc2
        · obtain ⟨h1, h2⟩ := kd76cLieP_A hp hp2 S hS hnab idx ⟨r, q, hq⟩ hchar ⟨e⟩ D hD hcard hDI
          exact ⟨h1, TauCeti.CFSGIndex.lie idx, h2, ⟨e⟩⟩
        · obtain ⟨h1, h2⟩ := kd76cLieP_twistedA hp hp2 S hS hnab idx ⟨r, q, hq⟩ hchar ⟨e⟩ D hD
            hcard hDI
          exact ⟨h1, TauCeti.CFSGIndex.lie idx, h2, ⟨e⟩⟩
        · obtain ⟨h1, h2⟩ := kd76cLieP_C hp hp2 S hS hnab idx ⟨r, q, hq⟩ hchar ⟨e⟩ D hD hcard hDI
          exact ⟨h1, TauCeti.CFSGIndex.lie idx, h2, ⟨e⟩⟩
        · obtain ⟨h1, h2⟩ := kd76cLieP_E6 hp hp2 S hS hnab idx ⟨q, hq⟩ hchar ⟨e⟩ D hD hcard hDI
          exact ⟨h1, TauCeti.CFSGIndex.lie idx, h2, ⟨e⟩⟩
        · obtain ⟨h1, h2⟩ := kd76cLieP_E7 hp hp2 S hS hnab idx ⟨q, hq⟩ hchar ⟨e⟩ D hD hcard hDI
          exact ⟨h1, TauCeti.CFSGIndex.lie idx, h2, ⟨e⟩⟩
        · obtain ⟨h1, h2⟩ := kd76cLieP_E8 hp hp2 S hS hnab idx ⟨q, hq⟩ hchar ⟨e⟩ D hD hcard hDI
          exact ⟨h1, TauCeti.CFSGIndex.lie idx, h2, ⟨e⟩⟩
        · obtain ⟨h1, h2⟩ := kd76cLieP_twistedE6 hp hp2 S hS hnab idx ⟨q, hq⟩ hchar ⟨e⟩ D hD
            hcard hDI
          exact ⟨h1, TauCeti.CFSGIndex.lie idx, h2, ⟨e⟩⟩
        · obtain ⟨h1, h2⟩ := kd76cLieP_F4 hp hp2 S hS hnab idx ⟨q, hq⟩ hchar ⟨e⟩ D hD hcard hDI
          exact ⟨h1, TauCeti.CFSGIndex.lie idx, h2, ⟨e⟩⟩
        · obtain ⟨h1, h2⟩ := kd76cLieP_G2 hp hp2 S hS hnab idx ⟨q, hq⟩ hchar ⟨e⟩ D hD hcard hDI
          exact ⟨h1, TauCeti.CFSGIndex.lie idx, h2, ⟨e⟩⟩
        · obtain ⟨h1, h2⟩ := kd76cLieP_reeG2 hp hp2 S hS hnab idx ⟨m, hm⟩ hchar ⟨e⟩ D hD hcard hDI
          exact ⟨h1, TauCeti.CFSGIndex.lie idx, h2, ⟨e⟩⟩
        · obtain ⟨h1, h2⟩ := kd76cLieP_trialityD4 hp hp2 S hS hnab idx ⟨q, hq⟩ hchar ⟨e⟩ D hD hcard
            hDI
          exact ⟨h1, TauCeti.CFSGIndex.lie idx, h2, ⟨e⟩⟩
        · exact absurd (hchar.symm.trans hc2) hp2
  · exact (kd76c_ambiguous hp hp2 S hamb D hD hcard hDI).elim

end Exceptional

end CFSG.LocalAnalysis.GLTheoremA
