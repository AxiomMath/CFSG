module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsCaseLBar
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsAutFieldUni
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
import CFSG.RankThree.SteinbergR3EUnitaryFieldDescent
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherIsotropicRadical
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormRealization
import CFSG.LocalAnalysis.ComponentInitial.UnitaryDiagonalOuterOrder
import CFSG.LieType.SeitzGeneration.HyperCoverUnitary
import CFSG.LieType.Steinberg.CentralExt.SUOddClosed
import CFSG.ClassicalGroups.Unitary.Finite
import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear
import CFSG.LocalAnalysis.GL83PartI.I_22_5.Basic
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.SchurFactsCore
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267RankAut
import CFSG.Open.StatedAPI
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Assembly.QuasithinDefs
public import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.Dihedral.DihedralFusionPrefixes
public import CFSG.Foundations
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.KProper
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ComponentInitial.PerfectOuterInjection
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267Facts
public import CFSG.LocalAnalysis.GLTheoremA.P55.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.Pump
public import CFSG.LocalAnalysis.GLTheoremA.S6.InputsProp65
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.LargeEvenClassification.TopScalarLiftSquare
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen

open CFSG.Open Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldAut)
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open CFSG.HardMathSupport.Timmesfeld.LinearRank (PGL)

section Model

open CFSG.SectionRank.OddCover (coe_diagHom)

variable {ℓ f n : ℕ} {K : Type} [Field K]

private noncomputable def suProjEquiv' (h : UnitaryFieldData ℓ f K) (hn : 1 ≤ n) :
    StatedProj (StatedSU n (ℓ ^ f) K) ≃*
      primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
  (unitaryPSUEquiv h hn).symm.trans
    (QuotientGroup.congr _ _ (MulEquiv.subgroupCongr (unitarySU_eq_gramSU h n)) (by
      ext z
      constructor
      · rintro ⟨y, ⟨c, hcN, hcn, hy⟩, rfl⟩
        exact ⟨c, hcN, hcn, hy⟩
      · rintro ⟨c, hcN, hcn, hz⟩
        exact ⟨(MulEquiv.subgroupCongr (unitarySU_eq_gramSU h n)).symm z, ⟨c, hcN, hcn, hz⟩,
          MulEquiv.apply_symm_apply _ _⟩))

abbrev unitaryI (h : UnitaryFieldData ℓ f K) (n : ℕ) : Subgroup (GL (Fin n) K) :=
  primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)

theorem mem_statedSU_iff_gramSU (h : UnitaryFieldData ℓ f K) {g : GL (Fin n) K} :
    g ∈ StatedSU n (ℓ ^ f) K ↔
      g ∈ gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  rw [Units.val_one, ← unitarySU_eq_gramSU h n]

theorem statedSU_le_unitaryI (h : UnitaryFieldData ℓ f K) :
    StatedSU n (ℓ ^ f) K ≤ unitaryI h n := fun _ hg =>
  ((mem_gramSU_iff_unitary h).1 ((mem_statedSU_iff_gramSU h).1 hg)).1

theorem unitaryI_le_normalizer (h : UnitaryFieldData ℓ f K) :
    unitaryI h n ≤ Subgroup.normalizer (StatedSU n (ℓ ^ f) K : Set (GL (Fin n) K)) := by
  intro M hM
  rw [Subgroup.mem_normalizer_iff]
  intro k
  rw [mem_statedSU_iff_gramSU h, mem_statedSU_iff_gramSU h]
  constructor
  · exact conj_mem_gramSU h _ hM
  · intro hk
    have := conj_mem_gramSU h _ (inv_mem hM) hk
    simpa [mul_assoc] using this

theorem unitaryI_le_isomGL (h : UnitaryFieldData ℓ f K) :
    unitaryI h n ≤ Cls.isomGL (Cls.unitForm (ι := Fin n) h.bar) := fun _ hg =>
  Cls.mem_isomGL.2 (unitForm_mulVec_of_mem h hg)

theorem semiConj_mem_unitaryI (h : UnitaryFieldData ℓ f K) {M g : GL (Fin n) K}
    (hM : M ∈ unitaryI h n) (σ : K ≃+* K) (hg : g ∈ unitaryI h n) :
    semiConj M σ g ∈ unitaryI h n := by
  rw [semiConj_apply]
  exact mul_mem (mul_mem hM (glAut_mem_primeFormUnitary h isPrimeFormGram_one σ
    (mul_mem (mul_mem (inv_mem hM) hg) hM))) (inv_mem hM)

theorem formRel_unitForm_of_mem (h : UnitaryFieldData ℓ f K) {M : GL (Fin n) K}
    (hM : M ∈ unitaryI h n) (σ : K ≃+* K) : FormRel (Cls.unitForm (ι := Fin n) h.bar) M σ :=
  ⟨1, fun u v => by
    rw [Units.val_one, one_mul, one_mul, semiMap_apply, semiMap_apply, unitForm_mulVec_of_mem h hM,
      unitForm_map, unitForm_mulVec_of_mem h (inv_mem hM)]⟩

theorem mem_center_of_conj_statedSU (h : UnitaryFieldData ℓ f K) (hn : 3 ≤ n)
    {c : GL (Fin n) K} (hcU : c ∈ unitaryI h n)
    (hc : ∀ k ∈ StatedSU n (ℓ ^ f) K, c * k * c⁻¹ * k⁻¹ ∈ StatedScalars (Fin n) K) :
    c ∈ Subgroup.center (GL (Fin n) K) := by
  have h1 : primeFormConjHom h _ ⟨c, hcU⟩ = 1 := by
    refine MulEquiv.ext fun x => ?_
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    rw [primeFormConjHom_mk, MulAut.one_apply]
    apply QuotientGroup.eq.2
    obtain ⟨u, hu⟩ := hc g ((mem_statedSU_iff_gramSU h).2 g.2)
    have he : (c * g * c⁻¹)⁻¹ * (g : GL (Fin n) K) = GeneralLinearGroup.scalar (Fin n) u⁻¹ := by
      have : c * g * c⁻¹ = GeneralLinearGroup.scalar (Fin n) u * g := by rw [hu]; group
      rw [this, map_inv, _root_.mul_inv_rev, mul_assoc,
        ← (Subgroup.mem_center_iff.1 (by
          rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
          exact ⟨u⁻¹, by rw [map_inv]⟩ : (GeneralLinearGroup.scalar (Fin n) u)⁻¹ ∈ _) g),
        ← mul_assoc, inv_mul_cancel, one_mul]
    set y : ↥(gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :=
      (⟨c * g * c⁻¹, conj_mem_gramSU h _ hcU g.2⟩ :
        ↥(gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))⁻¹ * g with hy
    have hyv : (y : GL (Fin n) K) = GeneralLinearGroup.scalar (Fin n) u⁻¹ := he
    have hyS := y.2
    rw [hyv, mem_gramSU_iff_unitary] at hyS
    refine ⟨u⁻¹, norm_eq_one_of_scalar_mem_primeFormUnitary h (by omega) 1 hyS.1, ?_, hyv⟩
    apply Units.ext
    have h2 := hyS.2
    rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h2
    rw [Units.val_pow_eq_pow_val, h2, Units.val_one]
  obtain ⟨c', -, hc'⟩ := eq_scalar_of_primeFormConjHom_eq_one h isPrimeFormGram_one hn h1
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
  exact ⟨c', hc'.symm⟩

theorem commutator_statedSU_eq_top (h : UnitaryFieldData ℓ f K) (hn : 3 ≤ n)
    (hq : ¬(n = 3 ∧ ℓ ^ f = 2)) : commutator ↥(StatedSU n (ℓ ^ f) K) = ⊤ := by
  haveI : Fact ℓ.Prime := ⟨h.prime⟩
  haveI : Finite K := h.finite
  haveI : CharP K ℓ := h.charP
  exact (CFSG.ClassicalGroups.Unitary.isPerfect_statedSU h.card_eq_sq hn
    (fun h3 => hq ⟨congrArg Prod.fst h3, congrArg Prod.snd h3⟩)).commutator_eq_top

private theorem isCyclic_ringEquiv'' [Finite K] : IsCyclic (K ≃+* K) := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨p, -, n, hp, hK⟩ := FiniteField.card' K
  have hK' : Nat.card K = p ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hK]
  exact (card_ringAut_and_isCyclic hp K hK').2

private theorem pow_ne_two (h : UnitaryFieldData ℓ f K) (hℓ2 : ℓ ≠ 2) : ℓ ^ f ≠ 2 := by
  intro h2
  have h1 : ℓ ∣ 2 := by
    rw [← h2]
    exact dvd_pow_self ℓ (by have := h.one_le; omega)
  exact hℓ2 ((Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_two).1 h1)

private theorem ne_of_dvd_pow_add_one (h : UnitaryFieldData ℓ f K) {p : ℕ} (hp : p.Prime)
    (hpq : p ∣ ℓ ^ f + 1) : p ≠ ℓ := by
  rintro rfl
  have h1 : p ∣ p ^ f := dvd_pow_self p (by have := h.one_le; omega)
  exact hp.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right h1).1 hpq))

private theorem card_units_eq (h : UnitaryFieldData ℓ f K) :
    Nat.card Kˣ = (ℓ ^ f + 1) * (ℓ ^ f - 1) := by
  haveI : Finite K := h.finite
  have hq : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ h.prime.pos
  obtain ⟨r, hr⟩ : ∃ r, ℓ ^ f = r + 1 := ⟨ℓ ^ f - 1, by omega⟩
  rw [Nat.card_units, h.card, mul_comm 2 f, pow_mul, hr,
    show (r + 1) ^ 2 = (r + 1 + 1) * r + 1 by ring, Nat.add_sub_cancel, Nat.add_sub_cancel]

private theorem bar_mul_self_eq_one (h : UnitaryFieldData ℓ f K) {p : ℕ} (hpq : p ∣ ℓ ^ f + 1)
    {x : K} (hx : x ^ p = 1) : h.bar x * x = 1 := by
  obtain ⟨k, hk⟩ := hpq
  rw [h.bar_apply, ← pow_succ, hk, pow_mul, hx, one_pow]

private theorem scalar_mem_unitaryI_of_pow (h : UnitaryFieldData ℓ f K) {p : ℕ}
    (hpq : p ∣ ℓ ^ f + 1) {l : Kˣ} (hl : l ^ p = 1) :
    GeneralLinearGroup.scalar (Fin n) l ∈ unitaryI h n :=
  scalar_mem_primeFormUnitary_one h (by
    rw [UnitaryFieldData.norm, mul_comm]
    exact bar_mul_self_eq_one h hpq (by rw [← Units.val_pow_eq_pow_val, hl, Units.val_one]))

private theorem norm_eq_one_of_norm_pow (h : UnitaryFieldData ℓ f K) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ ℓ ^ f + 1) {μ : Kˣ} (hμ : h.norm ((μ ^ p : Kˣ) : K) = 1) :
    h.norm (μ : K) = 1 := by
  haveI : Finite K := h.finite
  have hN : ∀ c : Kˣ, h.norm (c : K) = ((c ^ (ℓ ^ f + 1) : Kˣ) : K) := fun c => by
    rw [UnitaryFieldData.norm, h.bar_apply, Units.val_pow_eq_pow_val, pow_succ']
  set ν := μ ^ (ℓ ^ f + 1) with hν
  have h1 : ν ^ p = 1 := by
    apply Units.ext
    rw [hν, ← pow_mul, mul_comm, pow_mul, ← hN (μ ^ p), hμ, Units.val_one]
  have h2 : ν ^ (ℓ ^ f - 1) = 1 := by
    rw [hν, ← pow_mul, ← card_units_eq h, pow_card_eq_one']
  have hcop : Nat.Coprime p (ℓ ^ f - 1) := by
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro hd
    have hq1 : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ h.prime.pos
    have h3 : p ∣ (ℓ ^ f - 1) + 2 := by
      rw [show ℓ ^ f - 1 + 2 = ℓ ^ f + 1 by omega]
      exact hpq
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 ((Nat.dvd_add_right hd).1 h3))
  have h3 : ν = 1 := by
    have := pow_gcd_eq_one.2 ⟨h1, h2⟩
    rwa [Nat.Coprime.gcd_eq_one hcop, pow_one] at this
  rw [hN, ← hν, h3, Units.val_one]

theorem diagTorus_le_statedSU (h : UnitaryFieldData ℓ f K) {m p : ℕ} (hpq : p ∣ ℓ ^ f + 1) :
    diagTorus m p K ≤ StatedSU (m + 2) (ℓ ^ f) K := by
  intro d hd
  refine (mem_unitarySU_iff h).2 ⟨diagTorus_le_det_one hd, ?_⟩
  obtain ⟨e, rfl⟩ := hd
  rw [MonoidHom.comp_apply, coe_diagHom, Matrix.diagonal_map (map_zero h.bar),
    Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  exact bar_mul_self_eq_one h hpq (by rw [← Units.val_pow_eq_pow_val, torusVec_pow, Units.val_one])

theorem diagInvol_mem_statedSU (h : UnitaryFieldData ℓ f K) (m : ℕ) :
    diagInvol m K ∈ StatedSU (m + 2) (ℓ ^ f) K := by
  refine (mem_unitarySU_iff h).2 ⟨diagInvol_det m, ?_⟩
  rw [diagInvol, coe_diagHom, Matrix.diagonal_map (map_zero h.bar), Matrix.diagonal_transpose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  split_ifs <;> simp

end Model

section Cover

variable {ℓ f n : ℕ} {K : Type} [Field K]

theorem exists_cover_statedSU {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S : Subgroup Ω}
    (h : UnitaryFieldData ℓ f K) (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ)
    (hperf : ⁅S, S⁆ = S) (hcore : GLAPPrimeCore p ↥S = ⊥) (hn : 3 ≤ n)
    (hq : ¬(n = 3 ∧ ℓ ^ f = 2)) (e : PSimple p S ≃* StatedProj (StatedSU n (ℓ ^ f) K)) :
    ∃ φ : ↥(StatedSU n (ℓ ^ f) K) →* Ω, φ.range = S ∧
      φ.ker ≤ (StatedScalars (Fin n) K).subgroupOf (StatedSU n (ℓ ^ f) K) := by
  haveI : Fact ℓ.Prime := ⟨h.prime⟩
  haveI : Finite K := h.finite
  haveI : CharP K ℓ := h.charP
  have hF : Nat.card K = (ℓ ^ f) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
  have hq' : (n, ℓ ^ f) ≠ (3, 2) := fun h3 => hq ⟨congrArg Prod.fst h3, congrArg Prod.snd h3⟩
  by_cases ho : Even n
  ·
    have hn4 : 4 ≤ n := by
      obtain ⟨k, hk⟩ := ho
      omega
    haveI : Group.IsPerfect ↥S := ⟨S267.perfect_of_commutator_self_eq hperf⟩
    set ε := (S267.BadExc.psimpleEquivCenterQuotOfCore hcore).symm.trans e with hε
    set ρ : ↥S →* StatedProj (StatedSU n (ℓ ^ f) K) :=
      ε.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥S)) with hρ
    have hρs : Function.Surjective ρ := ε.surjective.comp (QuotientGroup.mk'_surjective _)
    have hρk : ρ.ker = Subgroup.center ↥S := by
      ext x
      rw [MonoidHom.mem_ker, hρ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        map_eq_one_iff _ ε.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    have hcop : Even n → ℓ.Coprime (Nat.card ρ.ker) := fun _ => by
      haveI : Fact p.Prime := ⟨hp⟩
      obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1
        (MovingAround.SchurFacts.isPGroup_center_of_glaPPrimeCore_eq_bot hp hcore)
      rw [hρk, hk]
      exact Nat.Coprime.pow_right _ ((Nat.coprime_primes h.prime hp).2 (Ne.symm hpℓ))
    obtain ⟨φ', hφ's, hφ'⟩ := CFSG.LieType.SeitzGeneration.exists_su_cover_hom hF h.one_le hn4 ρ
      hρs hρk.le hcop
    refine ⟨S.subtype.comp φ', ?_, fun g hg => ?_⟩
    · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 hφ's, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype]
    · have h1 : φ' g = 1 := Subtype.ext hg
      have h2 := hφ' g
      rw [h1, map_one, QuotientGroup.mk'_apply] at h2
      exact (QuotientGroup.eq_one_iff g).1 h2.symm
  · exact exists_cover_of_odd_splitting hp hp2 hperf hcore e
      (fun _ _ _ π hπ hcen _ =>
        CFSG.LieType.Steinberg.CentralExt.SUOdd.statedSU_odd_exists_section_of_central hF
          h.one_le hn ho hq' hπ hcen)

end Cover

section Aut

variable {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S : Subgroup Ω} [S.Normal]
variable {ℓ f n : ℕ} {K : Type} [Field K]

theorem ker_barCover_statedSU (h : UnitaryFieldData ℓ f K) (hn : 3 ≤ n)
    {φ : ↥(StatedSU n (ℓ ^ f) K) →* Ω} (hφS : φ.range = S)
    (hφk : φ.ker ≤ (StatedScalars (Fin n) K).subgroupOf (StatedSU n (ℓ ^ f) K)) :
    ((barMk S).comp φ).ker = (StatedScalars (Fin n) K).subgroupOf (StatedSU n (ℓ ^ f) K) :=
  ker_barCover hφS (statedSU_le_unitaryI h) (fun _ hc hk => mem_center_of_conj_statedSU h hn hc hk)
    hφk

private noncomputable def barModelSU (h : UnitaryFieldData ℓ f K) (hn : 3 ≤ n)
    {φ : ↥(StatedSU n (ℓ ^ f) K) →* Ω} (hφS : φ.range = S)
    (hφk : φ.ker ≤ (StatedScalars (Fin n) K).subgroupOf (StatedSU n (ℓ ^ f) K)) :
    primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ≃* ↥(barS S) :=
  (suProjEquiv' h (by omega)).symm.trans
    (coverProjEquiv ((barMk S).comp φ) (range_barCover hφS) (ker_barCover_statedSU h hn hφS hφk))

private noncomputable def gammaSU (h : UnitaryFieldData ℓ f K) (hn : 3 ≤ n)
    {φ : ↥(StatedSU n (ℓ ^ f) K) →* Ω} (hφS : φ.range = S)
    (hφk : φ.ker ≤ (StatedScalars (Fin n) K).subgroupOf (StatedSU n (ℓ ^ f) K)) :
    Ω →* MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :=
  (MulAut.congr (barModelSU h hn hφS hφk).symm).toMonoidHom.comp
    (MulAut.conjNormal.comp (barMk S))

private theorem gammaSU_apply (h : UnitaryFieldData ℓ f K) (hn : 3 ≤ n)
    {φ : ↥(StatedSU n (ℓ ^ f) K) →* Ω} (hφS : φ.range = S)
    (hφk : φ.ker ≤ (StatedScalars (Fin n) K).subgroupOf (StatedSU n (ℓ ^ f) K)) (x : Ω) :
    gammaSU h hn hφS hφk x = transAut (barModelSU h hn hφS hφk) (barMk S x) :=
  rfl

private theorem gammaSU_eq_conjHom_iff (h : UnitaryFieldData ℓ f K) (hn : 3 ≤ n)
    (hq : ¬(n = 3 ∧ ℓ ^ f = 2)) {φ : ↥(StatedSU n (ℓ ^ f) K) →* Ω} (hφS : φ.range = S)
    (hφk : φ.ker ≤ (StatedScalars (Fin n) K).subgroupOf (StatedSU n (ℓ ^ f) K)) (x : Ω)
    (M : ↥(unitaryI h n)) :
    gammaSU h hn hφS hφk x = primeFormConjHom h _ M ↔ ActsAs φ x M := by
  set e := barModelSU h hn hφS hφk with he
  set c := MulEquiv.subgroupCongr (unitarySU_eq_gramSU h n) with hc
  constructor
  · intro h1
    apply actsAs_of_barCover (commutator_statedSU_eq_top h hn hq) hφS
      (unitaryI_le_normalizer h M.2)
    intro k
    refine ⟨c.symm ⟨M * (c k) * (M : GL (Fin n) K)⁻¹, conj_mem_gramSU h _ M.2 (c k).2⟩, rfl, ?_⟩
    have h2 := transAut_spec e (barMk S x) (QuotientGroup.mk (c k))
    rw [show transAut e (barMk S x) = gammaSU h hn hφS hφk x from rfl, h1,
      primeFormConjHom_mk] at h2
    exact h2
  · intro h1
    refine MulEquiv.ext fun y => ?_
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    apply e.injective
    apply Subtype.ext
    rw [show gammaSU h hn hφS hφk x = transAut e (barMk S x) from rfl, transAut_spec,
      primeFormConjHom_mk]
    obtain ⟨k', hk', hφ⟩ := h1 (c.symm g)
    have hkk : k' = c.symm ⟨M * g * (M : GL (Fin n) K)⁻¹, conj_mem_gramSU h _ M.2 g.2⟩ :=
      Subtype.ext hk'
    change barMk S x * barMk S (φ (c.symm g)) * (barMk S x)⁻¹ =
      barMk S (φ (c.symm ⟨M * g * (M : GL (Fin n) K)⁻¹, conj_mem_gramSU h _ M.2 g.2⟩))
    rw [← hkk, hφ, map_mul, map_mul, map_inv]

private theorem mem_innerDiag_iff_uni (h : UnitaryFieldData ℓ f K) (hn : 3 ≤ n)
    (hq : ¬(n = 3 ∧ ℓ ^ f = 2)) {φ : ↥(StatedSU n (ℓ ^ f) K) →* Ω} (hφS : φ.range = S)
    (hφk : φ.ker ≤ (StatedScalars (Fin n) K).subgroupOf (StatedSU n (ℓ ^ f) K))
    {B : Subgroup Ω} {x : Ω} :
    x ∈ innerDiag φ (unitaryI h n) (unitaryI_le_normalizer h) B ↔
      x ∈ B ∧ gammaSU h hn hφS hφk x ∈
        primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  rw [mem_innerDiag]
  constructor
  · rintro ⟨hxB, A, hA, hact⟩
    exact ⟨hxB, ⟨A, hA⟩, ((gammaSU_eq_conjHom_iff h hn hq hφS hφk x ⟨A, hA⟩).2 hact).symm⟩
  · rintro ⟨hxB, M, hM⟩
    exact ⟨hxB, M, M.2, (gammaSU_eq_conjHom_iff h hn hq hφS hφk x M).1 hM.symm⟩

private theorem innerDiag_split_uni (h : UnitaryFieldData ℓ f K) (hp : p.Prime) (hn : 3 ≤ n)
    (hq : ¬(n = 3 ∧ ℓ ^ f = 2)) {φ : ↥(StatedSU n (ℓ ^ f) K) →* Ω} (hφS : φ.range = S)
    (hφk : φ.ker ≤ (StatedScalars (Fin n) K).subgroupOf (StatedSU n (ℓ ^ f) K))
    {B : Subgroup Ω} (hB : IsElemAbelian p B) :
    innerDiag φ (unitaryI h n) (unitaryI_le_normalizer h) B = B ∨
      ∃ b ∈ B, b ∉ innerDiag φ (unitaryI h n) (unitaryI_le_normalizer h) B ∧
        B = innerDiag φ (unitaryI h n) (unitaryI_le_normalizer h) B ⊔ Subgroup.zpowers b ∧
        Subgroup.zpowers b ⊓ innerDiag φ (unitaryI h n) (unitaryI_le_normalizer h) B = ⊥ := by
  haveI : Finite K := h.finite
  haveI := isCyclic_ringEquiv'' (K := K)
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  obtain ⟨-, -, -, -, -, -, -, hFker, -, -, -⟩ :=
    unitary_prime_form_full_semilinear_realization h hC hn hq
  refine eq_or_exists_zpowers_of_isCyclic hp hB innerDiag_le
    ((primeFormFieldFactor h hC hn hq).comp ((gammaSU h hn hφS hφk).comp B.subtype))
    fun x => ?_
  rw [mem_innerDiag_iff_uni h hn hq hφS hφk, ← hFker, MonoidHom.mem_ker]
  simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
  exact ⟨fun h1 => ⟨x.2, h1⟩, fun h1 => h1.2⟩

private theorem exists_fieldAct_caseL_uni (h : UnitaryFieldData ℓ f K) (hp : p.Prime)
    (hp2 : p ≠ 2) (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ ℓ ^ f = 2)) (hpℓ : p ≠ ℓ)
    {φ : ↥(StatedSU n (ℓ ^ f) K) →* Ω} (hφS : φ.range = S)
    (hφk : φ.ker ≤ (StatedScalars (Fin n) K).subgroupOf (StatedSU n (ℓ ^ f) K)) {b : Ω}
    (hbp : b ^ p = 1)
    (hbD : gammaSU h hn hφS hφk b ∉
      primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
    ∃ (A : GL (Fin n) K) (σ : K ≃+* K), A ∈ unitaryI h n ∧ FieldAct p φ b A σ := by
  haveI : Finite K := h.finite
  haveI : Fact p.Prime := ⟨hp⟩
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  set e := barModelSU h hn hφS hφk with he
  set γ := gammaSU h hn hφS hφk b with hγ
  have hγp : γ ^ p = 1 := by rw [hγ, ← map_pow, hbp, map_one]
  have hγ1 : γ ≠ 1 := fun h1 => hbD (by rw [h1]; exact one_mem _)
  have hγo : orderOf γ = p := orderOf_eq_prime hγp hγ1
  obtain ⟨-, -, -, -, -, -, -, hFker, -, -, -⟩ :=
    unitary_prime_form_full_semilinear_realization h hC hn hq
  set σ := primeFormFieldFactor h hC hn hq γ with hσ
  have hσp : σ ^ p = 1 := by rw [hσ, ← map_pow, hγp, map_one]
  have hσ1 : σ ≠ 1 := fun h1 => hbD (by rw [← hFker, MonoidHom.mem_ker]; exact h1)
  have hσo : orderOf σ = p := orderOf_eq_prime hσp hσ1
  obtain ⟨hpf, hcardK0, -, -, -, M, hM⟩ :=
    CFSG.RankThree.UnitaryDescent.unitary_prime_semilinear_field_descent h hn hq hp hp2 hpℓ γ
      hγo σ rfl hσo
  have hγeq : γ =
      primeFormConjHom h _ M * primeFormFieldHom h hC σ * (primeFormConjHom h _ M)⁻¹ := by
    rw [← hM]
    group
  refine ⟨M, σ, M.2, fieldAct_of_barCover (commutator_statedSU_eq_top h hn hq) hφS
    ⟨hσo, ?_, fun k => ?_⟩⟩
  ·
    rw [hcardK0, h.card, ← pow_mul, ← pow_mul]
    congr 1
    obtain ⟨m, rfl⟩ := hpf
    rw [Nat.mul_div_cancel_left m hp.pos]
    ring
  ·
    set kg : ↥(gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :=
      MulEquiv.subgroupCongr (unitarySU_eq_gramSU h n) k with hkg
    set g' : ↥(gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :=
      primeFormConjSU h _ M (primeFormFieldSU h hC σ (primeFormConjSU h _ M⁻¹ kg)) with hg'
    refine ⟨(MulEquiv.subgroupCongr (unitarySU_eq_gramSU h n)).symm g', ?_, ?_⟩
    · rw [semiConj_apply]
      change (M : GL (Fin n) K) * glAut σ (((M⁻¹ : primeFormUnitary h _) : GL (Fin n) K) *
        (k : GL (Fin n) K) * ((M⁻¹ : primeFormUnitary h _) : GL (Fin n) K)⁻¹) *
        (M : GL (Fin n) K)⁻¹ = _
      rw [Subgroup.coe_inv, inv_inv]
      rfl
    · have h1 : γ (QuotientGroup.mk kg) = QuotientGroup.mk g' := by
        rw [hγeq, MulAut.mul_apply, MulAut.mul_apply, ← map_inv, primeFormConjHom_mk]
        rfl
      have h2 := transAut_spec e (barMk S b) (QuotientGroup.mk kg)
      rw [show transAut e (barMk S b) = γ from rfl, h1] at h2
      exact h2

end Aut

section Torus

variable {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S : Subgroup Ω} [S.Normal]
variable {ℓ f : ℕ} {K : Type} [Field K]

private theorem isElemAbelian_range' {G G' : Type*} [Group G] [Group G'] {B : Subgroup G}
    (hB : IsElemAbelian p B) (f : ↥B →* G') : IsElemAbelian p f.range := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · obtain ⟨_, x, rfl⟩ := a
    obtain ⟨_, y, rfl⟩ := b
    apply Subtype.ext
    show f x * f y = f y * f x
    rw [← map_mul, ← map_mul, hB.1.is_comm.comm x y]
  · rintro _ ⟨x, rfl⟩
    rw [← map_pow, show x ^ p = 1 from Subtype.ext (hB.2 x x.2), map_one]

private theorem isElemAbelian_mono'' {G : Type*} [Group G] {E F : Subgroup G}
    (hE : IsElemAbelian p E) (hFE : F ≤ E) : IsElemAbelian p F :=
  ⟨⟨⟨fun a b => Subtype.ext (hE.comm (hFE a.2) (hFE b.2))⟩⟩, fun x hx => hE.2 x (hFE hx)⟩

private theorem torus_rank_uni (h : UnitaryFieldData ℓ f K) (hp : p.Prime)
    (hpK : p ∣ Nat.card Kˣ) (hpq : p ∣ ℓ ^ f + 1) (h2K : (2 : K) ≠ 0) {m : ℕ} (hm : 1 ≤ m)
    {φ : ↥(StatedSU (m + 2) (ℓ ^ f) K) →* Ω} (hφS : φ.range = S)
    (hφZ : ((barMk S).comp φ).ker =
      (StatedScalars (Fin (m + 2)) K).subgroupOf (StatedSU (m + 2) (ℓ ^ f) K))
    {A : GL (Fin (m + 2)) K} (hA : A ∈ unitaryI h (m + 2)) {σ : K ≃+* K} (hσ : σ ^ p = 1)
    {B₂ : Subgroup Ω} (hB₂ : IsElemAbelian p B₂) {s : ℕ} (hB₂c : Nat.card B₂ = p ^ s)
    (hB₂S : B₂ ⊓ S ≤ Subgroup.centralizer (S : Set Ω))
    (hB₂fix : ∀ y ∈ B₂, ∀ k : ↥(StatedSU (m + 2) (ℓ ^ f) K),
      glFieldAut (Fin (m + 2)) K σ (A⁻¹ * k * A) = A⁻¹ * k * A → y * φ k = φ k * y) :
    m + s ≤ GLATwoLocalRank p Ω := by
  haveI : Finite K := h.finite
  have hAN := unitaryI_le_normalizer h hA
  set c := MulAut.conj A with hc
  set X := (diagTorus m p K).map c.toMonoidHom with hX
  have hcA : ∀ g : GL (Fin (m + 2)) K, c.toMonoidHom g = A * g * A⁻¹ := fun g => rfl
  have hfixd : ∀ d ∈ diagTorus m p K, glFieldAut (Fin (m + 2)) K σ d = d := fun d hd =>
    Units.ext (by rw [coe_glFieldAut]; exact diagTorus_map_eq hp hσ hd)
  have hfixt : glFieldAut (Fin (m + 2)) K σ (diagInvol m K) = diagInvol m K :=
    Units.ext (by rw [coe_glFieldAut]; exact diagInvol_map_eq m σ)
  have hXH : X ≤ StatedSU (m + 2) (ℓ ^ f) K := by
    rintro _ ⟨d, hd, rfl⟩
    rw [hcA]
    exact (Subgroup.mem_normalizer_iff.1 hAN d).1 (diagTorus_le_statedSU h hpq hd)
  have hXel : IsElemAbelian p X := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨_, ⟨d, hd, rfl⟩⟩ := a
      obtain ⟨_, ⟨d', hd', rfl⟩⟩ := b
      apply Subtype.ext
      show c.toMonoidHom d * c.toMonoidHom d' = c.toMonoidHom d' * c.toMonoidHom d
      rw [← map_mul, ← map_mul,
        (isElemAbelian_diagTorus m p (L := K)).comm hd hd']
    · rintro _ ⟨d, hd, rfl⟩
      rw [← map_pow, (isElemAbelian_diagTorus m p (L := K)).2 d hd, map_one]
  have hcen : ∀ g, A * g * A⁻¹ ∈ Subgroup.center (GL (Fin (m + 2)) K) →
      g ∈ Subgroup.center (GL (Fin (m + 2)) K) := fun g hg => by
    have h1 : g = A⁻¹ * (A * g * A⁻¹) * A := by group
    rw [h1, mul_assoc, ← Subgroup.mem_center_iff.1 hg A, ← mul_assoc, inv_mul_cancel, one_mul]
    exact hg
  have hXZ : X ⊓ StatedScalars (Fin (m + 2)) K = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨⟨d, hd, rfl⟩, hz⟩
    rw [CFSG.Open.StatedAPI.statedScalars_eq_center, hcA] at hz
    have h1 : d ∈ diagTorus m p K ⊓ Subgroup.center (GL (Fin (m + 2)) K) := ⟨hd, hcen d hz⟩
    rw [diagTorus_inf_center, Subgroup.mem_bot] at h1
    rw [Subgroup.mem_bot, h1, map_one]
  have hXc : Nat.card X = p ^ m := by
    rw [hX, Subgroup.card_map_of_injective c.injective, card_diagTorus hp hpK m]
  have htH : A * diagInvol m K * A⁻¹ ∈ StatedSU (m + 2) (ℓ ^ f) K :=
    (Subgroup.mem_normalizer_iff.1 hAN _).1 (diagInvol_mem_statedSU h m)
  have ht2 : (A * diagInvol m K * A⁻¹) ^ 2 = 1 := by
    rw [conj_pow, diagInvol_sq, mul_one, mul_inv_cancel]
  have htZ : A * diagInvol m K * A⁻¹ ∉ StatedScalars (Fin (m + 2)) K := by
    rw [CFSG.Open.StatedAPI.statedScalars_eq_center]
    exact fun h' => diagInvol_not_mem m h2K hm (hcen _ h')
  have hXt : ∀ x ∈ X, x * (A * diagInvol m K * A⁻¹) = (A * diagInvol m K * A⁻¹) * x := by
    rintro _ ⟨d, hd, rfl⟩
    rw [hcA]
    calc A * d * A⁻¹ * (A * diagInvol m K * A⁻¹) = A * (d * diagInvol m K) * A⁻¹ := by group
      _ = A * (diagInvol m K * d) * A⁻¹ := by rw [diagTorus_comm_diagInvol hd]
      _ = A * diagInvol m K * A⁻¹ * (A * d * A⁻¹) := by group
  exact le_glaTwoLocalRank_of_torus hp hφS hφZ hXH hXel hXZ hXc htH ht2 htZ hXt hB₂ hB₂c
    hB₂S (fun y hy x hx => hB₂fix y hy x (by
      obtain ⟨d, hd, hdx⟩ := hx
      have : A⁻¹ * (x : GL (Fin (m + 2)) K) * A = d := by
        rw [← hdx, hcA]
        group
      rw [this, hfixd d hd]))
    (fun y hy => hB₂fix y hy _ (by
      have : A⁻¹ * (A * diagInvol m K * A⁻¹) * A = diagInvol m K := by group
      show glFieldAut (Fin (m + 2)) K σ (A⁻¹ * (A * diagInvol m K * A⁻¹) * A) = _
      rw [this, hfixt]))

end Torus

section Main

variable {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S : Subgroup Ω} [S.Normal]
variable {ℓ f n : ℕ} {K : Type} [Field K]

open CFSG.HardMathSupport.Timmesfeld.LinearRank (pRank_pgl_le card_le_of_pRank_le)

theorem card_le_of_caseL_uni (hp : p.Prime) (hp2 : p ≠ 2) (hperf : ⁅S, S⁆ = S)
    (hcore : GLAPPrimeCore p ↥S = ⊥) (hn : 3 ≤ n) (h : UnitaryFieldData ℓ f K) (hℓ2 : ℓ ≠ 2)
    (hdiag : p ∣ Nat.gcd n (ℓ ^ f + 1)) (e : PSimple p S ≃* StatedProj (StatedSU n (ℓ ^ f) K))
    {B : Subgroup Ω} (hB : IsElemAbelian p B) (hBC : Nat.card ↥(B ⊓ centModSubgroup p S) = p) :
    Nat.card B ≤ p ^ (n + 1) := by
  haveI : Finite K := h.finite
  have hpq : p ∣ ℓ ^ f + 1 := hdiag.trans (Nat.gcd_dvd_right _ _)
  have hq : ¬(n = 3 ∧ ℓ ^ f = 2) := fun h3 => pow_ne_two h hℓ2 h3.2
  obtain ⟨φ, hφS, hφk⟩ := exists_cover_statedSU h hp hp2 (ne_of_dvd_pow_add_one h hp hpq) hperf
    hcore hn hq e
  have hcent : ∀ c ∈ unitaryI h n,
      (∀ k ∈ StatedSU n (ℓ ^ f) K, c * k * c⁻¹ * k⁻¹ ∈ StatedScalars (Fin n) K) →
        c ∈ Subgroup.center (GL (Fin n) K) := fun _ hc hk => mem_center_of_conj_statedSU h hn hc hk
  have hY := unitaryI_le_normalizer h (n := n)
  have hpK : p ∣ Nat.card Kˣ := by
    rw [card_units_eq h]
    exact hpq.mul_right _
  set B₁ := innerDiag φ (unitaryI h n) hY B with hB₁
  set ψ := innerDiagHom (hY := hY) (B := B) hcent hφk with hψ
  have hB₀ : Nat.card ↥(B ⊓ Subgroup.centralizer (S : Set Ω)) = p := by
    rw [← inf_centMod_eq_inf_centralizer inferInstance hcore, hBC]
  have hB₁el : IsElemAbelian p B₁ := isElemAbelian_mono'' hB innerDiag_le
  have hψc : Nat.card ψ.range ≤ p ^ (n - 1) :=
    card_le_of_pRank_le hp (pRank_pgl_le hp hp2 hpK (by omega)) ψ.range
      (isElemAbelian_range' hB₁el ψ)
  have hB₁c : Nat.card B₁ ≤ p ^ n := by
    rw [hB₁, card_innerDiag hφS hcent hφk, hB₀]
    calc p * Nat.card ψ.range ≤ p * p ^ (n - 1) := Nat.mul_le_mul_left _ hψc
      _ = p ^ n := by rw [← pow_succ']; congr 1; omega
  rcases innerDiag_split_uni h hp hn hq hφS hφk hB with h' | ⟨b, hbB, hbB₁, hBb, hbinf⟩
  · rw [← h']
    exact hB₁c.trans (Nat.pow_le_pow_right hp.pos (Nat.le_succ n))
  · have hcomm : ∀ x ∈ B₁, ∀ y ∈ Subgroup.zpowers b, x * y = y * x := fun x hx y hy =>
      hB.comm (innerDiag_le hx) (Subgroup.zpowers_le.2 hbB hy)
    haveI : Fact p.Prime := ⟨hp⟩
    have hb1 : b ≠ 1 := fun h1 => hbB₁ (h1 ▸ one_mem _)
    have hzc : Nat.card (Subgroup.zpowers b) = p := by
      rw [Nat.card_zpowers, orderOf_eq_prime (hB.2 b hbB) hb1]
    rw [hBb, GL83.CompFam.card_sup_of_commute_of_inf_eq_bot hcomm (by rwa [inf_comm]), hzc,
      pow_succ]
    exact Nat.mul_le_mul_right _ hB₁c

theorem exists_caseLData_uni (hp : p.Prime) (hp2 : p ≠ 2) (hperf : ⁅S, S⁆ = S)
    (hcore : GLAPPrimeCore p ↥S = ⊥) (hn : 4 ≤ n) (h : UnitaryFieldData ℓ f K) (hℓ2 : ℓ ≠ 2)
    (hdiag : p ∣ Nat.gcd n (ℓ ^ f + 1)) (e : PSimple p S ≃* StatedProj (StatedSU n (ℓ ^ f) K))
    {B : Subgroup Ω} (hB : IsElemAbelian p B) (hBC : Nat.card ↥(B ⊓ centModSubgroup p S) = p)
    (hrank : p ^ GLATwoLocalRank p Ω ≤ Nat.card B) :
    ∃ φ : ↥(StatedSU n (ℓ ^ f) K) →* Ω, φ.range = S ∧
      φ.ker ≤ (StatedScalars (Fin n) K).subgroupOf (StatedSU n (ℓ ^ f) K) ∧
      ∃ (B₁ : Subgroup Ω) (θ : ↥B₁ →* GL (Fin n) K),
        B₁ ≤ B ∧ B ⊓ Subgroup.centralizer (S : Set Ω) ≤ B₁ ∧
        θ.range ≤ Cls.isomGL (Cls.unitForm (ι := Fin n) h.bar) ∧
        IsElemAbelian p θ.range ∧ θ.range ⊓ StatedScalars (Fin n) K = ⊥ ∧
        (∀ x : ↥B₁, θ x = 1 ↔ (x : Ω) ∈ Subgroup.centralizer (S : Set Ω)) ∧
        (∀ (x : ↥B₁) (k : ↥(StatedSU n (ℓ ^ f) K)), ∃ k' : ↥(StatedSU n (ℓ ^ f) K),
          (k' : GL (Fin n) K) = θ x * k * (θ x)⁻¹ ∧ φ k' = x * φ k * x⁻¹) ∧
        p ^ (n - 2) ≤ Nat.card θ.range ∧
        (B₁ = B ∨ ∃ b ∈ B, b ∉ B₁ ∧ B = B₁ ⊔ Subgroup.zpowers b ∧
          Subgroup.zpowers b ⊓ B₁ = ⊥ ∧
          ∃ (A : GL (Fin n) K) (σ : K ≃+* K), FieldAct p φ b A σ ∧
            FormRel (Cls.unitForm (ι := Fin n) h.bar) A σ ∧
            ∀ x : ↥B₁, semiConj A σ (θ x) * (θ x)⁻¹ ∈ StatedScalars (Fin n) K) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite K := h.finite
  have hn3 : 3 ≤ n := by omega
  have hpq : p ∣ ℓ ^ f + 1 := hdiag.trans (Nat.gcd_dvd_right _ _)
  have hn5 : 5 ≤ n := by
    by_contra h5
    have h4 : n = 4 := by omega
    have h1 : p ∣ 2 ^ 2 := by
      have := hdiag.trans (Nat.gcd_dvd_left _ _)
      rwa [h4] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h1))
  have hq : ¬(n = 3 ∧ ℓ ^ f = 2) := fun h3 => pow_ne_two h hℓ2 h3.2
  have hpℓ := ne_of_dvd_pow_add_one h hp hpq
  obtain ⟨φ, hφS, hφk⟩ := exists_cover_statedSU h hp hp2 hpℓ hperf hcore hn3 hq e
  have hcent : ∀ c ∈ unitaryI h n,
      (∀ k ∈ StatedSU n (ℓ ^ f) K, c * k * c⁻¹ * k⁻¹ ∈ StatedScalars (Fin n) K) →
        c ∈ Subgroup.center (GL (Fin n) K) := fun _ hc hk =>
    mem_center_of_conj_statedSU h hn3 hc hk
  have hY := unitaryI_le_normalizer h (n := n)
  have hpK : p ∣ Nat.card Kˣ := by
    rw [card_units_eq h]
    exact hpq.mul_right _
  have h2K : (2 : K) ≠ 0 := by
    haveI : CharP K ℓ := h.charP
    intro h0
    have := (CharP.cast_eq_zero_iff K ℓ 2).1 (by exact_mod_cast h0)
    exact hℓ2 ((Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_two).1 this)
  set B₁ := innerDiag φ (unitaryI h n) hY B with hB₁
  set ψ := innerDiagHom (hY := hY) (B := B) hcent hφk with hψ
  have hB₀ : Nat.card ↥(B ⊓ Subgroup.centralizer (S : Set Ω)) = p := by
    rw [← inf_centMod_eq_inf_centralizer inferInstance hcore, hBC]
  have hB₁el : IsElemAbelian p B₁ := isElemAbelian_mono'' hB innerDiag_le
  have hψel := isElemAbelian_range' hB₁el ψ
  have hB₁c : Nat.card B₁ = p * Nat.card ψ.range := by
    rw [hB₁, card_innerDiag hφS hcent hφk, hB₀]
  have hφZ := ker_barCover_statedSU h hn3 hφS hφk
  have hB₀B₁ : B ⊓ Subgroup.centralizer (S : Set Ω) ≤ B₁ := inf_centralizer_le_innerDiag hφS
  have hsplit := innerDiag_split_uni h hp hn3 hq hφS hφk hB
  have hfield : B₁ = B ∨ ∃ b ∈ B, b ∉ B₁ ∧ B = B₁ ⊔ Subgroup.zpowers b ∧
      Subgroup.zpowers b ⊓ B₁ = ⊥ ∧ ∃ (A : GL (Fin n) K) (σ : K ≃+* K),
        A ∈ unitaryI h n ∧ FieldAct p φ b A σ := by
    rcases hsplit with h' | ⟨b, hbB, hbB₁, hBb, hbinf⟩
    · exact Or.inl h'
    · refine Or.inr ⟨b, hbB, hbB₁, hBb, hbinf, ?_⟩
      have hbD : gammaSU h hn3 hφS hφk b ∉
          primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := fun hD =>
        hbB₁ ((mem_innerDiag_iff_uni h hn3 hq hφS hφk).2 ⟨hbB, hD⟩)
      exact exists_fieldAct_caseL_uni h hp hp2 hn3 hq hpℓ hφS hφk (hB.2 b hbB) hbD
  have hψc : p ^ (n - 2) ≤ Nat.card ψ.range := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    rw [show m + 2 - 2 = m by omega]
    have hm : 1 ≤ m := by omega
    rcases hfield with h' | ⟨b, hbB, hbB₁, hBb, hbinf, A, σ, hA, hact⟩
    ·
      have hφH : ∀ k, φ k ∈ S := fun k => hφS ▸ ⟨k, rfl⟩
      have h1 := torus_rank_uni h hp hpK hpq h2K hm hφS hφZ (A := 1) (one_mem _)
        (σ := RingEquiv.refl K) (one_pow p) (isElemAbelian_mono'' hB inf_le_left) (s := 1)
        (by rw [hB₀, pow_one]) (fun x hx => hx.1.2)
        (fun y hy k _ => ((Subgroup.mem_centralizer_iff.1 hy.2) _ (hφH k)).symm)
      have h2 : p ^ (m + 1) ≤ Nat.card B :=
        (Nat.pow_le_pow_right hp.pos h1).trans hrank
      rw [← h', hB₁c, pow_succ, mul_comm] at h2
      exact Nat.le_of_mul_le_mul_left h2 hp.pos
    ·
      have hσ : σ ^ p = 1 := hact.1 ▸ pow_orderOf_eq_one σ
      set D := B ⊓ Subgroup.centralizer (S : Set Ω) with hD
      have hDb : D ⊓ Subgroup.zpowers b = ⊥ := by
        rw [eq_bot_iff]
        rintro x ⟨hxD, hxb⟩
        have : x ∈ Subgroup.zpowers b ⊓ B₁ := ⟨hxb, hB₀B₁ hxD⟩
        rwa [hbinf] at this
      have hcommD : ∀ x ∈ D, ∀ y ∈ Subgroup.zpowers b, x * y = y * x := fun x hx y hy =>
        hB.comm hx.1 (Subgroup.zpowers_le.2 hbB hy)
      have hb1 : b ≠ 1 := fun h1 => hbB₁ (h1 ▸ one_mem _)
      have hzc : Nat.card (Subgroup.zpowers b) = p := by
        rw [Nat.card_zpowers, orderOf_eq_prime (hB.2 b hbB) hb1]
      have hB₂c : Nat.card ↥(D ⊔ Subgroup.zpowers b) = p ^ 2 := by
        rw [GL83.CompFam.card_sup_of_commute_of_inf_eq_bot hcommD hDb, hB₀, hzc, sq]
      have hB₂le : D ⊔ Subgroup.zpowers b ≤ B := sup_le inf_le_left (Subgroup.zpowers_le.2 hbB)
      have hB₂S : (D ⊔ Subgroup.zpowers b) ⊓ S ≤ Subgroup.centralizer (S : Set Ω) := by
        rintro x ⟨hx, hxS⟩
        obtain ⟨z, hz, k, -, rfl⟩ := Cls.exists_mul_pow_of_mem_sup hp hB inf_le_left hbB hx
        have hbk : b ^ k ∈ B₁ := by
          refine ⟨B.pow_mem hbB k, ?_⟩
          obtain ⟨g, hg⟩ : z * b ^ k ∈ φ.range := hφS ▸ hxS
          refine ⟨g, statedSU_le_unitaryI h g.2, fun k₀ =>
            ⟨conjOn (hY (statedSU_le_unitaryI h g.2)) k₀, coe_conjOn _ k₀, ?_⟩⟩
          have hk₀ : φ k₀ ∈ S := hφS ▸ ⟨k₀, rfl⟩
          have hzc : z * (b ^ k * φ k₀ * (b ^ k)⁻¹) = (b ^ k * φ k₀ * (b ^ k)⁻¹) * z :=
            ((Subgroup.mem_centralizer_iff.1 hz.2) _ ((inferInstance : S.Normal).conj_mem _ hk₀
              _)).symm
          have h1 : φ (conjOn (hY (statedSU_le_unitaryI h g.2)) k₀) = φ g * φ k₀ * (φ g)⁻¹ := by
            rw [← map_inv, ← map_mul, ← map_mul]
            congr 1
          rw [h1, hg]
          calc z * b ^ k * φ k₀ * (z * b ^ k)⁻¹ = z * (b ^ k * φ k₀ * (b ^ k)⁻¹) * z⁻¹ := by
                group
            _ = b ^ k * φ k₀ * (b ^ k)⁻¹ := by rw [hzc, mul_inv_cancel_right]
        have : b ^ k ∈ Subgroup.zpowers b ⊓ B₁ := ⟨Subgroup.pow_mem _ (Subgroup.mem_zpowers b) k,
          hbk⟩
        rw [hbinf, Subgroup.mem_bot] at this
        rw [this, mul_one]
        exact hz.2
      have h1 := torus_rank_uni h hp hpK hpq h2K hm hφS hφZ hA hσ
        (isElemAbelian_mono'' hB hB₂le) (s := 2) hB₂c hB₂S (fun y hy k hk => by
          have hsk : semiConj A σ k = k := by
            rw [semiConj_apply, hk]
            group
          have hbk : b * φ k = φ k * b := by
            obtain ⟨k', hk', hφ⟩ := hact.2.2 k
            have hkk : k' = k := Subtype.ext (by rw [hk', hsk])
            rw [hkk] at hφ
            calc b * φ k = b * φ k * b⁻¹ * b := by group
              _ = φ k * b := by rw [← hφ]
          have hle : D ⊔ Subgroup.zpowers b ≤ Subgroup.centralizer {φ k} := by
            refine sup_le (fun z hz => ?_) (Subgroup.zpowers_le.2 ?_)
            · rw [Subgroup.mem_centralizer_singleton_iff]
              exact ((Subgroup.mem_centralizer_iff.1 hz.2) _ (hφS ▸ ⟨k, rfl⟩)).symm
            · rw [Subgroup.mem_centralizer_singleton_iff]
              exact hbk
          exact Subgroup.mem_centralizer_singleton_iff.1 (hle hy))
      have h2 : p ^ (m + 2) ≤ Nat.card B :=
        (Nat.pow_le_pow_right hp.pos h1).trans hrank
      have hBc : Nat.card B = Nat.card B₁ * p := by
        have hcomm : ∀ x ∈ B₁, ∀ y ∈ Subgroup.zpowers b, x * y = y * x := fun x hx y hy =>
          hB.comm (innerDiag_le hx) (Subgroup.zpowers_le.2 hbB hy)
        conv_lhs => rw [hBb]
        rw [GL83.CompFam.card_sup_of_commute_of_inf_eq_bot hcomm (by rwa [inf_comm]), hzc]
      rw [hBc, hB₁c, pow_succ, pow_succ] at h2
      have h3 : p ^ m * p * p ≤ Nat.card ψ.range * p * p := by linarith
      exact Nat.le_of_mul_le_mul_right (Nat.le_of_mul_le_mul_right h3 hp.pos) hp.pos
  obtain ⟨A', hA'Y, hA'el, hA'Z, hA'E⟩ := exists_elemAbelian_lift hp hp2 hpK hn5 hψel hψc
    (innerDiagHom_range_le hcent hφk) (fun l hl => scalar_mem_unitaryI_of_pow h hpq hl)
    (fun μ hμ => ⟨μ, scalar_mem_primeFormUnitary_one h (norm_eq_one_of_norm_pow h hp hp2 hpq
      (norm_eq_one_of_scalar_mem_primeFormUnitary h (by omega) 1 hμ)), rfl⟩)
  obtain ⟨θ, hθr, hθψ, hθact, hθ1⟩ := exists_theta_of_lift hφS hcent hφk hA'Z hA'E
  have hA'c : Nat.card A' = Nat.card ψ.range := by
    rw [← hA'E]
    have hinj : Function.Injective ((pglMk n K).comp A'.subtype) := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro a ha
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype, pglMk_eq_one_iff,
        ← CFSG.HardMathSupport.Timmesfeld.LinearRank.mem_center_iff] at ha
      have : (a : GL (Fin n) K) ∈ A' ⊓ Subgroup.center (GL (Fin n) K) := ⟨a.2, ha⟩
      rw [hA'Z, Subgroup.mem_bot] at this
      exact (Subgroup.mem_bot).2 (Subtype.ext this)
    have hmap : Subgroup.map (pglMk n K) A' = ((pglMk n K).comp A'.subtype).range := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [hmap]
    exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
  have hθY : ∀ x : ↥B₁, θ x ∈ unitaryI h n := fun x => hA'Y (hθr ▸ ⟨x, rfl⟩)
  refine ⟨φ, hφS, hφk, B₁, θ, innerDiag_le, hB₀B₁,
    by rw [hθr]; exact hA'Y.trans (unitaryI_le_isomGL h), hθr ▸ hA'el,
    by rw [hθr, CFSG.Open.StatedAPI.statedScalars_eq_center]; exact hA'Z, hθ1,
    fun x k => hθact x k, by rw [hθr, hA'c]; exact hψc, ?_⟩
  rcases hfield with h' | ⟨b, hbB, hbB₁, hBb, hbinf, A, σ, hA, hact⟩
  · exact Or.inl h'
  · refine Or.inr ⟨b, hbB, hbB₁, hBb, hbinf, A, σ, hact, formRel_unitForm_of_mem h hA σ,
      fun x => ?_⟩
    rw [CFSG.Open.StatedAPI.statedScalars_eq_center]
    exact semiConj_mul_inv_mem_center hY hcent hφk hact (hθY x)
      (semiConj_mem_unitaryI h hA σ (hθY x)) (hθact x) (hB.comm hbB (innerDiag_le x.2))

end Main

end CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen

end
