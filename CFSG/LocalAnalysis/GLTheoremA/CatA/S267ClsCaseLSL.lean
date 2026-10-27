module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsCaseLBar
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
import CFSG.RankThree.SteinbergR3ELinearFieldDescent
import CFSG.RankThree.PartOne.S11d.OutLinear
import CFSG.LieType.Steinberg.CentralExt.SLCentrallyClosed
import CFSG.Adapters.StatedSLPerfect
import CFSG.LocalAnalysis.GL83PartI.I_22_5.Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen

open CFSG.Open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane
open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldAut)
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open CFSG.HardMathSupport.Timmesfeld.LinearRank (PGL)

section Model

variable {n : ℕ} {K : Type} [Field K]

private noncomputable def statedProjSLEquiv (n : ℕ) (K : Type) [Field K] :
    StatedProj (StatedSL n K) ≃* projectiveSL n K :=
  (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj n K).symm.trans
    (LinearCover.projectiveSpecialLinearEquivProjectiveSL n K)

private theorem coe_equivSL (g : SpecialLinearGroup (Fin n) K) :
    ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL n K g : GL (Fin n) K)) =
      SpecialLinearGroup.toGL g :=
  rfl

theorem normalizer_statedSL (A : GL (Fin n) K) :
    A ∈ Subgroup.normalizer (StatedSL n K : Set (GL (Fin n) K)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro k
  constructor
  · intro hk
    apply CFSG.Open.StatedAPI.mem_statedSL_of_det
    rw [Units.val_mul, Units.val_mul, det_mul, det_mul, CFSG.Open.StatedAPI.det_of_mem_statedSL hk,
      mul_one, ← det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, det_one]
  · intro hk
    apply CFSG.Open.StatedAPI.mem_statedSL_of_det
    have h := CFSG.Open.StatedAPI.det_of_mem_statedSL hk
    rw [Units.val_mul, Units.val_mul, det_mul, det_mul, mul_comm, ← mul_assoc, ← det_mul,
      ← Units.val_mul, inv_mul_cancel, Units.val_one, det_one, one_mul] at h
    exact h

theorem mem_center_of_conj_statedSL [Finite K] (hn : 3 ≤ n) {c : GL (Fin n) K}
    (hc : ∀ k ∈ StatedSL n K, c * k * c⁻¹ * k⁻¹ ∈ StatedScalars (Fin n) K) :
    c ∈ Subgroup.center (GL (Fin n) K) := by
  have h1 : conjAut n K c = 1 := by
    refine MulEquiv.ext fun x => ?_
    obtain ⟨g, rfl⟩ := proj_surjective n K x
    rw [conjAut_proj, MulAut.one_apply, proj_eq_proj_iff, scalars_eq_center,
      ← SpecialLinearGroup.toGL_mem_center_iff, map_mul, map_inv]
    obtain ⟨u, hu⟩ := hc _ (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL n K g).2
    rw [coe_equivSL] at hu
    have hconj : SpecialLinearGroup.toGL (CatalogueBHigherLinearAction.slConjugation n K c g) =
        c * SpecialLinearGroup.toGL g * c⁻¹ := by
      apply Units.ext
      rw [SpecialLinearGroup.coe_GL_coe_matrix, coe_slConjugation, Units.val_mul, Units.val_mul,
        SpecialLinearGroup.coe_GL_coe_matrix]
    rw [hconj]
    have he : (c * SpecialLinearGroup.toGL g * c⁻¹)⁻¹ * SpecialLinearGroup.toGL g =
        (SpecialLinearGroup.toGL g)⁻¹ * (GeneralLinearGroup.scalar (Fin n) u)⁻¹ *
          SpecialLinearGroup.toGL g := by
      rw [hu]
      group
    have hs : (GeneralLinearGroup.scalar (Fin n) u)⁻¹ ∈ Subgroup.center (GL (Fin n) K) := by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨u⁻¹, by rw [map_inv]⟩
    rw [he, mul_assoc, ← Subgroup.mem_center_iff.1 hs, inv_mul_cancel_left]
    exact hs
  obtain ⟨u, rfl⟩ := (conjAut_eq_one_iff hn c).1 h1
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
  exact ⟨u, rfl⟩

theorem exists_section_statedSL [Finite K] (hn : 3 ≤ n) (hK : 5 ≤ Nat.card K) {E : Type}
    [Group E] (π : E →* StatedSL n K) (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) : ∃ s : ↥(StatedSL n K) →* E, ∀ g, π (s g) = g := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  set eq := CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL (m + 1) K with heq
  set π' : E →* SpecialLinearGroup (Fin (m + 1)) K := eq.symm.toMonoidHom.comp π with hπ'
  have hπ's : Function.Surjective π' := eq.symm.surjective.comp hπ
  have hπ'k : π'.ker ≤ Subgroup.center E := by
    intro x hx
    apply hcen
    rw [MonoidHom.mem_ker] at hx ⊢
    have : eq.symm (π x) = 1 := hx
    rwa [map_eq_one_iff _ eq.symm.injective] at this
  obtain ⟨σ, hσ⟩ := CFSG.LieType.Steinberg.CentralExt.SLClosed.sl_exists_section_of_central
    (by omega) hK hπ's hπ'k
  refine ⟨σ.comp eq.symm.toMonoidHom, fun g => ?_⟩
  have h1 := hσ (eq.symm g)
  have h2 : eq.symm (π (σ (eq.symm g))) = eq.symm g := h1
  exact eq.symm.injective h2

theorem exists_cover_statedSL {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S : Subgroup Ω}
    [Finite K] (hp : p.Prime) (hp2 : p ≠ 2) (hperf : ⁅S, S⁆ = S)
    (hcore : GLAPPrimeCore p ↥S = ⊥) (hn : 3 ≤ n) (hK : 5 ≤ Nat.card K)
    (e : PSimple p S ≃* StatedProj (StatedSL n K)) :
    ∃ φ : ↥(StatedSL n K) →* Ω, φ.range = S ∧
      φ.ker ≤ (StatedScalars (Fin n) K).subgroupOf (StatedSL n K) :=
  exists_cover_of_odd_splitting hp hp2 hperf hcore e
    (fun _ _ _ π hπ hcen _ => exists_section_statedSL hn hK π hπ hcen)

theorem commutator_statedSL_eq_top (hn : 3 ≤ n) : commutator ↥(StatedSL n K) = ⊤ :=
  (CFSG.Open.StatedAPI.isPerfect_statedSL_of_three_le hn K).commutator_eq_top

private theorem mem_semilinearAutGroup_of_pow_eq_one [Finite K] (hn : 3 ≤ n)
    {γ : MulAut (projectiveSL n K)} {m : ℕ} (hm : Odd m) (hγ : γ ^ m = 1) :
    γ ∈ semilinearAutGroup n K := by
  obtain ⟨hgenTop, -⟩ := automorphism_generation (K := K) hn
  obtain ⟨-, -, -, -, -, -, -, hidx, -, -⟩ := standard_outer_quotients (n := n) (K := K)
  have : Finite (MulAut (projectiveSL n K)) := finite_mulAut_projectiveSL n
  have hidx' : (semilinearAutGroup n K).index ≤ 2 := by
    have h2 : (semilinearAutGroup n K).relIndex (standardAutGroup n K) ≤ 2 := hidx
    rwa [hgenTop, Subgroup.relIndex_top_right] at h2
  exact CFSG.RankThree.PartOne.OutStructure.mem_of_pow_mem_of_index_le_two _ hidx' hm
    (by rw [hγ]; exact one_mem _)

private theorem isCyclic_ringEquiv' [Finite K] : IsCyclic (K ≃+* K) := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨p, -, n, hp, hK⟩ := FiniteField.card' K
  have hK' : Nat.card K = p ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hK]
  exact (card_ringAut_and_isCyclic hp K hK').2

end Model

section Aut

variable {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S : Subgroup Ω} [S.Normal]
variable {n : ℕ} {K : Type} [Field K] [Finite K]

theorem ker_barCover_statedSL (hn : 3 ≤ n) {φ : ↥(StatedSL n K) →* Ω} (hφS : φ.range = S)
    (hφk : φ.ker ≤ (StatedScalars (Fin n) K).subgroupOf (StatedSL n K)) :
    ((barMk S).comp φ).ker = (StatedScalars (Fin n) K).subgroupOf (StatedSL n K) :=
  ker_barCover hφS (le_top : StatedSL n K ≤ ⊤) (fun _ _ hc => mem_center_of_conj_statedSL hn hc)
    hφk

private noncomputable def barModelSL (hn : 3 ≤ n) {φ : ↥(StatedSL n K) →* Ω} (hφS : φ.range = S)
    (hφk : φ.ker ≤ (StatedScalars (Fin n) K).subgroupOf (StatedSL n K)) :
    projectiveSL n K ≃* ↥(barS S) :=
  (statedProjSLEquiv n K).symm.trans
    (coverProjEquiv ((barMk S).comp φ) (range_barCover hφS) (ker_barCover_statedSL hn hφS hφk))

private noncomputable def gammaSL (hn : 3 ≤ n) {φ : ↥(StatedSL n K) →* Ω} (hφS : φ.range = S)
    (hφk : φ.ker ≤ (StatedScalars (Fin n) K).subgroupOf (StatedSL n K)) :
    Ω →* MulAut (projectiveSL n K) :=
  (MulAut.congr (barModelSL hn hφS hφk).symm).toMonoidHom.comp
    (MulAut.conjNormal.comp (barMk S))

private theorem gammaSL_apply (hn : 3 ≤ n) {φ : ↥(StatedSL n K) →* Ω} (hφS : φ.range = S)
    (hφk : φ.ker ≤ (StatedScalars (Fin n) K).subgroupOf (StatedSL n K)) (x : Ω) :
    gammaSL hn hφS hφk x = transAut (barModelSL hn hφS hφk) (barMk S x) :=
  rfl

private theorem barModelSL_proj (hn : 3 ≤ n) {φ : ↥(StatedSL n K) →* Ω} (hφS : φ.range = S)
    (hφk : φ.ker ≤ (StatedScalars (Fin n) K).subgroupOf (StatedSL n K))
    (g : SpecialLinearGroup (Fin n) K) :
    ((barModelSL hn hφS hφk (proj n K g) : ↥(barS S)) : Ω ⧸ centerIn S) =
      barMk S (φ (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL n K g)) :=
  rfl

private theorem coe_equivSL_slConjugation (A : GL (Fin n) K) (g : SpecialLinearGroup (Fin n) K) :
    ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL n K
        (CatalogueBHigherLinearAction.slConjugation n K A g) : GL (Fin n) K)) =
      A * (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL n K g : GL (Fin n) K) *
        A⁻¹ := by
  apply Units.ext
  rw [coe_equivSL, coe_equivSL, SpecialLinearGroup.coe_GL_coe_matrix, coe_slConjugation,
    Units.val_mul, Units.val_mul, SpecialLinearGroup.coe_GL_coe_matrix]

private theorem gammaSL_eq_conjAut_iff (hn : 3 ≤ n) {φ : ↥(StatedSL n K) →* Ω}
    (hφS : φ.range = S) (hφk : φ.ker ≤ (StatedScalars (Fin n) K).subgroupOf (StatedSL n K))
    (x : Ω) (A : GL (Fin n) K) : gammaSL hn hφS hφk x = conjAut n K A ↔ ActsAs φ x A := by
  set e := barModelSL hn hφS hφk with he
  set eq := CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL n K with heq
  constructor
  · intro h
    apply actsAs_of_barCover (commutator_statedSL_eq_top hn) hφS (normalizer_statedSL A)
    intro k
    refine ⟨eq (CatalogueBHigherLinearAction.slConjugation n K A (eq.symm k)), ?_, ?_⟩
    · rw [coe_equivSL_slConjugation, MulEquiv.apply_symm_apply]
    · have h1 := transAut_spec e (barMk S x) (proj n K (eq.symm k))
      rw [← gammaSL_apply hn hφS hφk, h, conjAut_proj, barModelSL_proj, barModelSL_proj,
        MulEquiv.apply_symm_apply] at h1
      simp only [MonoidHom.comp_apply]
      exact h1
  · intro h
    refine MulEquiv.ext fun y => ?_
    obtain ⟨g, rfl⟩ := proj_surjective n K y
    apply e.injective
    apply Subtype.ext
    rw [gammaSL_apply, transAut_spec, conjAut_proj, barModelSL_proj, barModelSL_proj]
    obtain ⟨k', hk', hφ⟩ := h (eq g)
    have hkk : k' = eq (CatalogueBHigherLinearAction.slConjugation n K A g) :=
      Subtype.ext (by rw [hk', coe_equivSL_slConjugation])
    rw [← hkk, hφ, map_mul, map_mul, map_inv]

private theorem mem_innerDiag_iff_lin (hn : 3 ≤ n) {φ : ↥(StatedSL n K) →* Ω}
    (hφS : φ.range = S) (hφk : φ.ker ≤ (StatedScalars (Fin n) K).subgroupOf (StatedSL n K))
    {B : Subgroup Ω} {x : Ω} :
    x ∈ innerDiag φ ⊤ (fun A _ => normalizer_statedSL A) B ↔
      x ∈ B ∧ gammaSL hn hφS hφk x ∈ linearAutGroup n K := by
  rw [mem_innerDiag, mem_linearAutGroup_iff]
  constructor
  · rintro ⟨hxB, A, -, hA⟩
    exact ⟨hxB, A, ((gammaSL_eq_conjAut_iff hn hφS hφk x A).2 hA).symm⟩
  · rintro ⟨hxB, A, hA⟩
    exact ⟨hxB, A, Subgroup.mem_top A, (gammaSL_eq_conjAut_iff hn hφS hφk x A).1 hA.symm⟩

private theorem isCyclic_semilinear_quot {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hn : 3 ≤ n)
    (hK : Nat.card K = ℓ ^ f) [CharP K ℓ]
    [(linearAutGroup n K).subgroupOf (semilinearAutGroup n K) |>.Normal] :
    IsCyclic (↥(semilinearAutGroup n K) ⧸
      (linearAutGroup n K).subgroupOf (semilinearAutGroup n K)) := by
  obtain ⟨-, -, -, -, hsup, hDn, -, -⟩ :=
    CFSG.RankThree.LinearDescent.higher_linear_prime_semilinear_field_descent hℓ hf hn hK
  haveI := hDn
  haveI := isCyclic_ringEquiv' (K := K)
  set R := (fieldAut n K).range
  have hRE : R ≤ semilinearAutGroup n K := hsup ▸ le_sup_right
  haveI : IsCyclic ↥R := isCyclic_of_surjective (fieldAut n K).rangeRestrict
    (fieldAut n K).rangeRestrict_surjective
  refine isCyclic_of_surjective ((QuotientGroup.mk' _).comp (Subgroup.inclusion hRE)) ?_
  intro q
  obtain ⟨⟨a, ha⟩, rfl⟩ := QuotientGroup.mk'_surjective _ q
  rw [← hsup] at ha
  obtain ⟨d, hd, r, hr, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 ha
  refine ⟨⟨r, hr⟩, ?_⟩
  simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply]
  apply QuotientGroup.eq.2
  rw [Subgroup.mem_subgroupOf]
  simp only [Subgroup.coe_inv, Subgroup.coe_mul, Subgroup.coe_inclusion]
  have : r⁻¹ * (d * r) = r⁻¹ * d * r := by group
  rw [this]
  exact hDn.conj_mem' d hd r

private theorem innerDiag_split_lin (hp : p.Prime) (hp2 : p ≠ 2) (hn : 3 ≤ n) {ℓ f : ℕ}
    (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) {φ : ↥(StatedSL n K) →* Ω}
    (hφS : φ.range = S) (hφk : φ.ker ≤ (StatedScalars (Fin n) K).subgroupOf (StatedSL n K))
    {B : Subgroup Ω} (hB : IsElemAbelian p B) :
    innerDiag φ ⊤ (fun A _ => normalizer_statedSL A) B = B ∨
      ∃ b ∈ B, b ∉ innerDiag φ ⊤ (fun A _ => normalizer_statedSL A) B ∧
        B = innerDiag φ ⊤ (fun A _ => normalizer_statedSL A) B ⊔ Subgroup.zpowers b ∧
        Subgroup.zpowers b ⊓ innerDiag φ ⊤ (fun A _ => normalizer_statedSL A) B = ⊥ := by
  haveI : CharP K ℓ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hℓ hf hK
  obtain ⟨-, -, hDnE, -, -, -, -, -⟩ :=
    CFSG.RankThree.LinearDescent.higher_linear_prime_semilinear_field_descent hℓ hf hn hK
  haveI := hDnE
  set γ := gammaSL hn hφS hφk with hγ
  have hγE : ∀ x : ↥B, γ x ∈ semilinearAutGroup n K := fun x =>
    mem_semilinearAutGroup_of_pow_eq_one hn (hp.odd_of_ne_two hp2)
      (by rw [← map_pow, hB.2 x x.2, map_one])
  let κ : ↥B →* ↥(semilinearAutGroup n K) ⧸
      (linearAutGroup n K).subgroupOf (semilinearAutGroup n K) :=
    (QuotientGroup.mk' _).comp ((γ.comp B.subtype).codRestrict _ hγE)
  haveI := isCyclic_semilinear_quot hℓ hf hn hK (n := n) (K := K)
  refine eq_or_exists_zpowers_of_isCyclic hp hB innerDiag_le κ fun x => ?_
  rw [mem_innerDiag_iff_lin hn hφS hφk]
  simp only [κ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf, MonoidHom.codRestrict_apply, Subgroup.coe_subtype]
  exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩

private theorem exists_fieldAct_caseL_lin (hp : p.Prime) (hp2 : p ≠ 2) (hn : 3 ≤ n) {ℓ f : ℕ}
    (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) (hpℓ : p ≠ ℓ)
    {φ : ↥(StatedSL n K) →* Ω} (hφS : φ.range = S)
    (hφk : φ.ker ≤ (StatedScalars (Fin n) K).subgroupOf (StatedSL n K)) {b : Ω}
    (hbp : b ^ p = 1) (hbD : gammaSL hn hφS hφk b ∉ linearAutGroup n K) :
    ∃ (A : GL (Fin n) K) (σ : K ≃+* K), FieldAct p φ b A σ := by
  haveI : CharP K ℓ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hℓ hf hK
  haveI : Fact p.Prime := ⟨hp⟩
  set e := barModelSL hn hφS hφk with he
  set γ := transAut e (barMk S b) with hγ
  have hγp : γ ^ p = 1 := by
    rw [hγ, ← gammaSL_apply hn hφS hφk, ← map_pow, hbp, map_one]
  have hγ1 : γ ≠ 1 := fun h => hbD (by rw [gammaSL_apply, ← hγ, h]; exact one_mem _)
  have hγo : orderOf γ = p := orderOf_eq_prime hγp hγ1
  have hγE : γ ∈ semilinearAutGroup n K :=
    mem_semilinearAutGroup_of_pow_eq_one hn (hp.odd_of_ne_two hp2) hγp
  obtain ⟨-, -, -, -, -, -, -, hdesc⟩ :=
    CFSG.RankThree.LinearDescent.higher_linear_prime_semilinear_field_descent hℓ hf hn hK
  obtain ⟨hpf, σ, hσo, ⟨h, hhD, hγeq⟩, hσcard⟩ := hdesc p hp hpℓ γ hγE hbD hγo
  obtain ⟨A, rfl⟩ := mem_linearAutGroup_iff.1 hhD
  refine ⟨A, σ, fieldAct_of_barCover (commutator_statedSL_eq_top hn) hφS
    ⟨hσo, ?_, fun k => ?_⟩⟩
  · rw [hσcard, hK, ← pow_mul, Nat.div_mul_cancel hpf]
  · set kS := (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL n K).symm k with hkS
    set kS' := CatalogueBHigherLinearAction.slConjugation n K A
      (SpecialLinearGroup.map σ.toRingHom
        (CatalogueBHigherLinearAction.slConjugation n K A⁻¹ kS)) with hkS'
    refine ⟨CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL n K kS', ?_, ?_⟩
    · apply Units.ext
      rw [CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe, hkS', coe_slConjugation,
        semiConj_apply, Units.val_mul, Units.val_mul, coe_glFieldAut]
      change (A : Matrix (Fin n) (Fin n) K) *
          ((CatalogueBHigherLinearAction.slConjugation n K A⁻¹ kS :
            SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K).map σ *
          ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = _
      have hkm : ((kS : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
          (((k : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) := by
        rw [hkS, ← CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe,
          MulEquiv.apply_symm_apply]
      rw [coe_slConjugation, inv_inv, Units.val_mul, Units.val_mul, hkm]
    · have h1 : γ (proj n K kS) = proj n K kS' := by
        rw [hγeq, MulAut.mul_apply, MulAut.mul_apply, ← map_inv, conjAut_proj, fieldAut_proj,
          conjAut_proj]
      have h2 := transAut_spec e (barMk S b) (proj n K kS)
      rw [← hγ, h1, barModelSL_proj, barModelSL_proj, hkS, MulEquiv.apply_symm_apply] at h2
      simp only [MonoidHom.comp_apply]
      exact h2

end Aut

section Main

variable {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S : Subgroup Ω} [S.Normal]
variable {n : ℕ} {K : Type} [Field K] [Finite K]

open CFSG.HardMathSupport.Timmesfeld.LinearRank (pRank_pgl_le card_le_of_pRank_le)

private theorem five_le_card_of_dvd {p ℓ f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hℓ : ℓ.Prime)
    (hℓ2 : ℓ ≠ 2) (hK : Nat.card K = ℓ ^ f) (hpK : p ∣ Nat.card K - 1) : 5 ≤ Nat.card K := by
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hpos : 0 < Nat.card K - 1 := by
    have := Nat.card_pos (α := K)
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    omega
  have h1 : p ≤ Nat.card K - 1 := Nat.le_of_dvd hpos hpK
  have hodd : Odd (Nat.card K) := hK ▸ (hℓ.odd_of_ne_two hℓ2).pow
  obtain ⟨k, hk⟩ := hodd
  omega

private theorem isElemAbelian_range {G G' : Type*} [Group G] [Group G'] {B : Subgroup G}
    (hB : IsElemAbelian p B) (f : ↥B →* G') : IsElemAbelian p f.range := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · obtain ⟨_, x, rfl⟩ := a
    obtain ⟨_, y, rfl⟩ := b
    apply Subtype.ext
    show f x * f y = f y * f x
    rw [← map_mul, ← map_mul, hB.1.is_comm.comm x y]
  · rintro _ ⟨x, rfl⟩
    rw [← map_pow, show x ^ p = 1 from Subtype.ext (hB.2 x x.2), map_one]

private theorem isElemAbelian_mono' {G : Type*} [Group G] {E F : Subgroup G}
    (hE : IsElemAbelian p E) (hFE : F ≤ E) : IsElemAbelian p F :=
  ⟨⟨⟨fun a b => Subtype.ext (hE.comm (hFE a.2) (hFE b.2))⟩⟩, fun x hx => hE.2 x (hFE hx)⟩

private theorem caseL_setup_lin (hp : p.Prime) (hp2 : p ≠ 2) (hperf : ⁅S, S⁆ = S)
    (hcore : GLAPPrimeCore p ↥S = ⊥) (hn : 3 ≤ n) {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hK : Nat.card K = ℓ ^ f) (hdiag : p ∣ Nat.gcd n (Nat.card K - 1))
    (e : PSimple p S ≃* StatedProj (StatedSL n K)) :
    ∃ φ : ↥(StatedSL n K) →* Ω, φ.range = S ∧
      φ.ker ≤ (StatedScalars (Fin n) K).subgroupOf (StatedSL n K) :=
  exists_cover_statedSL hp hp2 hperf hcore hn
    (five_le_card_of_dvd hp hp2 hℓ hℓ2 hK (hdiag.trans (Nat.gcd_dvd_right _ _))) e

theorem card_le_of_caseL_lin (hp : p.Prime) (hp2 : p ≠ 2) (hperf : ⁅S, S⁆ = S)
    (hcore : GLAPPrimeCore p ↥S = ⊥) (hn : 3 ≤ n) {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) (hdiag : p ∣ Nat.gcd n (Nat.card K - 1))
    (e : PSimple p S ≃* StatedProj (StatedSL n K)) {B : Subgroup Ω} (hB : IsElemAbelian p B)
    (hBC : Nat.card ↥(B ⊓ centModSubgroup p S) = p) : Nat.card B ≤ p ^ (n + 1) := by
  obtain ⟨φ, hφS, hφk⟩ := caseL_setup_lin hp hp2 hperf hcore hn hℓ hℓ2 hK hdiag e
  have hcent : ∀ c ∈ (⊤ : Subgroup (GL (Fin n) K)),
      (∀ k ∈ StatedSL n K, c * k * c⁻¹ * k⁻¹ ∈ StatedScalars (Fin n) K) →
        c ∈ Subgroup.center (GL (Fin n) K) := fun _ _ hc => mem_center_of_conj_statedSL hn hc
  have hY : (⊤ : Subgroup (GL (Fin n) K)) ≤ Subgroup.normalizer (StatedSL n K : Set _) :=
    fun A _ => normalizer_statedSL A
  have hpK : p ∣ Nat.card Kˣ := by
    rw [Nat.card_units]
    exact hdiag.trans (Nat.gcd_dvd_right _ _)
  set B₁ := innerDiag φ ⊤ hY B with hB₁
  set ψ := innerDiagHom (hY := hY) (B := B) hcent hφk with hψ
  have hB₀ : Nat.card ↥(B ⊓ Subgroup.centralizer (S : Set Ω)) = p := by
    rw [← inf_centMod_eq_inf_centralizer inferInstance hcore, hBC]
  have hB₁el : IsElemAbelian p B₁ := ⟨⟨⟨fun a b => Subtype.ext (hB.comm (innerDiag_le a.2)
    (innerDiag_le b.2))⟩⟩, fun x hx => hB.2 x (innerDiag_le hx)⟩
  have hψc : Nat.card ψ.range ≤ p ^ (n - 1) :=
    card_le_of_pRank_le hp (pRank_pgl_le hp hp2 hpK (by omega)) ψ.range
      (isElemAbelian_range hB₁el ψ)
  have hB₁c : Nat.card B₁ ≤ p ^ n := by
    rw [hB₁, card_innerDiag hφS hcent hφk, hB₀]
    calc p * Nat.card ψ.range ≤ p * p ^ (n - 1) := Nat.mul_le_mul_left _ hψc
      _ = p ^ n := by rw [← pow_succ']; congr 1; omega
  rcases innerDiag_split_lin hp hp2 hn hℓ hf hK hφS hφk hB with h | ⟨b, hbB, hbB₁, hBb, hbinf⟩
  · rw [← h]
    exact hB₁c.trans (Nat.pow_le_pow_right hp.pos (Nat.le_succ n))
  · have hcomm : ∀ x ∈ B₁, ∀ y ∈ Subgroup.zpowers b, x * y = y * x := fun x hx y hy =>
      hB.comm (innerDiag_le hx) (Subgroup.zpowers_le.2 hbB hy)
    haveI : Fact p.Prime := ⟨hp⟩
    have hb1 : b ≠ 1 := fun h => hbB₁ (h ▸ one_mem _)
    have hzc : Nat.card (Subgroup.zpowers b) = p := by
      rw [Nat.card_zpowers, orderOf_eq_prime (hB.2 b hbB) hb1]
    rw [hBb, GL83.CompFam.card_sup_of_commute_of_inf_eq_bot hcomm (by rwa [inf_comm]), hzc,
      pow_succ]
    exact Nat.mul_le_mul_right _ hB₁c

private theorem torus_rank_lin (hp : p.Prime) (hpK : p ∣ Nat.card Kˣ) (h2K : (2 : K) ≠ 0)
    {m : ℕ} (hm : 1 ≤ m) {φ : ↥(StatedSL (m + 2) K) →* Ω} (hφS : φ.range = S)
    (hφZ : ((barMk S).comp φ).ker =
      (StatedScalars (Fin (m + 2)) K).subgroupOf (StatedSL (m + 2) K))
    (A : GL (Fin (m + 2)) K) {σ : K ≃+* K} (hσ : σ ^ p = 1) {B₂ : Subgroup Ω}
    (hB₂ : IsElemAbelian p B₂) {s : ℕ} (hB₂c : Nat.card B₂ = p ^ s)
    (hB₂S : B₂ ⊓ S ≤ Subgroup.centralizer (S : Set Ω))
    (hB₂fix : ∀ y ∈ B₂, ∀ k : ↥(StatedSL (m + 2) K),
      glFieldAut (Fin (m + 2)) K σ (A⁻¹ * k * A) = A⁻¹ * k * A → y * φ k = φ k * y) :
    m + s ≤ GLATwoLocalRank p Ω := by
  set c := MulAut.conj A with hc
  set X := (diagTorus m p K).map c.toMonoidHom with hX
  have hdet : ∀ d ∈ diagTorus m p K, d ∈ StatedSL (m + 2) K := fun d hd =>
    CFSG.Open.StatedAPI.mem_statedSL_of_det (diagTorus_le_det_one hd)
  have hcA : ∀ g : GL (Fin (m + 2)) K, c.toMonoidHom g = A * g * A⁻¹ := fun g => rfl
  have hfixd : ∀ d ∈ diagTorus m p K, glFieldAut (Fin (m + 2)) K σ d = d := fun d hd =>
    Units.ext (by rw [coe_glFieldAut]; exact diagTorus_map_eq hp hσ hd)
  have hfixt : glFieldAut (Fin (m + 2)) K σ (diagInvol m K) = diagInvol m K :=
    Units.ext (by rw [coe_glFieldAut]; exact diagInvol_map_eq m σ)
  have hXH : X ≤ StatedSL (m + 2) K := by
    rintro _ ⟨d, hd, rfl⟩
    rw [hcA]
    exact (Subgroup.mem_normalizer_iff.1 (normalizer_statedSL A) d).1 (hdet d hd)
  have hXel : IsElemAbelian p X := by
    have := isElemAbelian_range (isElemAbelian_diagTorus m p (L := K))
      (c.toMonoidHom.comp (diagTorus m p K).subtype)
    rwa [MonoidHom.range_comp, Subgroup.range_subtype] at this
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
  have htH : A * diagInvol m K * A⁻¹ ∈ StatedSL (m + 2) K :=
    (Subgroup.mem_normalizer_iff.1 (normalizer_statedSL A) _).1
      (CFSG.Open.StatedAPI.mem_statedSL_of_det (diagInvol_det m))
  have ht2 : (A * diagInvol m K * A⁻¹) ^ 2 = 1 := by
    rw [conj_pow, diagInvol_sq, mul_one, mul_inv_cancel]
  have htZ : A * diagInvol m K * A⁻¹ ∉ StatedScalars (Fin (m + 2)) K := by
    rw [CFSG.Open.StatedAPI.statedScalars_eq_center]
    exact fun h => diagInvol_not_mem m h2K hm (hcen _ h)
  have hXt : ∀ x ∈ X, x * (A * diagInvol m K * A⁻¹) = (A * diagInvol m K * A⁻¹) * x := by
    rintro _ ⟨d, hd, rfl⟩
    rw [hcA]
    calc A * d * A⁻¹ * (A * diagInvol m K * A⁻¹) = A * (d * diagInvol m K) * A⁻¹ := by group
      _ = A * (diagInvol m K * d) * A⁻¹ := by rw [diagTorus_comm_diagInvol hd]
      _ = A * diagInvol m K * A⁻¹ * (A * d * A⁻¹) := by group
  have h := le_glaTwoLocalRank_of_torus hp hφS hφZ hXH hXel hXZ hXc htH ht2 htZ hXt hB₂ hB₂c
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
  exact h

theorem exists_caseLData_lin (hp : p.Prime) (hp2 : p ≠ 2) (hperf : ⁅S, S⁆ = S)
    (hcore : GLAPPrimeCore p ↥S = ⊥) (hn : 4 ≤ n) {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) (hpℓ : p ≠ ℓ)
    (hdiag : p ∣ Nat.gcd n (Nat.card K - 1)) (e : PSimple p S ≃* StatedProj (StatedSL n K))
    {B : Subgroup Ω} (hB : IsElemAbelian p B) (hBC : Nat.card ↥(B ⊓ centModSubgroup p S) = p)
    (hrank : p ^ GLATwoLocalRank p Ω ≤ Nat.card B) :
    ∃ φ : ↥(StatedSL n K) →* Ω, φ.range = S ∧
      φ.ker ≤ (StatedScalars (Fin n) K).subgroupOf (StatedSL n K) ∧
      ∃ (B₁ : Subgroup Ω) (θ : ↥B₁ →* GL (Fin n) K),
        B₁ ≤ B ∧ B ⊓ Subgroup.centralizer (S : Set Ω) ≤ B₁ ∧
        θ.range ≤ Cls.isomGL (0 : (Fin n → K) →ₗ[K] (Fin n → K) →ₗ[K] K) ∧
        IsElemAbelian p θ.range ∧ θ.range ⊓ StatedScalars (Fin n) K = ⊥ ∧
        (∀ x : ↥B₁, θ x = 1 ↔ (x : Ω) ∈ Subgroup.centralizer (S : Set Ω)) ∧
        (∀ (x : ↥B₁) (k : ↥(StatedSL n K)), ∃ k' : ↥(StatedSL n K),
          (k' : GL (Fin n) K) = θ x * k * (θ x)⁻¹ ∧ φ k' = x * φ k * x⁻¹) ∧
        p ^ (n - 2) ≤ Nat.card θ.range ∧
        (B₁ = B ∨ ∃ b ∈ B, b ∉ B₁ ∧ B = B₁ ⊔ Subgroup.zpowers b ∧
          Subgroup.zpowers b ⊓ B₁ = ⊥ ∧
          ∃ (A : GL (Fin n) K) (σ : K ≃+* K), FieldAct p φ b A σ ∧
            FormRel (0 : (Fin n → K) →ₗ[K] (Fin n → K) →ₗ[K] K) A σ ∧
            ∀ x : ↥B₁, semiConj A σ (θ x) * (θ x)⁻¹ ∈ StatedScalars (Fin n) K) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hn3 : 3 ≤ n := by omega
  have hn5 : 5 ≤ n := by
    by_contra h
    have h4 : n = 4 := by omega
    have h1 : p ∣ 2 ^ 2 := by
      have := hdiag.trans (Nat.gcd_dvd_left _ _)
      rwa [h4] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h1))
  obtain ⟨φ, hφS, hφk⟩ := caseL_setup_lin hp hp2 hperf hcore hn3 hℓ hℓ2 hK hdiag e
  have hcent : ∀ c ∈ (⊤ : Subgroup (GL (Fin n) K)),
      (∀ k ∈ StatedSL n K, c * k * c⁻¹ * k⁻¹ ∈ StatedScalars (Fin n) K) →
        c ∈ Subgroup.center (GL (Fin n) K) := fun _ _ hc => mem_center_of_conj_statedSL hn3 hc
  have hY : (⊤ : Subgroup (GL (Fin n) K)) ≤ Subgroup.normalizer (StatedSL n K : Set _) :=
    fun A _ => normalizer_statedSL A
  have hpK : p ∣ Nat.card Kˣ := by
    rw [Nat.card_units]
    exact hdiag.trans (Nat.gcd_dvd_right _ _)
  have h2K : (2 : K) ≠ 0 := by
    haveI : CharP K ℓ :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hℓ hf hK
    intro h
    have := (CharP.cast_eq_zero_iff K ℓ 2).1 (by exact_mod_cast h)
    exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 this)
  set B₁ := innerDiag φ ⊤ hY B with hB₁
  set ψ := innerDiagHom (hY := hY) (B := B) hcent hφk with hψ
  have hB₀ : Nat.card ↥(B ⊓ Subgroup.centralizer (S : Set Ω)) = p := by
    rw [← inf_centMod_eq_inf_centralizer inferInstance hcore, hBC]
  have hB₁el : IsElemAbelian p B₁ := ⟨⟨⟨fun a b => Subtype.ext (hB.comm (innerDiag_le a.2)
    (innerDiag_le b.2))⟩⟩, fun x hx => hB.2 x (innerDiag_le hx)⟩
  have hψel := isElemAbelian_range hB₁el ψ
  have hB₁c : Nat.card B₁ = p * Nat.card ψ.range := by
    rw [hB₁, card_innerDiag hφS hcent hφk, hB₀]
  have hφZ := ker_barCover_statedSL hn3 hφS hφk
  have hB₀B₁ : B ⊓ Subgroup.centralizer (S : Set Ω) ≤ B₁ := inf_centralizer_le_innerDiag hφS
  have hsplit := innerDiag_split_lin hp hp2 hn3 hℓ hf hK hφS hφk hB
  have hfield : B₁ = B ∨ ∃ b ∈ B, b ∉ B₁ ∧ B = B₁ ⊔ Subgroup.zpowers b ∧
      Subgroup.zpowers b ⊓ B₁ = ⊥ ∧ ∃ (A : GL (Fin n) K) (σ : K ≃+* K), FieldAct p φ b A σ := by
    rcases hsplit with h | ⟨b, hbB, hbB₁, hBb, hbinf⟩
    · exact Or.inl h
    · refine Or.inr ⟨b, hbB, hbB₁, hBb, hbinf, ?_⟩
      have hbD : gammaSL hn3 hφS hφk b ∉ linearAutGroup n K := fun hD =>
        hbB₁ ((mem_innerDiag_iff_lin hn3 hφS hφk).2 ⟨hbB, hD⟩)
      exact exists_fieldAct_caseL_lin hp hp2 hn3 hℓ hf hK hpℓ hφS hφk (hB.2 b hbB) hbD
  have hψc : p ^ (n - 2) ≤ Nat.card ψ.range := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    rw [show m + 2 - 2 = m by omega]
    have hm : 1 ≤ m := by omega
    rcases hfield with h | ⟨b, hbB, hbB₁, hBb, hbinf, A, σ, hact⟩
    ·
      have hφH : ∀ k, φ k ∈ S := fun k => hφS ▸ ⟨k, rfl⟩
      have h1 := torus_rank_lin hp hpK h2K hm hφS hφZ 1 (σ := RingEquiv.refl K) (one_pow p)
        (isElemAbelian_mono' hB inf_le_left) (s := 1) (by rw [hB₀, pow_one])
        (fun x hx => hx.1.2)
        (fun y hy k _ => ((Subgroup.mem_centralizer_iff.1 hy.2) _ (hφH k)).symm)
      have h2 : p ^ (m + 1) ≤ Nat.card B :=
        (Nat.pow_le_pow_right hp.pos h1).trans hrank
      rw [← h, hB₁c, pow_succ, mul_comm] at h2
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
      have hb1 : b ≠ 1 := fun h => hbB₁ (h ▸ one_mem _)
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
          obtain ⟨h, hh⟩ : z * b ^ k ∈ φ.range := hφS ▸ hxS
          refine ⟨h, Subgroup.mem_top _, fun k₀ => ⟨conjOn (normalizer_statedSL h) k₀,
            coe_conjOn _ k₀, ?_⟩⟩
          have hk₀ : φ k₀ ∈ S := hφS ▸ ⟨k₀, rfl⟩
          have hzc : z * (b ^ k * φ k₀ * (b ^ k)⁻¹) = (b ^ k * φ k₀ * (b ^ k)⁻¹) * z :=
            ((Subgroup.mem_centralizer_iff.1 hz.2) _ ((inferInstance : S.Normal).conj_mem _ hk₀
              _)).symm
          have h1 : φ (conjOn (normalizer_statedSL h) k₀) = φ h * φ k₀ * (φ h)⁻¹ := by
            rw [← map_inv, ← map_mul, ← map_mul]
            congr 1
          rw [h1, hh]
          calc z * b ^ k * φ k₀ * (z * b ^ k)⁻¹ = z * (b ^ k * φ k₀ * (b ^ k)⁻¹) * z⁻¹ := by
                group
            _ = b ^ k * φ k₀ * (b ^ k)⁻¹ := by rw [hzc, mul_inv_cancel_right]
        have : b ^ k ∈ Subgroup.zpowers b ⊓ B₁ := ⟨Subgroup.pow_mem _ (Subgroup.mem_zpowers b) k,
          hbk⟩
        rw [hbinf, Subgroup.mem_bot] at this
        rw [this, mul_one]
        exact hz.2
      have h1 := torus_rank_lin hp hpK h2K hm hφS hφZ A hσ (isElemAbelian_mono' hB hB₂le)
        (s := 2) hB₂c hB₂S (fun y hy k hk => by
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
  obtain ⟨A', -, hA'el, hA'Z, hA'E⟩ := exists_elemAbelian_lift hp hp2 hpK hn5 hψel hψc
    (Y := ⊤) (innerDiagHom_range_le hcent hφk) (fun _ _ => Subgroup.mem_top _)
    (fun μ _ => ⟨μ, Subgroup.mem_top _, rfl⟩)
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
  refine ⟨φ, hφS, hφk, B₁, θ, innerDiag_le, hB₀B₁, by rw [Cls.isomGL_zero]; exact le_top,
    hθr ▸ hA'el, by rw [hθr, CFSG.Open.StatedAPI.statedScalars_eq_center]; exact hA'Z, hθ1,
    fun x k => hθact x k, by rw [hθr, hA'c]; exact hψc, ?_⟩
  rcases hfield with h | ⟨b, hbB, hbB₁, hBb, hbinf, A, σ, hact⟩
  · exact Or.inl h
  · refine Or.inr ⟨b, hbB, hbB₁, hBb, hbinf, A, σ, hact, ⟨1, fun u v => by simp⟩, fun x => ?_⟩
    rw [CFSG.Open.StatedAPI.statedScalars_eq_center]
    exact semiConj_mul_inv_mem_center hY hcent hφk hact (Subgroup.mem_top _)
      (Subgroup.mem_top _) (hθact x) (hB.comm hbB (innerDiag_le x.2))

end Main

end CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen

end
