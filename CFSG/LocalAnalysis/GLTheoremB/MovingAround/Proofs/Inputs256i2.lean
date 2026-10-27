module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs256i
import all CFSG.HardMathSupport.Solomon.Coordinator.LieComp.UnitaryInnerExport
import all CFSG.HardMathSupport.Solomon.Coordinator.LieComp.UnitaryFieldExport
import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderSmallReeDescent
import all CFSG.HardMathSupport.Solomon.Coordinator.LieComp.OrthInnerExport
import all CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs256f2
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55UDesc
import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.OrtHBlock
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs256j2

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256i

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple)

section Small

theorem not_dvd_two_pow_mul_three_pow {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (a b : ℕ) :
    ¬ p ∣ 2 ^ a * 3 ^ b := by
  intro h
  rcases (Nat.Prime.dvd_mul hp).1 h with h | h
  · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
  · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h))

theorem coprime_card_sl_small {E : Type} [Field E] [Finite E] {m : ℕ}
    (hm : m ≤ 1 ∨ (m = 2 ∧ Nat.card E ≤ 3)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    Nat.Coprime (Nat.card (Matrix.SpecialLinearGroup (Fin m) E)) p := by
  rcases hm with hm | ⟨rfl, hE⟩
  · have hsub : ∀ A : Matrix.SpecialLinearGroup (Fin m) E, A = 1 := by
      intro A
      ext i j
      have hm1 : m = 1 := by have := i.pos; omega
      subst hm1
      have hi : i = 0 := Subsingleton.elim i 0
      have hj : j = 0 := Subsingleton.elim j 0
      subst hi
      subst hj
      have h := A.2
      rw [Matrix.det_fin_one] at h
      simp [h]
    have hcard : Nat.card (Matrix.SpecialLinearGroup (Fin m) E) = 1 :=
      Nat.card_eq_one_iff_unique.2 ⟨⟨fun A B => (hsub A).trans (hsub B).symm⟩, ⟨1⟩⟩
    rw [hcard]
    exact Nat.coprime_one_left p
  · haveI := Fintype.ofFinite E
    have hdvd : Nat.card (Matrix.SpecialLinearGroup (Fin 2) E) ∣ Nat.card (GL (Fin 2) E) :=
      Subgroup.card_dvd_of_injective Matrix.SpecialLinearGroup.toGL Matrix.SpecialLinearGroup.toGL_injective
    rw [Matrix.card_GL_field, Fin.prod_univ_two] at hdvd
    have hc : Fintype.card E = 2 ∨ Fintype.card E = 3 := by
      have h1 : 1 < Nat.card E := Finite.one_lt_card
      rw [Nat.card_eq_fintype_card] at hE h1
      omega
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
    intro hpd
    have h := hpd.trans hdvd
    rcases hc with hc | hc
    · rw [hc] at h
      exact not_dvd_two_pow_mul_three_pow hp hp2 hp3 1 1 (by norm_num at h ⊢; exact h)
    · rw [hc] at h
      exact not_dvd_two_pow_mul_three_pow hp hp2 hp3 4 1 (by norm_num at h ⊢; exact h)

end Small

section Linear

open Polynomial Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification
open CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.CALinearPrimary
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

variable {k : Type} [Field k] [Finite k]

theorem mem_iSup_specialFactor_of_pow {q : ℕ} (hq : q.Prime) (hk : ringChar k = q) {n : ℕ} {A : GL (Fin n) k}
    (hsq : Squarefree (minpoly k (glA A : Module.End k (Fin n → k))))
    (g : ↥(fixSubgroup (CatalogueBHigherLinearAction.slConjugation n k A))) {j : ℕ} (hg : g ^ q ^ j = 1) :
    (g : SpecialLinearGroup (Fin n) k) ∈
      ⨆ b : primaryFactors (glA A : Module.End k (Fin n → k)), specialFactor A b := by
  classical
  have hdet : ∀ b : primaryFactors (glA A : Module.End k (Fin n → k)),
      LinearMap.det ((Inputs141c.blockPiHom hsq g b : blockGL (glA A : Module.End k (Fin n → k)) b) :
        Module.End (AdjoinRoot (b : k[X]))
          (primaryComponent (glA A : Module.End k (Fin n → k)) (b : k[X]))) = 1 := by
    intro b
    have : Fact (Irreducible (b : k[X])) := ⟨irreducible_of_mem_primaryFactors b.2⟩
    have : Finite (AdjoinRoot (b : k[X])) := Module.finite_of_finite k
    have hchar : ringChar (AdjoinRoot (b : k[X])) = q := by
      rw [← Algebra.ringChar_eq k (AdjoinRoot (b : k[X])), hk]
    have h1 : (Inputs141c.blockPiHom hsq g b) ^ (q ^ j) = 1 := by
      rw [← Pi.pow_apply, ← map_pow, hg, map_one, Pi.one_apply]
    have h2 : (Units.map (LinearMap.det : Module.End (AdjoinRoot (b : k[X]))
        (primaryComponent (glA A : Module.End k (Fin n → k)) (b : k[X])) →* AdjoinRoot (b : k[X]))
        (Inputs141c.blockPiHom hsq g b)) ^ q ^ j = 1 := by rw [← map_pow, h1, map_one]
    have h3 := Inputs256e.eq_one_of_coprime_card (Inputs256e.coprime_card_units hq hchar) h2
    exact congrArg Units.val h3
  set W : Subgroup (SpecialLinearGroup (Fin n) k) :=
    ⨆ b : primaryFactors (glA A : Module.End k (Fin n → k)), specialFactor A b
  have key : Inputs141c.blockPiHom hsq g ∈ (W.subgroupOf
      (fixSubgroup (CatalogueBHigherLinearAction.slConjugation n k A))).map (Inputs141c.blockPiHom hsq) := by
    refine Subgroup.pi_mem_of_mulSingle_mem _ fun b => ?_
    have hγ := Inputs141c.symm_mulSingle_mem_linearSpecialBlock' (x := glA A) hsq b
      (Inputs141c.blockPiHom hsq g b) (hdet b)
    obtain ⟨s, hs⟩ := mem_range_slGL (det_eq_one_of_mem_linearSpecialBlock hsq b.2 hγ)
    have hsmem : s ∈ specialFactor A b := by
      rw [specialFactor, Subgroup.mem_comap, hs]
      exact hγ
    have hsfix : s ∈ fixSubgroup (CatalogueBHigherLinearAction.slConjugation n k A) :=
      mem_fixSubgroup_slConjugation_iff.2 (by rw [hs]; exact hγ.1)
    have hθs : Inputs141c.blockPiHom hsq ⟨s, hsfix⟩ = Pi.mulSingle b (Inputs141c.blockPiHom hsq g b) := by
      rw [Inputs141c.blockPiHom_apply]
      exact (glCentralizerEquivPi hsq).eq_symm_apply.1 (Subtype.ext hs)
    rw [← hθs]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 (Subgroup.mem_iSup_of_mem b hsmem))
  obtain ⟨w, hw, hwg⟩ := key
  rw [← Inputs141c.blockPiHom_injective hsq hwg]
  exact Subgroup.mem_subgroupOf.1 hw

theorem qGenCoprime_conjAut_three (hk : ringChar k = 3) {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    {A : GL (Fin n) k} {c : kˣ} (hA : A ^ p = Matrix.GeneralLinearGroup.scalar (Fin n) c) :
    QGenCoprime 3 p (LinearFlag.conjAut n k A) := by
  have hpk : ((p : ℕ) : k) ≠ 0 := Inputs256e.natCast_ne_zero_of_ne Nat.prime_three hp hp3 hk
  have hsq := squarefree_minpoly_glA hpk hA
  obtain ⟨hker, hcop⟩ := Inputs256e.proj_ker_facts Nat.prime_three hk n
  refine qGenCoprime_of_centralQuotient (LinearFlag.proj n k) (LinearFlag.proj_surjective n k) hker hcop
    (CatalogueBHigherLinearAction.slConjugation n k A) (LinearFlag.conjAut n k A)
    (fun x => (LinearFlag.conjAut_proj A x).symm)
    (fun h : primaryFactors (glA A : Module.End k (Fin n → k)) => specialFactor A h)
    (fun h => specialFactor_le_fixSubgroup A _) (fun h c' hc g hg => conj_mem_specialFactor hc hg)
    (fun h => ?_) (fun x hx ⟨j, hj⟩ => mem_iSup_specialFactor_of_pow Nat.prime_three hk hsq ⟨x, hx⟩ (j := j)
      (Subtype.ext hj))
  have : Fact (Irreducible (h : k[X])) := ⟨irreducible_of_mem_primaryFactors h.2⟩
  have : Finite (AdjoinRoot (h : k[X])) := Module.finite_of_finite k
  have hchar : ringChar (AdjoinRoot (h : k[X])) = 3 := by
    rw [← Algebra.ringChar_eq k (AdjoinRoot (h : k[X])), hk]
  obtain ⟨e⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.nonempty_mulEquiv_specialFactor hsq h.2
  by_cases hgood : IsGoodFactor A h
  · left
    refine ⟨open_isQuasisimple (isQuasisimple_specialFactor hsq h.2 hgood), ?_⟩
    haveI : Fintype (AdjoinRoot (h : k[X])) := Fintype.ofFinite _
    have hm : 2 ≤ primaryMultiplicity (glA A : Module.End k (Fin n → k)) (h : k[X]) := by
      rcases hgood with h3 | ⟨h2, -⟩ <;> omega
    have h4 : primaryMultiplicity (glA A : Module.End k (Fin n → k)) (h : k[X]) = 2 →
        4 ≤ Fintype.card (AdjoinRoot (h : k[X])) := fun h2 => by
      rcases hgood with h3 | ⟨-, h4⟩
      · omega
      · rwa [← Nat.card_eq_fintype_card]
    have hX := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.slFactorFacts_holds _ _ hm h4
    have hchev := hX.chev
    rw [hchar] at hchev
    exact CFSG.HardMathSupport.Solomon.Coordinator.LieComp.isChevSimple_congr
      (QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)) hchev
  · right
    rw [← Nat.card_congr e.toEquiv]
    refine coprime_card_sl_small ?_ hp hp2 hp3
    unfold IsGoodFactor at hgood
    omega

theorem qGenCoprime_fieldAut_three (hk : ringChar k = 3) {n : ℕ} (hn : 2 ≤ n) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) (σ : k ≃+* k) : QGenCoprime 3 p (LinearFlag.fieldAut n k σ) := by
  set k₀ : Subfield k := (σ : k →+* k).eqLocusField (RingHom.id k) with hk₀def
  have hk₀ : ∀ x, x ∈ k₀ ↔ σ x = x := fun x => Iff.rfl
  set α := CatalogueBHigherLinearField.slFieldAut (Fin n) k σ with hα
  have hC := Inputs256e.fixSubgroup_slFieldAut_eq_range (n := n) hk₀
  let e : Matrix.SpecialLinearGroup (Fin n) k₀ ≃* ↥(fixSubgroup α) :=
    (MonoidHom.ofInjective (Inputs256e.injective_map_subtype_sl k₀)).trans (MulEquiv.subgroupCongr hC.symm)
  have hαβ : ∀ x, LinearFlag.proj n k (α x) = LinearFlag.fieldAut n k σ (LinearFlag.proj n k x) :=
    fun x => (LinearFlag.descendAut_proj n k α x).symm
  have hchar : ringChar k₀ = 3 := by rw [Algebra.ringChar_eq k₀ k, hk]
  obtain ⟨hker, hcop⟩ := Inputs256e.proj_ker_facts Nat.prime_three hk n
  refine qGenCoprime_of_centralQuotient (LinearFlag.proj n k) (LinearFlag.proj_surjective n k) hker hcop α
    (LinearFlag.fieldAut n k σ) hαβ (fun _ : Unit => fixSubgroup α) (fun _ => le_rfl)
    (fun _ c hc g hg => (fixSubgroup α).mul_mem ((fixSubgroup α).mul_mem hc hg) ((fixSubgroup α).inv_mem hc))
    (fun _ => ?_) (fun x hx _ => Subgroup.mem_iSup_of_mem () hx)
  by_cases hperf : 3 ≤ n ∨ 4 ≤ Nat.card k₀
  · left
    refine ⟨open_isQuasisimple (CFSG.LocalCores.isQuasisimple_of_mulEquiv e
      (CFSG.SeitzReduction.LinearPilot.isQuasisimple_specialLinearGroup_of_le hn hperf)), ?_⟩
    haveI : Fintype k₀ := Fintype.ofFinite k₀
    have hX := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.slFactorFacts_holds k₀ n hn (fun h2 => by
      rcases hperf with h3 | h4
      · omega
      · rwa [← Nat.card_eq_fintype_card])
    have hchev := hX.chev
    rw [hchar] at hchev
    exact CFSG.HardMathSupport.Solomon.Coordinator.LieComp.isChevSimple_congr
      (QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)) hchev
  · right
    rw [← Nat.card_congr e.toEquiv]
    exact coprime_card_sl_small (Or.inr ⟨by omega, by omega⟩) hp hp2 hp3

theorem qGenCoprime_projectiveSL_three_le (hk : ringChar k = 3) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hp3 : p ≠ 3) {n : ℕ} (hn : 3 ≤ n) (β : MulAut (LinearFlag.projectiveSL n k)) (hβ : β ^ p = 1) :
    QGenCoprime 3 p β := by
  haveI : CharP k 3 := hk ▸ ringChar.charP k
  obtain ⟨f, hf, hK⟩ := Inputs256e.exists_card_eq_pow Nat.prime_three hk
  have hdesc := CFSG.RankThree.LinearDescent.higher_linear_prime_semilinear_field_descent Nat.prime_three hf hn hK
  by_cases hlin : β ∈ LinearFlag.linearAutGroup n k
  · have hrange : LinearFlag.linearAutGroup n k = (LinearFlag.conjAut n k).range := by
      rw [LinearFlag.linearAutGroup, ← MonoidHom.coe_range, Subgroup.closure_eq]
    rw [hrange] at hlin
    obtain ⟨A, rfl⟩ := hlin
    have hAp : A ^ p ∈ (LinearFlag.conjAut n k).ker := by rw [MonoidHom.mem_ker, map_pow, hβ]
    rw [hdesc.1] at hAp
    obtain ⟨c, hc⟩ := hAp
    exact qGenCoprime_conjAut_three hk hp hp2 hp3 hc.symm
  · obtain ⟨A, σ, rfl⟩ := CFSG.GH74.GLS.Stage2.Bender.Thm1.Ln.exists_conj_field_of_odd hn
      (hp.odd_of_ne_two hp2) hβ
    have hmem : LinearFlag.conjAut n k A * LinearFlag.fieldAut n k σ ∈ LinearFlag.semilinearAutGroup n k :=
      mul_mem (LinearFlag.linearAutGroup_le_semilinearAutGroup (LinearFlag.conjAut_mem_linearAutGroup A))
        (Subgroup.subset_closure (Or.inr ⟨σ, rfl⟩))
    have hne : LinearFlag.conjAut n k A * LinearFlag.fieldAut n k σ ≠ 1 := fun h => hlin (h ▸ one_mem _)
    have : Fact p.Prime := ⟨hp⟩
    have hord : orderOf (LinearFlag.conjAut n k A * LinearFlag.fieldAut n k σ) = p := orderOf_eq_prime hβ hne
    obtain ⟨-, τ, -, ⟨h, -, hβτ⟩, -⟩ := hdesc.2.2.2.2.2.2.2 p hp hp3 _ hmem hlin hord
    rw [hβτ]
    exact qGenCoprime_conj h _ (qGenCoprime_fieldAut_three hk (by omega) hp hp2 hp3 τ)

theorem qGenCoprime_projectiveSL_two (hk : ringChar k = 3) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (β : MulAut (LinearFlag.projectiveSL 2 k)) (hβ : β ^ p = 1) : QGenCoprime 3 p β := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨β₀, hββ₀⟩ : ∃ β₀ : MulAut (CFSG.GorensteinWalter.PSL2 k), MulAut.congr (psl2Equiv k) β₀ = β :=
    ⟨(MulAut.congr (psl2Equiv k)).symm β, (MulAut.congr (psl2Equiv k)).apply_symm_apply β⟩
  have hβ₀p : β₀ ^ p = 1 :=
    (MulAut.congr (psl2Equiv k)).injective (by rw [map_pow, hββ₀, hβ, map_one])
  have hcongr : ∀ A : GL (Fin 2) k, MulAut.congr (psl2Equiv k)
      (CatalogueSchreierLinearTwo.pglAction k (Matrix.ProjGenLinGroup.mk A)) = LinearFlag.conjAut 2 k A :=
    fun A => congr_pglAction_mk A
  by_cases hD : β₀ ∈ (CatalogueSchreierLinearTwo.pglAction k).range
  · obtain ⟨g, hg⟩ := hD
    obtain ⟨A, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
    have hβA : β = LinearFlag.conjAut 2 k A := by
      rw [← hββ₀, ← hg]
      exact hcongr A
    have hAp : A ^ p ∈ Subgroup.center (GL (Fin 2) k) := by
      have h1 : CatalogueSchreierLinearTwo.pglAction k (Matrix.ProjGenLinGroup.mk (A ^ p)) =
          CatalogueSchreierLinearTwo.pglAction k 1 := by
        rw [map_pow, map_pow, hg, hβ₀p, map_one]
      exact Matrix.ProjGenLinGroup.mk_eq_one.1
        (CatalogueSchreierLinearTwo.pglAction_injective k h1)
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hAp
    obtain ⟨c, hc⟩ := hAp
    rw [hβA]
    exact qGenCoprime_conjAut_three hk hp hp2 hp3 hc.symm
  · have hne : β₀ ≠ 1 := fun h => hD ⟨1, by rw [map_one, h]⟩
    have hord : orderOf β₀ = p := orderOf_eq_prime hβ₀p hne
    obtain ⟨σ, -, g, hgσ⟩ :=
      CFSG.RankThree.PartTwo.KFacts.linear_two_prime_order_field_descent hp β₀ hord hD
    obtain ⟨A, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
    have hβ' : β = LinearFlag.conjAut 2 k A * LinearFlag.fieldAut 2 k σ *
        (LinearFlag.conjAut 2 k A)⁻¹ := by
      rw [← hββ₀, hgσ, map_mul, map_mul, map_inv, hcongr, congr_psl2FieldAut]
    rw [hβ']
    exact qGenCoprime_conj _ _ (qGenCoprime_fieldAut_three hk le_rfl hp hp2 hp3 σ)

theorem qGenCoprime_projectiveSL_three (hk : ringChar k = 3) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    {n : ℕ} (hn : 2 ≤ n) (β : MulAut (LinearFlag.projectiveSL n k)) (hβ : β ^ p = 1) : QGenCoprime 3 p β := by
  rcases Nat.lt_or_ge n 3 with h | h
  · obtain rfl : n = 2 := by omega
    exact qGenCoprime_projectiveSL_two hk hp hp2 hp3 β hβ
  · exact qGenCoprime_projectiveSL_three_le hk hp hp2 hp3 h β hβ

end Linear

section UnitaryAbstract

open Polynomial CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne

universe u

variable {ℓ f : ℕ} {K : Type} [Field K] {hK : UnitaryFieldData ℓ f K} {V : Type u}
  [AddCommGroup V] [Module K V] [FiniteDimensional K V] {B : V →ₛₗ[hK.bar] V →ₗ[K] K}
  {x : LinearMap.GeneralLinearGroup K V}

theorem specialBlock_le_sesqSpecialUnitaryGroup' (H : UnitaryPrimaryData hK.bar B x) (hq : 2 ≤ ℓ ^ f)
    (a : primaryFactors (x : Module.End K V)) :
    specialBlock B x (a : K[X]) ≤ sesqSpecialUnitaryGroup B := by
  intro g hg
  refine mem_sesqSpecialUnitaryGroup.mpr ⟨(specialBlock_le_unitaryCentralizer hg).1, ?_⟩
  by_cases hself : dualPoly hK.bar (a : K[X]) = a
  · obtain ⟨hE, Hf, hHf, hHfl, φ, hφ, hdetK⟩ := exists_selfDualFactor hself (selfDualPrimaryBlock H a hself)
    obtain ⟨hs, hgc, hdet⟩ := mem_specialBlock.1 hg
    have hcompat : ((φ ⟨g, hs⟩ : sesqUnitaryGroup Hf) : blockGL (x : Module.End K V) (a : K[X])) =
        blockRestrict x (a : K[X]) ⟨g, hgc⟩ :=
      blockGL_ext fun v hv => hφ ⟨g, hs⟩ v hv
    refine hdetK ⟨g, hs⟩ ?_
    rw [mem_sesqSpecialUnitaryGroup]
    refine ⟨(φ ⟨g, hs⟩).2, ?_⟩
    have h1 : blockGLDet (x : Module.End K V) (a : K[X])
        ((φ ⟨g, hs⟩ : sesqUnitaryGroup Hf) : blockGL (x : Module.End K V) (a : K[X])) = 1 := by
      rw [hcompat]
      exact hdet
    have := congrArg Units.val h1
    simpa [blockGLDet] using this
  · exact (specialBlockFacts_of_paired hq a (pairedPrimaryBlock H a (Ne.symm hself))).detK g hg

theorem mem_iSup_specialBlock_of_blocks_two (H : UnitaryPrimaryData hK.bar B x)
    {y : LinearMap.GeneralLinearGroup K V} (hy : y ∈ unitaryCentralizer B x)
    (hdet : ∀ b : primaryFactors (x : Module.End K V),
      blockDetHom x (b : K[X]) ⟨y, hy.2⟩ = 1)
    (hone : ∀ b : primaryFactors (x : Module.End K V), primaryMultiplicity (x : Module.End K V) (b : K[X]) ≤ 1 →
      blockRestrict x (b : K[X]) ⟨y, hy.2⟩ = 1) :
    y ∈ ⨆ a : {a : primaryFactors (x : Module.End K V) //
        2 ≤ primaryMultiplicity (x : Module.End K V) (a : K[X])},
      specialBlock B x (a.1 : K[X]) := by
  classical
  have hsq := H.squarefree
  set M := ⨆ a : {a : primaryFactors (x : Module.End K V) //
      2 ≤ primaryMultiplicity (x : Module.End K V) (a : K[X])}, specialBlock B x (a.1 : K[X]) with hM
  suffices key : ∀ F : Finset K[X], ∀ (y : LinearMap.GeneralLinearGroup K V)
      (hy : y ∈ unitaryCentralizer B x),
      (∀ b : primaryFactors (x : Module.End K V), blockDetHom x (b : K[X]) ⟨y, hy.2⟩ = 1) →
      (∀ b : primaryFactors (x : Module.End K V), primaryMultiplicity (x : Module.End K V) (b : K[X]) ≤ 1 →
        blockRestrict x (b : K[X]) ⟨y, hy.2⟩ = 1) →
      (∀ b ∈ primaryFactors (x : Module.End K V), b ∉ F →
        ∀ v ∈ primaryComponent (x : Module.End K V) b, (y : Module.End K V) v = v) → y ∈ M by
    exact key (primaryFactors (x : Module.End K V)) y hy hdet hone fun b hb hbn => absurd hb hbn
  intro F
  induction F using Finset.induction_on with
  | empty =>
    intro y hy _ _ h
    have : y = 1 := eq_one_of_forall_apply_eq hsq fun b hb v hv => h b hb (by simp) v hv
    rw [this]
    exact M.one_mem
  | insert b F hbF ih =>
    intro y hy hdet hone h
    by_cases hbΦ : b ∈ primaryFactors (x : Module.End K V)
    · set O : Set K[X] := {b, dualPoly hK.bar b} with hOdef
      have hbO : b ∈ O := Or.inl rfl
      have hO : ∀ c ∈ primaryFactors (x : Module.End K V), c ∈ O → dualPoly hK.bar c ∈ O := by
        intro c hc hcO
        rcases hcO with rfl | hcO
        · exact Or.inr rfl
        · rw [Set.mem_singleton_iff] at hcO
          subst hcO
          exact Or.inl (dualPoly_dualPoly_of_mem H hbΦ)
      obtain ⟨gO, hgO, hgOeq⟩ := exists_component H hO hy
      have hgOc : gO ∈ gl_centralizer x := hgO.1.2
      have hres : ∀ c : primaryFactors (x : Module.End K V), (c : K[X]) ∈ O →
          blockRestrict x (c : K[X]) ⟨gO, hgOc⟩ = blockRestrict x (c : K[X]) ⟨y, hy.2⟩ :=
        fun c hc => blockGL_ext fun v hv => hgOeq c c.2 hc v hv
      have hres1 : ∀ c : primaryFactors (x : Module.End K V), (c : K[X]) ∉ O →
          blockRestrict x (c : K[X]) ⟨gO, hgOc⟩ = 1 :=
        fun c hc => blockGL_ext fun v hv => hgO.2 c c.2 hc v hv
      have hdetO : ∀ c : primaryFactors (x : Module.End K V),
          blockDetHom x (c : K[X]) ⟨gO, hgOc⟩ = 1 := by
        intro c
        by_cases hc : (c : K[X]) ∈ O
        · have : blockDetHom x (c : K[X]) ⟨gO, hgOc⟩ = blockDetHom x (c : K[X]) ⟨y, hy.2⟩ := by
            simp only [blockDetHom, MonoidHom.comp_apply]
            rw [hres c hc]
          rw [this]
          exact hdet c
        · simp only [blockDetHom, MonoidHom.comp_apply]
          rw [hres1 c hc, map_one]
      have honeO : ∀ c : primaryFactors (x : Module.End K V),
          primaryMultiplicity (x : Module.End K V) (c : K[X]) ≤ 1 →
          blockRestrict x (c : K[X]) ⟨gO, hgOc⟩ = 1 := by
        intro c hcb
        by_cases hc : (c : K[X]) ∈ O
        · rw [hres c hc]
          exact hone c hcb
        · exact hres1 c hc
      have hgOM : gO ∈ M := by
        by_cases hgood : 2 ≤ primaryMultiplicity (x : Module.End K V) b
        · refine Subgroup.mem_iSup_of_mem
            (⟨⟨b, hbΦ⟩, hgood⟩ : {a : primaryFactors (x : Module.End K V) //
              2 ≤ primaryMultiplicity (x : Module.End K V) (a : K[X])})
            (mem_specialBlock.mpr ⟨hgO, hgOc, hdetO ⟨b, hbΦ⟩⟩)
        · have h1 : gO = 1 := by
            refine eq_one_of_paired H hbΦ hgO fun v hv => ?_
            have := congrArg (fun γ : blockGL (x : Module.End K V) b => blockApply γ v hv)
              (honeO ⟨b, hbΦ⟩ (by simp only; omega))
            exact this
          rw [h1]
          exact M.one_mem
      have hy' : gO⁻¹ * y ∈ unitaryCentralizer B x := mul_mem (inv_mem hgO.1) hy
      have hdet' : ∀ c : primaryFactors (x : Module.End K V),
          blockDetHom x (c : K[X]) ⟨gO⁻¹ * y, hy'.2⟩ = 1 := by
        intro c
        have : (⟨gO⁻¹ * y, hy'.2⟩ : gl_centralizer x) = ⟨gO, hgOc⟩⁻¹ * ⟨y, hy.2⟩ := rfl
        rw [this, map_mul, map_inv, hdetO c, hdet c, inv_one, mul_one]
      have hone' : ∀ c : primaryFactors (x : Module.End K V),
          primaryMultiplicity (x : Module.End K V) (c : K[X]) ≤ 1 →
          blockRestrict x (c : K[X]) ⟨gO⁻¹ * y, hy'.2⟩ = 1 := by
        intro c hcb
        have : (⟨gO⁻¹ * y, hy'.2⟩ : gl_centralizer x) = ⟨gO, hgOc⟩⁻¹ * ⟨y, hy.2⟩ := rfl
        rw [this, map_mul, map_inv, honeO c hcb, hone c hcb, inv_one, mul_one]
      have hinv : ∀ u, ((gO⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V)
          ((gO : Module.End K V) u) = u := fun u => by
        rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel]
        rfl
      have h' : ∀ c ∈ primaryFactors (x : Module.End K V), c ∉ F →
          ∀ v ∈ primaryComponent (x : Module.End K V) c,
          ((gO⁻¹ * y : LinearMap.GeneralLinearGroup K V) : Module.End K V) v = v := by
        intro c hc hcF v hv
        by_cases hcO : c ∈ O
        · rw [Units.val_mul, Module.End.mul_apply, ← hgOeq c hc hcO v hv, hinv]
        · have hgo : (gO : Module.End K V) v = v := hgO.2 c hc hcO v hv
          have hcb : c ∉ insert b F := by
            simp only [Finset.mem_insert, not_or]
            exact ⟨fun h => hcO (h ▸ hbO), hcF⟩
          rw [Units.val_mul, Module.End.mul_apply, h c hc hcb v hv, ← hgo, hinv, hgo]
      have hrest := ih _ hy' hdet' hone' h'
      have hg_eq : y = gO * (gO⁻¹ * y) := by simp
      rw [hg_eq]
      exact M.mul_mem hgOM hrest
    · refine ih y hy hdet hone fun c hc hcF v hv => h c hc ?_ v hv
      simp only [Finset.mem_insert, not_or]
      exact ⟨fun h => hbΦ (h ▸ hc), hcF⟩

end UnitaryAbstract

section UnitaryConcrete

open Polynomial CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple (open_isQuasisimple)

variable {f : ℕ} {K : Type} [Field K]

theorem coprime_card_normOneScalars_unitary {ℓ n : ℕ} (h : UnitaryFieldData ℓ f K) :
    Nat.Coprime (Nat.card ↥(normOneScalars h (gramSU h (idGram K n)) n)) ℓ := by
  haveI := h.finite
  have hℓ : ℓ.Prime := h.prime
  haveI : CharP K ℓ := h.charP
  refine Inputs256e.coprime_card_of_pow_eq_one hℓ (Inputs256e.coprime_card_units hℓ (ringChar.eq K ℓ))
    fun z hz => ?_
  obtain ⟨c, -, -, hc⟩ := mem_normOneScalars.1 hz
  apply Subtype.ext
  rw [SubgroupClass.coe_pow, hc, ← map_pow, pow_card_eq_one', map_one, OneMemClass.coe_one]

theorem qGenCoprime_primeFormConjHom_three {ℓ n : ℕ} (h : UnitaryFieldData ℓ f K) (hℓ3 : ℓ = 3) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (A : primeFormUnitary h (idGram K n)) {c : Kˣ}
    (hA : (A : GL (Fin n) K) ^ p = Matrix.GeneralLinearGroup.scalar (Fin n) c) :
    QGenCoprime 3 p (primeFormConjHom h (idGram K n) A) := by
  classical
  subst hℓ3
  haveI := h.finite
  have hℓ : (3 : ℕ).Prime := h.prime
  haveI : CharP K 3 := h.charP
  have hq : 2 ≤ 3 ^ f := by
    have := Nat.one_lt_pow (by have := h.one_le; omega : f ≠ 0) hℓ.one_lt
    omega
  set x : LinearMap.GeneralLinearGroup K (Fin n → K) := Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K)
    with hx
  have H : UnitaryPrimaryData h.bar (idForm h n) x := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.primaryData_toLin' h A.2 hp hp3 hA
  set α : MulAut ↥(gramSU h (idGram K n)) := primeFormConjSU h (idGram K n) A with hα
  set β : MulAut (primeFormP h (idGram K n)) := primeFormConjHom h (idGram K n) A with hβ
  set π : ↥(gramSU h (idGram K n)) →* primeFormP h (idGram K n) :=
    QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker ≤ Subgroup.center ↥(gramSU h (idGram K n)) := by
    rw [hπ, QuotientGroup.ker_mk']
    exact normOneScalars_le_center h _ n
  have hcop : Nat.Coprime (Nat.card π.ker) 3 := by
    rw [hπ, QuotientGroup.ker_mk']
    exact coprime_card_normOneScalars_unitary h
  have hαβ : ∀ g, π (α g) = β (π g) := fun g => (primeFormConjHom_mk h (idGram K n) A g).symm
  have hSBle : ∀ a : {a : primaryFactors (x : Module.End K (Fin n → K)) //
      2 ≤ primaryMultiplicity (x : Module.End K (Fin n → K)) (a : K[X])},
      specialBlock (idForm h n) x (a.1 : K[X]) ≤ (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.toLinSU h n).range := fun a g hg =>
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.mem_range_toLinSU (specialBlock_le_sesqSpecialUnitaryGroup' H hq a.1 hg)
  let F : {a : primaryFactors (x : Module.End K (Fin n → K)) //
      2 ≤ primaryMultiplicity (x : Module.End K (Fin n → K)) (a : K[X])} →
      Subgroup ↥(gramSU h (idGram K n)) :=
    fun a => (specialBlock (idForm h n) x (a.1 : K[X])).comap (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.toLinSU h n)
  have hFmap : ∀ a, (F a).map (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.toLinSU h n) = specialBlock (idForm h n) x (a.1 : K[X]) :=
    fun a => Subgroup.map_comap_eq_self (hSBle a)
  have hFα : ∀ a, F a ≤ fixSubgroup α := fun a g hg =>
    (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.mem_fixSubgroup_primeFormConjSU_iff A hx g).mpr
      (specialBlock_le_unitaryCentralizer (Subgroup.mem_comap.mp hg)).2
  have hFn : ∀ a, ∀ c' ∈ fixSubgroup α, ∀ g ∈ F a, c' * g * c'⁻¹ ∈ F a := by
    intro a c' hc g hg
    have hcU := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.toLinSU_mem_unitaryCentralizer A hx hc
    have := conj_mem_specialBlock hcU (Subgroup.mem_comap.mp hg)
    rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
    exact this
  have eF : ∀ a, ↥(F a) ≃* ↥(specialBlock (idForm h n) x (a.1 : K[X])) := fun a =>
    (Subgroup.equivMapOfInjective (F a) (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.toLinSU h n) CFSG.HardMathSupport.Solomon.Coordinator.LieComp.toLinSU_injective).trans
      (MulEquiv.subgroupCongr (hFmap a))
  have hNC : (fixSubgroup α).map π ≤ fixSubgroup β :=
    CFSG.HardMathSupport.Solomon.Coordinator.map_fixSubgroup_le π hker α β hαβ
  have hNn : (((fixSubgroup α).map π).subgroupOf (fixSubgroup β)).Normal :=
    CFSG.HardMathSupport.Solomon.Coordinator.normal_map_fixSubgroup π hker α β hαβ hπs
  have hFtype : ∀ a, (CFSG.Open.IsQuasisimple (F a) ∧ IsChevSimple 3 (F a ⧸ Subgroup.center (F a))) ∨
      Nat.Coprime (Nat.card (F a)) p := by
    intro a
    by_cases hgood : IsGoodBlock h x a.1
    · left
      have hFq : CFSG.Open.IsQuasisimple (F a) :=
        open_isQuasisimple (CFSG.LocalCores.isQuasisimple_of_mulEquiv (eF a).symm
          ((specialBlockFacts_of_good H hq a.1 hgood).quasisimple a.2))
      refine ⟨hFq, ?_⟩
      obtain ⟨hqa, ⟨e2⟩⟩ := Inputs256e.centralImage_facts π hker hFq
      have hcomp : CFSG.Open.IsComponentOf ((F a).map π) (fixSubgroup β) :=
        ⟨(Subgroup.map_mono (hFα a)).trans hNC,
          IsSubnormal.step (Subgroup.map_mono (hFα a)) (Inputs256e.normal_map_subgroupOf_map π (hFn a))
            (IsSubnormal.step hNC hNn (IsSubnormal.refl _)), hqa⟩
      obtain ⟨Y, _, _, hY, -, g, hg, hgk⟩ :=
        CFSG.HardMathSupport.Solomon.Coordinator.LieComp.exists_lieFactor_of_component_primeFormConjHom
          CFSG.HardMathSupport.Solomon.Coordinator.LieComp.slFactorFacts_holds
          CFSG.HardMathSupport.Solomon.Coordinator.LieComp.suFactorFacts_holds hp hp3 A hA _ hcomp
      obtain ⟨e1⟩ :=
        CFSG.HardMathSupport.Solomon.Coordinator.LieComp.nonempty_centralQuotient_mulEquiv hY.perfect g hg hgk
      exact CFSG.HardMathSupport.Solomon.Coordinator.LieComp.isChevSimple_congr (e1.trans e2.symm) hY.chev
    · right
      have hself : dualPoly h.bar (a.1 : K[X]) = a.1 := by
        by_contra hne
        exact hgood ⟨a.2, fun h' => absurd h' hne⟩
      have hbad : (primaryMultiplicity (x : Module.End K (Fin n → K)) (a.1 : K[X]),
          3 ^ (f * (a.1 : K[X]).natDegree)) ∈ ({(2, 2), (2, 3), (3, 2)} : Set (ℕ × ℕ)) := by
        by_contra hnot
        exact hgood ⟨a.2, fun _ => hnot⟩
      have hp5 : 3 < p := by
        have := hp.two_le
        omega
      have hndvd := not_dvd_card_orbitFactor_exceptional H hp hp5 a.1 hself hbad
      have hdvd : Nat.card (specialBlock (idForm h n) x (a.1 : K[X])) ∣
          Nat.card (orbitFactor (idForm h n) x (a.1 : K[X])) :=
        Subgroup.card_dvd_of_le fun g hg => (mem_specialBlock.1 hg).1
      rw [Nat.card_congr (eF a).toEquiv, Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
      exact fun hpd => hndvd (hpd.trans hdvd)
  have hgen : ∀ g ∈ fixSubgroup α, (∃ j : ℕ, g ^ 3 ^ j = 1) → g ∈ ⨆ a, F a := by
    rintro g hg ⟨j, hj⟩
    have hy := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.toLinSU_mem_unitaryCentralizer A hx hg
    have hyj : (⟨CFSG.HardMathSupport.Solomon.Coordinator.LieComp.toLinSU h n g, hy.2⟩ : gl_centralizer x) ^ 3 ^ j = 1 := by
      apply Subtype.ext
      rw [SubgroupClass.coe_pow, ← map_pow, hj, map_one, OneMemClass.coe_one]
    have hdet : ∀ b : primaryFactors (x : Module.End K (Fin n → K)),
        blockDetHom x (b : K[X]) ⟨CFSG.HardMathSupport.Solomon.Coordinator.LieComp.toLinSU h n g, hy.2⟩ = 1 := by
      intro b
      have : Fact (Irreducible (b : K[X])) := ⟨irreducible_of_mem_primaryFactors b.2⟩
      have : Finite (AdjoinRoot (b : K[X])) := Module.finite_of_finite K
      have hchar : ringChar (AdjoinRoot (b : K[X])) = 3 :=
        (Algebra.ringChar_eq K (AdjoinRoot (b : K[X]))).symm.trans (ringChar.eq K 3)
      refine Inputs256e.eq_one_of_coprime_card (Inputs256e.coprime_card_units hℓ hchar) (n := j) ?_
      rw [← map_pow, hyj, map_one]
    have hone : ∀ b : primaryFactors (x : Module.End K (Fin n → K)),
        primaryMultiplicity (x : Module.End K (Fin n → K)) (b : K[X]) ≤ 1 →
        blockRestrict x (b : K[X]) ⟨CFSG.HardMathSupport.Solomon.Coordinator.LieComp.toLinSU h n g, hy.2⟩ = 1 := by
      intro b hle
      have : Fact (Irreducible (b : K[X])) := ⟨irreducible_of_mem_primaryFactors b.2⟩
      have : Finite (AdjoinRoot (b : K[X])) := Module.finite_of_finite K
      have hchar : ringChar (AdjoinRoot (b : K[X])) = 3 :=
        (Algebra.ringChar_eq K (AdjoinRoot (b : K[X]))).symm.trans (ringChar.eq K 3)
      haveI : Finite (blockGL (x : Module.End K (Fin n → K)) (b : K[X])) :=
        Nat.finite_of_card_ne_zero (Nat.pos_of_ne_zero (fun h0 => by
          have := Inputs256e.coprime_card_gl_of_finrank_le_one (W := primaryComponent (x :
            Module.End K (Fin n → K)) (b : K[X])) hℓ hchar hle
          rw [blockGL] at h0
          rw [h0] at this
          exact hℓ.one_lt.ne' (Nat.coprime_zero_left _ |>.1 this))).ne'
      refine Inputs256e.eq_one_of_coprime_card
        (Inputs256e.coprime_card_gl_of_finrank_le_one hℓ hchar hle) (n := j) ?_
      rw [← map_pow, hyj, map_one]
    have hmem := mem_iSup_specialBlock_of_blocks_two H hy hdet hone
    have hmapsup : (⨆ a, F a).map (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.toLinSU h n) =
        ⨆ a : {a : primaryFactors (x : Module.End K (Fin n → K)) //
          2 ≤ primaryMultiplicity (x : Module.End K (Fin n → K)) (a : K[X])},
          specialBlock (idForm h n) x (a.1 : K[X]) := by
      rw [Subgroup.map_iSup]
      exact iSup_congr hFmap
    have hk : CFSG.HardMathSupport.Solomon.Coordinator.LieComp.toLinSU h n g ∈ (⨆ a, F a).map (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.toLinSU h n) := by
      rw [hmapsup]
      exact hmem
    obtain ⟨s, hs, hs'⟩ := hk
    have : s = g := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.toLinSU_injective hs'
    rw [← this]
    exact hs
  exact qGenCoprime_of_centralQuotient π hπs hker hcop α β hαβ F hFα hFn hFtype hgen

open CFSG.LieType.Chevalley (fixSubfield)

theorem qGen_primeFormFieldHom_three {ℓ n : ℕ} (h : UnitaryFieldData ℓ f K) (hℓ3 : ℓ = 3) (hn : 3 ≤ n)
    (hC : IsPrimeFormGram (1 : GL (Fin n) K)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {σ : K ≃+* K} (hσ : orderOf σ = p) : Inputs256e.QGen 3 (primeFormFieldHom h hC σ) := by
  subst hℓ3
  haveI := h.finite
  have hℓ : (3 : ℕ).Prime := h.prime
  have h₀ : UnitaryFieldData 3 (f / p) (fixSubfield σ) :=
    CFSG.RankThree.Classical.fixSubfield_unitaryFieldData h hp hp2 hσ
  have hbar := CFSG.RankThree.Classical.fixSubfield_unitaryFieldData_bar h hp hp2 hσ
  obtain ⟨e⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.nonempty_statedSU_mulEquiv_fixSubgroup h h₀ hbar hC
  set α : MulAut ↥(gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := primeFormFieldSU h hC σ
    with hα
  let π : ↥(gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) →*
      primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    QuotientGroup.mk' (normOneScalars h (gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) n)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker ≤ Subgroup.center ↥(gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
    rw [QuotientGroup.ker_mk']
    exact normOneScalars_le_center h _ n
  have hcop : Nat.Coprime (Nat.card π.ker) 3 := by
    rw [QuotientGroup.ker_mk']
    exact coprime_card_normOneScalars_unitary h
  have hαβ : ∀ x, π (α x) = primeFormFieldHom h hC σ (π x) := fun x =>
    (primeFormFieldAut_mk h hC σ x).symm
  have hne : ¬ (n = 3 ∧ 3 ^ (f / p) = 2) := fun ⟨_, h2⟩ => by
    have : 3 ≤ 3 ^ (f / p) := Nat.le_self_pow (by have := h₀.one_le; omega) 3
    omega
  haveI : Fact (3 : ℕ).Prime := ⟨hℓ⟩
  have hcard : Nat.card (fixSubfield σ) = (3 ^ (f / p)) ^ 2 := by
    rw [h₀.card, ← pow_mul, mul_comm]
  have hqs : CFSG.IsQuasisimple ↥(fixSubgroup α) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e
      (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hcard hn
        (fun heq => hne ⟨(Prod.mk.inj heq).1, (Prod.mk.inj heq).2⟩)).1
  have hLF := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.unitary_fixSubfield_lieFactorData
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.suFactorFacts_holds h hn hp hp2 hσ hne
  have e₂ : (↥(CFSG.Open.StatedSU n (3 ^ (f / p)) (fixSubfield σ)) ⧸
      Subgroup.center ↥(CFSG.Open.StatedSU n (3 ^ (f / p)) (fixSubfield σ))) ≃*
      (↥(fixSubgroup α) ⧸ Subgroup.center ↥(fixSubgroup α)) :=
    QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)
  have hchev : IsChevSimple 3 (↥(fixSubgroup α) ⧸ Subgroup.center ↥(fixSubgroup α)) :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.isChevSimple_congr e₂ hLF.chev
  exact Inputs256e.qGen_of_centralQuotient π hπ hker hcop α _ hαβ (fun _ : Unit => fixSubgroup α)
    (fun _ => le_rfl)
    (fun _ c hc g hg => (fixSubgroup α).mul_mem ((fixSubgroup α).mul_mem hc hg) ((fixSubgroup α).inv_mem hc))
    (fun _ => open_isQuasisimple hqs) (fun _ => hchev) (fun x hx _ => Subgroup.mem_iSup_of_mem () hx)

end UnitaryConcrete

section Ree

open CFSG.LieType.Ree CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.Walter.Ward CFSG.Walter.WardLocal

theorem qGenCoprime_of_fixSubgroup {S : Type} [Group S] {q p : ℕ} {β : MulAut S}
    (h : IsChevSubOrCoprime q p β (fixSubgroup β)) : QGenCoprime q p β := fun s hs _ =>
  le_iSup₂_of_le (f := fun (J : Subgroup S) (_ : IsChevSubOrCoprime q p β J) => J) _ h le_rfl
    (mem_fixSubgroup.2 hs)

theorem qGenCoprime_of_coprime_card {S : Type} [Group S] [Finite S] {q p : ℕ} {β : MulAut S}
    (h : Nat.Coprime (Nat.card (fixSubgroup β)) q) : QGenCoprime q p β := by
  intro s hs ⟨n, hn⟩
  have h1 : (⟨s, mem_fixSubgroup.2 hs⟩ : fixSubgroup β) = 1 :=
    Inputs256e.eq_one_of_coprime_card h (n := n) (Subtype.ext (by simpa using hn))
  have h2 : s = 1 := congrArg Subtype.val h1
  rw [h2]
  exact Subgroup.one_mem _

theorem coprime_1512 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hp7 : p ≠ 7) : Nat.Coprime 1512 p := by
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
  intro h
  have h' : p ∣ (2 ^ 3 * 3 ^ 3) * 7 := by norm_num; exact h
  rcases (Nat.Prime.dvd_mul hp).1 h' with h1 | h1
  · exact not_dvd_two_pow_mul_three_pow hp hp2 hp3 3 3 h1
  · exact hp7 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h1)


theorem not_three_dvd_card_centralizer_reeType {G : Type} [Group G] [Finite G]
    (h : ReeTypeHyp G) {x : G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hx : orderOf x = p) : ¬ 3 ∣ Nat.card (Subgroup.centralizer ({x} : Set G)) := by
  classical
  intro h3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨⟨k, hk, hq⟩, hG⟩ := ward_order h
  letI : Fintype G := Fintype.ofFinite G
  haveI : CharP h.F 3 := ree_charP_three h hq
  obtain ⟨S, D, B, -⟩ := exists_data h hq hG
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(Subgroup.centralizer ({x} : Set G))) 3 h3
  have hyx : (y : G) * x = x * (y : G) := Subgroup.mem_centralizer_singleton_iff.mp y.2
  have hcomm : Commute x (y : G) := hyx.symm
  have hy3 : orderOf (y : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hy
  have hcop : (orderOf x).Coprime (orderOf (y : G)) := by
    rw [hx, hy3]
    exact (Nat.coprime_primes hp Nat.prime_three).mpr hp3
  have hxy : orderOf (x * (y : G)) = p * 3 := by
    rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hcop, hx, hy3]
  have hodd : Odd (orderOf (x * (y : G))) := by
    rw [hxy]
    exact (hp.odd_of_ne_two hp2).mul (by decide)
  have h3' : 3 ∣ orderOf (x * (y : G)) := by rw [hxy]; exact dvd_mul_left 3 p
  have hdvd := B.card_centralizer_dvd hq hG hodd h3'
  have hxmem : x ∈ Subgroup.centralizer ({x * (y : G)} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc x * (x * (y : G)) = x * ((y : G) * x) := by rw [hyx]
      _ = x * (y : G) * x := (mul_assoc _ _ _).symm
  have hpdvd : p ∣ Nat.card (Subgroup.centralizer ({x * (y : G)} : Set G)) := by
    rw [← hx, ← Subgroup.orderOf_mk x hxmem]
    exact orderOf_dvd_natCard _
  rcases (Nat.Prime.dvd_mul hp).mp (hpdvd.trans hdvd) with h2 | h2
  · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
  · have h3q : p ∣ 3 := by
      have := hp.dvd_of_dvd_pow h2
      rw [hq] at this
      exact hp.dvd_of_dvd_pow this
    exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3q)


theorem qGen3Ree_holds : QGen3Ree := by
  rintro ⟨d, hv⟩ hd3 p hp hp2 hp3 ⟨⟨m, hdm⟩, hexcl⟩ β hβ
  change d = .reeG2 m at hdm
  subst hdm
  have hm7 : ¬ (m = 3 ∧ p = 7) := fun ⟨h1, h2⟩ =>
    hexcl ⟨show TauCeti.LieTypeIndex.reeG2 m = .reeG2 3 from by rw [h1], h2⟩
  have hm1 : 1 ≤ m := by
    have h := ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    simpa [TauCeti.LieTypeIndex.inStandardRange_iff] using h
  have hT : CFSG.Blueprint.ReeTitsModel (CFSG.LieType.SeitzGeneration.Cat ⟨.reeG2 m, hv⟩) .twistedG2 3
      (2 * m + 1) :=
    CFSG.RankThree.PartOne.CTP.reeTitsModel_reeG2 m ⟨hv, ⟨MulEquiv.refl _⟩⟩
  obtain ⟨-, -, -, -, hiso⟩ := CFSG.LieType.Ree.small_Ree_model_Schreier _ 3 (2 * m + 1) hT
  obtain ⟨-, a', hfa', K, _, _, hK, ⟨e₀⟩⟩ := hT
  have ha' : a' = m := by omega
  subst ha'
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K ReeTag.G2.prime := charP_of_card_eq_prime_pow (f := 2 * a' + 1) (by
    rw [← Nat.card_eq_fintype_card, hK]
    rfl)
  obtain ⟨e⟩ := hiso a' K hfa' hK ⟨e₀⟩
  have hK' : Nat.card K = 3 ^ (2 * a' + 1) := hK
  have : Finite (ModGL ReeTag.G2.tag K) := finite_modGL
  refine qGenCoprime_of_congr e β ?_
  set β' : MulAut (ReeTag.G2.reeGamma K a') := MulAut.congr e β with hβ'def
  have hβ'o : orderOf β' = p :=
    (orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective β).trans hβ
  have hβ'p : β' ^ p = 1 := by rw [← hβ'o]; exact pow_orderOf_eq_one β'
  have hβ'1 : β' ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at hβ'o
    exact hp.one_lt.ne hβ'o
  obtain ⟨-, hsimple, hnc⟩ := CFSG.ComponentClassification.CatalogueBSmallRee.reeGamma_G2_simple hm1 K hK'
  haveI := hsimple
  by_cases hin : β' ∈ (MulAut.conj : ReeTag.G2.reeGamma K a' →* MulAut (ReeTag.G2.reeGamma K a')).range
  ·
    obtain ⟨x, hxβ, hxp, hx1⟩ := CFSG.HardMathSupport.Dickson.SuzukiReeB.exists_eq_conj_of_mem_range
      (CFSG.HardMathSupport.Solomon.Coordinator.b3Lie_center_eq_bot hnc) hin hβ'p hβ'1
    haveI : Fact p.Prime := ⟨hp⟩
    have hx : orderOf x = p := orderOf_eq_prime hxp hx1
    obtain ⟨hW⟩ := CFSG.Walter.Ree.Model.small_Ree_reeTypeHyp a' hm1 K hK'
    have h3 := not_three_dvd_card_centralizer_reeType hW hp hp2 hp3 hx
    rw [hxβ]
    refine qGenCoprime_of_coprime_card ?_
    rw [CFSG.HardMathSupport.Dickson.SuzukiReeB.fixSubgroup_conj, Nat.coprime_comm,
      Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    exact h3
  ·
    obtain ⟨-, δ, σ, hσ, hδ, -⟩ := CFSG.HardMathSupport.Lang.Coordinator.small_Ree_odd_prime_field_descent a'
      hm1 K hK' hp hp2 β' hβ'p hin
    obtain ⟨b, hbp, hbcard, hchar, ⟨eC⟩⟩ :=
      CFSG.HardMathSupport.Curtis.Coordinator.SeitzCyc.reeG2_fixed_data hK' hp hp2 hσ
    haveI := hchar
    set σh := ReeTag.G2.reeGammaFieldAut K a' σ with hσh
    have hβ'eq : β' = δ⁻¹ * σh * δ⁻¹⁻¹ := by rw [← hδ]; group
    rw [hβ'eq]
    refine qGenCoprime_conj δ⁻¹ σh (qGenCoprime_of_fixSubgroup ?_)
    let eF : ↥(fixSubgroup σh) ≃* ReeTag.G2.reeGamma (fixSubfield σ) b :=
      (MulEquiv.subgroupCongr
        (CFSG.HardMathSupport.Dickson.DefCharOuter.Export.SuzukiReeTits.fixSubgroup_eq_fixSub _)).trans eC
    rcases Nat.eq_zero_or_pos b with rfl | hb
    ·
      have hp7 : p ≠ 7 := fun h7 => hm7 ⟨by omega, h7⟩
      have h1512 := (CFSG.ComponentClassification.LiteratureLocal.G2_reeGamma_zero_structure hbcard).1
      refine Or.inr ⟨IsSubnormal.refl _, ?_⟩
      rw [Nat.card_congr eF.toEquiv, h1512]
      exact coprime_1512 hp hp2 hp3 hp7
    ·
      obtain ⟨htop, hsimple', hnc'⟩ :=
        CFSG.ComponentClassification.CatalogueBSmallRee.reeGamma_G2_simple hb (fixSubfield σ) hbcard
      haveI := hsimple'
      have hchev := CFSG.HardMathSupport.Dickson.DefCharOuter.Export.SuzukiReeTits.isChevSimple_commutator_reeGamma
        b (fixSubfield σ) hbcard
      have hZ : Subgroup.center (ReeTag.G2.reeGamma (fixSubfield σ) b) = ⊥ :=
        CFSG.HardMathSupport.Solomon.Coordinator.b3Lie_center_eq_bot hnc'
      let eZ : (ReeTag.G2.reeGamma (fixSubfield σ) b ⧸ Subgroup.center (ReeTag.G2.reeGamma (fixSubfield σ) b)) ≃*
          ReeTag.G2.reeGamma (fixSubfield σ) b :=
        (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
      have hq : CFSG.Open.IsQuasisimple (ReeTag.G2.reeGamma (fixSubfield σ) b) := ⟨htop, eZ.isSimpleGroup⟩
      refine Or.inl ⟨IsSubnormal.refl _, hq.of_mulEquiv eF, ?_⟩
      have e1 : ↥(commutator (ReeTag.G2.reeGamma (fixSubfield σ) b)) ≃* ReeTag.G2.reeGamma (fixSubfield σ) b :=
        (MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv
      have e2 : (↥(fixSubgroup σh) ⧸ Subgroup.center ↥(fixSubgroup σh)) ≃*
          (ReeTag.G2.reeGamma (fixSubfield σ) b ⧸ Subgroup.center (ReeTag.G2.reeGamma (fixSubfield σ) b)) :=
        QuotientGroup.congr _ _ eF (Subgroup.map_center_eq eF)
      exact CFSG.HardMathSupport.Solomon.Coordinator.LieComp.isChevSimple_congr (e1.trans (eZ.symm.trans e2.symm))
        hchev

end Ree

section SympGeneric

theorem qGenCoprime_of_lieCompsExport {X T : Type} [Group X] [Finite X] [Group T] [Finite T] {q p : ℕ}
    (hp : p.Prime) (π : X →* T) (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center X)
    (hcop : Nat.Coprime (Nat.card π.ker) q) (α : MulAut X) (β : MulAut T) (hαβ : ∀ x, π (α x) = β (π x))
    (hβ : CFSG.HardMathSupport.Solomon.Coordinator.LieComp.LieCompsExport q β) {N : Subgroup X}
    (hNα : N ≤ fixSubgroup α) (hN : ⁅N, N⁆ = N)
    (hgen : ∀ x ∈ fixSubgroup α, (∃ n : ℕ, x ^ q ^ n = 1) →
      x ∈ N ⊔ GLAPPrimeCoreOf p (fixSubgroup α)) :
    QGenCoprime q p β := by
  rintro s hs ⟨n, hn⟩
  obtain ⟨x, rfl, hx, hxn⟩ := Inputs256f.exists_fixed_lift π hπ hker hcop α β hαβ hs hn
  have hxm := hgen x (mem_fixSubgroup.2 hx) ⟨n, hxn⟩
  have hmap : (N ⊔ GLAPPrimeCoreOf p (fixSubgroup α)).map π ≤
      ⨆ (J : Subgroup T) (_ : IsChevSubOrCoprime q p β J), J := by
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · have hNT : N.map π ≤ fixSubgroup β :=
        (Subgroup.map_mono hNα).trans (CFSG.HardMathSupport.Solomon.Coordinator.map_fixSubgroup_le π hker α β hαβ)
      have hNP : ⁅N.map π, N.map π⁆ = N.map π := by rw [← Subgroup.map_commutator, hN]
      refine (hβ.layer _ hNT hNP).trans ?_
      refine sSup_le fun K hK => ?_
      obtain ⟨Y, _, _, hY, f, hf, hfk⟩ := hβ.comps K hK
      obtain ⟨e⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.nonempty_centralQuotient_mulEquiv
        hY.perfect f hf hfk
      exact le_iSup₂_of_le (f := fun (J : Subgroup T) (_ : IsChevSubOrCoprime q p β J) => J) K
        (Or.inl ⟨hK.2.1, hK.2.2, CFSG.HardMathSupport.Solomon.Coordinator.LieComp.isChevSimple_congr e hY.chev⟩)
        le_rfl
    · refine (CFSG.HardMathSupport.Solomon.Coordinator.map_glaPPrimeCoreOf_fixSubgroup_le π hker α β hαβ hπ
        hp).trans ?_
      refine le_iSup₂_of_le (f := fun (J : Subgroup T) (_ : IsChevSubOrCoprime q p β J) => J)
        (GLAPPrimeCoreOf p (fixSubgroup β)) (Or.inr ⟨?_, ?_⟩) le_rfl
      · have hle := CFSG.HardMathSupport.Timmesfeld.Proving.GLAPPrimeCoreOf_le (p := p) (fixSubgroup β)
        refine IsSubnormal.step hle ?_ (IsSubnormal.refl _)
        rw [Subgroup.normal_subgroupOf_iff hle]
        intro h k hh hk
        exact CFSG.HardMathSupport.Timmesfeld.Proving.GLAPPrimeCoreOf_conj_mem k hk h hh
      · exact Nat.coprime_comm.1 (CFSG.HardMathSupport.Timmesfeld.Proving.coprime_card_GLAPPrimeCoreOf hp _)
  exact hmap (Subgroup.mem_map_of_mem π hxm)

end SympGeneric

section SympTame

open CFSG.LocalAnalysis.ComponentInitial

variable {q p : ℕ}

@[expose] def QTameCopGrp (q p : ℕ) (H : Type*) [Group H] : Prop :=
  (CFSG.IsQuasisimple ↥(commutator H) ∧ ∀ h : H, (∃ n : ℕ, h ^ q ^ n = 1) → h ∈ commutator H) ∨
    (∀ h : H, (∃ n : ℕ, h ^ q ^ n = 1) → h = 1) ∨ Nat.Coprime (Nat.card H) p

@[expose] def QTameCop (q p : ℕ) {G : Type*} [Group G] (A : Subgroup G) : Prop :=
  (CFSG.IsQuasisimple ↥⁅A, A⁆ ∧ ∀ a ∈ A, (∃ n : ℕ, a ^ q ^ n = 1) → a ∈ ⁅A, A⁆) ∨
    (∀ a ∈ A, (∃ n : ℕ, a ^ q ^ n = 1) → a = 1) ∨ Nat.Coprime (Nat.card A) p

theorem map_commutator_mulEquiv_tame {A B : Type*} [Group A] [Group B] (φ : A ≃* B) :
    (commutator A).map φ.toMonoidHom = commutator B := by
  rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
    ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.2 φ.surjective]

theorem qTameCop_of_mulEquiv {G H : Type*} [Group G] [Group H] {A : Subgroup G} (φ : A ≃* H)
    (h : QTameCopGrp q p H) : QTameCop q p A := by
  have e : ↥(commutator ↥A) ≃* ↥(commutator H) :=
    ((commutator ↥A).equivMapOfInjective φ.toMonoidHom φ.injective).trans
      (MulEquiv.subgroupCongr (map_commutator_mulEquiv_tame φ))
  have e' : ↥(commutator ↥A) ≃* ↥⁅A, A⁆ :=
    ((commutator ↥A).equivMapOfInjective A.subtype A.subtype_injective).trans
      (MulEquiv.subgroupCongr (Subgroup.map_subtype_commutator A))
  have hpow : ∀ a (ha : a ∈ A) (n : ℕ), a ^ q ^ n = 1 → (φ ⟨a, ha⟩) ^ q ^ n = 1 := by
    intro a ha n hn
    rw [← map_pow]
    exact (map_eq_one_iff φ φ.injective).2 (Subtype.ext (by simpa using hn))
  rcases h with ⟨hq, hel⟩ | hel | hcop
  · refine Or.inl ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (e.symm.trans e') hq, ?_⟩
    rintro a ha ⟨n, hn⟩
    have h1 : φ ⟨a, ha⟩ ∈ commutator H := hel _ ⟨n, hpow a ha n hn⟩
    have h2 : (⟨a, ha⟩ : A) ∈ commutator ↥A := by
      rw [← map_commutator_mulEquiv_tame φ.symm]
      exact ⟨φ ⟨a, ha⟩, h1, φ.symm_apply_apply _⟩
    rw [← Subgroup.map_subtype_commutator]
    exact ⟨⟨a, ha⟩, h2, rfl⟩
  · refine Or.inr (Or.inl fun a ha ⟨n, hn⟩ => ?_)
    have h1 := hel (φ ⟨a, ha⟩) ⟨n, hpow a ha n hn⟩
    have h2 : (⟨a, ha⟩ : A) = 1 := (map_eq_one_iff φ φ.injective).1 h1
    exact congrArg Subtype.val h2
  · refine Or.inr (Or.inr ?_)
    rw [Nat.card_congr φ.toEquiv]
    exact hcop

theorem qTameCopGrp_of_isQuasisimple {H : Type*} [Group H] (h : CFSG.IsQuasisimple H) : QTameCopGrp q p H := by
  have h1 : commutator H = ⊤ := Group.isPerfect_def.mp h.1
  refine Or.inl ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv
    ((MulEquiv.subgroupCongr h1).trans Subgroup.topEquiv).symm h, fun g _ => ?_⟩
  rw [h1]
  exact Subgroup.mem_top g

theorem qTameCopGrp_of_ker {H Ab : Type*} [Group H] [CommGroup Ab] (D : H →* Ab)
    (hq : CFSG.IsQuasisimple ↥D.ker) (hD : ∀ h : H, (∃ n : ℕ, h ^ q ^ n = 1) → D h = 1) :
    QTameCopGrp q p H := by
  have hle : commutator H ≤ D.ker := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_commute.mpr (Commute.all _ _)
  have hge : D.ker ≤ commutator H := by
    have h1 := Subgroup.isPerfect_iff.mp hq.1
    calc D.ker = ⁅D.ker, D.ker⁆ := h1.symm
      _ ≤ ⁅(⊤ : Subgroup H), ⊤⁆ := Subgroup.commutator_mono le_top le_top
      _ = commutator H := (_root_.commutator_def H).symm
  have heq : D.ker = commutator H := le_antisymm hge hle
  refine Or.inl ⟨?_, fun g hg => hge (hD g hg)⟩
  rw [← heq]
  exact hq

theorem qTameCopGrp_of_injective {H H' : Type*} [Group H] [Group H'] [Finite H'] (ι : H →* H')
    (hι : Function.Injective ι) (hcop : Nat.Coprime (Nat.card H') q) : QTameCopGrp q p H :=
  Or.inr (Or.inl fun g ⟨n, hn⟩ => (map_eq_one_iff ι hι).1
    (Inputs256e.eq_one_of_coprime_card hcop (by rw [← map_pow, hn, map_one])))

theorem finite_gl_tame {E W : Type*} [Field E] [Finite E] [AddCommGroup W] [Module E W]
    [FiniteDimensional E W] : Finite (LinearMap.GeneralLinearGroup E W) := by
  have : Finite W := Module.finite_of_finite E
  have : Finite (Module.End E W) :=
    Finite.of_injective _ (DFunLike.coe_injective (F := W →ₗ[E] W))
  exact Finite.of_injective _ Units.val_injective

theorem coprime_card_gl_two_three {E W : Type*} [Field E] [Finite E] [AddCommGroup W] [Module E W]
    [FiniteDimensional E W] (hW : Module.finrank E W = 2) (hE : Nat.card E = 3) (hp : p.Prime) (hp2 : p ≠ 2)
    (hp3 : p ≠ 3) : Nat.Coprime (Nat.card (LinearMap.GeneralLinearGroup E W)) p := by
  haveI : Fintype E := Fintype.ofFinite E
  let b : Module.Basis (Fin 2) E W := Module.finBasisOfFinrankEq E W hW
  have e : LinearMap.GeneralLinearGroup E W ≃* Matrix.GeneralLinearGroup (Fin 2) E :=
    (LinearMap.GeneralLinearGroup.congrLinearEquiv b.equivFun).trans
      Matrix.GeneralLinearGroup.toLin.symm
  rw [Nat.card_congr e.toEquiv, Matrix.card_GL_field, Fin.prod_univ_two]
  have hc : Fintype.card E = 3 := by rw [← Nat.card_eq_fintype_card]; exact hE
  rw [hc, Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
  intro h
  exact not_dvd_two_pow_mul_three_pow hp hp2 hp3 4 1 (by norm_num at h ⊢; exact h)

theorem qTameCopGrp_gl_three {E W : Type*} [Field E] [Finite E] [AddCommGroup W] [Module E W]
    [FiniteDimensional E W] (hE : ringChar E = 3) (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    QTameCopGrp 3 p (LinearMap.GeneralLinearGroup E W) := by
  haveI := finite_gl_tame (E := E) (W := W)
  by_cases hm : 2 ≤ Module.finrank E W
  · by_cases h4 : 3 ≤ Module.finrank E W ∨ 4 ≤ Nat.card E
    · refine qTameCopGrp_of_ker (Units.map (LinearMap.det : Module.End E W →* E))
        (CFSG.RankThree.PartOne.KCUnitary.isQuasisimple_ker_det hm
          (h4.imp id CFSG.RankThree.PartOne.KCSpIsotypic.exists_finset_card_four_of_card))
        fun g ⟨n, hn⟩ => Inputs256e.eq_one_of_coprime_card (Inputs256e.coprime_card_units Nat.prime_three hE)
          (by rw [← map_pow, hn, map_one])
    · have h3 : Nat.card E = 3 := by
        obtain ⟨j, hj, hc⟩ := Inputs256e.exists_card_eq_pow Nat.prime_three hE
        rw [hc] at h4 ⊢
        rcases Nat.lt_or_ge j 2 with h | h
        · obtain rfl : j = 1 := by omega
          rfl
        · exfalso
          have : 3 ^ 2 ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) h
          omega
      exact Or.inr (Or.inr (coprime_card_gl_two_three (by omega) h3 hp hp2 hp3))
  · exact qTameCopGrp_of_injective (MonoidHom.id _) Function.injective_id
      (Inputs256e.coprime_card_gl_of_finrank_le_one Nat.prime_three hE (by omega))

theorem qTameCopGrp_unitary_three {g : ℕ} {E : Type} [Field E] (hE : UnitaryFieldData 3 g E)
    {W : Type*} [AddCommGroup W] [Module E W] [FiniteDimensional E W]
    {Hf : W →ₛₗ[hE.bar] W →ₗ[E] E} (hHf : Hf.IsSymm) (hHfl : Hf.SeparatingLeft) (hp : p.Prime)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) : QTameCopGrp 3 p ↥(sesqUnitaryGroup Hf) := by
  haveI := hE.finite
  haveI : Fact (3 : ℕ).Prime := ⟨Nat.prime_three⟩
  haveI : CharP E 3 := hE.charP
  have hE3 : ringChar E = 3 := ringChar.eq E 3
  have hQ : 3 ≤ 3 ^ g := Nat.le_self_pow (by have := hE.one_le; omega) 3
  haveI := finite_gl_tame (E := E) (W := W)
  by_cases hm : 2 ≤ Module.finrank E W
  · obtain ⟨hU, -, -, -, hker, -⟩ :=
      CFSG.LinearGroups.unitary_full_group_order hE hHf hHfl rfl (by omega)
    by_cases hgood : Module.finrank E W = 2 → 4 ≤ 3 ^ g
    · refine qTameCopGrp_of_ker (CFSG.LinearGroups.unitaryDet Hf) ?_
        fun u ⟨n, hn⟩ => Inputs256e.eq_one_of_coprime_card (Inputs256e.coprime_card_units Nat.prime_three hE3)
          (by rw [← map_pow, hn, map_one])
      rw [hker]
      exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe (sesqSpecialUnitaryGroup_le Hf)).symm
        (CFSG.RankThree.PartOne.KCUnitary.isQuasisimple_sesqSpecialUnitaryGroup_of_two_le hE hHf hHfl hm
          ⟨hgood, fun _ => hQ⟩)
    · push Not at hgood
      obtain ⟨h2, hlt⟩ := hgood
      have hg3 : 3 ^ g = 3 := by omega
      refine Or.inr (Or.inr ?_)
      rw [h2, hg3] at hU
      have h96 : Nat.card ↥(sesqUnitaryGroup Hf) = 96 := by
        have e : ((3 : ℕ) : ℤ) ^ (2 * (2 - 1) / 2) * ∏ i ∈ Finset.Icc 1 2, (((3 : ℕ) : ℤ) ^ i - (-1) ^ i) = 96 := by
          decide +kernel
        exact_mod_cast hU.trans e
      rw [h96, Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
      intro h
      exact not_dvd_two_pow_mul_three_pow hp hp2 hp3 5 1 (by norm_num at h ⊢; exact h)
  · exact qTameCopGrp_of_injective (sesqUnitaryGroup Hf).subtype Subtype.val_injective
      (Inputs256e.coprime_card_gl_of_finrank_le_one Nat.prime_three hE3 (by omega))

end SympTame

section SympInner

open Polynomial CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.Classical
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCSpIsotypic
open CFSG.RankThree.PartOne.KCOrthogonal (reciprocalPolynomial)

variable {r : ℕ} {K : Type} [Field K]

theorem qTameCop_spSupported_of_factor_three [Finite K] {f p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hKℓ : ringChar K = 3) (hK : Nat.card K = 3 ^ f) {x : StatedSp r K}
    {a : StatedProj (StatedSp r K)} (hsq : Squarefree (minpoly K (spEnd x)))
    (blocks : SpPrimaryBlocks 3 f p x a) (h : primaryFactors (spEnd x)) :
    QTameCop 3 p (spSupported x {(h : K[X]), reciprocalPolynomial (h : K[X])}) := by
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with hf0 | hf0
    · exfalso
      have h1 : 1 < Nat.card K := Finite.one_lt_card
      rw [hK, hf0, pow_zero] at h1
      omega
    · exact hf0
  have hK3 : 3 ≤ Nat.card K := by rw [hK]; exact Nat.le_self_pow (by omega) 3
  by_cases hself : reciprocalPolynomial (h : K[X]) = h
  · have hO : ({(h : K[X]), reciprocalPolynomial (h : K[X])} : Set K[X]) = {(h : K[X])} := by
      rw [hself, Set.pair_eq_singleton]
    rw [hO]
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
      by_cases hq : 4 ≤ Nat.card K ∨ 2 ≤ s
      · refine qTameCop_of_mulEquiv (φ.trans e) (qTameCopGrp_of_isQuasisimple
          (CFSG.LieType.Universal.Symplectic.isQuasisimple s K hs1 ?_))
        by_cases h4 : 4 ≤ Nat.card K
        · exact Or.inl (Or.inr h4)
        · exact Or.inr (Or.inl ⟨by omega, by omega⟩)
      · have hK3' : Nat.card K = 3 := by omega
        have hs' : s = 1 := by omega
        refine Or.inr (Or.inr ?_)
        haveI := finite_gl_tame (E := K) (W := primaryComponent (spEnd x) (X - 1))
        rw [Nat.card_congr φ.toEquiv]
        refine Nat.Coprime.coprime_dvd_left (Subgroup.card_subgroup_dvd_card _) ?_
        exact coprime_card_gl_two_three (by rw [hs, hs']) hK3' hp hp2 hp3
    · obtain ⟨d, -, -, σ, -, -, -, -, -, hE, -, Hf, hHf, hHfl, -, -, φ, -⟩ :=
        (blocks.selfDual h h1 hself).exists_half
      exact qTameCop_of_mulEquiv φ (qTameCopGrp_unitary_three hE hHf hHfl hp hp2 hp3)
  · have hP := blocks.paired h (fun e => hself e.symm)
    obtain ⟨φ, -, -⟩ := hP.factor
    haveI : Finite (AdjoinRoot (h : K[X])) := Module.finite_of_finite K
    have hEℓ : ringChar (AdjoinRoot (h : K[X])) = 3 :=
      (Algebra.ringChar_eq K (AdjoinRoot (h : K[X]))).symm.trans hKℓ
    exact qTameCop_of_mulEquiv φ (qTameCopGrp_gl_three hEℓ hp hp2 hp3)

theorem qGenCoprime_conj_sp_three {f p : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 3 ^ f) (hr : 1 ≤ r) (hp : p.Prime)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) (x : StatedSp r K) (hx : x ^ p = 1) (hx1 : x ≠ 1) :
    QGenCoprime 3 p (MulAut.conj (SymplecticFlag.proj r K x)) := by
  classical
  have hq0 : 3 ^ f ≠ 0 := pow_ne_zero f (by norm_num)
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact hq0)
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (3 : ℕ).Prime := ⟨Nat.prime_three⟩
  haveI := Fintype.ofFinite K
  have hcardK : Fintype.card K = 3 ^ f := by rw [Fintype.card_eq_nat_card, hK]
  haveI : CharP K 3 := charP_of_card_eq_prime_pow (f := f) hcardK
  have hKℓ : ringChar K = 3 := ringChar.eq K 3
  have hZc : (SymplecticFlag.proj r K).ker ≤ Subgroup.center (StatedSp r K) := by
    rw [SymplecticHigher.ker_proj]
    exact SymplecticHigher.spScalars_le_center
  have hcard2 : Nat.card (SymplecticFlag.proj r K).ker ∣ 2 := by
    rw [SymplecticHigher.ker_proj, card_spScalars_eq_gcd K hr]
    exact Nat.gcd_dvd_left 2 _
  have hZp : Nat.Coprime (Nat.card (SymplecticFlag.proj r K).ker) p :=
    Nat.Coprime.coprime_dvd_left hcard2 ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
  have hZℓ : Nat.Coprime (Nat.card (SymplecticFlag.proj r K).ker) 3 :=
    Nat.Coprime.coprime_dvd_left hcard2 (by norm_num)
  have ha1 : SymplecticFlag.proj r K x ≠ 1 := fun h =>
    hx1 (CFSG.RankThree.Classical.eq_of_map_eq_of_pow_eq_one_of_coprime (a := 1) (b := 0)
      (SymplecticFlag.proj r K) hZc hZp (by rwa [pow_one]) (by simp) (by rw [h, map_one]))
  have ha : orderOf (SymplecticFlag.proj r K x) = p :=
    orderOf_eq_prime (by rw [← map_pow, hx, map_one]) ha1
  have hxp : orderOf x = p := orderOf_eq_prime hx hx1
  have blocks := (symplectic_cross_prime_primary_centralizer_blocks Nat.prime_three hf hK hp hp2 hp3 hr _
    ha).2 x rfl hxp
  have hpK : (p : K) ≠ 0 := by
    intro h
    rw [CharP.cast_eq_zero_iff K 3] at h
    exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h).symm
  have hsq := (altPrimaryData_spLin hpK hx).squarefree
  haveI : Finite (reciprocalOrbits (spEnd x)) :=
    (Set.Finite.image _ (Finset.finite_toSet _)).to_subtype
  obtain ⟨hcomm, -, hjoin⟩ := blocks.directProduct
  set A : reciprocalOrbits (spEnd x) → Subgroup (StatedSp r K) :=
    fun O => spSupported x (O : Set K[X]) with hA
  have htame : ∀ O, QTameCop 3 p (A O) := by
    rintro ⟨O, h, hh, rfl⟩
    exact qTameCop_spSupported_of_factor_three hp hp2 hp3 hKℓ hK hsq blocks ⟨h, hh⟩
  set N : Subgroup (StatedSp r K) :=
    ⨆ O : {O : reciprocalOrbits (spEnd x) // CFSG.IsQuasisimple ↥⁅A O, A O⁆}, ⁅A O.1, A O.1⁆
    with hN
  have hfix : fixSubgroup (MulAut.conj x) = Subgroup.centralizer ({x} : Set (StatedSp r K)) := by
    ext g
    rw [mem_fixSubgroup, MulAut.conj_apply, mul_inv_eq_iff_eq_mul,
      Subgroup.mem_centralizer_singleton_iff]
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  have hNperf : ⁅N, N⁆ = N :=
    Inputs256f.commutator_iSup_eq _ fun O => Inputs256f.commutator_self_of_perfect (Group.isPerfect_def.mp O.2.1)
  have hNC : N ≤ fixSubgroup (MulAut.conj x) := by
    rw [hfix, ← hjoin]
    exact iSup_le fun O => (Inputs256f.commutator_le_self' _).trans (le_iSup A O.1)
  have hAC : ∀ O, A O ≤ fixSubgroup (MulAut.conj x) := fun O => by
    rw [hfix, ← hjoin]
    exact le_iSup A O
  have hAn : ∀ O, ∀ c ∈ fixSubgroup (MulAut.conj x), ∀ a ∈ A O, c * a * c⁻¹ ∈ A O := by
    intro O c hc a ha
    have hle : fixSubgroup (MulAut.conj x) ≤ Subgroup.normalizer (A O : Set (StatedSp r K)) := by
      rw [hfix, ← hjoin]
      refine iSup_le fun O' => ?_
      by_cases hOO : O' = O
      · rw [hOO]
        exact Subgroup.le_normalizer
      · intro g hg
        have hgc : ∀ b ∈ A O, Commute g b := fun b hb =>
          hcomm O'.1 O'.2 O.1 O.2 (fun h => hOO (Subtype.ext h)) g hg b hb
        rw [Subgroup.mem_normalizer_iff]
        intro b
        constructor
        · intro hb
          rw [(hgc b hb).eq, mul_inv_cancel_right]
          exact hb
        · intro hb
          have h1 : g * (g * b * g⁻¹) = (g * b * g⁻¹) * g := (hgc _ hb).eq
          have h2 : b = g * b * g⁻¹ := by
            calc b = g⁻¹ * ((g * b * g⁻¹) * g) := by group
              _ = g⁻¹ * (g * (g * b * g⁻¹)) := by rw [← h1]
              _ = g * b * g⁻¹ := by group
          rw [h2]
          exact hb
    have h1 := (Subgroup.mem_normalizer_iff.1 (hle hc) a).1 ha
    exact h1
  have hgen : ∀ y ∈ fixSubgroup (MulAut.conj x), (∃ n : ℕ, y ^ 3 ^ n = 1) →
      y ∈ N ⊔ GLAPPrimeCoreOf p (fixSubgroup (MulAut.conj x)) := by
    rintro y hy ⟨n, hn⟩
    rw [hfix, ← hjoin] at hy
    refine Inputs256f.mem_of_mem_iSup_commute Nat.prime_three A
      (fun i j hij a ha b hb => hcomm i.1 i.2 j.1 j.2 (fun h => hij (Subtype.ext h)) a ha b hb) _
      (fun O a ha haq => ?_) hy hn
    rcases htame O with ⟨hq, hel⟩ | hel | hcop
    · exact Subgroup.mem_sup_left ((le_iSup (fun O : {O : reciprocalOrbits (spEnd x) //
        CFSG.IsQuasisimple ↥⁅A O, A O⁆} => ⁅A O.1, A O.1⁆) ⟨O, hq⟩) (hel a ha haq))
    · rw [hel a ha haq]
      exact one_mem _
    · refine Subgroup.mem_sup_right ?_
      exact CFSG.HardMathSupport.Timmesfeld.Proving.le_GLAPPrimeCoreOf_of_normal (hAC O) (hAn O)
        (Nat.coprime_comm.1 hcop) ha
  exact qGenCoprime_of_lieCompsExport hp (SymplecticFlag.proj r K) SymplecticHigher.proj_surjective hZc hZℓ
    (MulAut.conj x) (MulAut.conj (SymplecticFlag.proj r K x)) (fun g => by simp [MulAut.conj_apply])
    (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.lieCompsExport_conj_sp
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.slFactorFacts_holds
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.suFactorFacts_holds
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.spFactorFacts_holds
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.spFourTwoFacts_holds hp hp2 Nat.prime_three hf hK hr
      hp3 x hx) hNC hNperf hgen

end SympInner

section SympOuter

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.ComponentClassification.UnbalancedCatalog (descentField)
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)

variable {r : ℕ} {K : Type} [Field K]

theorem qGen_fieldAut_sp_three [Finite K] (hKℓ : ringChar K = 3) (hr : 2 ≤ r) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (σ : K ≃+* K) (hσ : orderOf σ = p) : Inputs256e.QGen 3 (fieldAut r K σ) := by
  haveI : NeZero r := ⟨by omega⟩
  have hσp : σ ^ p = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  have hfix : fixSubgroup (fieldAut r K σ) =
      (CFSG.RankThree.PartOne.KCSpComm.subfieldInj (r := r) σ).range := by
    rw [CFSG.RankThree.PartOne.KCSpComm.range_subfieldInj,
      ← CFSG.RankThree.PartOne.KCSpComm.spFixedGroup_fieldAut_eq_range (hp.odd_of_ne_two hp2) hσp]
    exact Subgroup.ext fun x =>
      mem_fixSubgroup.trans CFSG.RankThree.PartOne.KCSpComm.mem_spFixedGroup.symm
  have hchar : ringChar (descentField σ) = 3 := by rw [Algebra.ringChar_eq (descentField σ) K, hKℓ]
  obtain ⟨j, hj, hcard⟩ := Inputs256e.exists_card_eq_pow Nat.prime_three hchar
  have hne : ¬(r = 2 ∧ Nat.card (descentField σ) = 2) := fun ⟨_, h2⟩ => by
    have : 3 ≤ 3 ^ j := Nat.le_self_pow (by omega) 3
    omega
  obtain ⟨-, hperf⟩ := CFSG.RankThree.PartOne.KCSpComm.simple_perfect_statedProj
    (k := descentField σ) hr hne
  have hβ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.lieCompsExport_fieldAut_sp
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.spFactorFacts_holds
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.spFourTwoFacts_holds hp hp2 hr σ hσ
  rw [hKℓ] at hβ
  refine Inputs256f.qGen_of_lieCompsExport hβ fun s hs _ => ⟨fixSubgroup (fieldAut r K σ), le_rfl, ?_,
    mem_fixSubgroup.2 hs⟩
  rw [hfix, MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← _root_.commutator_def,
    hperf.commutator_eq_top]

theorem center_eq_bot_of_simple_perfect' {T : Type*} [Group T] (hs : IsSimpleGroup T)
    (hperf : Group.IsPerfect T) : Subgroup.center T = ⊥ := by
  have := hs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center T) with h | h
  · exact h
  · exfalso
    have hcomm : commutator T = ⊥ := by
      rw [commutator, Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro g _
      rw [Subgroup.mem_centralizer_iff]
      intro k _
      have : k ∈ Subgroup.center T := h ▸ Subgroup.mem_top k
      exact (Subgroup.mem_center_iff.mp this g).symm
    have htop : (⊤ : Subgroup T) = ⊥ := by rw [← hcomm]; exact hperf.commutator_eq_top.symm
    obtain ⟨a, b, hab⟩ := exists_pair_ne T
    have ha : a ∈ (⊥ : Subgroup T) := htop ▸ Subgroup.mem_top a
    have hb : b ∈ (⊥ : Subgroup T) := htop ▸ Subgroup.mem_top b
    rw [Subgroup.mem_bot] at ha hb
    exact hab (ha.trans hb.symm)

theorem qGenCoprime_projSp_three {f p : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 3 ^ f) (hr : 2 ≤ r) (hp : p.Prime)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) (β : MulAut (StatedProj (StatedSp r K))) (hβ : orderOf β = p) :
    QGenCoprime 3 p β := by
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero _ (by norm_num))
  have hβp : β ^ p = 1 := by rw [← hβ]; exact pow_orderOf_eq_one β
  have hO := CFSG.RankThree.PartOne.KCSpComm.spOuter (K := K) Nat.prime_three hf hr hK
  have hodd : Odd (orderOf β) := by rw [hβ]; exact hp.odd_of_ne_two hp2
  have hE : β ∈ spSemilinearAutGroup r K :=
    CFSG.RankThree.PartOne.KCSpComm.mem_of_odd_orderOf_of_index_dvd_two _ hO.index_dvd hodd
  have hK3 : 3 ≤ Nat.card K := by
    rw [hK]
    exact Nat.le_self_pow (by omega) 3
  by_cases hD : β ∈ spLinearAutGroup r K
  · have : (inner (StatedProj (StatedSp r K))).Normal := inner_normal _
    have hrel : (inner (StatedProj (StatedSp r K))).relIndex (spLinearAutGroup r K) ∣ 2 :=
      hO.relIndex_dvd.trans (Nat.gcd_dvd_left 2 _)
    obtain ⟨t, rfl⟩ := CFSG.RankThree.PartOne.KCSpComm.mem_of_pow_eq_one_of_relIndex_dvd_two hrel
      hp hp2 hD hβp
    obtain ⟨hsimple, hperf⟩ := CFSG.RankThree.PartOne.KCSpComm.simple_perfect_statedProj (k := K) hr
      (fun h => by omega)
    have ht : t ^ p = 1 := by
      have hc : t ^ p ∈ Subgroup.center (StatedProj (StatedSp r K)) := by
        rw [Subgroup.mem_center_iff]
        intro g
        have h1 := congrArg (fun φ : MulAut (StatedProj (StatedSp r K)) => φ g)
          (show MulAut.conj (t ^ p) = 1 by rw [map_pow]; exact hβp)
        simp only [MulAut.conj_apply, MulAut.one_apply] at h1
        calc g * t ^ p = t ^ p * g * (t ^ p)⁻¹ * t ^ p := by rw [h1]
          _ = t ^ p * g := by group
      rw [center_eq_bot_of_simple_perfect' hsimple hperf, Subgroup.mem_bot] at hc
      exact hc
    obtain ⟨x, hx, hxp⟩ :=
      CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.exists_proj_eq_pow_eq_one_sp (by omega)
        hp hp2 ht
    have hx1 : x ≠ 1 := by
      rintro rfl
      rw [map_one] at hx
      subst hx
      rw [map_one, orderOf_one] at hβ
      exact hp.one_lt.ne hβ
    rw [← hx]
    exact qGenCoprime_conj_sp_three hf hK (by omega) hp hp2 hp3 x hxp hx1
  · obtain ⟨-, σ, hσ, h, -, hβeq⟩ := hO.descent p hp β hE hD hβ
    rw [hβeq]
    exact qGenCoprime_conj h _ (qGenCoprime_of_qGen
      (qGen_fieldAut_sp_three (Inputs256f.ringChar_eq_of_card Nat.prime_three hK) hr hp hp2 σ hσ))

end SympOuter

section OrthInner3

open Polynomial Module QuadraticMap CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.Classical2 (orthDerived ProjOrthDerived)
open CFSG.ClassicalGroups.Orthogonal (scalars)

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

theorem conj_mem_supportedBlock_orth3 (hx : OddOrderIsometry Q p x) {Rep : Finset K[X]}
    (hRep : IsOrbitRepresentatives x Rep) (r : ↥Rep) {c : V ≃ₗ[K] V} (hc : c ∈ isometryCentralizer Q x)
    {g : V ≃ₗ[K] V} (hg : g ∈ supportedBlock Q x r) : c * g * c⁻¹ ∈ supportedBlock Q x r := by
  have hle : isometryCentralizer Q x ≤ Subgroup.normalizer (supportedBlock Q x r : Set (V ≃ₗ[K] V)) := by
    rw [← hx.blocks_iSup_eq hRep]
    refine iSup_le fun r' => ?_
    by_cases hrr : r' = r
    · rw [hrr]
      exact Subgroup.le_normalizer
    · intro c' hc'
      rw [Subgroup.mem_normalizer_iff]
      intro b
      have hgc : ∀ b ∈ supportedBlock Q x r, Commute c' b := fun b hb =>
        hx.blocks_commute hRep hrr c' b hc' hb
      constructor
      · intro hb
        rw [(hgc b hb).eq, mul_inv_cancel_right]
        exact hb
      · intro hb
        have h1 : c' * (c' * b * c'⁻¹) = (c' * b * c'⁻¹) * c' := (hgc _ hb).eq
        have h2 : b = c' * b * c'⁻¹ := by
          calc b = c'⁻¹ * ((c' * b * c'⁻¹) * c') := by group
            _ = c'⁻¹ * (c' * (c' * b * c'⁻¹)) := by rw [← h1]
            _ = c' * b * c'⁻¹ := by group
        rw [h2]
        exact hb
  exact (Subgroup.mem_normalizer_iff.1 (hle hc) g).1 hg

theorem qTameCop_supportedBlock_orth3 (hx : OddOrderIsometry Q p x) (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hK3 : ringChar K = 3) {h : K[X]} [Fact (Irreducible h)] (hh : h ∈ primaryFactors x.toLinearMap)
    (hne1 : h ≠ X - 1) : QTameCop 3 p (supportedBlock Q x h) := by
  haveI : Finite (AdjoinRoot h) := Module.finite_of_finite K
  have hE3 : ringChar (AdjoinRoot h) = 3 := (Algebra.ringChar_eq K (AdjoinRoot h)).symm.trans hK3
  by_cases hself : h = reciprocalPolynomial h
  · obtain ⟨ℓ, f, hU, B, hBs, hBl, ⟨φ⟩⟩ :=
      CFSG.HardMathSupport.Dickson.Sec6.I1431.t6orth_selfDual_equiv hx hp2 hp hh hne1 hself
    have hℓ : ℓ = 3 := by
      haveI : CharP (AdjoinRoot h) ℓ := hU.charP
      rw [← hE3]
      exact (ringChar.eq (AdjoinRoot h) ℓ).symm
    subst hℓ
    exact qTameCop_of_mulEquiv φ (qTameCopGrp_unitary_three hU hBs hBl hp hp2 hp3)
  · exact qTameCop_of_mulEquiv (pairedBlockEquiv hx hh hself) (qTameCopGrp_gl_three hE3 hp hp2 hp3)

theorem fixedBlock_orth3 (hx : OddOrderIsometry Q p x) (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hK3 : ringChar K = 3) {m : ℕ} (F : Fin m → Subgroup (V ≃ₗ[K] V))
    (hFsup : FixedLayerListed Q x → ⨆ i, F i = supportedFixedDerived Q x) :
    Nat.Coprime (Nat.card (supportedBlock Q x (X - 1))) p ∨
      ∀ g ∈ supportedBlock Q x (X - 1), (∃ n : ℕ, g ^ 3 ^ n = 1) → g ∈ ⨆ i, F i := by
  classical
  haveI : Fact (3 : ℕ).Prime := ⟨Nat.prime_three⟩
  have hres : ∀ g (hg : g ∈ supportedBlock Q x (X - 1)) (k : ℕ), g ^ 3 ^ k = 1 →
      restrictFixed Q x ⟨g, hg⟩ ∈ TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype) ∧
        restrictFixed Q x ⟨g, hg⟩ ^ 3 ^ k = 1 := by
    intro g hg k hk
    refine ⟨?_, ?_⟩
    · rw [← isometryRestrictFixed_restrictFixed]
      exact isometryRestrictFixed_mem_orthogonalGroup _
    · rw [← map_pow]
      have : (⟨g, hg⟩ : ↥(supportedBlock Q x (X - 1))) ^ 3 ^ k = 1 := Subtype.ext (by simpa using hk)
      rw [this, map_one]
  by_cases hlist : FixedLayerListed Q x
  · right
    rintro g hg ⟨k, hk⟩
    obtain ⟨hwO, hwk⟩ := hres g hg k hk
    obtain ⟨j, -, hKcard⟩ := Inputs256e.exists_card_eq_pow Nat.prime_three hK3
    have hoddK : Odd (Nat.card K) := by
      rw [hKcard]
      exact (Nat.prime_three.odd_of_ne_two (by norm_num)).pow
    have hwΩ : restrictFixed Q x ⟨g, hg⟩ ∈ orthDerived (Q.comp (fixedSpace x).subtype) :=
      Inputs256f.mem_orthDerived_of_odd_orderOf _ hx.polarBilin_fixed_nondegenerate hoddK hlist.1 hlist.2
        hwO (Inputs256f.odd_orderOf_of_pow Nat.prime_three (by norm_num) hwk)
    have hgS : g ∈ supportedFixedDerived Q x := mem_supportedFixedDerived.mpr ⟨hg, hwΩ⟩
    rw [← hFsup hlist] at hgS
    exact hgS
  · by_cases hdim : finrank K (fixedSpace x) ≤ 2
    · right
      rintro g hg ⟨k, hk⟩
      obtain ⟨hwO, hwk⟩ := hres g hg k hk
      have hw1 : restrictFixed Q x ⟨g, hg⟩ = 1 :=
        Inputs256f.eq_one_of_pow_of_finrank_le_two hx.polarBilin_fixed_nondegenerate Nat.prime_three
          (by norm_num) hK3 hdim (g := ⟨restrictFixed Q x ⟨g, hg⟩, hwO⟩) (n := k) (Subtype.ext (by simpa using hwk))
      rw [hx.eq_one_of_restrictFixed_eq_one hg hw1]
      exact one_mem _
    · left
      push Not at hdim
      have hexc : SmallFixedException (Q.comp (fixedSpace x).subtype) := by
        by_contra hne
        exact hlist ⟨by omega, hne⟩
      obtain ⟨hno, -⟩ := orthogonal_regular_space_coverage (Q.comp (fixedSpace x).subtype)
        hx.polarBilin_fixed_nondegenerate (by omega)
      haveI : Finite (fixedSpace x) := Module.finite_of_finite K
      haveI : Finite (fixedSpace x ≃ₗ[K] fixedSpace x) :=
        Finite.of_injective (fun e : fixedSpace x ≃ₗ[K] fixedSpace x => (e : fixedSpace x → fixedSpace x))
          fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
      rw [Nat.card_congr (fixedBlockEquiv hx).toEquiv, Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
      intro hdvd
      haveI : Fact p.Prime := ⟨hp⟩
      obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hdvd
      have hp4 : 3 < p := by
        have := hp.two_le
        omega
      exact hno hexc g p hp hp4 hg

theorem conj_mem_orthDerived_orth3 {c : V ≃ₗ[K] V} (hc : c ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    {g : V ≃ₗ[K] V} (hg : g ∈ orthDerived Q) : c * g * c⁻¹ ∈ orthDerived Q := by
  have hn : (⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆.subgroupOf
      (TauCeti.QuadraticMap.orthogonalGroup Q)).Normal := by
    have h1 : (⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆.subgroupOf
        (TauCeti.QuadraticMap.orthogonalGroup Q)) = commutator ↥(TauCeti.QuadraticMap.orthogonalGroup Q) := by
      rw [← Subgroup.map_subtype_commutator]
      exact Subgroup.comap_map_eq_self_of_injective (TauCeti.QuadraticMap.orthogonalGroup Q).subtype_injective _
    rw [h1]
    infer_instance
  have hle : orthDerived Q ≤ TauCeti.QuadraticMap.orthogonalGroup Q :=
    CFSG.RankThree.Classical.orthDerived_le_orthogonalGroup Q
  have h1 := hn.conj_mem ⟨g, hle hg⟩ (Subgroup.mem_subgroupOf.2 hg) ⟨c, hc⟩
  rw [Subgroup.mem_subgroupOf] at h1
  simpa using h1

theorem exists_perfect_coprime_isometryCentralizer_orth3 (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) (hK3 : ringChar K = 3)
    (hx : OddOrderIsometry Q p x) (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    ∃ P₀ M : Subgroup (V ≃ₗ[K] V), P₀ ≤ orthDerived Q ∧ P₀ ≤ isometryCentralizer Q x ∧ ⁅P₀, P₀⁆ = P₀ ∧
      M ≤ orthDerived Q ∧ M ≤ isometryCentralizer Q x ∧ Nat.Coprime (Nat.card M) p ∧
      (∀ c ∈ isometryCentralizer Q x, ∀ m ∈ M, c * m * c⁻¹ ∈ M) ∧
      ∀ y ∈ isometryCentralizer Q x, (∃ n : ℕ, y ^ 3 ^ n = 1) → y ∈ P₀ ⊔ M := by
  classical
  haveI : Finite V := Module.finite_of_finite K
  haveI : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  obtain ⟨-, -, -, -, -, -, hodd, -, -⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
  obtain ⟨Rep, hRep⟩ := hx.exists_orbitRepresentatives
  obtain ⟨m, F, hF, hFsup, -⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.exists_fixedFactors hx
  set B : ↥Rep → Subgroup (V ≃ₗ[K] V) := fun r => supportedBlock Q x r with hB
  have hBC : ∀ r, B r ≤ isometryCentralizer Q x := fun r => supportedBlock_le_isometryCentralizer _
  have hCO : isometryCentralizer Q x ≤ TauCeti.QuadraticMap.orthogonalGroup Q := inf_le_left
  have hOΩ : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ = orthDerived Q := rfl
  let ι₁ := {r : ↥Rep // CFSG.IsQuasisimple ↥⁅B r, B r⁆}
  let Fam : Fin m ⊕ ι₁ → Subgroup (V ≃ₗ[K] V) := Sum.elim F (fun r => ⁅B r.1, B r.1⁆)
  let ι₂ := {r : ↥Rep // Nat.Coprime (Nat.card (B r)) p}
  have hcomm₂ : Pairwise fun i j : ι₂ => ∀ a b : V ≃ₗ[K] V, a ∈ B i.1 → b ∈ B j.1 → Commute a b :=
    fun i j hij a b ha hb => hx.blocks_commute hRep (fun h => hij (Subtype.ext h)) a b ha hb
  set P₀ := ⨆ i, Fam i with hP₀
  set M := (⨆ r : ι₂, B r.1) ⊓ orthDerived Q with hM
  have hFamΩ : ∀ i, Fam i ≤ orthDerived Q := by
    rintro (i | r)
    · exact (hF i).2.1.trans hx.supportedFixedDerived_le_orthDerived
    · rw [← hOΩ]
      exact Subgroup.commutator_mono ((hBC r.1).trans hCO) ((hBC r.1).trans hCO)
  have hFamC : ∀ i, Fam i ≤ isometryCentralizer Q x := by
    rintro (i | r)
    · exact (hF i).2.1.trans supportedFixedDerived_le_isometryCentralizer
    · exact (Inputs256f.commutator_le_self' _).trans (hBC r.1)
  have hFamP : ∀ i, ⁅Fam i, Fam i⁆ = Fam i := by
    rintro (i | r)
    · exact Inputs256f.commutator_self_of_perfect (Group.isPerfect_def.mp (hF i).1.1)
    · exact Inputs256f.commutator_self_of_perfect (Group.isPerfect_def.mp r.2.1)
  refine ⟨P₀, M, iSup_le hFamΩ, iSup_le hFamC, Inputs256f.commutator_iSup_eq Fam hFamP, inf_le_right,
    inf_le_left.trans (iSup_le fun r => hBC r.1), ?_, ?_, ?_⟩
  ·
    have h1 : Nat.card ↥(⨆ r : ι₂, B r.1) ∣ ∏ r : ι₂, Nat.card ↥(B r.1) := by
      rw [← Subgroup.noncommPiCoprod_range (hcomm := hcomm₂), ← Nat.card_pi]
      exact Subgroup.card_range_dvd _
    have h2 : Nat.Coprime (∏ r : ι₂, Nat.card ↥(B r.1)) p := Nat.Coprime.prod_left fun r _ => r.2
    exact Nat.Coprime.coprime_dvd_left ((Subgroup.card_dvd_of_le inf_le_left).trans h1) h2
  ·
    intro c hc g hg
    refine ⟨?_, conj_mem_orthDerived_orth3 (hCO hc) hg.2⟩
    have hmap : (⨆ r : ι₂, B r.1).map (MulAut.conj c).toMonoidHom ≤ ⨆ r : ι₂, B r.1 := by
      rw [Subgroup.map_iSup]
      refine iSup_le fun r => ?_
      rintro _ ⟨b, hb, rfl⟩
      exact Subgroup.mem_iSup_of_mem r (conj_mem_supportedBlock_orth3 hx hRep r.1 hc hb)
    have h1 := hmap (Subgroup.mem_map_of_mem _ hg.1)
    simpa [MulAut.conj_apply] using h1
  ·
    intro y hy ⟨n, hn⟩
    rw [← hx.blocks_iSup_eq hRep] at hy
    refine Inputs256f.mem_of_mem_iSup_commute Nat.prime_three B
      (fun i j hij a ha b hb => hx.blocks_commute hRep hij a b ha hb) _ ?_ hy hn
    rintro r g hg ⟨k, hk⟩
    have hgΩ : g ∈ orthDerived Q :=
      hodd g (hCO (hBC r hg)) (Inputs256f.odd_orderOf_of_pow Nat.prime_three (by norm_num) hk)
    by_cases hcop : Nat.Coprime (Nat.card (B r)) p
    · exact Subgroup.mem_sup_right ⟨Subgroup.mem_iSup_of_mem (⟨r, hcop⟩ : ι₂) hg, hgΩ⟩
    · haveI : Fact (Irreducible (r : K[X])) := ⟨irreducible_of_mem_primaryFactors (hRep.1 r.2)⟩
      by_cases hr1 : (r : K[X]) = X - 1
      · have hg' : g ∈ supportedBlock Q x (X - 1) := hr1 ▸ hg
        rcases fixedBlock_orth3 hx hp hp2 hp3 hK3 F hFsup with h | h
        · exact absurd (by rw [hB]; simp only; rw [hr1]; exact h) hcop
        · exact Subgroup.mem_sup_left ((iSup_le fun i => le_iSup Fam (Sum.inl i)) (h g hg' ⟨k, hk⟩))
      · rcases qTameCop_supportedBlock_orth3 hx hp hp2 hp3 hK3 (hRep.1 r.2) hr1 with ⟨hq, hel⟩ | hel | hcop'
        · exact Subgroup.mem_sup_left (le_iSup Fam (Sum.inr ⟨r, hq⟩) (hel g hg ⟨k, hk⟩))
        · rw [hel g hg ⟨k, hk⟩]
          exact one_mem _
        · exact absurd hcop' hcop

theorem qGenCoprime_conj_omega_three {t : StatedLieTag}
    (ht : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) {G : Type} [Group G] {n f : ℕ}
    (hG : CFSG.Assembly.LowTwoRank.StatedClassicalModel G t n 3 f) (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (a : G) (ha : orderOf (MulAut.conj a) = p) : QGenCoprime 3 p (MulAut.conj a) := by
  classical
  obtain ⟨K, _, _, V, _, _, _, Q, hQ, hT, hK3, ⟨e⟩⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.exists_projOrth_model ht hG
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite V := Module.finite_of_finite K
  haveI : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  haveI : Finite G := Finite.of_equiv _ e.symm.toEquiv
  obtain ⟨-, hcenter, hZ2, hsimple, hnonab, -, -, -, hlift⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
  haveI := hsimple
  have hZ : Subgroup.center (ProjOrthDerived Q) = ⊥ :=
    CFSG.HardMathSupport.Solomon.Coordinator.b3Lie_center_eq_bot hnonab
  have hc : MulAut.congr e (MulAut.conj a) = MulAut.conj (e a) := by
    ext y
    simp [MulAut.congr_apply, MulAut.conj_apply]
  have hea : orderOf (e a) = p := by
    rw [← Inputs256f.orderOf_conj_of_center_eq_bot hZ, ← hc, Inputs256f.orderOf_congr, ha]
  have hap : a ^ p = 1 := by
    have h1 : (e a) ^ p = 1 := by rw [← hea]; exact pow_orderOf_eq_one _
    exact (map_eq_one_iff e e.injective).1 (by rw [map_pow]; exact h1)
  obtain ⟨x, ⟨hxa, hxp⟩, -, -⟩ := hlift p hp hp2 (e a) hea
  have hx : OddOrderIsometry Q p (x : V ≃ₗ[K] V) :=
    oddOrderIsometry_of_orthDerived hp (by rw [hK3]; exact hp3) hQ x hxp
  obtain ⟨P₀, M, hP₀Ω, hP₀C, hP₀perf, hMΩ, hMC, hMcop, hMn, hgen⟩ :=
    exists_perfect_coprime_isometryCentralizer_orth3 hQ hT hK3 hx hp hp2 hp3
  set mk := QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) with hmk
  set π : ↥(orthDerived Q) →* G := e.symm.toMonoidHom.comp mk with hπ
  have hπs : Function.Surjective π := e.symm.surjective.comp (QuotientGroup.mk'_surjective _)
  have hkerπ : π.ker = mk.ker := by
    ext g
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hπ, MonoidHom.comp_apply]
    exact map_eq_one_iff _ e.symm.injective
  have hker : π.ker ≤ Subgroup.center ↥(orthDerived Q) := by
    rw [hkerπ, hmk, QuotientGroup.ker_mk', hcenter]
  have hcop : Nat.Coprime (Nat.card π.ker) 3 := by
    rw [hkerπ, hmk, QuotientGroup.ker_mk']
    have h1 := Nat.card_pos (α := ↥((scalars K V).subgroupOf (orthDerived Q)))
    rcases (show Nat.card ↥((scalars K V).subgroupOf (orthDerived Q)) = 1 ∨
        Nat.card ↥((scalars K V).subgroupOf (orthDerived Q)) = 2 by omega) with h | h
    · rw [h]
      exact Nat.coprime_one_left 3
    · rw [h]
      norm_num
  have hπx : π x = a := by
    rw [hπ, MonoidHom.comp_apply]
    show e.symm (QuotientGroup.mk x) = a
    rw [hxa, MulEquiv.symm_apply_apply]
  have hαβ : ∀ g, π (MulAut.conj x g) = MulAut.conj a (π g) := fun g => by
    rw [MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv, hπx]
  have hβ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.lieCompsExport_conj_omega
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.slFactorFacts_holds
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.suFactorFacts_holds
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.omegaFactorFacts_holds hp hp2 ht hG hp3 a hap
  have hfixC : ∀ z : ↥(orthDerived Q), z ∈ fixSubgroup (MulAut.conj x) →
      (z : V ≃ₗ[K] V) ∈ isometryCentralizer Q x := by
    intro z hz
    have h1 : x * z * x⁻¹ = z := mem_fixSubgroup.1 hz
    have hzx : z * x = x * z := by
      calc z * x = (x * z * x⁻¹) * x := by rw [h1]
        _ = x * z := by group
    exact Subgroup.mem_inf.mpr ⟨CFSG.RankThree.Classical.orthDerived_le_orthogonalGroup Q z.2,
      Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hzx)⟩
  have hCfix : ∀ z : ↥(orthDerived Q), (z : V ≃ₗ[K] V) ∈ isometryCentralizer Q x →
      z ∈ fixSubgroup (MulAut.conj x) := by
    intro z hz
    have h1 : (z : V ≃ₗ[K] V) * x = x * z :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hz).2
    have h2 : z * x = x * z := Subtype.ext h1
    rw [mem_fixSubgroup, MulAut.conj_apply, ← h2, mul_inv_cancel_right]
  refine qGenCoprime_of_lieCompsExport hp π hπs hker hcop (MulAut.conj x) (MulAut.conj a) hαβ hβ
    (N := P₀.subgroupOf (orthDerived Q)) (fun z hz => hCfix z (hP₀C (Subgroup.mem_subgroupOf.1 hz)))
    (Inputs256f.commutator_subgroupOf_eq' hP₀Ω hP₀perf) ?_
  rintro z hz ⟨k, hk⟩
  have hzk : (z : V ≃ₗ[K] V) ^ 3 ^ k = 1 := by
    have h1 := congrArg Subtype.val hk
    simpa using h1
  have h1 := hgen _ (hfixC z hz) ⟨k, hzk⟩
  have h2 : z ∈ (P₀ ⊔ M).subgroupOf (orthDerived Q) := Subgroup.mem_subgroupOf.2 h1
  rw [Subgroup.subgroupOf_sup hP₀Ω hMΩ] at h2
  have hM' : M.subgroupOf (orthDerived Q) ≤ GLAPPrimeCoreOf p (fixSubgroup (MulAut.conj x)) := by
    refine CFSG.HardMathSupport.Timmesfeld.Proving.le_GLAPPrimeCoreOf_of_normal
      (fun w hw => hCfix w (hMC (Subgroup.mem_subgroupOf.1 hw))) (fun c hc w hw => ?_) ?_
    · rw [Subgroup.mem_subgroupOf] at hw ⊢
      have h3 := hMn _ (hfixC c hc) _ hw
      simpa using h3
    · rw [Nat.coprime_comm, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMΩ).toEquiv]
      exact hMcop
  exact (sup_le_sup_left hM' _) h2

end OrthInner3

section Catalogue

open CFSG.LieType.SeitzGeneration (Cat IsLinearIndex IsUnitaryIndex')

theorem qGen3On_linear : QGen3On fun d _ => IsLinearIndex d.1 := by
  rintro ⟨d, hv⟩ hd3 p hp hp2 hp3 ⟨m, Q, rfl⟩ β hβ
  have : Fact Q.p.Prime := ⟨Q.prime_p⟩
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hQc : Q.p = 3 := by simpa using hd3
  let e : Cat ⟨.A m Q, hv⟩ ≃* CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL (m + 1)
      (GaloisField Q.p Q.exponent) :=
    (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL m Q hv).trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL (m + 1) _)
  have hchar : ringChar (GaloisField Q.p Q.exponent) = 3 := by rw [ringChar.eq _ Q.p, hQc]
  have hβp : MulAut.congr e β ^ p = 1 := by rw [← map_pow, ← hβ, pow_orderOf_eq_one, map_one]
  exact qGenCoprime_of_congr e β (qGenCoprime_projectiveSL_three hchar hp hp2 hp3 (by omega) _ hβp)

theorem qGen3On_unitary : QGen3On fun d _ => IsUnitaryIndex' d.1 := by
  rintro ⟨d, hv⟩ hd3 p hp hp2 hp3 ⟨r, Q, rfl⟩ β hβ
  have : Fact Q.p.Prime := ⟨Q.prime_p⟩
  have hQc : Q.p = 3 := by simpa using hd3
  obtain ⟨⟨hℓ, hf, hn3, hq⟩, K, _, _, hK, ⟨eT⟩⟩ :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r Q hv (MulEquiv.refl _)
  have h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData Q.p Q.exponent K :=
    ⟨hℓ, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  obtain ⟨eP⟩ := CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.nonempty_primeFormP_mulEquiv h
    (CFSG.RankThree.PartOne.KCUnitaryModel.isPrimeFormGram_idGram (n := r + 1) (K := K))
  let e' : Cat ⟨.twistedA r Q, hv⟩ ≃*
      CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormP h
        (CFSG.RankThree.PartOne.KCUnitaryModel.idGram K (r + 1)) :=
    (eT.trans (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSUEquiv h (by omega)).symm).trans eP.symm
  have hq' : ¬(r + 1 = 3 ∧ Q.p ^ Q.exponent = 2) := fun h3 => hq (Prod.ext h3.1 h3.2)
  have hC : CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.IsPrimeFormGram (1 : GL (Fin (r + 1)) K) :=
    CFSG.RankThree.PartOne.KCUnitaryModel.isPrimeFormGram_idGram
  have hβ' : MulAut.congr e' β ^ p = 1 := by rw [← map_pow, ← hβ, pow_orderOf_eq_one, map_one]
  obtain ⟨-, -, hker1, -, -, -, -, hkerD, -, -, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.unitary_prime_form_full_semilinear_realization h hC hn3 hq'
  refine qGenCoprime_of_congr e' β ?_
  by_cases hσ : CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormFieldFactor h hC hn3 hq'
      (MulAut.congr e' β) = 1
  ·
    have hβD : MulAut.congr e' β ∈
        (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormFieldFactor h hC hn3 hq').ker := hσ
    rw [hkerD, CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormD, MonoidHom.mem_range] at hβD
    obtain ⟨A, hA⟩ := hβD
    have h1 : CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormPsi h hC ⟨A ^ p, 1⟩ = 1 := by
      rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormPsi_apply, map_pow, hA, hβ', map_one,
        one_mul]
    obtain ⟨-, c, -, hc⟩ := (hker1 _).1 h1
    have hAp : (A : GL (Fin (r + 1)) K) ^ p = Matrix.GeneralLinearGroup.scalar (Fin (r + 1)) c := by
      rwa [SubgroupClass.coe_pow] at hc
    rw [← hA]
    exact qGenCoprime_primeFormConjHom_three h hQc hp hp2 hp3 A hAp
  ·
    have hne : MulAut.congr e' β ≠ 1 := fun h1 => hσ (by rw [h1, map_one])
    have : Fact p.Prime := ⟨hp⟩
    have hord : orderOf (MulAut.congr e' β) = p := orderOf_eq_prime hβ' hne
    have hσp : orderOf (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormFieldFactor h hC hn3 hq'
        (MulAut.congr e' β)) = p :=
      orderOf_eq_prime (by rw [← map_pow, hβ', map_one]) hσ
    obtain ⟨-, -, -, -, -, M, hM⟩ :=
      CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.unitary_prime_descent_char h hn3 hq' hp hp2
        (MulAut.congr e' β) hord _ rfl hσp
    have h1 := qGenCoprime_of_qGen (p := p) (qGen_primeFormFieldHom_three h hQc hn3 hC hp hp2 hσp)
    rw [← hM] at h1
    have h2 := qGenCoprime_conj (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjHom h
      (CFSG.RankThree.PartOne.KCUnitaryModel.idGram K (r + 1)) M) _ h1
    have hsimp : ∀ γ δ : MulAut (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormP h
        (CFSG.RankThree.PartOne.KCUnitaryModel.idGram K (r + 1))), γ * (γ⁻¹ * δ * γ) * γ⁻¹ = δ :=
      fun γ δ => by group
    rwa [hsimp] at h2

@[expose] def QGen3Orth : Prop :=
  QGen3On fun d _ => (∃ r Q, d.1 = .B r Q ∧ 3 ≤ r) ∨ (∃ r Q, d.1 = .D r Q) ∨ ∃ r Q, d.1 = .twistedD r Q

theorem qGen3SympOrth_of_orth (hO : QGen3Orth) : QGen3SympOrth := by
  rintro ⟨d, hv⟩ hd3 p hp hp2 hp3 hF β hβ
  have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  cases d with
  | B r Q =>
    rcases (show r = 2 ∨ 3 ≤ r by omega) with rfl | hr3
    · have : Fact Q.p.Prime := ⟨Q.prime_p⟩
      have hQc : Q.p = 3 := by simpa using hd3
      have hK : Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B 2 Q, hv⟩) = 3 ^ Q.exponent := by
        rw [← hQc]
        exact CFSG.Models.card_fixedField_of (TauCeti.LieTypeIndex.characteristic_B 2 Q)
          (TauCeti.LieTypeIndex.fieldExponent_B 2 Q)
      let e : Cat ⟨.B 2 Q, hv⟩ ≃*
          CFSG.Open.StatedProj (CFSG.Open.StatedSp 2 ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B 2 Q, hv⟩)) :=
        CFSG.QuasithinUnique.SQTK.typeB2GroupEquivStatedProj Q hv
      exact qGenCoprime_of_congr e β (qGenCoprime_projSp_three Q.exponent_pos hK le_rfl hp hp2 hp3 _
        (by rw [Inputs256f.orderOf_congr, hβ]))
    · exact hO ⟨_, hv⟩ hd3 p hp hp2 hp3 (Or.inl ⟨r, Q, rfl, hr3⟩) β hβ
  | C r Q =>
    have : Fact Q.p.Prime := ⟨Q.prime_p⟩
    have hQc : Q.p = 3 := by simpa using hd3
    have hK : Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.C r Q, hv⟩) = 3 ^ Q.exponent := by
      rw [← hQc]
      exact CFSG.Models.card_fixedField_of (TauCeti.LieTypeIndex.characteristic_C r Q)
        (TauCeti.LieTypeIndex.fieldExponent_C r Q)
    have hr2 : 2 ≤ r := by
      simp only at hr
      omega
    let e : Cat ⟨.C r Q, hv⟩ ≃*
        CFSG.Open.StatedProj (CFSG.Open.StatedSp r ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.C r Q, hv⟩)) :=
      CFSG.QuasithinUnique.SQTK.typeCGroupEquivStatedProj r Q hv
    exact qGenCoprime_of_congr e β (qGenCoprime_projSp_three Q.exponent_pos hK hr2 hp hp2 hp3 _
      (by rw [Inputs256f.orderOf_congr, hβ]))
  | D r Q => exact hO ⟨_, hv⟩ hd3 p hp hp2 hp3 (Or.inr (Or.inl ⟨r, Q, rfl⟩)) β hβ
  | twistedD r Q => exact hO ⟨_, hv⟩ hd3 p hp hp2 hp3 (Or.inr (Or.inr ⟨r, Q, rfl⟩)) β hβ
  | _ => simp [CFSG.Yardstones.Md42047359a2a.lieFamily] at hF

theorem qGen3OrthInner_holds :
    ∀ d : TauCeti.ValidLieTypeIndex,
      ((∃ r Q, d.1 = .B r Q ∧ 3 ≤ r) ∨ (∃ r Q, d.1 = .D r Q) ∨ ∃ r Q, d.1 = .twistedD r Q) →
      d.1.characteristic = 3 → ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 3 → ∀ t : Cat d,
        orderOf (MulAut.conj t) = p → QGenCoprime 3 p (MulAut.conj t) := by
  rintro ⟨d, hv⟩ hd hd3 p hp hp2 hp3 t ht
  rcases hd with ⟨r, Q, hdr, hr3⟩ | ⟨r, Q, hdr⟩ | ⟨r, Q, hdr⟩
  · change d = .B r Q at hdr
    subst hdr
    have hQc : Q.p = 3 := by simpa using hd3
    have hG := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_odd r Q hv (by omega) hr3
      (MulEquiv.refl _)
    rw [hQc] at hG
    exact qGenCoprime_conj_omega_three (Or.inl rfl) hG hp hp2 hp3 t ht
  · change d = .D r Q at hdr
    subst hdr
    have hQc : Q.p = 3 := by simpa using hd3
    have hG := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD r Q hv (MulEquiv.refl _)
    rw [hQc] at hG
    exact qGenCoprime_conj_omega_three (Or.inr (Or.inl rfl)) hG hp hp2 hp3 t ht
  · change d = .twistedD r Q at hdr
    subst hdr
    have hQc : Q.p = 3 := by simpa using hd3
    have hG := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD r Q hv (MulEquiv.refl _)
    rw [hQc] at hG
    exact qGenCoprime_conj_omega_three (Or.inr (Or.inr rfl)) hG hp hp2 hp3 t ht

theorem qGen3Orth_of_inner : QGen3Orth := by
  have hI := qGen3OrthInner_holds
  rintro d hd3 p hp hp2 hp3 hd β hβ
  by_cases hin : ∃ t : Cat d, MulAut.conj t = β
  · obtain ⟨t, rfl⟩ := hin
    exact hI d hd hd3 p hp hp2 hp3 t hβ
  · have hout : ∀ t : Cat d, MulAut.conj t ≠ β := fun t ht => hin ⟨t, ht⟩
    have hβp : β ^ p = 1 := by rw [← hβ]; exact pow_orderOf_eq_one β
    refine qGenCoprime_of_qGen ?_
    obtain ⟨d, hv⟩ := d
    have hfin : ∀ {t : CFSG.Open.StatedLieTag} {n ℓ f : ℕ}, (t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) →
        CFSG.Assembly.LowTwoRank.StatedClassicalModel (Cat ⟨d, hv⟩) t n ℓ f → Finite (Cat ⟨d, hv⟩) := by
      intro t n ℓ f ht hG
      obtain ⟨K, _, _, V, _, _, _, Q, -, -, -, ⟨e⟩⟩ :=
        CFSG.HardMathSupport.Solomon.Coordinator.LieComp.exists_projOrth_model ht hG
      haveI : Finite V := Module.finite_of_finite K
      haveI : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
        fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
      exact Finite.of_equiv _ e.symm.toEquiv
    rcases hd with ⟨r, Q, hdr, hr3⟩ | ⟨r, Q, hdr⟩ | ⟨r, Q, hdr⟩
    · change d = .B r Q at hdr
      subst hdr
      have hQc : Q.p = 3 := by simpa using hd3
      have hG := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_odd r Q hv (by omega) hr3
        (MulEquiv.refl _)
      haveI := hfin (Or.inl rfl) hG
      have h1 := Inputs256f.qGen_omega_outer (Or.inl rfl) hG (by omega) hp hp2 (fun _ _ h3 => absurd h3 hp3)
        β hβp hout
      rwa [hQc] at h1
    · change d = .D r Q at hdr
      subst hdr
      have hQc : Q.p = 3 := by simpa using hd3
      have hG := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD r Q hv (MulEquiv.refl _)
      haveI := hfin (Or.inr (Or.inl rfl)) hG
      have h1 := Inputs256f.qGen_omega_outer (Or.inr (Or.inl rfl)) hG (by omega) hp hp2
        (fun _ _ h3 => absurd h3 hp3) β hβp hout
      rwa [hQc] at h1
    · change d = .twistedD r Q at hdr
      subst hdr
      have hQc : Q.p = 3 := by simpa using hd3
      have hG := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD r Q hv (MulEquiv.refl _)
      haveI := hfin (Or.inr (Or.inr rfl)) hG
      have h1 := Inputs256f.qGen_omega_outer (Or.inr (Or.inr rfl)) hG (by omega) hp hp2
        (fun _ _ h3 => absurd h3 hp3) β hβp hout
      rwa [hQc] at h1

end Catalogue

section ExcField

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.StandardType.RecipeExcLang (inndiagGroup)
open CFSG.LieType.SeitzGeneration (Cat)

@[expose] def QGen3ExcInndiag : Prop :=
  ∀ (τ : Tag), (τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) →
    ∀ (K : Type) [Field K] [Finite K], ringChar K = 3 →
    ∀ (p : ℕ), p.Prime → p ≠ 2 → p ≠ 3 →
    ∀ (α : MulAut ↥(adjointGroup τ K)) (b : Fin τ.rank → Kˣ) (j : ModGL τ K), j ∈ adjointGroup τ K →
      (∀ c : adjointGroup τ K,
        (α c : ModGL τ K) = (rootDiagUnit τ b * j) * c * (rootDiagUnit τ b * j)⁻¹) →
      (rootDiagUnit τ b * j) ^ p = 1 → rootDiagUnit τ b * j ≠ 1 →
        QGenCoprime 3 p α

@[expose] def QGen3TwE6 : Prop := QGen3On fun d _ => ∃ q, d.1 = .twistedE6 q

@[expose] def QGen3TriD4 : Prop := QGen3On fun d _ => ∃ q, d.1 = .trialityD4 q

@[expose] def QGen3TriD4Inner : Prop :=
  ∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid), q.p = 3 →
    ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 3 → ∀ t : Cat ⟨.trialityD4 q, hv⟩,
      orderOf (MulAut.conj t) = p → QGenCoprime 3 p (MulAut.conj t)


theorem qGenCoprime_exc_untw_three (hI : QGen3ExcInndiag) {τ : Tag}
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {c : TauCeti.PrimePower → TauCeti.LieTypeIndex}
    (hB : CFSG.TauCetiBridge.Even.UntwistedBridgeAll τ c)
    (hchar : ∀ q : TauCeti.PrimePower, (c q).characteristic = q.p)
    (hvalid : ∀ q : TauCeti.PrimePower, (τ = .G2 → 3 ≤ q.card) → (c q).Valid)
    (hA6 : ∀ (q : TauCeti.PrimePower) (hv : (c q).Valid),
      IsEmpty ((TauCeti.CFSGIndex.lie ⟨c q, hv⟩).Group ≃* alternatingGroup (Fin 6)))
    (q : TauCeti.PrimePower) (hv : (c q).Valid) (h3 : q.p = 3) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hp3 : p ≠ 3) (β : MulAut (Cat ⟨c q, hv⟩)) (hβ : orderOf β = p) : QGenCoprime 3 p β := by
  classical
  obtain ⟨K, _, _, hK, hKchar, ⟨e⟩⟩ := CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup hB q hv
  have hℓ : ringChar K = q.p := ringChar.eq K q.p
  have hK3 : ringChar K = 3 := hℓ.trans h3
  have hα : MulAut.congr e β ^ p = 1 := by rw [← map_pow, ← hβ, pow_orderOf_eq_one, map_one]
  have hα1 : MulAut.congr e β ≠ 1 := fun h => by
    have h1 : β = 1 := (MulAut.congr e).injective (h.trans (map_one _).symm)
    rw [h1, orderOf_one] at hβ
    exact hp.one_lt.ne' hβ.symm
  refine qGenCoprime_of_congr e β ?_
  have hq3 : 3 ≤ Nat.card K := by
    rw [hK, TauCeti.PrimePower.card_def, h3]
    exact Nat.le_self_pow q.exponent_pos.ne' 3
  have hdisp : (∃ (σ : K ≃+* K) (ψ : MulAut ↥(adjointGroup τ K)),
      σ ≠ 1 ∧ ψ * MulAut.congr e β * ψ⁻¹ = entrywiseAdjointAut τ σ) ∨
    (∃ h ∈ inndiagGroup τ K, (∀ c : adjointGroup τ K, ((MulAut.congr e β) c : ModGL τ K) = h * c * h⁻¹) ∧
      h ^ p = 1 ∧ h ≠ 1) := by
    rcases hτ with h | h | h | h | h
    · exact CFSG.HardMathSupport.Solomon.Coordinator.LieComp.exists_field_or_inndiag_FG (Or.inr h)
        (fun _ => hq3) hp hp2 _ hα hα1
    · exact CFSG.HardMathSupport.Solomon.Coordinator.LieComp.exists_field_or_inndiag_FG (Or.inl h)
        (fun _ => hq3) hp hp2 _ hα hα1
    · exact CFSG.HardMathSupport.Solomon.Coordinator.LieComp.exists_field_or_inndiag_E (Or.inl h) hp hp2 _
        hα hα1
    · exact CFSG.HardMathSupport.Solomon.Coordinator.LieComp.exists_field_or_inndiag_E (Or.inr (Or.inl h))
        hp hp2 _ hα hα1
    · exact CFSG.HardMathSupport.Solomon.Coordinator.LieComp.exists_field_or_inndiag_E (Or.inr (Or.inr h))
        hp hp2 _ hα hα1
  rcases hdisp with ⟨σ, ψ, -, hψ⟩ | ⟨h, hh, hαh, hhp, hh1⟩
  · have hk : τ = .G2 → 3 ≤ Nat.card (fixSubfield σ) := fun _ => by
      obtain ⟨q', hq'p, hq'c⟩ :=
        CFSG.HardMathSupport.Solomon.Coordinator.LieComp.exists_primePower_card_subfield hℓ (fixSubfield σ)
      rw [hq'c, TauCeti.PrimePower.card_def, hq'p, h3]
      exact Nat.le_self_pow q'.exponent_pos.ne' 3
    have hQ : Inputs256e.QGen q.p (entrywiseAdjointAut τ σ) :=
      Inputs256f.qGen_of_qPerf (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.lieCompExport_entrywiseAdjointAut_untw
        hB hchar hvalid hA6 hℓ σ).toComps
        (Inputs256f.qPerf_of_qElemNormal (Inputs256f.qElemNormal_entrywiseAdjointAut τ q.prime_p hℓ σ hk))
    rw [h3] at hQ
    have hc : MulAut.congr ψ (MulAut.congr e β) = entrywiseAdjointAut τ σ := by
      rw [← hψ]
      exact MulEquiv.ext fun x => rfl
    refine qGenCoprime_of_congr ψ _ ?_
    rw [hc]
    exact qGenCoprime_of_qGen hQ
  · obtain ⟨b, j, hj, rfl⟩ := hh
    exact hI τ hτ K hK3 p hp hp2 hp3 _ b j hj hαh hhp hh1

theorem qGen3TriD4_of_inner (hI : QGen3TriD4Inner) : QGen3TriD4 := by
  rintro ⟨d, hv⟩ hd3 p hp hp2 hp3 ⟨q, hdq⟩ β hβ
  change d = .trialityD4 q at hdq
  subst hdq
  classical
  have h3 : q.p = 3 := by simpa using hd3
  obtain ⟨K, _, _, σ, hK, hσ, -, ⟨eK⟩⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_catEquiv_trialityD4 q hv
  have hα : orderOf (MulAut.congr eK β) = p := by rw [Inputs256f.orderOf_congr]; exact hβ
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  by_cases hin : MulAut.congr eK β ∈ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →*
      MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range
  · obtain ⟨y, hy⟩ := hin
    have hβy : β = MulAut.conj (eK.symm y) := by
      apply (MulAut.congr eK).injective
      rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, MulEquiv.apply_symm_apply]
      exact hy.symm
    rw [hβy] at hβ ⊢
    exact hI q hv h3 p hp hp2 hp3 _ hβ
  · have hp5 : 5 ≤ p := by
      have h2 := hp.two_le
      have h4 : p ≠ 4 := fun h4 => by rw [h4] at hp; exact absurd hp (by decide)
      omega
    have hpow : MulAut.congr eK β ^ p = 1 := by rw [← hα]; exact pow_orderOf_eq_one _
    refine qGenCoprime_of_congr eK β (qGenCoprime_of_qGen ?_)
    have h1 := Inputs256f.qGen_of_qPerf (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.trialityFieldExportP hp
      hp5 q.p q.exponent q.exponent_pos K hK σ hσ _ hpow hin)
      (Inputs256f.qPerf_triD4_outer q.prime_p q.exponent_pos hK σ hσ hp hp5 hα hin)
    rwa [h3] at h1

theorem twistedE6_mem_subfield_three {ℓ d : ℕ} (hℓ : ℓ.Prime) (hℓ3 : ℓ = 3) (hd : 1 ≤ d) {K : Type} [Field K]
    [Finite K] (k : Subfield K) (hk : Nat.card k = (ℓ ^ d) ^ 2) (σ₀ : k ≃+* k)
    (hσ₀ : ∀ c : k, (σ₀ c : K) = (c : K) ^ ℓ ^ d) (ψ : K ≃+* K) (hψ : ∀ c, ψ c = c ^ ℓ ^ d)
    {x : ModGL TwistTag.E6.tag K} (hx : x ∈ CFSG.Blueprint.twistedFixedGroup TwistTag.E6 K ψ.toRingHom) :
    x ∈ CFSG.RankThree.Chevalley.subfieldRootGroupImage TwistTag.E6 k σ₀ := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Finite k := Subtype.finite
  have hσ₀' : ∀ c : k, σ₀.toRingHom c = c ^ ℓ ^ d := fun c =>
    Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact hσ₀ c)
  have : CharP k ℓ := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hℓ
    (by omega : 1 ≤ d * 2) (by rw [hk, ← pow_mul])
  let Ω := AlgebraicClosure k
  have : CharP Ω ℓ := charP_of_injective_algebraMap (algebraMap k Ω).injective ℓ
  obtain ⟨hfinR, -, hder, -, -, hcardR, -⟩ := CFSG.RankThree.Classical2.twisted_E6_full_rational_fixed_group_order
    hℓ hd k hk σ₀.toRingHom hσ₀' Ω (iterateFrobenius Ω ℓ d) (fun c => iterateFrobenius_def ℓ d c)
  let _ : Algebra k K := k.subtype.toAlgebra
  have _ : Algebra.IsAlgebraic k K := Algebra.IsAlgebraic.of_finite k K
  let l : K →ₐ[k] Ω := IsAlgClosed.lift
  let ι : K →+* Ω := l.toRingHom
  have hιk : ι.comp k.subtype = algebraMap k Ω := RingHom.ext fun c => l.commutes c
  have hιψ : ι.comp ψ.toRingHom = (iterateFrobenius Ω ℓ d).comp ι := RingHom.ext fun c => by
    change ι (ψ c) = iterateFrobenius Ω ℓ d (ι c)
    rw [hψ, iterateFrobenius_def, map_pow]
  set R := CFSG.Blueprint.twistedFixedGroup TwistTag.E6 Ω (iterateFrobenius Ω ℓ d) with hR
  set CΩ := (graphFixedRootGroup TwistTag.E6 k σ₀.toRingHom).map (baseChangeGL (algebraMap k Ω)) with hCΩ
  obtain ⟨hxC, hxF⟩ := (mem_twistedFixedGroup_iff_twistHom TwistTag.E6 K ψ.toRingHom).1 hx
  have hxR : baseChangeGL ι x ∈ R := by
    refine (mem_twistedFixedGroup_iff_twistHom TwistTag.E6 Ω _).2
      ⟨baseChangeGL_mem_adjointGroup ι hxC, ?_⟩
    rw [twistHom_baseChangeGL ι hιψ, hxF]
  have hinj : Function.Injective (baseChangeGL ι : ModGL TwistTag.E6.tag K →* _) :=
    baseChangeGL_injective ι
  haveI : Finite ↥R := hfinR
  have hCR : CΩ ≤ R := by
    rw [← hder]
    exact Subgroup.commutator_le_self R
  have hcardC : Nat.card ↥CΩ = ordTwistedE6 (ℓ ^ d) := by
    rw [hCΩ, Subgroup.card_map_of_injective (baseChangeGL_injective _),
      CFSG.ClassicalInvolution.card_graphFixedRootGroup_E6 hℓ hd hk σ₀.toRingHom hσ₀']
  have hgcd : Nat.gcd 3 (ℓ ^ d + 1) = 1 := by
    subst hℓ3
    obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
    rw [pow_succ, Nat.gcd_comm, show 3 ^ e * 3 + 1 = 1 + 3 ^ e * 3 by ring, Nat.gcd_add_mul_right_left]
    rfl
  have hord : ordTwistedE6 (ℓ ^ d) = Nat.card ↥R := by
    rw [ordTwistedE6, hgcd, Nat.div_one, hcardR]
  have hidx1 : (CΩ.subgroupOf R).index = 1 := by
    have h1 := Subgroup.card_mul_index (CΩ.subgroupOf R)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCR).toEquiv, hcardC, hord] at h1
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (h1.trans (mul_one _).symm)
  have hmem : (⟨baseChangeGL ι x, hxR⟩ : ↥R) ∈ CΩ.subgroupOf R := by
    rw [Subgroup.index_eq_one.1 hidx1]
    exact Subgroup.mem_top _
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_subgroupOf.mp hmem
  refine ⟨y, hy, hinj ?_⟩
  change baseChangeGL ι (baseChangeGL k.subtype y) = baseChangeGL ι x
  rw [baseChangeGL_baseChangeGL, hιk]
  exact hyx

private theorem qPerf_twE6_field_three {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 3 ^ (2 * f)) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (3 ^ f)) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (Θ : MulAut (twistedE6RootGroup K σ) →* RingAut K)
    (hΘ : ∀ α g u δ, α = MulAut.conj g * compatDiagAutHom TwistTag.E6 K σ.toRingHom u *
      fieldActor σ δ → Θ α = δ)
    (β : MulAut (twistedE6RootGroup K σ)) (hβ : β ^ p = 1) (hη1 : Θ β ≠ 1) : Inputs256f.QPerf 3 β := by
  classical
  have hℓ : (3 : ℕ).Prime := Nat.prime_three
  obtain ⟨d, hd, hd1, r, s, T, ε, hT, hε, hrs, ψ, hψ, -⟩ :=
    CFSG.HardMathSupport.Lang.Coordinator.twisted_E6_field_descent_data_of_prime_order hℓ hf K hK
      σ hσ Θ hΘ hp hp2 β hβ hη1
  have hdp : d * p = f := by rw [hd, mul_comm]
  obtain ⟨fr, hfr, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality hℓ
      (by omega : 1 ≤ 2 * f) hK
  obtain ⟨κ, hκ⟩ : ∃ κ : K ≃+* K, ∀ c, κ c = c ^ 3 ^ (2 * d) :=
    ⟨fr ^ (2 * d), fun c => ringAut_pow_apply_of_frobenius hfr (2 * d) c⟩
  have hKdp : Nat.card K = 3 ^ (2 * d * p) := by rw [hK, mul_assoc, hdp]
  have hσdp : ∀ c, σ c = c ^ 3 ^ (d * p) := fun c => by rw [hσ, hdp]
  have hσ₀ : ∀ c : fixSubfield κ, (fixSubfieldRestrict T κ c : K) = (c : K) ^ 3 ^ d :=
    fun c => by rw [coe_fixSubfieldRestrict, hT]
  have hm3 : 3 ≤ p := by have := hp.two_le; omega
  obtain ⟨-, hcardk, hJC, -, hder, hsimpleJ, hncJ, -⟩ :=
    CFSG.RankThree.Chevalley.twisted_E6_canonical_odd_field_derived_subgroup_and_pointwise_centralizer
      hℓ hd1 hm3 (hp.odd_of_ne_two hp2) K hKdp κ hκ σ hσdp (fixSubfieldRestrict T κ) hσ₀ ε hε
  set J := CFSG.RankThree.Chevalley.subfieldRootGroupImage TwistTag.E6 (fixSubfield κ)
    (fixSubfieldRestrict T κ) with hJdef
  set δ := fieldActor (t := TwistTag.E6) σ ε with hδdef
  haveI : Finite (fixSubfield κ) := Subtype.finite
  have hder' : ⁅fixSubgroup δ, fixSubgroup δ⁆ = J.subgroupOf (twistedE6RootGroup K σ) := hder
  have eJC : J.subgroupOf (twistedE6RootGroup K σ) ≃* J := Subgroup.subgroupOfEquivOfLe hJC
  haveI := hsimpleJ
  have hJn : ∃ x y : J.subgroupOf (twistedE6RootGroup K σ), x * y ≠ y * x := by
    by_contra hcon
    push Not at hcon
    apply hncJ
    intro a b
    have h := hcon (eJC.symm a) (eJC.symm b)
    apply eJC.symm.injective
    rw [map_mul, map_mul]
    exact h
  have hJs : IsSimpleGroup (J.subgroupOf (twistedE6RootGroup K σ)) := eJC.isSimpleGroup
  have hJperf : ⁅J.subgroupOf (twistedE6RootGroup K σ), J.subgroupOf (twistedE6RootGroup K σ)⁆ =
      J.subgroupOf (twistedE6RootGroup K σ) :=
    Inputs256f.commutator_self_of_perfect
      (CFSG.HardMathSupport.Solomon.Coordinator.b3Lie_isQuasisimple_of_simple hJn).1
  have hψpow : ∀ c, (σ * ε) c = c ^ 3 ^ d := fun c => by
    have : Fintype K := Fintype.ofFinite K
    have hcard : Fintype.card K = 3 ^ (2 * d * p) := by rw [← Nat.card_eq_fintype_card, hKdp]
    have h1 : c ^ (3 ^ (2 * d * p)) = c := by
      have := FiniteField.pow_card c
      rwa [hcard] at this
    rw [RingAut.mul_apply, hε, hσdp, ← pow_mul, show 3 ^ (d * (p + 1)) * 3 ^ (d * p) =
      3 ^ (2 * d * p) * 3 ^ d by rw [← pow_add, ← pow_add]; congr 1; ring, pow_mul, h1]
  have hK0 : Nat.card (fixSubfield κ) = (3 ^ d) ^ 2 := by rw [hcardk, ← pow_mul, mul_comm]
  have hδ : Inputs256f.QPerf 3 δ := by
    intro x hx _
    refine ⟨J.subgroupOf (twistedE6RootGroup K σ), hder' ▸ Inputs256f.commutator_le_self' _, hJperf, ?_⟩
    have hδx : Units.map (entrywiseHom ε.toRingHom) (x : ModGL TwistTag.E6.tag K) = x := by
      have h := congrArg Subtype.val hx
      rwa [coe_fieldActor] at h
    have hxψ : (x : ModGL TwistTag.E6.tag K) ∈
        CFSG.Blueprint.twistedFixedGroup TwistTag.E6 K (σ * ε).toRingHom := by
      obtain ⟨hxA, hxσ⟩ := (mem_twistedFixedGroup_iff_twistHom TwistTag.E6 K σ.toRingHom).1
        (graphFixedRootGroup_le _ _ _ x.2)
      refine (mem_twistedFixedGroup_iff_twistHom TwistTag.E6 K (σ * ε).toRingHom).2 ⟨hxA, ?_⟩
      rw [twistHom_apply] at hxσ ⊢
      rw [show (σ * ε).toRingHom = σ.toRingHom.comp ε.toRingHom from RingHom.ext fun _ => rfl,
        ← units_map_entrywiseHom_comp, hδx]
      exact hxσ
    exact Subgroup.mem_subgroupOf.2 (twistedE6_mem_subfield_three hℓ rfl hd1
      (fixSubfield κ) hK0 (fixSubfieldRestrict T κ) hσ₀ (σ * ε) hψpow hxψ)
  have hβr : Inputs256f.QPerf 3 (β ^ r) := by
    refine Inputs256f.qPerf_of_congr ψ ?_
    have hc : MulAut.congr ψ (β ^ r) = δ := by
      rw [← hψ]
      exact MulEquiv.ext fun x => rfl
    rw [hc]
    exact hδ
  refine Inputs256f.qPerf_of_fixSubgroup_eq ?_ hβr
  ext x
  simp only [mem_fixSubgroup]
  constructor
  · intro hx
    exact Inputs256f.mulAut_pow_apply_of_apply_eq hx r
  · intro hx
    have h1 : (β ^ r) ^ s = β := hrs
    rw [← h1]
    exact Inputs256f.mulAut_pow_apply_of_apply_eq hx s

@[expose] def QGen3TwE6Inndiag : Prop :=
  ∀ (f : ℕ), 1 ≤ f → ∀ (K : Type) [Field K] [Finite K], Nat.card K = (3 ^ f) ^ 2 →
    ∀ (σ : K ≃+* K), (∀ c, σ c = c ^ (3 ^ f)) → ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 3 →
    ∀ h : ↥(CFSG.HardMathSupport.Timmesfeld.CrossChar.twistedE6InndiagGL K σ), h ^ p = 1 → h ≠ 1 →
      QGenCoprime 3 p (CFSG.HardMathSupport.Timmesfeld.CrossChar.twistedE6InndiagConj K σ h)

theorem qGen3TwE6_of_inndiag (h : QGen3TwE6Inndiag) : QGen3TwE6 := by
  rintro ⟨d, hv⟩ hd3 p hp hp2 hp3 ⟨q, rfl⟩ β hβ
  classical
  have hq3 : q.p = 3 := by simpa using hd3
  obtain ⟨K, _, σ, hK, hσ, ⟨eK⟩⟩ := CFSG.LieType.SeitzGeneration.exists_catEquiv_twistedE6 q hv
  haveI : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ q.prime_p.ne_zero))
  refine qGenCoprime_of_congr eK β ?_
  have hα : orderOf (MulAut.congr eK β) = p := by rw [Inputs256f.orderOf_congr]; exact hβ
  have hβ' : MulAut.congr eK β ^ p = 1 := by rw [← hα]; exact pow_orderOf_eq_one _
  have hβ1' : MulAut.congr eK β ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at hα
    exact hp.one_lt.ne' hα.symm
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, hΘ, -, hker, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form q.prime_p q.exponent_pos K hK σ hσ
  have hK3 : Nat.card K = (3 ^ q.exponent) ^ 2 := by rw [hK, hq3]
  have hσ3 : ∀ c, σ c = c ^ (3 ^ q.exponent) := fun c => by rw [hσ, hq3]
  by_cases hΘβ : Θ (MulAut.congr eK β) = 1
  · have hmem : MulAut.congr eK β ∈
        (CFSG.HardMathSupport.Timmesfeld.CrossChar.twistedE6InndiagConj K σ).range := by
      rw [CFSG.HardMathSupport.Timmesfeld.CrossChar.range_twistedE6InndiagConj, ← hker, MonoidHom.mem_ker]
      exact hΘβ
    obtain ⟨g, hg⟩ := hmem
    have hp1 : g ^ p = 1 :=
      CFSG.HardMathSupport.Timmesfeld.CrossChar.twistedE6InndiagConj_injective Nat.prime_three q.exponent_pos
        hK3 σ hσ3 (by rw [map_pow, hg, hβ', map_one])
    have hg1 : g ≠ 1 := fun h' => hβ1' (by rw [← hg, h', map_one])
    rw [← hg]
    exact h q.exponent q.exponent_pos K hK3 σ hσ3 p hp hp2 hp3 g hp1 hg1
  · have hK' : Nat.card K = 3 ^ (2 * q.exponent) := by rw [hK3, ← pow_mul, mul_comm]
    refine qGenCoprime_of_qGen (Inputs256f.qGen_of_qPerf
      (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.lieCompExport_twE6_field
        (fun q hv => CFSG.HardMathSupport.Solomon.Coordinator.LieComp.isEmpty_cat_alt6 ⟨.twistedE6 q, hv⟩
          (Or.inl rfl)) Nat.prime_three q.exponent_pos hK' σ hσ3 hp hp2 Θ hΘ _ hβ' hΘβ).toComps ?_)
    exact qPerf_twE6_field_three q.exponent_pos hK' σ hσ3 hp hp2 Θ hΘ _ hβ' hΘβ

theorem qGen3Exc_of_residuals (hI : QGen3ExcInndiag) (hT : QGen3TwE6) (hD : QGen3TriD4) : QGen3Exc := by
  rintro ⟨d, hv⟩ hd3 p hp hp2 hp3 hd β hβ
  cases d with
  | E6 q =>
    have h3 : q.p = 3 := by simpa using hd3
    exact qGenCoprime_exc_untw_three hI (τ := .E6) (Or.inr (Or.inr (Or.inl rfl))) (c := TauCeti.LieTypeIndex.E6)
      CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6 (fun q => TauCeti.LieTypeIndex.characteristic_E6 q)
      (fun q _ => TauCeti.LieTypeIndex.valid_E6 q)
      (fun q hv => CFSG.HardMathSupport.Solomon.Coordinator.LieComp.isEmpty_cat_alt6 ⟨.E6 q, hv⟩ (Or.inl rfl))
      q hv h3 hp hp2 hp3 β hβ
  | E7 q =>
    have h3 : q.p = 3 := by simpa using hd3
    exact qGenCoprime_exc_untw_three hI (τ := .E7) (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      (c := TauCeti.LieTypeIndex.E7)
      CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e7 (fun q => TauCeti.LieTypeIndex.characteristic_E7 q)
      (fun q _ => by simp)
      (fun q hv => CFSG.HardMathSupport.Solomon.Coordinator.LieComp.isEmpty_cat_alt6 ⟨.E7 q, hv⟩ (Or.inl rfl))
      q hv h3 hp hp2 hp3 β hβ
  | E8 q =>
    have h3 : q.p = 3 := by simpa using hd3
    exact qGenCoprime_exc_untw_three hI (τ := .E8) (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
      (c := TauCeti.LieTypeIndex.E8)
      CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e8 (fun q => TauCeti.LieTypeIndex.characteristic_E8 q)
      (fun q _ => by simp)
      (fun q hv => CFSG.HardMathSupport.Solomon.Coordinator.LieComp.isEmpty_cat_alt6 ⟨.E8 q, hv⟩ (Or.inl rfl))
      q hv h3 hp hp2 hp3 β hβ
  | F4 q =>
    have h3 : q.p = 3 := by simpa using hd3
    exact qGenCoprime_exc_untw_three hI (τ := .F4) (Or.inr (Or.inl rfl)) (c := TauCeti.LieTypeIndex.F4)
      CFSG.TauCetiBridge.Even.chevalleyBridgesAll.f4 (fun q => TauCeti.LieTypeIndex.characteristic_F4 q)
      (fun q _ => by simp)
      (fun q hv => CFSG.HardMathSupport.Solomon.Coordinator.LieComp.isEmpty_cat_alt6 ⟨.F4 q, hv⟩ (Or.inl rfl))
      q hv h3 hp hp2 hp3 β hβ
  | G2 q =>
    have h3 : q.p = 3 := by simpa using hd3
    exact qGenCoprime_exc_untw_three hI (τ := .G2) (Or.inl rfl) (c := TauCeti.LieTypeIndex.G2)
      CFSG.TauCetiBridge.Even.chevalleyBridgesAll.g2 (fun q => TauCeti.LieTypeIndex.characteristic_G2 q)
      (fun q hq => by
        rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
          TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
        exact ⟨hq rfl, by simp⟩)
      (fun q hv => CFSG.HardMathSupport.Solomon.Coordinator.LieComp.isEmpty_cat_alt6 ⟨.G2 q, hv⟩ (Or.inl rfl))
      q hv h3 hp hp2 hp3 β hβ
  | twistedE6 q => exact hT ⟨.twistedE6 q, hv⟩ hd3 p hp hp2 hp3 ⟨q, rfl⟩ β hβ
  | trialityD4 q => exact hD ⟨.trialityD4 q, hv⟩ hd3 p hp hp2 hp3 ⟨q, rfl⟩ β hβ
  | _ => simp [CFSG.Yardstones.Md42047359a2a.lieFamily] at hd

end ExcField

section ReeGenAbstract

open CFSG.RankThree.PartOne.CTP (FieldAutData IsOuterOfOrder)

variable {S : Type} [Group S]

@[expose] def derivedFixSubgroup (y : MulAut S) : Subgroup S :=
  (commutator ↥(fixSubgroup y)).map (fixSubgroup y).subtype

theorem derivedFixSubgroup_le (y : MulAut S) : derivedFixSubgroup y ≤ fixSubgroup y :=
  Subgroup.map_subtype_le _

theorem derivedFixSubgroup_subgroupOf (y : MulAut S) :
    (derivedFixSubgroup y).subgroupOf (fixSubgroup y) = commutator ↥(fixSubgroup y) :=
  Subgroup.comap_map_eq_self_of_injective (fixSubgroup y).subtype_injective _

theorem ctp_fixedSubgroup_eq_fixSubgroup (y : MulAut S) :
    CFSG.RankThree.PartOne.CTP.fixedSubgroup y = fixSubgroup y :=
  Subgroup.ext fun _ => CFSG.RankThree.PartOne.CTP.mem_fixedSubgroup.trans mem_fixSubgroup.symm

theorem commutator_eq_top_of_simple_nonabelian {G : Type*} [Group G] [IsSimpleGroup G]
    (hnc : ∃ x y : G, x * y ≠ y * x) : commutator G = ⊤ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator G) with h | h
  · exfalso
    obtain ⟨x, y, hxy⟩ := hnc
    rw [_root_.commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer] at h
    exact hxy ((Subgroup.mem_centralizer_iff.1 (h (Subgroup.mem_top x)) y (Subgroup.mem_top y)).symm)
  · exact h

@[expose] def chevFixJoin (q p : ℕ) (E : Subgroup (MulAut S)) : Subgroup S :=
  ⨆ (β : MulAut S) (_ : β ∈ E) (_ : β ≠ 1),
    ⨆ (J : Subgroup S) (_ : Inputs256e.IsChevSub q β J ∧ p ∣ Nat.card (J ⧸ Subgroup.center J)), J

theorem le_chevFixJoin {q p : ℕ} {E : Subgroup (MulAut S)} {β : MulAut S} (hβ : β ∈ E) (hβ1 : β ≠ 1)
    {J : Subgroup S} (hJ : Inputs256e.IsChevSub q β J) (hpJ : p ∣ Nat.card (J ⧸ Subgroup.center J)) :
    J ≤ chevFixJoin q p E :=
  le_iSup_of_le β (le_iSup_of_le hβ (le_iSup_of_le hβ1
    (le_iSup₂_of_le (f := fun (J : Subgroup S)
      (_ : Inputs256e.IsChevSub q β J ∧ p ∣ Nat.card (J ⧸ Subgroup.center J)) => J) J ⟨hJ, hpJ⟩ le_rfl)))

theorem chevFixJoin_mono {q p : ℕ} {E E' : Subgroup (MulAut S)} (h : E ≤ E') :
    chevFixJoin q p E ≤ chevFixJoin q p E' :=
  iSup_le fun _ => iSup_le fun hβ => iSup_le fun hβ1 => iSup₂_le fun _ hJ =>
    le_chevFixJoin (h hβ) hβ1 hJ.1 hJ.2

theorem card_quotient_center_map_mulEquiv {T : Type} [Group T] (e : S ≃* T) (J : Subgroup S) :
    Nat.card (↥(J.map (e : S →* T)) ⧸ Subgroup.center ↥(J.map (e : S →* T))) =
      Nat.card (↥J ⧸ Subgroup.center ↥J) := by
  let eJ : ↥J ≃* ↥(J.map (e : S →* T)) := J.equivMapOfInjective _ e.injective
  exact (Nat.card_congr (QuotientGroup.congr _ _ eJ (Subgroup.map_center_eq eJ)).toEquiv).symm

theorem map_chevFixJoin_le {q p : ℕ} {E : Subgroup (MulAut S)} {n : S}
    (hn : MulAut.conj n ∈ Subgroup.normalizer (E : Set (MulAut S))) :
    (chevFixJoin q p E).map (MulAut.conj n : S →* S) ≤ chevFixJoin q p E := by
  rw [chevFixJoin, Subgroup.map_iSup]
  refine iSup_le fun β => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hβ => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hβ1 => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun J => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hJ => ?_
  have hβ' : MulAut.congr (MulAut.conj n) β ∈ E := by
    rw [CFSG.HardMathSupport.Dickson.DefCharOuter.Export.SuzukiReeTits.mulAut_congr_self]
    exact (Subgroup.mem_normalizer_iff.1 hn β).1 hβ
  have hβ1' : MulAut.congr (MulAut.conj n) β ≠ 1 := fun h =>
    hβ1 ((MulAut.congr (MulAut.conj n)).injective (h.trans (map_one _).symm))
  refine le_chevFixJoin hβ' hβ1' (Inputs256e.isChevSub_map (MulAut.conj n) β hJ.1) ?_
  rw [card_quotient_center_map_mulEquiv]
  exact hJ.2

theorem mem_normalizer_chevFixJoin {q p : ℕ} {E : Subgroup (MulAut S)} {n : S}
    (hn : MulAut.conj n ∈ Subgroup.normalizer (E : Set (MulAut S))) :
    n ∈ Subgroup.normalizer (chevFixJoin q p E : Set S) := by
  have hn' : MulAut.conj n⁻¹ ∈ Subgroup.normalizer (E : Set (MulAut S)) := by
    rw [map_inv]
    exact Subgroup.inv_mem _ hn
  rw [Subgroup.mem_normalizer_iff]
  intro w
  constructor
  · intro hw
    have h := map_chevFixJoin_le (q := q) (p := p) hn (Subgroup.mem_map_of_mem _ hw)
    simpa [MulAut.conj_apply] using h
  · intro hw
    have h := map_chevFixJoin_le (q := q) (p := p) hn' (Subgroup.mem_map_of_mem _ hw)
    simpa [MulAut.conj_apply, mul_assoc] using h

theorem eq_zpowers_conj_sup_zpowers [Finite S] {p : ℕ} (hp : p.Prime) {E : Subgroup (MulAut S)}
    (hEc : Nat.card E = p ^ 2) {k : S} (hkE : MulAut.conj k ∈ E) (hk1 : MulAut.conj k ≠ 1)
    (hkp : MulAut.conj k ^ p = 1) {y : MulAut S} (hyE : y ∈ E) (hyout : ∀ g : S, y ≠ MulAut.conj g) :
    E = Subgroup.zpowers (MulAut.conj k) ⊔ Subgroup.zpowers y := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (MulAut S) := Finite.of_injective (fun e : MulAut S => (e : S → S))
    fun a b h => MulEquiv.ext (congrFun h)
  set A := Subgroup.zpowers (MulAut.conj k) with hA
  set H := A ⊔ Subgroup.zpowers y with hH
  have hHE : H ≤ E := sup_le (Subgroup.zpowers_le.2 hkE) (Subgroup.zpowers_le.2 hyE)
  have hAc : Nat.card A = p := by
    rw [hA, Nat.card_zpowers]
    exact orderOf_eq_prime hkp hk1
  have hAH : A ≤ H := le_sup_left
  have h1 : p ∣ Nat.card H := hAc ▸ Subgroup.card_dvd_of_le hAH
  have h2 : Nat.card H ∣ p ^ 2 := hEc ▸ Subgroup.card_dvd_of_le hHE
  have h3 : Nat.card H ≠ p := by
    intro h
    have hAeq : A = H := Subgroup.eq_of_le_of_card_ge hAH (by rw [h, hAc])
    have hy : y ∈ A := hAeq ▸ (Subgroup.mem_sup_right (Subgroup.mem_zpowers y) : y ∈ H)
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact hyout (k ^ j) (by rw [map_zpow, hj])
  obtain ⟨i, hi, hHi⟩ := (Nat.dvd_prime_pow hp).1 h2
  have hcard : Nat.card H = p ^ 2 := by
    interval_cases i
    · rw [hHi, pow_zero] at h1
      exact absurd (Nat.le_of_dvd one_pos h1) (by have := hp.two_le; omega)
    · rw [hHi, pow_one] at h3
      exact absurd rfl h3
    · exact hHi
  exact (Subgroup.eq_of_le_of_card_ge hHE (by rw [hcard, hEc])).symm

theorem conj_mem_of_eq_zpowers_sup {E : Subgroup (MulAut S)} {k : S} {y : MulAut S}
    (hE : E = Subgroup.zpowers (MulAut.conj k) ⊔ Subgroup.zpowers y) {n : S} (hny : y n = n)
    (hnk : n * k * n⁻¹ ∈ Subgroup.zpowers k) {β : MulAut S} (hβ : β ∈ E) :
    MulAut.conj n * β * (MulAut.conj n)⁻¹ ∈ E := by
  set φ : MulAut S →* MulAut S := (MulAut.conj (MulAut.conj n)).toMonoidHom with hφ
  have hφa : ∀ γ, φ γ = MulAut.conj n * γ * (MulAut.conj n)⁻¹ := fun γ => by
    rw [hφ, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  have hle : E.map φ ≤ E := by
    conv_lhs => rw [hE]
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hnk
      have hc : φ (MulAut.conj k) = MulAut.conj k ^ j := by
        rw [hφa, ← map_inv, ← map_mul, ← map_mul, ← hj, map_zpow]
      rw [hc, hE]
      exact Subgroup.mem_sup_left (Subgroup.zpow_mem_zpowers _ j)
    · rw [Subgroup.zpowers_le]
      have hc : y * MulAut.conj n * y⁻¹ = MulAut.conj n := by
        rw [CFSG.HardMathSupport.Dickson.DefCharOuter.Export.SuzukiReeTits.mul_conj_mul_inv, hny]
      have hφy : φ y = y := by
        rw [hφa]
        calc MulAut.conj n * y * (MulAut.conj n)⁻¹
            = (y * MulAut.conj n * y⁻¹) * y * (MulAut.conj n)⁻¹ := by rw [hc]
          _ = y := by group
      rw [hφy, hE]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  have h := hle (Subgroup.mem_map_of_mem φ hβ)
  rwa [hφa] at h

theorem conj_mem_normalizer_of_eq_zpowers_sup {E : Subgroup (MulAut S)} {k : S} {y : MulAut S}
    (hE : E = Subgroup.zpowers (MulAut.conj k) ⊔ Subgroup.zpowers y) {n : S} (hny : y n = n)
    (hn : n ∈ Subgroup.normalizer (Subgroup.zpowers k : Set S)) :
    MulAut.conj n ∈ Subgroup.normalizer (E : Set (MulAut S)) := by
  have hnk : n * k * n⁻¹ ∈ Subgroup.zpowers k :=
    (Subgroup.mem_normalizer_iff.1 hn k).1 (Subgroup.mem_zpowers k)
  have hn' : n⁻¹ ∈ Subgroup.normalizer (Subgroup.zpowers k : Set S) := Subgroup.inv_mem _ hn
  have hnk' : n⁻¹ * k * n⁻¹⁻¹ ∈ Subgroup.zpowers k :=
    (Subgroup.mem_normalizer_iff.1 hn' k).1 (Subgroup.mem_zpowers k)
  have hny' : y n⁻¹ = n⁻¹ := by rw [map_inv, hny]
  rw [Subgroup.mem_normalizer_iff]
  intro β
  refine ⟨fun hβ => conj_mem_of_eq_zpowers_sup hE hny hnk hβ, fun hβ => ?_⟩
  have h := conj_mem_of_eq_zpowers_sup hE hny' hnk' hβ
  rwa [map_inv, inv_inv, show (MulAut.conj n)⁻¹ * (MulAut.conj n * β * (MulAut.conj n)⁻¹) *
    MulAut.conj n = β by group] at h

theorem fixSubgroup_le_normalizer_sup_derived [Finite S] {p : ℕ} (hp : p.Prime) {y : MulAut S} {k : S}
    (hyk : y k = k) (hk1 : k ≠ 1) (hkp : k ^ p = 1) (hkD : k ∈ derivedFixSubgroup y)
    (hsq : ¬ p ^ 2 ∣ Nat.card (fixSubgroup y)) :
    fixSubgroup y ≤
      (Subgroup.normalizer (Subgroup.zpowers k : Set S) ⊓ fixSubgroup y) ⊔ derivedFixSubgroup y := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set C := fixSubgroup y with hC
  set kC : ↥C := ⟨k, mem_fixSubgroup.2 hyk⟩ with hkC
  have hok : orderOf kC = p := by
    rw [hkC, Subgroup.orderOf_mk]
    exact orderOf_eq_prime hkp hk1
  have hC0 : Nat.card ↥C ≠ 0 := Nat.card_pos.ne'
  have hfact : (Nat.card ↥C).factorization p = 1 := by
    have h1 : p ∣ Nat.card ↥C := hok ▸ orderOf_dvd_natCard kC
    have h1' : 1 ≤ (Nat.card ↥C).factorization p :=
      (hp.pow_dvd_iff_le_factorization hC0).1 (by rwa [pow_one])
    have h2 : ¬ 2 ≤ (Nat.card ↥C).factorization p := fun h =>
      hsq ((hp.pow_dvd_iff_le_factorization hC0).2 h)
    omega
  let P : Sylow p ↥C := Sylow.ofCard (Subgroup.zpowers kC) (by rw [Nat.card_zpowers, hok, hfact, pow_one])
  have hPc : (P : Subgroup ↥C) = Subgroup.zpowers kC := Sylow.coe_ofCard _ _
  set N := (derivedFixSubgroup y).subgroupOf C with hN
  haveI : N.Normal := by
    rw [hN, hC, derivedFixSubgroup_subgroupOf]
    infer_instance
  have hPN : (P : Subgroup ↥C) ≤ N := by
    rw [hPc, Subgroup.zpowers_le]
    exact Subgroup.mem_subgroupOf.2 hkD
  have hF := Sylow.normalizer_sup_eq_top' P hPN
  have key : ∀ m : ↥C, m ∈ Subgroup.normalizer ((P : Subgroup ↥C) : Set ↥C) →
      ∀ h ∈ Subgroup.zpowers k, (m : S) * h * (m : S)⁻¹ ∈ Subgroup.zpowers k := by
    intro m hm h hh
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    have h1 : m * kC ^ j * m⁻¹ ∈ (P : Subgroup ↥C) :=
      (Subgroup.mem_normalizer_iff.1 hm _).1 (by rw [hPc]; exact Subgroup.zpow_mem_zpowers kC j)
    rw [hPc] at h1
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 h1
    refine Subgroup.mem_zpowers_iff.2 ⟨i, ?_⟩
    have h2 := congrArg Subtype.val hi
    simpa [hkC] using h2
  intro g hg
  have hg' : (⟨g, hg⟩ : ↥C) ∈ Subgroup.normalizer ((P : Subgroup ↥C) : Set ↥C) ⊔ N := by
    have h : (⟨g, hg⟩ : ↥C) ∈ (⊤ : Subgroup ↥C) := Subgroup.mem_top _
    rw [← hF] at h
    exact h
  have hmap := Subgroup.mem_map_of_mem C.subtype hg'
  rw [Subgroup.map_sup] at hmap
  have h1 : (Subgroup.normalizer ((P : Subgroup ↥C) : Set ↥C)).map C.subtype ≤
      Subgroup.normalizer (Subgroup.zpowers k : Set S) ⊓ C := by
    rintro _ ⟨m, hm, rfl⟩
    refine Subgroup.mem_inf.2 ⟨?_, m.2⟩
    show (m : S) ∈ Subgroup.normalizer (Subgroup.zpowers k : Set S)
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => key m hm h hh, fun hh => ?_⟩
    have h1 := key m⁻¹ (Subgroup.inv_mem _ hm) _ hh
    simpa [mul_assoc] using h1
  have h2 : N.map C.subtype ≤ derivedFixSubgroup y := by
    rw [hN, Subgroup.subgroupOf_map_subtype]
    exact inf_le_left
  exact (sup_le_sup h1 h2) hmap

theorem top_le_chevFixJoin_of_fieldAutData [Finite S] [IsSimpleGroup S] (hnab : ∃ a b : S, a * b ≠ b * a)
    {q p : ℕ} (hp : p.Prime) (hd : FieldAutData S p)
    (hno : ∀ F : Subgroup S, IsElemAbelian p F → Nat.card F = p ^ 2 → False)
    (hD : ∀ y : MulAut S, IsOuterOfOrder p y →
      Inputs256e.IsChevSub q y (derivedFixSubgroup y) ∧
        p ∣ Nat.card (↥(derivedFixSubgroup y) ⧸ Subgroup.center ↥(derivedFixSubgroup y)) ∧
        (∀ g ∈ fixSubgroup y, g ^ p = 1 → g ∈ derivedFixSubgroup y) ∧
        ¬ p ^ 2 ∣ Nat.card (fixSubgroup y))
    (B : Subgroup (MulAut S)) (hB : IsElemAbelian p B) (hBc : p ^ 2 ≤ Nat.card B) :
    (⊤ : Subgroup S) ≤ chevFixJoin q p B := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hinj := CFSG.RankThree.PartOne.CTP.conj_injective_of_simple hnab
  haveI : Finite (MulAut S) := Finite.of_injective (fun e : MulAut S => (e : S → S))
    fun a b h => MulEquiv.ext (congrFun h)
  have hBp : IsPGroup p B := fun g => ⟨1, Subtype.ext (by simpa using hB.2 g g.2)⟩
  obtain ⟨n, hn⟩ := hBp.exists_card_eq
  have hn2 : 2 ≤ n := by
    by_contra h
    have h1 : p ^ n ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos (by omega)
    have h2 : p ^ 2 ≤ p ^ 1 := (hn ▸ hBc).trans h1
    have h3 : p ^ 1 < p ^ 2 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    omega
  obtain ⟨E₀, hE₀⟩ := Sylow.exists_subgroup_card_pow_prime p (n := 2) (G := ↥B)
    (by rw [hn]; exact pow_dvd_pow p hn2)
  set E := E₀.map B.subtype with hEdef
  have hEB : E ≤ B := Subgroup.map_subtype_le E₀
  have hEc : Nat.card E = p ^ 2 := by rw [hEdef, Subgroup.card_map_of_injective B.subtype_injective, hE₀]
  have hEel : IsElemAbelian p E := hB.mono hEB
  refine le_trans ?_ (chevFixJoin_mono hEB)
  haveI hEel' : CFSG.IsElementaryAbelian p E :=
    { is_comm := hEel.1.is_comm
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
        Subtype.ext (by simpa using hEel.2 x x.2) }
  obtain ⟨k, hk1, hkE⟩ := hd.out_rank E hEel' hEc
  obtain ⟨σ, hσE, hσinn⟩ : ∃ σ ∈ E, ∀ g : S, σ ≠ MulAut.conj g := by
    by_contra h
    push Not at h
    exact CFSG.LieType.SeitzGeneration.false_of_inner_plane_of_no_plane hinj hno hEel hEc
      (fun φ hφ => let ⟨g, hg⟩ := h φ hφ; ⟨g, hg.symm⟩)
  have hcommE : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb => hEel.comm ha hb
  have hckp : MulAut.conj k ^ p = 1 := hEel.2 _ hkE
  have hkp : k ^ p = 1 := hinj (by rw [map_pow, map_one]; exact hckp)
  have hck1 : MulAut.conj k ≠ 1 := fun h => hk1 (hinj (h.trans (map_one _).symm))
  set W := chevFixJoin q p E with hW
  have hCle : ∀ y ∈ E, (∀ g : S, y ≠ MulAut.conj g) →
      IsOuterOfOrder p y ∧ y k = k ∧ fixSubgroup y ≤ Subgroup.normalizer (W : Set S) := by
    intro y hy hyout
    have hy1 : y ≠ 1 := fun h => hyout 1 (by rw [h, map_one])
    have hyo : IsOuterOfOrder p y := ⟨orderOf_eq_prime (hEel.2 y hy) hy1, hyout⟩
    have hyk : y k = k := CFSG.RankThree.PartOne.CTP.apply_eq_of_commute_conj hinj (hcommE y hy _ hkE)
    obtain ⟨hJ, hpJ, hpel, hsq⟩ := hD y hyo
    have hkD : k ∈ derivedFixSubgroup y := hpel k (mem_fixSubgroup.2 hyk) hkp
    have hEeq := eq_zpowers_conj_sup_zpowers hp hEc hkE hck1 hckp hy hyout
    refine ⟨hyo, hyk, (fixSubgroup_le_normalizer_sup_derived hp hyk hk1 hkp hkD hsq).trans (sup_le ?_ ?_)⟩
    · rintro m ⟨hmN, hmC⟩
      exact mem_normalizer_chevFixJoin (conj_mem_normalizer_of_eq_zpowers_sup hEeq (mem_fixSubgroup.1 hmC) hmN)
    · exact (le_chevFixJoin hy hy1 hJ hpJ).trans Subgroup.le_normalizer
  obtain ⟨hσo, hkσ, hσC⟩ := hCle σ hσE hσinn
  have hσ'E : σ * MulAut.conj k ∈ E := E.mul_mem hσE hkE
  have hσ'inn : ∀ g : S, σ * MulAut.conj k ≠ MulAut.conj g := fun g h =>
    hσinn (g * k⁻¹) (by rw [map_mul, map_inv, ← h, mul_assoc, mul_inv_cancel, mul_one])
  obtain ⟨hσ'o, -, hσ'C⟩ := hCle _ hσ'E hσ'inn
  have hkσC : k ∈ CFSG.RankThree.PartOne.CTP.fixedSubgroup σ := hkσ
  have hpdvd : p ∣ Nat.card (CFSG.RankThree.PartOne.CTP.fixedSubgroup σ) := by
    have hord : orderOf k = p := orderOf_eq_prime hkp hk1
    have h1 : orderOf (⟨k, hkσC⟩ : CFSG.RankThree.PartOne.CTP.fixedSubgroup σ) ∣
        Nat.card (CFSG.RankThree.PartOne.CTP.fixedSubgroup σ) := orderOf_dvd_natCard _
    rwa [Subgroup.orderOf_mk, hord] at h1
  have hne : CFSG.RankThree.PartOne.CTP.fixedSubgroup σ ≠
      CFSG.RankThree.PartOne.CTP.fixedSubgroup (σ * MulAut.conj k) := by
    intro heq
    apply hk1
    refine hd.center σ hσo hpdvd k hkσC fun z hz => ?_
    have hz' : z ∈ CFSG.RankThree.PartOne.CTP.fixedSubgroup (σ * MulAut.conj k) := heq ▸ hz
    have h1 : σ z = z := hz
    have h2 : (σ * MulAut.conj k) z = z := hz'
    have h3 : σ (k * z * k⁻¹) = k * z * k⁻¹ := by rw [map_mul, map_mul, map_inv, hkσ, h1]
    have h4 : σ (k * z * k⁻¹) = z := by simpa [MulAut.mul_apply, MulAut.conj_apply] using h2
    rw [h4] at h3
    calc k * z = k * z * k⁻¹ * k := by group
      _ = z * k := by rw [← h3]
  have hgen : Subgroup.closure ((CFSG.RankThree.PartOne.CTP.fixedSubgroup σ : Set S) ∪
      (CFSG.RankThree.PartOne.CTP.fixedSubgroup (σ * MulAut.conj k) : Set S)) = ⊤ := by
    rcases hd.gen σ _ hσo hσ'o hne with h | h
    · exact h
    · exact absurd hpdvd h
  have htop : Subgroup.normalizer (W : Set S) = ⊤ := by
    rw [eq_top_iff, ← hgen, Subgroup.closure_le]
    rintro x (hx | hx)
    · rw [SetLike.mem_coe, ctp_fixedSubgroup_eq_fixSubgroup] at hx
      exact hσC hx
    · rw [SetLike.mem_coe, ctp_fixedSubgroup_eq_fixSubgroup] at hx
      exact hσ'C hx
  haveI hWn : W.Normal := Subgroup.normalizer_eq_top_iff.1 htop
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal W with hWb | hWt
  · exfalso
    obtain ⟨hJ, -, -, -⟩ := hD σ hσo
    have hσ1 : σ ≠ 1 := fun h => hσinn 1 (by rw [h, map_one])
    haveI := hJ.2.1.2
    obtain ⟨x, hx⟩ := exists_ne (1 : ↥(derivedFixSubgroup σ) ⧸ Subgroup.center ↥(derivedFixSubgroup σ))
    obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective x
    have hd1 : (d : S) ≠ 1 := fun h => hx (by rw [show d = 1 from Subtype.ext h]; rfl)
    have hdW : (d : S) ∈ W := le_chevFixJoin hσE hσ1 hJ (hD σ hσo).2.1 d.2
    rw [hWb, Subgroup.mem_bot] at hdW
    exact hd1 hdW
  · rw [hWt]

end ReeGenAbstract

section ReeGen37

open CFSG.LieType.Ree CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.RankThree.PartOne.CTP (FieldAutData IsOuterOfOrder)


theorem exists_fixSubgroup_equiv_reeGamma_zero (hv : (TauCeti.LieTypeIndex.reeG2 3).Valid)
    (y : MulAut (CFSG.LieType.SeitzGeneration.Cat ⟨.reeG2 3, hv⟩)) (hy : IsOuterOfOrder 7 y) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k) (_ : CharP k ReeTag.G2.prime),
      Nat.card k = 3 ^ (2 * 0 + 1) ∧ Nonempty (↥(fixSubgroup y) ≃* ReeTag.G2.reeGamma k 0) := by
  obtain ⟨X, _, _, _, hm1, hX, ⟨e⟩⟩ := CFSG.HardMathSupport.Curtis.Coordinator.SeitzCyc.exists_reeG2_model
    (K := CFSG.LieType.SeitzGeneration.Cat ⟨.reeG2 3, hv⟩) ⟨hv, ⟨MulEquiv.refl _⟩⟩
  set y' := MulAut.congr e y with hy'
  have hy'o : orderOf y' = 7 :=
    (orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective y).trans hy.1
  have hy'p : y' ^ 7 = 1 := by rw [← hy'o]; exact pow_orderOf_eq_one y'
  have hin : y' ∉ (MulAut.conj : ReeTag.G2.reeGamma X 3 →* MulAut (ReeTag.G2.reeGamma X 3)).range := by
    rintro ⟨g, hg⟩
    apply hy.2 (e.symm g)
    ext x
    have h1 := congrArg (fun φ : MulAut (ReeTag.G2.reeGamma X 3) => φ (e x)) hg
    simp only [hy', MulAut.conj_apply, MulAut.congr_apply] at h1
    apply e.injective
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    simpa using h1.symm
  obtain ⟨-, δ, σ, hσ, hδ, -⟩ := CFSG.HardMathSupport.Lang.Coordinator.small_Ree_odd_prime_field_descent 3 hm1 X
    hX (by norm_num) (by norm_num) y' hy'p hin
  obtain ⟨b, hbp, hbcard, hchar, ⟨eC⟩⟩ :=
    CFSG.HardMathSupport.Curtis.Coordinator.SeitzCyc.reeG2_fixed_data hX (by norm_num) (by norm_num) hσ
  obtain rfl : b = 0 := by omega
  set σh := ReeTag.G2.reeGammaFieldAut X 3 σ with hσh
  have hy'eq : y' = MulAut.congr δ⁻¹ σh := by
    rw [CFSG.HardMathSupport.Dickson.DefCharOuter.Export.SuzukiReeTits.mulAut_congr_self, ← hδ]
    group
  let e1 : ↥(fixSubgroup y) ≃* ↥(fixSubgroup y') :=
    ((fixSubgroup y).equivMapOfInjective (e : _ →* _) e.injective).trans
      (MulEquiv.subgroupCongr (Inputs256e.fixSubgroup_congr e y).symm)
  let e2 : ↥(fixSubgroup y') ≃* ↥(fixSubgroup σh) :=
    (MulEquiv.subgroupCongr (by rw [hy'eq, Inputs256e.fixSubgroup_congr])).trans
      ((fixSubgroup σh).equivMapOfInjective ((δ⁻¹ : MulAut _) : _ →* _) (δ⁻¹ : MulAut _).injective).symm
  let e3 : ↥(fixSubgroup σh) ≃* ReeTag.G2.reeGamma (fixSubfield σ) 0 :=
    (MulEquiv.subgroupCongr
      (CFSG.HardMathSupport.Dickson.DefCharOuter.Export.SuzukiReeTits.fixSubgroup_eq_fixSub _)).trans eC
  exact ⟨fixSubfield σ, inferInstance, inferInstance, hchar, hbcard, ⟨e1.trans (e2.trans e3)⟩⟩

theorem derivedFixSubgroup_data_ree37 (hv : (TauCeti.LieTypeIndex.reeG2 3).Valid)
    (y : MulAut (CFSG.LieType.SeitzGeneration.Cat ⟨.reeG2 3, hv⟩)) (hy : IsOuterOfOrder 7 y) :
    Inputs256e.IsChevSub 3 y (derivedFixSubgroup y) ∧
      7 ∣ Nat.card (↥(derivedFixSubgroup y) ⧸ Subgroup.center ↥(derivedFixSubgroup y)) ∧
      (∀ g ∈ fixSubgroup y, g ^ 7 = 1 → g ∈ derivedFixSubgroup y) ∧ ¬ 7 ^ 2 ∣ Nat.card (fixSubgroup y) := by
  obtain ⟨k, _, _, _, hk, ⟨eC⟩⟩ := exists_fixSubgroup_equiv_reeGamma_zero hv y hy
  set C := fixSubgroup y with hC
  set R := ReeTag.G2.reeGamma k 0 with hR
  obtain ⟨h1512, -, hidx, -, -, -⟩ := CFSG.ComponentClassification.LiteratureLocal.G2_reeGamma_zero_structure hk
  obtain ⟨hsR, hncR, -, -, -, -⟩ :=
    CFSG.ComponentClassification.CatalogueBSmallRee.small_Ree_whole_group_p_components 0 k hk
  have hchev := CFSG.HardMathSupport.Dickson.DefCharOuter.Export.SuzukiReeTits.isChevSimple_commutator_reeGamma
    0 k hk
  let eD : ↥(commutator ↥C) ≃* ↥(commutator R) :=
    ((commutator ↥C).equivMapOfInjective eC.toMonoidHom eC.injective).trans
      (MulEquiv.subgroupCongr (CFSG.ComponentClassification.CatalogueBSmallRee.map_commutator_mulEquiv eC))
  let eMD : ↥(commutator ↥C) ≃* ↥(derivedFixSubgroup y) :=
    (commutator ↥C).equivMapOfInjective C.subtype C.subtype_injective
  let eM : ↥(derivedFixSubgroup y) ≃* ↥(commutator R) := eMD.symm.trans eD
  haveI : IsSimpleGroup ↥(commutator R) := hsR
  haveI hsD : IsSimpleGroup ↥(derivedFixSubgroup y) := eM.isSimpleGroup
  have hncD : ∃ a b : ↥(derivedFixSubgroup y), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hncR
    exact ⟨eM.symm a, eM.symm b, fun h => hab (by simpa using congrArg eM h)⟩
  have hZD : Subgroup.center ↥(derivedFixSubgroup y) = ⊥ :=
    CFSG.HardMathSupport.Dickson.DefCharOuter.Export.SuzukiReeTits.center_eq_bot_of_simple hncD
  let eZ : (↥(derivedFixSubgroup y) ⧸ Subgroup.center ↥(derivedFixSubgroup y)) ≃* ↥(derivedFixSubgroup y) :=
    (QuotientGroup.quotientMulEquivOfEq hZD).trans QuotientGroup.quotientBot
  have hcardR' : Nat.card ↥(commutator R) = 504 := by
    have h := Subgroup.card_mul_index (commutator R)
    rw [hidx, h1512] at h
    omega
  have hcardC : Nat.card ↥C = 1512 := by rw [Nat.card_congr eC.toEquiv, h1512]
  have hcardC' : Nat.card ↥(commutator ↥C) = 504 := by rw [Nat.card_congr eD.toEquiv, hcardR']
  have hidxC : (commutator ↥C).index = 3 := by
    have h := Subgroup.card_mul_index (commutator ↥C)
    rw [hcardC', hcardC] at h
    omega
  refine ⟨⟨?_, ⟨commutator_eq_top_of_simple_nonabelian hncD, eZ.isSimpleGroup⟩, ?_⟩, ?_, ?_, ?_⟩
  · refine IsSubnormal.step (derivedFixSubgroup_le y) ?_ (IsSubnormal.refl _)
    rw [derivedFixSubgroup_subgroupOf]
    infer_instance
  · exact CFSG.HardMathSupport.Solomon.Coordinator.LieComp.isChevSimple_congr (eM.symm.trans eZ.symm) hchev
  · rw [Nat.card_congr (eZ.trans eM).toEquiv, hcardR']
    norm_num
  · intro g hg hg7
    set gC : ↥C := ⟨g, hg⟩ with hgC
    have h1 : orderOf (QuotientGroup.mk' (commutator ↥C) gC) ∣ 3 := by
      have h0 : orderOf (QuotientGroup.mk' (commutator ↥C) gC) ∣ (commutator ↥C).index :=
        orderOf_dvd_natCard _
      rw [hidxC] at h0
      exact h0
    have h2 : orderOf (QuotientGroup.mk' (commutator ↥C) gC) ∣ 7 := by
      refine orderOf_dvd_of_pow_eq_one ?_
      rw [← map_pow, show gC ^ 7 = 1 from Subtype.ext (by simpa [hgC] using hg7), map_one]
    have h3 : orderOf (QuotientGroup.mk' (commutator ↥C) gC) = 1 := by
      have h4 := Nat.dvd_gcd h1 h2
      have h5 : Nat.gcd 3 7 = 1 := by norm_num
      rw [h5, Nat.dvd_one] at h4
      exact h4
    rw [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h3
    exact ⟨gC, h3, rfl⟩
  · rw [hcardC]
    norm_num

theorem reeGen37_holds : ReeGen37 := by
  intro hv B hB hBc
  obtain ⟨X, _, _, _, hm1, hX, ⟨e⟩⟩ := CFSG.HardMathSupport.Curtis.Coordinator.SeitzCyc.exists_reeG2_model
    (K := CFSG.LieType.SeitzGeneration.Cat ⟨.reeG2 3, hv⟩) ⟨hv, ⟨MulEquiv.refl _⟩⟩
  have := (CFSG.ComponentClassification.CatalogueBSmallRee.reeGamma_G2_simple hm1 X hX).2.1
  have hnc := (CFSG.ComponentClassification.CatalogueBSmallRee.reeGamma_G2_simple hm1 X hX).2.2
  haveI hsimple : IsSimpleGroup (CFSG.LieType.SeitzGeneration.Cat ⟨.reeG2 3, hv⟩) := MulEquiv.isSimpleGroup e
  haveI hfin : Finite (CFSG.LieType.SeitzGeneration.Cat ⟨.reeG2 3, hv⟩) := Finite.of_equiv _ e.symm.toEquiv
  have hnab : ∃ a b : CFSG.LieType.SeitzGeneration.Cat ⟨.reeG2 3, hv⟩, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnc
    exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩
  have hd : FieldAutData (CFSG.LieType.SeitzGeneration.Cat ⟨.reeG2 3, hv⟩) 7 :=
    (CFSG.HardMathSupport.Curtis.Coordinator.SeitzCyc.fieldAutData_reeG2
      CFSG.LocalAnalysis.SubfieldPairReeG2.subfieldPairReeG2_of_pieces (by norm_num) (by norm_num) hm1
      hX).of_mulEquiv e (by norm_num)
  exact top_le_chevFixJoin_of_fieldAutData hnab (by norm_num) hd
    (fun F hF hFc => CFSG.LieType.SeitzGeneration.no_plane_cat_reeG2 hv (by norm_num) (by norm_num) F hF hFc)
    (fun y hy => derivedFixSubgroup_data_ree37 hv y hy) B hB (by norm_num; exact hBc)

end ReeGen37

section Lang3

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256j
open scoped Pointwise


variable {τ : Tag} {K : Type} [Field K] [Finite K] {ℓ : ℕ}

variable {p₀ : ℕ} (S : LangSetup τ (AlgebraicClosure K) p₀)

section SuN3

open Matrix CFSG.RankThree.Classical CFSG.RankThree.Classical2 CFSG.SectionRank.OddCover
open CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LieType.Steinberg.Adjoint
open scoped MatrixGroups commutatorElement

private theorem compCharElem_of_unitary_frame_three (hK : ringChar K = ℓ) (hℓp : ℓ.Prime) (hℓ3 : 3 ≤ ℓ)
    {ta : Fin τ.rank → (AlgebraicClosure K)ˣ} (hT : rootDiagUnit τ ta ∈ S.D.torus)
    (i : KernelComponent (rootCharHom ta)) {ν : ℕ} (hν : 3 ≤ ν)
    {ψ : SL(ν, AlgebraicClosure K) →* ModGL τ (AlgebraicClosure K)} {σ : Fin ν → Fin ν → Fin τ.rank → ℤ}
    (hψ : IsSLFrame ψ σ) (hΨ : componentRoots (rootCharHom ta) i = frameRoots σ) (π : Equiv.Perm (Fin ν))
    (hπ : ∀ a b, a ≠ b → (S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
      (componentRoots (rootCharHom ta) i)] (σ a b) = σ (π b) (π a)) :
    CompCharElem S ℓ ta i := by
  classical
  set L := AlgebraicClosure K with hLdef
  obtain ⟨hs0, -, -⟩ := outer_componentOrbitLength_spec S hT i
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom ta) i) with hsdef
  obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : CharP L r := hchar
  have hrℓ : r = ℓ := by
    have hLℓ : ringChar L = ℓ := by
      rw [CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ringChar_algebraicClosure, hK]
    rw [← hLℓ]
    exact (ringChar.eq L r).symm
  obtain ⟨σQ, hσQ⟩ := exists_ringEquiv_frob (L := L) r (e * s)
  have hσc : ∀ c, σQ c = c ^ (r ^ (e * s)) := fun c => by
    have h1 : σQ c = iterateFrobenius L r (e * s) c := by
      rw [← hσQ]
      rfl
    rw [h1, iterateFrobenius_def]
  have hQ : S.D.q ^ s = r ^ (e * s) := by rw [hq, ← pow_mul]
  set Fs : ModGL τ L →* ModGL τ L := iterHom S.D.step s with hFs
  choose! ε hε using fun (a b : Fin ν) (hab : a ≠ b) => hψ.transv a b hab
  have hπne : ∀ a b : Fin ν, a ≠ b → π b ≠ π a := fun a b hab => (π.injective.ne hab).symm
  have hstepU : ∀ a b : Fin ν, a ≠ b → ∃ μ : Lˣ, ∀ c : L,
      Fs (pinnedX τ L (σ a b) c) = pinnedX τ L (σ (π b) (π a)) ((μ : L) * σQ c) := by
    intro a b hab
    obtain ⟨μ, hμ0, hμ⟩ := iter_step_pinnedX S s (hψ.isRoot a b hab)
    refine ⟨Units.mk0 μ hμ0, fun c => ?_⟩
    rw [hFs, iterHom_eq_iterate, hμ, hπ a b hab, hσc, ← hQ]
    rfl
  choose! μ hμ using hstepU
  set β : Fin ν → Fin ν → Lˣ := fun a b =>
    μ a b * ε a b ^ (r ^ (e * s)) * (ε (π b) (π a))⁻¹ with hβ
  have hkey : ∀ (a b : Fin ν) (hab : a ≠ b) (t : L),
      Fs (ψ (Matrix.SpecialLinearGroup.transvection hab t)) =
        ψ (Matrix.SpecialLinearGroup.transvection (hπne a b hab) ((β a b : L) * σQ t)) := by
    intro a b hab t
    rw [hε a b hab t, hμ a b hab, hε (π b) (π a) (hπne a b hab)]
    congr 1
    rw [map_mul, hσc (ε a b : L), hβ]
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]
    have h0 : (ε (π b) (π a) : L) ≠ 0 := Units.ne_zero _
    field_simp
    ring
  have hcoc : ∀ a b c : Fin ν, a ≠ b → b ≠ c → a ≠ c → β a c = -(β a b * β b c) := by
    intro a b c hab hbc hac
    have hcomm := Matrix.SpecialLinearGroup.commutatorElement_transvection hab hbc hac (1 : L) 1
    rw [mul_one] at hcomm
    have h1 := congrArg (fun X => Fs (ψ X)) hcomm
    simp only [map_commutatorElement] at h1
    rw [hkey a b hab, hkey b c hbc, hkey a c hac, map_one, mul_one, mul_one, mul_one,
      ← map_commutatorElement ψ,
      commutator_transvection_rev (hπne a b hab) (hπne b c hbc) (hπne a c hac),
      hε _ _ (hπne a c hac), hε _ _ (hπne a c hac)] at h1
    have h2 := pinnedX_injective τ L _ h1
    have h0 : (ε (π c) (π a) : L) ≠ 0 := Units.ne_zero _
    apply Units.ext
    have h3 := mul_left_cancel₀ h0 h2
    rw [Units.val_neg, Units.val_mul]
    exact h3.symm
  obtain ⟨d, hd⟩ := exists_units_of_cocycle hν β hcoc
  set M : GL (Fin ν) L := diagHom ν d * (permGL π : GL (Fin ν) L)⁻¹ with hMdef
  obtain ⟨B, hB⟩ := exists_specialLinear_conj_eq (n := ν) (by omega) M
  have hBconj : ∀ (a b : Fin ν) (hab : a ≠ b) (u : L),
      B * Matrix.SpecialLinearGroup.transvection (hπne a b hab) u * B⁻¹ =
        Matrix.SpecialLinearGroup.transvection (Ne.symm hab) ((d b : L) * u * ((d a)⁻¹ : Lˣ)) := by
    intro a b hab u
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.transvection_coe, Matrix.SpecialLinearGroup.transvection_coe, hB]
    have hM : ∀ Y : Matrix (Fin ν) (Fin ν) L, (M : Matrix (Fin ν) (Fin ν) L) * Y *
        (↑M⁻¹ : Matrix (Fin ν) (Fin ν) L) = (diagHom ν d : Matrix (Fin ν) (Fin ν) L) *
          ((↑(permGL π : GL (Fin ν) L)⁻¹ : Matrix (Fin ν) (Fin ν) L) * Y *
            ((permGL π : GL (Fin ν) L) : Matrix (Fin ν) (Fin ν) L)) *
              (↑(diagHom ν d)⁻¹ : Matrix (Fin ν) (Fin ν) L) := by
      intro Y
      simp only [hMdef, _root_.mul_inv_rev, inv_inv, Units.val_mul, Matrix.mul_assoc]
    rw [hM, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Units.inv_mul,
      permGL_inv_mul_single_mul, diagHom_mul_one_add_single_mul d (Ne.symm hab) u]
  have hstd : ∀ X : SL(ν, L), ψ B * Fs (ψ X) * (ψ B)⁻¹ = ψ (stdUnitary σQ.toRingHom X) := by
    have h : (MulAut.conj (ψ B)).toMonoidHom.comp (Fs.comp ψ) =
        ψ.comp (stdUnitary σQ.toRingHom) := by
      refine MonoidHom.eq_of_eqOn_dense
        (CFSG.LinearGroups.special_linear_elementary_generation (n := ν) (K := L)) ?_
      rintro _ ⟨a, b, hab, t, rfl⟩
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [hkey a b hab t, ← map_mul, ← map_inv, ← map_mul, hBconj a b hab,
        stdUnitary_transvection]
      congr 2
      rw [hd a b hab]
      simp only [Units.val_neg, Units.val_mul, Units.val_inv_eq_inv_val,
        RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
      have h0 : (d a : L) ≠ 0 := Units.ne_zero _
      have h0' : (d b : L) ≠ 0 := Units.ne_zero _
      have e1 : (d b : L) * (-((d a : L) * (d b : L)⁻¹) * σQ t) * (d a : L)⁻¹ =
          -(σQ t) * ((d b : L) * (d b : L)⁻¹) * ((d a : L) * (d a : L)⁻¹) := by ring
      rw [e1, mul_inv_cancel₀ h0', mul_inv_cancel₀ h0, mul_one, mul_one]
    intro X
    have := DFunLike.congr_fun h X
    simpa [MulAut.conj_apply] using this
  have hψS : ∀ X, ψ X ∈ rootSpan τ L (componentRoots (rootCharHom ta) i) := fun X => by
    rw [hΨ, ← hψ.range]
    exact ⟨X, rfl⟩
  have hy₁ : ψ B ∈ rootSpan τ L (kernelRoots (rootCharHom ta)) :=
    rootSpan_mono (fun γ hγ => hγ.1) (hψS B)
  obtain ⟨z, hz, hnorm⟩ := exists_lang_mul_T S hT hs0 hy₁
  have hconj : ∀ X : SL(ν, L), Fs (z * ψ X * z⁻¹) = z * ψ (stdUnitary σQ.toRingHom X) * z⁻¹ := by
    intro X
    rw [← hstd X, map_mul, map_mul, map_inv, hz]
    group
  have hker : ψ.ker ≠ ⊤ := by
    intro h
    have h01 : (⟨0, by omega⟩ : Fin ν) ≠ ⟨1, by omega⟩ := by simp
    have h1 : Matrix.SpecialLinearGroup.transvection h01 (1 : L) ∈ ψ.ker := by
      rw [h]
      exact Subgroup.mem_top _
    rw [MonoidHom.mem_ker, hε _ _ h01, mul_one, ← pinnedX_zero τ L (σ _ _)] at h1
    exact Units.ne_zero _ (pinnedX_injective τ L _ h1)
  have hkerc : ∀ X : SL(ν, L), ψ X = 1 → X ∈ Subgroup.center SL(ν, L) := fun X hX =>
    mem_center_SL_of_commute hν ψ hker fun Y => by rw [hX, one_mul, mul_one]
  set C := CFSG.RankThree.Classical2.fixSubgroup (stdUnitaryEquiv (ν := ν) σQ) with hCdef
  have hCmem : ∀ X : SL(ν, L), X ∈ C ↔ stdUnitary σQ.toRingHom X = X := fun X => by
    rw [hCdef, CFSG.RankThree.Classical2.mem_fixSubgroup, stdUnitaryEquiv_apply]
  obtain ⟨-, hqsC, -⟩ := stdUnitary_fixSubgroup (ν := ν) hr (Nat.mul_pos he hs0) σQ hσc hν
  have hne : (ν, r ^ (e * s)) ≠ (3, 2) := by
    intro h
    have h2 : r ^ (e * s) = 2 := congrArg Prod.snd h
    have h3 : r ≤ r ^ (e * s) := Nat.le_self_pow (Nat.mul_pos he hs0).ne' r
    omega
  have hCperf : ⁅C, C⁆ = C := Subgroup.isPerfect_iff.1 (hqsC hne).1
  set θ : SL(ν, L) →* ModGL τ L := (MulAut.conj z).toMonoidHom.comp ψ with hθdef
  have hθ : ∀ X, θ X = z * ψ X * z⁻¹ := fun X => rfl
  refine ⟨C.map θ, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨X, -, rfl⟩
    rw [hθ]
    exact (hnorm i _).1 (hψS X)
  · rintro _ ⟨X, hX, rfl⟩
    show Fs (θ X) = θ X
    rw [hθ, hconj, (hCmem X).1 hX]
  · rw [← Subgroup.map_commutator, hCperf]
  · intro y hy hyF ⟨n, hn⟩
    have hy' : z⁻¹ * y * z ∈ rootSpan τ L (componentRoots (rootCharHom ta) i) := (hnorm i _).2 (by
      have e : z * (z⁻¹ * y * z) * z⁻¹ = y := by group
      rw [e]
      exact hy)
    rw [hΨ, ← hψ.range] at hy'
    obtain ⟨X, hX⟩ := hy'
    have hyX : y = θ X := by rw [hθ, hX]; group
    have hrℓ' : ℓ = r := hrℓ.symm
    have hcX : X ^ ℓ ^ n ∈ Subgroup.center SL(ν, L) := by
      refine hkerc _ ?_
      have h1 : θ (X ^ ℓ ^ n) = 1 := by rw [map_pow, ← hyX, hn]
      rw [hθ] at h1
      have h2 : ψ (X ^ ℓ ^ n) = z⁻¹ * (z * ψ (X ^ ℓ ^ n) * z⁻¹) * z := by group
      rw [h2, h1]
      group
    obtain ⟨N, hN, hcN⟩ := exists_coprime_pow_of_mem_center_SL hℓp hK (by omega) hcX
    have hcopy : Nat.Coprime N (orderOf y) :=
      Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hn) (Nat.Coprime.pow_right n hN)
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcopy
    set X₁ := (X ^ N) ^ m with hX₁
    have hyX₁ : y = θ X₁ := by
      rw [hX₁, map_pow, map_pow, ← hyX, hm]
    have hX₁n : X₁ ^ ℓ ^ n = 1 := by
      rw [hX₁, ← pow_mul, ← pow_mul, show N * (m * ℓ ^ n) = ℓ ^ n * N * m by ring, pow_mul, pow_mul, hcN,
        one_pow]
    set c₁ := stdUnitary σQ.toRingHom X₁ * X₁⁻¹ with hc₁
    have hc₁c : c₁ ∈ Subgroup.center SL(ν, L) := by
      refine hkerc _ ?_
      have h1 : Fs (θ X₁) = θ X₁ := by rw [← hyX₁]; exact hyF
      rw [hθ, hconj] at h1
      have h2 : ψ (stdUnitary σQ.toRingHom X₁) = ψ X₁ := by
        have := congrArg (fun g => z⁻¹ * g * z) h1
        simpa [mul_assoc] using this
      rw [hc₁, map_mul, map_inv, h2, mul_inv_cancel]
    have hc₁n : c₁ ^ ℓ ^ n = 1 := by
      have hcomm : Commute c₁ X₁ := (Subgroup.mem_center_iff.1 hc₁c X₁).symm
      have e1 : stdUnitary σQ.toRingHom X₁ = c₁ * X₁ := by rw [hc₁, inv_mul_cancel_right]
      have h1 : (stdUnitary σQ.toRingHom X₁) ^ ℓ ^ n = 1 := by rw [← map_pow, hX₁n, map_one]
      rw [e1, hcomm.mul_pow, hX₁n, mul_one] at h1
      exact h1
    haveI : Fact ℓ.Prime := ⟨hℓp⟩
    haveI : CharP L ℓ := hrℓ ▸ hchar
    have hc₁1 : c₁ = 1 := eq_one_of_mem_center_SL_charPow (by omega) hc₁c hc₁n
    have hX₁C : X₁ ∈ C := by
      rw [hCmem]
      exact mul_inv_eq_one.1 hc₁1
    exact ⟨X₁, hX₁C, hyX₁.symm⟩

private theorem compCharElem_suN_three (hK : ringChar K = ℓ) (hℓp : ℓ.Prime) (hℓ3 : 3 ≤ ℓ) {p : ℕ} (hp : p.Prime)
    {ta : Fin τ.rank → (AlgebraicClosure K)ˣ} (hT : rootDiagUnit τ ta ∈ S.D.torus) (hap : ∀ i, ta i ^ p = 1)
    (h1 : rootDiagUnit τ ta ≠ 1) (i : KernelComponent (rootCharHom ta))
    (hkind : twistKind S.ρ (rootCharHom ta) i = .suN) :
    CompCharElem S ℓ ta i := by
  classical
  have hℓL : ringChar (AlgebraicClosure K) ≠ p :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ringChar_ne_of_pow_eq_one hp hap h1
  have hpL : ((p : ℕ) : AlgebraicClosure K) ≠ 0 :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.natCast_ne_zero_of_ringChar_ne hp hℓL
  have hTp := rootDiagUnit_pow_eq_one_of_forall hap
  obtain ⟨h2, hn⟩ := suN_rank_ncard hkind
  obtain ⟨ν, ψ, σ, κ, hν, hψ, hκ, hnorm, hΨ⟩ :=
    exists_frame_of_typeA_tag_T_of_prime g2LongA2Frame_proved S hp hpL hTp i h2 hn
  obtain ⟨hs0, hs, -⟩ := outer_componentOrbitLength_spec S hT i
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom ta) i) with hsdef
  have hout : ¬ twistInner (componentRoots (rootCharHom ta) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[s]) := by
    intro h
    unfold twistKind at hkind
    rw [ite_eq_left_iff.2 (fun h' => absurd h h')] at hkind
    exact absurd hkind (by decide)
  have hmaps : ∀ a b, a ≠ b → (S.ρ : (Fin τ.rank → ℤ) → _)^[s] (σ a b) ∈ frameRoots σ := by
    intro a b hab
    have h1 : σ a b ∈ componentRoots (rootCharHom ta) i := by
      rw [hΨ]
      exact ⟨a, b, hab, rfl⟩
    have h2 : (S.ρ : (Fin τ.rank → ℤ) → _)^[s] (σ a b) ∈
        (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' componentRoots (rootCharHom ta) i := ⟨_, h1, rfl⟩
    rw [hs, hΨ] at h2
    exact h2
  have hneg : ∀ (n : ℕ) (γ : Fin τ.rank → ℤ),
      (S.ρ : (Fin τ.rank → ℤ) → _)^[n] (-γ) = -(S.ρ : (Fin τ.rank → ℤ) → _)^[n] γ := by
    intro n
    induction n with
    | zero => exact fun γ => rfl
    | succ n ih =>
      intro γ
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, S.frob.neg_eq]
  rcases hψ.aut_cases hν hκ hnorm ((S.ρ : (Fin τ.rank → ℤ) → _)^[s]) hmaps (hneg s)
      (iform_rho_iterate S s) with ⟨π, hπ⟩ | ⟨π, hπ⟩
  · exfalso
    apply hout
    obtain ⟨w, hw, hwσ⟩ := hψ.exists_weyl_perm hκ hnorm π
    refine ⟨w, ?_, fun γ hγ => ?_⟩
    · rw [hΨ]
      exact hw
    · rw [hΨ] at hγ
      obtain ⟨a, b, hab, rfl⟩ := hγ
      rw [hπ a b hab, hwσ]
  · exact compCharElem_of_unitary_frame_three S hK hℓp hℓ3 hT i hν hψ hΨ π hπ

end SuN3

open CFSG.HardMathSupport.Timmesfeld.CrossChar in
private theorem orbitCharElemPerfect_outer_any {p : ℕ} (hp : p.Prime) {a : Fin τ.rank → (AlgebraicClosure K)ˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ i, a i ^ p = 1) (h1 : rootDiagUnit τ a ≠ 1)
    (i : KernelComponent (rootCharHom a))
    (hkind : twistKind S.ρ (rootCharHom a) i = .twoD ∨ twistKind S.ρ (rootCharHom a) i = .exc) :
    OrbitCharElemPerfect S (ringChar K) a i := by
  classical
  have hℓ : (ringChar K).Prime := by
    haveI : Fintype K := Fintype.ofFinite K
    exact (FiniteField.card K (ringChar K)).choose_spec.1
  have hLℓ : ringChar (AlgebraicClosure K) = ringChar K :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ringChar_algebraicClosure K
  have hℓL : ringChar (AlgebraicClosure K) ≠ p :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ringChar_ne_of_pow_eq_one hp hap h1
  have hpL : ((p : ℕ) : AlgebraicClosure K) ≠ 0 :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.natCast_ne_zero_of_ringChar_ne hp hℓL
  have hTp := rootDiagUnit_pow_eq_one_of_forall hap
  rcases hkind with hk | hk
  · obtain ⟨hnin, h4, hcard⟩ := twoD_kind_unpack hk
    by_cases h5' : 5 ≤ compRank (componentRoots (rootCharHom a) i)
    · have hr := le_trans h5' (compRank_le_rank (componentRoots (rootCharHom a) i))
      have hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
        cases τ <;> simp_all [Tag.rank]
      refine exists_perfect_orbit_twoD_high S hLℓ (fun t ht => ?_) hτ hT i hk h5'
      obtain ⟨l, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
      obtain ⟨N, hN, hlN⟩ := exists_coprime_pow_eq_one_algClosure hℓ rfl l
      exact ⟨N, hN, rootDiagUnit_pow_eq_one_of_forall hlN⟩
    · have hr : compRank (componentRoots (rootCharHom a) i) = 4 := by omega
      have hc : (componentRoots (rootCharHom a) i).ncard = 24 := by
        rw [hcard, hr]
      exact orbitCharElemPerfect_rank_four e6FixDNAll_proved S hp hpL hT hTp h1 i hr hc hnin
  · exact orbitCharElemPerfect_exc S hp hpL hT hTp h1 i hk

private theorem exists_perfect_of_charElem_three (hK : ringChar K = ℓ) (hℓp : ℓ.Prime) (hq4 : 4 ≤ S.D.q)
    (hℓ3 : 3 ≤ ℓ)
    {p : ℕ} (hp : p.Prime) (hpℓ : p ≠ ℓ) {a : Fin τ.rank → (AlgebraicClosure K)ˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ i, a i ^ p = 1) (h1 : rootDiagUnit τ a ≠ 1)
    {k : ModGL τ (AlgebraicClosure K)} (hk : k ∈ S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a})
    {m : ℕ} (hkm : k ^ ℓ ^ m = 1) :
    ∃ P ≤ S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a}, ⁅P, P⁆ = P ∧ k ∈ P := by
  classical
  have hgood : ∀ O : Set.range (rationalRoots S.ρ (rootCharHom a)),
      ∃ P' : Subgroup (ModGL τ (AlgebraicClosure K)), ⁅P', P'⁆ = P' ∧
        P' ≤ S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a} ∧
        ∀ g ∈ rootSpan τ (AlgebraicClosure K) O.1, g ∈ S.D.model → (∃ n : ℕ, g ^ ℓ ^ n = 1) → g ∈ P' := by
    rintro ⟨_, i, rfl⟩
    have horb : ∃ P' : Subgroup (ModGL τ (AlgebraicClosure K)), ⁅P', P'⁆ = P' ∧
        P' ≤ rationalComponent S.ρ S.Γ (rootCharHom a) i ∧
        ∀ g ∈ rootSpan τ (AlgebraicClosure K) (rationalRoots S.ρ (rootCharHom a) i), g ∈ S.D.model →
          (∃ n : ℕ, g ^ ℓ ^ n = 1) → g ∈ P' := by
      cases hkind : twistKind S.ρ (rootCharHom a) i with
      | inner => exact exists_perfect_orbit_of_comp S hK hℓp hT i (compCharElem_inner S hK hℓp hq4 hT i hkind)
      | suN => exact exists_perfect_orbit_of_comp S hK hℓp hT i (compCharElem_suN_three S hK hℓp hℓ3 hp hT hap h1 i hkind)
      | twoD =>
        obtain ⟨P', hP'A, hP'perf, hP'⟩ := orbitCharElemPerfect_outer_any S hp hT hap h1 i (Or.inl hkind)
        rw [hK] at hP'
        exact ⟨P', hP'perf, le_rationalComponent_of_perfect S i hP'A hP'perf, hP'⟩
      | exc =>
        obtain ⟨P', hP'A, hP'perf, hP'⟩ := orbitCharElemPerfect_outer_any S hp hT hap h1 i (Or.inr hkind)
        rw [hK] at hP'
        exact ⟨P', hP'perf, le_rationalComponent_of_perfect S i hP'A hP'perf, hP'⟩
    obtain ⟨P', hP'perf, hP'R, hP'⟩ := horb
    exact ⟨P', hP'perf, hP'R.trans (langSubnormal_of_mem_torus S hT i).1, hP'⟩
  choose Pf hPfperf hPfle hPfmem using hgood
  exact ⟨⨆ O, Pf O, iSup_le hPfle, commutator_iSup_eq_charQ Pf hPfperf,
    mem_iSup_of_charElem_family S hK hℓp hp hpℓ hT hap Pf hPfmem hk hkm⟩

private theorem qGen_of_langSetup_charElem_three {p : ℕ} (hp : p.Prime)
    (hres : CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ExcRationalLieTypesP p)
    (hK : ringChar K = ℓ) (hℓp : ℓ.Prime) (hq4 : 4 ≤ S.D.q) (hℓ3 : 3 ≤ ℓ) (hpℓ : p ≠ ℓ)
    {C : Type} [Group C] (ι : C →* ModGL τ (AlgebraicClosure K)) (hι : Function.Injective ι)
    (hrange : ι.range = S.Γ) (β : MulAut C) {a : Fin τ.rank → (AlgebraicClosure K)ˣ}
    (hβ : ∀ c, ι (β c) = rootDiagUnit τ a * ι c * (rootDiagUnit τ a)⁻¹)
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ i, a i ^ p = 1) (h1 : rootDiagUnit τ a ≠ 1)
    (hTame : ∀ i : KernelComponent (rootCharHom a),
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) ∨
        Group.IsSolvable (rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    Inputs256e.QGen ℓ β := by
  classical
  intro s hs ⟨n, hn⟩
  set d : ModGL τ (AlgebraicClosure K) := rootDiagUnit τ a with hd
  set R : KernelComponent (rootCharHom a) → Subgroup (ModGL τ (AlgebraicClosure K)) :=
    fun i => rationalComponent S.ρ S.Γ (rootCharHom a) i with hR
  have hfix : (fixSubgroup β).map ι = S.Γ ⊓ Subgroup.centralizer {d} := by
    rw [CFSG.HardMathSupport.Solomon.Coordinator.LieComp.map_fixSubgroup_eq_of_conj ι hι β d hβ, hrange]
  have hcomapfix : (S.Γ ⊓ Subgroup.centralizer {d}).comap ι = fixSubgroup β := by
    rw [← hfix]
    exact Subgroup.comap_map_eq_self_of_injective hι _
  have hCdrange : S.Γ ⊓ Subgroup.centralizer {d} ≤ ι.range := fun x hx => by
    rw [hrange]
    exact (Subgroup.mem_inf.1 hx).1
  have hιs : ι s ∈ S.Γ ⊓ Subgroup.centralizer {d} := by
    rw [← hfix]
    exact ⟨s, mem_fixSubgroup.2 hs, rfl⟩
  have hιn : ι s ^ ℓ ^ n = 1 := by rw [← map_pow, hn, map_one]
  obtain ⟨P, hPle, hPperf, hsP⟩ := exists_perfect_of_charElem_three S hK hℓp hq4 hℓ3 hp hpℓ hT hap h1 hιs hιn
  have hPR := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.perfect_le_iSup_rationalComponent_of_prime
    S hp hT hap h1 hTame P hPle hPperf
  haveI : Finite (KernelComponent (rootCharHom a)) :=
    (root_character_kernel_orthogonal_central_product τ (AlgebraicClosure K) (rootCharHom a)).2.1
  let Q := {i : KernelComponent (rootCharHom a) // CFSG.IsQuasisimple (R i)}
  have hcompR : ∀ i : Q, IsComponentOf (R i.1) (S.Γ ⊓ Subgroup.centralizer {d}) := by
    intro i
    obtain ⟨hle, hsub⟩ := langSubnormal_of_mem_torus S hT i.1
    exact ⟨hle, (CFSG.Open.IsSubnormal.iff_subgroupOf hle).2 hsub, open_isQuasisimple i.2⟩
  have hRrange : ∀ i : Q, R i.1 ≤ ι.range := fun i => (hcompR i).1.trans hCdrange
  let Fq : Q → Subgroup C := fun i => (R i.1).comap ι
  have hmapF : (⨆ i, Fq i).map ι = ⨆ i : Q, R i.1 := by
    rw [Subgroup.map_iSup]
    exact iSup_congr fun i => Subgroup.map_comap_eq_self (hRrange i)
  have hsF : s ∈ ⨆ i, Fq i := by
    have h' : ι s ∈ (⨆ i, Fq i).map ι := by
      rw [hmapF]
      exact hPR hsP
    obtain ⟨s', hs', hs'eq⟩ := h'
    rwa [hι hs'eq] at hs'
  have hLℓ : ringChar (AlgebraicClosure K) = ℓ := by
    rw [CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ringChar_algebraicClosure, hK]
  have hFchev : ∀ i : Q, Inputs256e.IsChevSub ℓ β (Fq i) := by
    intro i
    have hc := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.isComponentOf_comap_of_injective ι hι
      (hRrange i) hCdrange (hcompR i)
    rw [hcomapfix] at hc
    obtain ⟨-, hsub, hq⟩ := hc
    let e : ↥(Fq i) ≃* ↥(R i.1) := (Subgroup.equivMapOfInjective (Fq i) ι hι).trans
      (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self (hRrange i)))
    have hdata := hres τ (AlgebraicClosure K) p₀ S a hT hap h1 i.1 i.2
    rw [hLℓ] at hdata
    exact ⟨hsub, hq, CFSG.HardMathSupport.Solomon.Coordinator.LieComp.isChevSimple_congr
      (QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)).symm hdata.chev⟩
  exact (iSup_le fun i => le_iSup₂_of_le (f := fun (J : Subgroup C) (_ : Inputs256e.IsChevSub ℓ β J) => J)
    (Fq i) (hFchev i) le_rfl) hsF

end Lang3

section Lang3Families

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256j
open CFSG.StandardType.RecipeExcLang (inndiagGroup)
open CFSG.LieType.SeitzGeneration (Cat)


theorem qGenCoprime_exc_inndiag_three_of_four_le {τ : Tag}
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type} [Field K] [Finite K]
    (hK3 : ringChar K = 3) (h4 : 4 ≤ Nat.card K) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (α : MulAut ↥(adjointGroup τ K)) (b : Fin τ.rank → Kˣ) (j : ModGL τ K) (hj : j ∈ adjointGroup τ K)
    (hα : ∀ c : adjointGroup τ K,
      (α c : ModGL τ K) = (rootDiagUnit τ b * j) * c * (rootDiagUnit τ b * j)⁻¹)
    (hp1 : (rootDiagUnit τ b * j) ^ p = 1) (hh1 : rootDiagUnit τ b * j ≠ 1) : QGenCoprime 3 p α := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hℓ, hf⟩ := FiniteField.card K (ringChar K)
  have hqK : Nat.card K = ringChar K ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hf
  have hpK : p ≠ ringChar K := by rw [hK3]; exact hp3
  have hpK' : ¬ p ∣ Nat.card K := by
    rw [hqK]
    intro h
    exact hpK ((Nat.prime_dvd_prime_iff_eq hp hℓ).1 (hp.dvd_of_dvd_pow h))
  have hmon : CFSG.HardMathSupport.Timmesfeld.CrossChar.MonomialToralAt τ p :=
    monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five
      (by rcases hτ with h | h | h | h | h <;> simp [h]) hp hp2
  have hperf : commutator ↥(adjointGroup τ K) = ⊤ := by
    rcases hτ with h | h | h | h | h
    · subst h
      exact (CFSG.LieType.Steinberg.Adjoint.isPerfect_g2_of_three_le_card K (by omega)).commutator_eq_top
    all_goals exact single_edge_perfect τ K (by simp [h])
  have hh : rootDiagUnit τ b * j ∈ inndiagGroup τ K := ⟨b, j, hj, rfl⟩
  obtain ⟨S, a, ι, hSq, -, hT, hap, h1, hinj, hrange, hconj⟩ :=
    exists_langSetup_of_inner_untw hτ hp hpK' (Or.inr h4) hmon hperf α (rootDiagUnit τ b * j)
      (baseChange_mem_adjointGroup_of_mem_inndiag hh) hα hp1 hh1
  have hq4 : 4 ≤ S.D.q := by rw [hSq]; exact h4
  have hQ := qGen_of_langSetup_charElem_three S hp (excRationalLieTypesP_charQ hp hp2) rfl hℓ hq4
    (by omega) hpK ι hinj hrange α hconj hT hap h1 (langSetup_hTame S hT hap h1)
  rw [hK3] at hQ
  exact qGenCoprime_of_qGen hQ

@[expose] def QGen3ExcInndiagF3 : Prop :=
  ∀ (τ : Tag), (τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) →
    ∀ (K : Type) [Field K] [Finite K], Nat.card K = 3 →
    ∀ (p : ℕ), p.Prime → p ≠ 2 → p ≠ 3 →
    ∀ (α : MulAut ↥(adjointGroup τ K)) (b : Fin τ.rank → Kˣ) (j : ModGL τ K), j ∈ adjointGroup τ K →
      (∀ c : adjointGroup τ K,
        (α c : ModGL τ K) = (rootDiagUnit τ b * j) * c * (rootDiagUnit τ b * j)⁻¹) →
      (rootDiagUnit τ b * j) ^ p = 1 → rootDiagUnit τ b * j ≠ 1 →
        QGenCoprime 3 p α

theorem qGen3ExcInndiag_of_F3 (h : QGen3ExcInndiagF3) : QGen3ExcInndiag := by
  intro τ hτ K _ _ hK3 p hp hp2 hp3 α b j hj hα hp1 hh1
  by_cases h4 : 4 ≤ Nat.card K
  · exact qGenCoprime_exc_inndiag_three_of_four_le hτ hK3 h4 hp hp2 hp3 α b j hj hα hp1 hh1
  · have hc : Nat.card K = 3 := by
      obtain ⟨n, hn, hcard⟩ := Inputs256e.exists_card_eq_pow Nat.prime_three hK3
      rw [hcard] at h4 ⊢
      rcases Nat.lt_or_ge n 2 with h' | h'
      · obtain rfl : n = 1 := by omega
        rfl
      · exfalso
        have : 3 ^ 2 ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) h'
        omega
    exact h τ hτ K hc p hp hp2 hp3 α b j hj hα hp1 hh1

theorem qGenCoprime_twE6_inndiag_three_of_two_le {f : ℕ} (hf : 2 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (3 ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (3 ^ f)) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) (h : ↥(CFSG.HardMathSupport.Timmesfeld.CrossChar.twistedE6InndiagGL K σ))
    (hp1 : h ^ p = 1) (hh1 : h ≠ 1) :
    QGenCoprime 3 p (CFSG.HardMathSupport.Timmesfeld.CrossChar.twistedE6InndiagConj K σ h) := by
  classical
  have hℓ : (3 : ℕ).Prime := Nat.prime_three
  have hf1 : 1 ≤ f := by omega
  have hmon : CFSG.HardMathSupport.Timmesfeld.CrossChar.MonomialToralAt Tag.E6 p :=
    monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five (by simp) hp hp2
  obtain ⟨p₀, hp₀, hp₀ℓ, hq₀⟩ := exists_setup_prime hℓ hf1 hp hp2 hp3
  obtain ⟨S, a, ι, hSq, -, hT, hap, h1, hinj, hrange, hconj⟩ :=
    exists_langSetup_of_inndiag_twE6_of_prime hℓ hf1 hK σ hσ hp hp3 hp₀ hp₀ℓ hq₀ hmon
      (CFSG.HardMathSupport.Timmesfeld.CrossChar.twistedE6InndiagConj K σ h) (h : ModGL TwistTag.E6.tag K) h.2
      (CFSG.HardMathSupport.Timmesfeld.CrossChar.twistedE6InndiagConj_apply h)
      (by rw [← Subgroup.coe_pow, hp1]; rfl) (fun h' => hh1 (Subtype.ext h'))
  have hKℓ : ringChar K = 3 :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ringChar_eq_of_card_eq_pow (n := f * 2) hℓ (by omega)
      (by rw [hK, ← pow_mul])
  have hq4 : 4 ≤ S.D.q := by
    rw [hSq]
    calc 4 ≤ 3 ^ 2 := by norm_num
      _ ≤ 3 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  exact qGenCoprime_of_qGen (qGen_of_langSetup_charElem_three S hp (excRationalLieTypesP_charQ hp hp2) hKℓ hℓ
    hq4 le_rfl hp3 ι hinj hrange _ hconj hT hap h1 (langSetup_hTame_of_prime S hp
      (natCast_ne_zero_algebraicClosure_of_ne hℓ hp hK hp3) (fun h => absurd h (by decide)) hT hap h1))

@[expose] def QGen3TwE6InndiagF3 : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = (3 ^ 1) ^ 2 →
    ∀ (σ : K ≃+* K), (∀ c, σ c = c ^ (3 ^ 1)) → ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 3 →
    ∀ h : ↥(CFSG.HardMathSupport.Timmesfeld.CrossChar.twistedE6InndiagGL K σ), h ^ p = 1 → h ≠ 1 →
      QGenCoprime 3 p (CFSG.HardMathSupport.Timmesfeld.CrossChar.twistedE6InndiagConj K σ h)

theorem qGen3TwE6Inndiag_of_F3 (h : QGen3TwE6InndiagF3) : QGen3TwE6Inndiag := by
  intro f hf K _ _ hK σ hσ p hp hp2 hp3 x hp1 hx1
  by_cases hf2 : 2 ≤ f
  · exact qGenCoprime_twE6_inndiag_three_of_two_le hf2 hK σ hσ hp hp2 hp3 x hp1 hx1
  · obtain rfl : f = 1 := by omega
    exact h K hK σ hσ p hp hp2 hp3 x hp1 hx1

theorem qGenCoprime_triD4_inner_three_of_two_le {f : ℕ} (hf : 2 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (3 ^ f) ^ 3) (Fr : K ≃+* K) (hFr : ∀ c, Fr c = c ^ (3 ^ f)) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) (x : ↥(graphFixedRootGroup TwistTag.D4 K Fr.toRingHom))
    (hφ : orderOf (MulAut.conj x) = p) : QGenCoprime 3 p (MulAut.conj x) := by
  classical
  have hℓ : (3 : ℕ).Prime := Nat.prime_three
  have hf1 : 1 ≤ f := by omega
  have hZ : Subgroup.center ↥(graphFixedRootGroup TwistTag.D4 K Fr.toRingHom) = ⊥ :=
    center_graphFixedRootGroup_eq_bot Fr.surjective
  have hxp : x ^ p = 1 :=
    mulAut_conj_injective_of_center_eq_bot hZ (by rw [map_pow, ← hφ, pow_orderOf_eq_one, map_one])
  have hx1 : x ≠ 1 := fun h' => by
    rw [h', map_one, orderOf_one] at hφ
    exact hp.one_lt.ne' hφ.symm
  have hmon : CFSG.HardMathSupport.Timmesfeld.CrossChar.MonomialToralAt Tag.D4 p :=
    monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five (by simp) hp hp2
  obtain ⟨p₀, hp₀, hp₀ℓ, hq₀⟩ := exists_setup_prime hℓ hf1 hp hp2 hp3
  obtain ⟨S, a, ι, hSq, -, hT, hap, h1, hinj, hrange, hconj⟩ :=
    exists_langSetup_of_inner_triD4_of_prime hℓ hf1 hK Fr hFr hp hp3 hp₀ hp₀ℓ hq₀ hmon x hxp hx1
  have hKℓ : ringChar K = 3 :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ringChar_eq_of_card_eq_pow (n := f * 3) hℓ (by omega)
      (by rw [hK, ← pow_mul])
  have hq4 : 4 ≤ S.D.q := by
    rw [hSq]
    calc 4 ≤ 3 ^ 2 := by norm_num
      _ ≤ 3 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  exact qGenCoprime_of_qGen (qGen_of_langSetup_charElem_three S hp (excRationalLieTypesP_charQ hp hp2) hKℓ hℓ
    hq4 le_rfl hp3 ι hinj hrange _ hconj hT hap h1 (langSetup_hTame_of_prime S hp
      (natCast_ne_zero_algebraicClosure_of_ne hℓ hp hK hp3) (fun h => absurd h (by decide)) hT hap h1))

@[expose] def QGen3TriD4InnerF3 : Prop :=
  ∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid), q.p = 3 → q.exponent = 1 →
    ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 3 → ∀ t : Cat ⟨.trialityD4 q, hv⟩,
      orderOf (MulAut.conj t) = p → QGenCoprime 3 p (MulAut.conj t)

theorem qGen3TriD4Inner_of_F3 (h : QGen3TriD4InnerF3) : QGen3TriD4Inner := by
  intro q hv hq3 p hp hp2 hp3 t ht
  by_cases hf : q.exponent = 1
  · exact h q hv hq3 hf p hp hp2 hp3 t ht
  · have hf2 : 2 ≤ q.exponent := by have := q.exponent_pos; omega
    classical
    obtain ⟨K, _, _, σ, hK, hσ, -, ⟨eK⟩⟩ :=
      CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_catEquiv_trialityD4 q hv
    rw [hq3] at hK hσ
    refine qGenCoprime_of_congr eK _ ?_
    rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj]
    have hφ : orderOf (MulAut.conj (eK t)) = p := by
      rw [← CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, Inputs256f.orderOf_congr]
      exact ht
    exact qGenCoprime_triD4_inner_three_of_two_le hf2 hK σ hσ hp hp2 hp3 (eK t) hφ

end Lang3Families

section Assembly

theorem input14_2StructThree_of_families
    (hI : QGen3ExcInndiagF3) (hT : QGen3TwE6InndiagF3) (hD : QGen3TriD4InnerF3) :
    Inputs256e.Input14_2StructThree :=
  input14_2StructThree_of_qGen3On (qGen3On_of_families qGen3On_linear qGen3On_unitary
    (qGen3SympOrth_of_orth qGen3Orth_of_inner)
    (qGen3Exc_of_residuals (qGen3ExcInndiag_of_F3 hI) (qGen3TwE6_of_inndiag (qGen3TwE6Inndiag_of_F3 hT))
      (qGen3TriD4_of_inner (qGen3TriD4Inner_of_F3 hD))) qGen3Ree_holds)
    (input14_2StructRee37_of_gen reeGen37_holds)

end Assembly

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256i

end
