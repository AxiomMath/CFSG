module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompAlgUnitaryBlock
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompAlgLinear
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxUnitary
import all CFSG.HardMathSupport.Solomon.Coordinator.LieComp.UnitaryInnerExport

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open Polynomial Module
open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.PerfectAutomorphisms
open CFSG.ComponentClassification.PerfectCentralQuotient
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitaryModel
open Matrix

variable {K : Type} [Field K] (h : UnitaryFieldData 2 3 K) {n : ℕ}

private theorem card_centerQuotient_unitaryBlock_eq
    {x : LinearMap.GeneralLinearGroup K (Fin n → K)}
    (a : primaryFactors (x : Module.End K (Fin n → K)))
    {e : TauCeti.ValidLieTypeIndex}
    (hidx : ∃ q : TauCeti.PrimePower,
      (e.1 = .A 1 q ∨ e.1 = .twistedA 2 q) ∧ q.card = 8)
    (hKiso : Nonempty (↥(unitaryBlockComponent h (x := x) (a : K[X])) ⧸
        Subgroup.center ↥(unitaryBlockComponent h (x := x) (a : K[X])) ≃*
        (TauCeti.CFSGIndex.lie e).Group)) :
    Nat.card (↥(unitaryBlockComponent h (x := x) (a : K[X])) ⧸
        Subgroup.center ↥(unitaryBlockComponent h (x := x) (a : K[X]))) = 504 ∨
      Nat.card (↥(unitaryBlockComponent h (x := x) (a : K[X])) ⧸
        Subgroup.center ↥(unitaryBlockComponent h (x := x) (a : K[X]))) = 5515776 := by
  obtain ⟨ei, hv⟩ := e
  obtain ⟨eK⟩ := hKiso
  let k8 : Type := GaloisField 2 3
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hk8 : Nat.card k8 = 8 := by
    dsimp only [k8]
    rw [GaloisField.card 2 3 (by norm_num)]
    norm_num
  obtain ⟨q, hq, hqcard⟩ := hidx
  rcases hq with hA | htw
  · subst hA
    left
    exact (Nat.card_congr eK.toEquiv).trans
      (card_catGroup_A_one_eight (k := k8) hk8 hqcard)
  · subst htw
    right
    exact (Nat.card_congr eK.toEquiv).trans (card_catGroup_twistedA_two_eight hqcard)

private theorem selfDual_natDegree_one_of_card
    {x : LinearMap.GeneralLinearGroup K (Fin n → K)}
    (H : UnitaryPrimaryData h.bar (idForm h n) x)
    {a : primaryFactors (x : Module.End K (Fin n → K))} (ha : IsGoodBlock h x a)
    (hN : Nat.card (↥(unitaryBlockComponent h (x := x) (a : K[X])) ⧸
        Subgroup.center ↥(unitaryBlockComponent h (x := x) (a : K[X]))) = 504 ∨
      Nat.card (↥(unitaryBlockComponent h (x := x) (a : K[X])) ⧸
        Subgroup.center ↥(unitaryBlockComponent h (x := x) (a : K[X]))) = 5515776) :
    dualPoly h.bar (a : K[X]) = a ∧ (a : K[X]).natDegree = 1 := by
  classical
  have hq : 2 ≤ 2 ^ 3 := by norm_num
  let SB := specialBlock (idForm h n) x (a : K[X])
  let Comp := unitaryBlockComponent h (x := x) (a : K[X])
  let F := unitaryPreimageBlock h (x := x) (a : K[X])
  let πF : ↥F →* ↥Comp :=
    MonoidHom.subgroupMap (QuotientGroup.mk' (unitaryNormOneScalars h n)) F
  have hπF : Function.Surjective πF :=
    (subgroupMap_mk'_surjective_ker_le_center (h := h) (x := x) a).1
  have hkerF : πF.ker ≤ Subgroup.center ↥F :=
    (subgroupMap_mk'_surjective_ker_le_center (h := h) (x := x) a).2
  let ε : ↥F ≃* ↥SB := specialBlockEquiv (h := h) H a hq ha
  let πSB : ↥SB →* ↥Comp := πF.comp ε.symm.toMonoidHom
  have hπSB : Function.Surjective πSB := hπF.comp ε.symm.surjective
  have hkerSB : πSB.ker ≤ Subgroup.center ↥SB := by
    rw [← MonoidHom.comap_ker]
    exact (Subgroup.comap_mono hkerF).trans (Subgroup.comap_center_le_center ε.symm.injective)
  have hj : 1 ≤ (a : K[X]).natDegree :=
    Irreducible.natDegree_pos (irreducible_of_mem_primaryFactors a.2)
  by_cases hself : dualPoly h.bar (a : K[X]) = a
  ·
    rcases exists_field_factor_of_good (hK := h) hq H a ha with
        ⟨Fld, hFld, hFldt, _hcharF, hcardF, h4, ⟨eM⟩⟩ |
        ⟨E, hE, hEt, m, _hcharE, hcardE, hm, hne, ⟨eM⟩⟩ |
        ⟨E, hE, hEt, m, _hcharE, hcardE, hm2, h4, ⟨eM⟩⟩
    ·
      letI : Field Fld := hFld
      letI : Fintype Fld := hFldt
      let πM : Matrix.SpecialLinearGroup (Fin 2) Fld →* ↥Comp :=
        πSB.comp eM.symm.toMonoidHom
      have hπM : Function.Surjective πM := hπSB.comp eM.symm.surjective
      have hkerM : πM.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) Fld) := by
        rw [← MonoidHom.comap_ker]
        exact (Subgroup.comap_mono hkerSB).trans
          (Subgroup.comap_center_le_center eM.symm.injective)
      have hperf : commutator (Matrix.SpecialLinearGroup (Fin 2) Fld) = ⊤ :=
        (slFactorFacts_holds Fld 2 le_rfl (fun _ => h4)).perfect
      have hFcard : Nat.card Fld = 2 ^ (3 * (a : K[X]).natDegree) := by
        rw [Nat.card_eq_fintype_card]
        exact hcardF
      have hres := card_centerQuotient_eq_504_of_surjective_SL_two
        (F := Fld) (j := (a : K[X]).natDegree) hj hFcard πM hπM hkerM hperf hN
      exact ⟨hself, hres.1⟩
    ·
      letI : Field E := hE
      letI : Fintype E := hEt
      let πM : ↥(StatedSU m (2 ^ (3 * (a : K[X]).natDegree)) E) →* ↥Comp :=
        πSB.comp eM.symm.toMonoidHom
      have hπM : Function.Surjective πM := hπSB.comp eM.symm.surjective
      have hkerM : πM.ker ≤
          Subgroup.center ↥(StatedSU m (2 ^ (3 * (a : K[X]).natDegree)) E) := by
        rw [← MonoidHom.comap_ker]
        exact (Subgroup.comap_mono hkerSB).trans
          (Subgroup.comap_center_le_center eM.symm.injective)
      have hperf : commutator ↥(StatedSU m (2 ^ (3 * (a : K[X]).natDegree)) E) = ⊤ :=
        (suFactorFacts_holds E m (2 ^ (3 * (a : K[X]).natDegree)) hcardE hm hne).perfect
      have hEcard : Nat.card E = (2 ^ (3 * (a : K[X]).natDegree)) ^ 2 := by
        rw [Nat.card_eq_fintype_card]
        exact hcardE
      have hres := card_centerQuotient_eq_5515776_of_surjective_statedSU
        (E := E) (m := m) (j := (a : K[X]).natDegree) hm hj hEcard πM hπM hkerM hperf hN
      exact ⟨hself, hres.2.1⟩
    ·
      exfalso
      letI : Field E := hE
      letI : Fintype E := hEt
      let πM : Matrix.SpecialLinearGroup (Fin m) E →* ↥Comp :=
        πSB.comp eM.symm.toMonoidHom
      have hπM : Function.Surjective πM := hπSB.comp eM.symm.surjective
      have hkerM : πM.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin m) E) := by
        rw [← MonoidHom.comap_ker]
        exact (Subgroup.comap_mono hkerSB).trans
          (Subgroup.comap_center_le_center eM.symm.injective)
      have hperf : commutator (Matrix.SpecialLinearGroup (Fin m) E) = ⊤ :=
        (slFactorFacts_holds E m hm2 (fun _ => h4)).perfect
      have hEcard : Nat.card E = 2 ^ (2 * (3 * (a : K[X]).natDegree)) := by
        rw [Nat.card_eq_fintype_card]
        exact hcardE
      exact false_of_surjective_SL_of_card_eq_two_pow_six_mul
        (E := E) (m := m) (j := (a : K[X]).natDegree) hm2 hj hEcard πM hπM hkerM hperf hN
  ·
    exfalso
    have hne : (a : K[X]) ≠ dualPoly h.bar (a : K[X]) := Ne.symm hself
    obtain ⟨eM⟩ := nonempty_specialBlock_mulEquiv_SL (pairedPrimaryBlock H a hne)
    letI : Fact (Irreducible (a : K[X])) := ⟨irreducible_of_mem_primaryFactors a.2⟩
    haveI : Finite K := h.finite
    haveI : Finite (AdjoinRoot (a : K[X])) := Module.finite_of_finite K
    letI : Fintype (AdjoinRoot (a : K[X])) := Fintype.ofFinite _
    let πM : Matrix.SpecialLinearGroup
        (Fin (primaryMultiplicity (x : Module.End K (Fin n → K)) (a : K[X])))
        (AdjoinRoot (a : K[X])) →* ↥Comp := πSB.comp eM.symm.toMonoidHom
    have hπM : Function.Surjective πM := hπSB.comp eM.symm.surjective
    have hkerM : πM.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup
        (Fin (primaryMultiplicity (x : Module.End K (Fin n → K)) (a : K[X])))
        (AdjoinRoot (a : K[X]))) := by
      rw [← MonoidHom.comap_ker]
      exact (Subgroup.comap_mono hkerSB).trans
        (Subgroup.comap_center_le_center eM.symm.injective)
    have hEcard : Nat.card (AdjoinRoot (a : K[X])) = 2 ^ (2 * (3 * (a : K[X]).natDegree)) := by
      have hcard : Nat.card (AdjoinRoot (a : K[X])) = Nat.card K ^ (a : K[X]).natDegree :=
        CFSG.RankThree.PartOne.KCLinPlane.natCard_adjoinRoot (a : K[X])
      rw [hcard, h.card, ← pow_mul]
      congr 1
      ring
    have h4 : 4 ≤ Fintype.card (AdjoinRoot (a : K[X])) := by
      rw [← Nat.card_eq_fintype_card, hEcard]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (2 * (3 * (a : K[X]).natDegree)) :=
            Nat.pow_le_pow_right (by norm_num) (by omega)
    have hperf : commutator (Matrix.SpecialLinearGroup
        (Fin (primaryMultiplicity (x : Module.End K (Fin n → K)) (a : K[X])))
        (AdjoinRoot (a : K[X]))) = ⊤ :=
      (slFactorFacts_holds (AdjoinRoot (a : K[X]))
        (primaryMultiplicity (x : Module.End K (Fin n → K)) (a : K[X])) ha.1
        (fun _ => h4)).perfect
    exact false_of_surjective_SL_of_card_eq_two_pow_six_mul
      (E := AdjoinRoot (a : K[X]))
      (m := primaryMultiplicity (x : Module.End K (Fin n → K)) (a : K[X]))
      (j := (a : K[X]).natDegree) ha.1 hj hEcard πM hπM hkerM hperf hN

private theorem specialBlockEquiv_symm_sesqSUConj
    {x : LinearMap.GeneralLinearGroup K (Fin n → K)}
    (H : UnitaryPrimaryData h.bar (idForm h n) x)
    (a : primaryFactors (x : Module.End K (Fin n → K))) (hq : 2 ≤ 2 ^ 3)
    (ha : IsGoodBlock h x a) {e : ℕ}
    {hE : UnitaryFieldData 2 (3 * e) (AdjoinRoot (a : K[X]))}
    {Hf : primaryComponent (x : Module.End K (Fin n → K)) (a : K[X]) →ₛₗ[hE.bar]
      primaryComponent (x : Module.End K (Fin n → K)) (a : K[X]) →ₗ[AdjoinRoot (a : K[X])]
        AdjoinRoot (a : K[X])}
    {Y : primeFormUnitary h (idGram K n)}
    {Φ : ↥(specialBlock (idForm h n) x (a : K[X])) ≃* ↥(sesqSpecialUnitaryGroup Hf)}
    (hΦ : ∀ (s : ↥(specialBlock (idForm h n) x (a : K[X]))) (v : Fin n → K)
      (hv : v ∈ primaryComponent (x : Module.End K (Fin n → K)) (a : K[X])),
      blockApply (Φ s : blockGL (x : Module.End K (Fin n → K)) (a : K[X])) v hv =
        ((s : LinearMap.GeneralLinearGroup K (Fin n → K)) :
          Module.End K (Fin n → K)) v)
    {g : ↥(sesqUnitaryGroup Hf)}
    (hm : Matrix.GeneralLinearGroup.toLin (Y : GL (Fin n) K) ∈
      unitaryCentralizer (idForm h n) x)
    (hg : ∀ (v : Fin n → K)
      (hv : v ∈ primaryComponent (x : Module.End K (Fin n → K)) (a : K[X])),
      blockApply g v hv =
        (Matrix.GeneralLinearGroup.toLin (Y : GL (Fin n) K) : Module.End K (Fin n → K)) v)
    (u : ↥(unitaryPreimageBlock h (x := x) (a : K[X])))
    (hYmem : primeFormConjSU h (idGram K n) Y u ∈
      unitaryPreimageBlock h (x := x) (a : K[X])) :
    (specialBlockEquiv h H a hq ha).symm
      (Φ.symm (sesqSUConj g (Φ (specialBlockEquiv h H a hq ha u)))) =
      (⟨primeFormConjSU h (idGram K n) Y u, hYmem⟩ :
        ↥(unitaryPreimageBlock h (x := x) (a : K[X]))) := by
  classical
  let ε := specialBlockEquiv h H a hq ha
  let w : ↥(specialBlock (idForm h n) x (a : K[X])) :=
    ⟨Matrix.GeneralLinearGroup.toLin (Y : GL (Fin n) K) *
      ((ε u : ↥(specialBlock (idForm h n) x (a : K[X]))) :
        LinearMap.GeneralLinearGroup K (Fin n → K)) *
      (Matrix.GeneralLinearGroup.toLin (Y : GL (Fin n) K))⁻¹,
      conj_mem_specialBlock hm (ε u).2⟩
  have hU2 := blockApply_conj_specialBlock (B := idForm h n) (x := x) (a := a)
    (G := sesqSpecialUnitaryGroup Hf) (Φ := Φ) hΦ hm hg (ε u)
  have hU2' : Φ w = sesqSUConj g (Φ (ε u)) := by
    apply Subtype.ext
    rw [sesqSUConj_apply]
    exact hU2
  have hεw : ε (⟨primeFormConjSU h (idGram K n) Y u, hYmem⟩ :
      ↥(unitaryPreimageBlock h (x := x) (a : K[X]))) = w := by
    apply Subtype.ext
    rw [specialBlockEquiv_apply_coe, toLinSU_primeFormConjSU,
      ← specialBlockEquiv_apply_coe h H a hq ha u]
  calc ε.symm (Φ.symm (sesqSUConj g (Φ (ε u))))
      = ε.symm (Φ.symm (Φ w)) := by rw [← hU2']
    _ = ε.symm w := by rw [Φ.symm_apply_apply]
    _ = (⟨primeFormConjSU h (idGram K n) Y u, hYmem⟩ :
        ↥(unitaryPreimageBlock h (x := x) (a : K[X]))) := by
      rw [← hεw, ε.symm_apply_apply]

theorem compAlgAt_primeFormP_unitary_eight {K : Type} [Field K]
    (h : UnitaryFieldData 2 3 K) {n : ℕ} (hn : 3 ≤ n) :
    CompAlgAt (primeFormP h (idGram K n)) := by
  classical
  intro β hβmem hβ3 hβ1 Kc hKc e hidx hKiso x hxmem hx3 hβx hxstab
  have hqne : ¬(n = 3 ∧ 2 ^ 3 = 2) := by
    rintro ⟨-, h2⟩
    norm_num at h2
  obtain ⟨A, c, hc, hA3, hβeq⟩ :=
    exists_primeFormConjHom_pow_scalar_of_mem_innAutDerived (h := h)
      (C := (1 : GL (Fin n) K)) isPrimeFormGram_idGram hn hqne hβmem hβ3
  obtain ⟨Y, d, hd, hY3, hxeq⟩ :=
    exists_primeFormConjHom_pow_scalar_of_mem_innAutDerived (h := h)
      (C := (1 : GL (Fin n) K)) isPrimeFormGram_idGram hn hqne hxmem hx3
  rw [hβeq] at hKc
  rw [hxeq] at hxstab
  rw [hxeq] at hx3
  rw [hβeq, hxeq] at hβx
  obtain ⟨μ, hYA⟩ := eq_scalar_commutator_of_commute_primeFormConjHom (h := h) hn hβx
  have H : UnitaryPrimaryData h.bar (idForm h n)
      (Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K)) :=
    primaryData_toLin' h A.2 Nat.prime_three (by norm_num) hA3
  have hq2 : 2 ≤ 2 ^ 3 := by norm_num
  obtain ⟨a, hT⟩ := exists_good_primaryFactor_of_component (h := h) (n := n)
    (x := Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K)) hq2 A rfl H Kc hKc
  let SB := specialBlock (idForm h n) (Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K))
    (a.1 : K[X])
  let Comp := unitaryBlockComponent h
    (x := Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K)) (a.1 : K[X])
  let F := unitaryPreimageBlock h
    (x := Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K)) (a.1 : K[X])
  have hT' : Kc = Comp := hT
  have hKisoComp : Nonempty (↥Comp ⧸ Subgroup.center ↥Comp ≃*
      (TauCeti.CFSGIndex.lie e).Group) := hT' ▸ hKiso
  have hN := card_centerQuotient_unitaryBlock_eq (h := h) a.1 hidx
    (by simpa only [Comp] using hKisoComp)
  obtain ⟨hself, hdeg⟩ := selfDual_natDegree_one_of_card (h := h) H a.2 hN
  have hmonic : (a.1 : K[X]).Monic := monic_of_mem_primaryFactors a.1.2
  obtain ⟨lam, hlam⟩ : ∃ lam : K, (a.1 : K[X]) = Polynomial.X - C lam :=
    ⟨-(a.1 : K[X]).coeff 0, by rw [map_neg, sub_neg_eq_add]; exact hmonic.eq_X_add_C hdeg⟩
  have hself_lam : dualPoly h.bar (Polynomial.X - C lam) = Polynomial.X - C lam := by
    rw [← hlam]
    exact hself
  have ha_mem_lam : Polynomial.X - C lam ∈ primaryFactors
      (Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K) : Module.End K (Fin n → K)) := by
    rw [← hlam]
    exact a.1.2
  have hS : SelfDualPrimaryBlock h (idForm h n)
      (Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K)) a.1 :=
    selfDualPrimaryBlock H a.1 hself
  have hstabComp : primeFormConjHom h (idGram K n) Y ∈
      CFSG.GroupActions.subgroupStabAut Comp := hT' ▸ hxstab
  have hnorm := map_conj_specialBlock_eq_self (h := h) (H := H) (a := a.1) hq2 a.2 hstabComp
  have hnorm_lam : (specialBlock (idForm h n)
        (Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K)) (Polynomial.X - C lam)).map
        (MulAut.conj (Matrix.GeneralLinearGroup.toLin (Y : GL (Fin n) K))).toMonoidHom =
      specialBlock (idForm h n) (Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K))
        (Polynomial.X - C lam) := by
    rw [← hlam]
    exact hnorm
  have hne_should : specialBlock (idForm h n)
      (Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K)) (Polynomial.X - C lam) ≠ ⊥ := by
    rw [← hlam]
    have hQ : CFSG.IsQuasisimple ↥SB :=
      (specialBlockFacts_of_good H hq2 a.1 a.2).quasisimple a.2.1
    exact (Subgroup.nontrivial_iff_ne_bot _).mp (CFSG.LocalCores.isQuasisimple_nontrivial hQ)
  have hscalar : (Matrix.GeneralLinearGroup.toLin (Matrix.GeneralLinearGroup.scalar (Fin n) μ) :
      Module.End K (Fin n → K)) = μ • 1 := by
    ext v i
    simp [Matrix.scalar_apply, Matrix.mulVec_diagonal, Units.smul_def]
  have hYA_end : (Matrix.GeneralLinearGroup.toLin (Y : GL (Fin n) K) :
        Module.End K (Fin n → K)) *
      (Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K) : Module.End K (Fin n → K)) =
      μ • ((Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K) : Module.End K (Fin n → K)) *
        (Matrix.GeneralLinearGroup.toLin (Y : GL (Fin n) K) : Module.End K (Fin n → K))) := by
    have h1 := congrArg (fun T : LinearMap.GeneralLinearGroup K (Fin n → K) =>
      (T : Module.End K (Fin n → K)))
      (congrArg (Matrix.GeneralLinearGroup.toLin (n := Fin n) (R := K)) hYA)
    simp only [Units.val_mul, map_mul] at h1
    rw [hscalar] at h1
    simpa only [smul_mul_assoc, one_mul] using h1
  have hμval : (μ : K) = 1 :=
    smul_eq_one_of_normalizes_specialBlock (hK := h) H ha_mem_lam hself_lam hYA_end
      hnorm_lam hne_should
  have hμ : μ = 1 := Units.ext hμval
  have hcomm : Commute (Matrix.GeneralLinearGroup.toLin (Y : GL (Fin n) K) :
        Module.End K (Fin n → K))
      (Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K) : Module.End K (Fin n → K)) := by
    rw [hμ, one_smul] at hYA_end
    exact hYA_end
  have hU : Matrix.GeneralLinearGroup.toLin (Y : GL (Fin n) K) ∈
      sesqUnitaryGroup (idForm h n) :=
    (toLin_mem_sesqUnitaryGroup_iff (h := h) (n := n) (Y : GL (Fin n) K)).mpr Y.2
  have hm : Matrix.GeneralLinearGroup.toLin (Y : GL (Fin n) K) ∈
      unitaryCentralizer (idForm h n)
        (Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K)) :=
    mem_unitaryCentralizer.mpr ⟨hU, hcomm⟩
  obtain ⟨hE, Hf, hHf, hHfl, Φ, hΦ, hisoG⟩ :=
    exists_selfDual_specialBlock_mulEquiv_sesqSpecialUnitary (hK := h) H hself hS
  obtain ⟨g, hg⟩ := hisoG (Matrix.GeneralLinearGroup.toLin (Y : GL (Fin n) K)) hm
  let πF : ↥F →* ↥Comp :=
    MonoidHom.subgroupMap (QuotientGroup.mk' (unitaryNormOneScalars h n)) F
  have hπF := subgroupMap_mk'_surjective_ker_le_center (h := h)
    (x := Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K)) a.1
  let ε : ↥F ≃* ↥SB := specialBlockEquiv (h := h) H a.1 hq2 a.2
  let π' : ↥(sesqSpecialUnitaryGroup Hf) →* ↥Comp :=
    πF.comp (ε.symm.toMonoidHom.comp Φ.symm.toMonoidHom)
  have hπ' : Function.Surjective π' :=
    hπF.1.comp (ε.symm.surjective.comp Φ.symm.surjective)
  have hker' : π'.ker ≤ Subgroup.center ↥(sesqSpecialUnitaryGroup Hf) := by
    rw [← MonoidHom.comap_ker]
    refine (Subgroup.comap_mono hπF.2).trans ?_
    have hinj : Function.Injective
        ⇑(ε.symm.toMonoidHom.comp Φ.symm.toMonoidHom) := by
      intro x y hxy
      exact Φ.symm.injective (ε.symm.injective hxy)
    exact Subgroup.comap_center_le_center hinj
  let γ : MulAut ↥Comp :=
    CFSG.GroupActions.subgroupStabRestrict Comp
      ⟨primeFormConjHom h (idGram K n) Y, hstabComp⟩
  have hγ : ∀ s : ↥(sesqSpecialUnitaryGroup Hf), γ (π' s) = π' (sesqSUConj g s) := by
    intro s
    let u : ↥F := ε.symm (Φ.symm s)
    have hεu : ε u = Φ.symm s := ε.apply_symm_apply _
    have hΦu : Φ (ε u) = s := by simpa only [hεu] using Φ.apply_symm_apply s
    have hcYmem : primeFormConjSU h (idGram K n) Y u ∈ F := by
      show toLinSU h n (primeFormConjSU h (idGram K n) Y u) ∈ SB
      rw [toLinSU_primeFormConjSU]
      have h2 : toLinSU h n u ∈ SB := u.2
      have h4 := Subgroup.mem_map_of_mem (MulAut.conj
        (Matrix.GeneralLinearGroup.toLin (Y : GL (Fin n) K))).toMonoidHom h2
      rwa [hnorm] at h4
    have hL : γ (π' s) = πF (⟨primeFormConjSU h (idGram K n) Y u, hcYmem⟩ : ↥F) := by
      have hπ's : π' s = πF u := rfl
      rw [hπ's]
      apply Subtype.ext
      rw [CFSG.GroupActions.subgroupStabRestrict_apply]
      exact primeFormConjHom_mk h (idGram K n) Y (u : ↥(gramSU h (idGram K n)))
    have hεsymm : ε.symm (Φ.symm (sesqSUConj g (Φ (ε u)))) =
        (⟨primeFormConjSU h (idGram K n) Y u, hcYmem⟩ : ↥F) :=
      specialBlockEquiv_symm_sesqSUConj (h := h) (e := (a.1 : K[X]).natDegree)
        (hE := hE) (Hf := Hf) (Y := Y) (Φ := Φ) (g := g)
        H a.1 hq2 a.2 hΦ hm hg u hcYmem
    have hR : π' (sesqSUConj g s) =
        πF (⟨primeFormConjSU h (idGram K n) Y u, hcYmem⟩ : ↥F) := by
      have hπ'c : π' (sesqSUConj g s) =
          πF (ε.symm (Φ.symm (sesqSUConj g s))) := rfl
      rw [hπ'c]
      have harg : ε.symm (Φ.symm (sesqSUConj g s)) =
          ε.symm (Φ.symm (sesqSUConj g (Φ (ε u)))) :=
        congrArg (fun t => ε.symm (Φ.symm (sesqSUConj g t))) hΦu.symm
      rw [harg, hεsymm]
    exact hL.trans hR.symm
  have hQSB : CFSG.IsQuasisimple ↥SB :=
    (specialBlockFacts_of_good H hq2 a.1 a.2).quasisimple a.2.1
  have hSUperf : commutator ↥(sesqSpecialUnitaryGroup Hf) = ⊤ := by
    haveI : Group.IsPerfect ↥SB := hQSB.1
    haveI : Group.IsPerfect ↥(sesqSpecialUnitaryGroup Hf) :=
      @Group.IsPerfect.ofSurjective ↥SB ↥(sesqSpecialUnitaryGroup Hf) _ _
        Φ.toMonoidHom hQSB.1 Φ.surjective
    exact Group.IsPerfect.commutator_eq_top
  have hγ3 : γ ^ 3 = 1 := by
    change ((CFSG.GroupActions.subgroupStabRestrict Comp
      ⟨primeFormConjHom h (idGram K n) Y, hstabComp⟩) ^ 3) = 1
    rw [← map_pow]
    have h1 : (⟨primeFormConjHom h (idGram K n) Y, hstabComp⟩ :
        CFSG.GroupActions.subgroupStabAut Comp) ^ 3 = 1 := by
      apply Subtype.ext
      simpa using hx3
    rw [h1, map_one]
  have hγp : centerQuotientHom ↥Comp γ ^ 3 = 1 := by
    rw [← map_pow, hγ3, map_one]
  have hgoal : centerQuotientHom ↥Comp γ ∈ innAutDerived (↥Comp ⧸ Subgroup.center ↥Comp) :=
    centerQuotientHom_mem_innAutDerived_of_sesqSUConj (hE := hE) hHf hHfl hSUperf
      Nat.prime_three (by norm_num) g π' hπ' hker' hγ hγp
  subst hxeq
  subst hT'
  exact hgoal

private theorem compAlgAt_primeFormP_unitary_of_eq {K : Type} [Field K] {ℓ f : ℕ}
    (h : UnitaryFieldData ℓ f K) (hℓ : ℓ = 2) (hf : f = 3) {n : ℕ} (hn : 3 ≤ n) :
    CompAlgAt (primeFormP h (idGram K n)) := by
  subst hℓ
  subst hf
  exact compAlgAt_primeFormP_unitary_eight h hn

theorem lieCompAlg_unitary : LieCompAlg isUnitaryIdx := by
  intro d hP hfield
  obtain ⟨r, q, K, _, hU, hr, hdA, _, ⟨eP⟩⟩ :=
    exists_primeFormP_mulEquiv_of_isUnitaryIdx hP
  have hq8 : q.card = 8 := by
    rw [hdA] at hfield
    exact hfield
  have hq8' : q.p ^ q.exponent = 2 ^ 3 :=
    (TauCeti.PrimePower.card_def q).symm.trans (hq8.trans (by norm_num))
  obtain ⟨hp2, he3⟩ := Nat.Prime.pow_inj' q.prime_p Nat.prime_two q.exponent_pos.ne'
    (by norm_num) hq8'
  have hn : 3 ≤ r + 1 := by omega
  exact compAlgAt_of_mulEquiv eP
    (compAlgAt_primeFormP_unitary_of_eq (hℓ := hp2) (hf := he3) hU hn)

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
