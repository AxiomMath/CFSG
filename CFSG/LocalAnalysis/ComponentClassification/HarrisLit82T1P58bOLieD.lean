module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58bOLiePc
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58bOLieField
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58bOLieMap
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58bOProps
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51eOrthFam
public import CFSG.LinearAlgebra.LinearGroups.Perfect
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBL2Reduction
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58bLift
public import CFSG.LocalAnalysis.ComponentClassification.Sol78Seven

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
  CFSG.ComponentClassification.CatLeafProof
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.Burgoyne.O CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.C
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL isoOrthGL transportGL
  trans_commutator map_commutator_mulEquiv)
open CFSG.GroupTheory.WeirSylow (IsPlusType isPlusType_congr isPlusType_quadPlus
  exists_isometry_quadPlus_or_quadMinus nonempty_isometry_of_not_isPlusType)
open scoped MatrixGroups commutatorElement

namespace P58b.OLie

theorem isQuasisimple_SL2 {F : Type*} [Field F] (h : ∃ s : Finset F, s.card = 4) :
    IsQuasisimple SL(2, F) := by
  have hperf := CFSG.LinearGroups.special_linear_isPerfect (K := F) (n := 2) le_rfl (Or.inr h)
  obtain ⟨-, hsimple, -⟩ := CFSG.LinearGroups.linear_projective_simple (K := F) (n := 2) le_rfl
    (Or.inr h)
  refine ⟨hperf, hsimple, ?_⟩
  by_contra hab
  push Not at hab
  have hle : commutator SL(2, F) ≤ Subgroup.center SL(2, F) := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [← QuotientGroup.eq_one_iff]
    change (QuotientGroup.mk' (Subgroup.center SL(2, F))) ⁅x, y⁆ = 1
    rw [map_commutatorElement, commutatorElement_def, hab (QuotientGroup.mk' _ x),
      mul_inv_cancel_right, mul_inv_cancel]
  have htop : commutator SL(2, F) = ⊤ := hperf.commutator_eq_top
  rw [htop] at hle
  have hc : Subgroup.center SL(2, F) = ⊤ := top_le_iff.mp hle
  have hnt := hsimple.toNontrivial
  obtain ⟨a, ha⟩ := exists_ne (1 : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective a
  exact ha ((QuotientGroup.eq_one_iff g).2 (hc ▸ Subgroup.mem_top g))

theorem factorization_eq_of_mul_two_eq {N p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hk : k ≠ 0)
    (h : N * 2 = p ^ k * ((p ^ k) ^ 2 - 1)) : N.factorization p = k := by
  have hq1 : 1 < (p ^ k) ^ 2 := Nat.one_lt_pow (by norm_num) (Nat.one_lt_pow hk hp.one_lt)
  have hfacP : (N * 2).factorization p = k := by
    rw [h, Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) (by omega), Finsupp.add_apply,
      Nat.Prime.factorization_pow hp, Finsupp.single_eq_same]
    have hcop : Nat.Coprime ((p ^ k) ^ 2 - 1) p :=
      CatLeafProof.coprime_pow_sub_one hp (dvd_pow_self p hk) (Nat.one_le_pow _ _ hp.pos)
        (by norm_num)
    rw [Nat.factorization_eq_zero_of_not_dvd ((Nat.Prime.coprime_iff_not_dvd hp).1 hcop.symm),
      add_zero]
  have hN : N ≠ 0 := by
    rintro rfl
    rw [zero_mul] at h
    exact Nat.mul_ne_zero (pow_ne_zero _ hp.ne_zero) (by omega) h.symm
  have hp2' : ¬ p ∣ 2 := fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h)
  rwa [Nat.factorization_mul hN two_ne_zero, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hp2', add_zero] at hfacP

variable {K : Type} [Field K] [Finite K] {d : ℕ} {w : Fin d → K} (hw : ∀ i, w i ≠ 0)

omit [Finite K] in
include hw in
theorem nonempty_blockP_equiv_commutator (hK : ringChar K ≠ 2) {I : Finset (Fin d)}
    (hIc : Iᶜ.Nonempty) :
    Nonempty (blockP K hw I ≃* commutator (TauCeti.QuadraticMap.orthogonalGroup
      (CatalogueBLinearHigherB.matrixQuadraticForm (diagGL (wRes_ne_zero hw I))))) := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  obtain ⟨e⟩ := nonempty_projBlock_equiv hw h2 hIc (le_refl (omegaI hw I))
  rw [← blockP_eq_projBlock] at e
  have hR : ((diagGL (wRes_ne_zero hw I) : GL (Fin I.card) K) :
      Matrix (Fin I.card) (Fin I.card) K)ᵀ = diagGL (wRes_ne_zero hw I) := by
    rw [coe_diagGL]
    exact diagonal_transpose _
  set φ := isoOrthGL hK _ hR with hφ
  have htc := trans_commutator φ
  let e₁ := (Subgroup.equivMapOfInjective (commutator (TauCeti.QuadraticMap.orthogonalGroup
      (CatalogueBLinearHigherB.matrixQuadraticForm (diagGL (wRes_ne_zero hw I)))))
      φ.toMonoidHom φ.injective).trans
    (((commutator (TauCeti.QuadraticMap.orthogonalGroup
      (CatalogueBLinearHigherB.matrixQuadraticForm (diagGL (wRes_ne_zero hw I))))).map
        φ.toMonoidHom).equivMapOfInjective _ (Subgroup.subtype_injective _))
  exact ⟨e.trans ((MulEquiv.subgroupCongr htc.symm).trans e₁.symm)⟩

include hw in
theorem nonempty_blockP_equiv_of_minus (hK : ringChar K ≠ 2) {I₁ I₂ : Finset (Fin d)}
    (hI₁c : I₁ᶜ.Nonempty) (hI₂c : I₂ᶜ.Nonempty) (h₁ : I₁.card = 4) (h₂ : I₂.card = 4)
    (hm₁ : ¬ IsPlusType (CatalogueBLinearHigherB.matrixQuadraticForm
      (diagGL (wRes_ne_zero hw I₁))))
    (hm₂ : ¬ IsPlusType (CatalogueBLinearHigherB.matrixQuadraticForm
      (diagGL (wRes_ne_zero hw I₂)))) :
    Nonempty (blockP K hw I₂ ≃* blockP K hw I₁) := by
  obtain ⟨e₁⟩ := nonempty_blockP_equiv_commutator hw hK hI₁c
  obtain ⟨e₂⟩ := nonempty_blockP_equiv_commutator hw hK hI₂c
  have hR : ∀ I : Finset (Fin d), ((diagGL (wRes_ne_zero hw I) : GL (Fin I.card) K) :
      Matrix (Fin I.card) (Fin I.card) K)ᵀ = diagGL (wRes_ne_zero hw I) := fun I => by
    rw [coe_diagGL]
    exact diagonal_transpose _
  have hQnd := fun I => CatalogueBLinearHigherB.polarBilin_matrixQuadraticForm_nondegenerate hK _
    (hR I)
  have hdim : ∀ {I : Finset (Fin d)}, I.card = 4 →
      Module.finrank K (Fin I.card → K) = 2 * 2 := fun hI => by
    rw [Module.finrank_fin_fun, hI]
  rcases exists_isometry_quadPlus_or_quadMinus _ (hQnd I₁) (by norm_num) (hdim h₁) with
    hi₁ | ⟨b, c, hirr, hi₁⟩
  · obtain ⟨i₁⟩ := hi₁
    exact absurd ((isPlusType_congr i₁).2 (isPlusType_quadPlus K 2)) hm₁
  obtain ⟨i₁⟩ := hi₁
  obtain ⟨i₂⟩ := nonempty_isometry_of_not_isPlusType (hQnd I₂) (by norm_num) (hdim h₂) hm₂ hirr
  let φ := TauCeti.QuadraticMap.orthogonalGroupCongr (i₂.trans i₁.symm)
  let ψ := (Subgroup.equivMapOfInjective (commutator (TauCeti.QuadraticMap.orthogonalGroup
      (CatalogueBLinearHigherB.matrixQuadraticForm (diagGL (wRes_ne_zero hw I₂)))))
      φ.toMonoidHom φ.injective).trans (MulEquiv.subgroupCongr (map_commutator_mulEquiv φ))
  exact ⟨e₂.trans (ψ.trans e₁.symm)⟩

omit [Field K] [Finite K] in
theorem exists_card_eq_four [Finite K] (h5 : 5 ≤ Nat.card K) : ∃ s : Finset K, s.card = 4 := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset K)) (n := 4)
    (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; omega)
  exact ⟨s, hs⟩

theorem false_of_typeD_model (hO : LieOrderFormulasInput) {X : Type} [Group X] [Finite X]
    (hX : IsQuasisimple X) {p k : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {c t : X} {Q L : Subgroup X}
    (hcfg : Lemma58bConfig X p k c t Q) (hL : IsTwoComponentIn L (centralizer {t}))
    (htL : t ∈ L) {τ' : StatedLieTag} {n' : ℕ}
    (hLie : Blueprint.LieModel (↥L ⧸ Open.fusionZStar ↥L) τ' n' p k)
    {K : Type} [Field K] [Finite K] (hK : ringChar K ≠ 2) {f : ℕ} (hKc : Nat.card K = p ^ f)
    {d : ℕ} (hd : Even d) (hd8 : 8 ≤ d) {R : GL (Fin d) K}
    (hR : (R : Matrix (Fin d) (Fin d) K)ᵀ = R)
    (θ : X ⧸ center X ≃* StatedProj (matrixDerived (oQ R))) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : p.Prime := Fact.out
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  obtain ⟨-, hf⟩ := GSThmB.QPUCl.prime_ne_two_and_one_le hK hp hKc
  obtain ⟨hzz, hz1, R₁, R₂, h₁H, h₁, ⟨e₁⟩, h₂H, h₂, hz₂, hZs⟩ :=
    comps_of_config hX hp2 hcfg hL htL θ
  have hz2 : orderOf (θ (QuotientGroup.mk t)) = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact hzz) hz1
  obtain ⟨T, hT, hθT, hT2 | hT2⟩ := P51e.Orth.exists_lift_sq h2 (by omega) hR hzz
  rotate_left
  · rw [hθT] at h₁H h₁ h₂H h₂ hz₂ hz2
    exact false_of_pc hK hp hKc (by omega) hR hT hT2 hz2 h₁H h₁ e₁ h₂H h₂ hz₂
  rw [hθT] at h₁H h₁ h₂H h₂ hz₂ hz1
  obtain ⟨w, hw, J, I, -, -, -, hIc, hNF, hq, h3, ⟨eI⟩, hIcev, hR₂⟩ :=
    two_comps_of_model hK hR hT hT2 hz1 h₁H h₁ e₁ h₂H h₂ hz₂
  have hcomp : Iᶜ.card = d - I.card := by rw [Finset.card_compl, Fintype.card_fin]
  have hIle : I.card ≤ d := by
    have := Finset.card_le_univ I
    rwa [Fintype.card_fin] at this
  have hIev : Even I.card := by
    obtain ⟨a, ha⟩ := hd
    obtain ⟨b, hb⟩ := hIcev
    rw [hcomp] at hb
    exact ⟨a - b, by omega⟩
  have h5 : 5 ≤ p ^ k := hcfg.2.2.2.2.2.2.1
  have hk : k ≠ 0 := by
    rintro rfl
    simp at h5
  have hcardF : Nat.card (GaloisField p k) = p ^ k := GaloisField.card p k hk
  have hsimple : IsSimpleGroup PSL(2, GaloisField p k) :=
    CatalogueBGeneralLinear.projectiveSpecialLinear_simple 2 (GaloisField p k) le_rfl
      (Or.inr (by omega)) (Or.inr (by omega))
  let eQ : ↥(blockP K hw I) ⧸ pPrimeCore 2 ↥(blockP K hw I) ≃* PSL(2, GaloisField p k) :=
    (QuotientGroup.congr _ _ eI.symm (pPrimeCore_map_iso 2 eI.symm)).trans e₁
  have hOI := GSThmB.QPUCl.pPrimeCore_blockP_eq_bot hK hw hIc hNF hq eQ.toEquiv.nontrivial
  have hcard : Nat.card (blockP K hw I) * 2 = p ^ k * ((p ^ k) ^ 2 - 1) := by
    have h1 := card_eq_card_pPrimeCore_mul (R := ↥(blockP K hw I))
    rw [Nat.card_congr eQ.toEquiv, hOI, Subgroup.card_bot, one_mul] at h1
    have hF2 : ringChar (GaloisField p k) ≠ 2 := ringChar_galoisField_ne_two hp2
    rw [h1, card_PSL_mul_two hF2, GorensteinWalter.sl2_card_formula, hcardF]
  rcases block_psl2_cases hw hK hp hKc hIc h3 h5 hcard with ⟨h3', -⟩ | ⟨h4, hk2, hmI⟩
  · exact absurd hIev (by rw [h3']; decide)
  rcases hR₂ with ⟨⟨eR₂⟩, hq₂, h3₂, hNF₂, hcen⟩ | ⟨-, hK3, ⟨g⟩⟩
  ·
    have hqR₂ : IsQuasisimple R₂ := LocalCores.isQuasisimple_of_mulEquiv eR₂.symm hq₂
    obtain ⟨eZ⟩ := hZs hqR₂
    have hLie' := CFSG.LieType.CurtisTits.lieModel_of_mulEquiv
      (eZ.trans (Sol78.centerQuotCongr eR₂)) hLie
    rw [hk2] at hLie'
    obtain ⟨a, ha⟩ : ∃ a, Iᶜ.card = 2 * a := by
      obtain ⟨b, hb⟩ := hIcev
      exact ⟨b, by omega⟩
    have hIcc : Iᶜᶜ.Nonempty := by
      rw [compl_compl]
      exact Finset.card_pos.1 (by omega)
    obtain ⟨rfl, hmIc⟩ := eq_two_of_lieModel_block hw hO hK hp hKc hIcc hNF₂ hq₂ ha
      (by omega) hLie'
    obtain ⟨ψ⟩ := nonempty_blockP_equiv_of_minus hw hK hIc hIcc h4 ha hmI hmIc
    have hcI : center (blockP K hw I) = ⊥ := by
      let eP : blockP K hw I ≃* PSL(2, GaloisField p k) :=
        QuotientGroup.quotientBot.symm.trans
          ((QuotientGroup.quotientMulEquivOfEq hOI.symm).trans eQ)
      rw [← Sol78.map_center_eq_of_mulEquiv eP.symm, GorensteinWalter.psl2_center_eq_bot,
        Subgroup.map_bot]
    apply hcen
    rw [← Sol78.map_center_eq_of_mulEquiv ψ.symm, hcI, Subgroup.map_bot]
  ·
    have hK5 : 5 ≤ Nat.card K := by
      have hodd : Odd (Nat.card K) := CatalogueBLinearHigherB.odd_card_of_ringChar_ne_two K hK
      have h3K : 3 ≤ Nat.card K := by
        rw [hKc]
        have h3p : 3 ≤ p := by have := hp.two_le; omega
        calc 3 ≤ p ^ 1 := by rw [pow_one]; exact h3p
          _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf
      obtain ⟨r, hr⟩ := hodd
      omega
    have hqR₂ : IsQuasisimple R₂ :=
      LocalCores.isQuasisimple_of_mulEquiv g.symm (isQuasisimple_SL2 (exists_card_eq_four hK5))
    obtain ⟨eZ⟩ := hZs hqR₂
    let eY : ↥L ⧸ Open.fusionZStar ↥L ≃* PSL(2, K) := eZ.trans (Sol78.centerQuotCongr g)
    have hadm := LieType.Steinberg.CentralExt.GriessNative.admissible_of_lieModel hLie
    obtain ⟨-, -, hfac⟩ := hO _ τ' n' p k hadm hLie
    have hPSL : Nat.card PSL(2, K) * 2 = p ^ f * ((p ^ f) ^ 2 - 1) := by
      rw [card_PSL_mul_two hK, GorensteinWalter.sl2_card_formula, hKc]
    rw [Nat.card_congr eY.toEquiv, factorization_eq_of_mul_two_eq hp hp2 (by omega) hPSL,
      hk2] at hfac
    rcases Nat.eq_zero_or_pos (lieSylowExponent τ' n') with h0 | hpos
    · rw [h0, zero_mul] at hfac
      omega
    · have : 2 * f ≤ lieSylowExponent τ' n' * (2 * f) := Nat.le_mul_of_pos_left _ hpos
      omega

end P58b.OLie

open P58b.OLie

theorem harris82Lemma58bRowLie_POmegaPlus (hO : LieOrderFormulasInput) (n : ℕ) :
    Harris82Lemma58bRowLie .POmegaPlus n := by
  intro X _ _ hX _ p f hp hp2 hm k c t Q L hcfg hL htL hLie
  obtain ⟨τ', n', hLie⟩ := hLie
  have : Fact p.Prime := ⟨hp⟩
  exfalso
  rcases hm with ⟨-, hc⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩
  rotate_left
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)
  obtain ⟨⟨-, -, hn⟩, K, _, _, hKc, ⟨e⟩⟩ := hc
  have : Fintype K := Fintype.ofFinite K
  have : CharP K p := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  have hK : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  obtain ⟨R, hR, hRQ⟩ := exists_gram h2 (coordinateQuadPlus n K)
    (regular_coordinateQuadPlus n K (by omega)).1
  have hS₁ : ∀ v, oQ R (((1 : GL (Fin (2 * n)) K) : Matrix _ _ K) *ᵥ v) =
      ((1 : Kˣ) : K) * coordinateQuadPlus n K v := by
    intro v
    rw [Units.val_one, one_mulVec, Units.val_one, one_mul, hRQ]
  exact false_of_typeD_model hO hX hp2 hcfg hL htL hLie hK hKc ⟨n, by ring⟩ (by omega) hR
    ((coordinatePlusWitnessEquiv K e).trans (oTransport 1 1 hS₁))

theorem harris82Lemma58bRowLie_POmegaMinus (hO : LieOrderFormulasInput) (n : ℕ) :
    Harris82Lemma58bRowLie .POmegaMinus n := by
  intro X _ _ hX _ p f hp hp2 hm k c t Q L hcfg hL htL hLie
  obtain ⟨τ', n', hLie⟩ := hLie
  have : Fact p.Prime := ⟨hp⟩
  exfalso
  rcases hm with ⟨-, hc⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩
  rotate_left
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)
  obtain ⟨⟨-, -, hn⟩, K, _, _, hKc, b, c', hirr, ⟨e⟩⟩ := hc
  have : Fintype K := Fintype.ofFinite K
  have : CharP K p := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  have hK : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hn1 : 1 ≤ n := by omega
  obtain ⟨R, hR, hRQ⟩ := exists_gram h2 (coordinateQuadMinus n K hn1 b c')
    (regular_coordinateQuadMinus n K b c' hn hirr).1
  have hS₁ : ∀ v, oQ R (((1 : GL (Fin (2 * n)) K) : Matrix _ _ K) *ᵥ v) =
      ((1 : Kˣ) : K) * coordinateQuadMinus n K hn1 b c' v := by
    intro v
    rw [Units.val_one, one_mulVec, Units.val_one, one_mul, hRQ]
  exact false_of_typeD_model hO hX hp2 hcfg hL htL hLie hK hKc ⟨n, by ring⟩ (by omega) hR
    ((coordinateMinusWitnessEquiv K hn1 b c' e).trans (oTransport 1 1 hS₁))

end CFSG.ComponentClassification.HarrisLit.T1
