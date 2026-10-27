module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOEvenOrth2
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X10OrthCent

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB.X10Orth

open Module Matrix CFSG Subgroup CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.TBLit
open CFSG.ComponentClassification.Burgoyne CFSG.ComponentClassification.Burgoyne.O
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.PSL (signMat diagGL coe_diagGL isoOrthGL transportGL
  trans_commutator)
open CFSG.LocalAnalysis.ComponentInitial
  (orthogonal_low_dimensional_fixed_derived_component_coverage)
open CFSG.ComponentClassification.CatalogueBOrthogonalFourNonsplit (extension specialRho
  specialImage specialRho_eq_one_iff_sign extension_card)
open CFSG.ComponentClassification.CatalogueBOrthogonalNonsplitFourComponents (specialLinearCover
  specialLinearCover_surjective specialLinearCover_kernel_central)
open scoped MatrixGroups

section Hermitian

variable {E : Type} [Field E] [Finite E] (δ : E) [Fact (¬ IsSquare δ)]

omit [Finite E] in
theorem ker_specialLinearCover_eq_center (h2 : (2 : E) ≠ 0) :
    (specialLinearCover δ h2).ker = center (SL(2, extension δ)) := by
  refine le_antisymm (specialLinearCover_kernel_central δ h2) fun A hA => ?_
  rw [Matrix.SpecialLinearGroup.mem_center_iff] at hA
  obtain ⟨r, hr, hrA⟩ := hA
  rw [Fintype.card_fin, sq] at hr
  have hA' : A = 1 ∨ A = -1 := by
    rcases mul_self_eq_one_iff.1 hr with rfl | rfl
    · left
      apply Subtype.ext
      rw [← hrA, Matrix.SpecialLinearGroup.coe_one, map_one]
    · right
      apply Subtype.ext
      rw [← hrA, Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
        map_neg, map_one]
  rw [MonoidHom.mem_ker]
  exact Subtype.ext ((specialRho_eq_one_iff_sign δ h2 A).2 hA')

@[expose] def specialImageEquiv (h2 : (2 : E) ≠ 0) :
    specialImage δ h2 ≃* PSL(2, extension δ) :=
  (QuotientGroup.quotientKerEquivOfSurjective _ (specialLinearCover_surjective δ h2)).symm.trans
    (QuotientGroup.quotientMulEquivOfEq (ker_specialLinearCover_eq_center δ h2))

omit [Finite E] [Fact (¬ IsSquare δ)] in
theorem card_extension : Nat.card (extension δ) = Nat.card E ^ 2 := extension_card δ

theorem isSimpleGroup_specialImage (h2 : (2 : E) ≠ 0) : IsSimpleGroup (specialImage δ h2) := by
  have h4 : 4 ≤ Nat.card (extension δ) := by
    rw [card_extension]
    have := Finite.one_lt_card (α := E)
    nlinarith
  have := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
  exact (specialImageEquiv δ h2).isSimpleGroup

theorem card_specialImage (h2 : (2 : E) ≠ 0) :
    Nat.card (specialImage δ h2) * 2 =
      Nat.card (extension δ) * (Nat.card (extension δ) ^ 2 - 1) := by
  have h2' : ringChar (extension δ) ≠ 2 := by
    intro h
    apply h2
    have := ringChar.Nat.cast_ringChar (R := extension δ)
    rw [h, Nat.cast_ofNat] at this
    exact (algebraMap E (extension δ)).injective (by rw [map_ofNat, this, map_zero])
  have hq := (center (SL(2, extension δ))).card_eq_card_quotient_mul_card_subgroup
  rw [C.card_center_SL_two h2', LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq
    (by norm_num)] at hq
  rw [Nat.card_congr (specialImageEquiv δ h2).toEquiv]
  change Nat.card (SL(2, extension δ) ⧸ center (SL(2, extension δ))) * 2 = _
  rw [← hq]
  norm_num

end Hermitian

theorem eq_of_mul_sq_sub_one_eq {x y : ℕ} (hx : 1 ≤ x) (hy : 1 ≤ y)
    (h : x * (x ^ 2 - 1) = y * (y ^ 2 - 1)) : x = y := by
  have key : ∀ a b : ℕ, 1 ≤ a → a < b → a * (a ^ 2 - 1) < b * (b ^ 2 - 1) := by
    intro a b ha hab
    have h1 : a ^ 2 < b ^ 2 := Nat.pow_lt_pow_left hab (by norm_num)
    have h2 : 1 ≤ a ^ 2 := Nat.one_le_pow _ _ ha
    have h3 : a ^ 2 - 1 < b ^ 2 - 1 := by omega
    calc a * (a ^ 2 - 1) ≤ b * (a ^ 2 - 1) := Nat.mul_le_mul_right _ hab.le
      _ < b * (b ^ 2 - 1) := Nat.mul_lt_mul_of_pos_left h3 (by omega)
  rcases lt_trichotomy x y with hxy | hxy | hxy
  · exact absurd h (key x y hx hxy).ne
  · exact hxy
  · exact absurd h (key y x hy hxy).ne'

theorem even_of_two_mul_eq {m x : ℕ} (hx : Odd x) (h : m * 2 = x * (x ^ 2 - 1)) : Even m := by
  obtain ⟨k, rfl⟩ := hx
  have hk : (2 * k + 1) ^ 2 - 1 = 4 * (k * (k + 1)) := by
    have : (2 * k + 1) ^ 2 = 4 * (k * (k + 1)) + 1 := by ring
    omega
  rw [hk] at h
  obtain ⟨j, hj⟩ := Nat.even_mul_succ_self k
  refine ⟨2 * ((2 * k + 1) * j), ?_⟩
  have : m * 2 = 8 * ((2 * k + 1) * j) := by
    rw [h, hj]
    ring
  omega

variable {K : Type} [Field K] [Finite K]

theorem card_of_orth2_nonsplit (hK : ringChar K ≠ 2) {c : K} (hc : ¬ IsSquare c)
    [Fact (Irreducible (sqPoly c))] {w : Fin 4 → EAlg c} (hw : ∀ i, w i ≠ 0)
    {R : GL (Fin (2 * 4)) K} (hRs : (R : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K)ᵀ = R)
    (hR : (R : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) =
      blkDiag 4 (wMat 1 c) * resMat (phiE c).toRingHom 4 (diagonal w))
    {gs : similarityPairs (oQ R)} (hσ : gs.val.right = 1)
    (hgA : (gs.val.left : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) = blkDiag 4 (jMat c))
    {M : Subgroup (GL (Fin (2 * 4)) K)} {Q : ℕ} (h : X10Data R gs M Q) (hQ : Odd Q)
    (hS : ¬ ∃ S : Submodule (EAlg c) (Fin 4 → EAlg c), Module.finrank (EAlg c) S = 2 ∧
      ∀ x ∈ S, CatalogueBLinearHigherB.matrixQuadraticForm (diagGL hw) x = 0) :
    Nat.card K ^ 4 = Q := by
  have hc0 : c ≠ 0 := fun h => hc ⟨0, by rw [h, mul_zero]⟩
  obtain ⟨hEf, hE⟩ := finite_ringChar_EAlg hK hc0
  have hoddE := CatalogueBLinearHigherB.odd_card_of_ringChar_ne_two (EAlg c) hE
  have hcardE : Nat.card (EAlg c) = Nat.card K ^ 2 := card_EAlg hc0
  set Rw : GL (Fin 4) (EAlg c) := diagGL hw with hRwdef
  have hRw : (Rw : Matrix (Fin 4) (Fin 4) (EAlg c))ᵀ = Rw := diagGL_transpose hw
  set QE := CatalogueBLinearHigherB.matrixQuadraticForm Rw with hQE
  have hQnd := CatalogueBLinearHigherB.polarBilin_matrixQuadraticForm_nondegenerate hE Rw hRw
  have hdim : Module.finrank (EAlg c) (Fin 4 → EAlg c) = 4 := Module.finrank_fin_fun _
  have hcov := orthogonal_low_dimensional_fixed_derived_component_coverage QE hQnd
    (Or.inl ⟨hoddE, Or.inr (Or.inl hdim)⟩)
  obtain ⟨δ, hδ, -, ψ, e', -, -, hcomm_eq, hq⟩ := hcov.2.2.2.2.1 hoddE hdim hS
  clear hcov
  have : Fact (¬ IsSquare (δ : EAlg c)) := ⟨hδ⟩
  set h2E := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hoddE with hh2E
  set I := CatalogueBGraphForm.isometryGroup 4 (EAlg c) Rw with hI
  set φ := (phiE c).toRingHom with hφ
  set θ : specialImage (δ : EAlg c) h2E →* GL (Fin (2 * 4)) K := (resGL φ 4).comp (I.subtype.comp
    ((isoOrthGL hE Rw hRw).toMonoidHom.comp (e'.symm.toMonoidHom.comp
      (specialImage (δ : EAlg c) h2E).subtype))) with hθ
  have hθi : Function.Injective θ :=
    (resGL_injective (phiE_injective c) 4).comp (Subtype.val_injective.comp
      ((isoOrthGL hE Rw hRw).injective.comp (e'.symm.injective.comp Subtype.val_injective)))
  have hZ := commutator_iso_inf_centralizer_eq (φ := φ) (σ := RingHom.id (EAlg c))
    (r := AdjoinRoot.root (sqPoly c)) (phiE_injective c) (wOne_inv_mul hc0)
    (fun x => transpose_phiE_mul_wOne hc0 x) (phiE_root c) (fun M hM => phiE_mem_range hc0 hM)
    (diagonal w) hR hgA
  rw [uGrp_id_eq_iso hw] at hZ
  have hN : (⁅isoCent R gs.val.left, isoCent R gs.val.left⁆ : Subgroup (GL (Fin (2 * 4)) K)) =
      θ.range := by
    rw [hZ, ← trans_commutator (isoOrthGL hE Rw hRw), hcomm_eq, hθ, MonoidHom.range_comp,
      MonoidHom.range_comp, MonoidHom.range_comp, MonoidHom.range_comp, Subgroup.range_subtype,
      transportGL]
  have eN : (⁅isoCent R gs.val.left, isoCent R gs.val.left⁆ : Subgroup (GL (Fin (2 * 4)) K)) ≃*
      specialImage (δ : EAlg c) h2E :=
    (MulEquiv.subgroupCongr hN).trans (MonoidHom.ofInjective hθi).symm
  have hNs : IsSimpleGroup (⁅isoCent R gs.val.left, isoCent R gs.val.left⁆ :
      Subgroup (GL (Fin (2 * 4)) K)) := by
    have := isSimpleGroup_specialImage (δ : EAlg c) h2E
    exact eN.isSimpleGroup
  have hNc : Nat.card (⁅isoCent R gs.val.left, isoCent R gs.val.left⁆ :
      Subgroup (GL (Fin (2 * 4)) K)) * 2 =
        Nat.card (extension (δ : EAlg c)) * (Nat.card (extension (δ : EAlg c)) ^ 2 - 1) := by
    rw [Nat.card_congr eN.toEquiv]
    exact card_specialImage (δ : EAlg c) h2E
  have hNq : IsQuasisimple (⁅isoCent R gs.val.left, isoCent R gs.val.left⁆ :
      Subgroup (GL (Fin (2 * 4)) K)) := by
    set θ' : _root_.commutator (TauCeti.QuadraticMap.orthogonalGroup QE) →*
        GL (Fin (2 * 4)) K := (resGL φ 4).comp (I.subtype.comp
      ((isoOrthGL hE Rw hRw).toMonoidHom.comp (_root_.commutator _).subtype)) with hθ'
    have hθ'i : Function.Injective θ' :=
      (resGL_injective (phiE_injective c) 4).comp (Subtype.val_injective.comp
        ((isoOrthGL hE Rw hRw).injective.comp Subtype.val_injective))
    have hN' : (⁅isoCent R gs.val.left, isoCent R gs.val.left⁆ :
        Subgroup (GL (Fin (2 * 4)) K)) = θ'.range := by
      rw [hZ, ← trans_commutator (isoOrthGL hE Rw hRw), hθ', MonoidHom.range_comp,
        MonoidHom.range_comp, MonoidHom.range_comp, Subgroup.range_subtype, transportGL]
    exact LocalCores.isQuasisimple_of_mulEquiv
      ((MonoidHom.ofInjective hθ'i).trans (MulEquiv.subgroupCongr hN'.symm)) hq
  obtain ⟨hNH, heq⟩ := h.map_eq_isoCent hK hRs hσ (Or.inr hNq)
  obtain ⟨N, hNdef⟩ : ∃ N : Subgroup (GL (Fin (2 * 4)) K),
      N = ⁅isoCent R gs.val.left, isoCent R gs.val.left⁆ := ⟨_, rfl⟩
  rw [← hNdef] at hNH heq hNs hNc
  clear hN eN hNq hZ
  obtain ⟨H, hH⟩ : ∃ H : Subgroup (GL (Fin (2 * 4)) K), H = matrixDerived (oQ R) := ⟨_, rfl⟩
  rw [← hH] at hNH heq
  obtain ⟨lamN, hlamN⟩ : ∃ f : N →* StatedProj H, f = (projH H).comp (inclusion hNH) :=
    ⟨_, rfl⟩
  have hlamr : lamN.range = (N.subgroupOf H).map (projH H) := by
    rw [hlamN, MonoidHom.range_comp]
    congr 1
    ext x
    simp [mem_subgroupOf]
  have hlami : Function.Injective lamN := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal lamN.ker with hb | ht
    · exact hb
    · exfalso
      have hbot : lamN.range = ⊥ := by
        rw [eq_bot_iff]
        rintro _ ⟨x, rfl⟩
        exact (MonoidHom.mem_ker.1 (ht ▸ mem_top x)) ▸ one_mem _
      rw [hlamr, ← heq] at hbot
      rw [hH] at hbot
      exact C.ne_bot_of_isPComponent h.fix h.comp hbot
  have eP : N ≃* ((M.subgroupOf H).map (projH H)) :=
    (MonoidHom.ofInjective hlami).trans (MulEquiv.subgroupCongr (hlamr.trans heq.symm))
  have hcardP : Nat.card ((M.subgroupOf H).map (projH H)) = Nat.card N :=
    (Nat.card_congr eP.toEquiv).symm
  have hEven : Even (Nat.card N) := even_of_two_mul_eq (by
    rw [card_extension, hcardE]
    exact Odd.pow (Odd.pow (CatalogueBLinearHigherB.odd_card_of_ringChar_ne_two K hK))) hNc
  have hO : Nat.card (pPrimeCore 2 ((M.subgroupOf H).map (projH H))) = 1 := by
    have : IsSimpleGroup ((M.subgroupOf H).map (projH H)) := eP.symm.isSimpleGroup
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := pPrimeCore_normal (p := 2) (G := ((M.subgroupOf H).map (projH H)))
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (pPrimeCore 2 ((M.subgroupOf H).map (projH H))) with hb | ht
    · rw [hb, Subgroup.card_bot]
    · exfalso
      have hcop := pPrimeCore_coprime_card (p := 2) (G := ((M.subgroupOf H).map (projH H)))
      rw [ht, Subgroup.card_top, hcardP] at hcop
      exact (Nat.coprime_two_left.1 hcop).not_two_dvd_nat (even_iff_two_dvd.1 hEven)
  have hcard := h.hyp.card
  rw [← hH] at hcard
  rw [hO, one_mul, hcardP] at hcard
  have hQe : Q * (Q ^ 2 - 1) / 2 * 2 = Q * (Q ^ 2 - 1) := by
    apply Nat.div_mul_cancel
    have : Even (Q ^ 2 - 1) := Nat.Odd.sub_odd hQ.pow odd_one
    exact (even_iff_two_dvd.1 this).mul_left _
  have hEQ : Nat.card (extension (δ : EAlg c)) = Q := by
    refine eq_of_mul_sq_sub_one_eq ?_ hQ.pos ?_
    · rw [card_extension, hcardE]
      exact Nat.one_le_pow _ _ (Nat.one_le_pow _ _ Nat.card_pos)
    · rw [← hNc, hcard, hQe]
  rw [← hEQ, card_extension, hcardE, ← pow_mul]

end CFSG.ComponentClassification.GSThmB.X10Orth
