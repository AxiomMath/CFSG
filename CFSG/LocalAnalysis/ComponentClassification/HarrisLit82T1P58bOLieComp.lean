module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51eOrthSign

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P58b.OLie

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.Burgoyne.O CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.C
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL signMat)
open CFSG.ComponentClassification.HarrisLit.T1.P51e.Comp (comp_map_mulEquiv)
open CFSG.ComponentClassification.HarrisLit.T1.P51e.Orth (sign_comp_cases even_card_of_mem_comp)
open scoped MatrixGroups

theorem false_of_mem_center_psl2 {R : Type*} [Group R] [Finite R] {F : Type*} [Field F]
    [Finite F] (e : R ⧸ pPrimeCore 2 R ≃* PSL(2, F)) {x : R} (hx : x ∈ center R)
    (hx2 : orderOf x = 2) : False := by
  have hc : e (QuotientGroup.mk x) ∈ center PSL(2, F) := by
    rw [mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective (pPrimeCore 2 R))) g
    change e (QuotientGroup.mk y) * e (QuotientGroup.mk x) =
      e (QuotientGroup.mk x) * e (QuotientGroup.mk y)
    rw [← map_mul, ← map_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
      mem_center_iff.1 hx y]
  rw [GorensteinWalter.psl2_center_eq_bot, mem_bot, map_eq_one_iff _ e.injective,
    QuotientGroup.eq_one_iff] at hc
  exact not_mem_pPrimeCore_of_orderOf hx2 hc

theorem false_of_sl2_of_psl2 {R : Type*} [Group R] [Finite R] {K F : Type*} [Field K] [Finite K]
    [Field F] [Finite F] (hK : ringChar K ≠ 2) (g : R ≃* SL(2, K))
    (e : R ⧸ pPrimeCore 2 R ≃* PSL(2, F)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := center SL(2, K)) 2
    (by rw [card_center_SL_two hK])
  have hyc : g.symm (y : SL(2, K)) ∈ center R := by
    rw [mem_center_iff]
    intro r
    apply g.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact mem_center_iff.1 y.2 (g r)
  refine false_of_mem_center_psl2 e hyc ?_
  rw [MulEquiv.orderOf_eq, Subgroup.orderOf_coe, hy]

variable {K : Type} [Field K] {d : ℕ}

theorem rank_signMat_add_one (hK : ringChar K ≠ 2) (J : Finset (Fin d)) :
    (signMat K J + 1).rank = Jᶜ.card := by
  classical
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hdiag : signMat K J + 1 = diagonal fun i => if i ∈ J then (0 : K) else 2 := by
    rw [signMat, ← diagonal_one, diagonal_add]
    congr 1
    ext i
    split_ifs <;> norm_num
  rw [hdiag, rank_diagonal, Fintype.card_subtype]
  congr 1
  ext i
  simp [Finset.mem_compl, h2]

theorem even_card_of_signGL_mem (hK : ringChar K ≠ 2) {R : GL (Fin d) K} {J : Finset (Fin d)}
    (hJ : signGL K J ∈ matrixDerived (oQ R)) : Even J.card := by
  have hdet := det_eq_one_of_mem_commutator hJ
  rw [coe_signGL, signMat, det_diagonal, Finset.prod_ite_mem, Finset.univ_inter,
    Finset.prod_const] at hdet
  have hne : (-1 : K) ≠ 1 := fun h => Ring.two_ne_zero hK (by linear_combination -h)
  exact (neg_one_pow_eq_one_iff_even hne).1 hdet

variable [Finite K]

theorem exists_sign_frame_rank (hK : ringChar K ≠ 2) {R : GL (Fin d) K}
    (hR : (R : Matrix (Fin d) (Fin d) K)ᵀ = R) {T : GL (Fin d) K}
    (hT : T ∈ matrixDerived (oQ R)) (hT2 : (T : Matrix (Fin d) (Fin d) K) * T = 1)
    (hT1 : projH _ (⟨T, hT⟩ : matrixDerived (oQ R)) ≠ 1) :
    ∃ (w : Fin d → K) (hw : ∀ i, w i ≠ 0) (J : Finset (Fin d))
      (hJ : signGL K J ∈ matrixDerived (oQ (diagGL hw)))
      (θ : StatedProj (matrixDerived (oQ R)) ≃* StatedProj (matrixDerived (oQ (diagGL hw)))),
      J.Nonempty ∧ Jᶜ.Nonempty ∧
      (∀ I : Finset (Fin d), (I = J ∨ I = Jᶜ) → 3 ≤ I.card → BlockNF w I) ∧
      θ (projH _ ⟨T, hT⟩) = projH _ ⟨signGL K J, hJ⟩ ∧
      ((T : Matrix (Fin d) (Fin d) K) + 1).rank = Jᶜ.card := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hTiso : T ∈ matrixIsometries (oQ R) := matrixDerived_le_isometries _ hT
  have hTR : (T : Matrix (Fin d) (Fin d) K)ᵀ * R * T = R :=
    (CatalogueBGraphForm.mem_isometryGroup _ _ _ _).1
      ((mem_matrixIsometries_oQ h2 R hR T).1 hTiso)
  obtain ⟨hab, cfr, hcA, horth, hdiag, hNF₁, hNF₂⟩ := exists_split_nf hK hR hTR hT2
  obtain ⟨hw, S, hS, heq⟩ := exists_transport_of_family h2 hTiso hab cfr hcA horth hdiag
  have hST : S * T * S⁻¹ = signGL K (famJ hab) := by
    have e := congrArg (fun g : similarityPairs (oQ (diagGL hw)) => g.val.left) heq
    simp only [transPair_left, linPair_left, linPair_right, map_one, MulAut.one_apply] at e
    rw [sgnPair, linPair_left] at e
    exact e
  have hXv : ((derivedTransport S 1 hS ⟨T, hT⟩ : matrixDerived (oQ (diagGL hw))) :
      GL (Fin d) K) = signGL K (famJ hab) := by
    rw [coe_derivedTransport]
    exact hST
  have hJ : signGL K (famJ hab) ∈ matrixDerived (oQ (diagGL hw)) :=
    hXv ▸ (derivedTransport S 1 hS ⟨T, hT⟩).2
  have hθt : oTransport S 1 hS (projH _ ⟨T, hT⟩) = projH _ ⟨signGL K (famJ hab), hJ⟩ := by
    rw [oTransport_proj]
    congr 1
    exact Subtype.ext hXv
  have hθ1 : oTransport S 1 hS (projH _ ⟨T, hT⟩) ≠ 1 := fun h1 =>
    hT1 ((oTransport S 1 hS).injective (by rw [h1, map_one]))
  have hrankJ : ∀ J : Finset (Fin d), S * T * S⁻¹ = signGL K J →
      ((T : Matrix (Fin d) (Fin d) K) + 1).rank = Jᶜ.card := by
    intro J hSTJ
    have hTm : (T : Matrix (Fin d) (Fin d) K) =
        ((S⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * signMat K J * S := by
      rw [← coe_signGL, ← hSTJ]
      simp only [Units.val_mul]
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mul, Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.mul_one]
    have hsum : (T : Matrix (Fin d) (Fin d) K) + 1 =
        ((S⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * (signMat K J + 1) * S := by
      rw [hTm, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, ← Units.val_mul, inv_mul_cancel,
        Units.val_one]
    rw [hsum, rank_mul_eq_left_of_isUnit_det _ _ (Matrix.isUnits_det_units S),
      rank_mul_eq_right_of_isUnit_det _ _ (Matrix.isUnits_det_units S⁻¹),
      rank_signMat_add_one hK]
  have hrank := hrankJ _ hST
  refine ⟨_, hw, famJ hab, hJ, oTransport S 1 hS, ?_, ?_, ?_, hθt, hrank⟩
  · rw [Finset.nonempty_iff_ne_empty]
    intro hJe
    apply hθ1
    rw [hθt]
    have e : (⟨signGL K (famJ hab), hJ⟩ : matrixDerived (oQ (diagGL hw))) = 1 := by
      apply Subtype.ext
      apply Units.ext
      change ((signGL K (famJ hab) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = 1
      rw [coe_signGL, hJe]
      ext i j
      simp [signMat, Matrix.diagonal_apply, Matrix.one_apply]
    rw [e, map_one]
  · rw [Finset.nonempty_iff_ne_empty]
    intro hJe
    apply hθ1
    rw [hθt]
    have hJu : famJ hab = Finset.univ := (Finset.compl_eq_empty_iff _).1 hJe
    have hsc : signGL K (famJ hab) = GeneralLinearGroup.scalar (Fin d) (-1 : Kˣ) := by
      apply Units.ext
      rw [coe_signGL, GeneralLinearGroup.coe_scalar, hJu]
      ext i j
      simp [signMat, Matrix.diagonal_apply, Matrix.scalar_apply]
    have hmem : GeneralLinearGroup.scalar (Fin d) (-1 : Kˣ) ∈ matrixDerived (oQ (diagGL hw)) :=
      hsc ▸ hJ
    have e : (⟨signGL K (famJ hab), hJ⟩ : matrixDerived (oQ (diagGL hw))) =
        ⟨GeneralLinearGroup.scalar (Fin d) (-1 : Kˣ), hmem⟩ := Subtype.ext hsc
    rw [e]
    exact (QuotientGroup.eq_one_iff _).2 (mem_subgroupOf.2 ⟨-1, rfl⟩)
  · rintro I (rfl | rfl) h3
    · exact hNF₁ (by rw [card_famJ] at h3; exact h3)
    · apply hNF₂
      rw [Finset.card_compl, Fintype.card_fin, card_famJ] at h3
      omega

section Diag

variable {w : Fin d → K} (hw : ∀ i, w i ≠ 0)

include hw in
theorem two_comps (hK : ringChar K ≠ 2) {F : Type*} [Field F] [Finite F]
    (J : Finset (Fin d)) (hJ : signGL K J ∈ matrixDerived (oQ (diagGL hw)))
    (hJne : J.Nonempty) (hJcne : Jᶜ.Nonempty)
    (hNF : ∀ I : Finset (Fin d), (I = J ∨ I = Jᶜ) → 3 ≤ I.card → BlockNF w I)
    {R₁ R₂ : Subgroup (StatedProj (matrixDerived (oQ (diagGL hw))))}
    (h₁H : R₁ ≤ centralizer ({projH _ ⟨signGL K J, hJ⟩} : Set _))
    (h₁ : IsPComponent 2 (R₁.subgroupOf (centralizer ({projH _ ⟨signGL K J, hJ⟩} : Set _))))
    (e₁ : ↥R₁ ⧸ pPrimeCore 2 ↥R₁ ≃* PSL(2, F))
    (h₂H : R₂ ≤ centralizer ({projH _ ⟨signGL K J, hJ⟩} : Set _))
    (h₂ : IsPComponent 2 (R₂.subgroupOf (centralizer ({projH _ ⟨signGL K J, hJ⟩} : Set _))))
    (hz₂ : projH _ (⟨signGL K J, hJ⟩ : matrixDerived (oQ (diagGL hw))) ∈ R₂) :
    ∃ I : Finset (Fin d), (I = J ∨ I = Jᶜ) ∧ Iᶜ.Nonempty ∧ BlockNF w I ∧ R₁ = blockP K hw I ∧
      IsQuasisimple (blockP K hw I) ∧ 3 ≤ I.card ∧ Even Iᶜ.card ∧ R₂ ≤ blockP K hw Iᶜ ∧
      ((R₂ = blockP K hw Iᶜ ∧ IsQuasisimple (blockP K hw Iᶜ) ∧ 3 ≤ Iᶜ.card ∧ BlockNF w Iᶜ) ∨
        (Iᶜ.card = 4 ∧ Nat.card K ≠ 3 ∧ IsQuasisimple R₂ ∧ Nonempty (↥R₂ ≃* SL(2, K)))) := by
  set z := projH _ (⟨signGL K J, hJ⟩ : matrixDerived (oQ (diagGL hw))) with hz
  have hz2 : orderOf z = 2 := orderOf_projH_sign hw hK hJ hJne hJcne
  obtain ⟨I₁, hI₁, hI₁c, hR₁I, hc₁⟩ := sign_comp_cases hw hK J hJ hJne hJcne h₁H h₁
  obtain ⟨hR₁e, hq₁, h3₁⟩ : R₁ = blockP K hw I₁ ∧ IsQuasisimple R₁ ∧ 3 ≤ I₁.card := by
    rcases hc₁ with h | ⟨-, -, -, ⟨g⟩⟩
    · exact h
    · exact (false_of_sl2_of_psl2 hK g e₁).elim
  obtain ⟨I₂, hI₂, hI₂c, hR₂I, hc₂⟩ := sign_comp_cases hw hK J hJ hJne hJcne h₂H h₂
  have hev := even_card_of_mem_comp hw hK J I₂ hI₂ hJ hI₂c hR₂I hz₂
  have hne : I₁ ≠ I₂ := by
    rintro rfl
    have hzR₁ : z ∈ R₁ := hR₁e ▸ hR₂I hz₂
    have hzc : (⟨z, hzR₁⟩ : R₁) ∈ center R₁ := by
      rw [mem_center_iff]
      intro y
      exact Subtype.ext (mem_centralizer_singleton_iff.1 (h₁H y.2))
    exact false_of_mem_center_psl2 e₁ hzc (by rw [Subgroup.orderOf_mk, hz2])
  have hI₂e : I₂ = I₁ᶜ := by
    rcases hI₁ with rfl | rfl <;> rcases hI₂ with rfl | rfl
    · exact absurd rfl hne
    · rfl
    · rw [compl_compl]
    · exact absurd rfl hne
  subst hI₂e
  have hI₁' : I₁ᶜ = J ∨ I₁ᶜ = Jᶜ := by
    rcases hI₁ with rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl (compl_compl _)
  refine ⟨I₁, hI₁, hI₁c, hNF I₁ hI₁ h3₁, hR₁e, hR₁e ▸ hq₁, h3₁, hev, hR₂I, ?_⟩
  rcases hc₂ with ⟨hR₂e, hq₂, h3₂⟩ | h
  · exact Or.inl ⟨hR₂e, hR₂e ▸ hq₂, h3₂, hNF _ hI₁' h3₂⟩
  · exact Or.inr h

end Diag

theorem two_comps_of_model (hK : ringChar K ≠ 2) {F : Type*} [Field F] [Finite F]
    {R : GL (Fin d) K} (hR : (R : Matrix (Fin d) (Fin d) K)ᵀ = R) {T : GL (Fin d) K}
    (hT : T ∈ matrixDerived (oQ R)) (hT2 : (T : Matrix (Fin d) (Fin d) K) * T = 1)
    (hT1 : projH _ (⟨T, hT⟩ : matrixDerived (oQ R)) ≠ 1)
    {R₁ R₂ : Subgroup (StatedProj (matrixDerived (oQ R)))}
    (h₁H : R₁ ≤ centralizer {projH _ (⟨T, hT⟩ : matrixDerived (oQ R))})
    (h₁ : IsPComponent 2 (R₁.subgroupOf (centralizer {projH _ (⟨T, hT⟩ : matrixDerived (oQ R))})))
    (e₁ : ↥R₁ ⧸ pPrimeCore 2 ↥R₁ ≃* PSL(2, F))
    (h₂H : R₂ ≤ centralizer {projH _ (⟨T, hT⟩ : matrixDerived (oQ R))})
    (h₂ : IsPComponent 2 (R₂.subgroupOf (centralizer {projH _ (⟨T, hT⟩ : matrixDerived (oQ R))})))
    (hz₂ : projH _ (⟨T, hT⟩ : matrixDerived (oQ R)) ∈ R₂) :
    ∃ (w : Fin d → K) (hw : ∀ i, w i ≠ 0) (J I : Finset (Fin d)),
      Even J.card ∧ ((T : Matrix (Fin d) (Fin d) K) + 1).rank = Jᶜ.card ∧ (I = J ∨ I = Jᶜ) ∧
      Iᶜ.Nonempty ∧ BlockNF w I ∧ IsQuasisimple (blockP K hw I) ∧ 3 ≤ I.card ∧
      Nonempty (↥R₁ ≃* blockP K hw I) ∧ Even Iᶜ.card ∧
      ((Nonempty (↥R₂ ≃* blockP K hw Iᶜ) ∧ IsQuasisimple (blockP K hw Iᶜ) ∧ 3 ≤ Iᶜ.card ∧
          BlockNF w Iᶜ ∧ center (blockP K hw Iᶜ) ≠ ⊥) ∨
        (Iᶜ.card = 4 ∧ Nat.card K ≠ 3 ∧ Nonempty (↥R₂ ≃* SL(2, K)))) := by
  obtain ⟨w, hw, J, hJ, θ, hJne, hJc, hNF, hθz, hrank⟩ := exists_sign_frame_rank hK hR hT hT2 hT1
  obtain ⟨h₁H', h₁'⟩ := comp_map_mulEquiv θ h₁H h₁
  obtain ⟨h₂H', h₂'⟩ := comp_map_mulEquiv θ h₂H h₂
  rw [hθz] at h₁H' h₁' h₂H' h₂'
  let eR₁ : R₁ ≃* R₁.map θ.toMonoidHom := R₁.equivMapOfInjective θ.toMonoidHom θ.injective
  let eR₂ : R₂ ≃* R₂.map θ.toMonoidHom := R₂.equivMapOfInjective θ.toMonoidHom θ.injective
  have e₁' : ↥(R₁.map θ.toMonoidHom) ⧸ pPrimeCore 2 ↥(R₁.map θ.toMonoidHom) ≃* PSL(2, F) :=
    (QuotientGroup.congr _ _ eR₁.symm (pPrimeCore_map_iso 2 eR₁.symm)).trans e₁
  have hz₂' : projH _ (⟨signGL K J, hJ⟩ : matrixDerived (oQ (diagGL hw))) ∈
      R₂.map θ.toMonoidHom := hθz ▸ mem_map_of_mem θ.toMonoidHom hz₂
  obtain ⟨I, hI, hIc, hNFI, hR₁e, hq, h3, hev, hR₂I, hc₂⟩ :=
    two_comps hw hK J hJ hJne hJc hNF h₁H' h₁' e₁' h₂H' h₂' hz₂'
  refine ⟨w, hw, J, I, even_card_of_signGL_mem hK hJ, hrank, hI, hIc, hNFI, hq, h3,
    ⟨eR₁.trans (MulEquiv.subgroupCongr hR₁e)⟩, hev, ?_⟩
  rcases hc₂ with ⟨hR₂e, hq₂, h3₂, hNF₂⟩ | ⟨h4, hK3, -, ⟨g⟩⟩
  · refine Or.inl ⟨⟨eR₂.trans (MulEquiv.subgroupCongr hR₂e)⟩, hq₂, h3₂, hNF₂, ?_⟩
    have hzP : projH _ (⟨signGL K J, hJ⟩ : matrixDerived (oQ (diagGL hw))) ∈ blockP K hw Iᶜ :=
      hR₂e ▸ hz₂'
    intro hbot
    have hzc : (⟨_, hzP⟩ : blockP K hw Iᶜ) ∈ center (blockP K hw Iᶜ) := by
      rw [mem_center_iff]
      intro y
      exact Subtype.ext (mem_centralizer_singleton_iff.1 (h₂H' (by rw [hR₂e]; exact y.2)))
    rw [hbot, mem_bot] at hzc
    have h1 := congrArg Subtype.val hzc
    have hz2 := orderOf_projH_sign hw hK hJ hJne hJc
    rw [show ((⟨_, hzP⟩ : blockP K hw Iᶜ) : StatedProj (matrixDerived (oQ (diagGL hw)))) =
      projH _ ⟨signGL K J, hJ⟩ from rfl] at h1
    rw [h1, OneMemClass.coe_one, orderOf_one] at hz2
    exact absurd hz2 (by norm_num)
  · exact Or.inr ⟨h4, hK3, ⟨eR₂.trans g⟩⟩

end CFSG.ComponentClassification.HarrisLit.T1.P58b.OLie
