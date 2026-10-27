module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X10OrthSign
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneCOSign
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUClOData

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB.QPUCl

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.Burgoyne.O CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL signMat)
open scoped MatrixGroups

variable {K : Type} [Field K] {d : ℕ}

theorem false_of_equiv_SL {R : Type} [Group R] [Finite R] {F : Type} [Field F]
    (h2 : (2 : F) ≠ 0) (hq : IsQuasisimple R) (e : R ≃* SL(2, F)) {p f : ℕ}
    (hm : Blueprint.LieModel (R ⧸ pPrimeCore 2 R) .PSL 2 p f) : False := by
  set z := e.symm (-1) with hz
  have hneg1 : (-1 : SL(2, F)) ≠ 1 := by
    intro h
    have e1 := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 0) h
    simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
      Matrix.neg_apply, Matrix.one_apply_eq] at e1
    exact h2 (by linear_combination -e1)
  have hz1 : z ≠ 1 := fun h1 => hneg1 (by rw [← e.apply_symm_apply (-1), ← hz, h1, map_one])
  have hzc : z ∈ center R := by
    rw [mem_center_iff]
    intro g
    apply e.injective
    rw [map_mul, map_mul, hz, MulEquiv.apply_symm_apply]
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_neg,
      Matrix.SpecialLinearGroup.coe_one, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_one,
      Matrix.one_mul]
  have hz2 : z ^ 2 = 1 := by
    apply e.injective
    rw [map_pow, hz, MulEquiv.apply_symm_apply, map_one, pow_two]
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_neg,
      Matrix.SpecialLinearGroup.coe_one, Matrix.neg_mul, Matrix.mul_neg, Matrix.one_mul,
      neg_neg]
  have hord : orderOf z = 2 := orderOf_eq_prime hz2 hz1
  have hO : pPrimeCore 2 R = ⊥ := Burgoyne.C.pPrimeCore_eq_bot_of_center hq hord fun y hy => by
    have hy' : e y ∈ center SL(2, F) := by
      rw [mem_center_iff]
      intro g
      obtain ⟨g', rfl⟩ := e.surjective g
      rw [← map_mul, ← map_mul, mem_center_iff.1 hy g']
    apply e.injective
    rw [map_pow, Burgoyne.C.sq_eq_one_of_mem_center_SL hy', map_one]
  have : Group.IsPerfect R := hq.1
  have : Group.IsPerfect (R ⧸ pPrimeCore 2 R) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (pPrimeCore 2 R))
      (QuotientGroup.mk'_surjective _)
  have hZ := center_eq_bot_of_lieModel (Or.inl rfl) hm
  have hc : (QuotientGroup.mk' (pPrimeCore 2 R) z) ∈ center (R ⧸ pPrimeCore 2 R) := by
    rw [mem_center_iff]
    intro g
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ g
    rw [← map_mul, ← map_mul, mem_center_iff.1 hzc g]
  rw [hZ, mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hO, mem_bot] at hc
  exact hz1 hc

theorem eq_blockP_of_barData [Finite K] (hK : ringChar K ≠ 2) (hd : 7 ≤ d) {w : Fin d → K}
    (hw : ∀ i, w i ≠ 0) {J : Finset (Fin d)} (hJ : signGL K J ∈ matrixDerived (oQ (diagGL hw)))
    (hJne : J.Nonempty) (hJcne : Jᶜ.Nonempty)
    (hNF : ∀ I : Finset (Fin d), (I = J ∨ I = Jᶜ) → 3 ≤ I.card → BlockNF w I)
    {E : Subgroup (MulAut (StatedProj (matrixDerived (oQ (diagGL hw)))))}
    {L J' J₀ : Subgroup (StatedProj (matrixDerived (oQ (diagGL hw))))} {p f : ℕ} (hp2 : p ≠ 2)
    (h : BarData E L (projH _ ⟨signGL K J, hJ⟩) J' J₀ p f) :
    ∃ I : Finset (Fin d), (I = J ∨ I = Jᶜ) ∧ 3 ≤ I.card ∧ I.card ≤ 4 ∧
      J' = Burgoyne.C.blockP K hw I ∧ IsQuasisimple (Burgoyne.C.blockP K hw I) ∧
      Burgoyne.C.blockP K hw I ≤ L := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hIc : ∀ {I : Finset (Fin d)}, (I = J ∨ I = Jᶜ) → Iᶜ.Nonempty := by
    rintro I (rfl | rfl)
    · exact hJcne
    · rwa [compl_compl]
  obtain ⟨I, hI, hJ'I⟩ : ∃ I, (I = J ∨ I = Jᶜ) ∧ J' ≤ Burgoyne.C.blockP K hw I := by
    have hsup := Burgoyne.C.le_blockP_sup_of_perfect hw hK J hJ h.hJt
      (Burgoyne.C.commutator_eq_of_isPComponent h.hJt h.hJc)
    rcases Burgoyne.C.le_or_le_of_le_sup h.hJt h.hJc
        (Burgoyne.C.blockP_le_centralizer hw J J (Or.inl rfl) hJ)
        (Burgoyne.C.blockP_le_centralizer hw J Jᶜ (Or.inr rfl) hJ)
        (Burgoyne.C.isSubnormal_blockP hw hK J J (Or.inl rfl) hJ)
        (Burgoyne.C.isSubnormal_blockP hw hK J Jᶜ (Or.inr rfl) hJ) hsup with h1 | h1
    · exact ⟨J, Or.inl rfl, h1⟩
    · exact ⟨Jᶜ, Or.inr rfl, h1⟩
  rcases Burgoyne.C.comp_cases_of_le_blockP hw hK J I hI hJ (hIc hI) h.hJt h.hJc hJ'I with
    ⟨hJe, hq⟩ | ⟨-, -, hq₂, ⟨f₂⟩⟩
  swap
  · exact (false_of_equiv_SL h2 hq₂ f₂ h.hJm).elim
  subst hJe
  have h3 := Burgoyne.C.three_le_card_of_isQuasisimple_blockP hw (hIc hI) h2 hq
  obtain ⟨I₀, hI₀, hI₀3, hI₀w, hns⟩ := hNF I hI h3
  have hin : ∀ (T : Finset (Fin d)) (hT : signGL K T ∈ oBlock K hw I),
      projH _ ⟨signGL K T, Burgoyne.C.oBlock_le_matrixDerived hw h2 I hT⟩ ∈
        Burgoyne.C.blockP K hw I := fun T hT => ⟨_, mem_subgroupOf.2 hT, rfl⟩
  have h4 : I.card ≤ 4 := by
    by_contra h5
    have hdiff : (I \ I₀).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro x hx y hy
      rw [Finset.mem_sdiff] at hx hy
      exact hns x hx.1 y hy.1 hx.2 hy.2
    have hI₀c : (I \ I₀).card = I.card - I₀.card := Finset.card_sdiff_of_subset hI₀
    have hI₀le : I₀.card ≤ I.card := Finset.card_le_card hI₀
    have hI₀4 : 4 ≤ I₀.card := by omega
    obtain ⟨T, hTI₀, hT4⟩ := Finset.exists_subset_card_eq hI₀4
    obtain ⟨i, j, k, l, hij, hik, hil, hjk, hjl, hkl, rfl⟩ := Finset.card_eq_four.1 hT4
    have hmem : ∀ x ∈ ({i, j, k, l} : Finset (Fin d)), x ∈ I₀ := fun x hx => hTI₀ hx
    have hi₀ := hmem i (by simp)
    have hj₀ := hmem j (by simp)
    have hk₀ := hmem k (by simp)
    have hl₀ := hmem l (by simp)
    have hX := signGL_pair_mem_oBlock hw (hI₀ hi₀) (hI₀ hj₀) hij (hI₀w i hi₀ j hj₀)
    have hY := signGL_pair_mem_oBlock hw (hI₀ hi₀) (hI₀ hk₀) hik (hI₀w i hi₀ k hk₀)
    have hZ := signGL_pair_mem_oBlock hw (hI₀ hi₀) (hI₀ hl₀) hil (hI₀w i hi₀ l hl₀)
    have hXH := Burgoyne.C.oBlock_le_matrixDerived hw h2 I hX
    have hYH := Burgoyne.C.oBlock_le_matrixDerived hw h2 I hY
    have hZH := Burgoyne.C.oBlock_le_matrixDerived hw h2 I hZ
    exact h.noE8 hp2 _ (hin _ hX) _ (hin _ hY) _ (hin _ hZ)
      (X10Orth.e8Triple_sign h2 hXH hYH hZH (X10Orth.e8Sets (by omega) hij hik hil hjk hjl hkl))
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 (by omega : 1 < I₀.card)
  have hs := signGL_pair_mem_oBlock hw (hI₀ ha) (hI₀ hb) hab (hI₀w a ha b hb)
  have hsΩ := Burgoyne.C.oBlock_le_matrixDerived hw h2 I hs
  have hpc : ({a, b} : Finset (Fin d))ᶜ.Nonempty :=
    X10Orth.compl_nonempty_of_card_le (by rw [Finset.card_pair hab]; omega) (by omega)
  have hy2 := Burgoyne.C.orderOf_projH_sign hw hK hsΩ ⟨a, by simp⟩ hpc
  have hO : pPrimeCore 2 (Burgoyne.C.blockP K hw I) = ⊥ :=
    Burgoyne.C.pPrimeCore_eq_bot_of_center hq (a := ⟨_, hin _ hs⟩)
      (by rw [← Subgroup.orderOf_coe]; exact hy2)
      (fun z hz => Burgoyne.C.sq_eq_one_of_mem_center_blockP hw hK (hIc hI) (hNF I hI h3) hz)
  have hJ₀ := h.hJ₀
  rw [hO, Subgroup.map_bot, sup_bot_eq] at hJ₀
  exact ⟨I, hI, h3, h4, rfl, hq, hJ₀ ▸ h.hJ₀L⟩

end CFSG.ComponentClassification.GSThmB.QPUCl
