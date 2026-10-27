module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB516LeafOBlk
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneCOSign
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB516LeafOSpin
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X10OrthSign

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB.Orth516

open Matrix CFSG Subgroup CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.Burgoyne CFSG.ComponentClassification.Burgoyne.O
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL signMat det_signMat)
open CFSG.ComponentClassification.Burgoyne.C (blockP blockP_cases oBlock_le_matrixDerived
  le_blockP_sup_of_perfect blockP_le_centralizer isSubnormal_blockP comp_cases_of_le_blockP
  three_le_card_of_isQuasisimple_blockP det_eq_one_of_mem_commutator signGL_empty)
open CFSG.ComponentClassification.GSThmB.Pump516 (NoCentralInv)
open CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

variable {K : Type} [Field K] {d : ℕ}

theorem exists_sign_frame [Finite K] (hK : ringChar K ≠ 2) {R : GL (Fin d) K}
    (hR : (R : Matrix (Fin d) (Fin d) K)ᵀ = R) {A : matrixDerived (oQ R)}
    (hA2 : ((A : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
      ((A : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = 1) :
    ∃ (w : Fin d → K) (hw : ∀ i, w i ≠ 0) (S : GL (Fin d) K)
      (hS : ∀ v, oQ (diagGL hw) ((S : Matrix (Fin d) (Fin d) K) *ᵥ v) = ((1 : Kˣ) : K) * oQ R v)
      (J : Finset (Fin d)) (hJ : signGL K J ∈ matrixDerived (oQ (diagGL hw))),
      oTransport S 1 hS (projH _ A) = projH _ ⟨signGL K J, hJ⟩ ∧
        (3 ≤ J.card → BlockNF w J) ∧ (3 ≤ Jᶜ.card → BlockNF w Jᶜ) := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hAI : (A : GL (Fin d) K) ∈ matrixIsometries (oQ R) := matrixDerived_le_isometries _ A.2
  have hAR : ((A : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)ᵀ * R *
      ((A : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = R := by
    have := hAI
    rw [matrixIsometries_oQ h2 R hR, CatalogueBGraphForm.mem_isometryGroup] at this
    exact this
  obtain ⟨hab, c, hcA, horth, hdiag, hNFM, hNFP⟩ := exists_split_nf hK hR hAR hA2
  obtain ⟨hw, S, hS, heq⟩ := exists_transport_of_family h2 hAI hab c hcA horth hdiag
  set J := famJ hab with hJdef
  have hSA : S * (A : GL (Fin d) K) * S⁻¹ = signGL K J := by
    have := congrArg (fun g : similarityPairs _ => g.val.left) heq
    simp only [transPair_left, linPair_right, map_one, MulAut.one_apply] at this
    exact this
  have hJ : signGL K J ∈ matrixDerived (oQ (diagGL hw)) := by
    rw [← hSA]
    exact (derivedTransport S 1 hS A).2
  refine ⟨_, hw, S, hS, J, hJ, ?_, fun h3 => hNFM ?_, fun h3 => hNFP ?_⟩
  · rw [oTransport_proj]
    congr 1
    exact Subtype.ext hSA
  · rw [hJdef, card_famJ] at h3
    exact h3
  · have h1 := card_compl_add J
    have h2' := card_famJ hab
    rw [← hJdef] at h2'
    omega

theorem false_of_sl2 {G : Type*} [Group G] (h2 : (2 : K) ≠ 0) {L : Subgroup G}
    (hZ : NoCentralInv L) (e : L ≃* SL(2, K)) : False := by
  set z : L := e.symm (-1) with hz
  have hzc : ∀ y : L, z * y = y * z := fun y => e.injective (by
    rw [map_mul, map_mul, hz, MulEquiv.apply_symm_apply, neg_one_mul, mul_neg_one])
  have hzz : z * z = 1 := e.injective (by
    rw [map_mul, hz, MulEquiv.apply_symm_apply, map_one, neg_one_mul, neg_neg])
  have h1 := hZ z z.2 (fun y hy => congrArg Subtype.val (hzc ⟨y, hy⟩))
    (congrArg Subtype.val hzz)
  have h1' : z = 1 := Subtype.ext h1
  have h3 := congrArg e h1'
  rw [hz, MulEquiv.apply_symm_apply, map_one] at h3
  have h4 := congrFun (congrFun (congrArg Subtype.val h3) 0) 0
  have h5 : ((1 : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 0 0 = 1 := by simp
  rw [SpecialLinearGroup.coe_neg, Matrix.neg_apply, h5] at h4
  exact h2 (by linear_combination -h4)

variable [Finite K] {w : Fin d → K} (hw : ∀ i, w i ≠ 0)

omit [Finite K] in
theorem even_card_of_signGL_mem (hK : ringChar K ≠ 2) {T : Finset (Fin d)}
    (hT : signGL K T ∈ matrixDerived (oQ (diagGL hw))) : Even T.card := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  rw [matrixDerived_oQ h2 _ (diagGL_transpose hw)] at hT
  have h := det_eq_one_of_mem_commutator hT
  rw [coe_signGL, det_signMat] at h
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  rw [hodd.neg_one_pow] at h
  exact h2 (by linear_combination -h)

theorem false_of_block_signGL_mem (hK : ringChar K ≠ 2) {I : Finset (Fin d)} (hIn : I.Nonempty)
    (hIc : Iᶜ.Nonempty) (hI34 : I.card = 3 ∨ I.card = 4) (hNF : BlockNF w I)
    (hS : signGL K I ∈ matrixDerived (oQ (diagGL hw))) (hZ : NoCentralInv (blockP K hw I)) :
    False := by
  have hev := even_card_of_signGL_mem hw hK hS
  have h4 : I.card = 4 := by
    rcases hI34 with h | h
    · rw [h] at hev
      exact absurd hev (by decide)
    · exact h
  exact central_involution_blockP hw (Ring.two_ne_zero hK) hIn hIc
    (signGL_mem_oBlock_of_square hw h4 hNF (isSquare_prod_of_signGL_mem hw hK hS)) hZ

theorem x_sign_reduce (hK : ringChar K ≠ 2) (hd : 7 ≤ d) {J : Finset (Fin d)}
    (hJ : signGL K J ∈ matrixDerived (oQ (diagGL hw))) (hJne : J.Nonempty) (hJcne : Jᶜ.Nonempty)
    (hNF : 3 ≤ J.card → BlockNF w J) (hNFc : 3 ≤ Jᶜ.card → BlockNF w Jᶜ)
    {J₁ : Subgroup (StatedProj (matrixDerived (oQ (diagGL hw))))}
    (hJC : J₁ ≤ centralizer ({projH _ ⟨signGL K J, hJ⟩} : Set _))
    (hJc : IsPComponent 2 (J₁.subgroupOf (centralizer ({projH _ ⟨signGL K J, hJ⟩} : Set _))))
    (hJZ : NoCentralInv J₁) (hJ8 : ∀ u ∈ J₁, ∀ v ∈ J₁, ∀ x ∈ J₁, ¬ X10Orth.E8Triple u v x) :
    J₁ = blockP K hw Jᶜ ∧ IsQuasisimple (blockP K hw Jᶜ) ∧ (Jᶜ.card = 3 ∨ Jᶜ.card = 4) ∧
      signGL K Jᶜ ∉ matrixDerived (oQ (diagGL hw)) := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  set x := projH _ (⟨signGL K J, hJ⟩ : matrixDerived (oQ (diagGL hw))) with hx
  obtain ⟨I, hI, hJI⟩ : ∃ I, (I = J ∨ I = Jᶜ) ∧ J₁ ≤ blockP K hw I := by
    have hsup := le_blockP_sup_of_perfect hw hK J hJ hJC (C.commutator_eq_of_isPComponent hJC hJc)
    rcases C.le_or_le_of_le_sup hJC hJc (blockP_le_centralizer hw J J (Or.inl rfl) hJ)
      (blockP_le_centralizer hw J Jᶜ (Or.inr rfl) hJ) (isSubnormal_blockP hw hK J J (Or.inl rfl) hJ)
      (isSubnormal_blockP hw hK J Jᶜ (Or.inr rfl) hJ) hsup with h | h
    · exact ⟨J, Or.inl rfl, h⟩
    · exact ⟨Jᶜ, Or.inr rfl, h⟩
  have hIn : I.Nonempty := by
    rcases hI with rfl | rfl
    · exact hJne
    · exact hJcne
  have hIc : Iᶜ.Nonempty := by
    rcases hI with rfl | rfl
    · exact hJcne
    · rwa [compl_compl]
  have hNFI : 3 ≤ I.card → BlockNF w I := by
    rcases hI with rfl | rfl
    · exact hNF
    · exact hNFc
  rcases comp_cases_of_le_blockP hw hK J I hI hJ hIc hJC hJc hJI with
    ⟨heq, hq⟩ | ⟨-, -, -, ⟨f⟩⟩
  swap
  · exact (false_of_sl2 h2 hJZ f).elim
  have h3 := three_le_card_of_isQuasisimple_blockP hw hIc h2 hq
  have hZI : NoCentralInv (blockP K hw I) := heq ▸ hJZ
  have hI34 : I.card = 3 ∨ I.card = 4 := by
    by_contra hbig
    have hI5 : 5 ≤ I.card := by omega
    obtain ⟨I₀, hI₀, hI₀3, hI₀w, hns⟩ := hNFI h3
    have hdiff : (I \ I₀).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      rw [Finset.mem_sdiff] at ha hb
      exact hns a ha.1 b hb.1 ha.2 hb.2
    have hI₀c : (I \ I₀).card = I.card - I₀.card := Finset.card_sdiff_of_subset hI₀
    have hI₀le : I₀.card ≤ I.card := Finset.card_le_card hI₀
    obtain ⟨T, hTI₀, hT4⟩ := Finset.exists_subset_card_eq (show 4 ≤ I₀.card by omega)
    obtain ⟨i, j, k, l, hij, hik, hil, hjk, hjl, hkl, rfl⟩ := Finset.card_eq_four.1 hT4
    have hmem : ∀ a ∈ ({i, j, k, l} : Finset (Fin d)), a ∈ I₀ := fun a ha => hTI₀ ha
    have hi₀ := hmem i (by simp)
    have hj₀ := hmem j (by simp)
    have hk₀ := hmem k (by simp)
    have hl₀ := hmem l (by simp)
    have hX := signGL_pair_mem_oBlock hw (hI₀ hi₀) (hI₀ hj₀) hij (hI₀w i hi₀ j hj₀)
    have hY := signGL_pair_mem_oBlock hw (hI₀ hi₀) (hI₀ hk₀) hik (hI₀w i hi₀ k hk₀)
    have hW := signGL_pair_mem_oBlock hw (hI₀ hi₀) (hI₀ hl₀) hil (hI₀w i hi₀ l hl₀)
    have hin : ∀ (T : Finset (Fin d)) (hT : signGL K T ∈ oBlock K hw I),
        projH _ (⟨signGL K T, oBlock_le_matrixDerived hw h2 I hT⟩ :
          matrixDerived (oQ (diagGL hw))) ∈ J₁ := fun T hT => by
      rw [heq]
      exact ⟨_, mem_subgroupOf.2 hT, rfl⟩
    exact hJ8 _ (hin _ hX) _ (hin _ hY) _ (hin _ hW)
      (X10Orth.e8Triple_sign h2 _ _ _ (X10Orth.e8Sets (by omega) hij hik hil hjk hjl hkl))
  have hNFI' := hNFI h3
  rcases hI with rfl | rfl
  ·
    exact (false_of_block_signGL_mem hw hK hIn hIc hI34 hNFI' hJ hZI).elim
  · refine ⟨heq, hq, hI34, fun hS => ?_⟩
    exact false_of_block_signGL_mem hw hK hIn hIc hI34 hNFI' hS hZI

end CFSG.ComponentClassification.GSThmB.Orth516
