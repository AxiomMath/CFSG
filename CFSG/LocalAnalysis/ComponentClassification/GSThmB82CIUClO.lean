module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CIUClOE
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUClOModel
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUClOComm
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUClOPc
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB516LeafOX
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneCOReduce
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUClOJ
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUClOMin
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUClOSign

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB.QPUJ6Cl

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.Burgoyne.O CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL)
open scoped Pointwise

theorem BarData6.noCentralInv {P : Type} [Group P] [Finite P] {E : Subgroup (MulAut P)}
    {L : Subgroup P} {t : P} {J J₀ : Subgroup P} {p f : ℕ} (h : BarData6 E L t J J₀ p f) :
    Pump516.NoCentralInv J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro z hz hzc hzz
  have hJperf := QPUCl.isPerfect_of_isPComponent h.hJt h.hJc
  have hZJ : center (↥J ⧸ pPrimeCore 2 ↥J) = ⊥ :=
    QPUCl.center_eq_bot_of_lieModel (Or.inl rfl) h.hJm
  have hc : QuotientGroup.mk' (pPrimeCore 2 ↥J) (⟨z, hz⟩ : ↥J) ∈
      center (↥J ⧸ pPrimeCore 2 ↥J) :=
    mem_center_iff.mpr fun w => by
      obtain ⟨w', rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥J) w
      rw [← map_mul, ← map_mul]
      exact congrArg _ (Subtype.ext (hzc w' w'.2).symm)
  rw [hZJ, mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hc
  have hd2 : orderOf (⟨z, hz⟩ : ↥J) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (by rw [sq]; exact Subtype.ext hzz)
  have hdO : orderOf (⟨z, hz⟩ : ↥J) ∣ Nat.card (pPrimeCore 2 ↥J) := by
    have := orderOf_dvd_natCard (⟨⟨z, hz⟩, hc⟩ : pPrimeCore 2 ↥J)
    rwa [Subgroup.orderOf_mk] at this
  have hcop := pPrimeCore_coprime_card (p := 2) (G := ↥J)
  have h1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hd2 hdO)
  exact congrArg Subtype.val h1

theorem false_of_barData6_model {K : Type} [Field K] [Finite K] {p f₀ f d : ℕ}
    {R : GL (Fin d) K} (hK : ringChar K ≠ 2) (hp : p.Prime) (hKc : Nat.card K = p ^ f₀)
    (hd : 7 ≤ d) (hR : (R : Matrix (Fin d) (Fin d) K)ᵀ = R) (hker : OKer (oQ R))
    [IsSimpleGroup (StatedProj (matrixDerived (oQ R)))]
    {E : Subgroup (MulAut (StatedProj (matrixDerived (oQ R))))}
    {L : Subgroup (StatedProj (matrixDerived (oQ R)))} {t : StatedProj (matrixDerived (oQ R))}
    {J J₀ : Subgroup (StatedProj (matrixDerived (oQ R)))}
    (h : BarData6 E L t J J₀ p f) (hκ : ∀ e ∈ E, ∃ g : similarityPairs (oQ R), e = oκ _ g) :
    False := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hp2 : p ≠ 2 := by
    have : Fintype K := Fintype.ofFinite K
    have : Fact p.Prime := ⟨hp⟩
    have : CharP K p := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
    rw [← ringChar.eq K p]
    exact hK
  have hE1 := h.exists_ne_one
  obtain ⟨T, hT, rfl, hT2 | hT2⟩ := QPUCl.exists_lift_sq h2 (by omega) hR h.ht2
  swap
  · exact QPUCl.false_of_pc_noE8 hK hp hKc hd hR hT hT2 h.hJt h.hJc (h.noE8 hp2)
  obtain ⟨w, hw, Js, hJs, θ, hker', hJne, hJcne, hNF, hθt, hκθ⟩ :=
    QPUCl.exists_sign_model hK hR hker hT hT2 h.ht1
  have hd' := h.map θ
  rw [hθt] at hd'
  have hκ' : ∀ e' ∈ E.map (MulAut.congr θ).toMonoidHom,
      ∃ g' : similarityPairs (oQ (diagGL hw)), e' = oκ _ g' := by
    rintro _ ⟨e, he, rfl⟩
    obtain ⟨g, rfl⟩ := hκ e he
    obtain ⟨g', hg'⟩ := hκθ g
    exact ⟨g', hg'⟩
  have hE1' : ∃ e' ∈ E.map (MulAut.congr θ).toMonoidHom, e' ≠ 1 := by
    obtain ⟨e, he, he1⟩ := hE1
    exact ⟨_, ⟨e, he, rfl⟩, fun h1 =>
      he1 ((MulAut.congr θ).injective (h1.trans (map_one _).symm))⟩
  obtain ⟨hJe, hq, hI34, hSI⟩ := Orth516.x_sign_reduce hw hK hd hJs hJne hJcne
    (hNF Js (Or.inl rfl)) (hNF Jsᶜ (Or.inr rfl)) hd'.hJt hd'.hJc hd'.noCentralInv (hd'.noE8 hp2)
  rw [hJe] at hd'
  have hIc : Jsᶜᶜ.Nonempty := by rwa [compl_compl]
  have h3 : 3 ≤ Jsᶜ.card := by omega
  have hNFI := hNF Jsᶜ (Or.inr rfl) h3
  have hIL : Burgoyne.C.blockP K hw Jsᶜ ≤ L.map θ.toMonoidHom := by
    obtain ⟨I₀, hI₀, hI₀3, hI₀w, -⟩ := id hNFI
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 (by omega : 1 < I₀.card)
    have hs := signGL_pair_mem_oBlock hw (hI₀ ha) (hI₀ hb) hab (hI₀w a ha b hb)
    have hsΩ := Burgoyne.C.oBlock_le_matrixDerived hw h2 Jsᶜ hs
    have hpc : ({a, b} : Finset (Fin d))ᶜ.Nonempty :=
      X10Orth.compl_nonempty_of_card_le (by rw [Finset.card_pair hab]; omega) (by omega)
    have hy2 := Burgoyne.C.orderOf_projH_sign hw hK hsΩ ⟨a, by simp⟩ hpc
    have hO : pPrimeCore 2 (Burgoyne.C.blockP K hw Jsᶜ) = ⊥ :=
      Burgoyne.C.pPrimeCore_eq_bot_of_center hq (a := ⟨_, ⟨_, mem_subgroupOf.2 hs, rfl⟩⟩)
        (by rw [← Subgroup.orderOf_coe]; exact hy2)
        (fun z hz => Burgoyne.C.sq_eq_one_of_mem_center_blockP hw hK hIc hNFI hz)
    have hJ₀ := hd'.hJ₀
    rw [hO, Subgroup.map_bot, sup_bot_eq] at hJ₀
    exact hJ₀ ▸ hd'.hJ₀L
  exact hSI (signGL_mem_of_scalar6 hw hK hJs (Or.inr rfl) h3 hIc hNFI hq hd' hIL hκ' hE1'
    fun g hfix ht => QPUCl.kappa_scalar_on_block hK hw hker' hJs (Or.inr rfl) hIc hNFI hq hfix ht)

theorem false_of_barConfig6_pomegaOdd {P : Type} [Group P] [Finite P] {n p f f₀ : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hP : StatedClassicalModel P .POmegaOdd n p f₀)
    (h : BarConfig6 P p f) : False := by
  have hsimp := (ClassicalGroups.Orthogonal.isSimpleGroup_of_statedClassicalModel_POmegaOdd
    P n p f₀ hP).2
  have hmod := hP
  obtain ⟨⟨-, -, hn, -⟩, F, _, _, hFc, ⟨e⟩⟩ := hP
  have : Fintype F := Fintype.ofFinite F
  have : Fact p.Prime := ⟨hp⟩
  have : CharP F p := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  have hF : ringChar F ≠ 2 := by rw [ringChar.eq F p]; exact hp2
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  obtain ⟨R, hR, hRQ⟩ := exists_gram h2 (coordinateQuadOdd n F)
    (regular_coordinateQuadOdd n F h2 hn).1
  have hS₁ : ∀ v, oQ R (((1 : GL (Fin (2 * n + 1)) F) : Matrix _ _ F) *ᵥ v) =
      ((1 : Fˣ) : F) * coordinateQuadOdd n F v := by
    intro v
    rw [Units.val_one, one_mulVec, Units.val_one, one_mul, hRQ]
  have hker := (oKer_coordinateOdd hmod F hFc e).transport 1 1 hS₁
  have hsurj := (oSurj_coordinateOdd hmod F hFc e).transport 1 1 hS₁
  set θ := (coordinateOddWitnessEquiv F e).trans (oTransport 1 1 hS₁) with hθ
  have := θ.symm.isSimpleGroup
  obtain ⟨E, L, t, J, J₀, hd⟩ := h
  exact false_of_barData6_model hF hp hFc (by omega) hR hker (hd.map θ) fun e' _ => hsurj e'

theorem false_of_barConfig6_pomegaMinus {P : Type} [Group P] [Finite P] {n p f f₀ : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hP : StatedClassicalModel P .POmegaMinus n p f₀)
    (h : BarConfig6 P p f) : False := by
  have hsimp := (ClassicalGroups.Orthogonal.isSimpleGroup_of_statedClassicalModel_POmegaMinus
    P n p f₀ hP).2
  have hmod := hP
  obtain ⟨⟨-, -, hn⟩, F, _, _, hFc, b, c, hirr, ⟨e⟩⟩ := hP
  have : Fintype F := Fintype.ofFinite F
  have : Fact p.Prime := ⟨hp⟩
  have : CharP F p := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  have hF : ringChar F ≠ 2 := by rw [ringChar.eq F p]; exact hp2
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have hn1 : 1 ≤ n := by omega
  obtain ⟨R, hR, hRQ⟩ := exists_gram h2 (coordinateQuadMinus n F hn1 b c)
    (regular_coordinateQuadMinus n F b c hn hirr).1
  have hS₁ : ∀ v, oQ R (((1 : GL (Fin (2 * n)) F) : Matrix _ _ F) *ᵥ v) =
      ((1 : Fˣ) : F) * coordinateQuadMinus n F hn1 b c v := by
    intro v
    rw [Units.val_one, one_mulVec, Units.val_one, one_mul, hRQ]
  have hker := (oKer_coordinateMinus hmod F hFc b c hirr e).transport 1 1 hS₁
  have hsurj := (oSurj_coordinateMinus hmod F hFc b c hirr e).transport 1 1 hS₁
  set θ := (coordinateMinusWitnessEquiv F hn1 b c e).trans (oTransport 1 1 hS₁) with hθ
  have := θ.symm.isSimpleGroup
  obtain ⟨E, L, t, J, J₀, hd⟩ := h
  exact false_of_barData6_model hF hp hFc (by omega) hR hker (hd.map θ) fun e' _ => hsurj e'

theorem false_of_barConfig6_pomegaPlus {P : Type} [Group P] [Finite P] {n p f f₀ : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hP : StatedClassicalModel P .POmegaPlus n p f₀)
    (h : BarConfig6 P p f) : False := by
  have hsimp := (ClassicalGroups.Orthogonal.isSimpleGroup_of_statedClassicalModel_POmegaPlus
    P n p f₀ hP).2
  have hmod := hP
  obtain ⟨⟨-, -, hn⟩, F, _, _, hFc, ⟨e⟩⟩ := hP
  have : Fintype F := Fintype.ofFinite F
  have : Fact p.Prime := ⟨hp⟩
  have : CharP F p := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  have hF : ringChar F ≠ 2 := by rw [ringChar.eq F p]; exact hp2
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  obtain ⟨R, hR, hRQ⟩ := exists_gram h2 (coordinateQuadPlus n F)
    (regular_coordinateQuadPlus n F (by omega)).1
  have hS₁ : ∀ v, oQ R (((1 : GL (Fin (2 * n)) F) : Matrix _ _ F) *ᵥ v) =
      ((1 : Fˣ) : F) * coordinateQuadPlus n F v := by
    intro v
    rw [Units.val_one, one_mulVec, Units.val_one, one_mul, hRQ]
  have hker := (oKer_coordinatePlus hmod F hFc e).transport 1 1 hS₁
  set Θ := oTransport 1 1 hS₁ with hΘ
  set θ := (coordinatePlusWitnessEquiv F e).trans Θ with hθ
  obtain ⟨E, L, t, J, J₀, hd⟩ := h
  have hd' := hd.map θ
  obtain ⟨β, hβ⟩ : ∃ β : MulAut (StatedProj (matrixDerived (oQ R))),
      ∀ e' ∈ E.map (MulAut.congr θ).toMonoidHom, ∃ g : similarityPairs (oQ R),
        β⁻¹ * e' * β = oκ _ g := by
    rcases Nat.lt_or_ge n 5 with h4 | h5'
    · obtain rfl : n = 4 := by omega
      obtain ⟨β₀, hβ₀⟩ := QPUCl.exists_conj_mem_familyAut_plus_four (K := F)
        (E := (E.map (MulAut.congr θ).toMonoidHom).map (MulAut.congr Θ.symm).toMonoidHom)
        (hd'.hE.map _)
      obtain ⟨β₁, hβ₁⟩ : ∃ β₁ : MulAut (StatedProj (matrixDerived (coordinateQuadPlus 4 F))),
          β₁ = β₀ := ⟨β₀, rfl⟩
      refine ⟨MulAut.congr Θ β₁, fun e' he' => ?_⟩
      have hmem := hβ₀ _ ⟨e', he', rfl⟩
      rw [coordinate_plus_family_eq_matrixImage hmod F hFc e] at hmem
      obtain ⟨g, hg⟩ := hmem
      have hg₁ : oκ _ g = β₁⁻¹ * MulAut.congr Θ.symm e' * β₁ := by rw [hβ₁]; exact hg
      refine ⟨transPair 1 1 hS₁ g, ?_⟩
      rw [← oTransport_kappa, ← hΘ, hg₁, map_mul, map_mul, map_inv]
      congr 1
      ext x
      simp
    · have hsurj := (oSurj_coordinatePlus hmod F hFc h5' e).transport 1 1 hS₁
      refine ⟨1, fun e' _ => ?_⟩
      obtain ⟨g, hg⟩ := hsurj e'
      exact ⟨g, by rw [inv_one, one_mul, mul_one]; exact hg⟩
  set θ' := θ.trans β.symm with hθ'
  have := θ'.symm.isSimpleGroup
  refine false_of_barData6_model hF hp hFc (by omega) hR hker (hd.map θ') ?_
  rintro _ ⟨e', he', rfl⟩
  obtain ⟨g, hg⟩ := hβ _ ⟨e', he', rfl⟩
  refine ⟨g, ?_⟩
  change MulAut.congr θ' e' = _
  rw [hθ', QPUCl.congr_trans_apply, ← hg]
  ext x
  rfl

end CFSG.ComponentClassification.GSThmB.QPUJ6Cl
