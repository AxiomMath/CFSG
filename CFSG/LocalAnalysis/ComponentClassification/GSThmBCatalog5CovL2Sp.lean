module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog5CovFour
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog5CovSpor
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog5CovNe
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallCover

public section

namespace CFSG.ComponentClassification.GSThmB.Cov

open CFSG Subgroup CFSG.ComponentClassification.CatFactsL4U4

variable {H : Type} [Group H] [Finite H] {h : Hyp52 H} (hKa : conjugate h.K h.a = h.K)

omit [Finite H] in
theorem exists_quotient_zStarBar (K : Subgroup H) :
    ∃ η : OddBar K →* ZStarBar K, Function.Surjective η ∧ η.ker = center (OddBar K) := by
  obtain ⟨eZ⟩ := nonempty_quotient_center_equiv_zStarBar K
  refine ⟨eZ.toMonoidHom.comp (QuotientGroup.mk' _), ?_, ?_⟩
  · rw [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom]
    exact eZ.surjective.comp (QuotientGroup.mk'_surjective _)
  · ext v
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

include hKa in
theorem false_of_psl_two
    (hZK : center (OddBar h.K) ≠ ⊥)
    (hZJ : center (OddBar h.J) = ⊥) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hm : Blueprint.LieModel (ZStarBar h.K) .PSL 2 p f) : False := by
  obtain ⟨eZ⟩ := nonempty_quotient_center_equiv_zStarBar h.K
  have hZ2 : IsPGroup 2 (center (OddBar h.K)) :=
    isPGroup_two_center_of_pPrimeCore_eq_bot (pPrimeCore_quotient_pPrimeCore_eq_bot 2)
  have hcard : Nat.card (center (OddBar h.K)) = 2 :=
    card_center_eq_two hZK (card_center_le_two_of_psl_two h.isQuasisimple_K hZ2 hp hp2
      (OddQuot.lieModel_of_equiv eZ.symm hm))
  obtain ⟨η, hηs, hker⟩ := exists_quotient_zStarBar h.K
  obtain ⟨-, -, F, _, _, hF, ⟨eS⟩⟩ := CatFactsSmall.exists_sl2_equiv_of_perfect
    h.isQuasisimple_K.1 hηs hker.le (by rw [hker]; exact hcard) hp2 hm
  have h2F : (2 : F) ≠ 0 :=
    CatFactsSp4.two_ne_zero_of_odd_card (by rw [hF]; exact (hp.odd_of_ne_two hp2).pow)
  obtain ⟨x, hx⟩ := exists_involution_imJB hKa
  refine not_mem_center_of_imJB hKa hZJ hx
    (CatFactsSmall.forall_sq_eq_one_mem_center_of_sl2 h2F eS _ ?_)
  have h0 := pow_orderOf_eq_one x
  rw [hx] at h0
  rw [← Subgroup.coe_pow, h0, Subgroup.coe_one]

include hKa in
theorem false_of_psp_four (hGKF : GH74.Generic.GenericKnownFacts)
    (hZK : center (OddBar h.K) ≠ ⊥) (hZJ : center (OddBar h.J) = ⊥) {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hm : Blueprint.LieModel (ZStarBar h.K) .PSp 2 p f) : False := by
  obtain ⟨eZ⟩ := nonempty_quotient_center_equiv_zStarBar h.K
  have hZ2 : IsPGroup 2 (center (OddBar h.K)) :=
    isPGroup_two_center_of_pPrimeCore_eq_bot (pPrimeCore_quotient_pPrimeCore_eq_bot 2)
  rcases hGKF.psp4_cover p f hp hp2 (OddBar h.K) h.isQuasisimple_K hZ2
      (OddQuot.lieModel_of_equiv eZ.symm hm) with hbot | ⟨F, _, _, hF, ⟨eS⟩⟩
  · exact hZK hbot
  have h2F : (2 : F) ≠ 0 :=
    CatFactsSp4.two_ne_zero_of_odd_card (by rw [hF]; exact (hp.odd_of_ne_two hp2).pow)
  have hneg : CatFactsSp4.negS F ∈ center (Assembly.LowTwoRank.StatedSp 2 F) :=
    CatFactsSp4.mem_center_of_mem_spScalars ((CatFactsSp4.mem_spScalars_iff _).mpr (Or.inr rfl))
  have key : ∀ w : ↥(imJB h), w * w = 1 → eS (w : OddBar h.K) = CatFactsSp4.negS F →
      w = 1 := by
    intro w hw2 hwn
    apply Subtype.ext
    refine eq_one_of_central_sq h hKa hZJ w.2 (fun g _ => ?_)
      (by rw [← Subgroup.coe_mul, hw2, Subgroup.coe_one])
    apply eS.injective
    rw [map_mul, map_mul, hwn]
    exact (mem_center_iff.mp hneg (eS g)).symm
  obtain ⟨x, y, hx, hy, hxy, hne⟩ := exists_four_imJB hKa hZJ
  have hsq : ∀ w : ↥(imJB h), orderOf w = 2 → w * w = 1 := fun w hw => by
    have h0 := pow_orderOf_eq_one w
    rw [hw, sq] at h0
    exact h0
  have hne1 : ∀ w : ↥(imJB h), orderOf w = 2 → w ≠ 1 := fun w hw h1 => by
    rw [h1, orderOf_one] at hw
    exact absurd hw (by norm_num)
  have hx2 := hsq x hx
  have hy2 := hsq y hy
  have hcoe : ∀ u v : ↥(imJB h), eS (u : OddBar h.K) * eS (v : OddBar h.K) =
      eS ((u * v : ↥(imJB h)) : OddBar h.K) := fun u v => by
    rw [Subgroup.coe_mul, map_mul]
  have hinj : ∀ u : ↥(imJB h), eS (u : OddBar h.K) = 1 → u = 1 := fun u hu =>
    Subtype.ext (eS.injective (by rw [hu, Subgroup.coe_one, map_one]))
  rcases CatFactsSp4.neg_one_mem_of_four_group h2F (x := eS (x : OddBar h.K))
      (y := eS (y : OddBar h.K)) (by rw [hcoe, hx2, Subgroup.coe_one, map_one])
      (by rw [hcoe, hy2, Subgroup.coe_one, map_one]) (by rw [hcoe, hcoe, hxy])
      (fun h1 => hne1 x hx (hinj x h1)) (fun h1 => hne1 y hy (hinj y h1))
      (fun h1 => hne (Subtype.ext (eS.injective h1))) with h1 | h1 | h1
  · exact hne1 x hx (key x hx2 h1)
  · exact hne1 y hy (key y hy2 h1)
  · have hxy2 : x * y * (x * y) = 1 := by
      calc x * y * (x * y) = x * (y * x) * y := by group
        _ = x * (x * y) * y := by rw [hxy]
        _ = (x * x) * (y * y) := by group
        _ = 1 := by rw [hx2, hy2, one_mul]
    have h3 : x * y = 1 := key (x * y) hxy2 (by rw [← hcoe]; exact h1)
    apply hne
    calc x = x * (y * y) := by rw [hy2, mul_one]
      _ = (x * y) * y := by group
      _ = y := by rw [h3, one_mul]

end CFSG.ComponentClassification.GSThmB.Cov
