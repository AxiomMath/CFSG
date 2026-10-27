module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3LConfig
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3LDX
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3LDAut
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3BDefs

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.Burgoyne.O CFSG.ComponentClassification.Burgoyne.Proj
open scoped MatrixGroups

namespace P58b3L

theorem isCyclic_center_of_multiplier (hGA : TBLit.GriessMultipliersAllModels) {X : Type}
    [Group X] [Finite X] (hX : IsQuasisimple X) {τ : StatedLieTag} {n p f : ℕ}
    (hm : CFSG.Models.LieModel (X ⧸ center X) τ n p f)
    (hg2 : (Blueprint.Multiplier.genericOrders τ n p f).2 = 1)
    (he : Blueprint.Multiplier.exceptionalOrders τ n p f = (1, 1)) : IsCyclic (center X) := by
  have : Group.IsPerfect X := hX.1
  obtain ⟨-, ⟨eM⟩⟩ := hGA _ τ n p f hm
  have hker : (QuotientGroup.mk' (center X)).ker ≤ center X := (QuotientGroup.ker_mk' _).le
  have h1 : Subsingleton (Multiplicative (ZMod (Blueprint.Multiplier.genericOrders τ n p f).2)) :=
    by rw [hg2]; infer_instance
  have h2 : Subsingleton (Multiplicative
      (ZMod (Blueprint.Multiplier.exceptionalOrders τ n p f).1)) := by rw [he]; infer_instance
  have h3 : Subsingleton (Multiplicative
      (ZMod (Blueprint.Multiplier.exceptionalOrders τ n p f).2)) := by rw [he]; infer_instance
  set ι : Multiplicative (ZMod (Blueprint.Multiplier.genericOrders τ n p f).1) →*
      Blueprint.Multiplier.generic τ n p f × Blueprint.Multiplier.exceptional τ n p f :=
    (MonoidHom.inl _ _).comp (MonoidHom.inl _ _) with hι
  have hιs : Function.Surjective ι := by
    rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩
    refine ⟨a, ?_⟩
    rw [hι, MonoidHom.comp_apply, MonoidHom.inl_apply, MonoidHom.inl_apply,
      Subsingleton.elim b 1, Subsingleton.elim c 1, Subsingleton.elim d 1]
    rfl
  set φ := (RankThree.PerfectCover.hopfMultiplierToKer (QuotientGroup.mk' (center X))
    (QuotientGroup.mk'_surjective _) hker).comp
      ((RankThree.PerfectCover.hopfMultiplierEquivGriess (X ⧸ center X)).toMonoidHom.comp
        (eM.symm.toMonoidHom.comp ι)) with hφ
  have hφs : Function.Surjective φ := by
    intro z
    obtain ⟨m, hm⟩ := RankThree.PerfectCover.hopfMultiplierToKer_surjective _ _ hker z
    obtain ⟨a, ha⟩ := hιs (eM ((RankThree.PerfectCover.hopfMultiplierEquivGriess
      (X ⧸ center X)).symm m))
    refine ⟨a, ?_⟩
    rw [hφ, MonoidHom.comp_apply, MonoidHom.comp_apply, MonoidHom.comp_apply, ha]
    simp only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply, MulEquiv.apply_symm_apply]
    exact hm
  have hcyc : IsCyclic (QuotientGroup.mk' (center X)).ker := isCyclic_of_surjective φ hφs
  exact isCyclic_of_surjective (MulEquiv.subgroupCongr (QuotientGroup.ker_mk' (center X)))
    (MulEquiv.surjective _)

theorem exceptionalOrders_POmega_three {τ : StatedLieTag} (hτ : τ = .POmegaPlus ∨
    τ = .POmegaMinus) (n : ℕ) : Blueprint.Multiplier.exceptionalOrders τ n 3 1 = (1, 1) := by
  rcases hτ with rfl | rfl <;>
    (unfold Blueprint.Multiplier.exceptionalOrders; split <;> simp_all)

end P58b3L

open P58b3L in
theorem harris82Lemma58bThreeRowAt_POmegaMinus_one (hGA : TBLit.GriessMultipliersAllModels)
    {n : ℕ} (hn : 5 ≤ n) : P58b3.Harris82Lemma58bThreeRowAt .POmegaMinus n 1 := by
  intro G _ _ z₁ z₂ hz₁ hz₂ _ _ L₁ L₂ K hL₁ _ hz₁L _ _ hKc hO₁ _ hN hz₂K hz₂Z hm
  exfalso
  have hz₁K : z₁ ∈ K := hO₁ (F3.mem_oPrimeResidualOf hz₁L hz₁)
  obtain ⟨hX, hO, hmX, -⟩ := P58b3.setting_facts hz₁ hz₂ hz₁L hKc hO₁ hz₂K hz₂Z hm
  have hc2 := P58b.orderOf_mk_eq_two (K := ↥K) (z := ⟨z₁, hz₁K⟩)
    (by rw [Subgroup.orderOf_mk]; exact hz₁)
  have ht2 := P58b.orderOf_mk_eq_two (K := ↥K) (z := ⟨z₂, hz₂K⟩)
    (by rw [Subgroup.orderOf_mk]; exact hz₂)
  have hcZ := mk_mem_center hKc.1 hz₁K
  have hcQ₁ : QuotientGroup.mk' (pPrimeCore 2 ↥K) ⟨z₁, hz₁K⟩ ∈
      ((L₁ ⊓ K).subgroupOf K).map (QuotientGroup.mk' (pPrimeCore 2 ↥K)) :=
    ⟨⟨z₁, hz₁K⟩, mem_subgroupOf.mpr ⟨hz₁L, hz₁K⟩, rfl⟩
  have ha := oddAutInner_of_POmegaMinus_three hX (by omega) hmX
  rcases hmX with ⟨-, hcm⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩
  rotate_left
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)
  have hb := P58b3.cyclicCenterTwo_of_isCyclic (isCyclic_center_of_multiplier hGA hX
    ⟨hcm.1, Or.inl hcm⟩ rfl (exceptionalOrders_POmega_three (Or.inr rfl) n))
  have hQ₁ := P58b3.lemma57_fourGroup_map hz₂ hL₁ hKc.1 hO₁ hN hz₂K ha hb
  have hcm' := hcm
  obtain ⟨-, K₀, _, _, hK₀c, b, c', hirr, ⟨e⟩⟩ := hcm'
  have hK3 : Nat.card K₀ = 3 := by rw [hK₀c, pow_one]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fintype K₀ := Fintype.ofFinite K₀
  have : CharP K₀ 3 := charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card, hK3])
  have hK : ringChar K₀ ≠ 2 := by rw [ringChar.eq K₀ 3]; norm_num
  have h2 : (2 : K₀) ≠ 0 := Ring.two_ne_zero hK
  have hn1 : 1 ≤ n := by omega
  obtain ⟨R, hR, hRQ⟩ := exists_gram h2 (coordinateQuadMinus n K₀ hn1 b c')
    (regular_coordinateQuadMinus n K₀ b c' (by omega) hirr).1
  have hS₁ : ∀ v, oQ R (((1 : GL (Fin (2 * n)) K₀) : Matrix _ _ K₀) *ᵥ v) =
      ((1 : K₀ˣ) : K₀) * coordinateQuadMinus n K₀ hn1 b c' v := by
    intro v
    rw [Units.val_one, one_mulVec, Units.val_one, one_mul, hRQ]
  have hker : OKer (oQ R) :=
    OKer.transport 1 1 hS₁ (oKer_coordinateMinus hcm K₀ hK₀c b c' hirr e)
  exact false_of_typeD_three hO hK3 hn hR hker
    ((coordinateMinusWitnessEquiv K₀ hn1 b c' e).trans (oTransport 1 1 hS₁)) hcZ hc2 ht2 hz₂Z
    hQ₁ hcQ₁

open P58b3L in
theorem harris82Lemma58bThreeRowAt_POmegaPlus_one (hGA : TBLit.GriessMultipliersAllModels)
    {n : ℕ} (hn : 5 ≤ n) (hodd : Odd n) : P58b3.Harris82Lemma58bThreeRowAt .POmegaPlus n 1 := by
  intro G _ _ z₁ z₂ hz₁ hz₂ _ _ L₁ L₂ K hL₁ _ hz₁L _ _ hKc hO₁ _ hN hz₂K hz₂Z hm
  exfalso
  have hz₁K : z₁ ∈ K := hO₁ (F3.mem_oPrimeResidualOf hz₁L hz₁)
  obtain ⟨hX, hO, hmX, -⟩ := P58b3.setting_facts hz₁ hz₂ hz₁L hKc hO₁ hz₂K hz₂Z hm
  have hc2 := P58b.orderOf_mk_eq_two (K := ↥K) (z := ⟨z₁, hz₁K⟩)
    (by rw [Subgroup.orderOf_mk]; exact hz₁)
  have ht2 := P58b.orderOf_mk_eq_two (K := ↥K) (z := ⟨z₂, hz₂K⟩)
    (by rw [Subgroup.orderOf_mk]; exact hz₂)
  have hcZ := mk_mem_center hKc.1 hz₁K
  have hcQ₁ : QuotientGroup.mk' (pPrimeCore 2 ↥K) ⟨z₁, hz₁K⟩ ∈
      ((L₁ ⊓ K).subgroupOf K).map (QuotientGroup.mk' (pPrimeCore 2 ↥K)) :=
    ⟨⟨z₁, hz₁K⟩, mem_subgroupOf.mpr ⟨hz₁L, hz₁K⟩, rfl⟩
  have ha := oddAutInner_of_POmegaPlus_three hX hn hmX
  rcases hmX with ⟨-, hcm⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩
  rotate_left
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)
  have hg2 : (Blueprint.Multiplier.genericOrders .POmegaPlus n 3 1).2 = 1 := by
    have h3 : ¬ Even 3 := by decide
    have hn' : ¬ Even n := Nat.not_even_iff_odd.mpr hodd
    simp [Blueprint.Multiplier.genericOrders, h3, hn']
  have hb := P58b3.cyclicCenterTwo_of_isCyclic (isCyclic_center_of_multiplier hGA hX
    ⟨hcm.1, Or.inl hcm⟩ hg2 (exceptionalOrders_POmega_three (Or.inl rfl) n))
  have hQ₁ := P58b3.lemma57_fourGroup_map hz₂ hL₁ hKc.1 hO₁ hN hz₂K ha hb
  have hcm' := hcm
  obtain ⟨-, K₀, _, _, hK₀c, ⟨e⟩⟩ := hcm'
  have hK3 : Nat.card K₀ = 3 := by rw [hK₀c, pow_one]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fintype K₀ := Fintype.ofFinite K₀
  have : CharP K₀ 3 := charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card, hK3])
  have hK : ringChar K₀ ≠ 2 := by rw [ringChar.eq K₀ 3]; norm_num
  have h2 : (2 : K₀) ≠ 0 := Ring.two_ne_zero hK
  obtain ⟨R, hR, hRQ⟩ := exists_gram h2 (coordinateQuadPlus n K₀)
    (regular_coordinateQuadPlus n K₀ (by omega)).1
  have hS₁ : ∀ v, oQ R (((1 : GL (Fin (2 * n)) K₀) : Matrix _ _ K₀) *ᵥ v) =
      ((1 : K₀ˣ) : K₀) * coordinateQuadPlus n K₀ v := by
    intro v
    rw [Units.val_one, one_mulVec, Units.val_one, one_mul, hRQ]
  have hker : OKer (oQ R) := OKer.transport 1 1 hS₁ (oKer_coordinatePlus hcm K₀ hK₀c e)
  exact false_of_typeD_three hO hK3 hn hR hker
    ((coordinatePlusWitnessEquiv K₀ e).trans (oTransport 1 1 hS₁)) hcZ hc2 ht2 hz₂Z hQ₁ hcQ₁

end CFSG.ComponentClassification.HarrisLit.T1
