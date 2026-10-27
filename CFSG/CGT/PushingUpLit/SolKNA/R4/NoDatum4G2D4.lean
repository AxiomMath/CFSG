module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.Small
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5G2D4

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TA3
open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LieType.Ree
open CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab

theorem noDatum4_g2Ne3 : ∀ (F : Type) [Group F], SmallG2Ne3 F → NoDatum4 F := by
  intro F _ hF
  obtain ⟨p, f, hp, hp2, hf, h3, hm⟩ := hF
  intro G _ _ N _ ⟨eN⟩ hC hgen R S t hD
  have hce := Q5G2D4.chevalleyExceptionalModel_of_lieModel hm (by decide) (by decide)
    (by decide)
  obtain ⟨htN, s, hsR, hsN, hs4⟩ := TightDatum.exists_cyclic4_of_outTwoCyclic hD hC
    (Nobq.OutTwoCyclic.of_mulEquiv eN (outTwoCyclic_G2 hp2 hce))
  obtain ⟨hadm, K, hKf, hKfin, hK, ⟨eF⟩⟩ := hce
  have hmN : LieModel N .G2 0 p f :=
    Or.inr (Or.inl ⟨rfl, by decide, hadm, K, hKf, hKfin, hK, ⟨eN.trans eF⟩⟩)
  have ht : orderOf (⟨t, htN⟩ : N) = 2 := by rw [Subgroup.orderOf_mk]; exact hD.order
  obtain ⟨F', _, _, Sh, hcard, -⟩ := GH74.GLS.IVK.GHInv.exists_shape_G2 hp hp2 hmN _ ht
  obtain ⟨ho, h4⟩ := odd_four_le_of_card hp hp2 (Q5G2D4.five_le hp hp2 hf h3) le_rfl
    (hcard.trans (pow_one _).symm)
  exact TightDatum.not_fourGenerated_of_shape_cyclic4 hD hsR hsN hs4 htN ho ho h4 h4 Sh hgen

theorem smallLeafR_g2Ne3 {r : ℕ} : SmallLeafR r SmallG2Ne3 :=
  SmallLeafR.of_noDatum4 noDatum4_g2Ne3

theorem noDatum4_d4Ne3 : ∀ (F : Type) [Group F], SmallD4Ne3 F → NoDatum4 F := by
  intro F _ hF
  obtain ⟨p, f, hp, hp2, hf, h3, hm⟩ := hF
  intro G _ _ N _ ⟨eN⟩ hC hgen R S t hD
  have hce := Q5G2D4.chevalleyExceptionalModel_of_lieModel hm (by decide) (by decide)
    (by decide)
  obtain ⟨htN, s, hsR, hsN, hs4⟩ := TightDatum.exists_cyclic4_of_outTwoCyclic hD hC
    (Nobq.OutTwoCyclic.of_mulEquiv eN (outTwoCyclic_trialityD4 hp2 hce))
  obtain ⟨hadm, K, hKf, hKfin, hK, σ, hσ, ⟨eF⟩⟩ := hce
  have hmN : LieModel N .trialityD4 0 p f :=
    Or.inr (Or.inl ⟨rfl, by decide, hadm, K, hKf, hKfin, hK, σ, hσ, ⟨eN.trans eF⟩⟩)
  have ht : orderOf (⟨t, htN⟩ : N) = 2 := by rw [Subgroup.orderOf_mk]; exact hD.order
  obtain ⟨F₁, F₂, _, _, _, _, Sh, hc₁, hc₂, -⟩ :=
    GH74.GLS.IVK.GHInv.exists_shape_D4 hp hp2 hmN _ ht
  have h5 := Q5G2D4.five_le hp hp2 hf h3
  obtain ⟨ho₁, h4₁⟩ := odd_four_le_of_card hp hp2 h5 (by norm_num) hc₁
  obtain ⟨ho₂, h4₂⟩ := odd_four_le_of_card hp hp2 h5 le_rfl (hc₂.trans (pow_one _).symm)
  exact TightDatum.not_fourGenerated_of_shape_cyclic4 hD hsR hsN hs4 htN ho₁ ho₂ h4₁ h4₂ Sh hgen

theorem smallLeafR_d4Ne3 {r : ℕ} : SmallLeafR r SmallD4Ne3 :=
  SmallLeafR.of_noDatum4 noDatum4_d4Ne3

end CFSG.CGT.PushingUpLit.SolKNA.R4
