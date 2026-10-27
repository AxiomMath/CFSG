module

public import CFSG.ClassicalInvolution.Q3.TL4OddSecE2
public import CFSG.ClassicalInvolution.Q3.TL4OddSecGood
public import CFSG.ClassicalInvolution.Q3.TL4E3Defs

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph


theorem tightMaxSecR_of_parts {n : ℕ} (hα : TightAlphaLeafR 3 n) (hE3 : TightE3LeafR' 3 n) :
    TightMaxSecR 3 n := by
  intro Y _ _ R S t hL hc hsp J hJ u hu htu ht
  have hd := hL.datum
  have hJn := hJ.1.2
  have hαt : TightSepAlpha R t := hα Y R S t hL hc
  have hαJ := hα Y R S t hL hc J hJn u hu
  have hRu := le_centralizer_of_alpha hd hJn hu hαJ
  obtain ⟨-, hu2, -, -⟩ := hd.edge_involution hJn hu
  obtain ⟨g, hgJ'⟩ := hJn.1
  have hgJ : conjSub g (tightCore R) = J := hgJ'
  have hgu : g * t * g⁻¹ = u := by
    have h1 := hd.isUniqueInvolution_core.conj g
    rw [hgJ] at h1
    exact h1.eq hu
  have hSu : (S : Subgroup R).map R.subtype ≤ Subgroup.centralizer ({u} : Set Y) :=
    (Subgroup.map_subtype_le _).trans hRu
  obtain ⟨S₁, hd₁, ⟨e₁⟩⟩ := hd.restrict hSu
  have hq8 : Nonempty (↥(S₁ : Subgroup (R.subgroupOf (Subgroup.centralizer ({u} : Set Y)))) ≃*
      QuaternionGroup 2) := ⟨e₁.trans (tightClsR_three_iff.mp hL.cls).1.some⟩
  obtain ⟨ht', S', hd', -, hcls'⟩ := hd₁.exists_cls_subnormalClosure hq8
  set H := subnormalClosure (tightCore (R.subgroupOf (Subgroup.centralizer ({u} : Set Y))))
    with hH
  have hHodd : Odd (Nat.card ↥(classicalInvolutionOddCore ↥H)) :=
    CFSG.ComponentClassification.OddCore.odd_card ↥H
  have hd'' := OddQ.datum hd' hHodd
  have hlt : Nat.card (↥H ⧸ classicalInvolutionOddCore ↥H) < n := by
    have h1 : Nat.card (↥H ⧸ classicalInvolutionOddCore ↥H) ≤ Nat.card ↥H :=
      Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)
    have h2 : Nat.card ↥H ≤ Nat.card ↥(Subgroup.centralizer ({u} : Set Y)) :=
      Subgroup.card_le_card_group H
    have hu2' : orderOf u = 2 := orderOf_eq_prime (by rw [pow_two]; exact hu2) hu.ne_one
    have hE2u : ¬ TightInO2 u := hgu ▸ not_tightInO2_conj hL.notInO2 g
    have h3 := card_centralizer_lt hu2' hE2u
    rw [← hL.card]
    omega
  rcases hL.tbelow _ hlt _ _ _ hd'' (tightClsR_three_iff.mpr hcls') with hex | hgood
  · exact secMovedOddFree_of_inO2 (hE3 Y R S t hL hc hsp hαt J hJ u hu htu ht _ hex)
  · exact secMovedOddFree_of_good hL hu.ne_one htu hRu ht hgood

end CFSG.ClassicalInvolution.Q3.TL4
