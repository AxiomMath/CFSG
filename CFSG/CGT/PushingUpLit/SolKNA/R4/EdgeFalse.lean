module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.Step
public import CFSG.ClassicalInvolution.Q3.TL4OddConv
public import CFSG.ClassicalInvolution.Q3.TL4OddSecE2
public import CFSG.CGT.PushingUpLit.SolKNA.R4.EdgeFalseT
public import CFSG.ClassicalInvolution.Q3.TL4E3Defs
public import CFSG.ClassicalInvolution.Q3.TL4SepAlphaB

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC.Graph

section Cit3

theorem tightEdgeFalseSR_of_leaves {r n : ℕ} (hr : 4 ≤ r) (hodd : TightOddLeafR r n)
    (hα : TL4.TightAlphaLeafR r n) (hconn : TightConnLeafR r n) (hsep : TightSepLeafR r n)
    (hE3 : TL4.TightE3LeafR' r n) : TightEdgeFalseSR r n := by
  classical
  intro hA hB Y _ _ hn R S t hd hc hE2 hQ hlarge hedge hZ
  have hL : TightLargeHypR r n Y R S t := ⟨hA, hB, hn, hd, hc, hE2, hQ, hlarge, hedge, hZ⟩
  have hO : TightOddCent t := hodd Y R S t hL
  have hΩ := hd.hypOmegaGen
  have h2 := hd.isPGroup_member hO
  have hcn := hconn Y R S t hL hO
  have hsp : TC.SepHyp (CoreAssembly.conjClass (tightCore R)) := hsep Y R S t hL hO
  have hal : TL4.TightSepAlpha R t := hα Y R S t hL hcn
  have huniq := hd.isUniqueInvolution_core
  have hK : tightCore R ∈ CoreAssembly.conjClass (tightCore R) :=
    CoreAssembly.mem_conjClass_self _
  have htr : ∀ J ∈ CoreAssembly.conjClass (tightCore R), ∃ g : Y, conjSub g (tightCore R) = J :=
    fun J hJ => hJ
  have hgen : (⨆ J ∈ CoreAssembly.conjClass (tightCore R), J) = ⊤ := by
    rw [iSup_conjClass_eq]
    exact hc.2.1
  have hF := TC.graphFam hΩ h2 hsp htr hgen hcn
  obtain ⟨J₀, hJ₀⟩ := hd.nonempty_omegaNbr_of_not_dEdgeless hedge
  obtain ⟨P, hP⟩ := exists_isMaxOrb (A := TC.nbrAdj (CoreAssembly.conjClass (tightCore R)))
    (⟨hK, hJ₀⟩ : TC.nbrAdj _ (tightCore R) J₀)
  obtain ⟨⟨J, hKJ, hJP⟩, -⟩ := id hP
  have hmax : MaxAdj (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) (tightCore R) J :=
    ⟨hKJ, by rw [hJP]; exact hP⟩
  have hJnbr := hKJ.2
  obtain ⟨g, hgJ'⟩ := hJnbr.1
  have hgJ : conjSub g (tightCore R) = J := hgJ'
  have hu : IsUniqueInvolution J (g * t * g⁻¹) := hgJ ▸ huniq.conj g
  obtain ⟨-, hu2, hut, htu, huK, -⟩ := hd.edge_involution hJnbr hu
  have hRO : oddCoreImg R = ⊥ := hd.oddCoreImg_eq_bot hO
  have hRu : R ≤ Subgroup.centralizer ({g * t * g⁻¹} : Set Y) := by
    intro x hx
    have h1 := (hd.act_eq_one_iff hut).mp huK x hx
    rw [hRO, Subgroup.mem_bot] at h1
    rw [Subgroup.mem_centralizer_singleton_iff]
    have : g * t * g⁻¹ * x * (g * t * g⁻¹)⁻¹ * x⁻¹ = 1 := h1
    calc x * (g * t * g⁻¹) = (g * t * g⁻¹ * x * (g * t * g⁻¹)⁻¹ * x⁻¹)⁻¹ * (g * t * g⁻¹ * x) := by
          group
      _ = g * t * g⁻¹ * x := by rw [this]; group
  obtain ⟨SJ, hLJ⟩ := TL4.tightLargeHypR_conj hL g
  have hOu : TightOddCent (g * t * g⁻¹) := hodd Y _ SJ _ hLJ
  have hOu' : classicalInvolutionOddCore
      ↥(Subgroup.centralizer ({g * t * g⁻¹} : Set Y)) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have : (x : Y) ∈ oddCoreImg (Subgroup.centralizer ({g * t * g⁻¹} : Set Y)) := ⟨x, hx, rfl⟩
    unfold TightOddCent at hOu
    rw [hOu, Subgroup.mem_bot] at this
    exact (Subgroup.mem_bot).mpr (Subtype.ext this)
  have hSu : (S : Subgroup R).map R.subtype ≤ Subgroup.centralizer ({g * t * g⁻¹} : Set Y) :=
    (Subgroup.map_subtype_le _).trans hRu
  obtain ⟨S₁, hd₁, ⟨e₁⟩⟩ := hd.restrict hSu
  have hq₁ : Nonempty (↥(S₁ : Subgroup (R.subgroupOf
      (Subgroup.centralizer ({g * t * g⁻¹} : Set Y)))) ≃* QuaternionGroup (2 ^ (r - 2))) :=
    ⟨e₁.trans hc.1.some⟩
  obtain ⟨ht, S', hd', -, hcls'⟩ := exists_clsR_subnormalClosure hd₁ hq₁
  set H := subnormalClosure (tightCore (R.subgroupOf
    (Subgroup.centralizer ({g * t * g⁻¹} : Set Y)))) with hH
  have hHodd : Odd (Nat.card ↥(classicalInvolutionOddCore ↥H)) :=
    CFSG.ComponentClassification.OddCore.odd_card ↥H
  have hd'' := OddQ.datum hd' hHodd
  have hlt : Nat.card (↥H ⧸ classicalInvolutionOddCore ↥H) < n := by
    have h1 : Nat.card (↥H ⧸ classicalInvolutionOddCore ↥H) ≤ Nat.card ↥H :=
      Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)
    have h2' : Nat.card ↥H ≤ Nat.card ↥(Subgroup.centralizer ({g * t * g⁻¹} : Set Y)) :=
      Subgroup.card_le_card_group H
    have hu2' : orderOf (g * t * g⁻¹) = 2 :=
      orderOf_eq_prime (by rw [pow_two]; exact hu2) hu.ne_one
    have h3 := card_centralizer_lt hu2' (not_tightInO2_conj hL.notInO2 g)
    rw [← hL.card]
    omega
  have hex := (hL.tbelow _ hlt _ _ _ hd'' hcls').resolve_right
    (not_goodThreeElement_of_four_le hr hd'' hcls'.1)
  have hE2' := hE3 Y R S t hL hcn hsp hal J hmax _ hu htu ht _ hex
  obtain ⟨Q, hQn, hQ2, htQ⟩ := inO2_of_section_inO2 hOu' ht hE2'
  have htwo : TC.TwoIn (g * t * g⁻¹) t := twoIn_of_centralizer htu hQn hQ2 htQ
  have hE2J : TC.E2At J (tightCore R) := by
    intro u' t' hu' ht'
    obtain rfl := hu.eq hu'
    obtain rfl := huniq.eq ht'
    exact htwo
  have hJK : MaxAdj (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) J (tightCore R) :=
    ⟨hF.graph.symm hmax.1, orbOf_mem_maxOrbs hF hmax.1 hmax.2⟩
  rcases TC.inO2_or_thinAt hΩ h2 hsp hK htr hgen hcn (hd.uAt_self hO) hJK hE2J huniq with
    hin | hall
  · exact hE2 hin
  · exact not_thinAt_of_four_le hr hd hc.1 hO hJnbr (hall _ _ hmax)

theorem tightMaxSecR_of_four_le {r n : ℕ} (hr : 4 ≤ r) (hα : TL4.TightAlphaLeafR r n)
    (hE3 : TL4.TightE3LeafR' r n) : TL4.TightMaxSecR r n := by
  intro Y _ _ R S t hL hc hsp J hJ u hu htu ht
  have hd := hL.datum
  have hJn := hJ.1.2
  have hαt : TL4.TightSepAlpha R t := hα Y R S t hL hc
  have hRu := TL4.le_centralizer_of_alpha hd hJn hu (hα Y R S t hL hc J hJn u hu)
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
  have hq₁ : Nonempty (↥(S₁ : Subgroup (R.subgroupOf (Subgroup.centralizer ({u} : Set Y)))) ≃*
      QuaternionGroup (2 ^ (r - 2))) := ⟨e₁.trans hL.cls.1.some⟩
  obtain ⟨ht', S', hd', -, hcls'⟩ := exists_clsR_subnormalClosure hd₁ hq₁
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
  have hex := (hL.tbelow _ hlt _ _ _ hd'' hcls').resolve_right
    (not_goodThreeElement_of_four_le hr hd'' hcls'.1)
  exact TL4.secMovedOddFree_of_inO2 (hE3 Y R S t hL hc hsp hαt J hJ u hu htu ht _ hex)

theorem tightOddLeafR_of_four_le {r n : ℕ} (hr : 4 ≤ r) (hα : TL4.TightAlphaLeafR r n)
    (hconn : TL4.TightConnLeafR' r n) (h4 : CIT3Below n → TightBelowR r n → TL4.Thm4RBelow r n)
    (hE3 : TL4.TightE3LeafR' r n) : TightOddLeafR r n :=
  TL4.tightOddLeafR_of_maxSec hα hconn
    (fun Y _ _ R S t hL hal =>
      TL4.tightSepLeafRα_of_thm4R (h4 hL.below hL.tbelow) Y R S t hL hal)
    (tightMaxSecR_of_four_le hr hα hE3)

theorem tightEdgeFalseSR_of_main {r n : ℕ} (hr : 4 ≤ r) (hα : TL4.TightAlphaLeafR r n)
    (hconn : TL4.TightConnLeafR' r n) (h4 : CIT3Below n → TightBelowR r n → TL4.Thm4RBelow r n)
    (hE3 : TL4.TightE3LeafR' r n) : TightEdgeFalseSR r n :=
  tightEdgeFalseSR_of_leaves hr (tightOddLeafR_of_four_le hr hα hconn h4 hE3) hα
    (TL4.tightConnLeafR_of_R' hconn)
    (fun Y _ _ R S t hL hO => TL4.tightSepLeafR_of_thm4R (h4 hL.below hL.tbelow) Y R S t hL hO)
    hE3

end Cit3

end CFSG.CGT.PushingUpLit.SolKNA.R4
