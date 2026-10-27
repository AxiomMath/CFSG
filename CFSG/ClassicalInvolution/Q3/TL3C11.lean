module

public import CFSG.ClassicalInvolution.Q3.TL3C10
public import CFSG.ClassicalInvolution.Q3.TL3GluePair
public import CFSG.ClassicalInvolution.Q3.TL3C9
public import CFSG.ClassicalInvolution.Q3.TL3GlueOdd

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph

section Gen

variable {Y : Type} [Group Y] {K : Subgroup Y}

theorem iSup_conjClass_eq (K : Subgroup Y) :
    (⨆ J ∈ CoreAssembly.conjClass K, J) = ⨆ g : Y, conjSub g K := by
  apply le_antisymm
  · refine iSup₂_le fun J hJ => ?_
    obtain ⟨g, rfl⟩ := hJ
    exact le_iSup (fun g : Y => conjSub g K) g
  · exact iSup_le fun g =>
      le_biSup (fun J => J) (show conjSub g K ∈ CoreAssembly.conjClass K from ⟨g, rfl⟩)

variable [Finite Y]

noncomputable abbrev secH (R : Subgroup Y) (u : Y) :
    Subgroup ↥(Subgroup.centralizer ({u} : Set Y)) :=
  subnormalClosure (tightCore (R.subgroupOf (Subgroup.centralizer ({u} : Set Y))))

abbrev SecQ (R : Subgroup Y) (u : Y) : Type :=
  ↥(secH R u) ⧸ classicalInvolutionOddCore ↥(secH R u)

noncomputable abbrev secR (R : Subgroup Y) (u : Y) : Subgroup (SecQ R u) :=
  ((R.subgroupOf (Subgroup.centralizer ({u} : Set Y))).subgroupOf (secH R u)).map
    (QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH R u)))

end Gen

section Cit3


structure TightLargeHyp (n : ℕ) (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R)
    (t : Y) : Prop where
  below : CIT3Below n
  tbelow : TightBelow n
  card : Nat.card Y = n
  datum : TightDatum R S t
  cls : TightCls Y R S t
  notInO2 : ¬ TightInO2 t
  fstar : TightFStarQuasisimple Y
  large : ¬ TwoSubgroupsFourGenerated (genFittingFStar Y)
  edge : ¬ TightEdgeless R
  center : Subgroup.center Y = ⊥

theorem TightLargeHyp.conj {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y}
    {S : Sylow 2 R} {t : Y} (h : TightLargeHyp n Y R S t) (g : Y) :
    ∃ SJ : Sylow 2 ↥(conjSub g R), TightLargeHyp n Y (conjSub g R) SJ (g * t * g⁻¹) := by
  obtain ⟨SJ, hdJ, ⟨eJ⟩⟩ := h.datum.conj g
  have hfam : CoreAssembly.conjClass (tightCore (conjSub g R)) =
      CoreAssembly.conjClass (tightCore R) := by
    rw [← conjSub_tightCore, conjClass_conjSub]
  refine ⟨SJ, ⟨h.below, h.tbelow, h.card, hdJ, h.cls.conj g eJ, not_tightInO2_conj h.notInO2 g,
    h.fstar, h.large, ?_, h.center⟩⟩
  have := h.edge
  unfold TightEdgeless at this ⊢
  rwa [hfam]

@[expose] def TightOddLeaf (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TightLargeHyp n Y R S t → TightOddCent t

@[expose] def TightConnLeaf (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TightLargeHyp n Y R S t → TightOddCent t →
      Disconnected.DConnected (CoreAssembly.conjClass (tightCore R))

@[expose] def TightSepLeaf (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TightLargeHyp n Y R S t → TightOddCent t → TC.SepHyp (CoreAssembly.conjClass (tightCore R))

@[expose] def TightThinLeaf (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TightLargeHyp n Y R S t → TightOddCent t →
      Disconnected.DConnected (CoreAssembly.conjClass (tightCore R)) →
      TC.SepHyp (CoreAssembly.conjClass (tightCore R)) →
      ¬ ∀ M N : Subgroup Y, MaxAdj (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) M N →
        TC.ThinAt (CoreAssembly.conjClass (tightCore R)) M N

@[expose] def TightE3Leaf (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TightLargeHyp n Y R S t → TightOddCent t →
      Disconnected.DConnected (CoreAssembly.conjClass (tightCore R)) →
      TC.SepHyp (CoreAssembly.conjClass (tightCore R)) →
      ∀ J : Subgroup Y, MaxAdj (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) (tightCore R) J →
      ∀ u : Y, IsUniqueInvolution J u → ∀ (htu : t ∈ Subgroup.centralizer ({u} : Set Y))
        (ht : (⟨t, htu⟩ : Subgroup.centralizer ({u} : Set Y)) ∈ secH R u)
        (Sb : Sylow 2 ↥(secR R u)),
        TightEx (SecQ R u) (secR R u) Sb
            (QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH R u)) ⟨⟨t, htu⟩, ht⟩) →
          TightInO2 (QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH R u))
            (⟨⟨t, htu⟩, ht⟩ : secH R u))

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem TightLargeHyp.good_section (hL : TightLargeHyp n Y R S t) (hodd : TightOddLeaf n)
    (hconn : TightConnLeaf n) (hsep : TightSepLeaf n) (hthin : TightThinLeaf n)
    (hE3 : TightE3Leaf n) {J : Subgroup Y}
    (hJ : MaxAdj (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) (tightCore R) J) {u : Y}
    (hu : IsUniqueInvolution J u) (htu : t ∈ Subgroup.centralizer ({u} : Set Y)) :
    GoodThreeElement (R.subgroupOf (Subgroup.centralizer ({u} : Set Y))) (⟨t, htu⟩ : _) := by
  classical
  have hd := hL.datum
  have hO : TightOddCent t := hodd Y R S t hL
  have h2R : IsPGroup 2 R := hd.isPGroup_of_oddCent hO
  have hRO : oddCoreImg R = ⊥ := hd.oddCoreImg_eq_bot hO
  have hΩ := hd.hypOmegaGen
  have h2 := hd.isPGroup_member hO
  have hcn := hconn Y R S t hL hO
  have hsp : TC.SepHyp (CoreAssembly.conjClass (tightCore R)) := @hsep Y _ _ R S t hL hO
  have huniq := hd.isUniqueInvolution_core
  have hK : tightCore R ∈ CoreAssembly.conjClass (tightCore R) :=
    CoreAssembly.mem_conjClass_self _
  have htr : ∀ J ∈ CoreAssembly.conjClass (tightCore R), ∃ g : Y, conjSub g (tightCore R) = J :=
    fun J hJ => hJ
  have hgen : (⨆ J ∈ CoreAssembly.conjClass (tightCore R), J) = ⊤ := by
    rw [iSup_conjClass_eq]
    exact hL.cls.2.1
  have hJnbr := hJ.1.2
  obtain ⟨-, hu2, hut, -, huK, -⟩ := hd.edge_involution hJnbr hu
  have hRu : R ≤ Subgroup.centralizer ({u} : Set Y) := by
    intro r hr
    have h1 := (hd.act_eq_one_iff hut).mp huK r hr
    rw [hRO, Subgroup.mem_bot] at h1
    rw [Subgroup.mem_centralizer_singleton_iff]
    have : u * r * u⁻¹ * r⁻¹ = 1 := h1
    calc r * u = (u * r * u⁻¹ * r⁻¹)⁻¹ * (u * r) := by group
      _ = u * r := by rw [this]; group
  obtain ⟨g, hgJ'⟩ := hJnbr.1
  have hgJ : conjSub g (tightCore R) = J := hgJ'
  have hgu : g * t * g⁻¹ = u := by
    have h1 := huniq.conj g
    rw [hgJ] at h1
    exact h1.eq hu
  obtain ⟨SJ, hLJ⟩ := hL.conj g
  have hOu : TightOddCent u := hgu ▸ hodd Y _ SJ _ hLJ
  have hOu' : classicalInvolutionOddCore ↥(Subgroup.centralizer ({u} : Set Y)) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have : (x : Y) ∈ oddCoreImg (Subgroup.centralizer ({u} : Set Y)) := ⟨x, hx, rfl⟩
    unfold TightOddCent at hOu
    rw [hOu, Subgroup.mem_bot] at this
    exact (Subgroup.mem_bot).mpr (Subtype.ext this)
  have hSu : (S : Subgroup R).map R.subtype ≤ Subgroup.centralizer ({u} : Set Y) :=
    (Subgroup.map_subtype_le _).trans hRu
  obtain ⟨S₁, hd₁, ⟨e₁⟩⟩ := hd.restrict hSu
  have hq8 : Nonempty (↥(S₁ : Subgroup (R.subgroupOf (Subgroup.centralizer ({u} : Set Y)))) ≃*
      QuaternionGroup 2) := ⟨e₁.trans hL.cls.1.some⟩
  obtain ⟨ht, S', hd', -, hcls'⟩ := hd₁.exists_cls_subnormalClosure hq8
  set H := subnormalClosure (tightCore (R.subgroupOf (Subgroup.centralizer ({u} : Set Y))))
    with hH
  have hHodd : Odd (Nat.card ↥(classicalInvolutionOddCore ↥H)) :=
    CFSG.ComponentClassification.OddCore.odd_card ↥H
  have hd'' := OddQ.datum hd' hHodd
  have hlt : Nat.card (↥H ⧸ classicalInvolutionOddCore ↥H) < n := by
    have h1 : Nat.card (↥H ⧸ classicalInvolutionOddCore ↥H) ≤ Nat.card ↥H :=
      Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)
    have h2' : Nat.card ↥H ≤ Nat.card ↥(Subgroup.centralizer ({u} : Set Y)) :=
      Subgroup.card_le_card_group H
    have hu2' : orderOf u = 2 := orderOf_eq_prime (by rw [pow_two]; exact hu2) hu.ne_one
    have hE2u : ¬ TightInO2 u := hgu ▸ not_tightInO2_conj hL.notInO2 g
    have h3 := card_centralizer_lt hu2' hE2u
    rw [← hL.card]
    omega
  rcases hL.tbelow _ hlt _ _ _ hd'' hcls' with hex | hgood
  ·
    have hE2' := hE3 Y R S t hL hO hcn hsp J hJ u hu htu ht _ hex
    obtain ⟨Q, hQn, hQ2, htQ⟩ := inO2_of_section_inO2 hOu' ht hE2'
    have htwo : TC.TwoIn u t := twoIn_of_centralizer htu hQn hQ2 htQ
    have hE2J : TC.E2At J (tightCore R) := by
      intro u' t' hu' ht'
      obtain rfl := hu.eq hu'
      obtain rfl := huniq.eq ht'
      exact htwo
    have hF := TC.graphFam hΩ h2 hsp htr hgen hcn
    have hJK : MaxAdj (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) J (tightCore R) :=
      ⟨hF.graph.symm hJ.1, orbOf_mem_maxOrbs hF hJ.1 hJ.2⟩
    rcases TC.inO2_or_thinAt hΩ h2 hsp hK htr hgen hcn (hd.uAt_self hO) hJK hE2J huniq with
      hin | hall
    · exact absurd hin hL.notInO2
    · exact absurd hall (hthin Y R S t hL hO hcn hsp)
  · exact hd₁.good_of_subnormalClosure hd' hgood

theorem tightEdgePairGoodS_of_leaves (hodd : ∀ n, TightOddLeaf n) (hconn : ∀ n, TightConnLeaf n)
    (hsep : ∀ n, TightSepLeaf n) (hthin : ∀ n, TightThinLeaf n) (hE3 : ∀ n, TightE3Leaf n) :
    ∀ n, TightEdgePairGoodS n := by
  intro n hA hB Y _ _ hn R S t hd hc hE2 hQ hlarge hedge hZ
  have hL : TightLargeHyp n Y R S t := ⟨hA, hB, hn, hd, hc, hE2, hQ, hlarge, hedge, hZ⟩
  have hO : TightOddCent t := hodd n Y R S t hL
  have hΩ := hd.hypOmegaGen
  have h2 := hd.isPGroup_member hO
  have hcn := hconn n Y R S t hL hO
  have hsp : TC.SepHyp (CoreAssembly.conjClass (tightCore R)) := @hsep n Y _ _ R S t hL hO
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
  obtain ⟨g, hgJ'⟩ := hKJ.2.1
  have hgJ : conjSub g (tightCore R) = J := hgJ'
  have hu : IsUniqueInvolution J (g * t * g⁻¹) := hgJ ▸ huniq.conj g
  obtain ⟨-, -, hut, htu, -⟩ := hd.edge_involution hKJ.2 hu
  refine ⟨g, hgJ ▸ hKJ.2, htu, hut, hL.good_section (hodd n) (hconn n) (hsep n) (hthin n)
    (hE3 n) hmax hu htu, ?_⟩
  obtain ⟨SJ, hLJ⟩ := hL.conj g
  have hJcore : tightCore (conjSub g R) = J := by rw [← conjSub_tightCore, hgJ]
  have hfam : CoreAssembly.conjClass (tightCore (conjSub g R)) =
      CoreAssembly.conjClass (tightCore R) := by
    rw [← conjSub_tightCore, conjClass_conjSub]
  have hmax' : MaxAdj (TC.nbrAdj (CoreAssembly.conjClass (tightCore (conjSub g R))))
      (tightCore (conjSub g R)) (tightCore R) := by
    rw [hfam, hJcore]
    exact ⟨hF.graph.symm hmax.1, orbOf_mem_maxOrbs hF hmax.1 hmax.2⟩
  exact hLJ.good_section (hodd n) (hconn n) (hsep n) (hthin n) (hE3 n) hmax' huniq hut

theorem tightLargeLiftS_of_leaves (hodd : ∀ n, TightOddLeaf n) (hconn : ∀ n, TightConnLeaf n)
    (hsep : ∀ n, TightSepLeaf n) (hthin : ∀ n, TightThinLeaf n) (hE3 : ∀ n, TightE3Leaf n) :
    ∀ n, TightLargeLiftS n :=
  tightLargeLiftS_of_edgePairS (tightEdgePairGoodS_of_leaves hodd hconn hsep hthin hE3)

end Cit3

end CFSG.ClassicalInvolution.Q3
