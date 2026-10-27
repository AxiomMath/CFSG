module

public import CFSG.ClassicalInvolution.Q3.TL3GlueMain

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

section Cit3


@[expose] def TightEdgePairGood (n : ℕ) : Prop :=
  CIT3Below n → TightBelow n → ∀ (Y : Type) [Group Y] [Finite Y], Nat.card Y = n →
    ∀ (R : Subgroup Y) (S : Sylow 2 R) (t : Y), TightDatum R S t → TightCls Y R S t →
      ¬ TightInO2 t → TightFStarQuasisimple Y →
        ¬ TwoSubgroupsFourGenerated (genFittingFStar Y) → ¬ TightEdgeless R →
          ∃ g : Y, conjSub g (tightCore R) ∈
              omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R) ∧
            ∃ (htu : t ∈ Subgroup.centralizer ({g * t * g⁻¹} : Set Y))
              (hut : g * t * g⁻¹ ∈ Subgroup.centralizer ({t} : Set Y)),
              GoodThreeElement (R.subgroupOf (Subgroup.centralizer ({g * t * g⁻¹} : Set Y)))
                (⟨t, htu⟩ : _) ∧
              GoodThreeElement ((conjSub g R).subgroupOf (Subgroup.centralizer ({t} : Set Y)))
                (⟨g * t * g⁻¹, hut⟩ : _)

theorem edgePair_of_edgeSection (h : ∀ n, TightEdgeSectionGood n) : ∀ n, TightEdgePairGood n := by
  intro n hA hB Y _ _ hn R S t hd hc hE2 hQ hlarge hedge
  have hΩ := hd.hypOmegaGen
  have huniq := hd.isUniqueInvolution_core
  have hK : tightCore R ∈ CoreAssembly.conjClass (tightCore R) :=
    CoreAssembly.mem_conjClass_self _
  obtain ⟨J, hJ⟩ := hd.nonempty_omegaNbr_of_not_dEdgeless hedge
  obtain ⟨g, hgJ'⟩ := hJ.1
  have hgJ : conjSub g (tightCore R) = J := hgJ'
  have hu : IsUniqueInvolution J (g * t * g⁻¹) := hgJ ▸ huniq.conj g
  obtain ⟨-, -, hut, htu, -⟩ := hd.edge_involution hJ hu
  have hJcore : tightCore (conjSub g R) = J := by rw [← conjSub_tightCore, hgJ]
  obtain ⟨SJ, hdJ, ⟨eJ⟩⟩ := hd.conj g
  have hcJ : TightCls Y (conjSub g R) SJ (g * t * g⁻¹) := hc.conj g eJ
  have hE2J : ¬ TightInO2 (g * t * g⁻¹) := not_tightInO2_conj hE2 g
  have hKJ : tightCore R ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) J :=
    Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hK hJ.1 hJ
  have hfam : CoreAssembly.conjClass (tightCore (conjSub g R)) =
      CoreAssembly.conjClass (tightCore R) := by
    rw [← conjSub_tightCore, conjClass_conjSub]
  have hKJ' : tightCore R ∈ omegaNbr (CoreAssembly.conjClass (tightCore (conjSub g R)))
      (tightCore (conjSub g R)) := by
    rw [hfam, hJcore]
    exact hKJ
  refine ⟨g, hgJ ▸ hJ, htu, hut, h n hA hB Y hn R S t hd hc hE2 hQ hlarge J hJ _ hu htu, ?_⟩
  exact h n hA hB Y hn (conjSub g R) SJ _ hdJ hcJ hE2J hQ hlarge _ hKJ' t huniq hut

@[expose] def TightEdgePairGoodS (n : ℕ) : Prop :=
  CIT3Below n → TightBelow n → ∀ (Y : Type) [Group Y] [Finite Y], Nat.card Y = n →
    ∀ (R : Subgroup Y) (S : Sylow 2 R) (t : Y), TightDatum R S t → TightCls Y R S t →
      ¬ TightInO2 t → TightFStarQuasisimple Y →
        ¬ TwoSubgroupsFourGenerated (genFittingFStar Y) → ¬ TightEdgeless R →
          Subgroup.center Y = ⊥ →
          ∃ g : Y, conjSub g (tightCore R) ∈
              omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R) ∧
            ∃ (htu : t ∈ Subgroup.centralizer ({g * t * g⁻¹} : Set Y))
              (hut : g * t * g⁻¹ ∈ Subgroup.centralizer ({t} : Set Y)),
              GoodThreeElement (R.subgroupOf (Subgroup.centralizer ({g * t * g⁻¹} : Set Y)))
                (⟨t, htu⟩ : _) ∧
              GoodThreeElement ((conjSub g R).subgroupOf (Subgroup.centralizer ({t} : Set Y)))
                (⟨g * t * g⁻¹, hut⟩ : _)

@[expose] def TightLargeLiftS (n : ℕ) : Prop :=
  CIT3Below n → TightBelow n → ∀ (Y : Type) [Group Y] [Finite Y], Nat.card Y = n →
    ∀ (R : Subgroup Y) (S : Sylow 2 R) (t : Y), TightDatum R S t → TightCls Y R S t →
      ¬ TightInO2 t → TightFStarQuasisimple Y →
        ¬ TwoSubgroupsFourGenerated (genFittingFStar Y) → ¬ TightEdgeless R →
          Subgroup.center Y = ⊥ → GoodThreeElement R t

theorem tightLargeLiftS_of_lift (h : ∀ n, TightLargeLift n) : ∀ n, TightLargeLiftS n :=
  fun n hA hB Y _ _ hn R S t hd hc hE2 hQ hlarge hedge _ =>
    h n hA hB Y hn R S t hd hc hE2 hQ hlarge hedge

theorem TightDatum.good_of_edgePair {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y}
    {S : Sylow 2 R} {t : Y} (hA : CIT3Below n) (hn : Nat.card Y = n) (hd : TightDatum R S t)
    (hE2 : ¬ TightInO2 t) {g : Y}
    (hJ : conjSub g (tightCore R) ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (htu : t ∈ Subgroup.centralizer ({g * t * g⁻¹} : Set Y))
    (hut : g * t * g⁻¹ ∈ Subgroup.centralizer ({t} : Set Y))
    (hg1 : GoodThreeElement (R.subgroupOf (Subgroup.centralizer ({g * t * g⁻¹} : Set Y)))
      (⟨t, htu⟩ : _))
    (hg2 : GoodThreeElement ((conjSub g R).subgroupOf (Subgroup.centralizer ({t} : Set Y)))
      (⟨g * t * g⁻¹, hut⟩ : _)) :
    GoodThreeElement R t := by
  have hΩ := hd.hypOmegaGen
  have huniq := hd.isUniqueInvolution_core
  have hK : tightCore R ∈ CoreAssembly.conjClass (tightCore R) :=
    CoreAssembly.mem_conjClass_self _
  set J : Subgroup Y := conjSub g (tightCore R) with hJdef
  have hu : IsUniqueInvolution J (g * t * g⁻¹) := huniq.conj g
  obtain ⟨-, hu2, hut', htu', huK, T, hTJ, -, hTc, hTD⟩ := hd.edge_involution hJ hu
  have hJcore : tightCore (conjSub g R) = J := by rw [← conjSub_tightCore]
  obtain ⟨SJ, hdJ, -⟩ := hd.conj g
  have hKJ : tightCore R ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) J :=
    Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hK hJ.1 hJ
  have hfam : CoreAssembly.conjClass (tightCore (conjSub g R)) =
      CoreAssembly.conjClass (tightCore R) := by
    rw [← conjSub_tightCore, conjClass_conjSub]
  have hKJ' : tightCore R ∈ omegaNbr (CoreAssembly.conjClass (tightCore (conjSub g R)))
      (tightCore (conjSub g R)) := by
    rw [hfam, hJcore]
    exact hKJ
  obtain ⟨-, -, -, -, -, T', hT'K, -, hT'c, hT'D⟩ := hdJ.edge_involution hKJ' huniq
  have hTJ' : IsSylow2In T (tightCore (conjSub g R)) := hJcore ▸ hTJ
  obtain ⟨L, hL⟩ := hd.exists_member_dbar hdJ hut' huK hTJ' hTc hTD hT'K hT'c hT'D hg2
  have hcard : Nat.card hd.Dbar + 1 ≤ n := by
    have := hd.card_dbar_lt hE2
    omega
  exact hd.good_of_section_member (CIT3Below.mono hcard hA) hut' huK hu2 htu hg1 hL

theorem tightLargeLift_of_edgePair (h : ∀ n, TightEdgePairGood n) : ∀ n, TightLargeLift n := by
  intro n hA hB Y _ _ hn R S t hd hc hE2 hQ hlarge hedge
  obtain ⟨g, hJ, htu, hut, hg1, hg2⟩ := h n hA hB Y hn R S t hd hc hE2 hQ hlarge hedge
  exact hd.good_of_edgePair hA hn hE2 hJ htu hut hg1 hg2

theorem tightLargeLiftS_of_edgePairS (h : ∀ n, TightEdgePairGoodS n) : ∀ n, TightLargeLiftS n := by
  intro n hA hB Y _ _ hn R S t hd hc hE2 hQ hlarge hedge hZ
  obtain ⟨g, hJ, htu, hut, hg1, hg2⟩ := h n hA hB Y hn R S t hd hc hE2 hQ hlarge hedge hZ
  exact hd.good_of_edgePair hA hn hE2 hJ htu hut hg1 hg2

end Cit3

end CFSG.ClassicalInvolution.Q3
