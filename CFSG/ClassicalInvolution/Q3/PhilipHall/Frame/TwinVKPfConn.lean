module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVKPfTrans
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVKPfLift
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinSetCore
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinConnFinalModel
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPairOdd
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVKPfSec

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC CFSG.ClassicalInvolution.Q3.TC.Graph
  CFSG.ClassicalInvolution.Q3.TL4 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge

section Outcome

variable {G : Type} [Group G] [Finite G] {K₀ : Subgroup G}

theorem twinSetSectionOutcome {n : ℕ} (hT : Thm1RTwinLiftSetBelow n)
    (hs : TwinGraphStd K₀) (hS : IsSimpleGroup ↥(genFittingFStar G))
    (hnab : ∃ a b : ↥(genFittingFStar G), a * b ≠ b * a) (hn : Nat.card G ≤ n)
    {K K' : Subgroup G} (hK : K ∈ CoreAssembly.conjClass K₀)
    (hK' : K' ∈ twinSet (CoreAssembly.conjClass K₀) K) (hne : K' ≠ K)
    (hq8 : Nonempty (↥K ≃* QuaternionGroup 2)) (hA : AEmpty (CoreAssembly.conjClass K₀) K)
    {z : G} (hz : IsUniqueInvolution K z) :
    ∃ π, maxOrbs (nbrAdj (CoreAssembly.conjClass K₀)) K = {π} ∧ NoCentralInv π ∧
      ∀ g : G, conjSub g K ∈ π → ∀ hKX : K ≤ conjSub g (piGen π),
        classicalInvolutionOddCore ↥(conjSub g (piGen π)) = ⊥ →
          TwinE4 (SecQuot (conjSub g (piGen π))) ∨
            LongFundSet3 (secImage (conjSub g (piGen π)) K)
              (secInv (conjSub g (piGen π)) ⟨z, hKX hz.mem⟩) ∨
            ∀ M N : Subgroup G, MaxAdj (nbrAdj (CoreAssembly.conjClass K₀)) M N →
              ThinAt (CoreAssembly.conjClass K₀) M N := by
  have hZ := InductionBridge.center_eq_bot_of_fstar_simple hS hnab
  have hO2 : ∀ P : Subgroup G, P.Normal → IsPGroup 2 ↥P → P = ⊥ := fun _ hPn hP =>
    TwinSecXg.normalTwo_eq_bot_of_fstar_simple hS hnab hPn hP
  obtain ⟨π, h1, -, hH1⟩ := twin_noCentralInv hs hZ hK hK'.1 hne hz
  have hπ : π ∈ maxOrbs (nbrAdj (CoreAssembly.conjClass K₀)) K := by rw [h1]; rfl
  have hos := hs.orbitStd
  refine ⟨π, h1, hH1, fun g hg hKX hO => ?_⟩
  have hcard := TwinSecXg.card_conj_lt hos hK hπ hH1 hZ hz g
  have hSec := TwinSecXg.twinSection_conj hos hK hπ hH1 hg hK' hne
  rcases sectionOutcomeSet_twin hT hs.hyp hs.two hK hq8 hA hSec.le_left (lt_of_lt_of_le hcard hn)
    hSec.gen hz ⟨K', hSec.twin, hSec.ne⟩ with h | h | h
  · exact Or.inr (Or.inr (TwinSecXg.twin_thin_of_tightInO2 hs hO2 hK hq8 hπ hH1 hz hg hKX hO h))
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

end Outcome

structure TwinConnPreS (n : ℕ) {Y : Type} [Group Y] [Finite Y] (R : Subgroup Y) (t : Y) :
    Prop where
  card : Nat.card Y = n
  simple : IsSimpleGroup ↥(genFittingFStar Y)
  nonab : ∃ a b : ↥(genFittingFStar Y), a * b ≠ b * a
  below : CIT3Below n
  twinBelow : Thm1RTwinLiftSetBelow n
  aEmpty : AEmpty (CoreAssembly.conjClass (tightCore R)) (tightCore R)
  ht : IsUniqueInvolution (tightCore R) t
  twin : ∃ K' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R), K' ≠ tightCore R
  oddCent : ∀ K ∈ CoreAssembly.conjClass (tightCore R), ∀ z : Y, IsUniqueInvolution K z →
    classicalInvolutionOddCore ↥(Subgroup.centralizer ({z} : Set Y)) = ⊥
  mem : ∀ J ∈ CoreAssembly.conjClass (tightCore R), IsPGroup 2 ↥J ∧
    Nonempty (↥J ≃* QuaternionGroup 2)
  gs : TwinGraphStd (tightCore R)
  autOdd : ∀ M ∈ CoreAssembly.conjClass (tightCore R),
      ∀ N ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) M,
      ∀ zM zN : Y, IsUniqueInvolution M zM → IsUniqueInvolution N zN → zM ≠ zN →
        ∀ hcomm : zM ∈ Subgroup.centralizer ({zN} : Set Y),
        ∀ L : Subgroup (OddQuot zN), CFSG.IsComponent L →
          oddQuotMk zN ⟨zM, hcomm⟩ ∈ Subgroup.normalizer (L : Set (OddQuot zN)) →
          (∃ y ∈ L, oddQuotMk zN ⟨zM, hcomm⟩ * y ≠ y * oddQuotMk zN ⟨zM, hcomm⟩) →
          Q3NM.AutOddFreeOn ↥L (TL4.IsInducedAut L (oddQuotMk zN ⟨zM, hcomm⟩))

theorem longFundSetE3_of_conn {Y : Type} [Group Y] [Finite Y] {n : ℕ} {R : Subgroup Y} {t : Y}
    (h : TwinConnPreS n R t)
    (hthin : ¬ ∀ M N : Subgroup Y, MaxAdj (nbrAdj (CoreAssembly.conjClass (tightCore R))) M N →
      ThinAt (CoreAssembly.conjClass (tightCore R)) M N)
    (he4 : ∀ π : Set (Subgroup Y),
      π ∈ maxOrbs (nbrAdj (CoreAssembly.conjClass (tightCore R))) (tightCore R) →
      NoCentralInv π → ∀ g : Y, conjSub g (tightCore R) ∈ π →
        ¬ TwinE4 (SecQuot (conjSub g (piGen π)))) :
    LongFundSetE3 R t := by
  classical
  have hZ : Subgroup.center Y = ⊥ :=
    InductionBridge.center_eq_bot_of_fstar_simple h.simple h.nonab
  have hK₀Ω : tightCore R ∈ CoreAssembly.conjClass (tightCore R) :=
    CoreAssembly.mem_conjClass_self _
  have hz : IsUniqueInvolution (tightCore R) t := h.ht
  have hgs := h.gs
  have hos := hgs.orbitStd
  have hq8 : Nonempty (↥(tightCore R) ≃* QuaternionGroup 2) := (h.mem _ hK₀Ω).2
  have hK₀8 : Nat.card (tightCore R) = 8 := by
    rw [Nat.card_congr hq8.some.toEquiv]
    simp [Nat.card_eq_fintype_card, QuaternionGroup.card]
  obtain ⟨K', hK', hne⟩ := h.twin
  obtain ⟨π, hmax, hH1, hall⟩ := twinSetSectionOutcome h.twinBelow hgs h.simple h.nonab
    (le_of_eq h.card) hK₀Ω hK' hne hq8 h.aEmpty hz
  have hπ : π ∈ maxOrbs (nbrAdj (CoreAssembly.conjClass (tightCore R))) (tightCore R) := by
    rw [hmax]
    rfl
  obtain ⟨g, hg⟩ := TwinSecXg.exists_conj_mem hos hK₀Ω hπ
  have hKX : tightCore R ≤ conjSub g (piGen π) := hos.le_conj_piGen hπ hg
  have hw : IsUniqueInvolution (conjSub g (tightCore R)) (g * t * g⁻¹) := hz.conj g
  have hXw := (hos.conj_piGen_le_centralizer hK₀Ω hπ hH1 hz g).1
  have hXn := hos.conj_piGen_normal hK₀Ω hπ hH1 hz g
  have hO : classicalInvolutionOddCore ↥(conjSub g (piGen π)) = ⊥ :=
    TwinSecXg.oddCore_eq_bot_of_normal hXn hXw (h.oddCent _ ⟨g, rfl⟩ _ hw)
  have hLF : LongFundSet3 (secImage (conjSub g (piGen π)) (tightCore R))
      (secInv (conjSub g (piGen π)) ⟨t, hKX hz.mem⟩) := by
    rcases hall g hg hKX hO with h4 | hLF | hth
    · exact absurd h4 (he4 π hπ hH1 g hg)
    · exact hLF
    · exact absurd hth hthin
  obtain ⟨Λ, hΛ1, hΛ2⟩ := twinLiftSet_of_longFundSet3 hgs.hyp hgs.two hK₀Ω hKX hz hO hLF
  set V := twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R) with hVdef
  have hVfam : ∀ J ∈ V, J ∈ twinSet
      {L | ∃ x : ↥(conjSub g (piGen π)), conjSub (x : Y) (tightCore R) = L} (tightCore R) := by
    intro J hJ
    obtain ⟨a, ha, hJa⟩ := TwinSecXg.twin_conj hos hK₀Ω hπ hH1 hg hJ
    exact ⟨⟨⟨a, ha⟩, hJa⟩, hJ.2⟩
  have htX' : t ∈ conjSub g (piGen π) := hKX hz.mem
  have htw : g * t * g⁻¹ ∈ Subgroup.centralizer ({t} : Set Y) :=
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp (hXw htX')).symm
  have hwt : g * t * g⁻¹ ≠ t := by
    intro heq
    have hmemV : conjSub g (tightCore R) ∈ V :=
      ⟨⟨g, rfl⟩, t, hz, heq ▸ hw⟩
    exact Set.disjoint_left.mp (hos.disjoint_twinSet hπ hH1) hmemV hg
  have h1 : oddCoreImg (Subgroup.centralizer ({t} : Set Y)) = ⊥ :=
    TwinConnT.oddCoreIn_eq_bot_of_classicalOddCore (h.oddCent _ hK₀Ω t hz)
  have hAut := h.autOdd (conjSub g (tightCore R)) ⟨g, rfl⟩ (tightCore R)
    (TwinSecXg.maxAdj_conj_left hos hπ hg).1.2 (g * t * g⁻¹) t hw hz hwt htw
  have hOL : ∀ J ∈ V, classicalInvolutionOddCore ↥(Λ J) = ⊥ := by
    intro J hJ
    obtain ⟨hJX, hLX, -, hL⟩ := hΛ1 J (hVfam J hJ)
    have hsubL := TwinConnT.isSubnormal_of_on hLX hL
    exact (TwinPairOdd.oddCoreIn_eq_bot_of_isSubnormal htw hw.sq hw.ne_one h1 hAut hXw hXn
      (CFSG.RankThreeEvenClassification.Helpers.subnormal_le hsubL) hsubL).2
  have hOC : classicalInvolutionOddCore
      ↥(conjSub g (piGen π) ⊓ Subgroup.centralizer ({t} : Set Y)) = ⊥ :=
    TwinConnT.classicalOddCore_eq_bot_of_oddCoreIn
      (TwinPairOdd.oddCoreIn_inf_centralizer_of_normal_eq_bot htw hw.sq hw.ne_one h1 hAut hXw hXn)
  obtain ⟨hK₀X, hΛK₀X, hKL, hL₀⟩ := hΛ1 (tightCore R) (hVfam _ (tightCore_mem_twinSet_of_twin ⟨K', hK', hne⟩))
  have hmodel : Model1520 (piGen π) (g * t * g⁻¹) :=
    TwinConnT.model1520_of_twin_core h.below (le_of_eq h.card) hZ hgs hK' hne hz hπ hH1 hg
      (h.oddCent _ hK₀Ω t hz) hKL hL₀
  have hcl := TwinConnT.classical_lifts_set hgs hz hπ hH1 hg hK₀8 hmodel
    (fun J hJ => by
      obtain ⟨-, hLX, hJL, hL⟩ := hΛ1 J (hVfam J hJ)
      exact ⟨hLX, hJL, hL⟩)
    (fun J hJ J' hJ' hne' => hΛ2 J (hVfam J hJ) J' (hVfam J' hJ') hne') hOL hOC
  refine ⟨Λ, fun J hJ => ⟨(hΛ1 J (hVfam J hJ)).2.2.1, hcl J hJ⟩,
    fun J hJ J' hJ' hne' => hΛ2 J (hVfam J hJ) J' (hVfam J' hJ') hne', ?_⟩
  intro J hJ c hc
  have hct' : c * t * c⁻¹ = t := by
    rw [mul_inv_eq_iff_eq_mul]
    exact (Subgroup.mem_centralizer_singleton_iff.mp hc)
  have hJc := TwinConnT.conj_mem_twinSet_of_fix hgs.hyp hz hJ hct'
  have hcj := (hcl J hJ).conj c
  rw [hct'] at hcj
  exact TwinConnT.liftUnique_in hgs.hyp hJc.1 (TwinSecXg.isUniqueInvolution_of_mem_twinSet hz hJc)
    (Subgroup.map_mono (hΛ1 J (hVfam J hJ)).2.2.1) (hΛ1 _ (hVfam _ hJc)).2.2.1
    hcj (hcl _ hJc) (h.oddCent _ hK₀Ω t hz)

theorem twinCoreConnSE'_of_prelude {n : ℕ}
    (hpre : ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
      TwinCoreHypS n Y R S t → DConnected (CoreAssembly.conjClass (tightCore R)) →
        TwinConnPreS n R t)
    (hthin : ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
      TwinCoreHypS n Y R S t → DConnected (CoreAssembly.conjClass (tightCore R)) →
        ¬ ∀ M N : Subgroup Y, MaxAdj (nbrAdj (CoreAssembly.conjClass (tightCore R))) M N →
          ThinAt (CoreAssembly.conjClass (tightCore R)) M N)
    (he4 : ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
      TwinCoreHypS n Y R S t → DConnected (CoreAssembly.conjClass (tightCore R)) →
        ∀ π : Set (Subgroup Y),
          π ∈ maxOrbs (nbrAdj (CoreAssembly.conjClass (tightCore R))) (tightCore R) →
          NoCentralInv π → ∀ g : Y, conjSub g (tightCore R) ∈ π →
            ¬ TwinE4 (SecQuot (conjSub g (piGen π)))) :
    TwinCoreConnSE' n :=
  fun Y _ _ R S t h hconn =>
    longFundSetE3_of_conn (hpre Y R S t h hconn) (hthin Y R S t h hconn) (he4 Y R S t h hconn)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
