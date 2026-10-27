module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm3QuotComp
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf49G3At
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf24Desc

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf.Thm3A

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3Typed CFSG.ClassicalInvolution.Asc77.T3Core
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open scoped commutatorElement

@[expose] def Thm3RGroupQuotG (Y : Type) [Group Y] [Finite Y] : Prop :=
  ∀ Φ : Set (Subgroup Y), TypeRHyp Φ → ∀ K ∈ Φ, ¬ AEmpty Φ K →
    Thm3RConclG (oddQuotientFamily Φ) (K.map (QuotientGroup.mk' (classicalInvolutionOddCore Y)))

theorem thm3RGroupQuotG_of_belowG {n : ℕ} (hB : Thm3RBelowG n) {Y : Type} [Group Y] [Finite Y]
    (hY : Nat.card Y < n) : Thm3RGroupQuotG Y := by
  intro Φ hΦ K hK hA
  set N := classicalInvolutionOddCore Y with hNdef
  have hN : Odd (Nat.card N) := CFSG.ComponentClassification.OddCore.odd_card Y
  have hΦ' : TypeRHyp (oddQuotientFamily Φ) := typeRHyp_oddQuot hΦ hN
  have hK' : K.map (QuotientGroup.mk' N) ∈ oddQuotientFamily Φ := map_mem_quotFamily hK
  have hA' : ¬ AEmpty (oddQuotientFamily Φ) (K.map (QuotientGroup.mk' N)) :=
    Thm3Quot.not_aEmpty_map hΦ.hyp hN hK hA
  have hlt : Nat.card (Y ⧸ N) < n :=
    lt_of_le_of_lt (Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_card N)) hY
  have hO : classicalInvolutionOddCore (Y ⧸ N) = ⊥ :=
    CFSG.ComponentClassification.OddCore.quotient_corefree Y
  exact hB _ hlt (Y ⧸ N) rfl hO _ hΦ' _ hK' hA'

theorem thm3R_lift_stab {Y : Type} [Group Y] [Finite Y] (hQ : Thm3RGroupQuotG Y)
    {Φ : Set (Subgroup Y)} (hΦ : TypeRHyp Φ) {K : Subgroup Y} (hK : K ∈ Φ) (hA : ¬ AEmpty Φ K)
    {L M : Subgroup Y} (hL : L ∈ Φ) (hLA : L ∉ aStar Φ K) (hM : M ∈ aStar Φ K) :
    L ≤ conjStab (aStar Φ K) ∧
      ∀ R : Subgroup Y, IsSylow2In R L →
        ∃ n ∈ classicalInvolutionOddCore Y,
          R ≤ Subgroup.normalizer ((conjSub n M : Subgroup Y) : Set Y) ∧
            conjSub n M ∈ aStar Φ K := by
  set N := classicalInvolutionOddCore Y with hNdef
  have hN : Odd (Nat.card N) := CFSG.ComponentClassification.OddCore.odd_card Y
  have hΩ : HypOmegaGen Φ := hΦ.hyp
  have hc := hΩ.conjInvariant
  have hMΦ : M ∈ Φ := mem_of_mem_aStar hK hM
  obtain ⟨⟨heq, hcomm⟩, -⟩ := hQ Φ hΦ K hK hA
  have hMb : M.map (QuotientGroup.mk' N) ∈ vStar (oddQuotientFamily Φ)
      (K.map (QuotientGroup.mk' N)) := by
    rw [← heq]
    exact Thm3Quot.map_mem_aStar hΩ hN hK hM
  have hLb : L.map (QuotientGroup.mk' N) ∉ vStar (oddQuotientFamily Φ)
      (K.map (QuotientGroup.mk' N)) := by
    rw [← heq]
    exact fun h => hLA ((Thm3Quot.map_mem_aStar_iff hΩ hN hK hA hL).mp h)
  have hc1 := hcomm _ (map_mem_quotFamily hL) hLb _ hMb
  have hLN : L.map (QuotientGroup.mk' N) ≤ Subgroup.normalizer
      ((M.map (QuotientGroup.mk' N) : Subgroup (Y ⧸ N)) : Set (Y ⧸ N)) :=
    le_normalizer_of_commutator_le (hc1.trans (inf_le_right.trans (oddCoreOf_le_self _)))
  have hNA : N ≤ conjStab (aStar Φ K) := Thm3Quot.le_conjStab_aStar_of_normal hΩ hN hK hA
  have hsyl : ∀ R : Subgroup Y, IsSylow2In R L →
      ∃ n ∈ N, R ≤ Subgroup.normalizer ((conjSub n M : Subgroup Y) : Set Y) ∧
        conjSub n M ∈ aStar Φ K := by
    intro R hR
    obtain ⟨n, hn, hRn⟩ := Thm3Quot.exists_conj_normalizes_of_map hΩ hN hMΦ hR.2.1
      ((Subgroup.map_mono hR.1).trans hLN)
    exact ⟨n, hn, hRn, (mem_conjStab_iff.mp (hNA hn) M).mpr hM⟩
  refine ⟨?_, hsyl⟩
  rw [← Thm3Quot.closure_twoElts_eq_of_typeRHyp hΦ hL, Subgroup.closure_le]
  rintro x ⟨hxL, hx2⟩
  obtain ⟨R, hR, hxR⟩ := IsSylow2In.exists_ge hx2 (Subgroup.zpowers_le.mpr hxL)
  obtain ⟨n, -, hRn, hMn⟩ := hsyl R hR
  exact mem_conjStab_aStar hc hK hMn
    (mem_normalizer_iff_conjSub_eq.mp (hRn (hxR (Subgroup.mem_zpowers x))))

theorem thm3R_comm_mod {Y : Type} [Group Y] [Finite Y] (hQ : Thm3RGroupQuotG Y)
    {Φ : Set (Subgroup Y)} (hΦ : TypeRHyp Φ) {K : Subgroup Y} (hK : K ∈ Φ) (hA : ¬ AEmpty Φ K)
    {L M : Subgroup Y} (hL : L ∈ Φ) (hLA : L ∉ aStar Φ K) (hM : M ∈ aStar Φ K) :
    ⁅L, M⁆ ≤ (oddCoreOf L ⊔ classicalInvolutionOddCore Y) ⊓
      (oddCoreOf M ⊔ classicalInvolutionOddCore Y) := by
  set N := classicalInvolutionOddCore Y with hNdef
  have hN : Odd (Nat.card N) := CFSG.ComponentClassification.OddCore.odd_card Y
  have hΩ : HypOmegaGen Φ := hΦ.hyp
  have hMΦ : M ∈ Φ := mem_of_mem_aStar hK hM
  obtain ⟨⟨heq, hcomm⟩, -⟩ := hQ Φ hΦ K hK hA
  have hMb : M.map (QuotientGroup.mk' N) ∈ vStar (oddQuotientFamily Φ)
      (K.map (QuotientGroup.mk' N)) := by
    rw [← heq]
    exact Thm3Quot.map_mem_aStar hΩ hN hK hM
  have hLb : L.map (QuotientGroup.mk' N) ∉ vStar (oddQuotientFamily Φ)
      (K.map (QuotientGroup.mk' N)) := by
    rw [← heq]
    exact fun h => hLA ((Thm3Quot.map_mem_aStar_iff hΩ hN hK hA hL).mp h)
  have hc1 := hcomm _ (map_mem_quotFamily hL) hLb _ hMb
  rw [← Subgroup.map_commutator, oddCoreOf_map_mk_of_odd (odd_natCard_inf hN L),
    oddCoreOf_map_mk_of_odd (odd_natCard_inf hN M)] at hc1
  have key : ∀ A : Subgroup Y, ⁅L, M⁆.map (QuotientGroup.mk' N) ≤ A.map (QuotientGroup.mk' N) →
      ⁅L, M⁆ ≤ A ⊔ N := by
    intro A h
    have := Subgroup.map_le_iff_le_comap.mp h
    rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at this
  exact le_inf (key _ (hc1.trans inf_le_left)) (key _ (hc1.trans inf_le_right))

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf.Thm3A
