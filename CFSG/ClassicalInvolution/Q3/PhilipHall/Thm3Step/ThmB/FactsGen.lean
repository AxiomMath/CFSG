module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.ThmB.Facts
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S6
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseIINbrTNormal

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.ThmB

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3Core
  CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

variable {Y : Type} [Group Y] [Finite Y] {Φ : Set (Subgroup Y)} {Q : Subgroup Y}

theorem inv_mem_of_aViol (hΦ : TypeRHyp Φ) (hO : classicalInvolutionOddCore Y = ⊥)
    (hQn : Q.Normal) {M J : Subgroup Y} {zM zJ : Y} (hM : M ∈ Φ) (hv : AViol Φ M J zM zJ)
    (hzM : zM ∈ Q) : zJ ∈ Q := by
  by_contra hzJ
  have hJC : J ≤ Subgroup.centralizer (Q : Set Y) :=
    (⟨hΦ, hO⟩ : S6.Hyp Φ).le_centralizer_of_not_mem hv.mem hv.hzJ hQn hzJ
  have hJz : J ≤ Subgroup.centralizer ({zM} : Set Y) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      ((Subgroup.mem_centralizer_iff.mp (hJC hx) zM hzM).symm)
  obtain ⟨R, hR, hRJ, -⟩ :=
    exists_mem_RSet_ge hv.mem (IsPGroup.of_bot : IsPGroup 2 (⊥ : Subgroup Y)) bot_le
  have h8 := Sec6Gen.eight_le_of_mem_RSet hΦ.hyp hR
  have hRN := Sec6Gen.le_normalizer_of_le_centralizer hΦ.hyp hM hv.mem hv.ne.symm hv.hzK hRJ.1
    hRJ.2.1 (by omega) (hRJ.1.trans hJz)
  exact hv.not_nbr ⟨hv.mem, hv.ne, R, hR, hRJ.1, hRN⟩

theorem inv_mem_of_mem_aStar (hΦ : TypeRHyp Φ) (hO : classicalInvolutionOddCore Y = ⊥)
    (hQn : Q.Normal) {K : Subgroup Y} (hK : K ∈ Φ)
    (hKQ : ∀ w : Y, IsUniqueInvolution K w → w ∈ Q) {M : Subgroup Y} (hM : M ∈ aStar Φ K) :
    ∀ w : Y, IsUniqueInvolution M w → w ∈ Q := by
  induction hM with
  | refl => exact hKQ
  | @tail L N hKL hLN ih =>
    intro w hw
    have hLΦ : L ∈ Φ := mem_of_mem_aStar hK hKL
    rcases hLN.2 with ⟨zL, zN, hv⟩ | ⟨zN, zL, hv⟩ | ⟨⟨-, w', hw'L, hw'N⟩, -⟩
    · rw [hw.eq hv.hzJ]
      exact inv_mem_of_aViol hΦ hO hQn hLΦ hv (ih zL hv.hzK)
    · have hvs := aviol_symm_of_hypOmegaGen hΦ.hyp hLN.1 hv
      rw [hw.eq hvs.hzJ]
      exact inv_mem_of_aViol hΦ hO hQn hLΦ hvs (ih zL hvs.hzK)
    · rw [hw.eq hw'N]
      exact ih w' hw'L

theorem isPGroup_of_mem_aStar (hΦ : TypeRHyp Φ) (hO : classicalInvolutionOddCore Y = ⊥)
    (hQn : Q.Normal) (hQ2 : IsPGroup 2 Q) {K : Subgroup Y} (hK : K ∈ Φ)
    (hKQ : ∀ w : Y, IsUniqueInvolution K w → w ∈ Q) {M : Subgroup Y} (hM : M ∈ aStar Φ K) :
    IsPGroup 2 M := by
  have hMΦ := mem_of_mem_aStar hK hM
  obtain ⟨w, hw⟩ := Sec6Gen.exists_uniqueInvolution hΦ.hyp hMΦ
  exact isPGroup_of_inv_mem hΦ hO hMΦ hw hQn hQ2 (inv_mem_of_mem_aStar hΦ hO hQn hK hKQ hM w hw)

theorem omegaOfSet_subset_of_aViol_of_isPGroup (hΦ : HypOmegaGen Φ) {M J : Subgroup Y}
    {zM zJ : Y} (hM : M ∈ Φ) (hv : AViol Φ M J zM zJ)
    (h2 : ∀ N ∈ twinSet Φ M, IsPGroup 2 N) :
    omegaOfSet Φ (twinSet Φ M) ⊆ omegaOfSet Φ (twinSet Φ J) := by
  intro L hLset
  obtain ⟨v, Ms, hVU, hVJ, -, -, htw, hvv⟩ :=
    Q3T6D.exists_hexagon_data3 hΦ hM hv.mem hv.hzK hv.hzJ hv.star hv.not_nbr hv.no_conj
  have hMT : M ∈ twinSet Φ M := ⟨hM, zM, hv.hzK, hv.hzK⟩
  have hMsT : Ms ∈ twinSet Φ M := by
    rw [htw]
    exact Or.inr rfl
  have hzJM : zJ ∈ M ⊔ Ms := Q3T6D.mem_sup_of_hexagon3 hΦ hv.hzJ hVU hVJ hvv
  have hLΦ : L ∈ Φ := hLset.1
  have hLM : L ∈ omegaNbr Φ M := hLset.2 M hMT
  obtain ⟨-, -, R, hR, hRL, hRN⟩ := hLM
  have hRs : IsSylow2In R L := Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΦ hLΦ hR hRL
  have h8 : 8 ≤ Nat.card R := Sec6Gen.eight_le_of_mem_RSet hΦ hR
  have hRc : ∀ N ∈ twinSet Φ M, Commutes N R := by
    intro N hN
    have hNΦ : N ∈ Φ := hN.1
    have hzN : IsUniqueInvolution N zM := isUniqueInvolution_of_mem_twinSet hv.hzK hN
    have hLN : L ≠ N := (hLset.2 N hN).2.1
    have hRNN : R ≤ Subgroup.normalizer (N : Set Y) :=
      Sec6Gen.le_normalizer_of_le_centralizer hΦ hNΦ hLΦ (Ne.symm hLN) hzN hRL hRs.2.1
        (by omega) (Sec6Gen.le_centralizer_of_le_normalizer' hv.hzK hRN)
    have hN2 := h2 N hN
    have hNR : N ≠ R := by
      intro e
      have hNL : N ≤ L := e ▸ hRL
      have h4 : 4 ≤ Nat.card N := by
        rw [e]
        omega
      exact hLN (Sec6Gen.eq_of_le_of_le hΦ hNΦ hLΦ hN2 h4 le_rfl hNL).symm
    exact TL4.commutes_of_le_normalizer hΦ (TC.mem_RSet_of_isPGroup hNΦ hN2) hR hN2 hRs.2.1
      hNR hRNN
  have hRzJ : R ≤ Subgroup.centralizer ({zJ} : Set Y) := by
    intro r hr
    have hle : M ⊔ Ms ≤ Subgroup.centralizer ({r} : Set Y) := sup_le
      (fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr ((hRc M hMT) x hx r hr))
      (fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr ((hRc Ms hMsT) x hx r hr))
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp (hle hzJM)).symm
  refine ⟨hLΦ, fun J' hJ' => ?_⟩
  have hzJ' : IsUniqueInvolution J' zJ := isUniqueInvolution_of_mem_twinSet hv.hzJ hJ'
  have hLJ' : L ≠ J' := by
    rintro rfl
    have h1 : M ∈ omegaNbr Φ L := Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΦ hM hLΦ (hLset.2 M hMT)
    exact hv.not_nbr (Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΦ hv.mem hM
      (TwinExitPf4.omegaNbr_of_twin hΦ hv.mem hzJ' hv.hzJ h1 hv.ne.symm))
  exact ⟨hLΦ, hLJ', R, hR, hRL, Sec6Gen.le_normalizer_of_le_centralizer hΦ hJ'.1 hLΦ
    (Ne.symm hLJ') hzJ' hRL hRs.2.1 (by omega) hRzJ⟩

theorem aStar_subset_vStar_of_inv_mem (hΦ : TypeRHyp Φ) (hO : classicalInvolutionOddCore Y = ⊥)
    (hQn : Q.Normal) (hQ2 : IsPGroup 2 Q) {K : Subgroup Y} (hK : K ∈ Φ)
    (hKQ : ∀ w : Y, IsUniqueInvolution K w → w ∈ Q) : aStar Φ K ⊆ vStar Φ K := by
  have h2 : ∀ M ∈ aStar Φ K, ∀ N ∈ twinSet Φ M, IsPGroup 2 N := by
    intro M hM N hN
    obtain ⟨hNΦ, w, hwM, hwN⟩ := hN
    exact isPGroup_of_mem_aStar hΦ hO hQn hQ2 hK hKQ (mem_aStar_of_twin hM hNΦ hwM hwN)
  intro M hM
  induction hM with
  | refl => exact ⟨hK, rfl⟩
  | @tail L N hKL hLN ih =>
    obtain ⟨hLΦ, heq⟩ := ih
    have hNA : N ∈ aStar Φ K := hKL.tail hLN
    refine ⟨hLN.1, heq.trans ?_⟩
    rcases hLN.2 with ⟨zL, zN, hv⟩ | ⟨zN, zL, hv⟩ | ⟨htw, -⟩
    · exact Set.Subset.antisymm (omegaOfSet_subset_of_aViol_of_isPGroup hΦ.hyp hLΦ hv (h2 L hKL))
        (omegaOfSet_subset_of_aViol_of_isPGroup hΦ.hyp hLN.1
          (aviol_symm_of_hypOmegaGen hΦ.hyp hLΦ hv) (h2 N hNA))
    · exact Set.Subset.antisymm (omegaOfSet_subset_of_aViol_of_isPGroup hΦ.hyp hLΦ
          (aviol_symm_of_hypOmegaGen hΦ.hyp hLN.1 hv) (h2 L hKL))
        (omegaOfSet_subset_of_aViol_of_isPGroup hΦ.hyp hLN.1 hv (h2 N hNA))
    · obtain ⟨w, hw⟩ := Sec6Gen.exists_uniqueInvolution hΦ.hyp hLΦ
      rw [twinSet_eq_of_mem_twinSet hw htw]

theorem aStar_subset_vStar (hΦ : TypeRHyp Φ) (hO : classicalInvolutionOddCore Y = ⊥)
    {K : Subgroup Y} (hK : K ∈ Φ) {z : Y} (hz : IsUniqueInvolution K z) (hzO : TightInO2 z) :
    aStar Φ K ⊆ vStar Φ K := by
  obtain ⟨Q, hQn, hQ2, hzQ⟩ := hzO
  exact aStar_subset_vStar_of_inv_mem hΦ hO hQn hQ2 hK fun w hw => hz.eq hw ▸ hzQ

end CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.ThmB
