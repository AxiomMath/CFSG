module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.ThmB.Facts
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseIINbrTNormal

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.ThmB

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3Typed CFSG.ClassicalInvolution.Asc77.T3Core
  CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

variable {Y : Type} [Group Y] [Finite Y] {Φ : Set (Subgroup Y)} {Q : Subgroup Y}

theorem exists_twin_mem_aSet (hΦ : TypeRHyp Φ) {K J Js : Subgroup Y} {zK zJ : Y} (hK : K ∈ Φ)
    (hv : AViol Φ K J zK zJ) (hJs : Js ∈ twinSet Φ J) (hne : Js ≠ J) :
    ∃ K' ∈ twinSet Φ K, Js ∈ aSet Φ K' := by
  have hvs : AViol Φ J K zJ zK := aviol_symm_of_hypOmegaGen hΦ.hyp hK hv
  obtain ⟨Ms, d⟩ := FrameTwins.exists_of_aviol hΦ.hyp hΦ.twoGroup (natCard_sylow_eq_eight hΦ)
    hv.mem hvs
  have hJs' : Js ∈ ({J, Ms} : Set (Subgroup Y)) := by
    rw [← d.twins]
    exact hJs
  have hJsMs : Js = Ms := by
    rcases hJs' with e | e
    · exact absurd e hne
    · exact e
  subst hJsMs
  obtain ⟨K', hv'⟩ := d.isAInv_twin ⟨K, hvs⟩
  exact ⟨K', ⟨hv'.mem, zK, hv.hzK, hv'.hzJ⟩, zK, zJ, aviol_symm_of_hypOmegaGen hΦ.hyp d.mem' hv'⟩

namespace QFam

variable (h : QFam Φ Q)
include h

theorem omegaOfSet_eq_of_aViol {M J : Subgroup Y} {zM zJ : Y} (hM : M ∈ Φ)
    (hv : AViol Φ M J zM zJ) : omegaOfSet Φ (twinSet Φ M) = omegaOfSet Φ (twinSet Φ J) := by
  have hN : ∀ K ∈ Φ, ∀ L ∈ omegaNbr Φ K, L ∉ twinSet Φ K →
      K ≤ Subgroup.normalizer (L : Set Y) :=
    fun K hK L hL _ => AscL62.le_normalizer_of_commutes (h.commutes_of_mem_omegaNbr hK hL)
  exact Set.Subset.antisymm (omegaOfSet_subset_of_normalizes h.hypGen hN hM hv)
    (omegaOfSet_subset_of_normalizes h.hypGen hN hv.mem
      (aviol_symm_of_hypOmegaGen h.hypGen hM hv))

theorem aStar_subset_vStar {K : Subgroup Y} (hK : K ∈ Φ) : aStar Φ K ⊆ vStar Φ K := by
  intro M hM
  induction hM with
  | refl => exact ⟨hK, rfl⟩
  | @tail L N _ hLN ih =>
    obtain ⟨hLΦ, heq⟩ := ih
    refine ⟨hLN.1, heq.trans ?_⟩
    rcases hLN.2 with ⟨zL, zN, hv⟩ | ⟨zN, zL, hv⟩ | ⟨htw, -⟩
    · exact h.omegaOfSet_eq_of_aViol hLΦ hv
    · exact (h.omegaOfSet_eq_of_aViol hLN.1 hv).symm
    · obtain ⟨w, hw⟩ := Sec6Gen.exists_uniqueInvolution h.hypGen hLΦ
      rw [twinSet_eq_of_mem_twinSet hw htw]

theorem not_mem_omegaOfSet_of_mem_aStar {K L P : Subgroup Y} (hK : K ∈ Φ) (hL : L ∈ aStar Φ K)
    (hP : P ∈ aStar Φ K) : P ∉ omegaOfSet Φ (twinSet Φ L) := by
  intro hPL
  obtain ⟨-, hKL⟩ := h.aStar_subset_vStar hK hL
  obtain ⟨hPΦ, hKP⟩ := h.aStar_subset_vStar hK hP
  rw [← hKL, hKP] at hPL
  obtain ⟨w, hw⟩ := Sec6Gen.exists_uniqueInvolution h.hypGen hPΦ
  exact (hPL.2 P ⟨hPΦ, w, hw, hw⟩).2.1 rfl

theorem conj_eq_of_mem_conjStab {K M : Subgroup Y} (hK : K ∈ Φ) (hM : M ∈ aStar Φ K) {t : Y}
    (htQ : t ∈ Q) (htA : t ∈ conjStab (aStar Φ K)) {w : Y} (hw : IsUniqueInvolution M w) :
    t * w * t⁻¹ = w := by
  have hΦ := h.hypGen
  have hMΦ : M ∈ Φ := mem_of_mem_aStar hK hM
  have hMt : conjSub t M ∈ aStar Φ K := (mem_conjStab_iff.mp htA M).mpr hM
  have hMtΦ : conjSub t M ∈ Φ := hΦ.conjInvariant t M hMΦ
  by_cases he : conjSub t M = M
  · exact hw.conj_eq he
  have hMQ : IsPGroup 2 ↥(M ⊔ Q) := by
    haveI := h.normal
    exact IsPGroup.to_sup_of_normal_right (h.isPGroup M hMΦ) h.two
  have hMtle : conjSub t M ≤ M ⊔ Q := by
    have := conjSub_mono (n := t) (le_sup_left : M ≤ M ⊔ Q)
    rwa [conjSub_eq_self_of_mem (Subgroup.mem_sup_right htQ)] at this
  have hcomm := h.commutes_of_le_isPGroup hMΦ hMtΦ (Ne.symm he) hMQ le_sup_left hMtle
  have hnbr : conjSub t M ∈ omegaNbr Φ M :=
    h.mem_omegaNbr_of_commutes hMtΦ he (commutes_symm hcomm)
  by_cases htw : conjSub t M ∈ twinSet Φ M
  · exact (hw.conj t).eq (isUniqueInvolution_of_mem_twinSet hw htw)
  · exact absurd (mem_omegaOfSet_of_mem_omegaNbr hΦ hw hnbr htw)
      (h.not_mem_omegaOfSet_of_mem_aStar hK hM hMt)

end QFam

end CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.ThmB
