module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm4TwinComp
public import CFSG.ClassicalInvolution.Q3.TL4SepTwoA

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge

namespace Thm4Twin

variable {r : ℕ} {G : Type} [Group G] [Finite G] {Δ : Set (Subgroup G)}

theorem TwinT4Hyp.isSubnormal_centralizer (h : TwinT4Hyp r G Δ) {J : Subgroup G} (hJ : J ∈ Δ)
    {u : G} (hu : IsUniqueInvolution J u) :
    CFSG.Open.IsSubnormal J (Subgroup.centralizer ({u} : Set G)) := by
  obtain ⟨S⟩ : Nonempty (Sylow 2 ↥J) := inferInstance
  have hd := h.q8Datum hJ hu S
  have hΩ := h.hypOmegaGen_conjClass hJ
  set T := twinGroup J with hT
  have hJT : J ≤ T := by
    have := tightCore_le_twinGroup hd
    rwa [h.tightCore_eq hJ] at this
  have hTC : T ≤ Subgroup.centralizer ({u} : Set G) := by
    refine iSup₂_le fun K hK => ?_
    obtain ⟨-, z, hzK, hzJ⟩ := hK
    have hz : z = u := hzK.eq (by rw [h.tightCore_eq hJ]; exact hu)
    rw [hz] at hzJ
    exact isUniqueInvolution_le_centralizer hzJ
  have hCN : Subgroup.centralizer ({u} : Set G) ≤ Subgroup.normalizer (T : Set G) := by
    intro d hdC
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => conj_mem_twinGroup hd hΩ hdC hx, fun hx => ?_⟩
    have := conj_mem_twinGroup hd hΩ (Subgroup.inv_mem _ hdC) hx
    simpa [mul_assoc] using this
  have hTN : T ≤ Subgroup.normalizer (J : Set G) := by
    refine iSup₂_le fun K hK => ?_
    obtain ⟨hKΩ, z, hzK, hzJ⟩ := hK
    have hKΔ : K ∈ Δ := by
      obtain ⟨g, rfl⟩ := hKΩ
      rw [h.tightCore_eq hJ]
      exact h.hyp.conjInvariant g J hJ
    by_cases hKJ : K = J
    · rw [hKJ]
      exact Subgroup.le_normalizer
    · have hz : z = u := hzK.eq (by rw [h.tightCore_eq hJ]; exact hu)
      rw [hz] at hzJ
      exact Sec6Gen.le_normalizer_of_twin h.hyp hKΔ hJ hKJ hzJ hu
  exact CFSG.Open.IsSubnormal.step hJT
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hJT).mpr hTN)
    (CFSG.Open.IsSubnormal.step hTC
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hTC).mpr hCN)
      (CFSG.Open.IsSubnormal.refl _))

theorem TwinT4Hyp.oddCoreImg_le (h : TwinT4Hyp r G Δ) {J : Subgroup G} (hJ : J ∈ Δ) {u : G}
    (hu : IsUniqueInvolution J u) :
    oddCoreImg J ≤ oddCoreImg (Subgroup.centralizer ({u} : Set G)) :=
  TwinExact.oddCoreOf_le_of_isSubnormal (h.isSubnormal_centralizer hJ hu)

theorem TwinT4Hyp.isPGroup_of_inO2 (h : TwinT4Hyp r G Δ) {J : Subgroup G} (hJ : J ∈ Δ) {u : G}
    (hu : IsUniqueInvolution J u) (hin : TightInO2 u) : IsPGroup 2 J := by
  obtain ⟨P, hPn, hP2, huP⟩ := hin
  have h1 : oddCoreImg J ≤ ⊥ := (h.oddCoreImg_le hJ hu).trans
    (TC.oddCoreImg_centralizer_eq_bot h.odd hPn hP2 huP).le
  have h2 : classicalInvolutionOddCore ↥J = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ J.subtype_injective).mp (le_bot_iff.mp h1)
  exact (h.twoGroup J hJ).of_equiv
    ((QuotientGroup.quotientMulEquivOfEq h2).trans QuotientGroup.quotientBot)

variable {J L : Subgroup G}

theorem TwinT4Min.symm (h : TwinT4Min r G Δ J L) : TwinT4Min r G Δ L J where
  ih := h.ih
  hyp := h.hyp
  memJ := h.memL
  memL := h.memJ
  notConj := by
    rintro ⟨g, hg⟩
    refine h.notConj ⟨g⁻¹, ?_⟩
    rw [← hg, conjSub_inv_conjSub]
  notComm := fun hc => h.notComm hc.symm

theorem TwinT4Min.false_of_mixed (h : TwinT4Min r G Δ J L) {u v : G}
    (hu : IsUniqueInvolution J u) (hv : IsUniqueInvolution L v) (hinu : TightInO2 u)
    (hinv : ¬ TightInO2 v) : False := by
  have hJ2 := h.hyp.isPGroup_of_inO2 h.memJ hu hinu
  have hJR := TL4.mem_RSet_self h.memJ hJ2
  obtain ⟨P, hPn, hP2, huP⟩ := hinu
  have hLP := h.hyp.le_centralizer_of_not_mem h.memL hv hPn fun hvP => hinv ⟨P, hPn, hP2, hvP⟩
  have hLu : L ≤ Subgroup.centralizer ({u} : Set G) := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      ((Subgroup.mem_centralizer_iff.mp (hLP hy)) u huP).symm
  have hJL : J ≠ L := fun e => h.notConj ⟨1, by rw [conjSub_one, e]⟩
  have hLN : L ≤ Subgroup.normalizer (J : Set G) :=
    h.hyp.le_normalizer_of_le_centralizer h.memJ h.memL hJL hu hLu
  apply h.notComm
  have hle : L ≤ Subgroup.centralizer (J : Set G) := by
    rw [← h.hyp.gen h.memL, Subgroup.closure_le]
    rintro y ⟨hyL, hy2⟩
    obtain ⟨T, hT, hTL, hyT⟩ := exists_mem_RSet_ge (Ω := Δ) h.memL hy2
      (Subgroup.zpowers_le.mpr hyL)
    have hne : J ≠ T := by
      intro hJT
      have huL : u ∈ L := hTL.1 (hJT ▸ hu.mem)
      have huv : u = v := (hv.unique u huL hu.sq).resolve_left hu.ne_one
      exact hinv (huv ▸ ⟨P, hPn, hP2, huP⟩)
    have hc := TL4.commutes_of_le_normalizer h.hyp.hyp hJR hT hJ2 hTL.2.1 hne
      (hTL.1.trans hLN)
    exact Subgroup.mem_centralizer_iff.mpr fun x hx => hc x hx y (hyT (Subgroup.mem_zpowers y))
  exact fun x hx y hy => (Subgroup.mem_centralizer_iff.mp (hle hy)) x hx

end Thm4Twin

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
