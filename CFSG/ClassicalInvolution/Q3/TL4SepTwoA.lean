module

public import CFSG.ClassicalInvolution.Q3.TL4SepAlpha
public import CFSG.ClassicalInvolution.Q3.TL4SepComm

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

variable {r : ℕ} {G : Type} [Group G] [Finite G] {Δ : Set (Subgroup G)}

theorem T4Hyp.isPGroup_of_inO2 (h : T4Hyp r G Δ) {J : Subgroup G} (hJ : J ∈ Δ) {u : G}
    (hu : IsUniqueInvolution J u) (hin : TightInO2 u) : IsPGroup 2 J := by
  obtain ⟨P, hPn, hP2, huP⟩ := hin
  have h1 : oddCoreImg J ≤ ⊥ := (oddCoreImg_le_of_tight hu (h.tight J hJ u hu)).trans
    (TC.oddCoreImg_centralizer_eq_bot h.odd hPn hP2 huP).le
  have h2 : classicalInvolutionOddCore ↥J = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ J.subtype_injective).mp (le_bot_iff.mp h1)
  exact (h.twoGroup J hJ).of_equiv
    ((QuotientGroup.quotientMulEquivOfEq h2).trans QuotientGroup.quotientBot)

theorem mem_RSet_self {J : Subgroup G} (hJ : J ∈ Δ) (hJ2 : IsPGroup 2 J) : J ∈ RSet Δ := by
  obtain ⟨R, hR, hRJ, hJR⟩ := exists_mem_RSet_ge (Ω := Δ) hJ hJ2 le_rfl
  rwa [le_antisymm hRJ.1 hJR] at hR

theorem commutes_of_le_normalizer (hΩ : HypOmegaGen Δ) {A B : Subgroup G} (hA : A ∈ RSet Δ)
    (hB : B ∈ RSet Δ) (hA2 : IsPGroup 2 A) (hB2 : IsPGroup 2 B) (hne : A ≠ B)
    (hBA : B ≤ Subgroup.normalizer (A : Set G)) : Commutes A B := by
  obtain ⟨S, hS⟩ := (IsPGroup.to_sup_of_normal_left' hA2 hB2 hBA).exists_le_sylow
  exact Q3CP.l67Gen G Δ hΩ S A hA B hB (le_sup_left.trans hS) (le_sup_right.trans hS) hne

variable {J L : Subgroup G}

theorem T4Min.symm (h : T4Min r G Δ J L) : T4Min r G Δ L J where
  ih := h.ih
  hyp := h.hyp
  memJ := h.memL
  memL := h.memJ
  notConj := by
    rintro ⟨g, hg⟩
    refine h.notConj ⟨g⁻¹, ?_⟩
    rw [← hg, conjSub_inv_conjSub]
  notComm := fun hc => h.notComm hc.symm

theorem T4Min.false_of_mixed (h : T4Min r G Δ J L) {u v : G} (hu : IsUniqueInvolution J u)
    (hv : IsUniqueInvolution L v) (hinu : TightInO2 u) (hinv : ¬ TightInO2 v) : False := by
  have hJ2 := h.hyp.isPGroup_of_inO2 h.memJ hu hinu
  have hJR := mem_RSet_self h.memJ hJ2
  obtain ⟨P, hPn, hP2, huP⟩ := hinu
  have hLP := h.hyp.le_centralizer_of_not_mem h.memL hv hPn fun hvP => hinv ⟨P, hPn, hP2, hvP⟩
  have hLu : L ≤ Subgroup.centralizer ({u} : Set G) := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      ((Subgroup.mem_centralizer_iff.mp (hLP hy)) u huP).symm
  have hLN : L ≤ Subgroup.normalizer (J : Set G) := hLu.trans (h.hyp.tight J h.memJ u hu)
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
    have hc := commutes_of_le_normalizer h.hyp.hyp hJR hT hJ2 hTL.2.1 hne
      (hTL.1.trans hLN)
    exact Subgroup.mem_centralizer_iff.mpr fun x hx => hc x hx y (hyT (Subgroup.mem_zpowers y))
  exact fun x hx y hy => (Subgroup.mem_centralizer_iff.mp (hle hy)) x hx

end CFSG.ClassicalInvolution.Q3.TL4
