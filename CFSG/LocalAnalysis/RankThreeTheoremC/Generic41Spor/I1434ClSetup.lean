module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434General
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LayerBridge

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434.Cl

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.RankThreeCoreUniqueness.Helpers (primeComplementCore)

section Setup

variable {K : Type} [Group K] [Finite K]

theorem card_center_quotient_eq_sixty {J : Subgroup K} (hq : CFSG.Open.IsQuasisimple ↥J)
    (h : Nonempty (↥J ⧸ primeComplementCore (G := ↥J) 5 ≃* alternatingGroup (Fin 5))) :
    Nat.card (↥J ⧸ Subgroup.center ↥J) = 60 := by
  obtain ⟨e⟩ := h
  have h60 : Nat.card (↥J ⧸ primeComplementCore (G := ↥J) 5) = 60 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  have h5 : 5 ∣ Nat.card J := by
    have hmul := (primeComplementCore (G := ↥J) 5).card_eq_card_quotient_mul_card_subgroup
    rw [h60] at hmul
    exact ⟨12 * Nat.card (primeComplementCore (G := ↥J) 5), by rw [hmul]; ring⟩
  haveI : (primeComplementCore (G := ↥J) 5).Normal :=
    CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore_normal 5
  have hcen : primeComplementCore (G := ↥J) 5 ≤ Subgroup.center ↥J :=
    CFSG.ComponentClassification.Quasisimple.normal_le_center_of_ne_top hq _
      (primeComplementCore_ne_top h5)
  let π : (↥J ⧸ primeComplementCore (G := ↥J) 5) →* (↥J ⧸ Subgroup.center ↥J) :=
    QuotientGroup.map _ _ (MonoidHom.id ↥J) hcen
  have hπ : Function.Surjective π := by
    intro y
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨QuotientGroup.mk a, rfl⟩
  haveI : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup_five
  haveI : IsSimpleGroup (↥J ⧸ primeComplementCore (G := ↥J) 5) := e.isSimpleGroup
  rcases (MonoidHom.normal_ker π).eq_bot_or_eq_top with hk | hk
  · have hinj : Function.Injective π := (MonoidHom.ker_eq_bot_iff π).1 hk
    rw [← Nat.card_congr (Equiv.ofBijective π ⟨hinj, hπ⟩)]
    exact h60
  · exfalso
    haveI := hq.2.toNontrivial
    obtain ⟨y, hy⟩ := exists_ne (1 : ↥J ⧸ Subgroup.center ↥J)
    obtain ⟨z, rfl⟩ := hπ y
    exact hy ((MonoidHom.mem_ker.1 (hk ▸ Subgroup.mem_top z)))

theorem fixSubgroup_congr {T : Type} [Group T] (φ : K ≃* T) (β : MulAut K) :
    fixSubgroup (MulAut.congr φ β) = (fixSubgroup β).map (φ : K →* T) := by
  ext y
  rw [mem_fixSubgroup]
  refine Iff.trans ?_ (Subgroup.mem_map_equiv (f := φ)).symm
  rw [mem_fixSubgroup]
  show φ (β (φ.symm y)) = y ↔ β (φ.symm y) = φ.symm y
  exact φ.eq_symm_apply.symm

theorem congr_conj_eq {T : Type} [Group T] (φ : K ≃* T) (x : K) :
    MulAut.congr φ (MulAut.conj x) = MulAut.conj (φ x) := by
  ext y
  obtain ⟨z, rfl⟩ := φ.surjective y
  simp [MulAut.congr_apply, MulAut.conj_apply]

theorem isComponentOf_map_of_five {T : Type} [Group T] (φ : K ≃* T) {x : K}
    (hlayer : PerfectInLayer (MulAut.congr φ (MulAut.conj x))) {J : Subgroup K}
    (hJ : GLAPComponent 5 (Subgroup.centralizer ({x} : Set K)) J) :
    IsComponentOf (J.map (φ : K →* T)) (fixSubgroup (MulAut.congr φ (MulAut.conj x))) ∧
      CFSG.Open.IsQuasisimple ↥J := by
  have hK : PerfectInLayer (MulAut.conj x) :=
    LieSemisimple.perfectInLayer_of_congr φ _ hlayer
  have hJ' : GLAPComponent 5 (fixSubgroup (MulAut.conj x)) J := by
    rw [b3Lie_fixSubgroup_conj]
    exact hJ
  have hle : J ≤ GLALayer (fixSubgroup (MulAut.conj x)) :=
    hK J hJ'.1 (CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hJ')
  obtain ⟨hc, -⟩ := glaPComponent_isComponent_of_le_layer hJ' hle
  refine ⟨?_, hc.2.2⟩
  rw [fixSubgroup_congr]
  exact CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map φ hc

theorem card_quotient_center_map {T : Type} [Group T] (φ : K ≃* T) (J : Subgroup K) :
    Nat.card (↥(J.map (φ : K →* T)) ⧸ Subgroup.center ↥(J.map (φ : K →* T))) =
      Nat.card (↥J ⧸ Subgroup.center ↥J) := by
  let e : ↥J ≃* ↥(J.map (φ : K →* T)) := J.equivMapOfInjective (φ : K →* T) φ.injective
  exact (Nat.card_congr (QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)).toEquiv).symm

theorem five_component_data {T : Type} [Group T] (φ : K ≃* T) {x : K}
    (hlayer : PerfectInLayer (MulAut.congr φ (MulAut.conj x))) {J : Subgroup K}
    (hJ : GLAPComponent 5 (Subgroup.centralizer ({x} : Set K)) J)
    (hq : Nonempty (↥J ⧸ primeComplementCore (G := ↥J) 5 ≃* alternatingGroup (Fin 5))) :
    IsComponentOf (J.map (φ : K →* T)) (fixSubgroup (MulAut.congr φ (MulAut.conj x))) ∧
      Nat.card (↥(J.map (φ : K →* T)) ⧸ Subgroup.center ↥(J.map (φ : K →* T))) = 60 := by
  obtain ⟨hc, hqs⟩ := isComponentOf_map_of_five φ hlayer hJ
  exact ⟨hc, (card_quotient_center_map φ J).trans (card_center_quotient_eq_sixty hqs hq)⟩

end Setup

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434.Cl
