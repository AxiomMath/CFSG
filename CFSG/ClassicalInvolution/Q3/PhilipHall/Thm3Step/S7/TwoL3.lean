module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7.TwoE3a
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5GL2
import CFSG.ClassicalInvolution.Q3.TA3FrameLayer
import CFSG.ClassicalInvolution.Q3.TA3LeafQ5U3Frame

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7Ident

open CFSG CFSG.Open CFSG.ClassicalInvolution Matrix
open CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups

theorem centComponent_of_frame {X : Type} [Group X] {t : X} (ht : orderOf t = 2)
    {F : Type} [Field F] [Finite F] {H : Subgroup (GL (Fin 2) F)} {π : H →* X}
    (hrange : π.range = Subgroup.centralizer ({t} : Set X)) (hk : TA3.Q5GL2.CubeKer π)
    (hcs : TA3.Q5GL2.SLCentScalar H) {F₀ : Type} [Field F₀] [Finite F₀] (h4 : 4 ≤ Nat.card F₀)
    (eJ : TA3.Q5GL2.slPart H ≃* SL(2, F₀)) {hm : (-1 : GL (Fin 2) F) ∈ H}
    (hneg : π ⟨-1, hm⟩ = t) :
    CFSG.Open.IsQuasisimple ↥⁅Subgroup.centralizer ({t} : Set X),
        Subgroup.centralizer ({t} : Set X)⁆ ∧
      Even (Nat.card ↥⁅Subgroup.centralizer ({t} : Set X),
        Subgroup.centralizer ({t} : Set X)⁆) ∧
      IsCyclic ↥(Subgroup.centralizer ({t} : Set X) ⊓
        Subgroup.centralizer ((⁅Subgroup.centralizer ({t} : Set X),
          Subgroup.centralizer ({t} : Set X)⁆ : Subgroup X) : Set X)) := by
  set C := Subgroup.centralizer ({t} : Set X) with hC
  set J : Subgroup X := (TA3.Q5GL2.slPart H).map π with hJ
  have hJr : J = (π.comp (TA3.Q5GL2.slPart H).subtype).range := by
    rw [hJ, MonoidHom.range_comp, Subgroup.range_subtype]
  let eJ' : ↥J ≃* SL(2, F₀) := (MulEquiv.subgroupCongr hJr).trans
    ((MonoidHom.ofInjective (TA3.Q5GL2.injective_slPart hk)).symm.trans eJ)
  have hJq : CFSG.Open.IsQuasisimple ↥J := TA3.Frame.isQuasisimple_of_equiv_sl2 h4 eJ'
  have hJC : J ≤ C := by
    rw [← hrange]
    exact Subgroup.map_le_range π _
  have hCC : ⁅C, C⁆ = J := by
    refine le_antisymm ?_ ?_
    · have := TA3.Q5GL2.commutator_range_le π
      rwa [hrange] at this
    · have hJJ : ⁅J, J⁆ = J := by
        rw [← Subgroup.map_subtype_commutator, hJq.1, ← MonoidHom.range_eq_map,
          Subgroup.range_subtype]
      calc J = ⁅J, J⁆ := hJJ.symm
        _ ≤ ⁅C, C⁆ := Subgroup.commutator_mono hJC hJC
  rw [hCC]
  refine ⟨hJq, ?_, ?_⟩
  ·
    have hmJ : (⟨-1, hm⟩ : H) ∈ TA3.Q5GL2.slPart H := by
      rw [TA3.Q5GL2.mem_slPart]
      ext
      simp [Matrix.det_fin_two]
    have htJ : t ∈ J := ⟨_, hmJ, hneg⟩
    have h2 : orderOf (⟨t, htJ⟩ : ↥J) = 2 := by
      rw [Subgroup.orderOf_mk]
      exact ht
    exact even_iff_two_dvd.mpr (h2 ▸ orderOf_dvd_natCard _)
  ·
    set Z : Subgroup H := (Subgroup.center (GL (Fin 2) F)).comap H.subtype with hZ
    haveI hcen : IsCyclic ↥(Subgroup.center (GL (Fin 2) F)) := by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact isCyclic_of_surjective (GeneralLinearGroup.scalar (Fin 2)).rangeRestrict
        (MonoidHom.rangeRestrict_surjective _)
    haveI : IsCyclic ↥(Z.map H.subtype) :=
      Subgroup.isCyclic_of_le (Subgroup.map_comap_le _ _)
    haveI : IsCyclic ↥Z :=
      isCyclic_of_surjective (Z.equivMapOfInjective H.subtype H.subtype_injective).symm
        (MulEquiv.surjective _)
    haveI : IsCyclic ↥(Z.map π) :=
      isCyclic_of_surjective (π.subgroupMap Z) (π.subgroupMap_surjective Z)
    refine Subgroup.isCyclic_of_le (H' := Z.map π) ?_
    rintro x ⟨hxC, hxJ⟩
    have hx : x ∈ π.range := hrange ▸ hxC
    obtain ⟨A, rfl⟩ := hx
    obtain ⟨c, hc⟩ := TA3.Q5GL2.exists_scalar_of_commute hk hcs (A := A) fun B hB =>
      (Subgroup.mem_centralizer_iff.mp hxJ (π B) ⟨B, hB, rfl⟩).symm
    refine ⟨A, ?_, rfl⟩
    show (A : GL (Fin 2) F) ∈ Subgroup.center (GL (Fin 2) F)
    rw [hc, Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨c, rfl⟩

theorem l3CentComponent : L3CentComponent := by
  intro X _ _ p f hp hp2 h3 hl z hz
  have hf : 1 ≤ f := hl.elim (fun h => h.admissible.2.1) (fun h => h.admissible.2.1)
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have h5 : 5 ≤ p ^ f := by
    rcases Nat.eq_or_lt_of_le hf with rfl | hf2
    · have hp4 : p ≠ 4 := by
        rintro rfl
        norm_num at hp
      simp only [pow_one] at h3 ⊢
      omega
    · calc 5 ≤ 3 ^ 2 := by norm_num
        _ ≤ p ^ 2 := Nat.pow_le_pow_left hp3 2
        _ ≤ p ^ f := Nat.pow_le_pow_right (by omega) hf2
  rcases hl with hl | hl
  · obtain ⟨-, K, _, _, hK, ⟨e₀⟩⟩ := hl.statedClassicalModel (by decide)
    let e : ↥(⊤ : Subgroup X) ≃* LinearFlag.projectiveSL 3 K :=
      Subgroup.topEquiv.trans ((e₀.trans
        (Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 K).symm).trans
          (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 K))
    have hoddK : Odd (Nat.card K) := hK ▸ (hp.odd_of_ne_two hp2).pow
    obtain ⟨Q, π, hrange, hk, hneg, hπ⟩ := TA3.Q5L3.exists_frame hoddK e (Subgroup.mem_top z) hz
    rw [top_inf_eq] at hrange
    exact centComponent_of_frame hz hrange hk TA3.Q5L3.slCentScalar_top (by rw [hK]; omega)
      TA3.Q5L3.slPartTopEquiv hneg
  · obtain ⟨⟨hℓ, hm1, -, -⟩, K, _, _, hK, ⟨e₀⟩⟩ := hl.statedClassicalModel (by decide)
    have h : UnitaryFieldData p f K := ⟨hℓ, hm1, by rw [hK, ← pow_mul, mul_comm]⟩
    haveI : Fact p.Prime := ⟨hp⟩
    haveI : CharP K p := h.charP
    obtain ⟨π, hrange, hk, hneg⟩ :=
      TA3.Q5U3.exists_frame h hp2 (Subgroup.topEquiv.trans e₀) (Subgroup.mem_top z) hz
    rw [top_inf_eq] at hrange
    obtain ⟨eJ⟩ := TA3.Q5U3.nonempty_slPart_equiv h
    have hq := LieType.Steinberg.card_fixedSubfield h.card_eq_sq
    exact centComponent_of_frame hz hrange hk (TA3.Q5U3.slCentScalar_GU2 h) (by rw [hq]; omega)
      eJ hneg

end CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7Ident
