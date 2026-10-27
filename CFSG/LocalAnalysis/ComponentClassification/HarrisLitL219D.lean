module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitL219C
import CFSG.GroupTheory.PCore.PrimeSetCore
public import CFSG.GH74.GLS.TwoThin.Pumpup

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.GH74.GLS.TwoThin CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

namespace L219

variable {G : Type} [Group G] [Finite G] {z : G}

omit [Finite G] in
theorem map_conj_eq_of_mem_normalizer {X : Subgroup G} {g : G}
    (hg : g ∈ normalizer (X : Set G)) : X.map (MulAut.conj g).toMonoidHom = X :=
  mem_normalizer_iff_map_conj_eq.mp hg

theorem part_c (hz : orderOf z = 2) {J : Subgroup G}
    (hJ : IsTwoComponentIn J (centralizer {z})) :
    ∃ K : Subgroup G, IsTwoComponent K ∧
      ((K.map (MulAut.conj z).toMonoidHom = K ∧ IsTwoComponentIn J (K ⊓ centralizer {z})) ∨
        (K.map (MulAut.conj z).toMonoidHom ≠ K ∧
          J = centralizerResidual (K ⊔ K.map (MulAut.conj z).toMonoidHom) z)) ∧
      ⁅J, K ⊔ K.map (MulAut.conj z).toMonoidHom⁆ = K ⊔ K.map (MulAut.conj z).toMonoidHom ∧
      ⁅J, twoLayer G⁆ = K ⊔ K.map (MulAut.conj z).toMonoidHom ∧
      (⨆ g : ↥(twoLayer G), J.map (MulAut.conj (g : G)).toMonoidHom) =
        K ⊔ K.map (MulAut.conj z).toMonoidHom := by
  obtain ⟨hJH, hJ2⟩ := isTwoComponentIn_iff_twoComponents.mp hJ
  have hJperf : Group.IsPerfect ↥J := hJ.2.2.1
  have hJJ : ⁅J, J⁆ = J := Subgroup.isPerfect_iff.mp hJperf
  obtain ⟨hJE, -, Lb, hLb, hcases, -, -, hiff⟩ := pumpupY_structure hz hJH hJ2
  have hinv : (barMk G z)⁻¹ = barMk G z := inv_eq_self_of_orderOf_eq_two (orderOf_barMk hz)
  have hLb2 : TwoComponents.IsTwoComponent Lb :=
    (isTwoComponent_iff_twoComponents Lb).mp
      ((isTwoComponent_iff_isComponent (pPrimeCore_quotient_eq_bot Nat.prime_two) Lb).mpr hLb)
  obtain ⟨K, hK, hKLb⟩ := OddKernelTwoComponents.exists_lift (barMk G) barMk_surjective
    odd_card_ker_barMk Lb hLb2
  have hKz := twoComponent_map_conj hK z
  set Kz := K.map (MulAut.conj z).toMonoidHom with hKzdef
  have hKzLb : Kz.map (barMk G) = conjSub (barMk G z)⁻¹ Lb := by
    rw [hKzdef, map_barMk_map_conj, hKLb, hinv]
  set D := K ⊔ Kz with hDdef
  set E := TwoLayer.subgroup G with hEdef
  have hDmap : D.map (barMk G) = Lb ⊔ conjSub (barMk G z)⁻¹ Lb := by
    rw [hDdef, Subgroup.map_sup, hKLb, hKzLb]
  have hKP : K ≤ pumpupY J := (hiff K hK).mpr (Or.inl hKLb)
  have hKzP : Kz ≤ pumpupY J := (hiff Kz hKz).mpr (Or.inr hKzLb)
  have hOD : pPrimeCore 2 G ≤ normalizer (D : Set G) :=
    le_normalizer_sup (pPrimeCore_le_normalizer hK) (pPrimeCore_le_normalizer hKz)
  have hED : E ≤ normalizer (D : Set G) :=
    le_normalizer_sup (twoLayer_le_normalizer hK) (twoLayer_le_normalizer hKz)
  have hJD : J ≤ D := by
    refine le_of_map_barMk_le hJperf hOD ?_
    rw [hDmap]
    rcases hcases with ⟨-, h⟩ | ⟨-, hAB, h⟩
    · exact h.trans le_sup_left
    · refine h.trans ?_
      rintro _ ⟨x, rfl⟩
      exact swapDiag_mem_sup hAB x
  have hPD : pumpupY J = D := by
    refine le_antisymm (pumpupY_le_of_forall fun g hg => ?_) (sup_le hKP hKzP)
    have := map_mono (f := (MulAut.conj g).toMonoidHom) hJD
    rwa [map_conj_eq_of_mem_normalizer (hED hg)] at this
  have hiSup : (⨆ g : ↥E, J.map (MulAut.conj (g : G)).toMonoidHom) = D := by
    rw [← hPD]
    exact le_antisymm (iSup_le fun g => le_pumpupY J g.2) (pumpupY_le_of_forall fun g hg =>
      le_iSup (fun g : ↥E => J.map (MulAut.conj (g : G)).toMonoidHom) ⟨g, hg⟩)
  have hDE : D ≤ E := sup_le (le_sSup hK) (le_sSup hKz)
  have hJle : J ≤ ⁅J, E⁆ := calc
    J = ⁅J, J⁆ := hJJ.symm
    _ ≤ ⁅J, E⁆ := commutator_mono le_rfl hJE
  have hJEc : ⁅J, E⁆ = D := by
    refine le_antisymm ?_ ?_
    · rw [commutator_le]
      intro j hj e he
      have h1 : e * j⁻¹ * e⁻¹ ∈ D := (mem_normalizer_iff.mp (hED he) _).mp (inv_mem (hJD hj))
      have h2 : j * e * j⁻¹ * e⁻¹ = j * (e * j⁻¹ * e⁻¹) := by group
      rw [commutatorElement_def, h2]
      exact mul_mem (hJD hj) h1
    · rw [← hPD]
      refine pumpupY_le_of_forall fun g hg => ?_
      rintro _ ⟨j, hj, rfl⟩
      have h1 : ⁅g, j⁆ ∈ ⁅J, E⁆ := by
        rw [commutator_comm]
        exact commutator_mem_commutator hg hj
      have h2 : (MulAut.conj g).toMonoidHom j = ⁅g, j⁆ * j := by
        rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, commutatorElement_def]
        group
      rw [h2]
      exact mul_mem h1 (hJle hj)
  have hJDc : ⁅J, D⁆ = D := by
    refine le_antisymm ((commutator_mono le_rfl hDE).trans hJEc.le) ?_
    have hKperf : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.mp ⟨TwoComponents.perfect hK⟩
    have hKzperf : ⁅Kz, Kz⁆ = Kz := Subgroup.isPerfect_iff.mp ⟨TwoComponents.perfect hKz⟩
    have hDperf : Group.IsPerfect ↥D := by
      rw [Subgroup.isPerfect_iff]
      refine le_antisymm (Subgroup.commutator_le_self D) (sup_le ?_ ?_)
      · calc K = ⁅K, K⁆ := hKperf.symm
          _ ≤ ⁅D, D⁆ := commutator_mono le_sup_left le_sup_left
      · calc Kz = ⁅Kz, Kz⁆ := hKzperf.symm
          _ ≤ ⁅D, D⁆ := commutator_mono le_sup_right le_sup_right
    refine le_of_map_barMk_le_of_le_normalizer hDperf (le_normalizer_commutator J D) ?_
    set Db := Lb ⊔ conjSub (barMk G z)⁻¹ Lb with hDbdef
    have hEb : E.map (barMk G) ≤ Db ⊔ centralizer (Db : Set (barQ G)) := by
      refine map_twoLayer_le_layer.trans ?_
      simp only [CFSG.layer.eq_sSup]
      refine sSup_le fun Q hQ => ?_
      rcases CFSG.LocalCores.distinct_components_commute hQ hLb with h | h
      · rw [h]
        exact le_sup_left.trans le_sup_left
      rcases CFSG.LocalCores.distinct_components_commute hQ (isComponent_conjSub hLb _) with
        h' | h'
      · rw [h']
        exact le_sup_right.trans le_sup_left
      have hQ1 : Lb ≤ centralizer (Q : Set (barQ G)) :=
        le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp h)
      have hQ2 : conjSub (barMk G z)⁻¹ Lb ≤ centralizer (Q : Set (barQ G)) :=
        le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp h')
      exact le_sup_of_le_right (le_centralizer_iff.mpr (sup_le hQ1 hQ2))
    have hDbN : Db ≤ normalizer ((centralizer (Db : Set (barQ G)) : Subgroup (barQ G)) :
        Set (barQ G)) :=
      (le_centralizer_iff.mp le_rfl).trans (centralizer_le_normalizer _)
    have hcomm : ⁅J.map (barMk G), E.map (barMk G)⁆ ≤ ⁅J.map (barMk G), Db⁆ := by
      rw [commutator_le]
      intro j hj e he
      have he' := hEb he
      rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right _ _ hDbN] at he'
      obtain ⟨d, hd, c, hc, rfl⟩ := he'
      have hjD : j ∈ Db := hDmap ▸ map_mono hJD hj
      have hcj : Commute c j := (mem_centralizer_iff.mp hc j hjD).symm
      have hcj' : c * j⁻¹ = j⁻¹ * c := hcj.inv_right.eq
      have : ⁅j, d * c⁆ = ⁅j, d⁆ := by
        rw [commutatorElement_def, commutatorElement_def]
        calc j * (d * c) * j⁻¹ * (d * c)⁻¹ = j * d * (c * j⁻¹) * c⁻¹ * d⁻¹ := by group
          _ = j * d * (j⁻¹ * c) * c⁻¹ * d⁻¹ := by rw [hcj']
          _ = j * d * j⁻¹ * d⁻¹ := by group
      rw [this]
      exact commutator_mem_commutator hj hd
    calc D.map (barMk G) = ⁅J, E⁆.map (barMk G) := by rw [hJEc]
      _ = ⁅J.map (barMk G), E.map (barMk G)⁆ := map_commutator _ _ _
      _ ≤ ⁅J.map (barMk G), Db⁆ := hcomm
      _ = ⁅J, D⁆.map (barMk G) := by rw [map_commutator, hDmap]
  have hcase : (Kz = K ∧ IsTwoComponentIn J (K ⊓ centralizer {z})) ∨
      (Kz ≠ K ∧ J = centralizerResidual D z) := by
    rcases hcases with ⟨hfix, hJL⟩ | ⟨hmov, -, -⟩
    · have hKzK : Kz = K := OddKernelTwoComponents.lift_unique (barMk G) barMk_surjective
        odd_card_ker_barMk _ _ hKz hK (by rw [hKzLb, hfix, hKLb])
      have hJK : J ≤ K := le_of_map_barMk_le hJperf (pPrimeCore_le_normalizer hK)
        (by rw [hKLb]; exact hJL)
      exact Or.inl ⟨hKzK, le_inf hJK hJH, isSubnormal_subgroupOf_of_le inf_le_right hJ.2.1,
        hJ.2.2⟩
    · have hKzK : Kz ≠ K := fun h => hmov (by rw [← hKzLb, h, hKLb])
      refine Or.inr ⟨hKzK, ?_⟩
      have hR := (part_b1 hz hK hKzK).1
      have hJR : J ≤ centralizerResidual D z := le_perfectResidual_map (le_inf hJD hJH) hJperf
      obtain ⟨hRH, hR2⟩ := isTwoComponentIn_iff_twoComponents.mp hR
      have h := TwoComponentSubnormal.eq_of_le _ _ hJ2 hR2 (fun x hx => hJR hx)
      rwa [subgroupOf_inj, inf_of_le_left hJH, inf_of_le_left hRH] at h
  refine ⟨K, (isTwoComponent_iff_twoComponents K).mpr hK, hcase, hJDc, ?_, ?_⟩
  · rw [twoLayer_eq]
    exact hJEc
  · rw [twoLayer_eq]
    exact hiSup

end L219

theorem harris82Lemma219Input_holds : Harris82Lemma219Input := by
  intro G _ _ z hz
  refine ⟨fun L hL => ⟨fun _ J hJ => L219.part_a hL.1 hJ, fun hLz => ?_⟩,
    fun J hJ => L219.part_c hz hJ⟩
  have hL' := (L219.isTwoComponent_iff_twoComponents L).mp hL
  exact ⟨(L219.part_b1 hz hL' hLz).1, L219.part_b2 hz hL' hLz, L219.part_b3 hz hL' hLz⟩

end CFSG.ComponentClassification.HarrisLit
