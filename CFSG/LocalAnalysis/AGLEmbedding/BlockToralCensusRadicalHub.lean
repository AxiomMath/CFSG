module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutRadical
public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.AGLEmbedding.ToralCensus

open CFSG.Open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.LieType.BorelTits CFSG.AGLEmbedding.ParabHub
  CFSG.AGLEmbedding.ParabPrime CFSG.AGLEmbedding.LieOut

@[expose] def RadicalSelfNormOver (X : Type*) [Group X] : Prop :=
  ∀ (T : Sylow 2 X) (J : Subgroup X), Subgroup.normalizer ((T : Subgroup X) : Set X) ≤ J →
    Subgroup.normalizer (pCoreOf 2 J : Set X) ≤ J

theorem RadicalSelfNormOver.of_mulEquiv {X X' : Type*} [Group X] [Group X'] [Finite X]
    (e : X ≃* X') (h : RadicalSelfNormOver X) : RadicalSelfNormOver X' := by
  have : Finite X' := Finite.of_equiv X e.toEquiv
  intro T' J' hNJ'
  have hmap : ∀ A B : Subgroup X', A.map e.symm.toMonoidHom ≤ B.map e.symm.toMonoidHom →
      A ≤ B := fun A B hAB => by
    have := Subgroup.map_mono (f := e.toMonoidHom) hAB
    simpa [Subgroup.map_map] using this
  refine hmap _ _ ?_
  set T : Sylow 2 X := Sylow.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective T'
  have hT : (T : Subgroup X) = (T' : Subgroup X').map e.symm.toMonoidHom :=
    Sylow.coe_mapSurjective _ _
  have hN := h T (J'.map e.symm.toMonoidHom) (by
    rw [hT, ← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hNJ')
  rwa [pCoreOf_map_mulEquiv, ← Subgroup.map_equiv_normalizer_eq] at hN

section Hub

variable {K Y : Type*} [Group K] [Group Y] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K} {π : K →* Y} {M : ℕ}

theorem normalizer_pCoreOf_le_of_borelQuotient (h : BorelQuotient D n H π M) {J : Subgroup Y}
    (hBJ : (borel D H).map π ≤ J) : Subgroup.normalizer (pCoreOf 2 J : Set Y) ≤ J := by
  set N : Subgroup Y := Subgroup.normalizer (pCoreOf 2 J : Set Y) with hN
  have hBN : (borel D H).map π ≤ N := hBJ.trans (le_normalizer_pCoreOf 2 J)
  have hBA : borel D H ≤ J.comap π := fun b hb => hBJ ⟨b, hb, rfl⟩
  have hBNA : borel D H ≤ N.comap π := fun b hb => hBN ⟨b, hb, rfl⟩
  rw [eq_map_borel_sup_of_le h.ct h.extras h.surj hBN]
  refine sup_le hBJ (iSup₂_le fun j hj => Subgroup.map_le_iff_le_comap.2 ?_)
  by_cases hjJ : j ∈ negIndices D (J.comap π)
  · exact rankOne_le_of_mem_negIndices hBA hjJ
  have hα : (Pi.single j 1 : Fin D.rank → ℤ) ∈ D.roots :=
    (RootSystem.ofCartan D.isFiniteType D.divisible).single_mem j
  refine sup_le ((rootGroup_le_borel hα (ht_single_pos j)).trans hBA) ?_
  have hR2 : IsPGroup 2 ((radical D j).map π) :=
    (isPGroup_iSup_posSet h.extras h.pGroup (coordHom D j) : IsPGroup 2 (radical D j)).map π
  have hRJ : (radical D j).map π ≤ J :=
    (Subgroup.map_mono ((radical_le_posUnipotent j).trans posUnipotent_le_borel)).trans hBJ
  have hJR : J ≤ Subgroup.normalizer ((radical D j).map π : Set Y) := by
    calc J = (borel D H).map π ⊔ ⨆ i ∈ negIndices D (J.comap π), (rankOne D.rootGroup i).map π :=
          eq_map_borel_sup_of_le h.ct h.extras h.surj hBJ
      _ ≤ _ := by
          refine sup_le ?_ (iSup₂_le fun i hi => ?_)
          · exact (Subgroup.map_mono (borel_le_normalizer_radical h.ct h.extras j)).trans
              (Subgroup.le_normalizer_map π)
          · have hij : i ≠ j := fun e => hjJ (e ▸ hi)
            exact (Subgroup.map_mono (rankOne_le_normalizer_radical h.extras hij)).trans
              (Subgroup.le_normalizer_map π)
  have hRO : (radical D j).map π ≤ pCoreOf 2 J := le_pCoreOf_of_le_normalizer 2 hRJ hJR hR2
  have hnN : π (n j) ∈ N := (rankOne_le_of_mem_negIndices hBNA hj) (h.ct.n_mem j)
  intro y hy
  have hy' : y ∈ (D.rootGroup (Pi.single j 1)).map (MulAut.conj (n j)).toMonoidHom := by
    rw [actsAs_n h.ct j _ hα, weylAction_simple_single]
    exact hy
  obtain ⟨x, hx, rfl⟩ := hy'
  have hxO : π x ∈ pCoreOf 2 J := hRO ⟨x, rootGroup_le_radical hα (by simp) hx, rfl⟩
  have hc : π (n j * x * (n j)⁻¹) ∈ pCoreOf 2 J := by
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.1 hnN _).1 hxO
  exact pCoreOf_le 2 J hc

theorem radicalSelfNormOver_of_borelQuotient [Finite K] [Finite Y]
    (h : BorelQuotient D n H π M) :
    RadicalSelfNormOver Y := by
  intro T J hNJ
  obtain ⟨π', hπ', hker, hT⟩ := h.exists_conj_eq T
  have hQ : BorelQuotient D n H π' M :=
    { ct := h.ct, extras := h.extras, pGroup := h.pGroup, surj := hπ', odd := h.odd
      torus_pow := h.torus_pow
      ker_central := fun z hz => h.ker_central z (hker ▸ hz)
      ker_pow := fun z hz => h.ker_pow z (hker ▸ hz) }
  have hNπ := hQ.normalizer_map_posUnipotent
  rw [← hT] at hNπ
  exact normalizer_pCoreOf_le_of_borelQuotient hQ (hNπ ▸ hNJ)

end Hub

end CFSG.AGLEmbedding.ToralCensus
