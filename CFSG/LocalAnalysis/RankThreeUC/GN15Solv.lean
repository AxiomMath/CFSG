module

public import CFSG.LocalAnalysis.RankThreeUC.GN15SolvBase
public import CFSG.LocalAnalysis.RankThreeUC.GN15DQ

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.Quasithin CFSG.QuasithinUnique
  CFSG.Open
open scoped commutatorElement
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

@[expose] def JOutCentral : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (T : Subgroup X), GNSetting X T → JOutCentralAt T

variable {X : Type} [Group X] [Finite X] {T T₁ T₂ : Subgroup X}

@[expose] noncomputable def gnWPre (T : Subgroup X) : Subgroup X := gnWComp T ⊔ (gnQPre T ⊔ gnDPre T)

theorem gnQPre_sup_gnDPre_normal (hX : GNSetting X T) : (gnQPre T ⊔ gnDPre T).Normal := by
  have := gnQPre_normal hX
  have := gnDPre_normal hX
  infer_instance

theorem gnWPre_normal (hX : GNSetting X T) : (gnWPre T).Normal := by
  have := gnWComp_normal (T := T)
  have := gnQPre_sup_gnDPre_normal hX
  exact Subgroup.sup_normal _ _

omit [Finite X] in
theorem gnQPre_sup_gnDPre_le_gnWPre : gnQPre T ⊔ gnDPre T ≤ gnWPre T := le_sup_right

theorem thompsonJ_le_gnWPre (hX : GNSetting X T) : thompsonJ T ≤ gnWPre T :=
  (thompsonJ_le_gnWComp hX).trans le_sup_left

theorem commutator_mem_gnQPre_sup_gnDPre (hJ : JOutCentralAt T) (hX : GNSetting X T) {w j : X}
    (hw : w ∈ gnWComp T) (hj : j ∈ thompsonJ T) : ⁅w, j⁆ ∈ gnQPre T ⊔ gnDPre T := by
  apply mem_gnQPre_sup_gnDPre_of_mem_sup
  set S : Set (Subgroup (X ⧸ gnC T)) :=
    {L | IsComponentOf L ⊤ ∧ ⁅L, gnImg T (thompsonJ T)⁆ ≠ ⊥} with hS
  have hfin : S.Finite := Set.toFinite S
  have hD : (⨆ B ∈ hfin.toFinset, B : Subgroup (X ⧸ gnC T)) = gnDStar T :=
    le_antisymm
      (iSup₂_le fun B hB => le_iSup₂_of_le B (hfin.mem_toFinset.1 hB) le_rfl)
      (iSup₂_le fun B hB => le_iSup₂_of_le B (hfin.mem_toFinset.2 hB) le_rfl)
  rw [map_commutatorElement, ← hD]
  refine mem_sup_centralizer_biSup hfin.toFinset ?_ ?_
  · intro B hB B' hB' hne
    have hB1 := hfin.mem_toFinset.1 hB
    have hB2 := hfin.mem_toFinset.1 hB'
    rcases CFSG.LocalCores.distinct_components_commute ((CFSG.isComponent_iff_open B).2 hB1.1)
      ((CFSG.isComponent_iff_open B').2 hB2.1) with h | h
    · exact absurd h hne
    · exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 h
  · intro B hB
    have hB1 := hfin.mem_toFinset.1 hB
    have hwB := (mem_gnWComp_iff.1 hw) B hB1.1
    have hjB := (mem_gnWComp_iff.1 (thompsonJ_le_gnWComp hX hj)) B hB1.1
    by_cases hc : IsMulCommutative (Outer ↥B)
    · exact commutator_mem_sup_centralizer_of_isMulCommutative_outer hc hwB hjB
    · exact hJ B hB1.1 hB1.2 hc (toStar T w) hwB (toStar T j) ⟨j, hj, rfl⟩

theorem gnWPre_commutator_le (hJ : JOutCentralAt T) (hX : GNSetting X T) :
    ⁅gnWPre T, thompsonJ T⁆ ≤ gnQPre T ⊔ gnDPre T := by
  have hQD := gnQPre_sup_gnDPre_normal hX
  rw [Subgroup.commutator_le]
  intro w hw j hj
  obtain ⟨w₀, hw₀, e, he, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hw
  have key : ⁅w₀ * e, j⁆ = w₀ * ⁅e, j⁆ * w₀⁻¹ * ⁅w₀, j⁆ := by
    simp only [commutatorElement_def]
    group
  rw [key]
  have h1 : ⁅e, j⁆ ∈ gnQPre T ⊔ gnDPre T := by
    rw [commutatorElement_def]
    have : j * e⁻¹ * j⁻¹ ∈ gnQPre T ⊔ gnDPre T := hQD.conj_mem _ (inv_mem he) j
    simpa [mul_assoc] using mul_mem he this
  exact mul_mem (hQD.conj_mem _ h1 w₀) (commutator_mem_gnQPre_sup_gnDPre hJ hX hw₀ hj)

theorem gnWPre_le_sup_normalizer (hX : GNSetting X T)
    (hcomm : ⁅gnWPre T, thompsonJ T⁆ ≤ gnQPre T ⊔ gnDPre T) :
    gnWPre T ≤ (gnQPre T ⊔ gnDPre T) ⊔ Subgroup.normalizer (thompsonJ T : Set X) := by
  intro a ha
  obtain ⟨b, hb, n, hn, rfl⟩ := eq_mul_normalizer_thompsonJ_of_commutator_le hX.sylow
    (gnQPre_sup_gnDPre_normal hX) gnQPre_sup_gnDPre_le_gnWPre hcomm a ha
  exact Subgroup.mul_mem_sup hb hn.2

theorem gnAbsorbs_gnWPre (hX : GNSetting X T) (hP : IsC118Pair T T₁ T₂)
    (hH : GNAbsorbs T T₁ T₂ (gnHPre T))
    (hcomm : ⁅gnWPre T, thompsonJ T⁆ ≤ gnQPre T ⊔ gnDPre T) :
    GNAbsorbs T T₁ T₂ (gnWPre T) := by
  obtain ⟨-, h1, -, -, h2, h2c, -⟩ := id hP
  exact GNAbsorbs.of_le_mul_normalizer_thompsonJ hX.sylow h1 h2 h2c
    (gnQPre_sup_gnDPre_normal hX) (gnWPre_normal hX) gnQPre_sup_gnDPre_le_gnWPre
    (gnWPre_le_sup_normalizer hX hcomm) (gnAbsorbs_QD hX hP hH)

theorem gnFactor_of_gnAbsorbs_gnWPre (hX : GNSetting X T) (hP : IsC118Pair T T₁ T₂)
    (hW : GNAbsorbs T T₁ T₂ (gnWPre T)) : GNFactor T T₁ T₂ := by
  obtain ⟨-, h1, -, -, h2, h2c, -⟩ := id hP
  have h1M : (1 : X) ∈ gnM T T₁ T₂ :=
    mem_gnM_iff.2 ⟨1, one_mem _, 1, one_mem _, 1, one_mem _, by simp⟩
  refine gnFactor_of_normal hX h1 h2 h2c (gnWPre_normal hX) (thompsonJ_le_gnWPre hX)
    fun w hw => ?_
  have := hW w hw 1 h1M
  rw [mul_one] at this
  exact mem_gnM_iff.1 this

theorem gnFactor_of_absorbs_H_of_commutator_le (hX : GNSetting X T) (hP : IsC118Pair T T₁ T₂)
    (hH : GNAbsorbs T T₁ T₂ (gnHPre T))
    (hcomm : ⁅gnWPre T, thompsonJ T⁆ ≤ gnQPre T ⊔ gnDPre T) : GNFactor T T₁ T₂ :=
  gnFactor_of_gnAbsorbs_gnWPre hX hP (gnAbsorbs_gnWPre hX hP hH hcomm)

theorem gnFactor_of_absorbs_H_at (hJ : JOutCentralAt T) (hX : GNSetting X T)
    (hP : IsC118Pair T T₁ T₂) (hH : GNAbsorbs T T₁ T₂ (gnHPre T)) : GNFactor T T₁ T₂ :=
  gnFactor_of_absorbs_H_of_commutator_le hX hP hH (gnWPre_commutator_le hJ hX)

theorem gnFactor_of_absorbs_H (hJ : JOutCentral) (hX : GNSetting X T)
    (hP : IsC118Pair T T₁ T₂) (hH : GNAbsorbs T T₁ T₂ (gnHPre T)) : GNFactor T T₁ T₂ :=
  gnFactor_of_absorbs_H_at (hJ X T hX) hX hP hH

theorem gnFactor_of_absorbs_H_of_outer_commutative (hX : GNSetting X T)
    (hP : IsC118Pair T T₁ T₂) (hH : GNAbsorbs T T₁ T₂ (gnHPre T))
    (hcomm : ∀ L : Subgroup (X ⧸ gnC T), IsComponentOf L ⊤ → ⁅L, gnImg T (thompsonJ T)⁆ ≠ ⊥ →
      IsMulCommutative (Outer ↥L)) : GNFactor T T₁ T₂ :=
  gnFactor_of_absorbs_H_at (fun L hL hne hnc => absurd (hcomm L hL hne) hnc) hX hP hH

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15
