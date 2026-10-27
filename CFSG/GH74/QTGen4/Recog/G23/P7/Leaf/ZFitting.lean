module

public import CFSG.GH74.QTGen4.Recog.G23.MLetters
public import CFSG.GH74.QTGen4.Recog.G23.MSylowC
public import CFSG.GH74.QTGen4.Recog.G23.HK
public import CFSG.GH74.QTGen4.Recog.G23.P7.OpenLeaves

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Recog.G23.P7

open CFSG.Open CFSG.Quasithin.G23Type CFSG.GH74.QTGen4.Recog.G23 CFSG.CosetTable

variable {G : Type} [Group G]

theorem leafZFitting_zOf_mem_inf {T H H₁ H₂ M : Subgroup G} {e : Fin 6 → G}
    (h : Setup G T H H₁ H₂ M e) : zOf e ∈ H₁ ⊓ H₂ := by
  have hr : FreeGroup.lift e (FreeGroup.mk ([(0, true), (1, true), (0, true), (1, true),
      (3, false), (2, false), (3, false), (2, false)] : List (Fin 6 × Bool))) = 1 :=
    h.lets.rels _ (by simp [g23WordsH])
  have hr' : e 0 * e 1 * e 0 * e 1 * (e 3)⁻¹ * (e 2)⁻¹ * (e 3)⁻¹ * (e 2)⁻¹ = 1 := by
    simpa [FreeGroup.lift_mk, mul_assoc] using hr
  have hA : e 0 * e 1 * e 0 * e 1 = e 2 * e 3 * e 2 * e 3 := by
    calc e 0 * e 1 * e 0 * e 1
        = (e 0 * e 1 * e 0 * e 1 * (e 3)⁻¹ * (e 2)⁻¹ * (e 3)⁻¹ * (e 2)⁻¹) *
            (e 2 * e 3 * e 2 * e 3) := by group
      _ = e 2 * e 3 * e 2 * e 3 := by rw [hr', one_mul]
  have hz2 : zOf e = (e 2 * e 3) ^ 2 := by
    unfold zOf
    simp only [sq, mul_assoc] at hA ⊢
    exact hA
  have he0 : e 0 ∈ H₁ := by
    rw [← h.lets.gen₁]; exact Subgroup.subset_closure (Set.mem_insert _ _)
  have he1 : e 1 ∈ H₁ := by
    rw [← h.lets.gen₁]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have he2 : e 2 ∈ H₂ := by
    rw [← h.lets.gen₂]; exact Subgroup.subset_closure (Set.mem_insert _ _)
  have he3 : e 3 ∈ H₂ := by
    rw [← h.lets.gen₂]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · exact pow_mem (mul_mem he0 he1) 2
  · rw [hz2]; exact pow_mem (mul_mem he2 he3) 2

theorem leafZFitting : LeafZFitting := by
  intro G _ _ T H H₁ H₂ M e h
  have hctx : G23Ctx G T H H₁ H₂ M := h.ctx
  have hzQ : zOf e ∈ H₁ ⊓ H₂ := leafZFitting_zOf_mem_inf h
  have hzH : zOf e ∈ H := G23One.inf_le hctx.one hzQ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTs : IsPGroup 2 T ∧ ¬ 2 ∣ T.index := hctx.sylow
  have hTH : T ≤ H := hctx.tH
  have hTM : T ≤ M := hctx.tM
  have hTdvdH : (T.subgroupOf H).index ∣ T.index := Dvd.intro _ (Subgroup.relIndex_mul_index hTH)
  have hTidxH : ¬ 2 ∣ (T.subgroupOf H).index := fun hd => hTs.2 (dvd_trans hd hTdvdH)
  have hTdvdM : (T.subgroupOf M).index ∣ T.index := Dvd.intro _ (Subgroup.relIndex_mul_index hTM)
  have hTidxM : ¬ 2 ∣ (T.subgroupOf M).index := fun hd => hTs.2 (dvd_trans hd hTdvdM)
  have hTsH : IsPGroup 2 (T.subgroupOf H) :=
    hTs.1.of_injective (Subgroup.subgroupOfEquivOfLe hTH).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hTH).injective
  have hQN : ((H₁ ⊓ H₂).subgroupOf H).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hc : (g : G) * (n : G) = (n : G) * (g : G) :=
      G23One.mul_comm_of_mem_inf hctx.one g.2 hn
    have hgn : ((g * n * g⁻¹ : ↥H) : G) = (n : G) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hc, mul_inv_cancel_right]
    rw [hgn]
    exact hn
  have hQ2 : IsPGroup 2 ((H₁ ⊓ H₂).subgroupOf H) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (G23One.inf_le hctx.one)).toEquiv,
      hctx.one.card_inf]
    norm_num
  have hQT : (H₁ ⊓ H₂).subgroupOf H ≤ T.subgroupOf H := by
    have := hQN
    have hle := IsPGroup.le_sylow_of_normal hQ2 (hTsH.toSylow hTidxH)
    rwa [IsPGroup.toSylow_coe] at hle
  have hzT : zOf e ∈ T := by
    have hmem : (⟨zOf e, hzH⟩ : ↥H) ∈ (H₁ ⊓ H₂).subgroupOf H := Subgroup.mem_subgroupOf.mpr hzQ
    exact Subgroup.mem_subgroupOf.mp (hQT hmem)
  have hVT : quasithinGenFitting M ≤ T := G23Two.fitting_le_T hctx.two hTM hTs.1 hTidxM
  have hzC : zOf e ∈ Subgroup.centralizer (quasithinGenFitting M : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact G23One.mul_comm_of_mem_inf hctx.one (hTH (hVT hv)) hzQ
  have hzV : zOf e ∈ M ⊓ Subgroup.centralizer (quasithinGenFitting M : Set G) :=
    Subgroup.mem_inf.mpr ⟨hTM hzT, hzC⟩
  rwa [G23Two.inf_centralizer_fitting hctx.two] at hzV

end CFSG.GH74.QTGen4.Recog.G23.P7
