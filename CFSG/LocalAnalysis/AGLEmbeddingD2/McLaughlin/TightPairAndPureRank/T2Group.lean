module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.T2Abs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.ActionOnSub
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs
import CFSG.LocalAnalysis.AGLEmbedding.PushingUpLemmas
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.PerfectCommutator

public section

open scoped Pointwise commutatorElement

namespace CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank

open CFSG.AGLEmbedding CFSG.Open

variable {G : Type} [Group G]

@[expose, instance_reducible] def commGroupOfElemAbelian {N : Subgroup G} (hN : IsElemAbelian 2 N) :
    CommGroup ↥N :=
  { (inferInstance : Group ↥N) with
    mul_comm := fun a b => hN.1.is_comm.comm a b }

theorem expTwo_of_elemAbelian {N : Subgroup G} (hN : IsElemAbelian 2 N) :
    @ExpTwo ↥N (commGroupOfElemAbelian hN).toGroup :=
  @ExpTwo.mk ↥N (commGroupOfElemAbelian hN).toGroup fun v => Subtype.ext (by
    have := hN.2 v.1 v.2
    simpa [pow_two] using this)

section Translate

variable {N L : Subgroup G} (hN : IsElemAbelian 2 N) (hL : L ≤ Subgroup.normalizer (N : Set G))

include hN

theorem map_commSubOf (W : Subgroup ↥N) :
    letI := commGroupOfElemAbelian hN
    haveI := expTwo_of_elemAbelian hN
    (commSubOf (actHom N L hL) W).map N.subtype = ⁅W.map N.subtype, L⁆ := by
  let _ := commGroupOfElemAbelian hN
  have _ := expTwo_of_elemAbelian hN
  rw [commSubOf, MonoidHom.map_closure]
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ ⟨_, ⟨a, w, hw, rfl⟩, rfl⟩
    have e : N.subtype (actHom N L hL a w * w⁻¹) = ⁅(a : G), (w : G)⁆ := by
      rw [map_mul, map_inv]
      show ((actHom N L hL a w : ↥N) : G) * ((w : ↥N) : G)⁻¹ = _
      rw [actHom_apply_coe]
      simp [commutatorElement_def]
    rw [e, ← commutatorElement_inv]
    exact Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator ⟨w, hw, rfl⟩ a.2)
  · rw [Subgroup.commutator_le]
    rintro _ ⟨w, hw, rfl⟩ a ha
    have e : N.subtype (actHom N L hL ⟨a, ha⟩ w * w⁻¹) = ⁅a, (w : G)⁆ := by
      rw [map_mul, map_inv]
      show ((actHom N L hL ⟨a, ha⟩ w : ↥N) : G) * ((w : ↥N) : G)⁻¹ = _
      rw [actHom_apply_coe]
      simp [commutatorElement_def]
    have hgen : N.subtype (actHom N L hL ⟨a, ha⟩ w * w⁻¹) ∈
        N.subtype '' {x | ∃ a : ↥L, ∃ w ∈ W, x = actHom N L hL a w * w⁻¹} :=
      ⟨_, ⟨⟨a, ha⟩, w, hw, rfl⟩, rfl⟩
    have e2 : ⁅(N.subtype w : G), a⁆ = (N.subtype (actHom N L hL ⟨a, ha⟩ w * w⁻¹))⁻¹ := by
      rw [e, commutatorElement_inv]
      rfl
    rw [e2]
    exact Subgroup.inv_mem _ (Subgroup.subset_closure hgen)

theorem map_fixSubA :
    letI := commGroupOfElemAbelian hN
    haveI := expTwo_of_elemAbelian hN
    (fixSubA (actHom N L hL)).map N.subtype = N ⊓ Subgroup.centralizer (L : Set G) := by
  let _ := commGroupOfElemAbelian hN
  have _ := expTwo_of_elemAbelian hN
  ext g
  constructor
  · rintro ⟨n, hn, rfl⟩
    refine ⟨n.2, Subgroup.mem_centralizer_iff.mpr fun l hl => ?_⟩
    have := hn ⟨l, hl⟩
    have h2 := congrArg (fun m : ↥N => (m : G)) this
    simp only [actHom_apply_coe] at h2
    calc (l : G) * ((n : ↥N) : G) = (l * n * l⁻¹) * l := by group
      _ = n * l := by rw [h2]
  · rintro ⟨hgN, hgC⟩
    refine ⟨⟨g, hgN⟩, fun a => ?_, rfl⟩
    apply Subtype.ext
    rw [actHom_apply_coe]
    have := Subgroup.mem_centralizer_iff.mp hgC a a.2
    calc (a : G) * g * (a : G)⁻¹ = (g * a) * (a : G)⁻¹ := by rw [← this]
      _ = g := by group

theorem map_commSub :
    letI := commGroupOfElemAbelian hN
    haveI := expTwo_of_elemAbelian hN
    (commSub (actHom N L hL)).map N.subtype = ⁅N, L⁆ := by
  let _ := commGroupOfElemAbelian hN
  have _ := expTwo_of_elemAbelian hN
  rw [commSub, map_commSubOf hN hL, Subgroup.map_top, Subgroup.range_subtype]

theorem irrQuotGroup_of_hasIrr (hirr : HasIrreducibleCommutatorQuotient L N) :
    letI := commGroupOfElemAbelian hN
    haveI := expTwo_of_elemAbelian hN
    IrrQuotGroup (actHom N L hL) := by
  let _ := commGroupOfElemAbelian hN
  have _ := expTwo_of_elemAbelian hN
  have hU := map_commSub hN hL
  have hF := map_fixSubA hN hL
  have hUN : ⁅N, L⁆ ≤ N := by rw [← hU]; exact Subgroup.map_subtype_le _
  have hC : (fixSubA (actHom N L hL) ⊓ commSub (actHom N L hL)).map N.subtype =
      ⁅N, L⁆ ⊓ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.map_inf _ _ _ N.subtype_injective, hF, hU]
    ext x
    constructor
    · rintro ⟨⟨-, hc⟩, hu⟩; exact ⟨hu, hc⟩
    · rintro ⟨hu, hc⟩; exact ⟨⟨hUN hu, hc⟩, hu⟩
  refine ⟨?_, fun W hCW hWU hW => ?_⟩
  · rw [← Subgroup.map_lt_map_iff_of_injective N.subtype_injective, hC, hU]
    exact hirr.1
  · have hCW' : ⁅N, L⁆ ⊓ Subgroup.centralizer (L : Set G) ≤ W.map N.subtype := by
      rw [← hC]; exact Subgroup.map_mono hCW
    have hWU' : W.map N.subtype ≤ ⁅N, L⁆ := by
      rw [← hU]; exact Subgroup.map_mono hWU
    have hLW : L ≤ Subgroup.normalizer ((W.map N.subtype : Subgroup G) : Set G) := by
      refine le_normalizer_of_forall_map_conj_le fun l hl => ?_
      rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      refine ⟨actHom N L hL ⟨l, hl⟩ w, hW _ w hw, ?_⟩
      show ((actHom N L hL ⟨l, hl⟩ w : ↥N) : G) = _
      rw [actHom_apply_coe]
      simp [MulAut.conj_apply]
    rcases hirr.2 _ hCW' hWU' hLW with h | h
    · left
      apply Subgroup.map_injective N.subtype_injective
      rw [h, hC]
    · right
      apply Subgroup.map_injective N.subtype_injective
      rw [h, hU]

end Translate

theorem centralizes_commutator_of_irreducibleQuotient [Finite G] {N L₁ L₂ : Subgroup G}
    (hN : IsElemAbelian 2 N) (h₁ : L₁ ≤ Subgroup.normalizer (N : Set G))
    (h₂ : L₂ ≤ Subgroup.normalizer (N : Set G))
    (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, ∀ n ∈ N, a * (b * n * b⁻¹) * a⁻¹ = b * (a * n * a⁻¹) * b⁻¹)
    (hperf₁ : ⁅L₁, L₁⁆ = L₁) (hperf₂ : ⁅L₂, L₂⁆ = L₂)
    (hirr : HasIrreducibleCommutatorQuotient L₁ N) :
    ∀ b ∈ L₂, ∀ u ∈ ⁅N, L₁⁆, b * u * b⁻¹ = u := by
  let _ := commGroupOfElemAbelian hN
  have _ := expTwo_of_elemAbelian hN
  have hNc : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hN.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hU := map_commSub hN h₁
  have hB : commutator ↥L₂ = ⊤ := by
    rw [commutator_def]
    apply Subgroup.map_injective L₂.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype, hperf₂]
  have hperf : commSub (actHom N L₁ h₁) ≤ commSubOf (actHom N L₁ h₁) (commSub (actHom N L₁ h₁)) := by
    rw [← Subgroup.map_le_map_iff_of_injective N.subtype_injective, hU,
      map_commSubOf hN h₁, hU]
    exact WeakBlockModuleData.commutator_le_commutator_commutator_of_perfect hperf₁ h₁ hNc
  have hcomm' : ∀ (a : ↥L₁) (b : ↥L₂) (v : ↥N),
      actHom N L₁ h₁ a (actHom N L₂ h₂ b v) = actHom N L₂ h₂ b (actHom N L₁ h₁ a v) := by
    intro a b v
    apply Subtype.ext
    rw [actHom_apply_coe, actHom_apply_coe, actHom_apply_coe, actHom_apply_coe]
    exact hcomm a a.2 b b.2 v v.2
  have key := centralizes_commSub_of_irrQuot (actHom N L₁ h₁) (actHom N L₂ h₂) hcomm' hB hperf
    (irrQuotGroup_of_hasIrr hN h₁ hirr)
  intro b hb u hu
  rw [← hU] at hu
  obtain ⟨u₀, hu₀, rfl⟩ := hu
  have := congrArg (fun m : ↥N => (m : G)) (key ⟨b, hb⟩ u₀ hu₀)
  simpa [actHom_apply_coe] using this

end CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank
