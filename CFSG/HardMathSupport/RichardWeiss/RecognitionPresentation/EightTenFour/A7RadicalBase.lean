
module

public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.EightTenFour.A7Classify
public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.EightTenFour.Radical

@[expose] public section

namespace CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.EightTenFour

open Equiv Equiv.Perm CFSG.Open CFSG.Quasithin

theorem isTwoRadicalIn_top_map {G G' : Type*} [Group G] [Group G'] (e : G ≃* G')
    {P : Subgroup G} (h : IsTwoRadicalIn ⊤ P) : IsTwoRadicalIn ⊤ (P.map e.toMonoidHom) := by
  obtain ⟨-, hne, hP2, hmax⟩ := isTwoRadicalIn_iff.1 h
  have hN : ∀ x : G', x ∈ Subgroup.normalizer ((P.map e.toMonoidHom : Subgroup G') : Set G') ↔
      e.symm x ∈ Subgroup.normalizer (P : Set G) := by
    intro x
    rw [← Subgroup.map_equiv_normalizer_eq P e, Subgroup.mem_map_equiv]
  refine isTwoRadicalIn_iff.2 ⟨le_top, ?_, hP2.map _, ?_⟩
  · intro hbot
    exact hne ((Subgroup.map_eq_bot_iff_of_injective P e.injective).1 hbot)
  · intro T' hT' hT'2 hTn
    have hT'N : ∀ t ∈ T', e.symm t ∈ Subgroup.normalizer (P : Set G) := fun t ht =>
      (hN t).1 (hT' ht).2
    set T : Subgroup G := T'.map e.symm.toMonoidHom with hT
    have hmemT : ∀ x, x ∈ T ↔ e x ∈ T' := fun x => by
      rw [hT, Subgroup.mem_map_equiv]; simp
    have hTle : T ≤ ⊤ ⊓ Subgroup.normalizer (P : Set G) := fun x hx =>
      ⟨trivial, by simpa using hT'N _ ((hmemT x).1 hx)⟩
    have hnormal : (T.subgroupOf (⊤ ⊓ Subgroup.normalizer (P : Set G))).Normal := by
      rw [Subgroup.normal_subgroupOf_iff hTle]
      intro x k hx hk
      have hk' : e k ∈ Subgroup.normalizer ((P.map e.toMonoidHom : Subgroup G') : Set G') := by
        rw [hN]; simpa using hk.2
      have := (Subgroup.normal_subgroupOf_iff hT').1 hTn (e x) (e k) ((hmemT x).1 hx)
        ⟨trivial, hk'⟩
      rw [hmemT, map_mul, map_mul, map_inv]
      exact this
    have hTP := hmax T hTle (hT'2.map _) hnormal
    intro t ht
    rw [Subgroup.mem_map_equiv]
    exact hTP ((hmemT _).2 (by simpa using ht))

theorem good_of_map (e : A7 ≃* A7) {P : Subgroup A7} (h : A7Good (P.map e.toMonoidHom)) :
    A7Good P := by
  unfold A7Good at h ⊢
  obtain ⟨H₀, hs, ⟨a, ha, b, hb, hab⟩, hle, hodd⟩ := h
  have hinj : Function.Injective e.symm.toMonoidHom := e.symm.injective
  refine ⟨H₀.map e.symm.toMonoidHom, ?_, ⟨e.symm a, ⟨a, ha, rfl⟩, e.symm b, ⟨b, hb, rfl⟩, ?_⟩,
    ?_, ?_⟩
  · exact (Subgroup.equivMapOfInjective H₀ _ hinj).symm.isSimpleGroup
  · intro hcomm
    apply hab
    have := congrArg e (hcomm)
    simpa using this
  · intro x hx
    exact ⟨e x, hle ⟨x, hx, rfl⟩, by simp⟩
  · have hP : P = (P.map e.toMonoidHom).map e.symm.toMonoidHom := by
      rw [Subgroup.map_map]
      have : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id A7 := by ext x; simp
      rw [this, Subgroup.map_id]
    have := Subgroup.relIndex_map_map_of_injective (P.map e.toMonoidHom) H₀ hinj
    rw [← hP] at this
    unfold Subgroup.relIndex at this
    rw [this]
    exact hodd

end CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.EightTenFour
