module

public import CFSG.GH74.Generic.Front.Transfer

public section

namespace CFSG.GH74.Generic

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.GH74.Filter.ClassicalOdd Subgroup

theorem GoodSub.mono {T T' : Prop} (h : T → T') {Y : Type*} [Group Y] {P : Subgroup Y}
    (hP : GoodSub T P) : GoodSub T' P :=
  hP.imp id fun h' => ⟨h'.1, h h'.2⟩

theorem ThreeModel.of_mulEquiv {K K' : Type} [Group K] [Group K'] (e : K ≃* K')
    (h : ThreeModel K) : ThreeModel K' := by
  obtain ⟨F, hF1, hF2, hF3, h⟩ := h
  exact ⟨F, hF1, hF2, hF3, h.imp (fun ⟨e'⟩ => ⟨e.symm.trans e'⟩) (fun ⟨e'⟩ => ⟨e.symm.trans e'⟩)⟩

theorem FrontData0.ofMulEquiv {K K' : Type} [Group K] [Group K'] (e : K ≃* K')
    (D : FrontData0 K) : Nonempty (FrontData0 K') := by
  refine ⟨⟨e.toMonoidHom.comp D.φ, e D.w, D.J.map e.toMonoidHom, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact e.injective.comp D.inj
  · rw [← map_mul, D.w_sq, map_one]
  · intro g h
    have := congrArg e (D.w_swap g h)
    simpa [map_mul, map_inv] using this
  · intro t ht1 ht2 ht3
    have h1 : e.symm t * e.symm t = 1 := by rw [← map_mul, ht1, map_one]
    have h2 : e.symm t ≠ 1 := fun h => ht2 (by simpa using congrArg e h)
    have h3 : e.symm t ∉ Subgroup.center K := fun h => ht3 (by
      have := (mem_center_iff_of_mulEquiv e (e.symm t)).2 h
      rwa [MulEquiv.apply_symm_apply] at this)
    obtain ⟨k, hk⟩ := D.oneClass _ h1 h2 h3
    refine ⟨e k, ?_⟩
    have := congrArg e hk
    simpa [map_mul, map_inv] using this
  · intro g hg
    obtain ⟨a, rfl⟩ := hg
    exact ⟨D.φ a, D.range_le ⟨a, rfl⟩, rfl⟩
  · intro g hg
    obtain ⟨j, hj, rfl⟩ := hg
    have := D.le_centralizer hj
    rw [Subgroup.mem_centralizer_singleton_iff] at this ⊢
    simpa [map_mul] using congrArg e this
  · exact (goodSub_map e.toMonoidHom D.good).mono (ThreeModel.of_mulEquiv e)

theorem NoCentral.ofMulEquiv {K K' : Type} [Group K] [Group K'] (e : K ≃* K')
    (h : NoCentral K) : NoCentral K' := by
  intro ψ hψ hcen
  apply h (e.symm.toMonoidHom.comp ψ) (e.symm.injective.comp hψ)
  exact (mem_center_iff_of_mulEquiv e.symm (ψ (QuaternionGroup.a 2, 1))).2 hcen

end CFSG.GH74.Generic
