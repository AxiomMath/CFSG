module

public import CFSG.ClassicalInvolution.Q3.TL4LinkZ2G4Red
public import CFSG.ClassicalInvolution.Q3.TL4Mdl1521MemSp

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.Z2W.G4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Blueprint

theorem false_of_sPHyp_PSp {S : Type} [Group S] (hS : LieModel S .PSp 2 3 1) {A B : Subgroup S}
    {r : S} {x : MulAut S} (h : SPHyp A B r x) : False := by
  rcases hS with ⟨-, -, F, _, _, hF, ⟨e₀⟩⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · rw [pow_one] at hF
    obtain ⟨e, he⟩ := E1521.exists_mulEquiv_blockQ0Sp hF e₀ h.quat.q8
    have hB8 : Nonempty (↥(B.map e.toMonoidHom) ≃* QuaternionGroup 2) := by
      obtain ⟨eB⟩ := h.q8B
      exact ⟨(B.equivMapOfInjective _ e.injective).symm.trans eB⟩
    have hB2 : B.map e.toMonoidHom = E1521.blockQ2Sp F := E1521.eq_blockQ2Sp_of_comm hF hB8 (by
      rw [← he]
      rintro _ ⟨b, hb, rfl⟩ _ ⟨a, ha, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom]
      rw [← map_mul, ← map_mul, h.comm a ha b hb])
    set α : MulAut _ := (e.symm.trans x).trans e with hαdef
    have hα : ∀ y, α (e y) = e (x y) := fun y => by
      simp only [hαdef, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    refine E1521.sig_psp4_false hF α ?_ ?_ ?_
    · ext y
      obtain ⟨s, rfl⟩ := e.surjective y
      rw [MulAut.mul_apply, hα, hα, h.apply_apply, MulAut.one_apply]
    · rw [← he]
      rintro _ ⟨a, ha, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom]
      rw [hα, h.fixA a ha]
    · obtain ⟨b, hb, -, hxb⟩ := h.exists_moved
      have hb' : e b ∈ E1521.blockQ2Sp F := hB2 ▸ ⟨b, hb, rfl⟩
      refine ⟨e b, fun y hy => (E1521.blockQ0Sp_comm_blockQ2Sp hF hy hb').symm, fun h1 => ?_⟩
      exact hxb (e.injective (by rw [← hα, h1]))
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)

end CFSG.ClassicalInvolution.Q3.TL4.Z2W.G4
