module

public import CFSG.ClassicalInvolution.Q3.TL4E3S3OM1SD
public import CFSG.ClassicalInvolution.Q3.TL4Mdl1521MemSp

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.Blueprint
open CFSG.Assembly.LowTwoRank (StatedProj StatedSp)

namespace E3S3O

theorem sigmaFixOm3_of_blocks {S M : Type} [Group S] [Group M] {Q0 Q2 : Subgroup M}
    (hex : ∀ A : Subgroup S, Nonempty (↥A ≃* QuaternionGroup 2) →
      ∃ e : S ≃* M, A.map e.toMonoidHom = Q0)
    (htw : ∀ B : Subgroup M, Nonempty (↥B ≃* QuaternionGroup 2) →
      (∀ x ∈ B, ∀ y ∈ Q0, x * y = y * x) → B = Q2)
    (hno : ∀ α : MulAut M, (∀ a ∈ Q0, α a = a) →
      (∃ w ∈ Q2, orderOf w = 4 ∧ ∀ b ∈ Q2, α b = w * b * w⁻¹) → α * α ≠ 1) :
    SigmaFixOm3 S := by
  intro A B r x hd ⟨q, hq, hqB⟩ hne hxx hfixA ⟨w, hwB, hw4, hwx⟩ _
  exfalso
  obtain ⟨e, he⟩ := hex A hd.q8
  have hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := by
    rcases hd.twins q hq with h | h
    · exact absurd (hqB.symm.trans h) hne
    · rw [← hqB]
      exact h
  have hB8 : Nonempty (↥(B.map e.toMonoidHom) ≃* QuaternionGroup 2) := by
    obtain ⟨eA⟩ := hd.q8
    rw [← hqB]
    exact ⟨((conjSub q A).equivMapOfInjective _ e.injective).symm.trans
      ((A.equivMapOfInjective (MulAut.conj q).toMonoidHom (MulAut.conj q).injective).symm.trans
        eA)⟩
  have hB2 : B.map e.toMonoidHom = Q2 := htw _ hB8 (by
    rw [← he]
    rintro _ ⟨b, hb, rfl⟩ _ ⟨a, ha, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, hcomm a ha b hb])
  set α : MulAut M := (e.symm.trans x).trans e with hαdef
  have hα : ∀ y, α (e y) = e (x y) := fun y => by
    simp only [hαdef, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  refine hno α ?_ ⟨e w, ?_, ?_, ?_⟩ ?_
  · rw [← he]
    rintro _ ⟨a, ha, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [hα, hfixA a ha]
  · rw [← hB2]
    exact ⟨w, hwB, rfl⟩
  · rw [MulEquiv.orderOf_eq, hw4]
  · rw [← hB2]
    rintro _ ⟨b, hb, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [hα, hwx b hb, map_mul, map_mul, map_inv]
  · ext y
    obtain ⟨s, rfl⟩ := e.surjective y
    have h1 : x (x s) = s := by
      have := congrArg (fun τ : MulAut S => τ s) hxx
      simpa using this
    rw [MulAut.mul_apply, hα, hα, h1, MulAut.one_apply]

theorem sigmaFixOm3_PSL {S : Type} [Group S] (hS : LieModel S .PSL 4 3 1) : SigmaFixOm3 S := by
  obtain ⟨F, _, _, hF, ⟨e₀⟩⟩ :=
    LocalAnalysis.ComponentInitial.LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hS
  rw [pow_one] at hF
  exact sigmaFixOm3_of_blocks (fun A hA => E1521.exists_mulEquiv_blockQ0 hF e₀ hA)
    (fun B hB hc => E1521.eq_blockQ2_of_comm hF hB hc)
    (fun α h1 h2 => E1521.no_sigma_blockQ hF α h1 h2)

theorem sigmaFixOm3_PSp {S : Type} [Group S] (hS : LieModel S .PSp 2 3 1) : SigmaFixOm3 S := by
  rcases hS with ⟨-, -, F, _, _, hF, ⟨e₀⟩⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · rw [pow_one] at hF
    exact sigmaFixOm3_of_blocks (fun A hA => E1521.exists_mulEquiv_blockQ0Sp hF e₀ hA)
      (fun B hB hc => E1521.eq_blockQ2Sp_of_comm hF hB hc)
      (fun α h1 h2 => E1521.no_sigma_blockQSp hF α h1 h2)
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)

end E3S3O

end CFSG.ClassicalInvolution.Q3.TL4
