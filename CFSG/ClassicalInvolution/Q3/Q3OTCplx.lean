module

public import CFSG.ClassicalInvolution.Q3.Q3NMOrth
public import CFSG.ClassicalInvolution.SmallOrth.Orth3GaussMain

public section

namespace CFSG.ClassicalInvolution.Q3.Q3OT

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalGroups.Orthogonal.Small
  CFSG.ClassicalInvolution.Q3.Q3NM CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Balance
  CFSG.LieType.Universal.Unitary CFSG.Open CFSG.ComponentClassification CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.ModelFacts

section Final

variable {F : Type} [Field F] [Finite F] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V}

theorem oddCoreIn_fixed_eq_bot_of_cplx (hF : Nat.card F = 3)
    (hQ : (polarBilin Q).Nondegenerate) (hdim : 6 ≤ Module.finrank F V)
    (hOE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ ≤
      elementaryGroup Q) {g : V ≃ₗ[F] V} (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hg2 : ∀ x, g (g x) = -x) :
    oddCoreIn (fixedSubgroup (autToCentralQuotient ↥(elementaryGroup Q) (conjE Q g hgO))) = ⊥ := by
  have : Fact (Nat.card F = 3) := ⟨hF⟩
  obtain ⟨-, h2⟩ := three_eq_zero_two_ne_zero_of_card_eq_three hF
  obtain ⟨m, hm, ⟨ab⟩⟩ := exists_adaptedBasis hF hQ hgO hg2
  have hm3 : 3 ≤ m := by omega
  have hZ := isPGroup_center_elementaryGroup hF hQ (by omega : 3 ≤ Module.finrank F V)
  set θ := thetaSU ab h2 hm3 hOE with hθ
  refine oddCoreIn_fixed_eq_bot_of_blocks hZ (conjE Q g hgO) (ι := Unit) (fun _ => θ.range)
    ?_ ?_ ?_ ?_
  · rintro - x ⟨X, rfl⟩
    exact (mem_fixedSubgroup_conjE hgO _).mpr
      (thetaHom_mul_comm ab hg2 (X : GL (Fin m) (GaussField F)))
  · intro _ b hb x hx
    obtain ⟨X, rfl⟩ := hx
    have hcomm : (b : V ≃ₗ[F] V) * g = g * b := (mem_fixedSubgroup_conjE hgO b).mp hb
    obtain ⟨A, hA, hνA⟩ :=
      exists_unitary_of_commute ab hg2 (elementaryGroup_le_orthogonalGroup Q b.2) hcomm
    obtain ⟨X', hX'⟩ := exists_su_conj hA X
    exact ⟨X', Subtype.ext (conj_thetaHom ab hA hνA _ _ hX').symm⟩
  · intro _
    show oddCoreIn (θ.range.map (QuotientGroup.mk' (Subgroup.center ↥(elementaryGroup Q)))) = ⊥
    rw [← MonoidHom.range_comp]
    refine oddCoreIn_range_eq_bot_of_central_kernel
      ((QuotientGroup.mk' (Subgroup.center ↥(elementaryGroup Q))).comp θ)
      (componentOddCore_su_eq_bot m) ?_ ?_
    · intro X hX
      have h1 : θ X ∈ Subgroup.center ↥(elementaryGroup Q) := (QuotientGroup.eq_one_iff _).mp hX
      rw [Subgroup.mem_center_iff]
      intro Y
      apply thetaSU_injective ab h2 hm3 hOE
      rw [map_mul, map_mul]
      exact Subgroup.mem_center_iff.mp h1 (θ Y)
    · intro X
      obtain ⟨k, hk⟩ := hZ ⟨θ X.1, (QuotientGroup.eq_one_iff _).mp X.2⟩
      refine ⟨k, Subtype.ext (thetaSU_injective ab h2 hm3 hOE ?_)⟩
      simpa using congrArg Subtype.val hk
  · intro ν hν hL
    have hcomm : (ν : V ≃ₗ[F] V) * g = g * ν := (mem_fixedSubgroup_conjE hgO ν).mp hν
    obtain ⟨A, hA, hνA⟩ :=
      exists_unitary_of_commute ab hg2 (elementaryGroup_le_orthogonalGroup Q ν.2) hcomm
    have hAX : ∀ X : SUid (gaussSigma (F := F)) m,
        A * ((X : GL (Fin m) (GaussField F)) : Matrix (Fin m) (Fin m) (GaussField F)) =
          ((X : GL (Fin m) (GaussField F)) : Matrix (Fin m) (Fin m) (GaussField F)) * A := by
      intro X
      apply thetaEnd_injective ab
      rw [map_mul, map_mul, ← hνA]
      exact LinearMap.ext fun x =>
        LinearEquiv.congr_fun (congrArg Subtype.val (hL () (θ X) ⟨X, rfl⟩)) x
    obtain ⟨c, hc⟩ := exists_scalar_of_commute_su (by omega : 2 ≤ m) hAX
    have hc4 : c ^ 4 = 1 := by
      rw [hc, conjTr_scalar, ← map_mul] at hA
      have h1 := congrFun (congrFun hA ⟨0, by omega⟩) ⟨0, by omega⟩
      simp only [Matrix.scalar_apply, Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at h1
      have h3 : gaussSigma (F := F) c = c ^ 3 := by
        rw [gaussSigma_apply, gauss_pow_three]
      rw [h3] at h1
      calc c ^ 4 = c ^ 3 * c := by ring
        _ = 1 := h1
    have h4 : thetaEnd ab A ^ 4 = 1 := by
      rw [hc, ← map_pow, ← map_pow, hc4, map_one, map_one]
    refine ⟨2, Subtype.ext (LinearEquiv.ext fun x => ?_)⟩
    rw [Subgroup.coe_pow, LinearEquiv.coe_pow]
    have h5 := congrArg (fun φ : V →ₗ[F] V => φ x) h4
    rw [← hνA, Module.End.coe_pow] at h5
    exact h5

end Final

end CFSG.ClassicalInvolution.Q3.Q3OT
