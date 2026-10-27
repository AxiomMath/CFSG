module

public import CFSG.HardMathSupport.Malle.Coordinator.CoverThree.CoverIso

public section

namespace CFSG.HardMathSupport.Malle.Coordinator.CoverThree

open scoped MatrixGroups
open CFSG.LieType.SeitzGeneration Matrix

theorem coverThree_gen_toral_linear {K : Type} [Group K] [Finite K] (hK : Open.IsQuasisimple K)
    (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.A 2 q).Valid) (h9 : 9 ∣ q.card - 1)
    (e : K ⧸ Subgroup.center K ≃* Cat ⟨.A 2 q, hv⟩)
    (hz : 3 ∣ Nat.card (Subgroup.center K))
    (P : Subgroup K) (hPc : IsMulCommutative P) (hP : Nat.card P = 3 ^ 3)
    (hPZ : Nat.card (P ⊓ Subgroup.center K : Subgroup K) = 3)
    (hP3 : ∀ x ∈ P, x ^ 3 ∈ Subgroup.center K) :
    Subgroup.closure {k : K | ∃ x ∈ P, x ∉ Subgroup.center K ∧ k * x = x * k} = ⊤ := by
  classical
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hperf : Group.IsPerfect K := Group.isPerfect_def.mpr hK.1
  set F := GaloisField q.p q.exponent
  have hF : Nat.card F = q.card := by
    rw [GaloisField.card _ _ q.exponent_pos.ne', TauCeti.PrimePower.card_def]
  have hF9 : 9 ∣ Nat.card F - 1 := by rw [hF]; exact h9
  let eL := CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 q hv
  let ρ : K →* ProjectiveSpecialLinearGroup (Fin 3) F :=
    (eL.toMonoidHom.comp e.toMonoidHom).comp (QuotientGroup.mk' (Subgroup.center K))
  have hρs : Function.Surjective ρ :=
    (eL.surjective.comp e.surjective).comp (QuotientGroup.mk'_surjective _)
  have hker : ρ.ker = Subgroup.center K := by
    ext x
    simp only [MonoidHom.mem_ker, ρ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  obtain ⟨ψ⟩ := exists_mulEquiv_sl3_of_cover hF9 ρ hρs hker hz
  set P' : Subgroup SL(3, F) := P.map ψ.symm.toMonoidHom with hP'
  have hP'comm : IsMulCommutative P' := by
    refine ⟨⟨fun a b => ?_⟩⟩
    obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.mp a.2
    obtain ⟨y, hy, hyb⟩ := Subgroup.mem_map.mp b.2
    apply Subtype.ext
    change (a : SL(3, F)) * b = b * a
    rw [← hxa, ← hyb]
    simp only [MulEquiv.coe_toMonoidHom, ← map_mul]
    congr 1
    exact congrArg Subtype.val (hPc.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hP'card : Nat.card P' = 27 := by
    rw [hP', Subgroup.card_map_of_injective ψ.symm.injective, hP]
    norm_num
  have hP'Z : Nat.card (P' ⊓ Subgroup.center SL(3, F) : Subgroup SL(3, F)) = 3 := by
    rw [hP', map_inf_center, Subgroup.card_map_of_injective ψ.symm.injective]
    exact hPZ
  have hP'3 : ∀ x ∈ P', x ^ 3 ∈ Subgroup.center SL(3, F) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, ← map_pow]
    exact (mem_center_map_iff ψ.symm _).2 (hP3 x hx)
  have htop := sl3_closure_centralizers hF9 P' hP'comm hP'card hP'Z hP'3
  have hmap : P'.map ψ.toMonoidHom = P := by
    rw [hP', Subgroup.map_map]
    ext x
    simp
  have h1 := closure_centralizers_map ψ P'
  rw [hmap, htop, Subgroup.map_top_of_surjective _ ψ.surjective] at h1
  exact h1

end CFSG.HardMathSupport.Malle.Coordinator.CoverThree
