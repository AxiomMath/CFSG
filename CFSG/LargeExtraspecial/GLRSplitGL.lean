module

public import CFSG.LargeExtraspecial.GLRSplitBasic
public import CFSG.GroupTheory.GLnTwoSplitting.Main

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.GLR

open Subgroup Module CFSG.RankThree.Literature.FSmith

theorem card_SL_zmod_two (n : ℕ) :
    Nat.card (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) = Nat.card (GL (Fin n) (ZMod 2)) := by
  refine Nat.card_eq_of_bijective (Matrix.SpecialLinearGroup.toGL) ⟨fun a b h => ?_, fun g => ?_⟩
  · ext i j
    have := congrArg (fun g : GL (Fin n) (ZMod 2) => (g : Matrix (Fin n) (Fin n) (ZMod 2)) i j) h
    exact this
  · have hu : IsUnit (g : Matrix (Fin n) (Fin n) (ZMod 2)).det :=
      (Units.isUnit g).map Matrix.detMonoidHom
    have hdet : (g : Matrix (Fin n) (Fin n) (ZMod 2)).det = 1 := by
      rcases zmod2_cases (g : Matrix (Fin n) (Fin n) (ZMod 2)).det with h | h
      · exact absurd h hu.ne_zero
      · exact h
    exact ⟨⟨g, hdet⟩, Units.ext rfl⟩

variable {G : Type*} [Group G] [Finite G] {S : Setting G} (C : Config S)

namespace Config

theorem card_Xbar : Nat.card C.Xbar = Nat.card (GL (Fin S.width) (ZMod 2)) := by
  obtain ⟨e⟩ := C.nonempty_equiv
  rw [Nat.card_congr e.toEquiv, card_SL_zmod_two]

theorem isPerfect_Xbar : Group.IsPerfect C.Xbar := by
  obtain ⟨e⟩ := C.nonempty_equiv
  have := CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect
    (K := ZMod 2) (n := S.width) (by have := C.four_le_width; omega)
  exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective

theorem map_eq_At {x : S.O} (hx : x ∈ C.Xbar) :
    C.At.map ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) = C.At := by
  refine le_antisymm ?_ fun v hv => ?_
  · rintro _ ⟨v, hv, rfl⟩
    exact C.apply_At x hx v hv
  · refine ⟨((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v, C.apply_At _ (C.Xbar.inv_mem hx) v hv, ?_⟩
    exact apply_inv_apply x v

theorem map_eq_Bt {x : S.O} (hx : x ∈ C.Xbar) :
    C.Bt.map ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) = C.Bt := by
  refine le_antisymm ?_ fun v hv => ?_
  · rintro _ ⟨v, hv, rfl⟩
    exact C.apply_Bt x hx v hv
  · refine ⟨((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v, C.apply_Bt _ (C.Xbar.inv_mem hx) v hv, ?_⟩
    exact apply_inv_apply x v

@[expose] noncomputable def resAt : C.Xbar →* (C.At ≃ₗ[ZMod 2] C.At) where
  toFun x := LinearEquiv.ofSubmodules (x : S.Qt ≃ₗ[ZMod 2] S.Qt) C.At C.At (C.map_eq_At x.2)
  map_one' := LinearEquiv.ext fun _ => rfl
  map_mul' _ _ := LinearEquiv.ext fun _ => rfl

@[expose] noncomputable def resBt : C.Xbar →* (C.Bt ≃ₗ[ZMod 2] C.Bt) where
  toFun x := LinearEquiv.ofSubmodules (x : S.Qt ≃ₗ[ZMod 2] S.Qt) C.Bt C.Bt (C.map_eq_Bt x.2)
  map_one' := LinearEquiv.ext fun _ => rfl
  map_mul' _ _ := LinearEquiv.ext fun _ => rfl

theorem resAt_apply (x : C.Xbar) (v : C.At) :
    ((C.resAt x v : C.At) : S.Qt) = ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v := rfl

theorem resBt_apply (x : C.Xbar) (v : C.Bt) :
    ((C.resBt x v : C.Bt) : S.Qt) = ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v := rfl

theorem resAt_injective : Function.Injective C.resAt := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  refine Subtype.ext (C.eq_one_of_forall_At x.2 fun v hv => ?_)
  have := congrArg (fun e : C.At ≃ₗ[ZMod 2] C.At => ((e ⟨v, hv⟩ : C.At) : S.Qt)) hx
  exact this

theorem resBt_injective : Function.Injective C.resBt := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  refine Subtype.ext (C.eq_one_of_forall_Bt x.2 fun v hv => ?_)
  have := congrArg (fun e : C.Bt ≃ₗ[ZMod 2] C.Bt => ((e ⟨v, hv⟩ : C.Bt) : S.Qt)) hx
  exact this

instance finite_linearEquiv (W : Submodule (ZMod 2) S.Qt) : Finite (W ≃ₗ[ZMod 2] W) :=
  Finite.of_injective (fun e : W ≃ₗ[ZMod 2] W => (e : W → W)) fun _ _ h => LinearEquiv.ext
    (congrFun h)

theorem resAt_bijective : Function.Bijective C.resAt := by
  refine C.resAt_injective.bijective_of_nat_card_le ?_
  rw [CFSG.GroupTheory.GLnTwoSplitting.card_linearEquiv_eq C.finrank_At, C.card_Xbar]

theorem resBt_bijective : Function.Bijective C.resBt := by
  refine C.resBt_injective.bijective_of_nat_card_le ?_
  rw [CFSG.GroupTheory.GLnTwoSplitting.card_linearEquiv_eq C.finrank_Bt, C.card_Xbar]

end Config

end CFSG.LargeExtraspecial.GLR
