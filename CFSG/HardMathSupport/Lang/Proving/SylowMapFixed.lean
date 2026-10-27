module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.HardMathSupport.Lang.Proving

theorem exists_sylow_map_eq_of_pow_three {G : Type*} [Group G] [Finite G] (u : MulAut G)
    (hu : u ^ 3 = 1) :
    ∃ S : Sylow 3 G, (S : Subgroup G).map u.toMonoidHom = (S : Subgroup G) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (Sylow 3 G) :=
    Finite.of_injective (fun P : Sylow 3 G => (P : Set G))
      (fun P Q h => Sylow.ext (SetLike.coe_injective h))
  have : Fintype (Sylow 3 G) := Fintype.ofFinite _
  have hsurj : Function.Surjective u.toMonoidHom := fun x => ⟨u.symm x, by simp⟩
  let f : Function.End (Sylow 3 G) := fun P => Sylow.mapSurjective hsurj P
  have hcomp : (u.toMonoidHom.comp u.toMonoidHom).comp u.toMonoidHom = MonoidHom.id G := by
    ext x
    have h := congrArg (fun w : MulAut G => w x) hu
    simpa [pow_three, MulAut.mul_apply] using h
  have hPow : ∀ P : Sylow 3 G, f (f (f P)) = P := by
    intro P
    apply Sylow.ext
    show (((P : Subgroup G).map u.toMonoidHom).map u.toMonoidHom).map u.toMonoidHom
      = (P : Subgroup G)
    rw [Subgroup.map_map, Subgroup.map_map, hcomp, Subgroup.map_id]
  have hf3 : f ^ 3 = 1 := by
    funext P
    exact hPow P
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 3) (n := 1) (f := f)
    (by rw [pow_one]; exact hf3)
  have h1 := card_sylow_modEq_one (p := 3) (G := G)
  have hpos : 0 < Fintype.card f.fixedPoints := by
    rcases Nat.eq_zero_or_pos (Fintype.card f.fixedPoints) with h0 | h0
    · exfalso
      rw [h0] at hmod
      rw [Nat.card_eq_fintype_card] at h1
      unfold Nat.ModEq at hmod h1
      omega
    · exact h0
  obtain ⟨⟨P, hP⟩⟩ := Fintype.card_pos_iff.mp hpos
  have hfix : f P = P := hP
  exact ⟨P, congrArg (fun Q : Sylow 3 G => (Q : Subgroup G)) hfix⟩

end CFSG.HardMathSupport.Lang.Proving
