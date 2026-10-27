module

public import CFSG.LargeExtraspecial.GLRLinPair

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.GLR

open Subgroup Module QuadraticMap

theorem card_SL_eq_card_GL (n : ℕ) :
    Nat.card (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) = Nat.card (GL (Fin n) (ZMod 2)) := by
  refine Nat.card_congr (Equiv.ofBijective (fun x => Matrix.SpecialLinearGroup.toGL x) ⟨?_, ?_⟩)
  · intro x y hxy
    apply Subtype.ext
    have := congrArg (fun g : GL (Fin n) (ZMod 2) => (g : Matrix (Fin n) (Fin n) (ZMod 2))) hxy
    simpa using this
  · intro g
    have hdet : (g : Matrix (Fin n) (Fin n) (ZMod 2)).det = 1 := by
      have hu : IsUnit (g : Matrix (Fin n) (Fin n) (ZMod 2)).det :=
        (Matrix.isUnit_iff_isUnit_det _).mp g.isUnit
      rcases zmod2_eq_zero_or_one (g : Matrix (Fin n) (Fin n) (ZMod 2)).det with h | h
      · rw [h] at hu
        exact absurd hu not_isUnit_zero
      · exact h
    refine ⟨⟨g, hdet⟩, ?_⟩
    ext i j
    rfl

theorem card_linearEquiv {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] {n : ℕ} (hn : finrank (ZMod 2) V = n) :
    Nat.card (V ≃ₗ[ZMod 2] V) = Nat.card (GL (Fin n) (ZMod 2)) := by
  have e : V ≃ₗ[ZMod 2] (Fin n → ZMod 2) :=
    LinearEquiv.ofFinrankEq V (Fin n → ZMod 2) (by rw [hn, finrank_fin_fun])
  rw [← Nat.card_congr (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).toEquiv,
    Nat.card_congr (LinearMap.GeneralLinearGroup.congrLinearEquiv e).toEquiv,
    Nat.card_congr (Matrix.GeneralLinearGroup.toLin).toEquiv]

variable {G : Type*} [Group G] [Finite G] {S : Setting G}

namespace Pair

variable {X : Subgroup S.O} {A B : Submodule (ZMod 2) S.Qt}

@[expose] noncomputable def resA (h : Pair S X A B) (x : X) : A ≃ₗ[ZMod 2] A :=
  LinearEquiv.ofSubmodules ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) A A (h.map_A_eq x.2)

theorem resA_apply (h : Pair S X A B) (x : X) (a : A) :
    ((h.resA x a : A) : S.Qt) = ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) a := rfl

theorem resA_bijective (h : Pair S X A B) : Function.Bijective h.resA := by
  have hinj : Function.Injective h.resA := by
    intro x y hxy
    refine Subtype.ext (h.ext_of_eqOn x.2 y.2 fun a ha => ?_)
    have := congrArg (fun g : A ≃ₗ[ZMod 2] A => ((g ⟨a, ha⟩ : A) : S.Qt)) hxy
    simpa [resA_apply] using this
  have : Finite (A ≃ₗ[ZMod 2] A) :=
    Finite.of_injective (fun e : A ≃ₗ[ZMod 2] A => (e : A → A))
      (fun _ _ he => LinearEquiv.ext (congrFun he))
  refine hinj.bijective_of_nat_card_le ?_
  rw [card_linearEquiv h.finrank_A, h.card]

theorem exists_eqOn (h : Pair S X A B) (f : A ≃ₗ[ZMod 2] A) :
    ∃ x ∈ X, ∀ a : A, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) a = f a := by
  obtain ⟨x, hx⟩ := h.resA_bijective.2 f
  refine ⟨x, x.2, fun a => ?_⟩
  rw [← h.resA_apply, hx]

theorem exists_transvection (h : Pair S X A B) {u c : S.Qt} (hu : u ∈ A) (huc : polar S.q u c = 0) :
    ∃ x ∈ X, ∀ a ∈ A, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) a = a + polar S.q a c • u := by
  let f : A →ₗ[ZMod 2] A :=
    LinearMap.id + LinearMap.smulRight ((S.q.polarBilin.flip c).domRestrict A) ⟨u, hu⟩
  have hf : ∀ a : A, ((f a : A) : S.Qt) = a + polar S.q a c • u := fun _ => rfl
  have hinv : Function.Involutive f := by
    intro a
    apply Subtype.ext
    rw [hf, hf, polar_add_left, polar_smul_left, huc, smul_zero, add_zero, add_assoc,
      two_vec, add_zero]
  obtain ⟨x, hx, hxa⟩ := h.exists_eqOn (LinearEquiv.ofInvolutive f hinv)
  exact ⟨x, hx, fun a ha => (hxa ⟨a, ha⟩).trans (hf ⟨a, ha⟩)⟩

end Pair

end CFSG.LargeExtraspecial.GLR
