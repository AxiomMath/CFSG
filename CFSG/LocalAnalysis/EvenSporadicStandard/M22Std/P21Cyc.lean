module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.P21Field
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.P21FieldA

public section

namespace CFSG.EvenSporadicStandard.M22Std.P21Field

open Module

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem exists_cyclic_subspace (f : V →ₗ[ZMod 2] V) {ℓ : ℕ} (hℓ : ℓ.Prime) (hodd : Odd ℓ)
    (hf : f ^ ℓ = 1) (hne : f ≠ 1) :
    ∃ (S : Submodule (ZMod 2) V) (hS : ∀ s ∈ S, f s ∈ S), S ≠ ⊥ ∧ S ≤ LinearMap.range (f - 1) ∧
      (∀ W : Submodule (ZMod 2) V, W ≤ S → Inv f W → W = ⊥ ∨ W = S) ∧
      Irr (f.restrict hS) ∧ f.restrict hS ≠ 1 ∧ ℓ ∣ 2 ^ finrank (ZMod 2) S - 1 := by
  obtain ⟨S, hSne, hSr, hSinv, hmin, s₀, hs₀, hfs₀⟩ := exists_minimal_invariant f hodd hf hne
  refine ⟨S, hSinv, hSne, hSr, hmin, ?_⟩
  have hnt : Nontrivial S := Submodule.nontrivial_iff_ne_bot.2 hSne
  have hirr : Irr (f.restrict hSinv) := by
    refine ⟨hnt, fun W' hW' => ?_⟩
    have hW : Inv f (W'.map S.subtype) := by
      rintro _ ⟨w, hw, rfl⟩
      exact ⟨f.restrict hSinv w, hW' w hw, rfl⟩
    rcases hmin _ (Submodule.map_subtype_le S W') hW with h | h
    · left
      exact Submodule.map_injective_of_injective S.injective_subtype
        (h.trans (Submodule.map_bot _).symm)
    · right
      refine Submodule.map_injective_of_injective S.injective_subtype ?_
      rw [h, Submodule.map_subtype_top]
  have hne' : f.restrict hSinv ≠ 1 := by
    intro h
    apply hfs₀
    have := congrArg (fun T => (T ⟨s₀, hs₀⟩ : V)) h
    rw [LinearMap.coe_restrict_apply] at this
    exact this
  refine ⟨hirr, hne', ?_⟩
  letI : Field (K (f.restrict hSinv)) := fieldK hirr
  have hfinEnd : Finite (Module.End (ZMod 2) S) :=
    Finite.of_injective (fun f : Module.End (ZMod 2) S => (f : S → S)) DFunLike.coe_injective
  have hfinK : Finite (K (f.restrict hSinv)) :=
    Finite.of_injective (fun a : K (f.restrict hSinv) => (a : Module.End (ZMod 2) S))
      Subtype.val_injective
  set a : K (f.restrict hSinv) := ⟨f.restrict hSinv, g_mem_K _⟩ with ha
  have hapow : a ^ ℓ = 1 := by
    apply Subtype.ext
    show (f.restrict hSinv) ^ ℓ = 1
    have hpowrest : ∀ (n : ℕ) (v : S), (((f.restrict hSinv) ^ n) v : V) = (f ^ n) v := by
      intro n
      induction n with
      | zero => intro v; simp
      | succ n ih =>
        intro v
        rw [pow_succ, Module.End.mul_apply, pow_succ, Module.End.mul_apply, ih]
        rfl
    ext v
    rw [hpowrest, hf]
    rfl
  have ha1 : a ≠ 1 := fun h => hne' (congrArg Subtype.val h)
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, zero_pow hℓ.ne_zero] at hapow
    exact zero_ne_one hapow
  have hord : orderOf a = ℓ := by
    have hd : orderOf a ∣ ℓ := orderOf_dvd_of_pow_eq_one hapow
    rcases (Nat.dvd_prime hℓ).1 hd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) ha1
    · exact h
  have hdvd : orderOf (Units.mk0 a ha0) ∣ Nat.card (K (f.restrict hSinv))ˣ :=
    orderOf_dvd_natCard _
  have hordu : orderOf (Units.mk0 a ha0) = ℓ := by
    rw [← orderOf_units, Units.val_mk0]
    exact hord
  rw [hordu] at hdvd
  have hc : Nat.card (K (f.restrict hSinv)) = 2 ^ finrank (ZMod 2) S := by
    rw [card_K hirr, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have hunits : Nat.card (K (f.restrict hSinv))ˣ = Nat.card (K (f.restrict hSinv)) - 1 := by
    classical
    have := Fintype.ofFinite (K (f.restrict hSinv))
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_units]
  rwa [hunits, hc] at hdvd

end CFSG.EvenSporadicStandard.M22Std.P21Field
