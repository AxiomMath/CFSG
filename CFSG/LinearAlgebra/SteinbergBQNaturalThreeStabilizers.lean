module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import CFSG.LinearAlgebra.BinaryReflectionNormalizer
public import Mathlib.FieldTheory.Finiteness

public noncomputable section

namespace CFSG.LinearAlgebra

open Module

theorem nq_two_natural_three_space_stabilizers {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (hV : finrank (ZMod 2) V = 3) {d : ℕ} (hd : d = 1 ∨ d = 2) (v : Fin d → V) :
    ∃ B : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V),
      (∀ g ∈ B, ∀ i, (g : V →ₗ[ZMod 2] V) (v i) = v i) ∧ IsElementaryAbelian 2 B ∧
        Nat.card B = 4 := by
  classical
  have : FiniteDimensional (ZMod 2) V := Module.finite_of_finrank_pos (by omega)
  set A := Submodule.span (ZMod 2) (Set.range v) with hA
  have hAdim : finrank (ZMod 2) A ≤ 2 := by
    have := finrank_span_le_card (R := ZMod 2) (Set.range v)
    rw [← hA] at this
    have h2 : (Set.range v).toFinset.card ≤ d := by
      rw [Set.toFinset_range]
      exact Finset.card_image_le.trans (by rw [Finset.card_univ, Fintype.card_fin])
    omega
  have step : ∀ X : Submodule (ZMod 2) V, finrank (ZMod 2) X < 3 →
      ∃ X' : Submodule (ZMod 2) V, X ≤ X' ∧ finrank (ZMod 2) X' = finrank (ZMod 2) X + 1 := by
    intro X hX
    obtain ⟨x, hx⟩ : ∃ x, x ∉ X := by
      by_contra h
      push Not at h
      have htop : X = ⊤ := eq_top_iff.2 fun y _ => h y
      rw [htop, finrank_top] at hX
      omega
    have hx0 : x ≠ 0 := fun h => hx (h ▸ X.zero_mem)
    refine ⟨X ⊔ Submodule.span (ZMod 2) {x}, le_sup_left, ?_⟩
    have hdisj : X ⊓ Submodule.span (ZMod 2) {x} = ⊥ := by
      rw [eq_bot_iff]
      rintro y ⟨hyX, hyx⟩
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hyx
      rw [Submodule.mem_bot]
      by_cases hc : c = 0
      · rw [hc, zero_smul]
      · exfalso
        apply hx
        have := X.smul_mem c⁻¹ hyX
        rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
    have h := Submodule.finrank_sup_add_finrank_inf_eq X (Submodule.span (ZMod 2) {x})
    rw [hdisj, finrank_bot, add_zero, finrank_span_singleton hx0] at h
    exact h
  obtain ⟨W, hAW, hW⟩ : ∃ W : Submodule (ZMod 2) V, A ≤ W ∧ finrank (ZMod 2) W = 2 := by
    rcases (by omega : finrank (ZMod 2) A = 0 ∨ finrank (ZMod 2) A = 1 ∨
        finrank (ZMod 2) A = 2) with h0 | h1 | h2
    · obtain ⟨X, hAX, hX⟩ := step A (by omega)
      obtain ⟨Y, hXY, hY⟩ := step X (by omega)
      exact ⟨Y, hAX.trans hXY, by omega⟩
    · obtain ⟨X, hAX, hX⟩ := step A (by omega)
      exact ⟨X, hAX, by omega⟩
    · exact ⟨A, le_rfl, h2⟩
  have hWtop : W < ⊤ := lt_top_iff_ne_top.2 fun h => by
    rw [h, finrank_top] at hW
    omega
  obtain ⟨f, hf0, hfW⟩ := W.exists_dual_map_eq_bot_of_lt_top hWtop inferInstance
  have hfw : ∀ w ∈ W, f w = 0 := fun w hw => by
    have : f w ∈ W.map f := Submodule.mem_map_of_mem hw
    rwa [hfW, Submodule.mem_bot] at this
  let tv : W → Module.End (ZMod 2) V := fun w => 1 + f.smulRight (w : V)
  have htv : ∀ w x, tv w x = x + f x • (w : V) := fun w x => rfl
  have htvmul : ∀ w w', tv w * tv w' = tv (w + w') := fun w w' => LinearMap.ext fun x => by
    rw [Module.End.mul_apply, htv, htv, htv, map_add, map_smul, hfw _ w'.2, smul_eq_mul,
      mul_zero, add_zero, Submodule.coe_add, smul_add]
    abel
  have htv0 : tv 0 = 1 := LinearMap.ext fun x => by
    rw [htv, Submodule.coe_zero, smul_zero, add_zero, Module.End.one_apply]
  have htvsq : ∀ w, tv w * tv w = 1 := fun w => by
    rw [htvmul, show w + w = 0 from by
      ext
      exact (zmod2_vec_add_self (w : V)), htv0]
  let φ : Multiplicative W →* LinearMap.GeneralLinearGroup (ZMod 2) V :=
    { toFun := fun w => ⟨tv w.toAdd, tv w.toAdd, htvsq _, htvsq _⟩
      map_one' := Units.ext htv0
      map_mul' := fun w w' => Units.ext (htvmul w.toAdd w'.toAdd).symm }
  have hφ : ∀ w x, ((φ w : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) x =
      x + f x • ((Multiplicative.toAdd w : W) : V) := fun w x => rfl
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro w hw
    obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
      by_contra h
      push Not at h
      exact hf0 (LinearMap.ext h)
    have h1 := congrArg (fun g : LinearMap.GeneralLinearGroup (ZMod 2) V =>
      (g : V →ₗ[ZMod 2] V) x) hw
    simp only [hφ, Units.val_one, Module.End.one_apply, add_eq_left] at h1
    have h2 := (smul_eq_zero.1 h1).resolve_left hx
    have h3 : Multiplicative.toAdd w = 0 := Subtype.ext h2
    exact h3
  refine ⟨φ.range, ?_, ?_, ?_⟩
  · rintro _ ⟨w, rfl⟩ i
    rw [hφ, hfw _ (hAW (Submodule.subset_span ⟨i, rfl⟩)), zero_smul, add_zero]
  · have hcomm : ∀ a b : φ.range, a * b = b * a := by
      rintro ⟨_, ⟨w, rfl⟩⟩ ⟨_, ⟨w', rfl⟩⟩
      refine Subtype.ext ?_
      change φ w * φ w' = φ w' * φ w
      rw [← map_mul, ← map_mul, mul_comm]
    refine { is_comm := ⟨hcomm⟩, exponent_dvd_p := ?_ }
    refine Monoid.exponent_dvd_of_forall_pow_eq_one fun a => ?_
    obtain ⟨_, ⟨w, rfl⟩⟩ := a
    refine Subtype.ext ?_
    change φ w ^ 2 = 1
    rw [← map_pow, pow_two]
    have : w * w = 1 := by
      change Multiplicative.ofAdd (Multiplicative.toAdd w + Multiplicative.toAdd w) = 1
      rw [show Multiplicative.toAdd w + Multiplicative.toAdd w = 0 from by
        ext
        exact zmod2_vec_add_self _]
      rfl
    rw [this, map_one]
  · have : Finite V := Module.finite_of_finite (ZMod 2)
    rw [← Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv]
    change Nat.card W = 4
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hW]
    norm_num

end CFSG.LinearAlgebra
