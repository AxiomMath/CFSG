module

public import Mathlib.Algebra.Module.ZMod
public import CFSG.HardMathSupport.Curtis.Proving.FixedPointFreeZmod

public section

namespace CFSG.HardMathSupport.Curtis.Proving

theorem addSubgroup_invariant_core {p r : ℕ} [hp : Fact p.Prime] [hr : Fact r.Prime]
    (hdvd : r ∣ p ^ 2 + 1) (hndvd : ¬ r ∣ p ^ 2 - 1)
    {A : Type*} [AddCommGroup A] [Module (ZMod p) A] [Module.Finite (ZMod p) A]
    (hsmul : ∀ (z : ZMod p) (x : A), z • x = z.val • x) (hcard : Nat.card A = p ^ 4)
    (φ : A ≃+ A) (k : ℕ) (hk : φ^[r ^ k] = id) (hne : ∃ a : A, φ a ≠ a)
    (B : AddSubgroup A) (hB : ∀ b ∈ B, φ b ∈ B) :
    B = ⊥ ∨ B = ⊤ := by
  obtain ⟨c, hcoe⟩ : ∃ c : A ≃ₗ[ZMod p] A, ⇑c = ⇑φ :=
    ⟨LinearEquiv.ofBijective ((φ : A →+ A).toZModLinearMap p) ⟨φ.injective, φ.surjective⟩, rfl⟩
  have hit : ⇑(c ^ (r ^ k)) = id := by
    rw [LinearEquiv.coe_pow, hcoe]
    exact hk
  have hcpow : ∃ m : ℕ, c ^ (r ^ m) = 1 :=
    ⟨k, LinearEquiv.ext fun x => congrFun hit x⟩
  have hne' : c ≠ 1 := by
    intro h
    obtain ⟨a, ha⟩ := hne
    apply ha
    have h2 : c a = a := by rw [h]; rfl
    rw [← congrFun hcoe a]
    exact h2
  have hV : Module.finrank (ZMod p) A = 4 := by
    have h := natCard_eq_pow_finrank_zmod (U := A) p
    rw [hcard] at h
    exact Nat.pow_right_injective hp.out.two_le h.symm
  let W : Submodule (ZMod p) A :=
    { carrier := (B : Set A)
      add_mem' := fun {x y} hx hy => B.add_mem hx hy
      zero_mem' := B.zero_mem
      smul_mem' := fun z x hx => by
        rw [hsmul]
        exact B.nsmul_mem hx _ }
  have hW : ∀ w ∈ W, c w ∈ W := fun w hw => by
    show c w ∈ B
    rw [congrFun hcoe w]
    exact hB w hw
  rcases invariant_subspace_eq_bot_or_top hdvd hndvd hV c hcpow hne' W hW with h | h
  · left
    ext x
    have hx := SetLike.ext_iff.mp h x
    simpa [W] using hx
  · right
    ext x
    have hx := SetLike.ext_iff.mp h x
    simpa [W] using hx

theorem addSubgroup_invariant_bot_or_top {p r : ℕ} [hp : Fact p.Prime] [hr : Fact r.Prime]
    (hdvd : r ∣ p ^ 2 + 1) (hndvd : ¬ r ∣ p ^ 2 - 1)
    {A : Type*} [AddCommGroup A] (hexp : ∀ a : A, p • a = 0) (hcard : Nat.card A = p ^ 4)
    (φ : A ≃+ A) (k : ℕ) (hk : φ^[r ^ k] = id) (hne : ∃ a : A, φ a ≠ a)
    (B : AddSubgroup A) (hB : ∀ b ∈ B, φ b ∈ B) :
    B = ⊥ ∨ B = ⊤ := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  let hmod : Module (ZMod p) A := AddCommGroup.zmodModule hexp
  have : Finite A := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 4 hp.out.ne_zero)
  have hsmul : ∀ (z : ZMod p) (x : A), z • x = z.val • x := fun z x => by
    rw [← Nat.cast_smul_eq_nsmul (ZMod p) z.val x, ZMod.natCast_zmod_val]
  have hfin : Module.Finite (ZMod p) A := Module.Finite.of_finite (R := ZMod p) (M := A)
  exact @addSubgroup_invariant_core p r _ _ hdvd hndvd A _ hmod hfin hsmul hcard φ k hk hne B hB

end CFSG.HardMathSupport.Curtis.Proving

end
