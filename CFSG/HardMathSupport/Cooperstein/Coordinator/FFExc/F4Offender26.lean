module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc.F4ModTwist
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc.F4SylowE6

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Chevalley
  Matrix

variable (K : Type) [Field K] [Finite K] [CharP K 2]

@[expose] def fix26 (k : ℕ) (A : Subgroup (adjointGroup Tag.F4 K)) : Submodule K (Idx26 → K) where
  carrier := {w | ∀ a ∈ A, m26Phi K k a w = w}
  add_mem' := fun hv hw a ha => by rw [map_add, hv a ha, hw a ha]
  zero_mem' := fun a _ => map_zero _
  smul_mem' := fun c v hv a ha => by rw [map_smul, hv a ha]

theorem f4Embed_phiPow (k : ℕ) (a : adjointGroup Tag.F4 K) :
    f4Embed K (phiF4 K ^ k) a = f4Embed K (idF4 K) ((phiF4 K ^ k) a) := rfl

theorem jExt_m26Phi (k : ℕ) (a : adjointGroup Tag.F4 K) (w : Idx26 → K) :
    jExt K (m26Phi K k a w) = e6Data_valid.endo K (f4Embed K (phiF4 K ^ k) a) (jExt K w) := by
  rw [m26Phi_apply, jExt_m26Rep, f4Embed_phiPow]

theorem natCard_fix26 (k : ℕ) (A : Subgroup (adjointGroup Tag.F4 K)) :
    Nat.card (fix26 K k A) =
      Nat.card ↥(fixSub e6Data_valid (A.map (f4Embed K (phiF4 K ^ k))) ⊓ M26 e6Data_valid K) := by
  refine Nat.card_congr (Equiv.ofBijective
    (fun w : fix26 K k A => (⟨jExt K w.1, ?_⟩ : ↥(fixSub e6Data_valid (A.map (f4Embed K (phiF4 K ^ k))) ⊓
      M26 e6Data_valid K))) ⟨?_, ?_⟩)
  · refine Submodule.mem_inf.2 ⟨?_, ?_⟩
    · rintro _ ⟨a, ha, rfl⟩
      have h := w.2 a ha
      change e6Data_valid.endo K (f4Embed K (phiF4 K ^ k) a) (jExt K w.1) = jExt K w.1
      rw [← jExt_m26Phi]
      exact congrArg (jExt K) h
    · rw [M26_eq_ker]; exact LinearMap.mem_ker.2 (fT_jExt K w.1)
  · intro v w h
    have h' : jExt K v.1 = jExt K w.1 := congrArg Subtype.val h
    exact Subtype.ext (jExt_injective K h')
  · rintro ⟨x, hx⟩
    have hxM : fT K x = 0 := by
      have := (Submodule.mem_inf.1 hx).2
      rw [M26_eq_ker] at this
      exact LinearMap.mem_ker.1 this
    refine ⟨⟨pRes K x, fun a ha => ?_⟩, Subtype.ext (jExt_pRes K x hxM)⟩
    have hfix := (Submodule.mem_inf.1 hx).1 (f4Embed K (phiF4 K ^ k) a) ⟨a, ha, rfl⟩
    apply jExt_injective K
    rw [jExt_m26Phi, jExt_pRes K x hxM]
    exact hfix

theorem f4_26_twist_offender_bound (k : ℕ)
    (H : ∀ A : Subgroup (e6Data_valid.minGroup K), A ≤ posU6 K → A ≠ ⊥ → (∀ a ∈ A, a ^ 2 = 1) →
      Nat.card A * Nat.card (fixSub e6Data_valid A) ≤ Nat.card K ^ 26 ∧
        Nat.card A ^ 2 * Nat.card (fixSub e6Data_valid A) ≤ Nat.card K ^ 42)
    {A : Subgroup (adjointGroup Tag.F4 K)} (hne : A ≠ ⊥) (hel : ∀ a ∈ A, a ^ 2 = 1) :
    Nat.card A * Nat.card (fix26 K k A) ≤ Nat.card K ^ 25 ∧
      Nat.card A ^ 2 * Nat.card (fix26 K k A) ≤ Nat.card K ^ 41 := by
  rw [natCard_fix26]
  exact f4_26_offender_bound_posU6 K H (phiF4 K ^ k) hne hel

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc
