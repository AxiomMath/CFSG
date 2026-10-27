
module

public import CFSG.GH74.E2.SD16Cert
public meta import Mathlib
public import CFSG.GH74.E2.D8CertInputs
public meta import CFSG.GH74.E2.D8CertInputs

@[expose] public section

namespace CFSG.GH74.E2

section Relations

variable {M : Type*} [Group M]

theorem d8relA_aut (ψ : MulAut M) {a b : M} (h : D8RelA a b) : D8RelA (ψ a) (ψ b) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_pow, h1, map_one]
  · rw [← map_pow, h2, map_one]
  · simpa using congrArg ψ h3
  · intro h
    apply h4
    apply ψ.injective
    rw [map_pow, h, map_one]
  · intro h
    apply h5
    apply ψ.injective
    rw [h, map_one]

end Relations

section Certificate

variable (m : ℕ)

section Decidability

variable [NeZero m]

instance d8decRelA (a b : D8M × QuaternionGroup m) : Decidable (D8RelA a b) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

instance d8decRelB (a b c : D8M × QuaternionGroup m) : Decidable (RelB m a b c) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

instance d8decRelC (a b c d : D8M × QuaternionGroup m) : Decidable (RelC m a b c d) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

instance d8decCentralPow (c : D8M × QuaternionGroup m) : Decidable (D8CentralPow m c) :=
  inferInstanceAs (Decidable (∀ y : D8M × QuaternionGroup m, y * c ^ m = c ^ m * y))

instance d8decSearch4 (a b c : D8M × QuaternionGroup m) : Decidable (D8Search4 m a b c) :=
  inferInstanceAs (Decidable (∀ d : D8M × QuaternionGroup m, RelC m a b c d → False))

instance d8decSearch3 (t₀ a b : D8M × QuaternionGroup m) : Decidable (D8Search3 m t₀ a b) :=
  inferInstanceAs (Decidable (∀ c : D8M × QuaternionGroup m, RelB m a b c → D8CentralPow m c →
    c ^ m ≠ t₀ → D8Search4 m a b c))

instance d8decSearch2 (t₀ a : D8M × QuaternionGroup m) : Decidable (D8Search2 m t₀ a) :=
  inferInstanceAs (Decidable (∀ b : D8M × QuaternionGroup m, D8RelA a b → D8Search3 m t₀ a b))

instance d8decSearchOK (t₀ : D8M × QuaternionGroup m) : Decidable (D8SearchOK m t₀) :=
  inferInstanceAs (Decidable (∀ a : D8M × QuaternionGroup m, a ^ 4 = 1 → D8Search2 m t₀ a))

end Decidability

theorem fix_of_search_D8 (a b c d : D8M × QuaternionGroup m) (hA : D8RelA a b)
    (hB : RelB m a b c) (hC : RelC m a b c d) (hsearch : D8SearchOK m (c ^ m)) :
    ∀ ψ : MulAut (D8M × QuaternionGroup m), ψ (c ^ m) ∈ Subgroup.center _ →
      ψ (c ^ m) = c ^ m := by
  refine fix_of_cert4 a b c d (fun a b c d => D8RelA a b ∧ RelB m a b c ∧ RelC m a b c d)
    (fun ψ a b c d h => ⟨d8relA_aut ψ h.1, relB_aut m ψ h.2.1, relC_aut m ψ h.2.2⟩)
    ⟨hA, hB, hC⟩ (fun _ _ c _ => c ^ m) (fun ψ a b c d => by simp [map_pow]) ?_
  intro a' b' c' d' hR hcent
  by_contra hne
  obtain ⟨hA', hB', hC'⟩ := hR
  have hc : D8CentralPow m c' := Subgroup.mem_center_iff.1 hcent
  exact hsearch a' hA'.1 b' hA' c' hB' hc hne d' hC'

end Certificate

section Instances

@[expose] def d8x (m : ℕ) [NeZero m] : D8M × QuaternionGroup m := (DihedralGroup.r 1, 1)

@[expose] def d8y (m : ℕ) [NeZero m] : D8M × QuaternionGroup m := (DihedralGroup.sr 0, 1)

@[expose] def d8d (m : ℕ) [NeZero m] : D8M × QuaternionGroup m := (1, QuaternionGroup.xa 0)

theorem d8relA_Q8 : D8RelA (d8x 2) (d8y 2) := by
  unfold D8RelA d8x d8y
  decide

theorem d8relB_Q8 : RelB 2 (d8x 2) (d8y 2) (d8c 2) := by
  unfold RelB d8x d8y d8c
  decide

theorem d8relC_Q8 : RelC 2 (d8x 2) (d8y 2) (d8c 2) (d8d 2) := by
  unfold RelC d8x d8y d8c d8d
  decide

theorem d8relA_Q16 : D8RelA (d8x 4) (d8y 4) := by
  unfold D8RelA d8x d8y
  decide

theorem d8relB_Q16 : RelB 4 (d8x 4) (d8y 4) (d8c 4) := by
  unfold RelB d8x d8y d8c
  decide

theorem d8relC_Q16 : RelC 4 (d8x 4) (d8y 4) (d8c 4) (d8d 4) := by
  unfold RelC d8x d8y d8c d8d
  decide

end Instances

end CFSG.GH74.E2
