
module

public import CFSG.GH74.E2.AutCert
public import CFSG.CharacterTheory.Semidihedral.NormalForm
public meta import Mathlib
public meta import CFSG.CharacterTheory.Semidihedral.Model
public import CFSG.GH74.E2.SD16CertInputs
public meta import CFSG.GH74.E2.SD16CertInputs

@[expose] public section

namespace CFSG.GH74.E2

open CFSG.Semidihedral

instance : Fintype SD16M := Fintype.ofEquiv _ SemidirectProduct.equivProd.symm

section Relations

variable {M : Type*} [Group M]

theorem relA_aut (ψ : MulAut M) {a b : M} (h : RelA a b) : RelA (ψ a) (ψ b) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_pow, h1, map_one]
  · rw [← map_pow, h2, map_one]
  · rw [← map_inv, ← map_mul, ← map_mul, ← map_pow, h3]
  · intro h
    apply h4
    apply ψ.injective
    rw [map_pow, h, map_one]
  · intro h
    apply h5
    apply ψ.injective
    rw [h, map_one]

theorem relB_aut (m : ℕ) (ψ : MulAut M) {a b c : M} (h : RelB m a b c) :
    RelB m (ψ a) (ψ b) (ψ c) := by
  obtain ⟨h4, h5, h6, h7⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← map_pow, h4, map_one]
  · rw [← map_mul, ← map_mul, h5]
  · rw [← map_mul, ← map_mul, h6]
  · intro h
    apply h7
    apply ψ.injective
    rw [map_pow, h, map_one]

theorem relC_aut (m : ℕ) (ψ : MulAut M) {a b c d : M} (h : RelC m a b c d) :
    RelC m (ψ a) (ψ b) (ψ c) (ψ d) := by
  obtain ⟨h7, h8, h9, h10⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← map_pow, ← map_pow, h7]
  · rw [← map_inv, ← map_mul, ← map_mul, ← map_inv, h8]
  · rw [← map_mul, ← map_mul, h9]
  · rw [← map_mul, ← map_mul, h10]

end Relations

section Certificate

variable (m : ℕ)

section Decidability

variable [NeZero m]

instance (a b : SD16M × QuaternionGroup m) : Decidable (RelA a b) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

instance (a b c : SD16M × QuaternionGroup m) : Decidable (RelB m a b c) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

instance (a b c d : SD16M × QuaternionGroup m) : Decidable (RelC m a b c d) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

instance (c : SD16M × QuaternionGroup m) : Decidable (CentralPow m c) :=
  inferInstanceAs (Decidable (∀ y : SD16M × QuaternionGroup m, y * c ^ m = c ^ m * y))

instance (a b c : SD16M × QuaternionGroup m) : Decidable (Search4 m a b c) :=
  inferInstanceAs (Decidable (∀ d : SD16M × QuaternionGroup m, RelC m a b c d → False))

instance (t₀ a b : SD16M × QuaternionGroup m) : Decidable (Search3 m t₀ a b) :=
  inferInstanceAs (Decidable (∀ c : SD16M × QuaternionGroup m, RelB m a b c → CentralPow m c →
    c ^ m ≠ t₀ → Search4 m a b c))

instance (t₀ a : SD16M × QuaternionGroup m) : Decidable (Search2 m t₀ a) :=
  inferInstanceAs (Decidable (∀ b : SD16M × QuaternionGroup m, RelA a b → Search3 m t₀ a b))

instance (t₀ : SD16M × QuaternionGroup m) : Decidable (SearchOK m t₀) :=
  inferInstanceAs (Decidable (∀ a : SD16M × QuaternionGroup m, a ^ 8 = 1 → Search2 m t₀ a))

end Decidability

theorem fix_of_search (a b c d : SD16M × QuaternionGroup m) (hA : RelA a b) (hB : RelB m a b c)
    (hC : RelC m a b c d) (hsearch : SearchOK m (c ^ m)) :
    ∀ ψ : MulAut (SD16M × QuaternionGroup m), ψ (c ^ m) ∈ Subgroup.center _ →
      ψ (c ^ m) = c ^ m := by
  refine fix_of_cert4 a b c d (fun a b c d => RelA a b ∧ RelB m a b c ∧ RelC m a b c d)
    (fun ψ a b c d h => ⟨relA_aut ψ h.1, relB_aut m ψ h.2.1, relC_aut m ψ h.2.2⟩)
    ⟨hA, hB, hC⟩ (fun _ _ c _ => c ^ m) (fun ψ a b c d => by simp [map_pow]) ?_
  intro a' b' c' d' hR hcent
  by_contra hne
  obtain ⟨hA', hB', hC'⟩ := hR
  have hc : CentralPow m c' := Subgroup.mem_center_iff.1 hcent
  exact hsearch a' hA'.1 b' hA' c' hB' hc hne d' hC'

end Certificate

section Instances

end Instances

end CFSG.GH74.E2
