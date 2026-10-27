module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.GroupTheory.WeirSylow

variable {p : ℕ} [Fact p.Prime] {G H : Type*} [Group G] [Group H]

theorem nonempty_sylow_mulEquiv_of_injective [Finite G] (φ : H →* G)
    (hφ : Function.Injective φ) (hH : Nat.card H = p ^ (Nat.card G).factorization p)
    (P : Sylow p G) : Nonempty (P ≃* H) := by
  have hR : Nat.card φ.range = p ^ (Nat.card G).factorization p := by
    rw [← hH]
    exact Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv.symm
  exact ⟨(Sylow.equiv P (Sylow.ofCard φ.range hR)).trans (MonoidHom.ofInjective hφ).symm⟩

theorem nonempty_sylow_mulEquiv_sylow_of_injective [Finite G] (φ : H →* G)
    (hφ : Function.Injective φ)
    (h : (Nat.card H).factorization p = (Nat.card G).factorization p) (P : Sylow p G)
    (P' : Sylow p H) : Nonempty (P ≃* P') := by
  have : Finite H := Finite.of_injective φ hφ
  have hcard : Nat.card (P'.1.map φ) = p ^ (Nat.card G).factorization p := by
    rw [Subgroup.card_map_of_injective hφ, P'.card_eq_multiplicity, h]
  exact ⟨(Sylow.equiv P (Sylow.ofCard _ hcard)).trans
    (Subgroup.equivMapOfInjective P'.1 φ hφ).symm⟩

theorem nonempty_sylow_mulEquiv_sylow_of_mulEquiv [Finite G] (e : H ≃* G) (P : Sylow p G)
    (P' : Sylow p H) : Nonempty (P ≃* P') :=
  nonempty_sylow_mulEquiv_sylow_of_injective e.toMonoidHom e.injective
    (by rw [Nat.card_congr e.toEquiv]) P P'

end CFSG.GroupTheory.WeirSylow
