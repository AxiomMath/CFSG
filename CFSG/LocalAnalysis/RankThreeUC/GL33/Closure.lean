module

public import Certificates.Data.GL33.Code
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.GL33

open CFSG.GL33.Native Subgroup

theorem mem_normalizer_of_conj {X : Type*} [Group X] [Finite X] {s : Set X} {n : X}
    (h : ∀ k ∈ s, n * k * n⁻¹ ∈ Subgroup.closure s) :
    n ∈ normalizer (Subgroup.closure s : Set X) := by
  set H := Subgroup.closure s
  have hle : H.map (MulAut.conj n).toMonoidHom ≤ H := by
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    exact h k hk
  have hcard : Nat.card ↥(H.map (MulAut.conj n).toMonoidHom) = Nat.card H :=
    Subgroup.card_map_of_injective (MulAut.conj n).injective
  have heq : H.map (MulAut.conj n).toMonoidHom = H :=
    Subgroup.eq_of_le_of_card_ge hle hcard.ge
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    rw [← heq]
    exact ⟨g, hg, rfl⟩
  · intro hg
    rw [← heq] at hg
    obtain ⟨g', hg', e⟩ := hg
    have : g' = g := by simpa using e
    rwa [← this]

section Conj

variable {X : Type*} [Group X]

theorem map_conj_eq_of_mem_normalizer {H : Subgroup X} {n : X}
    (hn : n ∈ normalizer (H : Set X)) : H.map (MulAut.conj n).toMonoidHom = H := by
  ext h
  rw [Subgroup.mem_normalizer_iff] at hn
  constructor
  · rintro ⟨h', hh', rfl⟩
    exact (hn h').1 hh'
  · intro hh
    refine ⟨n⁻¹ * h * n, ?_, by simp [mul_assoc]⟩
    apply (hn (n⁻¹ * h * n)).2
    simpa [mul_assoc] using hh

theorem map_conj_map_conj (H : Subgroup X) (g g' : X) :
    (H.map (MulAut.conj g').toMonoidHom).map (MulAut.conj g).toMonoidHom =
      H.map (MulAut.conj (g * g')).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [mul_assoc]

theorem map_conj_one (H : Subgroup X) : H.map (MulAut.conj (1 : X)).toMonoidHom = H :=
  map_conj_eq_of_mem_normalizer (one_mem _)

theorem conj_conj_inv_apply (g σ : X) : MulAut.conj g ((MulAut.conj g)⁻¹ σ) = σ := by
  simp [mul_assoc]

end Conj

end CFSG.GL33

end
