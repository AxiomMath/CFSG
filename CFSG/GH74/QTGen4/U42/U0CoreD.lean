module

public import CFSG.GH74.QTGen4.U42.U0CoreC
public meta import CFSG.GH74.QTGen4.U42.U0CoreC
public meta import CFSG.Quasithin.H13.A5Setting
public meta import CFSG.Quasithin.Background.G2A5
public meta import Mathlib.GroupTheory.SemidirectProduct

public section

namespace CFSG.GH74.QTGen4.U42

open CFSG.Quasithin.A5Model CFSG.QuasithinUnique CFSG.Quasithin.H13.A5 Subgroup

def mulClo (L : Finset W5) (S : Finset W5) : Finset W5 :=
  S ∪ ((S ×ˢ L).image fun p => p.1 * p.2)

def cloIter (L : Finset W5) : ℕ → Finset W5
  | 0 => {1}
  | n + 1 => mulClo L (cloIter L n)

def orbitA4 (u : W5) : Finset W5 :=
  ((Finset.univ : Finset (Equiv.Perm (Fin 5))).filter
    (fun σ => σ.sign = 1 ∧ σ 4 = 4)).image (fun σ => pact σ u)

theorem span_check : ∀ u : W5, c4 u ≠ 1 → (cloIter (orbitA4 u) 4).card = 16 := by
  decide +kernel

theorem mem_cloIter_of_c4 {u : W5} (hc : c4 u ≠ 1) (w : W5) :
    w ∈ cloIter (orbitA4 u) 4 := by
  have hcard : (cloIter (orbitA4 u) 4).card = Fintype.card W5 := by
    rw [span_check u hc, ← Nat.card_eq_fintype_card, CFSG.Quasithin.H13.A5.card_W5]
  rw [Finset.eq_univ_of_card (cloIter (orbitA4 u) 4) hcard]
  exact Finset.mem_univ w

theorem cloIter_mem {X : Subgroup Mc} (L : Finset W5)
    (hL : ∀ x ∈ L, (SemidirectProduct.inl x : Mc) ∈ X) :
    ∀ n : ℕ, ∀ x ∈ cloIter L n, (SemidirectProduct.inl x : Mc) ∈ X := by
  intro n
  induction n with
  | zero =>
    intro x hx
    rw [cloIter, Finset.mem_singleton] at hx
    subst hx
    rw [map_one]
    exact X.one_mem
  | succ n ih =>
    intro x hx
    rw [cloIter, mulClo, Finset.mem_union, Finset.mem_image] at hx
    rcases hx with hx | ⟨⟨a, b⟩, hab, rfl⟩
    · exact ih x hx
    · rw [Finset.mem_product] at hab
      rw [map_mul]
      exact X.mul_mem (ih a hab.1) (hL b hab.2)

theorem orbitA4_mem {X : Subgroup Mc} (hXB : ∀ b ∈ Bc, ∀ x ∈ X, b * x * b⁻¹ ∈ X) {u : W5}
    (hu : (SemidirectProduct.inl u : Mc) ∈ X) :
    ∀ x ∈ orbitA4 u, (SemidirectProduct.inl x : Mc) ∈ X := by
  intro x hx
  rw [orbitA4, Finset.mem_image] at hx
  obtain ⟨σ, hσ, rfl⟩ := hx
  rw [Finset.mem_filter] at hσ
  exact conj_inl_mem_of_B hXB hσ.2.1 hσ.2.2 hu

attribute [local irreducible] cloIter orbitA4

theorem inl_mem_of_c4 {X : Subgroup Mc} (hXB : ∀ b ∈ Bc, ∀ x ∈ X, b * x * b⁻¹ ∈ X) {u : W5}
    (hu : (SemidirectProduct.inl u : Mc) ∈ X) (hc : c4 u ≠ 1) (w : W5) :
    (SemidirectProduct.inl w : Mc) ∈ X := by
  have hL : ∀ x ∈ orbitA4 u, (SemidirectProduct.inl x : Mc) ∈ X := orbitA4_mem hXB hu
  have hw : w ∈ cloIter (orbitA4 u) 4 := mem_cloIter_of_c4 (u := u) hc w
  exact cloIter_mem (orbitA4 u) hL 4 w hw

theorem wc_le_of_c4_ne_one {X : Subgroup Mc} (hXB : ∀ b ∈ Bc, ∀ x ∈ X, b * x * b⁻¹ ∈ X) {u : W5}
    (hu : (SemidirectProduct.inl u : Mc) ∈ X) (hc : c4 u ≠ 1) : Wc ≤ X := by
  rintro _ ⟨w, rfl⟩
  exact inl_mem_of_c4 hXB hu hc w

end CFSG.GH74.QTGen4.U42
