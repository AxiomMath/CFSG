module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FCore
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FK1

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z : G} {A B : Subgroup G}
  {φ : (Fin 7 → ZMod 2) → G}

theorem Sec4FSetup.fiber_core (h : Sec4FSetup t L S z A B φ) {y x : G}
    (hy : ∃ g : G, y = g⁻¹ * t * g) (hyN : y ∈ normalizer (A : Set G))
    {a b : Option (Fin 7)} (hab : a ≠ b) (hσ : Sec4MRealizes t φ y (Equiv.swap a b))
    (hxA : x ∈ A) (hxy : x * y = y * x) (hyx : ∃ g : G, y * x = g⁻¹ * t * g) :
    x = 1 ∨ x = sec4MPt t φ a * sec4MPt t φ b := by
  obtain ⟨r, -, hr⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card
      (s := ({a, b} : Finset (Option (Fin 7)))) (t := Finset.univ)
      (by rw [Finset.card_pair hab]; decide)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hr
  obtain ⟨hra, hrb⟩ := hr
  obtain ⟨m, ν, hm, hν, hν0, hcomm, hreal, h6⟩ := h.k1_outer hy hyN hab hσ hra hrb
  have hνa : ν⁻¹ a ≠ none := by
    intro h0
    have : a = r := by
      calc a = ν (ν⁻¹ a) := (Equiv.apply_symm_apply ν a).symm
        _ = ν none := by rw [h0]
        _ = r := hν0
    exact hra this.symm
  have hνb : ν⁻¹ b ≠ none := by
    intro h0
    have : b = r := by
      calc b = ν (ν⁻¹ b) := (Equiv.apply_symm_apply ν b).symm
        _ = ν none := by rw [h0]
        _ = r := hν0
    exact hrb this.symm
  obtain ⟨i, hi⟩ := Option.ne_none_iff_exists'.mp hνa
  obtain ⟨j, hj⟩ := Option.ne_none_iff_exists'.mp hνb
  have hij : i ≠ j := by
    intro hij
    apply hab
    have h1 : ν (some i) = ν (some j) := by rw [hij]
    rw [← hi, ← hj] at h1
    simpa using h1
  have hμ : ∃ g : G, m⁻¹ * y * m = g⁻¹ * t * g := by
    obtain ⟨g, hg⟩ := hy
    exact ⟨g * m, by rw [hg]; group⟩
  have hμN : m⁻¹ * y * m ∈ normalizer (A : Set G) :=
    (normalizer (A : Set G)).mul_mem
      ((normalizer (A : Set G)).mul_mem ((normalizer (A : Set G)).inv_mem hm) hyN) hm
  have hμr' : Sec4MRealizes t φ (m⁻¹ * y * m) (Equiv.swap (some i) (some j)) := by
    rw [hi, hj] at hreal
    exact hreal
  have hx'A : m⁻¹ * x * m ∈ A := by
    have hfin := (Subgroup.mem_set_normalizer_iff.mp
      ((normalizer (A : Set G)).inv_mem hm) x).mp hxA
    simpa using hfin
  have hx'μ : (m⁻¹ * x * m) * (m⁻¹ * y * m) = (m⁻¹ * y * m) * (m⁻¹ * x * m) := by
    calc (m⁻¹ * x * m) * (m⁻¹ * y * m) = m⁻¹ * (x * y) * m := by group
      _ = m⁻¹ * (y * x) * m := by rw [hxy]
      _ = (m⁻¹ * y * m) * (m⁻¹ * x * m) := by group
  have hμx : ∃ g : G, (m⁻¹ * y * m) * (m⁻¹ * x * m) = g⁻¹ * t * g := by
    obtain ⟨g, hg⟩ := hyx
    refine ⟨g * m, ?_⟩
    calc (m⁻¹ * y * m) * (m⁻¹ * x * m) = m⁻¹ * (y * x) * m := by group
      _ = m⁻¹ * (g⁻¹ * t * g) * m := by rw [hg]
      _ = (g * m)⁻¹ * t * (g * m) := by group
  have hcore : m⁻¹ * x * m = 1 ∨
      m⁻¹ * x * m = sec4MPt t φ (some i) * sec4MPt t φ (some j) :=
    h.fiber_core_cent (μ := m⁻¹ * y * m) (x := m⁻¹ * x * m) hij hμ hμN hcomm hμr' h6
      hx'A hx'μ hμx
  have hx' : x = m * (m⁻¹ * x * m) * m⁻¹ := by group
  rcases hcore with h1 | h1
  · left
    exact hx'.trans (by rw [h1]; group)
  · right
    have hνi : ν (some i) = a := by
      rw [← hi]
      simpa using Equiv.apply_symm_apply ν a
    have hνj : ν (some j) = b := by
      rw [← hj]
      simpa using Equiv.apply_symm_apply ν b
    calc x = m * (m⁻¹ * x * m) * m⁻¹ := hx'
      _ = m * (sec4MPt t φ (some i) * sec4MPt t φ (some j)) * m⁻¹ := by rw [h1]
      _ = (m * sec4MPt t φ (some i) * m⁻¹)
            * (m * sec4MPt t φ (some j) * m⁻¹) := by group
      _ = sec4MPt t φ (ν (some i)) * sec4MPt t φ (ν (some j)) := by
        rw [hν (some i), hν (some j)]
      _ = sec4MPt t φ a * sec4MPt t φ b := by rw [hνi, hνj]

end CFSG.OddStandard.SmallF3.Omega
