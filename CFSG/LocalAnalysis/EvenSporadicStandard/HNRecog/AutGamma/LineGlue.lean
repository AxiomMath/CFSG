module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutGamma.OrbConj
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Local

public section

namespace CFSG.EvenSporadicStandard.HNRecog.AutGamma

open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3

variable {G : Type} [Group G] {a z : G}

theorem orderOf_eq_six {X : Type*} [Group X] {u : X} (h6 : u ^ 6 = 1) (h2 : u ^ 2 ≠ 1)
    (h3 : u ^ 3 ≠ 1) : orderOf u = 6 := by
  refine orderOf_eq_of_pow_and_pow_div_prime (by norm_num) h6 fun p hp hpd => ?_
  have h6' : p ∣ 2 * 3 := hpd
  rcases (Nat.Prime.dvd_mul hp).1 h6' with h | h
  · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h
    simpa using h3
  · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h
    simpa using h2

@[expose] def HasLine (a z : G) (k₁ k₂ k₃ : OrbitKind) : Prop :=
  ∃ b : G, IsConj a b ∧ ∃ x ∈ orbitOf a z b k₁, ∃ y ∈ orbitOf a z b k₂,
    x * y ∈ orbitOf a z b k₃

theorem HasLine.at_self {k₁ k₂ k₃ : OrbitKind} (h : HasLine a z k₁ k₂ k₃) :
    ∃ x ∈ orbitOf a z a k₁, ∃ y ∈ orbitOf a z a k₂, x * y ∈ orbitOf a z a k₃ := by
  obtain ⟨b, hb, x, hx, y, hy, hxy⟩ := h
  obtain ⟨g, hg⟩ := isConj_iff.1 hb
  have hb' : g⁻¹ * b * g⁻¹⁻¹ = a := by rw [← hg]; group
  refine ⟨g⁻¹ * x * g⁻¹⁻¹, ?_, g⁻¹ * y * g⁻¹⁻¹, ?_, ?_⟩
  · have := (conj_mem_orbitOf (a := a) (z := z) g⁻¹ k₁ (x := b) (c := x)).2 hx
    rwa [hb'] at this
  · have := (conj_mem_orbitOf (a := a) (z := z) g⁻¹ k₂ (x := b) (c := y)).2 hy
    rwa [hb'] at this
  · have := (conj_mem_orbitOf (a := a) (z := z) g⁻¹ k₃ (x := b) (c := x * y)).2 hxy
    rw [hb'] at this
    convert this using 1
    group

theorem line_of_hasLine {k₁ k₂ k₃ : OrbitKind} (hk : IsConjOrbit (Gx a) (orbitOf a z a k₁))
    (h : HasLine a z k₁ k₂ k₃) :
    ∀ x ∈ orbitOf a z a k₁, ∃ y ∈ orbitOf a z a k₂, x * y ∈ orbitOf a z a k₃ := by
  obtain ⟨x₀, hx₀, y₀, hy₀, hxy₀⟩ := h.at_self
  intro x hx
  obtain ⟨g, hg, hgx⟩ := hk.transitive x₀ hx₀ x hx
  have hga : g * a * g⁻¹ = a := by
    have := mem_Gx.1 hg
    rw [← this]
    group
  refine ⟨g * y₀ * g⁻¹, ?_, ?_⟩
  · have := (conj_mem_orbitOf (a := a) (z := z) g k₂ (x := a) (c := y₀)).2 hy₀
    rwa [hga] at this
  · have := (conj_mem_orbitOf (a := a) (z := z) g k₃ (x := a) (c := x₀ * y₀)).2 hxy₀
    rw [hga] at this
    convert this using 1
    rw [← hgx]
    group

theorem isConjOrbit_orb2B (hL : F5Local G a z) : IsConjOrbit (Gx a) (orb2B a z a) :=
  hL.tableV.self.partition.orbit 1

theorem isConjOrbit_orb4A (hL : F5Local G a z) : IsConjOrbit (Gx a) (orb4A a z a) :=
  hL.tableV.self.partition.orbit 2

theorem isConjOrbit_orb4B (hL : F5Local G a z) : IsConjOrbit (Gx a) (orb4B a a) :=
  hL.tableV.self.partition.orbit 3

theorem isConjOrbit_orb5A (hL : F5Local G a z) : IsConjOrbit (Gx a) (orb5A a a) :=
  hL.tableVII.self.partition.orbit 1

theorem isConjOrbit_orb5E (hL : F5Local G a z) : IsConjOrbit (Gx a) (orb5E a a) :=
  hL.tableVII.self.partition.orbit 2

end CFSG.EvenSporadicStandard.HNRecog.AutGamma
