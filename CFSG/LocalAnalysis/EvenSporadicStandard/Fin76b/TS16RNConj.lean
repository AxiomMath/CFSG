module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.I13Syl

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup

theorem conj_max_cent_gen {G : Type} [Group G] {E P : Subgroup G} (g : G)
    (hP : IsPGroup 2 P) (hPE : P ≤ Subgroup.centralizer (E : Set G))
    (hmax : ∀ R : Subgroup G, IsPGroup 2 R →
      R ≤ Subgroup.centralizer (E : Set G) → P ≤ R → R = P) :
    IsPGroup 2 (P.map (MulAut.conj g).toMonoidHom) ∧
      P.map (MulAut.conj g).toMonoidHom ≤
        Subgroup.centralizer ((E.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) ∧
      ∀ R : Subgroup G, IsPGroup 2 R →
        R ≤ Subgroup.centralizer ((E.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) →
        P.map (MulAut.conj g).toMonoidHom ≤ R → R ≤ P.map (MulAut.conj g).toMonoidHom := by
  have hmem : ∀ y : G, y ∈ P.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * y * g ∈ P := by
    intro y
    constructor
    · rintro ⟨s, hs, rfl⟩
      simpa [MulAut.conj_apply, mul_assoc] using hs
    · intro hy
      exact ⟨g⁻¹ * y * g, hy, by simp [MulAut.conj_apply]; group⟩
  have hmemE : ∀ y : G, y ∈ E.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * y * g ∈ E := by
    intro y
    constructor
    · rintro ⟨s, hs, rfl⟩
      simpa [MulAut.conj_apply, mul_assoc] using hs
    · intro hy
      exact ⟨g⁻¹ * y * g, hy, by simp [MulAut.conj_apply]; group⟩
  refine ⟨hP.map _, ?_, ?_⟩
  · intro y hy
    rw [hmem] at hy
    refine mem_centralizer_iff.2 fun e he => ?_
    have h1 := mem_centralizer_iff.1 (hPE hy) (g⁻¹ * e * g) ((hmemE e).1 he)
    calc e * y = g * ((g⁻¹ * e * g) * (g⁻¹ * y * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * y * g) * (g⁻¹ * e * g)) * g⁻¹ := by rw [h1]
      _ = y * e := by group
  · intro R hR hRE hle
    have hR₀2 : IsPGroup 2 (R.map (MulAut.conj g⁻¹).toMonoidHom) := hR.map _
    have hR₀E : R.map (MulAut.conj g⁻¹).toMonoidHom ≤ centralizer (E : Set G) := by
      rintro _ ⟨r, hr, rfl⟩
      refine mem_centralizer_iff.2 fun e he => ?_
      have hge : g * e * g⁻¹ ∈ E.map (MulAut.conj g).toMonoidHom := by
        refine (hmemE (g * e * g⁻¹)).2 ?_
        have h' : g⁻¹ * (g * e * g⁻¹) * g = e := by group
        rw [h']
        exact he
      have h1 := mem_centralizer_iff.1 (hRE hr) (g * e * g⁻¹) hge
      simp only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom, inv_inv]
      calc e * (g⁻¹ * r * g) = g⁻¹ * ((g * e * g⁻¹) * r) * g := by group
        _ = g⁻¹ * (r * (g * e * g⁻¹)) * g := by rw [h1]
        _ = g⁻¹ * r * g * e := by group
    have hSle : P ≤ R.map (MulAut.conj g⁻¹).toMonoidHom := by
      intro s hs
      have h2 : g⁻¹ * (g * s * g⁻¹) * g = s := by group
      refine ⟨g * s * g⁻¹, hle ((hmem _).2 (by rw [h2]; exact hs)), ?_⟩
      simpa [MulAut.conj_apply] using h2
    have heq := hmax _ hR₀2 hR₀E hSle
    intro r hr
    rw [hmem]
    have hmemR : g⁻¹ * r * g ∈ R.map (MulAut.conj g⁻¹).toMonoidHom :=
      ⟨r, hr, by simp [MulAut.conj_apply]⟩
    rw [heq] at hmemR
    exact hmemR

theorem card_le_of_max {G : Type} [Group G] [Finite G] {Θ P : Subgroup G}
    (hPΘ : P ≤ Θ) (hP2 : IsPGroup 2 P)
    (hPmax : ∀ R : Subgroup G, IsPGroup 2 R → R ≤ Θ → P ≤ R → R ≤ P)
    {R' : Subgroup G} (hR' : IsPGroup 2 R') (hR'Θ : R' ≤ Θ) : Nat.card ↥R' ≤ Nat.card ↥P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := (hR'.comap_subtype (K := Θ)).exists_le_sylow
  have h1 : Nat.card ↥(R'.subgroupOf Θ) ≤ Nat.card ↥(Q : Subgroup ↥Θ) :=
    Subgroup.card_le_of_le hQ
  have h2 : Nat.card ↥(Q : Subgroup ↥Θ) =
      Nat.card ↥(sylowOfMax hPΘ hP2 hPmax : Subgroup ↥Θ) := by
    rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
  have h3 : Nat.card ↥(sylowOfMax hPΘ hP2 hPmax : Subgroup ↥Θ) = Nat.card ↥P :=
    Nat.card_congr (subgroupOfEquivOfLe hPΘ).toEquiv
  have h4 : Nat.card ↥(R'.subgroupOf Θ) = Nat.card ↥R' :=
    Nat.card_congr (subgroupOfEquivOfLe hR'Θ).toEquiv
  omega

theorem maximal_of_card_eq {G : Type} [Group G] [Finite G] {Θ P S₀ : Subgroup G}
    (hPΘ : P ≤ Θ) (hP2 : IsPGroup 2 P)
    (hPmax : ∀ R : Subgroup G, IsPGroup 2 R → R ≤ Θ → P ≤ R → R ≤ P)
    (hS₀Θ : S₀ ≤ Θ) (hS₀2 : IsPGroup 2 S₀) (hcard : Nat.card ↥S₀ = Nat.card ↥P) :
    ∀ R : Subgroup G, IsPGroup 2 R → R ≤ Θ → S₀ ≤ R → R ≤ S₀ := by
  intro R hR hRΘ hSR
  have hcardle : Nat.card ↥R ≤ Nat.card ↥S₀ := by
    rw [hcard]
    exact card_le_of_max hPΘ hP2 hPmax hR hRΘ
  exact (Subgroup.eq_of_le_of_card_ge hSR hcardle).symm.le

end CFSG.EvenSporadicStandard.Fin76b
