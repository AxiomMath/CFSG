module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral

public section

namespace CFSG.QuasithinUnique.DoubleA3

open DihedralGroup

theorem dihedral4_klein : ∀ V : Finset (DihedralGroup 4), V.card = 4 → (∀ x ∈ V, x * x = 1) →
    (∀ x ∈ V, ∀ y ∈ V, x * y ∈ V) →
      V = {1, r 2, sr 0, sr 2} ∨ V = {1, r 2, sr 1, sr 3} := by decide +kernel

theorem dihedral4_invol : ∀ d : DihedralGroup 4, d * d = 1 →
    d ∈ ({1, r 2, sr 0, sr 2} ∪ {1, r 2, sr 1, sr 3} : Finset (DihedralGroup 4)) := by
  decide +kernel

theorem klein_cover {G : Type} [Group G] {R U V : Subgroup G} (f : ↥R ≃* DihedralGroup 4)
    (hUR : U ≤ R) (hVR : V ≤ R) (hU4 : Nat.card U = 4) (hV4 : Nat.card V = 4)
    (hUsq : ∀ u ∈ U, u * u = 1) (hVsq : ∀ v ∈ V, v * v = 1) (hUV : U ≠ V) {a : G} (haR : a ∈ R)
    (ha2 : a * a = 1) : a ∈ U ∨ a ∈ V := by
  classical
  let D : Subgroup G → Finset (DihedralGroup 4) := fun X =>
    Finset.univ.filter (fun d => ((f.symm d : ↥R) : G) ∈ X)
  have hD : ∀ X d, d ∈ D X ↔ ((f.symm d : ↥R) : G) ∈ X := by
    intro X d
    simp [D]
  have hcard : ∀ X : Subgroup G, X ≤ R → Nat.card X = (D X).card := by
    intro X hXR
    have e : ↥X ≃ {d // d ∈ D X} :=
      { toFun := fun a => ⟨f ⟨a, hXR a.2⟩, by rw [hD]; simp⟩
        invFun := fun d => ⟨((f.symm d : ↥R) : G), (hD X d).mp d.2⟩
        left_inv := fun a => by ext; simp
        right_inv := fun d => by ext; simp }
    rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]
  have hmul : ∀ X : Subgroup G, ∀ d ∈ D X, ∀ d' ∈ D X, d * d' ∈ D X := by
    intro X d hd d' hd'
    rw [hD] at hd hd' ⊢
    have : ((f.symm (d * d') : ↥R) : G) = ((f.symm d : ↥R) : G) * ((f.symm d' : ↥R) : G) := by
      rw [map_mul]
      rfl
    rw [this]
    exact X.mul_mem hd hd'
  have hsq : ∀ X : Subgroup G, (∀ u ∈ X, u * u = 1) → ∀ d ∈ D X, d * d = 1 := by
    intro X hX d hd
    rw [hD] at hd
    have h1 := hX _ hd
    have h2 : f.symm (d * d) = f.symm 1 := by
      rw [map_mul, map_one]
      exact Subtype.ext h1
    exact f.symm.injective h2
  have hinj : ∀ X Y : Subgroup G, X ≤ R → Y ≤ R → D X = D Y → X = Y := by
    intro X Y hXR hYR h
    ext g
    constructor
    · intro hg
      have : f ⟨g, hXR hg⟩ ∈ D X := by rw [hD]; simpa using hg
      rw [h, hD] at this
      simpa using this
    · intro hg
      have : f ⟨g, hYR hg⟩ ∈ D Y := by rw [hD]; simpa using hg
      rw [← h, hD] at this
      simpa using this
  have hDU := dihedral4_klein (D U) (by rw [← hcard U hUR, hU4]) (hsq U hUsq) (hmul U)
  have hDV := dihedral4_klein (D V) (by rw [← hcard V hVR, hV4]) (hsq V hVsq) (hmul V)
  have hne : D U ≠ D V := fun h => hUV (hinj U V hUR hVR h)
  have hd2 : f ⟨a, haR⟩ * f ⟨a, haR⟩ = 1 := by
    rw [← map_mul, ← map_one f]
    congr 1
    exact Subtype.ext ha2
  have hdcov := dihedral4_invol _ hd2
  have hmemD : ∀ X : Subgroup G, f ⟨a, haR⟩ ∈ D X → a ∈ X := by
    intro X h
    rw [hD] at h
    simpa using h
  rcases hDU with hU | hU <;> rcases hDV with hV | hV
  · exact absurd (hU.trans hV.symm) hne
  · rcases Finset.mem_union.mp hdcov with h | h
    · left; exact hmemD U (by rw [hU]; exact h)
    · right; exact hmemD V (by rw [hV]; exact h)
  · rcases Finset.mem_union.mp hdcov with h | h
    · right; exact hmemD V (by rw [hV]; exact h)
    · left; exact hmemD U (by rw [hU]; exact h)
  · exact absurd (hU.trans hV.symm) hne

end CFSG.QuasithinUnique.DoubleA3
