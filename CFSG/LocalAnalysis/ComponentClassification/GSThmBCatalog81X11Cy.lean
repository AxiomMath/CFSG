module

public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import CFSG.GH74.GLS.Bg.Local.Transfer1515

public section

namespace CFSG.ComponentClassification.GSThmB

namespace X11

open Subgroup CFSG.GH74.GLS.Bg.Thompson

theorem exists_zmod_hom_ne_one {A : Type*} [CommGroup A] [Finite A] {x : A} (hx : x ≠ 1) :
    ∃ (n : ℕ) (χ : A →* Multiplicative (ZMod n)), χ x ≠ 1 := by
  obtain ⟨ι, _, n, -, ⟨e⟩⟩ := CommGroup.equiv_prod_multiplicative_zmod_of_finite A
  have hex : e x ≠ 1 := fun h1 => hx (e.injective (h1.trans (map_one e).symm))
  obtain ⟨i, hi⟩ : ∃ i, e x i ≠ 1 := by
    by_contra hall
    exact hex (funext fun i => not_not.mp fun h => hall ⟨i, h⟩)
  exact ⟨n i, (Pi.evalMonoidHom _ i).comp e.toMonoidHom, hi⟩

theorem exists_zmod_hom_ne_one' {A : Type*} [Group A] [Finite A]
    (hcomm : ∀ a b : A, a * b = b * a) {x : A} (hx : x ≠ 1) :
    ∃ (n : ℕ) (χ : A →* Multiplicative (ZMod n)), χ x ≠ 1 := by
  let _ : CommGroup A := { (inferInstance : Group A) with mul_comm := hcomm }
  exact exists_zmod_hom_ne_one hx

variable {H : Type*} [Group H] [Finite H]

theorem exists_normal_of_zmod_character {T : Subgroup H} (hT : IsPGroup 2 T)
    (hTidx : ¬ 2 ∣ T.index) {n : ℕ} (χ : T →* Multiplicative (ZMod n)) {u : H} (huT : u ∈ T)
    (hu : χ ⟨u, huT⟩ ≠ 1) (huu : u * u = 1)
    (hext : ∀ (g : H) (hg : g⁻¹ * u * g ∈ T), IsExtremalIn 2 T (g⁻¹ * u * g) →
      χ ⟨g⁻¹ * u * g, hg⟩ = χ ⟨u, huT⟩) :
    ∃ (N : Subgroup H) (_ : N.Normal), IsCyclic (H ⧸ N) ∧ IsPGroup 2 (H ⧸ N) ∧ u ∉ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q : Subgroup H := χ.ker.map T.subtype with hQ
  have hmemQ : ∀ (t : H) (ht : t ∈ T), t ∈ Q ↔ χ ⟨t, ht⟩ = 1 := by
    intro t ht
    constructor
    · rintro ⟨s, hs, hst⟩
      have hs' : s = ⟨t, ht⟩ := Subtype.ext hst
      rw [← hs']
      exact hs
    · intro h1
      exact ⟨⟨t, ht⟩, h1, rfl⟩
  have hQT : Q ≤ T := map_subtype_le _
  have hQn : ∀ t ∈ T, ∀ q ∈ Q, t * q * t⁻¹ ∈ Q := by
    intro t ht q hq
    have hqT := hQT hq
    rw [hmemQ _ hqT] at hq
    rw [hmemQ _ (T.mul_mem (T.mul_mem ht hqT) (T.inv_mem ht))]
    have e : (⟨t * q * t⁻¹, T.mul_mem (T.mul_mem ht hqT) (T.inv_mem ht)⟩ : T) =
        ⟨t, ht⟩ * ⟨q, hqT⟩ * (⟨t, ht⟩ : T)⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, hq, mul_one, mul_inv_cancel]
  have hcyc : ∃ c ∈ T, ∀ t ∈ T, ∃ k : ℤ, (c ^ k)⁻¹ * t ∈ Q := by
    obtain ⟨g₀, hg₀⟩ := IsCyclic.exists_generator (α := χ.range)
    obtain ⟨c, hc⟩ := g₀.2
    refine ⟨c, c.2, fun t ht => ?_⟩
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (hg₀ ⟨χ ⟨t, ht⟩, ⟨_, rfl⟩⟩)
    refine ⟨k, ?_⟩
    have hmem : ((c : H) ^ k)⁻¹ * t ∈ T := T.mul_mem (T.inv_mem (T.zpow_mem c.2 k)) ht
    rw [hmemQ _ hmem]
    have e : (⟨((c : H) ^ k)⁻¹ * t, hmem⟩ : T) = (c ^ k)⁻¹ * ⟨t, ht⟩ :=
      Subtype.ext (by simp)
    have hk' : (g₀ : Multiplicative (ZMod n)) ^ k = χ ⟨t, ht⟩ := by
      have := congrArg Subtype.val hk
      simpa using this
    rw [e, map_mul, map_inv, map_zpow, hc, hk', inv_mul_cancel]
  have huQ : u ∉ Q := fun h1 => hu ((hmemQ _ huT).mp h1)
  have htr := thompson_transfer_1515 (p := 2) hT hTidx hQn hcyc huT huQ
    (fun g k _ => by
      rw [pow_mul, sq, huu, one_pow, mul_one, inv_mul_cancel]
      exact one_mem _)
    (fun g hg hge => by
      right
      have hmem : u⁻¹ * (g⁻¹ * u * g) ∈ T := T.mul_mem (T.inv_mem huT) hg
      rw [hmemQ _ hmem]
      have e : (⟨u⁻¹ * (g⁻¹ * u * g), hmem⟩ : T) = (⟨u, huT⟩ : T)⁻¹ * ⟨g⁻¹ * u * g, hg⟩ := rfl
      rw [e, map_mul, map_inv, hext g hg hge, inv_mul_cancel])
  rcases htr with ⟨N, hN, hcycN, hpN, huN⟩ | ⟨g, hgQ, hgext, -⟩
  · exact ⟨N, hN, hcycN, hpN, huN⟩
  · have h1 := (hmemQ _ (hQT hgQ)).mp hgQ
    rw [hext g (hQT hgQ) hgext] at h1
    exact absurd h1 hu

end X11

end CFSG.ComponentClassification.GSThmB
