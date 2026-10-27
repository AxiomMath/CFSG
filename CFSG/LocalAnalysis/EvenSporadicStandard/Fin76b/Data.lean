module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Config

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup

@[expose] def SylowData (X : Type*) [Group X] : Prop :=
  ∃ (T : Subgroup X) (t b : X), IsPGroup 2 T ∧ (∃ m : ℕ, Odd m ∧ Nat.card X = Nat.card T * m) ∧
    t * t = 1 ∧ t ≠ 1 ∧ t ∈ T ∧ (∀ x ∈ T, x * t = t * x) ∧
    (∀ y ∈ T, (∀ x ∈ T, x * y = y * x) → y = 1 ∨ y = t) ∧ (∃ g : X, g * g = t) ∧
    ∀ a : X, a * a = 1 → a ≠ 1 → (∃ c : X, a = c * t * c⁻¹) ∨ (∃ c : X, a = c * b * c⁻¹)

theorem SylowData.of_mulEquiv {X Y : Type*} [Group X] [Group Y] [Finite X] (e : X ≃* Y)
    (h : SylowData X) : SylowData Y := by
  obtain ⟨T, t, b, hT, ⟨m, hm, hcard⟩, ht2, ht1, htT, htc, hcen, ⟨g, hg⟩, hcls⟩ := h
  have hcardT : Nat.card (T.map e.toMonoidHom) = Nat.card T :=
    Subgroup.card_map_of_injective e.injective
  refine ⟨T.map e.toMonoidHom, e t, e b, ?_, ⟨m, hm, ?_⟩, ?_, ?_, ⟨t, htT, rfl⟩, ?_, ?_,
    ⟨e g, by rw [← map_mul, hg]⟩, ?_⟩
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := hT.exists_card_eq
    exact IsPGroup.of_card (n := n) (by rw [hcardT, hn])
  · rw [Nat.card_congr e.toEquiv.symm, hcard, hcardT]
  · rw [← map_mul, ht2, map_one]
  · exact fun h1 => ht1 (e.injective (by rw [h1, map_one]))
  · rintro _ ⟨x, hx, rfl⟩
    show e x * e t = e t * e x
    rw [← map_mul, ← map_mul, htc x hx]
  · intro y hy hc
    obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.1 hy
    have : ∀ x ∈ T, x * y' = y' * x := fun x hx => e.injective (by
      rw [map_mul, map_mul]; exact hc (e x) ⟨x, hx, rfl⟩)
    rcases hcen y' hy' this with h1 | h1
    · exact Or.inl (by rw [h1, map_one])
    · exact Or.inr (by rw [h1]; rfl)
  · intro a ha2 ha1
    have hx : e.symm a * e.symm a = 1 := by rw [← map_mul, ha2, map_one]
    have hne : e.symm a ≠ 1 := fun h1 => ha1 (by simpa using congrArg e h1)
    rcases hcls (e.symm a) hx hne with ⟨c, hc⟩ | ⟨c, hc⟩
    · refine Or.inl ⟨e c, ?_⟩
      have := congrArg e hc
      simpa [map_mul, map_inv] using this
    · refine Or.inr ⟨e c, ?_⟩
      have := congrArg e hc
      simpa [map_mul, map_inv] using this

variable {G : Type*} [Group G] {L : Subgroup G}

theorem InnerConfig.of_sylowData [Finite G] {X : Type*} [Group X] [Finite X] (φ : X ≃* L)
    (hX : SylowData X) {z : G} (hz2 : z * z = 1) (hz1 : z ≠ 1)
    (hzc : z ∈ centralizer (L : Set G)) (hd : Disjoint L (zpowers z))
    (hcent : centralizer ({z} : Set G) = L ⊔ zpowers z) :
    ∃ (t : G) (T₀ : Subgroup G), InnerConfig G L z t T₀ := by
  obtain ⟨T, t, b, hT, ⟨m, hm, hcard⟩, ht2, ht1, htT, htc, hcen, ⟨g, hg⟩, hcls⟩ := hX
  let ι : X →* G := L.subtype.comp φ.toMonoidHom
  have hι : Function.Injective ι := L.subtype_injective.comp φ.injective
  have hrange : ∀ a ∈ L, ∃ a' : X, ι a' = a := fun a ha => ⟨φ.symm ⟨a, ha⟩, by simp [ι]⟩
  have hιL : ∀ a' : X, ι a' ∈ L := fun a' => (φ a').2
  have hcardT : Nat.card (T.map ι) = Nat.card T := Subgroup.card_map_of_injective hι
  have hcardL : Nat.card L = Nat.card X := Nat.card_congr φ.toEquiv.symm
  refine ⟨ι t, T.map ι, ?_⟩
  exact
  { z_sq := hz2
    z_ne := hz1
    z_cent := hzc
    disjoint := hd
    cent_eq := hcent
    T₀_le := by rintro _ ⟨x, -, rfl⟩; exact hιL x
    T₀_pgroup := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨n, hn⟩ := hT.exists_card_eq
      exact IsPGroup.of_card (n := n) (by rw [hcardT, hn])
    T₀_odd := ⟨m, hm, by rw [hcardL, hcard, hcardT]⟩
    t_sq := by rw [← map_mul, ht2, map_one]
    t_ne := fun h1 => ht1 (hι (by rw [h1, map_one]))
    t_mem := ⟨t, htT, rfl⟩
    t_central := by
      rintro _ ⟨x, hx, rfl⟩
      rw [← map_mul, ← map_mul, htc x hx]
    center_le := by
      intro y hy hc
      obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.1 hy
      have : ∀ x ∈ T, x * y' = y' * x := fun x hx => hι (by
        rw [map_mul, map_mul]; exact hc (ι x) ⟨x, hx, rfl⟩)
      rcases hcen y' hy' this with h1 | h1
      · exact Or.inl (by rw [h1, map_one])
      · exact Or.inr (by rw [h1])
    t_square := ⟨ι g, hιL g, by rw [← map_mul, hg]⟩
    classes := by
      refine ⟨ι b, hιL b, ?_⟩
      intro a ha ha2 ha1
      obtain ⟨a', rfl⟩ := hrange a ha
      have hx : a' * a' = 1 := hι (by rw [map_mul, ha2, map_one])
      have hne : a' ≠ 1 := fun h1 => ha1 (by rw [h1, map_one])
      rcases hcls a' hx hne with ⟨c, hc⟩ | ⟨c, hc⟩
      · exact Or.inl ⟨ι c, hιL c, by rw [hc]; simp [map_mul, map_inv]⟩
      · exact Or.inr ⟨ι c, hιL c, by rw [hc]; simp [map_mul, map_inv]⟩ }

end CFSG.EvenSporadicStandard.Fin76b
