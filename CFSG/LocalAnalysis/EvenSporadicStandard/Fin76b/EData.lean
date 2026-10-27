module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Data

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup

@[expose] def SylowEData (X : Type*) [Group X] : Prop :=
  ∃ (T E : Subgroup X) (t b : X), IsPGroup 2 T ∧
    (∃ m : ℕ, Odd m ∧ Nat.card X = Nat.card T * m) ∧
    t * t = 1 ∧ t ≠ 1 ∧ t ∈ T ∧ (∀ x ∈ T, x * t = t * x) ∧
    (∀ y ∈ T, (∀ x ∈ T, x * y = y * x) → y = 1 ∨ y = t) ∧ (∃ g : X, g * g = t) ∧
    (∀ a : X, a * a = 1 → a ≠ 1 → (∃ c : X, a = c * t * c⁻¹) ∨ (∃ c : X, a = c * b * c⁻¹)) ∧
    E ≤ T ∧ t ∈ E ∧ (∀ e ∈ E, e * e = 1 → e ≠ 1 → ∃ c : X, e = c * t * c⁻¹) ∧
    E = closure {e | e ∈ E ∧ e * e = 1 ∧ e ≠ 1} ∧
    (∃ e₁ ∈ E, ∃ e₂ ∈ E, e₁ * e₂ ≠ e₂ * e₁) ∧
    (∀ e₁ ∈ E, ∀ e₂ ∈ E, e₁ * e₂ * e₁⁻¹ * e₂⁻¹ = 1 ∨ e₁ * e₂ * e₁⁻¹ * e₂⁻¹ = t) ∧
    (∀ y ∈ E, (∀ f ∈ E, f * y = y * f) → y = 1 ∨ y = t) ∧
    (∀ P : Subgroup X, P ≤ T → Nonempty (E ≃* P) → P = E) ∧
    (∀ s ∈ T, ∀ e ∈ E, s * e * s⁻¹ ∈ E) ∧
    (∀ s ∈ T, (∀ e ∈ E, s * e = e * s) → s = 1 ∨ s = t)

structure EConfig {G : Type*} [Group G] (A T₀ E : Subgroup G) (t : G) : Prop where
  le : E ≤ T₀
  t_mem : t ∈ E
  conj : ∀ e ∈ E, e * e = 1 → e ≠ 1 → ∃ c ∈ A, e = c * t * c⁻¹
  gen : E = closure {e | e ∈ E ∧ e * e = 1 ∧ e ≠ 1}
  nonab : ∃ e₁ ∈ E, ∃ e₂ ∈ E, e₁ * e₂ ≠ e₂ * e₁
  comm : ∀ e₁ ∈ E, ∀ e₂ ∈ E, e₁ * e₂ * e₁⁻¹ * e₂⁻¹ = 1 ∨ e₁ * e₂ * e₁⁻¹ * e₂⁻¹ = t
  center : ∀ y ∈ E, (∀ f ∈ E, f * y = y * f) → y = 1 ∨ y = t
  unique : ∀ P : Subgroup G, P ≤ T₀ → Nonempty (E ≃* P) → P = E
  normal : ∀ s ∈ T₀, ∀ e ∈ E, s * e * s⁻¹ ∈ E
  cent : ∀ s ∈ T₀, (∀ e ∈ E, s * e = e * s) → s = 1 ∨ s = t

variable {G : Type*} [Group G] {L : Subgroup G}

theorem InnerConfig.of_sylowEData [Finite G] {X : Type*} [Group X] [Finite X] (φ : X ≃* L)
    (hX : SylowEData X) {z : G} (hz2 : z * z = 1) (hz1 : z ≠ 1)
    (hzc : z ∈ centralizer (L : Set G)) (hd : Disjoint L (zpowers z))
    (hcent : centralizer ({z} : Set G) = L ⊔ zpowers z) :
    ∃ (t : G) (T₀ E : Subgroup G), InnerConfig G L z t T₀ ∧ EConfig L T₀ E t := by
  obtain ⟨T, E, t, b, hT, ⟨m, hm, hcard⟩, ht2, ht1, htT, htc, hcen, ⟨g, hg⟩, hcls, hET, htE,
    hEconj, hEgen, hEnab, hEcomm, hEcen, hEuniq, hEnorm, hEcent⟩ := hX
  let ι : X →* G := L.subtype.comp φ.toMonoidHom
  have hι : Function.Injective ι := L.subtype_injective.comp φ.injective
  have hrange : ∀ a ∈ L, ∃ a' : X, ι a' = a := fun a ha => ⟨φ.symm ⟨a, ha⟩, by simp [ι]⟩
  have hιL : ∀ a' : X, ι a' ∈ L := fun a' => (φ a').2
  have hcardT : Nat.card (T.map ι) = Nat.card T := Subgroup.card_map_of_injective hι
  have hcardL : Nat.card L = Nat.card X := Nat.card_congr φ.toEquiv.symm
  have hX' : SylowData X := ⟨T, t, b, hT, ⟨m, hm, hcard⟩, ht2, ht1, htT, htc, hcen, ⟨g, hg⟩, hcls⟩
  refine ⟨ι t, T.map ι, E.map ι, ?_, ?_⟩
  · exact
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
  · have hEmem : ∀ e ∈ E.map ι, ∃ e' ∈ E, ι e' = e := fun e he => by
      obtain ⟨e', he', rfl⟩ := Subgroup.mem_map.1 he
      exact ⟨e', he', rfl⟩
    refine
    { le := Subgroup.map_mono hET
      t_mem := ⟨t, htE, rfl⟩
      conj := ?_
      gen := ?_
      nonab := ?_
      comm := ?_
      center := ?_
      unique := ?_
      normal := ?_
      cent := ?_ }
    · intro e he he2 he1
      obtain ⟨e', he', rfl⟩ := hEmem e he
      have hx : e' * e' = 1 := hι (by rw [map_mul, he2, map_one])
      have hne : e' ≠ 1 := fun h1 => he1 (by rw [h1, map_one])
      obtain ⟨c, hc⟩ := hEconj e' he' hx hne
      exact ⟨ι c, hιL c, by rw [hc]; simp [map_mul, map_inv]⟩
    · apply le_antisymm
      · rintro _ ⟨e', he', rfl⟩
        have h1 : e' ∈ closure {e | e ∈ E ∧ e * e = 1 ∧ e ≠ 1} := hEgen ▸ he'
        have h2 : closure {e | e ∈ E ∧ e * e = 1 ∧ e ≠ 1} ≤
            (closure {e | e ∈ E.map ι ∧ e * e = 1 ∧ e ≠ 1}).comap ι := by
          rw [closure_le]
          intro e hex
          refine subset_closure ?_
          obtain ⟨he, he2, he1⟩ := hex
          exact ⟨⟨e, he, rfl⟩, by rw [← map_mul, he2, map_one], fun h1 => he1 (hι (by
            rw [h1, map_one]))⟩
        exact h2 h1
      · rw [closure_le]
        intro e he
        exact he.1
    · obtain ⟨e₁, he₁, e₂, he₂, hne⟩ := hEnab
      exact ⟨ι e₁, ⟨e₁, he₁, rfl⟩, ι e₂, ⟨e₂, he₂, rfl⟩, fun h1 => hne (hι (by
        rw [map_mul, map_mul]; exact h1))⟩
    · rintro _ ⟨e₁, he₁, rfl⟩ _ ⟨e₂, he₂, rfl⟩
      rcases hEcomm e₁ he₁ e₂ he₂ with h1 | h1
      · exact Or.inl (by
          have : ι (e₁ * e₂ * e₁⁻¹ * e₂⁻¹) = 1 := by rw [h1, map_one]
          simpa [map_mul, map_inv] using this)
      · exact Or.inr (by
          have : ι (e₁ * e₂ * e₁⁻¹ * e₂⁻¹) = ι t := by rw [h1]
          simpa [map_mul, map_inv] using this)
    · rintro _ ⟨y, hy, rfl⟩ hc
      have : ∀ f ∈ E, f * y = y * f := fun f hf => hι (by
        rw [map_mul, map_mul]; exact hc (ι f) ⟨f, hf, rfl⟩)
      rcases hEcen y hy this with h1 | h1
      · exact Or.inl (by rw [h1, map_one])
      · exact Or.inr (by rw [h1])
    · intro P hP hiso
      have hPr : P ≤ ι.range := fun x hx => by
        obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.1 (hP hx)
        exact ⟨y, rfl⟩
      have hPT : P.comap ι ≤ T := fun x hx => by
        obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 (hP hx)
        rwa [← hι hyx]
      obtain ⟨e⟩ := hiso
      have e2 : E ≃* P.comap ι :=
        ((E.equivMapOfInjective ι hι).trans e).trans
          (((P.comap ι).equivMapOfInjective ι hι).trans
            (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self hPr))).symm
      have := hEuniq (P.comap ι) hPT ⟨e2⟩
      rw [← Subgroup.map_comap_eq_self hPr, this]
    · rintro _ ⟨s, hs, rfl⟩ _ ⟨e, he, rfl⟩
      exact ⟨s * e * s⁻¹, hEnorm s hs e he, by simp [map_mul, map_inv]⟩
    · rintro _ ⟨s, hs, rfl⟩ hc
      have : ∀ e ∈ E, s * e = e * s := fun e he => hι (by
        rw [map_mul, map_mul]; exact hc (ι e) ⟨e, he, rfl⟩)
      rcases hEcent s hs this with h1 | h1
      · exact Or.inl (by rw [h1, map_one])
      · exact Or.inr (by rw [h1])

end CFSG.EvenSporadicStandard.Fin76b
