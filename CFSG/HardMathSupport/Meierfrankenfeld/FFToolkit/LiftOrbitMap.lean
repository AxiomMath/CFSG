module

public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.LnLift

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit

open CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

theorem map_le_normalizer_map {H S : Type*} [Group H] [Group S] (ι : H →* S)
    {U T : Subgroup H} (hTN : T ≤ Subgroup.normalizer (U : Set H)) :
    T.map ι ≤ Subgroup.normalizer ((U.map ι : Subgroup S) : Set S) := by
  rintro _ ⟨t, ht, rfl⟩
  rw [Subgroup.mem_set_normalizer_iff]
  intro x
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨t * u * t⁻¹, ?_, by simp [map_mul, map_inv]⟩
    exact (Subgroup.mem_set_normalizer_iff.1 (hTN ht) u).1 hu
  · rintro ⟨u, hu, hx⟩
    refine ⟨t⁻¹ * u * t, ?_, ?_⟩
    · have := (Subgroup.mem_set_normalizer_iff.1 (hTN ht) (t⁻¹ * u * t)).2
      apply this
      simpa [mul_assoc] using hu
    · rw [map_mul, map_mul, map_inv, hx]
      group

theorem two_pow_le_card_of_lift_orbit_map {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w * w = 1) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {L : Subgroup (MulAut W)} {S H : Type} [Group S] [Group H] (π : ↥L →* S)
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center ↥L)
    (hKp : ¬ p ∣ Nat.card π.ker) (ι : H →* S) (hι : Function.Injective ι) {U₀ T₀ : Subgroup H}
    (hUc : ∀ a ∈ U₀, ∀ b ∈ U₀, a * b = b * a) (hUp : ∀ a ∈ U₀, a ^ p = 1) (hU : U₀ ≠ ⊥)
    (hTN : T₀ ≤ Subgroup.normalizer (U₀ : Set H)) {m : ℕ}
    (horb : ∀ D₀ : Subgroup H, D₀ ≤ U₀ → D₀.relIndex U₀ = p →
      m ≤ (T₀ ⊓ Subgroup.normalizer (D₀ : Set H)).relIndex T₀) :
    2 ^ (m * orderOf (2 : ZMod p)) ≤ Nat.card W := by
  refine two_pow_le_card_of_lift_orbit hW hp2 π hπ hker hKp (U₀ := U₀.map ι) (T₀ := T₀.map ι)
    ?_ ?_ ?_ (map_le_normalizer_map ι hTN) ?_
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hUc a ha b hb]
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hUp a ha, map_one]
  · intro h
    apply hU
    rw [eq_bot_iff]
    intro u hu
    have : ι u ∈ U₀.map ι := ⟨u, hu, rfl⟩
    rw [h, Subgroup.mem_bot, ← map_one ι] at this
    rw [Subgroup.mem_bot]
    exact hι this
  · intro D' hD' hrel
    set D := D'.comap ι with hDdef
    have hDmap : D.map ι = D' := Subgroup.map_comap_eq_self (hD'.trans (Subgroup.map_le_range _ _))
    have hDU : D ≤ U₀ := by
      intro x hx
      have : ι x ∈ U₀.map ι := hD' hx
      obtain ⟨y, hy, hyx⟩ := this
      rwa [← hι hyx]
    have hrelD : D.relIndex U₀ = p := by
      rw [← Subgroup.relIndex_map_map_of_injective D U₀ hι, hDmap]
      exact hrel
    have h1 := horb D hDU hrelD
    have hN : T₀.map ι ⊓ Subgroup.normalizer (D' : Set S) =
        (T₀ ⊓ Subgroup.normalizer (D : Set H)).map ι := by
      apply le_antisymm
      · rintro _ ⟨⟨t, ht, rfl⟩, htN⟩
        refine ⟨t, ⟨ht, ?_⟩, rfl⟩
        have htN' : ι t ∈ Subgroup.normalizer (D' : Set S) := htN
        show t ∈ Subgroup.normalizer (D : Set H)
        rw [Subgroup.mem_set_normalizer_iff] at htN' ⊢
        have htN := htN'
        intro x
        have h2 := htN (ι x)
        rw [← hDmap] at h2
        constructor
        · intro hx
          have : ι (t * x * t⁻¹) ∈ D.map ι := by
            rw [map_mul, map_mul, map_inv]
            exact h2.1 ⟨x, hx, rfl⟩
          obtain ⟨y, hy, hyx⟩ := this
          rwa [← hι hyx]
        · intro hx
          have : ι x ∈ D.map ι := by
            apply h2.2
            rw [← map_inv, ← map_mul, ← map_mul]
            exact ⟨_, hx, rfl⟩
          obtain ⟨y, hy, hyx⟩ := this
          rwa [← hι hyx]
      · rintro _ ⟨t, ⟨ht, htN⟩, rfl⟩
        refine ⟨⟨t, ht, rfl⟩, ?_⟩
        show ι t ∈ Subgroup.normalizer (D' : Set S)
        rw [← hDmap]
        exact map_le_normalizer_map ι (T := Subgroup.zpowers t) (U := D)
          (fun y hy => by
            obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
            exact Subgroup.zpow_mem _ htN k) ⟨t, Subgroup.mem_zpowers t, rfl⟩
    rw [hN, Subgroup.relIndex_map_map_of_injective _ _ hι]
    exact h1

end CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit
