module

import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SmallRankOneLinTwo
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallDefs

public section

namespace CFSG.AGLEmbedding.KFactProofs.SmallIdent

open CFSG.Open CFSG.PSL2Table

theorem ncard_of_sq_invariant {F : Type} [Field F] [Finite F] (hq : Odd (Nat.card F))
    (S : Set F) (h0 : (0 : F) ∉ S) (hS : ∀ a ∈ S, ∀ μ : Fˣ, (μ : F) ^ 2 * a ∈ S) :
    S.ncard = 0 ∨ S.ncard = Nat.card F - 1 ∨ 2 * S.ncard = Nat.card F - 1 := by
  classical
  let Q : Subgroup Fˣ := (powMonoidHom 2 : Fˣ →* Fˣ).range
  have hunits : Nat.card Fˣ = Nat.card F - 1 := Nat.card_units F
  have heven : 2 ∣ Nat.card Fˣ := by
    rw [hunits]
    obtain ⟨k, hk⟩ := hq
    exact ⟨k, by omega⟩
  have hQcard : Nat.card Q = Nat.card Fˣ / 2 := by
    have h1 : Nat.card Q = Nat.card Fˣ / (Nat.card Fˣ).gcd 2 :=
      IsCyclic.card_powMonoidHom_range Fˣ 2
    rw [h1, Nat.gcd_eq_right heven]
  have hQ2 : 2 * Nat.card Q = Nat.card Fˣ := by
    rw [hQcard]
    exact Nat.mul_div_cancel' heven
  have hQpos : 0 < Nat.card Fˣ := Nat.card_pos
  have hindex : Q.index = 2 := by
    have h := Subgroup.index_mul_card Q
    have h2 : Q.index * Nat.card Q = 2 * Nat.card Q := by rw [h, hQ2]
    exact Nat.eq_of_mul_eq_mul_right (by omega) h2
  set S' : Set Fˣ := {u | (u : F) ∈ S} with hS'
  have hSS' : S = Units.val '' S' := by
    ext a
    constructor
    · intro ha
      have : a ≠ 0 := fun h => h0 (h ▸ ha)
      exact ⟨Units.mk0 a this, ha, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      exact hu
  have hncard : S.ncard = S'.ncard := by
    rw [hSS', Set.ncard_image_of_injective _ Units.val_injective]
  have hinv : ∀ u ∈ S', ∀ q ∈ Q, u * q ∈ S' := by
    rintro u hu _ ⟨μ, rfl⟩
    show ((u * μ ^ 2 : Fˣ) : F) ∈ S
    rw [Units.val_mul, Units.val_pow_eq_pow_val, mul_comm]
    exact hS _ hu μ
  by_cases hne : S'.Nonempty
  · obtain ⟨u₀, hu₀⟩ := hne
    by_cases hall : ∀ u ∈ S', u₀⁻¹ * u ∈ Q
    · right
      right
      have hS'eq : S' = (fun q => u₀ * q) '' (Q : Set Fˣ) := by
        ext u
        constructor
        · intro hu
          exact ⟨u₀⁻¹ * u, hall u hu, by simp⟩
        · rintro ⟨q, hq', rfl⟩
          exact hinv u₀ hu₀ q hq'
      rw [hncard, hS'eq, Set.ncard_image_of_injective _ (mul_right_injective u₀)]
      rw [← hunits, ← hQ2]
      rw [← Nat.card_coe_set_eq]
      rfl
    · right
      left
      push Not at hall
      obtain ⟨u₁, hu₁, hnQ⟩ := hall
      have hall' : S' = Set.univ := by
        ext w
        simp only [Set.mem_univ, iff_true]
        by_cases hw : u₀⁻¹ * w ∈ Q
        · simpa using hinv u₀ hu₀ _ hw
        · have h2 : (u₀⁻¹ * w) * (u₀⁻¹ * u₁)⁻¹ ∈ Q := by
            rw [Subgroup.mul_mem_iff_of_index_two hindex, inv_mem_iff]
            exact iff_of_false hw hnQ
          have h3 : u₁ * ((u₀⁻¹ * w) * (u₀⁻¹ * u₁)⁻¹) = w := by
            rw [mul_inv_rev, inv_inv]
            calc u₁ * (u₀⁻¹ * w * (u₁⁻¹ * u₀)) = (u₁ * u₁⁻¹) * (u₀⁻¹ * u₀) * w := by
                  simp only [mul_assoc, mul_comm, mul_left_comm]
              _ = w := by simp
          rw [← h3]
          exact hinv u₁ hu₁ _ h2
      rw [hncard, hall', Set.ncard_univ, hunits]
  · left
    rw [hncard, Set.not_nonempty_iff_eq_empty.1 hne]
    simp

section Torus

variable {K : Type} [Group K] [Finite K] {p : ℕ}

theorem exists_torus_action_of_isSmallLinTwo [Fact p.Prime] (hp2 : p ≠ 2)
    (hK : IsSmallLinTwo p K) (T : Sylow p K) :
    ∃ φ : Multiplicative (GaloisField p 2) →* K, Function.Injective φ ∧
      φ.range = (T : Subgroup K) ∧
      ∀ μ : (GaloisField p 2)ˣ, ∃ c ∈ Subgroup.normalizer ((T : Subgroup K) : Set K),
        ∀ a : Multiplicative (GaloisField p 2), c * φ a * c⁻¹ =
          φ (Multiplicative.ofAdd ((μ : GaloisField p 2) ^ 2 * Multiplicative.toAdd a)) := by
  obtain ⟨d, hd, ⟨e₁⟩⟩ := hK
  obtain ⟨e₂⟩ := nonempty_mulEquiv_psl2GF_of_isLinTwoIndex hd
  let e : K ≃* PSL2GF p 2 := e₁.trans e₂
  have hfs : Function.Surjective (e : K →* PSL2GF p 2) := e.surjective
  have hUT : ((T.mapSurjective hfs : Sylow p (PSL2GF p 2)) : Subgroup (PSL2GF p 2)) =
      (T : Subgroup K).map e.toMonoidHom := Sylow.coe_mapSurjective hfs T
  obtain ⟨ψ, hψ, hψU, hψc⟩ :=
    CFSG.AGLEmbedding.exists_torus_action hp2 (by norm_num : 1 ≤ 2) (T.mapSurjective hfs)
  refine ⟨e.symm.toMonoidHom.comp ψ, e.symm.injective.comp hψ, ?_, fun μ => ?_⟩
  · ext t
    simp only [MonoidHom.mem_range, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    constructor
    · rintro ⟨m, rfl⟩
      have h1 : ψ m ∈ ψ.range := ⟨m, rfl⟩
      rw [hψU, hUT] at h1
      obtain ⟨t', ht', hEq⟩ := h1
      rw [← hEq]
      have h2 : e.symm (e.toMonoidHom t') = t' := e.symm_apply_apply t'
      rw [h2]
      exact ht'
    · intro ht
      have h1 : e t ∈ ψ.range := by
        rw [hψU, hUT]
        exact ⟨t, ht, rfl⟩
      obtain ⟨m, hm⟩ := h1
      exact ⟨m, by rw [hm]; simp⟩
  · obtain ⟨c, hcN, hc⟩ := hψc μ
    refine ⟨e.symm c, ?_, fun a => ?_⟩
    · apply Subgroup.mem_normalizer_fintype
      intro t ht
      have h1 : e t ∈ ((T.mapSurjective hfs : Sylow p (PSL2GF p 2)) : Subgroup (PSL2GF p 2)) := by
        rw [hUT]
        exact ⟨t, ht, rfl⟩
      have h2 := (Subgroup.mem_normalizer_iff.1 hcN (e t)).1 h1
      rw [hUT] at h2
      obtain ⟨t'', ht'', h3⟩ := h2
      have h4 : e.symm c * t * (e.symm c)⁻¹ = t'' := by
        apply e.injective
        simpa using h3.symm
      rw [h4]
      exact ht''
    · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      rw [← hc a]
      simp

theorem orbits_of_isSmallLinTwo (hp : p.Prime) (hp2 : p ≠ 2) (hK : IsSmallLinTwo p K)
    (T : Sylow p K) (O : Set K) (hO : O ⊆ (T : Set K) \ {1})
    (hinv : ∀ n ∈ Subgroup.normalizer ((T : Subgroup K) : Set K), ∀ t ∈ O, n * t * n⁻¹ ∈ O) :
    O.ncard = 0 ∨ O.ncard = p ^ 2 - 1 ∨ 2 * O.ncard = p ^ 2 - 1 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨φ, hφinj, hφT, hφc⟩ := exists_torus_action_of_isSmallLinTwo hp2 hK T
  let f : GaloisField p 2 → K := fun a => φ (Multiplicative.ofAdd a)
  have hfinj : Function.Injective f := fun a b h => Multiplicative.ofAdd.injective (hφinj h)
  set S : Set (GaloisField p 2) := {a | f a ∈ O} with hSdef
  have h0 : (0 : GaloisField p 2) ∉ S := by
    intro h
    have h1 : f 0 = 1 := by simp [f]
    exact (hO h).2 h1
  have hS : ∀ a ∈ S, ∀ μ : (GaloisField p 2)ˣ, (μ : GaloisField p 2) ^ 2 * a ∈ S := by
    intro a ha μ
    obtain ⟨c, hcN, hc⟩ := hφc μ
    have h1 : c * f a * c⁻¹ ∈ O := hinv c hcN _ ha
    have h2 : c * f a * c⁻¹ = f ((μ : GaloisField p 2) ^ 2 * a) := by
      simpa [f] using hc (Multiplicative.ofAdd a)
    show f ((μ : GaloisField p 2) ^ 2 * a) ∈ O
    rw [← h2]
    exact h1
  have hOS : O = f '' S := by
    ext t
    constructor
    · intro ht
      have hT' : t ∈ φ.range := by
        rw [hφT]
        exact (hO ht).1
      obtain ⟨m, rfl⟩ := hT'
      exact ⟨Multiplicative.toAdd m, ht, by simp [f]⟩
    · rintro ⟨a, ha, rfl⟩
      exact ha
  have hq : Nat.card (GaloisField p 2) = p ^ 2 := GaloisField.card p 2 (by norm_num)
  have hodd : Odd (Nat.card (GaloisField p 2)) := by
    rw [hq]
    exact (hp.odd_of_ne_two hp2).pow
  have hcount := ncard_of_sq_invariant hodd S h0 hS
  have hn : O.ncard = S.ncard := by
    rw [hOS, Set.ncard_image_of_injective _ hfinj]
  rw [hq] at hcount
  rw [hn]
  exact hcount

end Torus

end CFSG.AGLEmbedding.KFactProofs.SmallIdent
