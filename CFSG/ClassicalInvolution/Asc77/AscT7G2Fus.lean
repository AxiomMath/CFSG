module

public import CFSG.ClassicalInvolution.Asc77.AscT7G2Fin
public import CFSG.ClassicalInvolution.Asc77.AscT7F2Trans
public import CFSG.ClassicalInvolution.Asc77.AscT7G2Frat

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected


variable (p f : ℕ) [Fact p.Prime]

@[expose] def C25_20_fus : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25 p f Ω K K' W S R R' z t u₁ u₂ →
      Nat.card ↥(S : Subgroup G) = 4 * Nat.card ↥(R ⊔ R') →
        ∀ t' : G, t' ∈ (S : Subgroup G) → t' * t' = 1 → (∃ g : G, g * z * g⁻¹ = t') →
          conjSub t' R = R' → (¬ ∃ y : G, y * z * y⁻¹ = t' * z) →
            ∀ s ∈ (S : Subgroup G), conjSub s R = R → s ∉ R ⊔ R' → s * t' = t' * s →
              (∀ δ ∈ R ⊔ R', δ * t' = t' * δ → (s * δ) * (s * δ) ≠ 1) →
                (∀ x : G, x⁻¹ * s * x ∈ (S : Subgroup G) →
                    x⁻¹ * s * x ∉ R ⊔ R' ⊔ Subgroup.zpowers t') ∧
                  ∀ (i : ℕ) (x : G), x⁻¹ * s ^ (2 ^ (i + 1)) * x ∈ (S : Subgroup G) →
                    x⁻¹ * s ^ (2 ^ (i + 1)) * x ∈ R ⊔ R' ⊔ Subgroup.zpowers t'

variable {p f}

namespace T7G2

open T7F2

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]

theorem relIndex_B {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {S : Sylow 2 G}
    {R R' : Subgroup G} {z t u₁ u₂ t' : G}
    (hT : Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t')
    (h4 : Nat.card ↥(S : Subgroup G) = 4 * Nat.card ↥(R ⊔ R')) :
    (R ⊔ R' ⊔ Subgroup.zpowers t').relIndex (S : Subgroup G) = 2 := by
  have hRRN : R ⊔ R' ≤ Nsub S R := sup_le hT.R_le_N hT.R'_le_N
  have ht'n : t' ∉ R ⊔ R' := fun hmem => hT.t'_not_mem_N (hRRN hmem)
  have ht1 : t' ≠ 1 := fun h1 => ht'n (h1 ▸ (R ⊔ R').one_mem)
  have hz2 : orderOf t' = 2 := orderOf_eq_prime (by rw [pow_two]; exact hT.ht'2) ht1
  have hnorm : Subgroup.zpowers t' ≤ Subgroup.normalizer ((R ⊔ R' : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    exact conj_mem_RR hT hT.ht'S hx |> fun h1 => by simpa [hT.ht'inv] using h1
  have hinf : (R ⊔ R') ⊓ Subgroup.zpowers t' = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    rintro x ⟨hx1, k, hk⟩
    simp only at hk
    subst hk
    have hzz : t' ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hT.ht'2
    obtain ⟨m, hm⟩ := Int.even_or_odd' k
    rcases hm with rfl | rfl
    · rw [zpow_mul, hzz, one_zpow]
    · exfalso
      apply ht'n
      have : t' ^ (2 * m + 1) = t' := by
        rw [zpow_add, zpow_mul, hzz, one_zpow, one_mul, zpow_one]
      rwa [this] at hx1
  have hprod := T7A.card_sup_mul_card_inf hnorm
  rw [hinf, Subgroup.card_bot, Nat.card_zpowers, hz2, mul_one, sup_comm] at hprod
  have hBS : R ⊔ R' ⊔ Subgroup.zpowers t' ≤ (S : Subgroup G) :=
    sup_le (sup_le hT.hRS hT.hR'S) (Subgroup.zpowers_le.mpr hT.ht'S)
  have h2 := Subgroup.relIndex_mul_card (R ⊔ R' ⊔ Subgroup.zpowers t') (S : Subgroup G)
  rw [inf_eq_left.mpr hBS, hprod, h4] at h2
  have hρ : 0 < Nat.card ↥(R ⊔ R') := Nat.card_pos
  have : (R ⊔ R' ⊔ Subgroup.zpowers t').relIndex (S : Subgroup G) * (Nat.card ↥(R ⊔ R') * 2) =
      2 * (Nat.card ↥(R ⊔ R') * 2) := by rw [h2]; ring
  exact Nat.eq_of_mul_eq_mul_right (by positivity) this

theorem c25_20_inv_of_fus (h11 : C25_11 p f) (h16 : C25_16 p f) (hfus : C25_20_fus p f) :
    C25_20_inv p f := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp h4 t' ht'S ht'2 hg ht'R hnf
  by_contra hno
  push Not at hno
  have hT : Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t' := ⟨hyp, ht'S, ht'2, ht'R⟩
  obtain ⟨g, hg'⟩ := hg
  obtain ⟨s, hsN, hsn, hst'⟩ := exists_s hT h11 h16 h4 hg' hnf
  obtain ⟨hsS, hsR⟩ := mem_Nsub.mp hsN
  have hRRN : R ⊔ R' ≤ Nsub S R := sup_le hT.R_le_N hT.R'_le_N
  have hsemi : ∀ δ ∈ R ⊔ R', δ * t' = t' * δ → (s * δ) * (s * δ) ≠ 1 := by
    intro δ hδ hδt'
    have hδN : δ ∈ Nsub S R := hRRN hδ
    obtain ⟨hδS, hδR⟩ := mem_Nsub.mp hδN
    refine hno (s * δ) ((S : Subgroup G).mul_mem hsS hδS) ?_ ?_ ?_
    · rw [conjSub_mul, hδR, hsR]
    · intro hmem
      apply hsn
      have := (R ⊔ R').mul_mem hmem ((R ⊔ R').inv_mem hδ)
      simpa using this
    · calc s * δ * t' = s * (δ * t') := by group
        _ = s * (t' * δ) := by rw [hδt']
        _ = (s * t') * δ := by group
        _ = (t' * s) * δ := by rw [hst']
        _ = t' * (s * δ) := by group
  obtain ⟨h1, h2⟩ := hfus G Ω K K' W S R R' z t u₁ u₂ hyp h4 t' ht'S ht'2 ⟨g, hg'⟩ ht'R hnf
    s hsS hsR hsn hst' hsemi
  obtain ⟨x, hx, y, hy, hxy⟩ := hT.hqR.exists_not_commute
  exact T7F2.false_of_fusion (hom_eq_one_of_isSimpleGroup ⟨x, y, hxy⟩) S _
    (relIndex_B hT h4) s hsS h1 h2

theorem c25_20_of_fus (h11 : C25_11 p f) (h16 : C25_16 p f) (hfus : C25_20_fus p f) :
    C25_20 p f :=
  c25_20_of_inv h11 h16 (c25_20_inv_of_fus h11 h16 hfus)

end T7G2

end CFSG.ClassicalInvolution.Asc77
