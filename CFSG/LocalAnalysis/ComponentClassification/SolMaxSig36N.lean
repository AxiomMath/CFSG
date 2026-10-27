module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig36B
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig36F

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

theorem pResidual_two_eq_top [Finite X] [IsSimpleGroup X] (hnab : ∃ a b : X, a * b ≠ b * a) :
    CFSG.Quasithin.pResidual 2 X = ⊤ := by
  refine eq_top_iff.2 (le_iInf fun N => le_iInf fun hN => le_iInf fun hp => ?_)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · exfalso
    have h2 : IsPGroup 2 X := fun x => by
      obtain ⟨k, hk⟩ := hp x
      rw [h, mem_bot] at hk
      exact ⟨k, hk⟩
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hc : Nontrivial (center X) := h2.center_nontrivial
    rcases (inferInstance : (center X).Normal).eq_bot_or_eq_top with hz | hz
    · rw [hz] at hc
      obtain ⟨x, y, hxy⟩ := hc
      exact hxy (Subsingleton.elim x y)
    · obtain ⟨a, b, hab⟩ := hnab
      exact hab (mem_center_iff.mp (hz ▸ mem_top a : a ∈ center X) b).symm
  · rw [h]

theorem sign_eq_neg_one_of_two {m : ℕ} {σ : Perm (Fin m)} (hσ : σ * σ = 1)
    (h2 : σ.support.card = 2) : Perm.sign σ = -1 := by
  have hne : σ ≠ 1 := by
    rintro rfl
    rw [Perm.support_one, Finset.card_empty] at h2
    omega
  have hord : orderOf σ = 2 := orderOf_eq_prime (by rw [sq]; exact hσ) hne
  obtain ⟨k, hk⟩ := Perm.cycleType_prime_order (σ := σ) (by rw [hord]; exact Nat.prime_two)
  rw [hord] at hk
  have hsum := Perm.sum_cycleType σ
  rw [hk, h2, Multiset.sum_replicate, smul_eq_mul] at hsum
  have hk0 : k = 0 := by omega
  rw [Perm.sign_of_cycleType, hk, hk0, Multiset.sum_replicate, Multiset.card_replicate,
    smul_eq_mul]
  decide

namespace Sig36

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}
  (S : Sig36 X t J n e E D)
include S

theorem false_of_add_two (h33 : Sol78.BalanceLemmaInput) (h35 : SignalizerLemma35)
    (hT13 : Sol76T13.SolomonThm13Simple) (hML : Sol78.MaximalityLemmaInput)
    (hSch : SolAltLit.SchurAlternatingMultiplierInput) {M : Subgroup X} {m : ℕ} (hm : m = n + 2)
    (hMH : M ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))))
    (hJM : J ≤ M)
    (hHN : normalizer (Sol78.signalizerCompletion E E : Set X) ≤ normalizer (M : Set X))
    (hker : ∀ g ∈ normalizer (Sol78.signalizerCompletion E E : Set X),
      g ∈ UnbalancedLayer.coreActionKernel M → Odd (orderOf g))
    {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin m)}
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin m)} (hρ : IsPermAction θ ρ)
    (hA : ∀ (x : X) (hx : x ∈ normalizer (Sol78.signalizerCompletion E E : Set X)), x * x = 1 →
      (ρ ⟨x, hHN hx⟩).support.card = 4 →
        centralizer ({x} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X)) :
    False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := normalizer (Sol78.signalizerCompletion E E : Set X) with hHdef
  have hn9 := S.nine_le
  have hCt : centralizer ({t} : Set X) ≤ H :=
    S.centralizer_le_normalizer_completion h33 h35 hT13 hML hSch
  have htH : t ∈ H := hCt (mem_centralizer_singleton_iff.mpr rfl)
  have ht2 : t * t = 1 := by rw [← sq, ← S.pair.1.1, pow_orderOf_eq_one]
  obtain ⟨θ', ρ', hρ', hcard⟩ :=
    S.exists_isPermAction_of_pumped hT13 hML hSch hMH hMpc (hHN htH) hJM (by omega) θ
  have ht2' : (ρ ⟨t, hHN htH⟩).support.card = 2 := by
    have h1 := hρ.card_support_eq hρ' (by omega) (by omega) ⟨t, hHN htH⟩
    omega
  have hsq : ∀ g : ↥(normalizer (M : Set X)), (g : X) * g = 1 → ρ g * ρ g = 1 := by
    intro g hg
    rw [← map_mul, show g * g = 1 from Subtype.ext hg, map_one]
  have hsignt : Perm.sign (ρ ⟨t, hHN htH⟩) = -1 := sign_eq_neg_one_of_two (hsq _ ht2) ht2'
  have hfus : ∀ g : X, g * t * g⁻¹ ∈ H → g ∈ H := fun g hg =>
    hρ.mem_of_conj_mem (by omega) hMH hHN hker hA ht2 hCt hg
  obtain ⟨P, hPH⟩ := exists_sylow_le_of_conj_mem htH ht2 hfus
  let σ : ↥(P : Subgroup X) →* ℤˣ :=
    Perm.sign.comp (ρ.comp (Subgroup.inclusion (hPH.trans hHN)))
  set Q : Subgroup X := σ.ker.map (P : Subgroup X).subtype with hQdef
  have hQP : Q ≤ (P : Subgroup X) := map_subtype_le _
  have hsignconj : ∀ g : X, ∀ hg : g ∈ H, ∀ hgt : g * t * g⁻¹ ∈ H,
      Perm.sign (ρ ⟨g * t * g⁻¹, hHN hgt⟩) = -1 := by
    intro g hg hgt
    have h1 : (⟨g * t * g⁻¹, hHN hgt⟩ : ↥(normalizer (M : Set X))) =
        ⟨g, hHN hg⟩ * ⟨t, hHN htH⟩ * (⟨g, hHN hg⟩)⁻¹ := rfl
    rw [h1, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, hsignt,
      mul_comm (Perm.sign _) (-1), mul_assoc, mul_inv_cancel, mul_one]
  have hnoconj : ∀ g : X, g * t * g⁻¹ ∉ Q := by
    rintro g ⟨⟨u, huP⟩, hu, hug⟩
    have hgtH : g * t * g⁻¹ ∈ H := hPH (hug ▸ huP)
    have hgH := hfus g hgtH
    have h1 := hsignconj g hgH hgtH
    have h2 : σ ⟨u, huP⟩ = 1 := hu
    have h3 : σ ⟨u, huP⟩ = Perm.sign (ρ ⟨g * t * g⁻¹, hHN hgtH⟩) := by
      change Perm.sign (ρ ⟨u, hHN (hPH huP)⟩) = _
      congr 2
      exact Subtype.ext hug
    rw [h2, h1] at h3
    exact absurd h3 (by decide)
  obtain ⟨h₀, hh₀⟩ := exists_conj_mem_of_card_eq (G := ↥H) (H := (P : Subgroup X).subgroupOf H)
    (by
      rw [Nat.card_congr (subgroupOfEquivOfLe hPH).toEquiv, P.card_eq_multiplicity]
      congr 1
      have h1 : 2 ^ (Nat.card X).factorization 2 ∣ Nat.card H := by
        rw [← P.card_eq_multiplicity]
        exact card_dvd_of_le hPH
      have h2 : Nat.card H ∣ Nat.card X := card_subgroup_dvd_card H
      apply le_antisymm
      · exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two
          (Nat.card_pos (α := ↥H)).ne').mp h1
      · exact (Nat.factorization_le_iff_dvd (Nat.card_pos (α := ↥H)).ne'
          (Nat.card_pos (α := X)).ne').mpr h2 2)
    (x := (⟨t, htH⟩ : ↥H)) (isPGroup_zpowers_of_mul_self (Subtype.ext ht2))
  rw [mem_subgroupOf] at hh₀
  have hu : ((h₀ : X) * t * (h₀ : X)⁻¹) ∈ (P : Subgroup X) := by simpa using hh₀
  have hσu : σ ⟨_, hu⟩ = -1 := by
    change Perm.sign (ρ ⟨(h₀ : X) * t * (h₀ : X)⁻¹, hHN (hPH hu)⟩) = -1
    exact hsignconj h₀ h₀.2 (hPH hu)
  have hrange : σ.range = ⊤ := by
    rw [eq_top_iff]
    intro z _
    rcases Int.units_eq_one_or z with rfl | rfl
    · exact one_mem _
    · exact ⟨_, hσu⟩
  have hidx : Q.relIndex (P : Subgroup X) = 2 := by
    rw [hQdef, relIndex, subgroupOf_map_subtype_self, Subgroup.index_ker, hrange,
      Subgroup.card_top, Nat.card_eq_fintype_card, Fintype.card_units_int]
  have hT := CFSG.Quasithin.thompson_transfer_lemma P hQP hidx S.pair.1.1 (fun x hx => by
    have h1 := hnoconj x⁻¹
    rw [inv_inv] at h1
    exact h1 hx)
  rw [pResidual_two_eq_top S.nonab] at hT
  exact hT (mem_top t)

end Sig36

end CFSG.ComponentClassification.SolMax
