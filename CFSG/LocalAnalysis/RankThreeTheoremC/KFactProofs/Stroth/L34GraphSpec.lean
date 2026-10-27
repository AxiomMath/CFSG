module

public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
public import Certificates.Certificate41502
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.L34Graph

open CFSG.ComponentClassification.PSL3Four CFSG.ABGLocalTools

theorem l34Graph_spec :
    ∃ T₀ : Subgroup (Equiv.Perm (Fin 42)), T₀ ≤ S ∧ Nat.card T₀ = 64 ∧
      ∀ x ∈ S, (∀ t ∈ T₀, x * t * x⁻¹ ∈ T₀) → x ^ 3 = 1 → x ≠ 1 →
        (∀ r ∈ R, (∀ t ∈ T₀, r * t * r⁻¹ ∈ T₀) → r * x = x * r → r ^ 4 = 1 → r ^ 2 = 1) ∧
        (∀ r ∈ R, (∀ t ∈ T₀, r * t * r⁻¹ ∈ T₀) → r * x = x * r →
          ∀ r' ∈ R, (∀ t ∈ T₀, r' * t * r'⁻¹ ∈ T₀) → r' * x = x * r' →
            r ^ 2 = 1 → r' ^ 2 = 1 → r ≠ 1 → r' ≠ 1 → r ≠ r' → r * r' ≠ r' * r) ∧
        (∀ r ∈ R, (∀ t ∈ T₀, r * t * r⁻¹ ∈ T₀) → r * x = x * r → r ^ 2 = 1 → r ≠ 1 →
          ∀ t ∈ S, t * x = x * t → t * r = r * t → t = 1 ∨ t = x ∨ t = x * x) :=
  Certificates.certificate41502

theorem l34Graph_of_sylow
    {S₁ : Subgroup (Equiv.Perm (Fin 42))} (hS₁S : S₁ ≤ S) (hS₁c : Nat.card S₁ = 64)
    {u : Equiv.Perm (Fin 42)} (huS : u ∈ S) (hu3 : u ^ 3 = 1) (hu1 : u ≠ 1)
    (huN : ∀ t ∈ S₁, u * t * u⁻¹ ∈ S₁) :
    (∀ r ∈ R, (∀ t ∈ S₁, r * t * r⁻¹ ∈ S₁) → r * u = u * r → r ^ 4 = 1 → r ^ 2 = 1) ∧
    (∀ r ∈ R, (∀ t ∈ S₁, r * t * r⁻¹ ∈ S₁) → r * u = u * r →
      ∀ r' ∈ R, (∀ t ∈ S₁, r' * t * r'⁻¹ ∈ S₁) → r' * u = u * r' →
        r ^ 2 = 1 → r' ^ 2 = 1 → r ≠ 1 → r' ≠ 1 → r ≠ r' → r * r' ≠ r' * r) ∧
    (∀ r ∈ R, (∀ t ∈ S₁, r * t * r⁻¹ ∈ S₁) → r * u = u * r → r ^ 2 = 1 → r ≠ 1 →
      ∀ t ∈ S, t * u = u * t → t * r = r * t → t = 1 ∨ t = u ∨ t = u * u) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T₀, hT₀S, hT₀c, hT₀⟩ := l34Graph_spec
  have hfac : (Nat.card S).factorization 2 = 6 := by
    rw [card_S, Nat.factorization_def _ Nat.prime_two,
      show (20160 : ℕ) = 2 ^ 6 * 315 by norm_num, padicValNat.mul (by norm_num) (by norm_num),
      padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd (by norm_num)]
  have hsyl₀ : IsSylowOf 2 T₀ S := isSylowOf_of_card hT₀S (by rw [hfac, hT₀c]; norm_num)
  have hsyl₁ : IsSylowOf 2 S₁ S := isSylowOf_of_card hS₁S (by rw [hfac, hS₁c]; norm_num)
  obtain ⟨s, hsS, hs⟩ := hsyl₀.exists_mem_conj hsyl₁
  let κ : Equiv.Perm (Fin 42) →* Equiv.Perm (Fin 42) := (MulAut.conj s⁻¹).toMonoidHom
  have hκ : ∀ y, κ y = s⁻¹ * y * s := fun y => by simp [κ, MulAut.conj_apply]
  have hκinj : Function.Injective κ := (MulAut.conj s⁻¹).injective
  have hsR : s ∈ R := S_le_R hsS
  have hκR : ∀ y ∈ R, κ y ∈ R := fun y hy => by
    rw [hκ]
    exact R.mul_mem (R.mul_mem (R.inv_mem hsR) hy) hsR
  have hκS : ∀ y ∈ S, κ y ∈ S := fun y hy => by
    rw [hκ]
    exact S.mul_mem (S.mul_mem (S.inv_mem hsS) hy) hsS
  have hκN : ∀ r, (∀ t ∈ S₁, r * t * r⁻¹ ∈ S₁) → ∀ t ∈ T₀, κ r * t * (κ r)⁻¹ ∈ T₀ := by
    intro r hr t ht
    have h1 : s * t * s⁻¹ ∈ S₁ :=
      (hs _).2 (by rw [show s⁻¹ * (s * t * s⁻¹) * s = t by group]; exact ht)
    have h2 := (hs _).1 (hr _ h1)
    rwa [show s⁻¹ * (r * (s * t * s⁻¹) * r⁻¹) * s = κ r * t * (κ r)⁻¹ by rw [hκ]; group] at h2
  have hκ1 : ∀ y, κ y = 1 → y = 1 := fun y hy => hκinj (by rw [hy, map_one])
  obtain ⟨hA, hB, hC⟩ := hT₀ (κ u) (hκS u huS) (hκN u huN) (by rw [← map_pow, hu3, map_one])
    (fun h => hu1 (hκ1 u h))
  refine ⟨?_, ?_, ?_⟩
  · intro r hrR hrN hru hr4
    have h2 := hA (κ r) (hκR r hrR) (hκN r hrN) (by rw [← map_mul, ← map_mul, hru])
      (by rw [← map_pow, hr4, map_one])
    exact hκ1 _ (by rw [map_pow, h2])
  · intro r hrR hrN hru r' hr'R hr'N hr'u hr2 hr'2 hr1 hr'1 hne hcomm
    refine hB (κ r) (hκR r hrR) (hκN r hrN) (by rw [← map_mul, ← map_mul, hru]) (κ r')
      (hκR r' hr'R) (hκN r' hr'N) (by rw [← map_mul, ← map_mul, hr'u])
      (by rw [← map_pow, hr2, map_one]) (by rw [← map_pow, hr'2, map_one])
      (fun h => hr1 (hκ1 r h)) (fun h => hr'1 (hκ1 r' h)) (fun h => hne (hκinj h)) ?_
    rw [← map_mul, ← map_mul, hcomm]
  · intro r hrR hrN hru hr2 hr1 t htS htu htr
    have h2 := hC (κ r) (hκR r hrR) (hκN r hrN) (by rw [← map_mul, ← map_mul, hru])
      (by rw [← map_pow, hr2, map_one]) (fun h => hr1 (hκ1 r h)) (κ t) (hκS t htS)
      (by rw [← map_mul, ← map_mul, htu]) (by rw [← map_mul, ← map_mul, htr])
    rcases h2 with h | h | h
    · exact Or.inl (hκ1 t h)
    · exact Or.inr (Or.inl (hκinj h))
    · exact Or.inr (Or.inr (hκinj (by rw [h, map_mul])))

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.L34Graph
