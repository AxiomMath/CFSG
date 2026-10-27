module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSmallPKFacts
public import Certificates.Certificate9460
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.L34ModelS
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UPrimeExcL34
import CFSG.LocalAnalysis.ComponentClassification.PSL3FourAutomorphisms

public section

namespace CFSG.AGLEmbedding

namespace KFactProofs.L34OuterGen

open CFSG.ComponentClassification.PSL3Four CFSG.PSL3Four.Native CFSG.ABGLocalTools

theorem exists_commuting_not_normalizing
    {T' : Subgroup (Equiv.Perm (Fin 42))} (hT'S : T' ≤ S)
    (hT'c : Nat.card T' = 9) {ρ : Equiv.Perm (Fin 42)} (hρR : ρ ∈ R) (hρ3 : ρ ^ 3 = 1)
    (hρS : ρ ∉ S) (hρT : ∀ t ∈ T', ρ * t * ρ⁻¹ ∈ T') :
    ∃ c ∈ S, c * ρ = ρ * c ∧ ∃ t ∈ T', c * t * c⁻¹ ∉ T' := by
  obtain ⟨T₀, hT₀S, hT₀c, hT₀⟩ := Certificates.certificate9460
  have hfac : (Nat.card S).factorization 3 = 2 := by
    rw [card_S, Nat.factorization_def _ Nat.prime_three,
      show (20160 : ℕ) = 3 ^ 2 * 2240 by norm_num, padicValNat.mul (by norm_num) (by norm_num),
      padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd (by norm_num)]
  have hsyl₀ : IsSylowOf 3 T₀ S := isSylowOf_of_card hT₀S (by rw [hfac, hT₀c]; norm_num)
  have hsyl' : IsSylowOf 3 T' S := isSylowOf_of_card hT'S (by rw [hfac, hT'c]; norm_num)
  obtain ⟨s, hsS, hs⟩ := hsyl₀.exists_mem_conj hsyl'
  obtain ⟨x, hx⟩ : ∃ x, x = s⁻¹ * ρ * s := ⟨_, rfl⟩
  have hsR : s ∈ R := S_le_R hsS
  have hxR : x ∈ R := by
    rw [hx]
    exact R.mul_mem (R.mul_mem (R.inv_mem hsR) hρR) hsR
  have hx3 : x ^ 3 = 1 := by
    calc x ^ 3 = s⁻¹ * ρ ^ 3 * s := by rw [hx, pow_three, pow_three]; group
      _ = 1 := by rw [hρ3]; group
  have hxS : x ∉ S := fun hxS => hρS (by
    rw [show ρ = s * x * s⁻¹ by rw [hx]; group]
    exact S.mul_mem (S.mul_mem hsS hxS) (S.inv_mem hsS))
  have hxN : ∀ t ∈ T₀, x * t * x⁻¹ ∈ T₀ := by
    intro t ht
    have h1 : s * t * s⁻¹ ∈ T' :=
      (hs _).2 (by rw [show s⁻¹ * (s * t * s⁻¹) * s = t by group]; exact ht)
    have h2 := (hs _).1 (hρT _ h1)
    rwa [show s⁻¹ * (ρ * (s * t * s⁻¹) * ρ⁻¹) * s = x * t * x⁻¹ by rw [hx]; group] at h2
  obtain ⟨c₀, hc₀S, hc₀x, t₀, ht₀, hnot⟩ := hT₀ x hxR hx3 hxS hxN
  refine ⟨s * c₀ * s⁻¹, S.mul_mem (S.mul_mem hsS hc₀S) (S.inv_mem hsS), ?_, s * t₀ * s⁻¹,
    (hs _).2 (by rw [show s⁻¹ * (s * t₀ * s⁻¹) * s = t₀ by group]; exact ht₀), fun hmem => hnot ?_⟩
  · calc s * c₀ * s⁻¹ * ρ = s * (c₀ * x) * s⁻¹ := by rw [hx]; group
      _ = s * (x * c₀) * s⁻¹ := by rw [hc₀x]
      _ = ρ * (s * c₀ * s⁻¹) := by rw [hx]; group
  · have := (hs _).1 hmem
    rwa [show s⁻¹ * (s * c₀ * s⁻¹ * (s * t₀ * s⁻¹) * (s * c₀ * s⁻¹)⁻¹) * s = c₀ * t₀ * c₀⁻¹ by
      group] at this

theorem congr_apply_apply {K G : Type} [Group K] [Group G] (ε : K ≃* G) (f : MulAut K) (k : K) :
    (MulAut.congr ε f) (ε k) = ε (f k) := by
  rw [MulAut.congr_apply]
  simp

theorem exists_fixed_not_mem_normalizer
    {K : Type} [Group K] [Finite K] (hK : IsLinThreeFour K)
    (T : Sylow 3 K) (f : MulAut K) (hf3 : f ^ 3 = 1)
    (hfout : f ∉ (MulAut.conj : K →* MulAut K).range)
    (hfT : ∀ t ∈ (T : Subgroup K), f t ∈ (T : Subgroup K)) :
    ∃ k : K, f k = k ∧ k ∉ Subgroup.normalizer ((T : Subgroup K) : Set K) := by
  obtain ⟨ε⟩ := L34ModelS.nonempty_mulEquiv_S_of_isLinThreeFour hK
  obtain ⟨φ, hφ, hφS⟩ := full_automorphism_action
  let ι : K →* Equiv.Perm (Fin 42) := S.subtype.comp ε.toMonoidHom
  have hι : ∀ k, ι k = ((ε k : S) : Equiv.Perm (Fin 42)) := fun k => rfl
  have hι_inj : Function.Injective ι := Subtype.val_injective.comp ε.injective
  let ρR : ↥R := φ.symm (MulAut.congr ε f)
  have hφρ : φ ρR = MulAut.congr ε f := φ.apply_symm_apply _
  have hρ : ∀ k : K, ι (f k) = (ρR : Equiv.Perm (Fin 42)) * ι k * (ρR : Equiv.Perm (Fin 42))⁻¹ := by
    intro k
    have h1 := hφ ρR (ε k)
    rw [hφρ, congr_apply_apply] at h1
    rw [hι, hι, h1]
    rfl
  have hρ3 : (ρR : Equiv.Perm (Fin 42)) ^ 3 = 1 := by
    have : ρR ^ 3 = 1 := by
      apply φ.injective
      rw [map_pow, hφρ, ← map_pow, hf3, map_one, map_one]
    simpa using congrArg Subtype.val this
  have hρS : (ρR : Equiv.Perm (Fin 42)) ∉ S := by
    intro hS
    have hmem : φ ρR ∈ (MulAut.conj : S →* MulAut S).range :=
      hφS ▸ Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hS)
    obtain ⟨g, hg⟩ := hmem
    refine hfout ⟨ε.symm g, MulEquiv.ext fun k => ε.injective ?_⟩
    rw [hφρ] at hg
    have := congrArg (fun α : MulAut S => α (ε k)) hg
    simp only [MulAut.conj_apply, congr_apply_apply] at this
    simp [this]
  let T' : Subgroup (Equiv.Perm (Fin 42)) := (T : Subgroup K).map ι
  have hT'S : T' ≤ S := by
    rintro _ ⟨t, -, rfl⟩
    exact (ε t).2
  have hT'c : Nat.card T' = 9 := by
    rw [Subgroup.card_map_of_injective hι_inj]
    exact KFactProofs.UPrimeExcL34.card_sylow_three_of_isLinThreeFour hK T
  have hρT : ∀ t ∈ T', (ρR : Equiv.Perm (Fin 42)) * t * (ρR : Equiv.Perm (Fin 42))⁻¹ ∈ T' := by
    rintro _ ⟨t, ht, rfl⟩
    rw [← hρ]
    exact ⟨f t, hfT t ht, rfl⟩
  obtain ⟨c, hcS, hcρ, t', ht', hnot⟩ :=
    exists_commuting_not_normalizing hT'S hT'c ρR.2 hρ3 hρS hρT
  refine ⟨ε.symm ⟨c, hcS⟩, ?_, fun hk => hnot ?_⟩
  · apply hι_inj
    rw [hρ]
    have : ι (ε.symm ⟨c, hcS⟩) = c := by rw [hι]; simp
    rw [this, ← hcρ]
    group
  · obtain ⟨t, ht, rfl⟩ := ht'
    have hk' := (Subgroup.mem_normalizer_iff.1 hk t).1 ht
    have : ι (ε.symm ⟨c, hcS⟩) = c := by rw [hι]; simp
    rw [← this, ← map_mul, ← map_inv, ← map_mul]
    exact ⟨_, hk', rfl⟩

end KFactProofs.L34OuterGen

open CFSG.ComponentClassification.PSL3Four in
theorem kFactL34OuterGen :
    KFactL34OuterGen := by
  intro K _ _ hK T f hf3 hfout hfT Y hY hNY
  by_contra hYtop
  obtain ⟨e⟩ := KFactProofs.UPrimeExcL34.nonempty_equiv_projSL hK
  have hTcard := KFactProofs.UPrimeExcL34.card_sylow_three_of_isLinThreeFour hK T
  have hYN : Y = Subgroup.normalizer ((T : Subgroup K) : Set K) :=
    CFSG.RankThree.PartTwo.KFacts.L34Max.eq_normalizer_of_normalizer_le e hTcard hNY hYtop
  obtain ⟨k, hkf, hkN⟩ :=
    KFactProofs.L34OuterGen.exists_fixed_not_mem_normalizer hK T f hf3 hfout hfT
  exact hkN (hYN ▸ hY k hkf)

end CFSG.AGLEmbedding
