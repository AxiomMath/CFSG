module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Facts
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.FactsModel
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.FactsTransport

public section

namespace CFSG.EvenSporadicStandard.HSStd

open Subgroup CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier CFSG.Blueprint
  CFSG.Blueprint.NativeSporadic
open scoped commutatorElement

theorem aut_apply_eq_iff {e : hsR ≃* MulAut hsP}
    (he : ∀ (x : hsR) (p : hsP), ((e x p : hsP) : Equiv.Perm (Fin 3850)) =
      x * p * (x : Equiv.Perm (Fin 3850))⁻¹) (x : hsR) (c : hsP) :
    e x c = c ↔ (x : Equiv.Perm (Fin 3850)) * c = c * x := by
  rw [← Subtype.coe_inj, he, mul_inv_eq_iff_eq_mul]

theorem hs_perfect_H
    (τ : ↥hsP) (hτ : (τ : Equiv.Perm (Fin 3850)) = hsT1) :
    ∃ Q : Subgroup ↥hsP, Q ≤ centralizer ({τ} : Set ↥hsP) ∧ ⁅Q, Q⁆ = Q ∧ τ ∈ Q := by
  obtain ⟨hC1, hperf, hT1⟩ := hs_perfect_spec
  have hle : hsPerf ≤ hsP := hC1.trans inf_le_left
  refine ⟨hsPerf.comap hsP.subtype, fun q hq => ?_, ?_, by rw [mem_comap]; simpa [hτ] using hT1⟩
  · have hq' : (q : Equiv.Perm (Fin 3850)) ∈ centralizer ({hsT1} : Set (Equiv.Perm (Fin 3850))) :=
      (mem_inf.1 (hC1 hq)).2
    rw [mem_centralizer_singleton_iff]
    exact Subtype.ext (by simpa [hτ] using mem_centralizer_singleton_iff.1 hq')
  · apply Subgroup.map_injective (f := hsP.subtype) hsP.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_comap_eq_self (by rwa [range_subtype]), hperf]

theorem layerZero_t1
    (τ : ↥hsP) (hτ : (τ : Equiv.Perm (Fin 3850)) = hsT1) :
    LayerZeroInvolution ↥hsP τ := by
  obtain ⟨e, he, -⟩ := hs_full_automorphism_model
  refine ⟨fun φ hφ => ?_, Or.inl (hs_perfect_H τ hτ)⟩
  obtain ⟨x, rfl⟩ := e.surjective φ
  have hx2 := hs_u1 (x : Equiv.Perm (Fin 3850)) x.2 fun c hc => by
    have hcτ : (⟨c, (mem_inf.1 hc).1⟩ : ↥hsP) ∈ centralizer ({τ} : Set ↥hsP) := by
      rw [mem_centralizer_singleton_iff]
      exact Subtype.ext (by simpa [hτ] using mem_centralizer_singleton_iff.1 (mem_inf.1 hc).2)
    exact (aut_apply_eq_iff he x ⟨c, (mem_inf.1 hc).1⟩).1 (hφ _ hcτ)
  rw [← map_mul, show x * x = 1 from Subtype.ext hx2, map_one]

theorem layerZero_t2
    (τ : ↥hsP) (hτ : (τ : Equiv.Perm (Fin 3850)) = hsT2) :
    LayerZeroInvolution ↥hsP τ := by
  obtain ⟨e, he, -⟩ := hs_full_automorphism_model
  have hodd : ∀ φ : MulAut ↥hsP, (∀ x ∈ centralizer ({τ} : Set ↥hsP), Odd (orderOf x) →
      φ x = x) → φ * φ = 1 := by
    intro φ hφ
    obtain ⟨x, rfl⟩ := e.surjective φ
    have key : ∀ (a : Equiv.Perm (Fin 3850)) (n : ℕ), a ∈ hsC2 → a ^ n = 1 → Odd n →
        (x : Equiv.Perm (Fin 3850)) * a = a * x := by
      intro a n ha han hn
      have haτ : (⟨a, (mem_inf.1 ha).1⟩ : ↥hsP) ∈ centralizer ({τ} : Set ↥hsP) := by
        rw [mem_centralizer_singleton_iff]
        exact Subtype.ext (by simpa [hτ] using mem_centralizer_singleton_iff.1 (mem_inf.1 ha).2)
      have hord : Odd (orderOf (⟨a, (mem_inf.1 ha).1⟩ : ↥hsP)) := by
        rw [← Subgroup.orderOf_coe]
        exact hn.of_dvd_nat (orderOf_dvd_of_pow_eq_one han)
      exact (aut_apply_eq_iff he x _).1 (hφ _ haτ hord)
    have hx2 := hs_u2b (x : Equiv.Perm (Fin 3850)) x.2
      (key _ 5 hsOddA_mem hsOddA_pow (by decide)) (key _ 3 hsOddB_mem hsOddB_pow (by decide))
    rw [← map_mul, show x * x = 1 from Subtype.ext hx2, map_one]
  exact ⟨fun φ hφ => hodd φ fun x hx _ => hφ x hx, Or.inr hodd⟩

theorem layerZero_hsP
    (τ : ↥hsP) (hτ : orderOf τ = 2) :
    LayerZeroInvolution ↥hsP τ := by
  have hτ' : orderOf (τ : Equiv.Perm (Fin 3850)) = 2 := by rwa [Subgroup.orderOf_coe]
  obtain ⟨-, -, -, -, hcover⟩ := CFSG.Sporadic.SmallOddCore.hs_reps
  obtain ⟨r, hr, g, hg, hrg⟩ := hcover τ τ.2 hτ'
  have hτg : ∀ τ₀ : ↥hsP, (τ₀ : Equiv.Perm (Fin 3850)) = r →
      τ = (⟨g, hg⟩ : ↥hsP) * τ₀ * (⟨g, hg⟩ : ↥hsP)⁻¹ := fun τ₀ h0 =>
    Subtype.ext (by simp [h0, hrg])
  rcases hr with rfl | rfl
  · rw [hτg ⟨hsT1, hsT1_mem_ord.1⟩ rfl]
    exact (layerZero_t1 ⟨hsT1, hsT1_mem_ord.1⟩ rfl).conj _
  · rw [hτg ⟨hsT2, hsT2_mem_ord.1⟩ rfl]
    exact (layerZero_t2 ⟨hsT2, hsT2_mem_ord.1⟩ rfl).conj _

theorem exists_sylow_centralizerPerfect :
    ∃ T : Sylow 2 ↥hsP, CentralizerPerfect (T : Subgroup ↥hsP) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hcard, hT0C1, hcent⟩ := hs_t0_spec
  have hT0P : hsT0 ≤ hsP := hT0C1.trans inf_le_left
  have hT0Hcard : Nat.card (hsT0.subgroupOf hsP) = 2 ^ (Nat.card ↥hsP).factorization 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hT0P).toEquiv, hcard, card_hsP,
      show (44352000 : ℕ) = 2 ^ 9 * 86625 by norm_num, factorization_two_pow_mul (by norm_num)]
    norm_num
  refine ⟨Sylow.ofCard (hsT0.subgroupOf hsP) hT0Hcard, ?_⟩
  rw [Sylow.coe_ofCard]
  set z : ↥hsP := ⟨hsT1, hsT1_mem_ord.1⟩ with hz
  unfold CentralizerPerfect
  refine ⟨z, by rw [← Subgroup.orderOf_coe]; exact hsT1_mem_ord.2, ?_, hs_perfect_H z rfl⟩
  ext x
  rw [mem_centralizer_iff, mem_zpowers_iff]
  constructor
  · intro hx
    have hxc : (x : Equiv.Perm (Fin 3850)) ∈
        hsP ⊓ centralizer (hsT0 : Set (Equiv.Perm (Fin 3850))) := by
      refine mem_inf.2 ⟨x.2, ?_⟩
      rw [mem_centralizer_iff]
      intro s hs
      have := hx ⟨s, hT0P hs⟩ (by simpa [mem_subgroupOf] using hs)
      exact congrArg Subtype.val this
    rw [hcent, mem_zpowers_iff] at hxc
    obtain ⟨k, hk⟩ := hxc
    exact ⟨k, Subtype.ext (by simpa [hz] using hk)⟩
  · rintro ⟨k, rfl⟩ s hs
    have hs' : (s : Equiv.Perm (Fin 3850)) ∈ hsT0 := hs
    have hc : Commute (s : Equiv.Perm (Fin 3850)) hsT1 :=
      mem_centralizer_singleton_iff.1 (mem_inf.1 (hT0C1 hs')).2
    exact Subtype.ext (by simpa [hz] using (hc.zpow_right k).eq)

theorem hsFacts :
    HSFacts where
  invol Y _ h z hz := by
    obtain ⟨e₀⟩ := h
    have e : Y ≃* NativeSporadic.HS := e₀
    exact LayerZeroInvolution.of_mulEquiv (e.trans hsPermEquiv)
      (layerZero_hsP _ (by rw [MulEquiv.orderOf_eq]; exact hz))
  sylow_centralizer Y _ _ h R := by
    obtain ⟨e₀⟩ := h
    have e : Y ≃* NativeSporadic.HS := e₀
    obtain ⟨T, hT⟩ := exists_sylow_centralizerPerfect
    exact CentralizerPerfect.of_sylow (e.trans hsPermEquiv) T hT R

end CFSG.EvenSporadicStandard.HSStd
