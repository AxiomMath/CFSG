module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.BorelLocal
import CFSG.RankThree.PartOne.KP.SporadicDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open Subgroup CFSG.AGLEmbeddingD2 CFSG.ComponentClassification.OuterAutomorphisms

theorem zin_eq_inf_centralizer {K : Type} [Group K] (S : Subgroup K) :
    Zin S = S ⊓ centralizer (S : Set K) := by
  ext x
  constructor
  · rintro ⟨⟨y, hy⟩, hyc, rfl⟩
    refine Subgroup.mem_inf.2 ⟨hy, Subgroup.mem_centralizer_iff.2 ?_⟩
    intro h hh
    have := Subgroup.mem_center_iff.mp hyc ⟨h, hh⟩
    exact congrArg Subtype.val this
  · intro hx
    obtain ⟨hxS, hxc⟩ := Subgroup.mem_inf.1 hx
    refine Subgroup.mem_map.2 ⟨⟨x, hxS⟩, ?_, rfl⟩
    refine Subgroup.mem_center_iff.2 fun g => ?_
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hxc g g.2)

theorem heis_local {i : TauCeti.CFSGIndex} {p : ℕ} (H : D2HeisLocalAt i fun q => q = p)
    {K : Type} [Group K] [Finite K] (hK : Nonempty (K ≃* i.Group)) (hcen : Subgroup.center K = ⊥)
    (S : Sylow p K) :
    ¬ p ∣ Nat.card (Outer ↥(⊤ : Subgroup K)) ∧ Nat.card (S : Subgroup K) = p ^ 3 ∧
      (∀ Y : Subgroup K, normalizer ((S : Subgroup K) : Set K) ≤ Y →
        Y = normalizer ((S : Subgroup K) : Set K) ∨ Y = ⊤) ∧
      Nat.card ((S : Subgroup K) ⊓ centralizer ((S : Subgroup K) : Set K) : Subgroup K) = p ∧
      ⁅(S : Subgroup K), (S : Subgroup K)⁆ =
        (S : Subgroup K) ⊓ centralizer ((S : Subgroup K) : Set K) ∧
      (∀ r ∈ (S : Subgroup K), r ^ p = 1) ∧
      ∃ t ∈ normalizer ((S : Subgroup K) : Set K), ∃ m : ℕ, 2 ≤ m ∧
        ∀ j : ℕ, 0 < j → j < m → ∀ F : Subgroup K,
          (S : Subgroup K) ⊓ centralizer ((S : Subgroup K) : Set K) ≤ F → F ≤ (S : Subgroup K) →
            F.relIndex (S : Subgroup K) = p → t ^ j ∉ normalizer (F : Set K) := by
  obtain ⟨e⟩ := hK
  have hKc : Subgroup.centralizer (((⊤ : Subgroup K) : Subgroup K) : Set K) = ⊥ := by
    rw [Subgroup.coe_top, Subgroup.centralizer_univ, hcen]
  obtain ⟨hout, hcard, hmax, -, hZ, hcomm, hexp, -, t, htN, m, -, -, hm, -, -, -, -, hline⟩ :=
    H K ⊤ inferInstance hKc ⟨Subgroup.topEquiv.trans e⟩ p rfl S
  exact ⟨hout, hcard, hmax, hZ, hcomm, hexp, t, htN, m, hm, hline⟩

theorem extra_of_d2Heis {i : TauCeti.CFSGIndex} {p : ℕ} (hp : p.Prime)
    (H : D2HeisLocalAt i fun q => q = p) {T : ℕ → ∀ (Q : Type) [Group Q], Prop}
    (hT : ∀ (K : Type) [Group K] [Finite K], T p K → Nonempty (K ≃* i.Group) ∧ Subgroup.center K = ⊥) :
    (∀ (K : Type) [Group K] [Finite K], T p K → SylowIsHeisenberg p K) ∧
    (∀ (K : Type) [Group K] [Finite K], T p K → NoOuterP p K) ∧
    (∀ (K : Type) [Group K] [Finite K], T p K → NormalizerMaximal p K) ∧
    (∀ (K : Type) [Group K] [Finite K], T p K → NormalizerIrreducibleQuotient p K) := by
  haveI : Fact p.Prime := ⟨hp⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro K _ _ hK S
    obtain ⟨hKe, hcen⟩ := hT K hK
    obtain ⟨-, hcard, -, hZ, hcomm, hexp, -⟩ := heis_local H hKe hcen S
    refine ⟨hcard, ?_, hexp⟩
    by_contra hnon
    have hall : ∀ a ∈ (S : Subgroup K), ∀ b ∈ (S : Subgroup K), a * b = b * a := by
      intro a ha b hb
      by_contra hab
      exact hnon ⟨a, ha, b, hb, hab⟩
    have h1 : ⁅(S : Subgroup K), (S : Subgroup K)⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro a ha b hb
      exact (hall b hb a ha)
    rw [h1] at hcomm
    have : Nat.card ((S : Subgroup K) ⊓ centralizer ((S : Subgroup K) : Set K) : Subgroup K) = 1 := by
      rw [← hcomm]; simp
    rw [hZ] at this
    exact hp.one_lt.ne' this
  · intro K _ _ hK
    obtain ⟨hKe, hcen⟩ := hT K hK
    obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow p K))
    obtain ⟨hout, -⟩ := heis_local H hKe hcen S
    unfold NoOuterP
    have hcard := CFSG.RankThree.PartOne.card_outer_eq_of_mulEquiv
      (Subgroup.topEquiv : (⊤ : Subgroup K) ≃* K)
    rw [← hcard]
    exact hout
  · intro K _ _ hK S
    obtain ⟨hKe, hcen⟩ := hT K hK
    exact (heis_local H hKe hcen S).2.2.1
  · intro K _ _ hK S A hZA hAS hNA
    obtain ⟨hKe, hcen⟩ := hT K hK
    obtain ⟨-, hcard, -, hZ, -, -, t, htN, m, hm, hline⟩ := heis_local H hKe hcen S
    rw [zin_eq_inf_centralizer] at hZA ⊢
    by_contra hne
    rw [not_or] at hne
    obtain ⟨hAZ, hAS'⟩ := hne
    have hdvd : Nat.card A ∣ p ^ 3 := hcard ▸ Subgroup.card_dvd_of_le hAS
    obtain ⟨k, hk3, hk⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    have hZA' : p ≤ Nat.card A := by
      have := Subgroup.card_le_of_le hZA
      rwa [hZ] at this
    have hk2 : k = 2 := by
      interval_cases k
      · rw [pow_zero] at hk
        have := hp.one_lt
        omega
      · exfalso
        exact hAZ (Subgroup.eq_of_le_of_card_ge hZA (by rw [hZ, hk]; simp)).symm
      · rfl
      · exfalso
        exact hAS' (Subgroup.eq_of_le_of_card_ge hAS (by omega))
    subst hk2
    have hrel : A.relIndex (S : Subgroup K) = p := by
      have h1 := Subgroup.relIndex_mul_card (H := A) (K := (S : Subgroup K))
      rw [inf_eq_left.mpr hAS, hk, hcard] at h1
      have hp0 : 0 < p ^ 2 := pow_pos hp.pos 2
      have : A.relIndex (S : Subgroup K) * p ^ 2 = p * p ^ 2 := by rw [h1]; ring
      exact Nat.eq_of_mul_eq_mul_right hp0 this
    exact hline 1 one_pos (by omega) A hZA hAS hrel (by simpa using hNA htN)

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
