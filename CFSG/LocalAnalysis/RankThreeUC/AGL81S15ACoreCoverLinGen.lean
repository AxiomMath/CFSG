module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACoreLift
public import CFSG.Open.LocalVocabulary
import CFSG.RankThree.CentralLift.ClassicalCoverTools

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.ACore

open CFSG.RankThree.PerfectCover

theorem exists_odd_central_quotient {K J : Type} [Group K] [Finite K] [Group J] (ρ : K →* J)
    (hρ : Function.Surjective ρ) (hker : ρ.ker = Subgroup.center K) :
    ∃ (N : Subgroup K) (_ : N.Normal) (q : K ⧸ N →* J) (j : ℕ), Nat.card N = 2 ^ j ∧
      Function.Surjective q ∧ q.ker ≤ Subgroup.center (K ⧸ N) ∧ ¬ 2 ∣ Nat.card q.ker ∧
      Nat.card (Subgroup.center K) = 2 ^ j * Nat.card q.ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ : Nonempty (Sylow 2 (Subgroup.center K)) := inferInstance
  set N : Subgroup K := (P : Subgroup (Subgroup.center K)).map (Subgroup.center K).subtype
  have hNc : N ≤ Subgroup.center K := Subgroup.map_subtype_le _
  have : N.Normal := Subgroup.normal_of_le_center hNc
  have hNker : N ≤ ρ.ker := hker ▸ hNc
  set q : K ⧸ N →* J := QuotientGroup.lift N ρ hNker with hq
  have hqker : q.ker = (Subgroup.center K).map (QuotientGroup.mk' N) := by
    rw [hq, QuotientGroup.ker_lift, hker]
  let f : Subgroup.center K →* K ⧸ N := (QuotientGroup.mk' N).comp (Subgroup.center K).subtype
  have hfk : f.ker = (P : Subgroup (Subgroup.center K)) := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    exact Subgroup.mem_map_iff_mem (Subgroup.center K).subtype_injective
  have hfr : f.range = q.ker := by
    rw [hqker, MonoidHom.range_comp, Subgroup.range_subtype]
  have hcard : Nat.card (P : Subgroup (Subgroup.center K)) * Nat.card q.ker =
      Nat.card (Subgroup.center K) := by
    rw [← hfk, ← hfr]
    exact Subgroup.card_ker_mul_card_range f
  have hPN : Nat.card N = Nat.card (P : Subgroup (Subgroup.center K)) :=
    Subgroup.card_subtype _ _
  obtain ⟨j, hj⟩ := (P.isPGroup'.map (Subgroup.center K).subtype).exists_card_eq
  refine ⟨N, inferInstance, q, j, hj, QuotientGroup.lift_surjective_of_surjective N ρ hρ hNker,
    ?_, fun h2 => ?_, ?_⟩
  · rw [hqker]
    exact Subgroup.map_center_le_center (QuotientGroup.mk'_surjective N)
  · have hidx : Nat.card q.ker = (P : Subgroup (Subgroup.center K)).index :=
      Nat.eq_of_mul_eq_mul_left Nat.card_pos (hcard.trans (Subgroup.card_mul_index _).symm)
    exact P.not_dvd_index (hidx ▸ h2)
  · rw [← hcard, ← hPN, hj]

theorem coverId_of_two_index {S₀ K : Type} [Group S₀] [Finite S₀] [Group K] [Finite K]
    (hS₀ : Group.IsPerfect S₀) (hK : Group.IsPerfect K) (D : Subgroup S₀) [D.Normal]
    (hD : D ≤ Subgroup.center S₀) (ρ : K →* S₀ ⧸ D) (hρ : Function.Surjective ρ)
    (hker : ρ.ker = Subgroup.center K) {k : ℕ}
    (hcard : Nat.card (hopfMultiplier (S₀ ⧸ D)) = Nat.card D * 2 ^ k) :
    ∃ (Z₀ : Subgroup S₀) (_ : Z₀.Normal) (j : ℕ), Z₀ ≤ D ∧
      Nat.card (Subgroup.center K) = 2 ^ j * (Nat.card D / Nat.card Z₀) ∧
      ∀ r : ℕ, r.Prime → r ≠ 2 → CFSG.Open.pRank r (⊤ : Subgroup K) =
        CFSG.Open.pRank r (⊤ : Subgroup (S₀ ⧸ Z₀)) := by
  obtain ⟨N, hNn, q, j, hj, hqs, hqc, hq2, hZ⟩ := exists_odd_central_quotient ρ hρ hker
  have hcop : Nat.Coprime (Nat.card q.ker) (2 ^ k) :=
    Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hq2).symm
  have hk₀ : (QuotientGroup.mk' D).ker ≤ Subgroup.center S₀ := by
    rwa [QuotientGroup.ker_mk']
  obtain ⟨α, -, hαc⟩ := exists_lift_of_coprime_card hS₀ inferInstance (QuotientGroup.mk' D)
    (QuotientGroup.mk'_surjective D) hk₀ q hqs hqc hcop (by rwa [QuotientGroup.ker_mk'])
  obtain ⟨-, hZD, -, ⟨e, -⟩, ⟨eC⟩⟩ := CFSG.RankThree.CentralLift.cover_map_of_comp_eq
    (QuotientGroup.mk'_surjective D) hqc hαc
  rw [QuotientGroup.ker_mk'] at hZD
  refine ⟨α.ker, inferInstance, j, hZD, ?_, fun r hr hr2 => ?_⟩
  ·
    have h1 : Nat.card q.ker = Nat.card ((QuotientGroup.mk' D).ker ⧸
        α.ker.subgroupOf (QuotientGroup.mk' D).ker) := Nat.card_congr eC.toEquiv
    rw [QuotientGroup.ker_mk'] at h1
    have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (α.ker.subgroupOf D)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZD).toEquiv] at h2
    rw [hZ, h1, h2, Nat.mul_div_cancel _ Nat.card_pos]
  · haveI : Fact r.Prime := ⟨hr⟩
    have hrN : ¬ r ∣ Nat.card N := by
      rw [hj]
      exact fun h => hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h))
    rw [← CFSG.SectionRank.pRank_quotient_eq N hrN,
      CFSG.SectionRank.pRank_top_eq_of_mulEquiv hr.one_lt e.symm]

end CFSG.LocalAnalysis.RankThreeUC.S15.ACore
