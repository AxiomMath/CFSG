module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Concl

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.GLTheoremB CFSG.SectionRank

theorem i165On_of_cover_sc {P : GLALabel → ℕ → Prop}
    (hcov : ∀ (K : Type) [Group K] [Finite K] (lab : GLALabel) (p q : ℕ),
      HasLabel K (fun l : GLALabel => l = lab) → P lab p →
      p.Prime → p ≠ 2 → q.Prime → q ≠ 2 → q ≠ p →
      (∀ lab' : GLALabel, HasLabel K (fun l : GLALabel => l = lab') → ¬ GLASplit16 p lab') →
      evenRank K = GLATwoLocalRank q K → 4 ≤ evenRank K →
      ∃ (H : Type) (_ : Group H) (_ : Finite H) (π : H →* K),
        Function.Surjective π ∧ π.ker ≤ Subgroup.center H ∧ ¬ p ∣ Nat.card π.ker ∧
        ∀ Ã : Subgroup H, IsElemAbelian p Ã →
          (∀ g ∈ Subgroup.centralizer (Ã : Set H), orderOf g = p → g ∈ Ã) →
          CFSG.Open.pRank p (⊤ : Subgroup H) ≤ CFSG.Open.pRank p Ã →
          3 ≤ CFSG.Open.pRank p Ã → Concl165Avoid H p q Ã π.ker) :
    I165On P := by
  intro K _ _ lab p q hK hP hp hp2 hq hq2 hqp hns hZ A hAe hSC h12 hmax hb he hm1 hm4
  have hm3 : 3 ≤ CFSG.Open.pRank p A := by omega
  have hm4K : 4 ≤ evenRank K := le_trans hm4 hm1
  obtain ⟨H, hHgrp, hHfin, π, hπ, hker, hpk, hconcl⟩ :=
    hcov K lab p q hK hP hp hp2 hq hq2 hqp hns he hm4K
  letI := hHgrp
  letI := hHfin
  obtain ⟨R, -, hRe, hRmap, -⟩ :=
    CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.exists_elemAbelian_lift hp hpk
      (Subgroup.map_comap_eq_self_of_surjective hπ A) hAe
  haveI : Fact p.Prime := ⟨hp⟩
  have hquot : CFSG.Open.pRank p (⊤ : Subgroup (H ⧸ π.ker)) =
      CFSG.Open.pRank p (⊤ : Subgroup H) :=
    CFSG.SectionRank.pRank_quotient_eq π.ker hpk
  have hiso : CFSG.Open.pRank p (⊤ : Subgroup (H ⧸ π.ker)) =
      CFSG.Open.pRank p (⊤ : Subgroup K) :=
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt
      (QuotientGroup.quotientKerEquivOfSurjective π hπ)
  have hRankH : CFSG.Open.pRank p (⊤ : Subgroup H) =
      CFSG.Open.pRank p (⊤ : Subgroup K) := hquot.symm.trans hiso
  have hRankR : CFSG.Open.pRank p R = CFSG.Open.pRank p A := by
    have hRp : IsPGroup p R :=
      CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.isPGroup_of_pow_eq_one hRe.2
    have hinj : Function.Injective (π.comp R.subtype) := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro x hx
      have hx' : ((x : H)) ∈ R ⊓ π.ker := ⟨x.2, hx⟩
      rw [CFSG.GroupTheory.SteinbergBS.inf_eq_bot_of_isPGroup_of_not_dvd hpk hRp,
        Subgroup.mem_bot] at hx'
      exact Subtype.ext hx'
    have htop : (⊤ : Subgroup R).map (π.comp R.subtype) = R.map π := by
      rw [Subgroup.map_top, MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← hRmap, ← htop, pRank_eq_pRank_top_subgroup R]
    exact (CFSG.LocalAnalysis.GLTheoremB.pRank_map_eq_of_injective hp.one_lt
      (π.comp R.subtype) hinj ⊤).symm
  have hRmax : CFSG.Open.pRank p (⊤ : Subgroup H) ≤ CFSG.Open.pRank p R := by
    rw [hRankH, hRankR]
    exact hmax
  have hR3 : 3 ≤ CFSG.Open.pRank p R := by
    rw [hRankR]
    exact hm3
  have hRSC : ∀ g ∈ Subgroup.centralizer (R : Set H), orderOf g = p → g ∈ R := by
    intro g hg hgord
    have hgcen : π g ∈ Subgroup.centralizer (A : Set K) := by
      rw [Subgroup.mem_centralizer_iff] at hg ⊢
      intro a ha
      rw [← hRmap] at ha
      obtain ⟨r, hrR, rfl⟩ := ha
      simpa only [map_mul] using congrArg π (hg r hrR)
    have hgordp : orderOf (π g) = p := by
      have hdiv : orderOf (π g) ∣ p := hgord ▸ orderOf_map_dvd π g
      have hne : orderOf (π g) ≠ 1 := by
        intro h1
        have hgker : g ∈ π.ker := by
          rw [MonoidHom.mem_ker]
          exact orderOf_eq_one_iff.mp h1
        have hgdvd : orderOf g ∣ Nat.card π.ker := by
          have := orderOf_dvd_natCard (⟨g, hgker⟩ : ↥π.ker)
          simpa [Subgroup.orderOf_mk] using this
        exact hpk (hgord ▸ hgdvd)
      rcases (Nat.dvd_prime hp).1 hdiv with h | h
      · exact absurd h hne
      · exact h
    have hmemA : π g ∈ A := hSC (π g) hgcen hgordp
    rw [← hRmap] at hmemA
    obtain ⟨r, hrR, hrg⟩ := hmemA
    have hzker : g * r⁻¹ ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hrg, mul_inv_cancel]
    have hcomm : Commute g r :=
      (Subgroup.mem_centralizer_iff.1 hg r hrR).symm
    have hgp : g ^ p = 1 := by rw [← hgord]; exact pow_orderOf_eq_one g
    have hrp : r ^ p = 1 := hRe.2 r hrR
    have hzp : (g * r⁻¹) ^ p = 1 := by
      rw [hcomm.inv_right.mul_pow, hgp, inv_pow, hrp, inv_one, mul_one]
    have hzdvd : orderOf (g * r⁻¹) ∣ p := orderOf_dvd_of_pow_eq_one hzp
    have hzdvdker : orderOf (g * r⁻¹) ∣ Nat.card π.ker := by
      have := orderOf_dvd_natCard (⟨g * r⁻¹, hzker⟩ : ↥π.ker)
      simpa [Subgroup.orderOf_mk] using this
    have hcop : Nat.Coprime p (Nat.card π.ker) :=
      (Nat.Prime.coprime_iff_not_dvd hp).2 hpk
    have hz1 : g * r⁻¹ = 1 :=
      orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop hzdvd hzdvdker)
    have hgr : g = r := by
      have h := congrArg (fun x => x * r) hz1
      rw [one_mul] at h
      rwa [mul_assoc, inv_mul_cancel, mul_one] at h
    rw [hgr]
    exact hrR
  have hA' : Concl165 K p q (R.map π) :=
    concl165_map_of_central hp hq π hπ hker hpk (hconcl R hRe hRSC hRmax hR3)
  rw [hRmap] at hA'
  simpa only [Concl165] using hA'

theorem i165On_of_model_sc {P : GLALabel → ℕ → Prop}
    (hmodel : ∀ (K : Type) [Group K] [Finite K] (lab : GLALabel) (p q : ℕ),
      HasLabel K (fun l : GLALabel => l = lab) → P lab p →
      p.Prime → p ≠ 2 → q.Prime → q ≠ 2 → q ≠ p →
      (∀ lab' : GLALabel, HasLabel K (fun l : GLALabel => l = lab') → ¬ GLASplit16 p lab') →
      evenRank K = GLATwoLocalRank q K → 4 ≤ evenRank K →
      ∀ A : Subgroup K, IsElemAbelian p A →
        (∀ g ∈ Subgroup.centralizer (A : Set K), orderOf g = p → g ∈ A) →
        CFSG.Open.pRank p (⊤ : Subgroup K) ≤ CFSG.Open.pRank p A →
        3 ≤ CFSG.Open.pRank p A → Concl165 K p q A) : I165On P := by
  refine i165On_of_cover_sc ?_
  intro K _ _ lab p q hK hP hp hp2 hq hq2 hqp hns he hm4
  refine ⟨K, inferInstance, inferInstance, MonoidHom.id K, Function.surjective_id, ?_, ?_, ?_⟩
  · rw [MonoidHom.ker_id]
    exact bot_le
  · rw [MonoidHom.ker_id, Subgroup.card_bot]
    exact Nat.Prime.not_dvd_one hp
  · intro A hAe hASC hmax hA3
    obtain ⟨D, E, F, J, hDE, hEA, hD, hE, hJ, hAJ, hlay, hFD, hF, hFJ, hF3⟩ :=
      hmodel K lab p q hK hP hp hp2 hq hq2 hqp hns he hm4 A hAe hASC hmax hA3
    refine ⟨D, E, F, J, hDE, hEA, hD, hE, hJ, hAJ, hlay, hFD, hF, hFJ, hF3, ?_⟩
    rw [MonoidHom.ker_id]
    exact inf_bot_eq F


end CFSG.LocalAnalysis.GLTheoremA.Y10F
