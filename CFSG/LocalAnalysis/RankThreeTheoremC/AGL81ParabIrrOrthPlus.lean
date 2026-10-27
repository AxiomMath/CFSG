module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabIrrGeneric
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommOrthPlus
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabIrrOrthPlusRank
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabIrrOrthPlusOrder
import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusHubCenter

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabIrr

namespace OrthPlus

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.LeviBlock CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit CFSG.LieType.Universal.Spin
open CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm
open CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.OrthPlus

theorem autHom_eq_one_of_not_dvd {A : Type} [Group A] [Finite A] {Y P : Subgroup A} {r : ℕ}
    {K : Type} [Field K] [Finite K] [CharP K 2] {D : Finset ℕ}
    (ρ : ↥(orthElementaryGroup (quadPlus r K)) ≃* ↥Y)
    (hρ : ∀ x : ↥(orthElementaryGroup (quadPlus r K)),
      (x : GLV r K) ∈ plusFlagStab K r D ↔ ((ρ x : ↥Y) : A) ∈ P)
    (hPY : P ≤ Y) (hr4 : 4 ≤ r) (hD : ∀ d ∈ D, 1 ≤ d ∧ d ≤ r) (hD1 : r - 1 ∈ D → r ∈ D)
    (hna : ∃ x ∈ P, ∃ y ∈ P, x * y * x⁻¹ * y⁻¹ ∉ pCoreOf 2 P) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpK : ¬ p ∣ Nat.card Kˣ) (h43 : ¬ (r = 4 ∧ p = 3)) {b : A}
    (hbY : b ∈ Subgroup.normalizer (Y : Set A)) (hbP : b ∈ Subgroup.normalizer (P : Set A))
    (hW : WCent P b) {k : ℕ} (hk : b ^ p ^ k = 1) : autHom ρ ⟨b, hbY⟩ = 1 := by
  have hp_odd : Odd p := hp.odd_of_ne_two hp2
  have hr3 : 3 ≤ r := by omega
  have hD' : ∀ d ∈ D, d ≤ r := fun d hd => (hD d hd).2
  have hD1' : ∀ d ∈ D, 1 ≤ d := fun d hd => (hD d hd).1
  have ht : D.sup id = 0 ∨ D.sup id ∈ D := sup_eq_zero_or_mem D
  have hDt : ∀ d ∈ D, d ≤ D.sup id := fun d hd => Finset.le_sup (f := id) hd
  obtain ⟨m, htm⟩ : ∃ m, D.sup id + m = r :=
    ⟨r - D.sup id, by have := Finset.sup_le (f := id) (a := r) hD'; omega⟩
  have hm : m = 0 ∨ 2 ≤ m := eq_zero_or_two_le hr3 hD1 ht hDt htm
  have hblk : (∃ b ∈ D, 2 ≤ b - predCut D b) ∨ 2 ≤ m :=
    exists_block_of_nonabelian (ρ := ρ) (hρ := hρ) hPY hD1' hDt hD' ht htm hm hna
  have hsl : IsSemilinear (autHom ρ ⟨b, hbY⟩) := by
    rcases hr4.eq_or_lt with hr | hr5
    · subst hr
      have h4 : p ≠ 4 := by
        rintro rfl
        exact absurd hp (by norm_num)
      have : 3 < p := by
        have := hp.two_le
        have h3 : p ≠ 3 := fun h => h43 ⟨rfl, h⟩
        omega
      exact isSemilinear_of_pow_eq_one_four hp this _ (autHom_pow_eq_one ρ ⟨b, hbY⟩ hk)
    · exact isSemilinear_of_five_le (by omega) _
  have hN : NormFix hD' ht htm (autHom ρ ⟨b, hbY⟩) :=
    normFix_autHom (ρ := ρ) (hρ := hρ) hPY hr3 hD1' hDt hm hbY hbP hW
  obtain ⟨h, hh, hα, hblocks, hres⟩ := exists_data hr3 hD ht hDt htm hm hblk hsl
    (odd_orderOf_autHom ρ ⟨b, hbY⟩ hp_odd hk) hN
  obtain ⟨j, hj⟩ := exists_pow_eq_one_of_central_blocks hr3 hD ht hDt htm hh hblocks hres
  set ν := (orthElementaryGroup (quadPlus r K)).normalizerMonoidHom with hν
  have hn := mem_normalizer_orthElementaryGroup (mem_plusFlagStabO.1 hh).1
  have hαν : autHom ρ ⟨b, hbY⟩ = ν ⟨h, hn⟩ :=
    MulEquiv.ext fun x => Subtype.ext (by
      rw [hα, hν, Subgroup.normalizerMonoidHom_apply_apply_coe])
  have h1 : autHom ρ ⟨b, hbY⟩ ^ (2 * Nat.card Kˣ * 2 ^ j) = 1 := by
    rw [hαν, ← map_pow]
    have : (⟨h, hn⟩ : ↥(Subgroup.normalizer (orthElementaryGroup (quadPlus r K) :
        Set (GLV r K)))) ^ (2 * Nat.card Kˣ * 2 ^ j) = 1 := Subtype.ext hj
    rw [this, map_one]
  have hcop : Nat.Coprime (p ^ k) (2 * Nat.card Kˣ * 2 ^ j) := by
    refine Nat.Coprime.pow_left _ ?_
    have h2 : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).2 hp2
    exact (h2.mul_right ((Nat.Prime.coprime_iff_not_dvd hp).2 hpK)).mul_right (h2.pow_right _)
  exact (pow_eq_one_iff_of_coprime hcop).1 ⟨autHom_pow_eq_one ρ ⟨b, hbY⟩ hk, h1⟩

end OrthPlus

theorem parabIrrOn_idxD_of
    (hGA : CFSG.Open.GriessAllModelsStatement) :
    ParabIrrOn (CFSG.AGLEmbedding.IsLieOf CFSG.AGLEmbedding.IdxD) := by
  intro A _ _ Y P B N p hp hp2 hY h2 hF hpar hne hna hBp hcyc hBY hBP hW hNY hNP hNB hirr
  obtain ⟨r, K, _, _, _, D, ρ, hr4, hD, hD1, hρ⟩ :=
    ParabComm.OrthPlus.exists_flag_setup (CFSG.AGLEmbedding.oddCenterRest_of_griess hGA) hY h2 hF
      hpar hne
  by_cases h43 : r = 4 ∧ p = 3
  · obtain ⟨rfl, rfl⟩ := h43
    exact Or.inr (ParabComm.OrthPlus.four_le_pRank_three_of_equiv ρ)
  by_cases hpK : p ∣ Nat.card Kˣ
  · exact Or.inr (hr4.trans (OrthPlus.le_pRank_of_dvd_card_units (by omega) hp hp2 hpK ρ))
  refine Or.inl fun b hb => ?_
  obtain ⟨k, hk⟩ := hBp ⟨b, hb⟩
  have hk' : b ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
  exact ParabComm.OrthPlus.centralizes_of_autHom_eq_one ρ ⟨b, hBY hb⟩
    (OrthPlus.autHom_eq_one_of_not_dvd ρ hρ hpar.1 hr4 hD hD1 hna hp hp2 hpK h43 (hBY hb)
      (hBP hb) (hW b hb) hk')

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabIrr
