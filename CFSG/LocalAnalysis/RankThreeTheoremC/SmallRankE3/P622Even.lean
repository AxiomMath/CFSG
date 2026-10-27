module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622Basic
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.S622Sylow
import CFSG.LocalAnalysis.RankThreeUC.TheoremDClauseCCore
public import CFSG.Monster.B.Fischer.Fi22Order

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x z : G}
  {T S : Subgroup G}

theorem p622_odd_core (hKD : P622KFactD) (hS : Setting G) (c : P622Conf p P M x z T S)
    (hnc : ¬ SmallRankCover p M x) : Odd (Nat.card (smallRankD p x)) := by
  by_contra hodd
  have hprime : p.Prime := sigmaA_prime p c.failure.situation.mem_sigmaA
  have hp2 : p ≠ 2 := sigmaA_odd p c.failure.situation.mem_sigmaA
  haveI : Fact p.Prime := ⟨hprime⟩
  obtain ⟨H, hH⟩ : ∃ H : Subgroup G, H = centralizer ({x} : Set G) := ⟨_, rfl⟩
  obtain ⟨D, hDdef⟩ : ∃ D : Subgroup G, D = smallRankD p x := ⟨_, rfl⟩
  have hspec : D ≤ H ∧ H ≤ normalizer (D : Set G) ∧ Nat.Coprime p (Nat.card D) := by
    rw [hDdef, hH]
    exact CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec p _
  obtain ⟨hDH, hHD, hcop⟩ := hspec
  have hev : Even (Nat.card D) := by
    rw [hDdef]
    exact Nat.not_odd_iff_even.mp hodd
  have hpD : ¬ p ∣ Nat.card D := (Nat.Prime.coprime_iff_not_dvd hprime).mp hcop
  have hDn : (D.subgroupOf H).Normal := (normal_subgroupOf_iff_le_normalizer hDH).mpr hHD
  have hBp : IsPGroup p ↥(zpowers x ⊔ zpowers z) := P.isPGroup'.to_le c.B_le_P
  have hBH : zpowers x ⊔ zpowers z ≤ H := hH ▸ c.B_le_centralizer
  have hBD : zpowers x ⊔ zpowers z ≤ normalizer (D : Set G) := hBH.trans hHD
  have hmax : IsMaxTwoInvariantIn (zpowers x ⊔ zpowers z) H S := hH ▸ c.isMax
  have hV := CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.s622_isSylowOf_inf hprime hp2 hBp hDH
    hDn hpD hBD hmax
  have hzD : z ∈ normalizer (D : Set G) := hBD (mem_sup_right (mem_zpowers z))
  have hzS : z ∈ normalizer (S : Set G) := c.z_le_normalizer (mem_zpowers z)
  have hzV : z ∈ normalizer ((S ⊓ D : Subgroup G) : Set G) :=
    inf_normalizer_le_normalizer_inf ⟨hzS, hzD⟩
  have hVne : S ⊓ D ≠ ⊥ := by
    intro hbot
    have hcard := hV.card_eq
    rw [hbot, Subgroup.card_bot] at hcard
    have h2 : 2 ∣ Nat.card D := even_iff_two_dvd.mp hev
    have hpos : 0 < Nat.card D := Nat.card_pos
    have h1 : 1 ≤ (Nat.card D).factorization 2 :=
      (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two hpos.ne').mp h2
    have h3 : 2 ^ 1 ≤ 2 ^ (Nat.card D).factorization 2 :=
      Nat.pow_le_pow_right (by norm_num) h1
    omega
  have hVN : normalizer ((S ⊓ D : Subgroup G) : Set G) ≤ M :=
    c.normalizer_le hS inf_le_left hVne (zpowers_le.mpr hzV)
  have hFrat := CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.s622_le_sup_normalizer Nat.prime_two
    hDH hDn hV
  have hKD' := hKD G p D (S ⊓ D) (M ⊓ D) z hprime hp2
    (hDdef ▸ p622_isKGroup_primeCore hS c.failure.point.ne_one)
    (orderOf_eq_prime c.failure.central.pow_eq_one c.failure.central.ne_one) hzD hpD hV hzV
    inf_le_right
    (fun U hUV hU1 hzU => inf_le_inf_right D
      (c.normalizer_le hS (hUV.trans inf_le_left) hU1 (zpowers_le.mpr hzU)))
    (inf_le_inf_right D (c.centralizer_le_M hS))
    (fun U hUD hU2 hU1 hUz => inf_le_inf_right D
      (c.normalizer_le_of_invariant hU2 hU1 (hUz.trans (c.centralizer_le_M hS))
        (c.B_le_normalizer_of_z (hUD.trans (hH ▸ hDH))
          (CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.s622_zpowers_le_normalizer_of_le_centralizer
            hUz))))
  have hDle : D ≤ (M ⊓ H) ⊔ rankThreePrimeCore 2 D :=
    hKD'.trans (sup_le_sup_right (inf_le_inf_left M hDH) _)
  have hNle : normalizer ((S ⊓ D : Subgroup G) : Set G) ⊓ H ≤
      (M ⊓ H) ⊔ rankThreePrimeCore 2 D := (inf_le_inf_right H hVN).trans le_sup_left
  have hcov : H ≤ (M ⊓ H) ⊔ rankThreePrimeCore 2 D := hFrat.trans (sup_le hDle hNle)
  apply hnc
  rw [hDdef, hH] at hcov
  exact hcov

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
