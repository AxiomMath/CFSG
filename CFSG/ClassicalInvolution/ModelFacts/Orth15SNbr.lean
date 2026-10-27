module

public import CFSG.ClassicalInvolution.Asc77.WP3LayerSec
public import CFSG.ClassicalInvolution.AschTight.HypOmegaGenMod
public import CFSG.ClassicalInvolution.AschTight.Sec6Gen64E

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen
open scoped commutatorElement

section Coprime

variable {G : Type} [Group G] [Finite G]

theorem exists_isSylow2In_inf_centralizer_of_trivialOnQuot {J : Subgroup G} {c z : G}
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) (hcJ : c ∈ trivialOnQuot J) (hcz : c * z = z * c) :
    ∃ P : Subgroup G, IsSylow2In P (J ⊓ Subgroup.centralizer ({z} : Set G)) ∧
      P ≤ Subgroup.centralizer ({c} : Set G) := by
  set D : Subgroup G := J ⊓ Subgroup.centralizer ({z} : Set G) with hD
  set O : Subgroup G := oddCoreIn J ⊓ D with hO
  have hA : Subgroup.zpowers c ≤ trivialOnQuot J := Subgroup.zpowers_le.mpr hcJ
  have hAz : Subgroup.zpowers c ≤ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hcz)
  have hOD : O ≤ D := inf_le_right
  have hOnorm : D ≤ Subgroup.normalizer (O : Set G) := by
    intro d hd
    have key : ∀ d ∈ D, ∀ h ∈ O, d * h * d⁻¹ ∈ O := by
      intro d hd h hh
      have hdJ' : d ∈ Subgroup.normalizer (J : Set G) := Subgroup.le_normalizer hd.1
      exact ⟨conj_mem_oddCoreIn_of_mem_normalizer hdJ' hh.1, D.mul_mem (D.mul_mem hd hh.2)
        (D.inv_mem hd)⟩
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => key d hd h hh, fun hh => ?_⟩
    have := key d⁻¹ (D.inv_mem hd) _ hh
    simpa [mul_assoc] using this
  have hOodd : Odd (Nat.card O) :=
    (odd_card_oddCoreIn J).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have hOle : O ≤ oddCoreOf D := le_oddCoreOf_of_normal hOD hOnorm hOodd
  have hcomm : ⁅Subgroup.zpowers c, D⁆ ≤ oddCoreOf D := by
    refine le_trans (Subgroup.commutator_le.mpr fun a ha x hx => ?_) hOle
    have haJ := (hA ha)
    have h1 : ⁅a, x⁆ ∈ oddCoreIn J := (mem_trivialOnQuot_iff.mp haJ).2 x hx.1
    have haN : a ∈ Subgroup.normalizer (J : Set G) := (mem_trivialOnQuot_iff.mp haJ).1
    have h2J : ⁅a, x⁆ ∈ J := by
      rw [commutatorElement_def]
      exact J.mul_mem ((Subgroup.mem_normalizer_iff.mp haN x).mp hx.1) (J.inv_mem hx.1)
    have h2z : ⁅a, x⁆ ∈ Subgroup.centralizer ({z} : Set G) := by
      rw [commutatorElement_def]
      exact (Subgroup.centralizer {z}).mul_mem
        ((Subgroup.centralizer {z}).mul_mem
          ((Subgroup.centralizer {z}).mul_mem (hAz ha) hx.2) ((Subgroup.centralizer {z}).inv_mem
            (hAz ha))) ((Subgroup.centralizer {z}).inv_mem hx.2)
    have h2 : ⁅a, x⁆ ∈ D := ⟨h2J, h2z⟩
    exact ⟨h1, h2⟩
  obtain ⟨P, hP, hPc⟩ := AscE184Sect.exists_isSylow2In_centralizer hc2 hcomm
  exact ⟨P, hP, by rwa [centralizer_zpowers_eq_singleton'] at hPc⟩

end Coprime

section Nbr

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem not_mem_omegaNbr_of_exact (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) {K J : Subgroup G} (hK : K ∈ tqMembers Ω c)
    (hJ : J ∈ tqMembers Ω c) (hKJ : K ≠ J) {z : G} (hz : IsUniqueInvolution K z)
    (hzK : z ∈ exactCore c K)
    (h : ¬ ∃ T : Subgroup G, IsSylow2In T (exactCore c J) ∧
        T ≤ Subgroup.normalizer ((exactCore c K : Subgroup G) : Set G)) :
    J ∉ omegaNbr Ω K := by
  rintro ⟨-, -, R', hR', hR'J, hR'N⟩
  have hΩg : HypOmegaGen Ω := hypOmegaGen_of_mod hp hq hΩ
  have hR'syl : IsSylow2In R' J := isSylow2In_of_mem_RSet_of_le hΩg hJ.1 hR' hR'J
  have hR'z : R' ≤ Subgroup.centralizer ({z} : Set G) := le_centralizer_of_le_normalizer' hz hR'N
  have hzc : c * z = z * c :=
    (Subgroup.mem_centralizer_singleton_iff.mp (exactCore_le_centralizer c K hzK)).symm
  obtain ⟨P, hPD, hPc⟩ := exists_isSylow2In_inf_centralizer_of_trivialOnQuot hc2 hJ.2 hzc
  have hR'D : R' ≤ J ⊓ Subgroup.centralizer ({z} : Set G) := le_inf hR'J hR'z
  have hle : Nat.card R' ≤ Nat.card P := hPD.natCard_le hR'syl.2.1 hR'D
  have hPJ : IsSylow2In P J := hR'syl.of_natCard_le hPD.2.1 (hPD.1.trans inf_le_left) hle
  have hPJc : IsSylow2In P (exactCore c J) :=
    (isSylow2In_exactCore_iff hΩ hc2 hJ.1 hJ.2).mpr ⟨hPJ, hPc⟩
  have h3 : 3 ≤ Nat.card P := by
    have := eight_le_of_mem_RSet hΩg hR'
    omega
  have hPK : P ≤ Subgroup.normalizer (K : Set G) :=
    le_normalizer_of_le_centralizer hΩg hK.1 hJ.1 hKJ hz hPJ.1 hPJ.2.1 h3
      (hPD.1.trans inf_le_right)
  have hPKc : P ≤ Subgroup.normalizer ((exactCore c K : Subgroup G) : Set G) := by
    intro b hb
    have hnorm : b ∈ Subgroup.normalizer
        ((K ⊓ Subgroup.centralizer ({c} : Set G) : Subgroup G) : Set G) :=
      mem_normalizer_inf (hPK hb) (Subgroup.le_normalizer (hPc hb))
    exact CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf_normalizer_contains _ hnorm
  exact h ⟨P, hPJc, hPKc⟩

end Nbr

end CFSG.ClassicalInvolution.Asc77
