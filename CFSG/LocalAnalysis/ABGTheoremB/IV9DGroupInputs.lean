module

public import CFSG.LocalAnalysis.ABGTheoremB.V4Inputs
import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.ConjugacyBasic
import CFSG.LocalAnalysis.ABGTheoremB.IV9DGroupInputsTransport
import CFSG.LocalAnalysis.ABGTheoremB.IV9DGroupInputsQuotient
import CFSG.GroupTheory.ABGLocalTools.PStabilityRelative

public section

namespace CFSG.ABGTheoremB

open CFSG.QuasiDihedralFusion CFSG.ABGDGroups CFSG.ABGTheoremB.IV9DGroups

variable {G : Type} [Group G] [Finite G] {σ : Setting G}

namespace IV9DGroups

theorem D_le_centralizer_x (hσ : σ.IsValid) : σ.D ≤ Subgroup.centralizer ({σ.x} : Set G) := by
  intro d hd
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact Subgroup.mem_centralizer_iff.mp hσ.x_mem_center.2 d (σ.D_le_S hd)

theorem D_ne_T (hσ : σ.IsValid) : σ.D ≠ σ.T := by
  intro hDT
  have hT4 : Nat.card σ.T = 4 := (TotallyInverted.Conjugacy.isKleinFour_T hσ).card_four
  have hS : 4 < Nat.card (σ.S : Subgroup G) := by
    rcases hσ.sylow with ⟨-, n, hn⟩ | hw
    · obtain ⟨f⟩ := hn.2 σ.S
      rw [← Nat.card_congr f.toEquiv, CFSG.Semidihedral.card n (by have := hn.1; omega)]
      calc 4 < 2 ^ 4 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn.1
    · obtain ⟨e⟩ := hw.2 σ.S
      rw [Nat.card_congr e.toEquiv, CFSG.Wreathed.card_wreath]
      have h4 : 4 ≤ 2 ^ σ.height :=
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ σ.height := Nat.pow_le_pow_right (by norm_num) hw.1
      nlinarith
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTS := σ.T_le_S hσ
  have hlt : σ.T.subgroupOf σ.S < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    have hTeq : σ.T = σ.S := by
      refine le_antisymm hTS fun s hs => ?_
      have hs' : (⟨s, hs⟩ : (σ.S : Subgroup G)) ∈ σ.T.subgroupOf σ.S := htop ▸ Subgroup.mem_top _
      exact hs'
    rw [hTeq] at hT4
    omega
  have hnil : Group.IsNilpotent (σ.S : Subgroup G) := σ.S.isPGroup'.isNilpotent
  have hnorm := Group.normalizerCondition_of_isNilpotent (G := (σ.S : Subgroup G)) _ hlt
  rw [← Subgroup.subgroupOf_normalizer_eq hTS] at hnorm
  obtain ⟨⟨n, hnS⟩, hnN, hnT⟩ := IsConcreteLE.exists_of_lt hnorm
  apply hnT
  have hnD : n ∈ σ.D := ⟨hnS, hnN⟩
  rw [hDT] at hnD
  exact hnD

end IV9DGroups

theorem Setting.dGroupSignalizerInput_of (hσ : σ.IsValid) : V4.DGroupSignalizerInput σ := by
  intro _ H hDH hDG Z hZH hZ hZD
  have hTD := σ.T_le_D hσ
  have hTH : σ.T ≤ H := hTD.trans hDH
  have hxH : σ.x ∈ H := hTH σ.x_mem_T
  have hT : IsKleinFour σ.T := TotallyInverted.Conjugacy.isKleinFour_T hσ
  have hD2 : IsPGroup 2 σ.D := σ.S.isPGroup'.to_le σ.D_le_S
  have hT2 : IsPGroup 2 σ.T := hD2.to_le hTD
  have hQ : IsDGroup (H ⧸ CFSG.oddCore H) := isDGroup_quotient_oddCore hDG
  have hO : CFSG.oddCore (H ⧸ CFSG.oddCore H) = ⊥ :=
    CFSG.ABGLocalTools.oddCore_quotient_oddCore_eq_bot
  have hDT : quotImage H σ.D ≠ quotImage H σ.T := by
    intro h
    apply D_ne_T hσ
    have hcard := congrArg (fun K : Subgroup (H ⧸ CFSG.oddCore H) => Nat.card K) h
    rw [card_quotImage_of_isPGroup hDH hD2, card_quotImage_of_isPGroup hTH hT2] at hcard
    exact (Subgroup.eq_of_le_of_card_ge hTD hcard.le).symm
  have hxD : quotImage H σ.D ≤ Subgroup.centralizer
      ({QuotientGroup.mk' (CFSG.oddCore H) (⟨σ.x, hxH⟩ : H)} : Set (H ⧸ CFSG.oddCore H)) := by
    intro y hy
    obtain ⟨d, hd, hdH, rfl⟩ := exists_of_mem_quotImage hy
    exact mk_mem_centralizer_singleton hdH hxH (D_le_centralizer_x hσ hd)
  have hx1 : QuotientGroup.mk' (CFSG.oddCore H) (⟨σ.x, hxH⟩ : H) ≠ 1 := by
    rw [Ne, mk_eq_one_iff hxH]
    intro hxO
    have h1 := Subgroup.orderOf_dvd_natCard (oddCoreIn H) hxO
    rw [hσ.x_order] at h1
    exact (Nat.not_even_iff_odd.mpr (odd_card_oddCoreIn H)) (even_iff_two_dvd.mpr h1)
  obtain ⟨W, hWodd, hZW, hWx, hCW⟩ := exists_odd_le_centralizer hQ hO
    (isKleinFour_quotImage hTH hT) (quotImage_mono hTD) (isPGroup_quotImage hDH hD2) hDT
    (quotImage_le_normalizer inf_le_right) (mk_mem_quotImage hxH σ.x_mem_T) hx1 hxD
    (odd_card_quotImage hZ) (quotImage_le_normalizer hZD)
  exact le_sup_oddCoreIn_of_quotImage_le hxH hσ.x_order hWodd hWx hCW hZH hZW

end CFSG.ABGTheoremB
