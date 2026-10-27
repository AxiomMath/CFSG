module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8S12Ord
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87TwoCov
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93M12Bender
public import CFSG.Timmesfeld.Orders.Classical

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.Blueprint CFSG.ComponentClassification CFSG.GH74.Uniqueness.Bender
  CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87

variable {A : Type} [Group A] [Finite A] {zb : A} {Sb Vb J : Subgroup A}

theorem AFrame.false_of_L216 (hfr : AFrame A zb Sb Vb)
    (hJ : IsComponent J) (h : LieModel (↥J ⧸ center ↥J) .PSL 2 2 4) : False := by
  have hst : StatedClassicalModel (↥J ⧸ center ↥J) .PSL 2 2 4 := by
    rcases h with ⟨-, h⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact h
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
  have hN : Nat.card (↥J ⧸ center ↥J) = 4080 := by
    have h1 := (CFSG.Timmesfeld.card_statedClassicalModel_two hst).1 rfl
    rw [h1]
    decide
  refine hfr.false_of_order hJ hN (by decide) ?_
  obtain ⟨hs, hns⟩ := Gen.quasisimple_quot hJ.1
  have hZ : center (↥J ⧸ center ↥J) = ⊥ := center_eq_bot_of_not_solvable hns
  obtain ⟨e⟩ := KGroups.equiv_psl2_of_lieModel_even (S := ↥J ⧸ center ↥J) (f := 4)
    (by norm_num) h
  have hB : BenderType (↥J ⧸ center ↥J) 4 1 1 := .linear 4 (by norm_num) e
  have hOut : Nat.card (OuterAutomorphisms.Outer (↥J ⧸ center ↥J)) = 4 := hB.outer_linear.2
  have hY : Nat.card (MulAut (↥J ⧸ center ↥J)) ≤ 4 * 4080 := by
    have := card_mulAut_le_of_outer (G := ↥J ⧸ center ↥J) hOut.le
    rwa [hN] at this
  exact not_dvd_card_mulAut hZ hN hY (fun m h1 h2 => by
    interval_cases m <;> decide)

theorem AFrame.false_of_Sz8 (hfr : AFrame A zb Sb Vb)
    (hJ : IsComponent J) (h : LieModel (↥J ⧸ center ↥J) .twistedB2 0 2 3) : False := by
  have hN : Nat.card (↥J ⧸ center ↥J) = 29120 := card_sz8 h
  refine hfr.false_of_order hJ hN (by decide) ?_
  obtain ⟨hs, hns⟩ := Gen.quasisimple_quot hJ.1
  have hZ : center (↥J ⧸ center ↥J) = ⊥ := center_eq_bot_of_not_solvable hns
  have hS : SuzukiModel (↥J ⧸ center ↥J) 2 3 := by
    rcases h with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, hS⟩
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact hS
  obtain ⟨e⟩ := CFSG.GH74.GLS.IVK.Proofs2.ivk93m12_szModel_equiv hS
  have hB : BenderType (↥J ⧸ center ↥J) (2 * 1 + 1) 2 1 := .suzuki 1 le_rfl e
  have hOut : Nat.card (OuterAutomorphisms.Outer (↥J ⧸ center ↥J)) ≤ 3 :=
    Nat.le_of_dvd (by norm_num) hB.outer_suzuki.2.1
  have hY : Nat.card (MulAut (↥J ⧸ center ↥J)) ≤ 3 * 29120 := by
    have := card_mulAut_le_of_outer (G := ↥J ⧸ center ↥J) hOut
    rwa [hN] at this
  exact not_dvd_card_mulAut hZ hN hY (fun m h1 h2 => by
    interval_cases m <;> decide)

theorem AFrame.false_of_U34 (hfr : AFrame A zb Sb Vb)
    (hJ : IsComponent J) (h : LieModel (↥J ⧸ center ↥J) .PSU 3 2 2) : False := by
  have hst : StatedClassicalModel (↥J ⧸ center ↥J) .PSU 3 2 2 := by
    rcases h with ⟨-, h⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact h
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
  have hN : Nat.card (↥J ⧸ center ↥J) = 62400 := by
    have h1 := (CFSG.Timmesfeld.card_statedClassicalModel_two hst).2.1 rfl
    rw [h1]
    decide
  have hY : ¬ KindFactorAll Kind.ly (↥J ⧸ center ↥J) := fun hK =>
    (by decide : ¬ 62400 ∣ Nat.factorial 11) (hN ▸ hK.card_dvd (Or.inr rfl))
  obtain ⟨hZ, hu, -⟩ := hfr.reduce hJ hY
  obtain ⟨φ, hinj, -⟩ := hfr.embed_aut hJ hZ hu
  obtain ⟨e⟩ := (CFSG.RankTwoShapes.statedClassicalModel_PSU_three_two_iff (↥J ⧸ center ↥J) 2
    le_rfl).1 hst
  have hmodel : CFSG.Theory.Comparator.PSU3Model 2 = CFSG.Open.PSU3 2 2 := by
    simp only [CFSG.Theory.Comparator.PSU3Model, CFSG.Open.PSU3]
  have hB := BenderType.unitary 2 le_rfl (e.trans (MulEquiv.subgroupCongr hmodel))
  have hrank : 4 ≤ CFSG.pRank 2 ↥Sb := hfr.rank_lo
  obtain ⟨E, hE, hEcard⟩ := exists_isElementaryAbelian_of_le_pRank hrank
  let e0 : (↥J ⧸ center ↥J) ≃* ↥J :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  let ψ : ↥Sb →* MulAut (↥J ⧸ center ↥J) := (MulAut.congr e0).symm.toMonoidHom.comp φ
  have hψ : Function.Injective ψ := (MulAut.congr e0).symm.injective.comp hinj
  have hsq : ∀ x ∈ E.map ψ, x * x = 1 := by
    rintro _ ⟨s, hs, rfl⟩
    have h2 : s ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian s hs
    rw [← map_mul, ← pow_two, h2, map_one]
  have hle := (hB.card_le_of_sq_eq_one_aut (E.map ψ) hsq).1
  rw [Subgroup.card_map_of_injective hψ] at hle
  have : (2 : ℕ) ^ 4 ≤ 2 ^ (2 + 1) := le_trans (by simpa using hEcard) hle
  norm_num at this

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
