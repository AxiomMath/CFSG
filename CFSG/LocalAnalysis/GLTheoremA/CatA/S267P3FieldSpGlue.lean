module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267P3FieldSp
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267P3Iso
import CFSG.LieType.Steinberg.CentralExt.PSpMultiplier
import CFSG.LieType.SeitzGeneration.OuterSpData
import CFSG.RankThree.PartTwo.KFacts.AutPSp4Odd
import CFSG.GroupTheory.WeirSylow.CrossRankForms
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.P3

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

section Symplectic

variable {K : Type} [Field K] [Finite K]

theorem exists_modelB_projectiveSp (hK2 : ringChar K ≠ 2)
    (hfield : ∀ σ : K ≃+* K, orderOf σ = 3 → ModelB (StatedProj (StatedSp 2 K)) (fieldAut 2 K σ))
    (β : MulAut (StatedProj (StatedSp 2 K))) (hβ3 : β ^ 3 = 1)
    (hβ : β ∉
      (MulAut.conj : StatedProj (StatedSp 2 K) →* MulAut (StatedProj (StatedSp 2 K))).range) :
    ∃ (g : StatedProj (StatedSp 2 K)) (ψ : MulAut (StatedProj (StatedSp 2 K))),
      β = MulAut.conj g * ψ ∧ ModelB (StatedProj (StatedSp 2 K)) ψ := by
  have hD : β ∉ (conjAut 2 K).range := by
    rintro ⟨A, rfl⟩
    apply hβ
    have h2 : conjAut 2 K A ^ 2 ∈
        (MulAut.conj : StatedProj (StatedSp 2 K) →* MulAut (StatedProj (StatedSp 2 K))).range := by
      rw [← map_pow]
      exact conjAut_mem_inner_of_isSquare ⟨(multiplier 2 K A : K), by
        rw [map_pow, Units.val_pow_eq_pow_val, sq]⟩
    rw [show conjAut 2 K A = (conjAut 2 K A ^ 2)⁻¹ by
      rw [eq_inv_iff_mul_eq_one, sq, ← pow_three, hβ3]]
    exact inv_mem h2
  obtain ⟨A, σ, rfl⟩ := CFSG.RankThree.PartTwo.KFacts.psp4_odd_automorphism_normal_form hK2 β
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    exact hD ⟨A, by rw [map_one, mul_one]⟩
  obtain ⟨hσ, H, hH⟩ := CFSG.RankThree.PartTwo.KFacts.conjAut_mul_fieldAut_of_pow_three_eq_one
    (by norm_num) A σ hσ1 hβ3
  rw [hH]
  refine ⟨1, MulAut.congr (conjAut 2 K H) (fieldAut 2 K σ), ?_,
    ModelB.congr (conjAut 2 K H) (hfield σ hσ)⟩
  rw [map_one, one_mul]
  exact MulEquiv.ext fun _ => rfl

theorem card_le_nine_projectiveSp (hK3 : ¬ 3 ∣ Nat.card K)
    (F : Subgroup (StatedProj (StatedSp 2 K))) (hF : IsElemAbelian 3 F) : Nat.card F ≤ 3 ^ 2 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : 3 ∣ Nat.card K ^ 2 - 1 := by
    rw [show Nat.card K ^ 2 - 1 = (Nat.card K + 1) * (Nat.card K - 1) by
      rw [← Nat.sq_sub_sq, one_pow]]
    rcases (by omega : 3 ∣ Nat.card K + 1 ∨ 3 ∣ Nat.card K - 1) with h | h
    · exact h.mul_right _
    · exact h.mul_left _
  have hr := CFSG.GroupTheory.WeirSylow.pRank_top_statedProj_statedSp_eq_of_dvd (p := 3) ⟨1, rfl⟩
    h3 (n := 2) (by norm_num)
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.1 hF.isPGroup
  rw [hj]
  exact Nat.pow_le_pow_right (by norm_num)
    ((CFSG.SectionRank.le_pRank (by norm_num) le_top hF hj).trans hr.le)

end Symplectic

theorem p3At_B_two_of_field
    (hfield : ∀ (K : Type) [Field K] [Finite K], ringChar K ≠ 2 → ringChar K ≠ 3 →
      ∀ σ : K ≃+* K, orderOf σ = 3 →
        ModelB (StatedProj (StatedSp 2 K))
          (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldAut 2 K σ))
    {Q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.B 2 Q).Valid) : P3At ⟨_, hv⟩ := by
  rintro q Ω _ _ S B H hchar ⟨e⟩
  have hQq : Q.p = q := by
    change (TauCeti.LieTypeIndex.B 2 Q).characteristic = q at hchar
    rwa [TauCeti.LieTypeIndex.characteristic_B] at hchar
  haveI := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField ⟨.B 2 Q, hv⟩
  set K := ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B 2 Q, hv⟩) with hKdef
  have hKcard : Nat.card K = Q.p ^ Q.exponent := by
    rw [hKdef, TauCeti.ValidLieTypeIndex.card_fixedField,
      TauCeti.ValidLieTypeIndex.fieldOrder_eq_characteristic_pow,
      show TauCeti.ValidLieTypeIndex.characteristic ⟨.B 2 Q, hv⟩ = Q.p from
        TauCeti.LieTypeIndex.characteristic_B 2 Q,
      show TauCeti.ValidLieTypeIndex.fieldExponent ⟨.B 2 Q, hv⟩ = Q.exponent from
        TauCeti.LieTypeIndex.fieldExponent_B 2 Q]
  haveI : CharP K Q.p := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Q.prime_p Q.exponent_pos hKcard
  have hchK : ringChar K = q := by rw [ringChar.eq K Q.p, hQq]
  have hK3 : ¬ 3 ∣ Nat.card K := by
    rw [hKcard]
    intro h
    exact H.three (hQq ▸ ((Nat.prime_dvd_prime_iff_eq Nat.prime_three Q.prime_p).1
      (Nat.prime_three.dvd_of_dvd_pow h)).symm)
  set e₁ : PSimple 3 S ≃* StatedProj (StatedSp 2 K) :=
    e.trans (CFSG.QuasithinUnique.SQTK.typeB2GroupEquivStatedProj Q hv)
  have hZ : Subgroup.center ↥S = ⊥ := by
    refine H.center_eq_bot_of_multiplier e₁ ?_
    have hK5 : 5 ≤ Nat.card K := by
      rw [hKcard]
      exact (Q.prime_p.five_le_of_ne_two_of_ne_three (hQq ▸ H.two) (hQq ▸ H.three)).trans
        (Nat.le_self_pow Q.exponent_pos.ne' _)
    obtain ⟨-, ⟨eM⟩⟩ :=
      CFSG.LieType.Steinberg.CentralExt.SpClosed.psp_hopfMultiplier (K := K) (n := 2) le_rfl hK5
    rw [Nat.card_congr eM.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    intro hd
    have := Nat.le_of_dvd (by norm_num) (hd.trans (Nat.gcd_dvd_left _ _))
    omega
  obtain ⟨φ, hφ, hφS⟩ := exists_embedding_of_mulEquiv H hZ e₁.symm
  exact Or.inl (concA_of_outer H hZ φ hφ hφS
    (CFSG.LieType.SeitzGeneration.center_statedProj_statedSp_eq_bot le_rfl)
    (card_le_nine_projectiveSp hK3)
    (exists_modelB_projectiveSp (by rw [hchK]; exact H.two)
      (hfield K (by rw [hchK]; exact H.two) (by rw [hchK]; exact H.three))))

theorem p3At_B_two {Q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.B 2 Q).Valid) :
    P3At ⟨_, hv⟩ :=
  p3At_B_two_of_field (fun K _ _ hK2 hK3 σ hσ => Field.modelB_psp4 hK2 hK3 hσ) hv

end CFSG.LocalAnalysis.GLTheoremA.S267.P3

end
