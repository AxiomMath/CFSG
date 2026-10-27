module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I106TFacts
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSp48Aut
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSp48Frob
import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.OddCentre
import CFSG.RankThree.PartTwo.KFacts.AutPSpOrderThree
import CFSG.Foundations.SteinbergCADefinitionNodes

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S8.L84

open CFSG.Open CFSG.Quasithin CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.AGLEmbedding.KFactProofs.Sp48
open CFSG.RankThree.PartTwo.KFacts CFSG.Yardstones.Md0ec50421ce4

private theorem exists_lie_index_of_isSp48 {i : TauCeti.CFSGIndex} (h : isSp48 i) :
    ∃ (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower),
      i = .lie d ∧ d.1 = .B 2 q ∧ q.card = 8 := by
  rcases i with p | n | d | s
  · simp [isSp48, onLie] at h
  · simp [isSp48, onLie] at h
  · obtain ⟨x, hx⟩ := d
    rcases x with a | a | ⟨rank, q⟩ | a | a | a | a | a | a | a | a | a | a | a | a | a | a
    all_goals simp [isSp48, onLie] at h
    by_cases hrank : rank = 2
    · subst hrank
      simp only [isSp48, onLie] at h
      exact ⟨⟨.B 2 q, hx⟩, q, rfl, rfl,
        by simpa [TauCeti.PrimePower.card_def] using h⟩
    · simp [isSp48, onLie, hrank] at h
  · simp [isSp48, onLie] at h

private theorem isElemAbelian_spE : IsElemAbelian 3 spE := by
  refine ⟨IsMulCommutative.of_comm ?_, fun x hx => ((mem_spE_iff_cube x).1 hx).2⟩
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  exact Subtype.ext (comm_spT0 a (spE_le_spT0 ha) b (spE_le_spT0 hb))

private theorem fixed_fieldSp_on_spE {σ : GF8 ≃+* GF8}
    (hσ : σ = frobE ∨ σ = frobE ^ 2) : ∀ x ∈ spE, fieldSp 2 GF8 σ x = x := by
  intro x hx
  have hxT : x ∈ spT0 := spE_le_spT0 hx
  have hfx : fr x = x := (fr_eq_self_iff_mem_spE hxT).2 hx
  rcases hσ with h | h
  · rw [h]
    exact hfx
  · rw [h, map_pow]
    change (fr ^ 2) x = x
    rw [pow_two, MulAut.mul_apply, hfx, hfx]

theorem i106TSp48Fact_holds : I106TSp48Fact := by
  intro i H _ _ hisSp hq hZ3 hquot α hα3 hαnot
  obtain ⟨d, q, rfl, hdq, hq8⟩ := exists_lie_index_of_isSp48 hisSp
  have h8 : q.p ^ q.exponent = 2 ^ 3 := by
    rw [← TauCeti.PrimePower.card_def, hq8]
    norm_num
  have hq2 : q.p = 2 := by
    have h1 : q.p ∣ q.p ^ q.exponent := dvd_pow_self q.p q.exponent_pos.ne'
    rw [h8] at h1
    exact (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1
      (q.prime_p.dvd_of_dvd_pow h1)
  have hq3 : q.exponent = 3 := by
    rw [hq2] at h8
    exact Nat.pow_right_injective (le_refl 2) h8
  have hd : CFSG.AGLEmbedding.IsSpFourEightIndex d := ⟨q, hq2, hq3, hdq⟩
  obtain ⟨e⟩ := hquot
  obtain ⟨⟨e8⟩, -⟩ := CFSG.AGLEmbedding.KFactProofs.Sp48.exists_equiv_sp8 hd e
  have hK : CFSG.IsQuasisimple H :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff H).2.2.1.mpr hq
  have hodd : Odd (Nat.card (Subgroup.center H)) := by
    have hP : IsPGroup 3 (Subgroup.center H) := by
      rw [isPGroup_iff_pow_pow_eq_one]
      intro z
      obtain ⟨n, hn⟩ := hZ3 (z : H) z.2
      exact ⟨n, Subtype.ext (by simpa using hn)⟩
    obtain ⟨n, hn⟩ := hP.exists_card_eq
    rw [hn]
    exact Odd.pow (n := n) (show Odd 3 by decide)
  have hcenter : Subgroup.center H = ⊥ := by
    refine CFSG.SectionRank.QTK.Insp443.center_eq_bot_of_psp4 hK hodd (F := GF8) ?_
      (e8.trans piP)
    rw [card_gf8]
    norm_num
  let ψ : H ≃* Sp8 := QuotientGroup.quotientBot.symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hcenter.symm).trans e8)
  let αs : MulAut Sp8 := MulAut.congr ψ α
  have hα3' : α ^ 3 = 1 := by
    ext x
    simp only [pow_three, MulAut.mul_apply, MulAut.one_apply]
    exact hα3 x
  have hαs3 : αs ^ 3 = 1 := by
    change (MulAut.congr ψ α) ^ 3 = 1
    rw [← map_pow, hα3', map_one]
  have hαnot' : ¬ IsInnerAut α := by
    rintro ⟨h, hh⟩
    exact hαnot ⟨h, fun x => by rw [← hh]; rfl⟩
  have hαsnot : ¬ IsInnerAut αs := by
    change ¬ IsInnerAut (MulAut.congr ψ α)
    exact fun h => hαnot' ((isInnerAut_congr ψ α).mp h)
  have hαs_apply (y : H) : αs (ψ y) = ψ (α y) := by
    change MulAut.congr ψ α (ψ y) = ψ (α y)
    simp [MulAut.congr, MulEquiv.symm_apply_apply]
  let ρ : MulAut Sp8 ≃* MulAut (StatedProj (StatedSp 2 GF8)) := MulAut.congr piP
  let β : MulAut (StatedProj (StatedSp 2 GF8)) := ρ αs
  have hβ3 : β ^ 3 = 1 := by
    rw [show β = MulAut.congr piP αs from rfl]
    rw [← map_pow, hαs3, map_one]
  have hβnot : ¬ IsInnerAut β := by
    rw [show β = MulAut.congr piP αs from rfl, isInnerAut_congr]
    exact hαsnot
  have hβrange : β ∉ (conjAut 2 GF8).range := by
    rintro ⟨A, hA⟩
    apply hβnot
    rw [← hA]
    exact conjAut_mem_inner_of_charTwo A
  obtain ⟨σ, hσord, A, hβeq⟩ :=
    sp4_even_order_three_field_descent (F := GF8) β hβ3 hβrange
  have hσ : σ = frobE ∨ σ = frobE ^ 2 := by
    rcases ringAut_gf8 σ with h | h | h
    · rw [h, orderOf_one] at hσord
      omega
    · exact Or.inl h
    · exact Or.inr h
  let c : MulAut Sp8 := ρ.symm (conjAut 2 GF8 A)
  have hfield : ρ.symm (fieldAut 2 GF8 σ) = fieldSp 2 GF8 σ := by
    change (MulAut.congr piP).symm (fieldAut 2 GF8 σ) = fieldSp 2 GF8 σ
    rw [← congr_piP_fieldSp σ, MulEquiv.symm_apply_apply]
  have hαseq : αs = c * fieldSp 2 GF8 σ * c⁻¹ := by
    have h := congrArg ρ.symm hβeq
    have hβsymm : ρ.symm β = αs := MulEquiv.symm_apply_apply ρ αs
    rw [hβsymm, map_mul, map_mul, map_inv, hfield] at h
    simpa [c] using h
  have hfixE : ∀ x ∈ spE, fieldSp 2 GF8 σ x = x := fixed_fieldSp_on_spE hσ
  let Esp : Subgroup Sp8 := spE.map c.toMonoidHom
  have hαs_fix : ∀ x ∈ Esp, αs x = x := by
    rintro _ ⟨s, hs, rfl⟩
    calc
      αs (c s) = (c * fieldSp 2 GF8 σ * c⁻¹) (c s) := by rw [hαseq]
      _ = c (fieldSp 2 GF8 σ (c⁻¹ (c s))) := by simp [MulAut.mul_apply]
      _ = c (fieldSp 2 GF8 σ s) := by simp
      _ = c s := by rw [hfixE s hs]
  let E : Subgroup H := Esp.map ψ.symm.toMonoidHom
  refine ⟨E, ?_, ?_, ?_, ?_⟩
  · exact (isElemAbelian_spE.map c.toMonoidHom).map ψ.symm.toMonoidHom
  · rw [show E = Esp.map ψ.symm.toMonoidHom from rfl,
      Subgroup.card_map_of_injective ψ.symm.injective]
    rw [show Esp = spE.map c.toMonoidHom from rfl,
      Subgroup.card_map_of_injective c.injective, card_spE]
    norm_num
  · rintro _ ⟨x, hx, rfl⟩
    apply ψ.injective
    calc
      ψ (α (ψ.symm x)) = αs x := by
        simpa using (hαs_apply (ψ.symm x)).symm
      _ = x := hαs_fix x hx
      _ = ψ (ψ.symm x) := by simp
  · simp [hcenter]

end CFSG.LocalAnalysis.GLTheoremA.S8.L84
