module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2017ClsOut
import CFSG.GroupTheory.CenterlessInnerCentralizer
import CFSG.LocalAnalysis.GLTheoremA.CatB.I269R3
import CFSG.LocalAnalysis.GLTheoremA.CatB.I269R4

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2017Cls

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)


set_option linter.unusedSectionVars false

private theorem card_alt_eight_d4 : Nat.card (alternatingGroup (Fin 8)) = 20160 := by
  have h := two_mul_nat_card_alternatingGroup (α := Fin 8)
  rw [Nat.card_perm, Nat.card_fin] at h
  have h8 : (8 : ℕ).factorial = 40320 := by decide
  omega

private theorem center_eq_bot_d4two {T : Type} [Group T] [IsSimpleGroup T]
    (hnc : ∃ a b : T, a * b ≠ b * a) : Subgroup.center T = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center T) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnc
    apply hab
    have ha : a ∈ Subgroup.center T := by
      rw [h]
      trivial
    exact (Subgroup.mem_center_iff.1 ha b).symm

section Certs


theorem d4TwoNoA8_holds : D4TwoNoA8 := by
  intro d hd
  obtain ⟨d₁, hv⟩ := d
  have hd₁ : d₁ = TauCeti.LieTypeIndex.D 4 gfTwoPP := hd
  subst hd₁
  intro _ _ β hβ3 hβ1 hA8
  classical
  have hcat : catalogIs (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.D 4 gfTwoPP, hv⟩).Group
      CFSG.LocalAnalysis.GLTheoremA.S9.isD4two := by
    refine ⟨.lie ⟨TauCeti.LieTypeIndex.D 4 gfTwoPP, hv⟩, ?_, ⟨MulEquiv.refl _⟩⟩
    show gfTwoPP.card = 2
    rw [TauCeti.PrimePower.card_def]
    rfl
  obtain ⟨eS⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.bridge_d4two hcat
  let e1 : (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.D 4 gfTwoPP, hv⟩).Group ≃*
      StatedProj (StatedOmega (StatedQuadPlus 4 (ZMod 2))) :=
    eS.trans (CFSG.LocalAnalysis.GLTheoremA.CatB.statedProjZMod2Equiv
      (StatedOmega (StatedQuadPlus 4 (ZMod 2)))).symm
  let eO : StatedProj (StatedOmega (StatedQuadPlus 4 (ZMod 2))) ≃*
      CFSG.LocalAnalysis.GLTheoremA.I269R.OG :=
    CFSG.HardMathSupport.Curtis.Coordinator.projEquivElementary (ZMod 2) (by simp) (n := 4)
      (by norm_num)
  obtain ⟨eA⟩ :=
    CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.nonempty_statedProj_equiv_adjointGroup (ZMod 2)
  have h7 := CFSG.LocalAnalysis.GLTheoremA.I269R.noThreeSeven_orth.of_mulEquiv (e1.trans eO)
  have h5 := CFSG.LocalAnalysis.GLTheoremA.I269R.outerNoFive_adjoint.of_mulEquiv (e1.trans eA)
  obtain ⟨J, hJ, hJc, ⟨eJ⟩⟩ := hA8
  have hJcard : 20160 ∣ Nat.card J := by
    have h1 : Nat.card (↥J ⧸ Subgroup.center ↥J) = 20160 := by
      rw [Nat.card_congr eJ.toEquiv]
      exact card_alt_eight_d4
    have h2 := Subgroup.card_quotient_dvd_card (Subgroup.center ↥J)
    rwa [h1] at h2
  have hZ := center_eq_bot_d4two
    (CFSG.LocalAnalysis.GLTheoremA.exists_mul_ne_mul_of_glaPComponent Nat.prime_three hJ)
  by_cases hinn : ∃ t, MulAut.conj t = β
  ·
    obtain ⟨t, rfl⟩ := hinn
    have ht3 : t ^ 3 = 1 :=
      CFSG.mulAutConj_injective_of_center_eq_bot hZ (by rw [map_pow, hβ3, map_one])
    have ht1 : t ≠ 1 := by
      rintro rfl
      exact hβ1 (map_one _)
    haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 7 ((by norm_num : 7 ∣ 20160).trans hJcard)
    have hfix : MulAut.conj t (y : _) = y := hJc.1 y.2
    rw [MulAut.conj_apply] at hfix
    refine h7 t y ht3 ht1 (by rw [Subgroup.orderOf_coe, hy]) ?_
    calc t * y = t * y * t⁻¹ * t := by group
      _ = y * t := by rw [hfix]
  ·
    push Not at hinn
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 5 ((by norm_num : 5 ∣ 20160).trans hJcard)
    exact h5 β hβ3 hinn y (by rw [Subgroup.orderOf_coe, hy]) (hJc.1 y.2)

end Certs

end CFSG.LocalAnalysis.GLTheoremA.I2017Cls

end
