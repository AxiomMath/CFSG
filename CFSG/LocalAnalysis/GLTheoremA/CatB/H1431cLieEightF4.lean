module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieEightD4Tri
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieEightUni
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.F4InnerComp
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.ExcResOutF4
public import CFSG.HardMathSupport.Dickson.Bal207.OrthSU38Image
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.CompSLOB

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1431c

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (LieOrderBridge)
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)

local notation "fixSub" => CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup

section F4

set_option linter.unusedSectionVars false


theorem lieSEightNoAt_F4 (hLO : LieOrderBridge) :
    LieSEightNoAt fun d => ∃ q, d = .F4 q := by
  rintro Y _ _ hY - - ⟨d, hv⟩ ⟨q, rfl⟩ hc hf ⟨e⟩ α hα hα3 hα1 ⟨J, hJ, hT⟩
  have hq8 : q.card = 8 := hf
  have hp2 : q.p = 2 := (TauCeti.LieTypeIndex.characteristic_F4 q).symm.trans hc
  have hexp : q.exponent = 3 := by
    have h := q.card_def
    rw [hq8, hp2] at h
    exact Nat.pow_right_injective (le_refl 2) (h.symm.trans (by norm_num : 8 = 2 ^ 3))
  haveI : IsSimpleGroup (Y ⧸ Subgroup.center Y) := hY.2
  have hnab : ∃ a b : Y ⧸ Subgroup.center Y, a * b ≠ b * a :=
    CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian Y hY
  have hZ : Subgroup.center (Y ⧸ Subgroup.center Y) = ⊥ :=
    lieSEightD4_center_eq_bot inferInstance hnab
  have hqS : CFSG.Open.IsQuasisimple (Y ⧸ Subgroup.center Y) :=
    lieSEightD4_isQuasisimple inferInstance hnab
  let eS : (Y ⧸ Subgroup.center Y) ⧸ Subgroup.center (Y ⧸ Subgroup.center Y) ≃*
      (TauCeti.CFSGIndex.lie ⟨.F4 q, hv⟩).Group :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans e
  have hLieS : IsLieQuot (Y ⧸ Subgroup.center Y) IsF4EightIndex :=
    ⟨⟨.F4 q, hv⟩, ⟨hp2, hexp⟩, ⟨eS⟩⟩
  obtain ⟨-, ⟨θ⟩⟩ := F4InnerExAux.center_bot_and_equiv hqS hLieS
  have hF8 : Nat.card (GaloisField 2 3) = 2 ^ 3 := GaloisField.card 2 3 (by norm_num)
  have hαθ : MulAut.congr θ α ∈ innAutDerived (adjointGroup Tag.F4 (GaloisField 2 3)) :=
    (CFSG.ComponentClassification.OuterAutomorphisms.mem_innAutDerived_congr θ).2 hα
  obtain ⟨g, hg⟩ := CFSG.HardMathSupport.Dickson.Sec6.I1431.excres_innAutDerived_le_inner_F4
    Nat.prime_two (by norm_num) hF8 hαθ
  have hα' : α = MulAut.conj (θ.symm g) := by
    refine MulEquiv.ext fun y => ?_
    have h1 := congrArg (fun φ : MulAut (adjointGroup Tag.F4 (GaloisField 2 3)) => φ (θ y)) hg
    simp only [MulAut.conj_apply, MulAut.congr_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply] at h1
    apply θ.injective
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact h1.symm
  subst hα'
  set s : Y ⧸ Subgroup.center Y := θ.symm g with hs
  have hs3 : s ^ 3 = 1 := by
    apply CFSG.mulAutConj_injective_of_center_eq_bot hZ
    rw [map_pow, hα3, map_one]
  have hs1 : s ≠ 1 := fun h => hα1 (by rw [h, map_one])
  have hsT : IsSimpleGroup ↥(⊤ : Subgroup (Y ⧸ Subgroup.center Y)) :=
    (MulEquiv.isSimpleGroup_congr Subgroup.topEquiv).2 inferInstance
  have hnabT : ∃ a b : ↥(⊤ : Subgroup (Y ⧸ Subgroup.center Y)), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    exact ⟨Subgroup.topEquiv.symm a, Subgroup.topEquiv.symm b, fun h => hab (by
      have := congrArg (Subgroup.topEquiv (G := Y ⧸ Subgroup.center Y)) h
      simpa using this)⟩
  have hqT : CFSG.Open.IsQuasisimple ↥(⊤ : Subgroup (Y ⧸ Subgroup.center Y)) :=
    lieSEightD4_isQuasisimple hsT hnabT
  have hLieT : IsLieQuot ↥(⊤ : Subgroup (Y ⧸ Subgroup.center Y)) IsF4EightIndex := by
    obtain ⟨d', hd', ⟨e''⟩⟩ := hLieS
    exact ⟨d', hd', ⟨(QuotientGroup.congr _ _ Subgroup.topEquiv
      (Subgroup.map_center_eq _)).trans e''⟩⟩
  have hnc : s ∉ Subgroup.centralizer ((⊤ : Subgroup (Y ⧸ Subgroup.center Y)) : Set _) := by
    intro h
    apply hs1
    have hsc : s ∈ Subgroup.center (Y ⧸ Subgroup.center Y) := by
      rw [Subgroup.mem_center_iff]
      intro z
      exact Subgroup.mem_centralizer_iff.1 h z (Subgroup.mem_top z)
    rw [hZ] at hsc
    exact Subgroup.mem_bot.1 hsc
  have hcl := f4EightClass_holds (Y ⧸ Subgroup.center Y) ⊤ s
    ⟨le_rfl, CFSG.Open.IsSubnormal.refl _, hqT⟩ hLieT
    (Subgroup.mem_normalizer_iff.2 fun h => by simp) hs3 hnc ⟨s, Subgroup.mem_top s, by simp⟩
  have hJ' : GLAPComponent 3
      (⊤ ⊓ Subgroup.centralizer ({s} : Set (Y ⧸ Subgroup.center Y))) J := by
    rw [top_inf_eq, ← CFSG.HardMathSupport.Dickson.Bal207.OrthFix.fixSubgroup_conj_eq_centralizer]
    exact hJ
  obtain ⟨hJq, d', hd', ⟨eJ⟩⟩ := hcl.1 J hJ'
  have hc1 := hLO d' _ ⟨eJ⟩
  have hc2 := lieSEight_card_quot_center hLO hJ hJq hT
  rw [hc2] at hc1
  rcases hd' with ⟨q', hq', hd'e⟩ | ⟨q', hq', hd'e⟩
  · rw [hd'e] at hc1
    have hq'c : q'.card = 8 := by
      rw [TauCeti.PrimePower.card_def, hq'.1, hq'.2]
      norm_num
    change 1056706560 = orderBC 3 q'.card at hc1
    rw [hq'c] at hc1
    exact absurd hc1 (by decide +kernel)
  · rw [hd'e] at hc1
    have hq'c : q'.card = 2 ^ 3 := by rw [TauCeti.PrimePower.card_def, hq'.1, hq'.2]
    change 1056706560 = orderTwistedA 2 q'.card at hc1
    rw [hq'c] at hc1
    exact lieSEight_orderTwistedA_ne (r := 2) (g := 3) (by norm_num) (by norm_num) hc1.symm

end F4

end CFSG.LocalAnalysis.GLTheoremA.H1431c

end
