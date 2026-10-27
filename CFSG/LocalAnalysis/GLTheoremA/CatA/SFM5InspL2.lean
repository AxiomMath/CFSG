module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.SFM5Lemmas
public import CFSG.HardMathSupport.Solomon.Coordinator.L2FldHolds

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1431c

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.GLTheoremA.SFM5
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

theorem sfm5_fixSub_congr {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y') (α : MulAut Y) :
    CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns.fixSub (MulAut.congr e α) =
      (fixSubgroup α).map e.toMonoidHom := by
  ext y'
  rw [Subgroup.mem_map]
  constructor
  · intro h
    have h' : e (α (e.symm y')) = y' := h
    refine ⟨e.symm y', ?_, by simp⟩
    show α (e.symm y') = e.symm y'
    apply e.injective
    rw [h']
    simp
  · rintro ⟨y, hy, rfl⟩
    have hy' : α y = y := hy
    show e (α (e.symm (e y))) = e y
    rw [MulEquiv.symm_apply_apply, hy']

theorem sfm5_fixSub_one {W : Type} [Group W] :
    CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns.fixSub (1 : MulAut W) = ⊤ := by
  ext w
  simp [CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns.mem_fixSub]

theorem I1431InspL2_of_L2CentreThree
    (h0 : CFSG.HardMathSupport.Solomon.Coordinator.L2CentreThree) : I1431InspL2 := by
  intro Y _ _ hQ hO hcat τ hτ A hA hTC
  obtain ⟨F, hFf, hFfin, hF, ⟨e⟩⟩ := catalogIs_three18 hcat
  have hZ : Subgroup.center Y = ⊥ := by
    by_contra hne
    have h9 := h0 Y hQ (isPGroup_center_of_glaPPrimeCore_eq_bot hO) hne F ⟨e⟩
    rw [hF] at h9
    norm_num at h9
  let eY : Y ≃* StatedProj (StatedSL 2 F) :=
    QuotientGroup.quotientBot.symm.trans ((QuotientGroup.quotientMulEquivOfEq hZ).symm.trans e)
  let β : MulAut (StatedProj (StatedSL 2 F)) := MulAut.congr eY τ
  have hβ3 : β ^ 3 = 1 := by
    show MulAut.congr eY τ ^ 3 = 1
    rw [← map_pow, hτ, map_one]
  have hfix : CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns.fixSub β =
      (fixSubgroup τ).map eY.toMonoidHom := sfm5_fixSub_congr eY τ
  let ψ : ↥(fixSubgroup τ) ≃*
      ↥(CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns.fixSub β) :=
    (Subgroup.equivMapOfInjective (fixSubgroup τ) eY.toMonoidHom eY.injective).trans
      (MulEquiv.subgroupCongr hfix.symm)
  by_cases hβ1 : β = 1
  ·
    have hfix1 : CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns.fixSub β = ⊤ := by
      rw [hβ1]
      exact sfm5_fixSub_one
    let eX : ↥(fixSubgroup τ) ≃* StatedProj (StatedSL 2 F) :=
      ψ.trans ((MulEquiv.subgroupCongr hfix1).trans Subgroup.topEquiv)
    exact not_comp_A6_of_simple (k := 18) (by norm_num) hF eX hA hTC.1
  · rcases CFSG.HardMathSupport.Solomon.Coordinator.l2Aut3Classification_holds F β hβ3 with
      hβ1' | hsolv | ⟨σ, φ, γ, hφ, hβγ⟩
    · exact absurd hβ1' hβ1
    ·
      haveI := hsolv
      have hXs : Group.IsSolvable ↥(fixSubgroup τ) :=
        Group.isSolvable_of_surjective (f := ψ.symm.toMonoidHom) ψ.symm.surjective
      exact not_comp_of_solvable hXs hA
    ·
      obtain ⟨F₀, hF₀f, hF₀fin, hF₀card, ⟨ψ₀⟩⟩ :=
        CFSG.HardMathSupport.Solomon.Coordinator.l2FieldFixed_holds F β hβ3 hβ1 σ φ γ hφ hβγ
      have hk : Nat.card F₀ = 3 ^ 6 := by
        have h1 : Nat.card F₀ ^ 3 = (3 ^ 6) ^ 3 := by
          rw [← hF₀card, hF]
          norm_num
        exact Nat.pow_left_injective (by norm_num) h1
      exact not_comp_A6_of_simple (k := 6) (by norm_num) hk (ψ.trans ψ₀) hA hTC.1

section

theorem I1431InspL2_holds : I1431InspL2 :=
  I1431InspL2_of_L2CentreThree CFSG.HardMathSupport.Solomon.Coordinator.l2CentreThree_holds

end

end CFSG.LocalAnalysis.GLTheoremA.H1431c

end
