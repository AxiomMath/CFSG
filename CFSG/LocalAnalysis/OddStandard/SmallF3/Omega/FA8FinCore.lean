module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FA8FinHeis
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGAutCentBK
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Om6ParG

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private theorem fa8fin_h_apply_comm {s g : OGroup Q} (hg : g * s = s * g) (v : V) :
    (g : V ≃ₗ[ZMod 3] V) ((s : V ≃ₗ[ZMod 3] V) v) =
      (s : V ≃ₗ[ZMod 3] V) ((g : V ≃ₗ[ZMod 3] V) v) := by
  have h := congrArg (fun e : OGroup Q => (e : V ≃ₗ[ZMod 3] V) v) hg
  simpa only [Subgroup.coe_mul, LinearEquiv.mul_apply] using h

private theorem fa8fin_h_pres {s : OGroup Q} (hs : s * s = 1) {g : OGroup Q}
    (hg : g * s = s * g) : ∀ w ∈ commSp s, (g : V ≃ₗ[ZMod 3] V) w ∈ commSp s := by
  intro w hw
  rw [mem_commSp_iff hs] at hw ⊢
  rw [← fa8fin_h_apply_comm hg, hw, map_neg]

private theorem fa8fin_h_preserve_W {s : OGroup Q} (hs : s * s = 1) {x : simGroup Q}
    (hx : simAct Q x s = s) : ∀ w ∈ commSp s, (x : V ≃ₗ[ZMod 3] V) w ∈ commSp s := by
  intro w hw
  have h := om6par_comm_t hx w
  rw [mem_commSp_iff hs] at hw ⊢
  rw [← h, hw, map_neg]

private noncomputable def fa8fin_h_rhoW {s : OGroup Q} (hs : s * s = 1) (R : Subgroup (OGroup Q))
    (hcent : ∀ g ∈ R, g * s = s * g) : ↥R →* Module.End (ZMod 3) (commSp s) where
  toFun g := ((g : OGroup Q) : V ≃ₗ[ZMod 3] V).toLinearMap.restrict
    (fa8fin_h_pres hs (hcent g g.2))
  map_one' := by
    ext w
    simp [LinearMap.restrict_apply]
  map_mul' g g' := by
    ext w
    simp [LinearMap.restrict_apply]

theorem fa8fin_core (hQ : Q.Nondegenerate) {s : OGroup Q} (hs : s * s = 1)
    (hW : Module.finrank (ZMod 3) (commSp s) = 4) (R : Subgroup (OGroup Q)) (hsR : s ∈ R)
    (hcard : Nat.card R = 32) (hcent : ∀ g ∈ R, g * s = s * g)
    (hpartner : ∀ g ∈ R, g ≠ 1 → g ≠ s → ∃ h ∈ R, h * g * h⁻¹ = s * g)
    {x : simGroup Q} (hx : ∀ g ∈ R, simAct Q x g = g) :
    ∃ b : OGroup (Q.restrict (FGSplit.comm hQ hs).P),
      (QuotientGroup.mk x : ProjSim Q) = fgIotaP (FGSplit.comm hQ hs) b := by
  have hxs : simAct Q x s = s := hx s hsR
  haveI : Finite ↥R := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  let ρ := fa8fin_h_rhoW hs R hcent
  let s' : ↥R := ⟨s, hsR⟩
  have hs'2 : s' * s' = 1 := Subtype.ext hs
  have hs'1 : s' ≠ 1 := by
    intro h
    have h1 : s = 1 := congrArg Subtype.val h
    have h2 : invDim s = 0 := (invDim_eq_zero_iff hs).mpr h1
    have h3 : invDim s = 4 := hW
    omega
  have hρs : ρ s' = -1 := by
    ext w
    show (s : V ≃ₗ[ZMod 3] V) (w : V) = -(w : V)
    exact (mem_commSp_iff hs).mp w.2
  have hpartner' : ∀ g : ↥R, g ≠ 1 → g ≠ s' → ∃ h : ↥R, h * g * h⁻¹ = s' * g := by
    intro g hg1 hgs
    obtain ⟨h, hh, hhg⟩ := hpartner g g.2 (fun h => hg1 (Subtype.ext h))
      (fun h => hgs (Subtype.ext h))
    exact ⟨⟨h, hh⟩, Subtype.ext hhg⟩
  let f : Module.End (ZMod 3) (commSp s) :=
    ((x : V ≃ₗ[ZMod 3] V) : V →ₗ[ZMod 3] V).restrict (fa8fin_h_preserve_W hs hxs)
  have hf : ∀ g : ↥R, f * ρ g = ρ g * f := by
    intro g
    ext w
    show (x : V ≃ₗ[ZMod 3] V) (((g : OGroup Q) : V ≃ₗ[ZMod 3] V) (w : V)) =
      ((g : OGroup Q) : V ≃ₗ[ZMod 3] V) ((x : V ≃ₗ[ZMod 3] V) (w : V))
    rw [om6par_simAct_apply x (g : OGroup Q) (w : V), hx g g.2]
  obtain ⟨c, hc⟩ := fa8fin_commutant_scalar hW hcard ρ s' hs'2 hs'1 hρs hpartner' f hf
  have hcw : ∀ w ∈ commSp s, (x : V ≃ₗ[ZMod 3] V) w = c • w := by
    intro w hw
    have := congrArg (fun F : Module.End (ZMod 3) (commSp s) => ((F ⟨w, hw⟩ : commSp s) : V)) hc
    simpa [f] using this
  have hc0 : c ≠ 0 := by
    rintro rfl
    have hpos : 0 < Module.finrank (ZMod 3) (commSp s) := by rw [hW]; norm_num
    haveI : Nontrivial (commSp s) := Module.finrank_pos_iff.mp hpos
    obtain ⟨w, hw0⟩ := exists_ne (0 : commSp s)
    apply hw0
    apply Subtype.ext
    apply (x : V ≃ₗ[ZMod 3] V).injective
    simp [hcw w w.2]
  have hc1 : c = 1 ∨ c = -1 := by
    revert hc0
    generalize c = c'
    revert c'
    decide
  have hP : ∀ p ∈ (FGSplit.comm hQ hs).P, (x : V ≃ₗ[ZMod 3] V) p ∈ (FGSplit.comm hQ hs).P :=
    om6par_preserve_P hxs
  have h3 : 3 ≤ Module.finrank (ZMod 3) (FGSplit.comm hQ hs).W := by
    show 3 ≤ Module.finrank (ZMod 3) (commSp s)
    rw [hW]
    norm_num
  have hO := fg_bk_orthogonal (FGSplit.comm hQ hs) h3 x hc1 hcw
  let g₀ : OGroup Q := ⟨(x : V ≃ₗ[ZMod 3] V), hO⟩
  have hg₀ : (QuotientGroup.mk x : ProjSim Q) = projOrthToProjSim Q (toProj Q g₀) := rfl
  rcases hc1 with rfl | rfl
  · obtain ⟨b, hb⟩ := (FGSplit.comm hQ hs).ext_surj g₀
      (fun w => by simpa using hcw w w.2) (fun p => hP p p.2)
    refine ⟨b, ?_⟩
    rw [hg₀, fgIotaP, MonoidHom.comp_apply, MonoidHom.comp_apply, hb]
  · let g₁ : OGroup Q := piOrth Q * g₀
    obtain ⟨b, hb⟩ := (FGSplit.comm hQ hs).ext_surj g₁
      (fun w => by
        change (piOrth Q : V ≃ₗ[ZMod 3] V) ((x : V ≃ₗ[ZMod 3] V) (w : V)) = (w : V)
        rw [coe_piOrth_apply, hcw w w.2]
        simp)
      (fun p => by
        change (piOrth Q : V ≃ₗ[ZMod 3] V) ((x : V ≃ₗ[ZMod 3] V) (p : V)) ∈
          (FGSplit.comm hQ hs).P
        rw [coe_piOrth_apply]
        exact (FGSplit.comm hQ hs).P.neg_mem (hP p p.2))
    refine ⟨b, ?_⟩
    rw [hg₀, fgIotaP, MonoidHom.comp_apply, MonoidHom.comp_apply, hb]
    congr 1
    rw [show g₁ = piOrth Q * g₀ from rfl, map_mul, toProj_piOrth, one_mul]

end CFSG.OddStandard.SmallF3.Omega
