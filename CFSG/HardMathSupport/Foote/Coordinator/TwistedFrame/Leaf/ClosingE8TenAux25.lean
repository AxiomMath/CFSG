module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ClosingE8TenAux24
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ClosingE8TenAux21
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ClosingE8TenAux23

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.E8TenAux

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8
open scoped commutatorElement

set_option linter.unusedSectionVars false


section Case1

variable {K : Type} [Field K] [Finite K] (D : LangLevi TwClass.e8Ten.tag K TwClass.e8Ten.w)

theorem case1_main (hK : Nat.card K = 2) {H : Subgroup (ModGL Tag.E8 K)}
    (hHG : H ≤ adjointGroup Tag.E8 K)
    (hb : TwBasic (TwClass.e8Ten.X₁ D) (TwClass.e8Ten.X₂ D))
    (hXH : TwClass.e8Ten.X₁ D ⊔ TwClass.e8Ten.X₂ D ≤ H)
    {v : ModGL Tag.E8 K} (hvQ : v ∈ Qθ Tag.E8 K)
    (hvB : conjSub v (Heis.Uneg Tag.E8 K) ≤ H)
    (hvM : ∀ β, κF D v β ≠ 0 → β ∈ mRoots)
    (hY1 : ∃ β, κF D v β ≠ 0 ∧ (cls β = 2 ∨ cls β = 3)) :
    ∃ m ∈ H, m ∈ Qθ Tag.E8 K ∧
      heisCoord Tag.E8 K m ∉ VS (TwClass.e8Ten.X₁ D ⊔ TwClass.e8Ten.X₂ D) := by
  by_contra hno
  have hvR : ∀ r : ModGL Tag.E8 K, r ∈ Rθ (TwClass.e8Ten.X₁ D) → r * v = v * r := fun r hr =>
    v_comm_R D hvQ (fun β hβ => mRoots_not_Bset (hvM β hβ)) hr
  obtain ⟨Zp, hZpA, ζp, hζp, hΨp⟩ := exists_Zroot D hK pairData_P2
  obtain ⟨Zm, hZmA, ζm, hζm, hΨm⟩ := exists_Zroot D hK pairData_P4
  rw [zP2] at hΨp
  rw [zP4] at hΨm
  have hZp : ∃ Z ∈ Agp D, ∃ ζ : D.L, ζ ≠ 0 ∧ ΨE D Z = pinnedX Tag.E8 D.L vGp ζ :=
    ⟨Zp, hZpA, ζp, hζp, hΨp⟩
  have hZm : ∃ Z ∈ Agp D, ∃ ζ : D.L, ζ ≠ 0 ∧ ΨE D Z = pinnedX Tag.E8 D.L vGc ζ :=
    ⟨Zm, hZmA, ζm, hζm, hΨm⟩
  have h₁ : ∀ ν ∈ mRoots, ν + vGp ∈ rootFinset Tag.E8 → κF D v ν = 0 := fun ν hν hνp =>
    zstep D hK hHG hb hXH hvQ hvB hvR vGp_data.1 vGp_data.2 hZp hno hν
      ((mRoots_closed ν hν).1 hνp)
  have h₂ : ∀ ν ∈ mRoots, ν + vGc ∈ rootFinset Tag.E8 → κF D v ν = 0 := fun ν hν hνc =>
    zstep D hK hHG hb hXH hvQ hvB hvR vGc_data.1 vGc_data.2 hZm hno hν
      ((mRoots_closed ν hν).2 hνc)
  obtain ⟨ℓ, hℓX, c, d, z, hc, hd, hΨℓ⟩ := exists_T3 D hK
  have hℓL : ΨE D ℓ ∈ Lθ Tag.E8 D.L := by
    rw [hΨℓ]
    exact mul_mem (mul_mem (pinnedX_mem_Lθ_of_deg_zero (mem_rootFinset.1 vA6_data.1) vA6_data.2 c)
      (pinnedX_mem_Lθ_of_deg_zero (mem_rootFinset.1 vA7_data.1) vA7_data.2 d))
      (pinnedX_mem_Lθ_of_deg_zero (mem_rootFinset.1 vGc_data.1) vGc_data.2 z)
  have hT : ActsBy (ΨE D ℓ) (Tm c d z) := by
    rw [hΨℓ]
    have h := ((actsBy_pinnedX vA6_data.1 vA6_data.2 c).mul
      (actsBy_pinnedX vA7_data.1 vA7_data.2 d)).mul (actsBy_pinnedX vGc_data.1 vGc_data.2 z)
    rw [LinearMap.comp_assoc] at h
    exact h
  have hℓU : ∀ u : ModGL Tag.E8 K, u ∈ Heis.Uneg Tag.E8 K → ℓ * u = u * ℓ := by
    intro u hu
    obtain ⟨t, ht⟩ := ΨE_Uneg D hu
    apply ΨE_injective D
    rw [ΨE_mul, ΨE_mul, hΨℓ, ht]
    have hc3 : ∀ γ ∈ ([vA6, vA7, vGc] : List (Fin Tag.E8.rank → ℤ)) , ∀ s : D.L,
        pinnedX Tag.E8 D.L γ s * pinnedX Tag.E8 D.L (-highRoot Tag.E8) t =
          pinnedX Tag.E8 D.L (-highRoot Tag.E8) t * pinnedX Tag.E8 D.L γ s := by
      intro γ hγ s
      have hdata := uneg_comm γ hγ
      have hγr : γ ∈ rootFinset Tag.E8 := by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hγ
        rcases hγ with rfl | rfl | rfl
        · exact vA6_data.1
        · exact vA7_data.1
        · exact vGc_data.1
      exact pinnedX_commute_of_not_root hγr (mem_rootFinset.2 (isRoot_neg_highRoot _))
        hdata.1 hdata.2.1 hdata.2.2 s t
    have h6 := hc3 vA6 (by simp)
    have h7 := hc3 vA7 (by simp)
    have hc := hc3 vGc (by simp)
    calc pinnedX Tag.E8 D.L vA6 c * pinnedX Tag.E8 D.L vA7 d * pinnedX Tag.E8 D.L vGc z *
          pinnedX Tag.E8 D.L (-highRoot Tag.E8) t
        = pinnedX Tag.E8 D.L vA6 c * pinnedX Tag.E8 D.L vA7 d *
          (pinnedX Tag.E8 D.L vGc z * pinnedX Tag.E8 D.L (-highRoot Tag.E8) t) := by
            simp only [mul_assoc]
      _ = pinnedX Tag.E8 D.L vA6 c * pinnedX Tag.E8 D.L vA7 d *
          (pinnedX Tag.E8 D.L (-highRoot Tag.E8) t * pinnedX Tag.E8 D.L vGc z) := by rw [hc z]
      _ = pinnedX Tag.E8 D.L vA6 c * (pinnedX Tag.E8 D.L vA7 d *
          pinnedX Tag.E8 D.L (-highRoot Tag.E8) t) * pinnedX Tag.E8 D.L vGc z := by
            simp only [mul_assoc]
      _ = pinnedX Tag.E8 D.L vA6 c * (pinnedX Tag.E8 D.L (-highRoot Tag.E8) t *
          pinnedX Tag.E8 D.L vA7 d) * pinnedX Tag.E8 D.L vGc z := by rw [h7 d]
      _ = (pinnedX Tag.E8 D.L vA6 c * pinnedX Tag.E8 D.L (-highRoot Tag.E8) t) *
          pinnedX Tag.E8 D.L vA7 d * pinnedX Tag.E8 D.L vGc z := by simp only [mul_assoc]
      _ = (pinnedX Tag.E8 D.L (-highRoot Tag.E8) t * pinnedX Tag.E8 D.L vA6 c) *
          pinnedX Tag.E8 D.L vA7 d * pinnedX Tag.E8 D.L vGc z := by rw [h6 c]
      _ = _ := by simp only [mul_assoc]
  obtain ⟨hv'Q, hv'B, hv'R, hκ'⟩ := conj_step D hK hXH hℓX hℓL hℓU hT hvQ hvB hvR
  have h₃ : ∀ μ ∈ mRoots, μ + vGp ∈ rootFinset Tag.E8 → Tm c d z (κF D v) μ = 0 := by
    intro μ hμ hμp
    have := zstep D hK hHG hb hXH hv'Q hv'B hv'R vGp_data.1 vGp_data.2 hZp hno hμ
      ((mRoots_closed μ hμ).1 hμp)
    rw [hκ'] at this
    exact this
  obtain ⟨β, hβ, hcls⟩ := hY1
  exact hβ (Y1_vanish hc hd (κF D v) (fun ν hν => hvM ν hν) h₁ h₂ h₃ β (hvM β hβ) hcls)

end Case1

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.E8TenAux
