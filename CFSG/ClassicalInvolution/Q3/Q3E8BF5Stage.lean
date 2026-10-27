module

public import CFSG.ClassicalInvolution.Q3.Q3E8BF5Rat
public import CFSG.ClassicalInvolution.Q3.Q3E8BF5HJ
public import CFSG.ClassicalInvolution.ModelFacts.E8ExclD6Words

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Universal
  CFSG.LieType.CurtisTits CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.ModelFacts.Levi CFSG.ClassicalInvolution.ModelFacts
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD CFSG.Timmesfeld
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ClassicalInvolution.ModelFacts.E7Model CFSG.LieType.HighestRoot
open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open scoped commutatorElement MatrixGroups

set_option linter.unusedSectionVars false


local notation "M₇" => E7sc 3 1
local notation "D₇" => e7Datum (GaloisField 3 1)

section Stage

theorem exists_levi_conj_of_commutes_theta3 {X : Subgroup M₇}
    (hX : X ∈ Generic.fundamentalSubgroups .E7 D₇)
    (hcomm : Commutes (stdRankOne D₇ thetaE7) X) :
    ∃ x : M₇, (∃ a : Fin (Tag.rank .E7) → (GaloisField 3 1)ˣ,
        ∃ η ∈ NJ (GaloisField 3 1) JE7, εm (GaloisField 3 1) x = rootDiagUnit .E7 a * η) ∧
      conjSub x (stdRankOne D₇ thetaE7) = stdRankOne D₇ thetaE7 ∧
      ∃ γ : V7, IsRoot .E7 γ ∧ conjSub x X = stdRankOne D₇ γ := by
  have hF : ringChar (GaloisField 3 1) ≠ 2 := ringChar_galoisField_ne_two (by norm_num)
  have hodd : Odd (Nat.card (GaloisField 3 1)) := odd_gf3
  obtain ⟨hsingle, hRθF⟩ := e7_fund_class3
  obtain ⟨r₁, hr₁, hr₁2⟩ := exists_involution_fund3 hX
  obtain ⟨h, hh⟩ := hsingle _ hRθF X hX
  have hεr₁ := εm_involution_of_mem_fund3 (h := h) (by rw [← hh]; exact hr₁) hr₁2
  set y := εm (GaloisField 3 1) r₁ with hy
  have hr1sq : r₁ * r₁ = 1 := by rw [← sq]; exact hr₁2 ▸ pow_orderOf_eq_one r₁
  have hy2 : y * y = 1 := by rw [hy, ← map_mul, hr1sq, map_one]
  have hyθ : ∀ A : SL2 (GaloisField 3 1),
      y * rootSL2 .E7 (GaloisField 3 1) thetaE7 A =
        rootSL2 .E7 (GaloisField 3 1) thetaE7 A * y := by
    intro A
    have hmem : rootSL2 .E7 (GaloisField 3 1) thetaE7 A ∈
        (stdRankOne D₇ thetaE7).map (εm (GaloisField 3 1)) := by
      rw [map_stdRankOne_εm isRoot_thetaE7]
      exact ⟨A, rfl⟩
    obtain ⟨x, hx, hxe⟩ := Subgroup.mem_map.1 hmem
    rw [← hxe, hy, ← map_mul, ← map_mul, (hcomm x hx r₁ hr₁).symm]
  have hyd : y * rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : (GaloisField 3 1)ˣ)) =
      rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : (GaloisField 3 1)ˣ)) * y := by
    have h1 := hyθ (HSL (-1))
    rwa [show rootSL2 .E7 (GaloisField 3 1) thetaE7 (HSL (-1)) =
      rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : (GaloisField 3 1)ˣ)) from
        rootTorusSL2_thetaE7 (-1)] at h1
  set k := AlgebraicClosure (GaloisField 3 1) with hkdef
  set ι := algebraMap (GaloisField 3 1) k with hι
  have hpk : CharP k 3 := charP_of_injective_algebraMap ι.injective 3
  have hkF : ringChar k ≠ 2 := by rw [ringChar.eq k 3]; norm_num
  have h2 : (2 : k) ≠ 0 := Ring.two_ne_zero hkF
  have hyG' : baseChangeGL ι y ∈ adjointGroup .E7 k := baseChangeGL_mem_adjointGroup ι (εm_mem r₁)
  have hyk : ∀ A : SL2 k, Commute (baseChangeGL ι y) (rootSL2 .E7 k thetaE7 A) :=
    commute_rootSL2_baseChange (Or.inr (Or.inr (Or.inl rfl))) ι h2 _ (fun A => hyθ A)
  obtain ⟨a, ha⟩ := exists_unit_pow_ne_one (k := k) 4
  have ha4 : a ^ 4 ≠ 1 := ha 4 (by norm_num) le_rfl
  have hchar : rootChar (thetaDiag thetaE7 a) thetaE7 = a ^ 2 := by
    rw [rootChar_thetaDiag, iform_self_isRoot_E7 isRoot_thetaE7]
    simp
  have hyb : baseChangeGL ι y * rootDiagUnit .E7 (thetaDiag thetaE7 a) =
      rootDiagUnit .E7 (thetaDiag thetaE7 a) * baseChangeGL ι y := by
    rw [← rootTorusSL2_thetaE7 a]
    exact (hyk (HSL a)).eq
  have hyd' : baseChangeGL ι y * rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : kˣ)) =
      rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : kˣ)) * baseChangeGL ι y := by
    rw [← baseChangeGL_rootDiagUnit_thetaDiag_E7 ι, ← map_mul, ← map_mul, hyd]
  have hyJ : baseChangeGL ι y ∈ parabolicLevi .E7 k JE7 :=
    mem_parabolicLevi_of_commute_diag (F := k) hkF hyG' hyd'
      (by rw [hchar, ← pow_mul]; exact ha4) hyb
  obtain ⟨δ, hδ, u, huG, hu, hucomm, a₀, η, hη, hue⟩ := exists_rational_levi_conj_nj hodd
    (fun j hj => iform_thetaE7_single_of_mem hj) (fun σ hσ => abs_iform_thetaE7_le σ hσ)
    (fun σ hσ h0 => mem_parabolicRoots_E7 (mem_rootFinset.1 hσ) h0)
    (εm_mem r₁) (εm_mem h) hy2 hyJ hεr₁.symm
  obtain ⟨x, hx⟩ := εm_surjective huG
  have hθJ : ∀ j ∈ JE7, Even (iform thetaE7 (Pi.single j 1)) := fun j hj => by
    rw [iform_thetaE7_single_of_mem hj]
    exact ⟨0, by simp⟩
  have hxθ : conjSub x (stdRankOne D₇ thetaE7) = stdRankOne D₇ thetaE7 := by
    have hRθ' := std_mem_fund3 isRoot_thetaE7
    apply eq_of_map_εm_eq3 (conjSub_mem_fundamentalSubgroups hRθ' x) hRθ'
    have hwd : u * rootTorusSL2 .E7 (GaloisField 3 1) thetaE7 (-1) =
        rootTorusSL2 .E7 (GaloisField 3 1) thetaE7 (-1) * u := by
      rw [rootTorusSL2_eq_thetaDiag isRoot_thetaE7]
      exact hucomm _ (fun j hj => by simp [thetaDiag, (hθJ j hj).neg_one_zpow])
    rw [map_conjSub, hx, map_stdRankOne_εm isRoot_thetaE7,
      map_conj_rootRankOneGroup_of_commute_gen hF hodd isRoot_thetaE7 huG hwd]
  have hconj : (u * εm (GaloisField 3 1) h) * rootTorusSL2 .E7 (GaloisField 3 1) thetaE7 (-1) *
      (u * εm (GaloisField 3 1) h)⁻¹ =
      rootDiagUnit .E7 (thetaDiag δ (-1 : (GaloisField 3 1)ˣ)) := by
    rw [rootTorusSL2_thetaE7]
    calc (u * εm (GaloisField 3 1) h) *
          rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : (GaloisField 3 1)ˣ)) *
          (u * εm (GaloisField 3 1) h)⁻¹ =
        u * (εm (GaloisField 3 1) h *
          rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : (GaloisField 3 1)ˣ)) *
          (εm (GaloisField 3 1) h)⁻¹) * u⁻¹ := by group
      _ = u * y * u⁻¹ := by rw [← hεr₁]
      _ = _ := hu
  obtain ⟨γ, hγ, hLγ, -, -⟩ := exists_rootRankOneGroup_of_conj_toral3
    (isLongRoot_of_isRoot_of_simplyLaced (Or.inr (Or.inl rfl)) isRoot_thetaE7)
    (mul_mem huG (εm_mem h)) (fun i => thetaDiag_neg_one_sign_E7 δ i) hconj
  have hγr : IsRoot .E7 γ := hγ.1
  refine ⟨x, ⟨a₀, η, hη, hx.trans hue⟩, hxθ, γ, hγr, ?_⟩
  have hγF := std_mem_fund3 hγr
  rw [hh, ← conjSub_mul]
  apply eq_of_map_εm_eq3 (conjSub_mem_fundamentalSubgroups hRθF _) hγF
  rw [map_conjSub, map_mul, hx, map_stdRankOne_εm isRoot_thetaE7, map_stdRankOne_εm hγr]
  exact hLγ

theorem exists_mem_HJ_conj_of_commutes_theta3 {X : Subgroup M₇}
    (hX : X ∈ Generic.fundamentalSubgroups .E7 D₇)
    (hcomm : Commutes (stdRankOne D₇ thetaE7) X) :
    ∃ h ∈ HJ 3 1, X = conjSub h (rankOne (e7Datum (GaloisField 3 1)).rootGroup (e7Idx 6)) := by
  obtain ⟨x, ⟨a, η, hη, hxe⟩, hxθ, γ, hγ, hxX⟩ := exists_levi_conj_of_commutes_theta3 hX hcomm
  have hcγ : Commutes (stdRankOne D₇ thetaE7) (stdRankOne D₇ γ) := by
    have := hcomm.conjSub x
    rwa [hxθ, hxX] at this
  have h0 : iform thetaE7 γ = 0 := iform_eq_zero_of_commutes3 isRoot_thetaE7 hγ hcγ
  obtain ⟨h₁, hh₁, hh₁γ⟩ := exists_mem_HJ_conj3 (x := x⁻¹)
    ⟨η⁻¹, inv_mem hη, a⁻¹, by rw [map_inv, hxe, mul_inv_rev, rootDiagUnit_inv]⟩
  obtain ⟨k, hk, hkγ⟩ := exists_mem_HJ_conj_rankOne (p := 3) (f := 1) hγ h0
  refine ⟨h₁ * k⁻¹, mul_mem hh₁ (inv_mem hk), ?_⟩
  have hX' : X = conjSub x⁻¹ (stdRankOne D₇ γ) := by
    rw [← hxX, Generic.conjSub_inv_conjSub]
  have hRγ : stdRankOne D₇ γ =
      conjSub k⁻¹ (rankOne (e7Datum (GaloisField 3 1)).rootGroup (e7Idx 6)) := by
    rw [← hkγ, Generic.conjSub_inv_conjSub]
  rw [hX', hh₁γ γ hγ, hRγ, ← conjSub_mul]

end Stage

end CFSG.ClassicalInvolution.Q3.Q3W
