module

public import CFSG.ClassicalInvolution.Q3.Q3E7MPair
public import CFSG.ClassicalInvolution.Q3.Q3E7MLin
public import CFSG.ClassicalInvolution.ModelFacts.E7ModelSignMain
public import CFSG.ClassicalInvolution.ModelFacts.E7ModelPerp

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


section Sign

theorem levi_step3 {y : ModGL .E7 (GaloisField 3 1)}
    (hyG : y ∈ adjointGroup .E7 (GaloisField 3 1))
    (hyd : y * rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : (GaloisField 3 1)ˣ)) =
      rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : (GaloisField 3 1)ˣ)) * y)
    (hye : ∀ A : SL2 (GaloisField 3 1),
      y * rootSL2 .E7 (GaloisField 3 1) (Pi.single (e7Idx 0) 1) A =
        rootSL2 .E7 (GaloisField 3 1) (Pi.single (e7Idx 0) 1) A * y) :
    baseChangeGL (algebraMap (GaloisField 3 1) (AlgebraicClosure (GaloisField 3 1))) y ∈
      parabolicLevi .E7 (AlgebraicClosure (GaloisField 3 1)) JE7 := by
  set k := AlgebraicClosure (GaloisField 3 1) with hkdef
  set ι := algebraMap (GaloisField 3 1) k with hι
  have hpk : CharP k 3 := charP_of_injective_algebraMap ι.injective 3
  have hkF : ringChar k ≠ 2 := by rw [ringChar.eq k 3]; norm_num
  have h2 : (2 : k) ≠ 0 := Ring.two_ne_zero hkF
  have he0 : IsRoot .E7 (Pi.single (e7Idx 0) 1 : V7) := isRoot_single .E7 (e7Idx 0)
  have hyG' : baseChangeGL ι y ∈ adjointGroup .E7 k := baseChangeGL_mem_adjointGroup ι hyG
  have hyk : ∀ A : SL2 k, Commute (baseChangeGL ι y)
      (rootSL2 .E7 k (Pi.single (e7Idx 0) 1) A) :=
    commute_rootSL2_baseChange (Or.inr (Or.inr (Or.inl rfl))) ι h2 _ (fun A => hye A)
  obtain ⟨a, ha⟩ := exists_unit_pow_ne_one (k := k) 2
  have ha2 : a ^ 2 ≠ 1 := ha 2 (by norm_num) le_rfl
  have hchar : rootChar (thetaDiag (Pi.single (e7Idx 0) 1 : V7) a) thetaE7 = a := by
    rw [rootChar_thetaDiag, iform_comm, iform_thetaE7_single]
    simp [e7Idx]
  have hyb : baseChangeGL ι y * rootDiagUnit .E7 (thetaDiag (Pi.single (e7Idx 0) 1 : V7) a) =
      rootDiagUnit .E7 (thetaDiag (Pi.single (e7Idx 0) 1 : V7) a) * baseChangeGL ι y := by
    rw [← rootTorusSL2_eq_thetaDiag_gen he0]
    exact (hyk (HSL a)).eq
  have hyd' : baseChangeGL ι y * rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : kˣ)) =
      rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : kˣ)) * baseChangeGL ι y := by
    rw [← baseChangeGL_rootDiagUnit_thetaDiag_E7 ι, ← map_mul, ← map_mul, hyd]
  exact mem_parabolicLevi_of_commute_diag (F := k) hkF hyG' hyd'
    (by rw [hchar]; exact ha2) hyb

theorem levi_prefix3 {y : ModGL .E7 (GaloisField 3 1)}
    (hyG : y ∈ adjointGroup .E7 (GaloisField 3 1))
    (hyd : y * rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : (GaloisField 3 1)ˣ)) =
      rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : (GaloisField 3 1)ˣ)) * y)
    (hye : ∀ A : SL2 (GaloisField 3 1),
      y * rootSL2 .E7 (GaloisField 3 1) (Pi.single (e7Idx 0) 1) A =
        rootSL2 .E7 (GaloisField 3 1) (Pi.single (e7Idx 0) 1) A * y) :
    baseChangeGL (algebraMap (GaloisField 3 1) (AlgebraicClosure (GaloisField 3 1))) y ∈
      parabolicLevi .E7 (AlgebraicClosure (GaloisField 3 1)) Jsign := by
  set k := AlgebraicClosure (GaloisField 3 1) with hkdef
  set ι := algebraMap (GaloisField 3 1) k with hι
  have hpk : CharP k 3 := charP_of_injective_algebraMap ι.injective 3
  have hkF : ringChar k ≠ 2 := by rw [ringChar.eq k 3]; norm_num
  have hk2 : (-1 : kˣ) ≠ 1 := fun h =>
    Ring.neg_one_ne_one_of_char_ne_two hkF (by simpa using congrArg Units.val h)
  have he0 : IsRoot .E7 (Pi.single (e7Idx 0) 1 : V7) := isRoot_single .E7 (e7Idx 0)
  have hyL : baseChangeGL ι y ∈ parabolicLevi .E7 k JE7 := levi_step3 hyG hyd hye
  have hyG' : baseChangeGL ι y ∈ adjointGroup .E7 k := baseChangeGL_mem_adjointGroup ι hyG
  have hyde : y * rootDiagUnit .E7
      (thetaDiag (Pi.single (e7Idx 0) 1 : V7) (-1 : (GaloisField 3 1)ˣ)) =
      rootDiagUnit .E7 (thetaDiag (Pi.single (e7Idx 0) 1 : V7) (-1 : (GaloisField 3 1)ˣ)) * y := by
    rw [← rootTorusSL2_eq_thetaDiag_gen he0]
    exact hye (HSL (-1))
  have hyde' : baseChangeGL ι y * rootDiagUnit .E7
      (thetaDiag (Pi.single (e7Idx 0) 1 : V7) (-1 : kˣ)) = rootDiagUnit .E7
      (thetaDiag (Pi.single (e7Idx 0) 1 : V7) (-1 : kˣ)) * baseChangeGL ι y := by
    rw [← baseChangeGL_rootDiagUnit_thetaDiag_E7 ι, ← map_mul, ← map_mul, hyde]
  exact mem_levi_of_commute_signdiag hk2 (fun j hj => iform_thetaE7_single_of_mem hj)
    (fun σ hσ => abs_iform_thetaE7_le σ hσ) he0 sign_cut hyG' hyL hyde'

theorem sign_core3 {y g : ModGL .E7 (GaloisField 3 1)}
    (hyG : y ∈ adjointGroup .E7 (GaloisField 3 1))
    (hgG : g ∈ adjointGroup .E7 (GaloisField 3 1)) (hy2 : y * y = 1)
    (hgy : g * rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : (GaloisField 3 1)ˣ)) * g⁻¹ = y)
    (hyd : y * rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : (GaloisField 3 1)ˣ)) =
      rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : (GaloisField 3 1)ˣ)) * y)
    (hye : ∀ A : SL2 (GaloisField 3 1),
      y * rootSL2 .E7 (GaloisField 3 1) (Pi.single (e7Idx 0) 1) A =
        rootSL2 .E7 (GaloisField 3 1) (Pi.single (e7Idx 0) 1) A * y) :
    ∃ δ, IsRoot .E7 δ ∧ ∃ u ∈ adjointGroup .E7 (GaloisField 3 1),
      u * y * u⁻¹ = rootDiagUnit .E7 (thetaDiag δ (-1 : (GaloisField 3 1)ˣ)) ∧
      u * rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : (GaloisField 3 1)ˣ)) =
        rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : (GaloisField 3 1)ˣ)) * u ∧
      u * rootDiagUnit .E7 (thetaDiag (Pi.single (e7Idx 0) 1) (-1 : (GaloisField 3 1)ˣ)) =
        rootDiagUnit .E7 (thetaDiag (Pi.single (e7Idx 0) 1) (-1 : (GaloisField 3 1)ˣ)) * u := by
  have hodd : Odd (Nat.card (GaloisField 3 1)) := odd_gf3
  have hyJ'' := levi_prefix3 hyG hyd hye
  obtain ⟨δ, hδ, u, huG, hu, hucomm⟩ := exists_rational_levi_conj hodd lamSign_J lamSign_B
    lamSign_ker hyG hgG hy2 hyJ'' hgy
  refine ⟨δ, hδ, u, huG, hu, hucomm _ fun j hj => ?_, hucomm _ fun j hj => ?_⟩
  · simp [thetaDiag, (Jsign_thetaDiag_one j hj).1]
  · simp [thetaDiag, (Jsign_thetaDiag_one j hj).2]


theorem sign_step3 {X : Subgroup M₇}
    (hX : X ∈ Generic.fundamentalSubgroups .E7 D₇) {r₁ r₂ : M₇} (hr₁ : r₁ ∈ X)
    (hr₁2 : orderOf r₁ = 2)
    (hr₂ : r₂ ∈ stdRankOne D₇ thetaE7) (hr₂2 : orderOf r₂ = 2)
    (hnorm : ∀ x ∈ X, r₂ * x * r₂⁻¹ ∈ X)
    (hcomm : Commutes (stdRankOne D₇ (Pi.single (e7Idx 0) 1)) X) :
    ∃ x : M₇, conjSub x (stdRankOne D₇ thetaE7) = stdRankOne D₇ thetaE7 ∧
      conjSub x (stdRankOne D₇ (Pi.single (e7Idx 0) 1)) =
        stdRankOne D₇ (Pi.single (e7Idx 0) 1) ∧
      ∃ γ : Fin (Tag.rank .E7) → ℤ, IsRoot .E7 γ ∧ conjSub x X = stdRankOne D₇ γ := by
  have hF : ringChar (GaloisField 3 1) ≠ 2 := ringChar_galoisField_ne_two (by norm_num)
  have hodd : Odd (Nat.card (GaloisField 3 1)) := odd_gf3
  obtain ⟨hsingle, hRθF⟩ := e7_fund_class3
  have he0 : IsRoot .E7 (Pi.single (e7Idx 0) 1 : V7) := isRoot_single .E7 (e7Idx 0)
  have he0F := std_mem_fund3 he0
  have hεr₂ : εm (GaloisField 3 1) r₂ =
      rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : (GaloisField 3 1)ˣ)) := by
    have := εm_involution_of_mem_fund3 (h := 1) (by rw [conjSub_one]; exact hr₂) hr₂2
    simpa using this
  have hr₁₂ : r₂ * r₁ * r₂⁻¹ = r₁ := by
    refine eq_of_orderOf_two_fund3 hX (hnorm r₁ hr₁) hr₁ ?_ hr₁2
    rw [← hr₁2]
    exact (orderOf_injective (MulAut.conj r₂).toMonoidHom (MulAut.conj r₂).injective r₁)
  obtain ⟨h, hh⟩ := hsingle _ hRθF X hX
  have hεr₁ := εm_involution_of_mem_fund3 (h := h) (by rw [← hh]; exact hr₁) hr₁2
  set y := εm (GaloisField 3 1) r₁ with hy
  have hr1sq : r₁ * r₁ = 1 := by rw [← sq]; exact hr₁2 ▸ pow_orderOf_eq_one r₁
  have hy2 : y * y = 1 := by
    rw [hy, ← map_mul, hr1sq, map_one]
  have hyd : y * rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : (GaloisField 3 1)ˣ)) =
      rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : (GaloisField 3 1)ˣ)) * y := by
    rw [← hεr₂, hy, ← map_mul, ← map_mul]
    congr 1
    have := hr₁₂
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm
  have hye : ∀ A : SL2 (GaloisField 3 1),
      y * rootSL2 .E7 (GaloisField 3 1) (Pi.single (e7Idx 0) 1) A =
        rootSL2 .E7 (GaloisField 3 1) (Pi.single (e7Idx 0) 1) A * y := by
    intro A
    have hmem : rootSL2 .E7 (GaloisField 3 1) (Pi.single (e7Idx 0) 1) A ∈
        (stdRankOne D₇ (Pi.single (e7Idx 0) 1)).map (εm (GaloisField 3 1)) := by
      rw [map_stdRankOne_εm he0]
      exact ⟨A, rfl⟩
    obtain ⟨x, hx, hxe⟩ := Subgroup.mem_map.1 hmem
    rw [← hxe, hy, ← map_mul, ← map_mul, (hcomm x hx r₁ hr₁).symm]
  obtain ⟨δ, hδ, u, huG, hu, hudθ, hude0⟩ := sign_core3 (εm_mem r₁) (εm_mem h) hy2
    hεr₁.symm hyd hye
  obtain ⟨x, hx⟩ := εm_surjective huG
  have hxL : conjSub x (stdRankOne D₇ thetaE7) = stdRankOne D₇ thetaE7 := by
    apply eq_of_map_εm_eq3 (conjSub_mem_fundamentalSubgroups hRθF x) hRθF
    rw [map_conjSub, hx, map_stdRankOne_εm isRoot_thetaE7,
      map_conj_rootRankOneGroup_of_commute hF huG hudθ]
  have hxE : conjSub x (stdRankOne D₇ (Pi.single (e7Idx 0) 1)) =
      stdRankOne D₇ (Pi.single (e7Idx 0) 1) := by
    apply eq_of_map_εm_eq3 (conjSub_mem_fundamentalSubgroups he0F x) he0F
    have hwd : u * rootTorusSL2 .E7 (GaloisField 3 1) (Pi.single (e7Idx 0) 1) (-1) =
        rootTorusSL2 .E7 (GaloisField 3 1) (Pi.single (e7Idx 0) 1) (-1) * u := by
      rw [rootTorusSL2_eq_thetaDiag_gen he0 (-1)]
      exact hude0
    rw [map_conjSub, hx, map_stdRankOne_εm he0,
      map_conj_rootRankOneGroup_of_commute_gen hF hodd he0 huG hwd]
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
  refine ⟨x, hxL, hxE, γ, hγr, ?_⟩
  have hγF := std_mem_fund3 hγr
  rw [hh, ← conjSub_mul]
  apply eq_of_map_εm_eq3 (conjSub_mem_fundamentalSubgroups hRθF _) hγF
  rw [map_conjSub, map_mul, hx, map_stdRankOne_εm isRoot_thetaE7, map_stdRankOne_εm hγr]
  exact hLγ


theorem e7Sign_sc_3 :
    ∀ R₁ ∈ Generic.fundamentalSubgroups .E7 D₇, ∀ R₂ ∈ Generic.fundamentalSubgroups .E7 D₇,
      ∀ R₃ ∈ Generic.fundamentalSubgroups .E7 D₇,
      Gaps.ModelAdj (Subgroup.center M₇) R₁ R₂ → Gaps.ModelAdj (Subgroup.center M₇) R₃ R₂ →
      Commutes R₁ R₃ → (∃ W, LinearBlockStandardPair (GaloisField 3 1) W R₁ R₂) →
      ∃ W, LinearBlockStandardPair (GaloisField 3 1) W R₂ R₃ := by
  intro R₁ hR₁ R₂ hR₂ R₃ hR₃ hadj12 hadj32 hc13 hlin12
  have he0 : IsRoot .E7 (Pi.single (e7Idx 0) 1 : V7) := isRoot_single .E7 (e7Idx 0)
  have he2 : IsRoot .E7 (Pi.single (e7Idx 2) 1 : V7) := isRoot_single .E7 (e7Idx 2)
  obtain ⟨g, hg1, hg2⟩ := e7PairFrame_sc_3 R₁ hR₁ R₂ hR₂ hadj12 hlin12 0 2 (by decide)
  have hpair : iform (Pi.single (e7Idx 2) 1 : V7) (Pi.single (e7Idx 0) 1) = 1 ∨
      iform (Pi.single (e7Idx 2) 1 : V7) (Pi.single (e7Idx 0) 1) = -1 := by decide +kernel
  obtain ⟨k, hk2, hk0⟩ := exists_conj_theta_e0 (GaloisField 3 1) he2 he0 hpair
  rw [e7Idx_zero] at hk0
  set x₀ : M₇ := k * g⁻¹ with hx₀
  have hx₀2 : conjSub x₀ R₂ = stdRankOne D₇ thetaE7 := by
    rw [hx₀, conjSub_mul, hg2, Generic.conjSub_inv_conjSub]
    exact hk2
  have hx₀1 : conjSub x₀ R₁ = stdRankOne D₇ (Pi.single (e7Idx 0) 1) := by
    rw [hx₀, conjSub_mul, hg1, Generic.conjSub_inv_conjSub]
    exact hk0
  obtain ⟨hne32, hnc32, r₃, r₂', hr₃, hr₂', -, hnorm⟩ := hadj32
  set X := conjSub x₀ R₃ with hXdef
  have hXF : X ∈ Generic.fundamentalSubgroups .E7 D₇ := conjSub_mem_fundamentalSubgroups hR₃ x₀
  have hr₃' : x₀ * r₃ * x₀⁻¹ ∈ X := conj_mem_conjSub hr₃.1
  have hr₃2 : orderOf (x₀ * r₃ * x₀⁻¹) = 2 := by
    rw [← hr₃.2]
    exact orderOf_injective (MulAut.conj x₀).toMonoidHom (MulAut.conj x₀).injective r₃
  have hr₂'' : x₀ * r₂' * x₀⁻¹ ∈ stdRankOne D₇ thetaE7 := by
    rw [← hx₀2]
    exact conj_mem_conjSub hr₂'.1
  have hr₂2 : orderOf (x₀ * r₂' * x₀⁻¹) = 2 := by
    rw [← hr₂'.2]
    exact orderOf_injective (MulAut.conj x₀).toMonoidHom (MulAut.conj x₀).injective r₂'
  have hnorm' : ∀ x ∈ X, (x₀ * r₂' * x₀⁻¹) * x * (x₀ * r₂' * x₀⁻¹)⁻¹ ∈ X := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hx
    have : x₀ * (r₂' * a * r₂'⁻¹) * x₀⁻¹ ∈ conjSub x₀ R₃ := conj_mem_conjSub (hnorm a ha)
    convert this using 1
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hcomm' : Commutes (stdRankOne D₇ (Pi.single (e7Idx 0) 1)) X := by
    have := hc13.conjSub x₀
    rwa [hx₀1] at this
  obtain ⟨x, hxL, hxE, γ, hγ, hxX⟩ := sign_step3 hXF hr₃' hr₃2 hr₂'' hr₂2 hnorm' hcomm'
  have hθ : IsRoot .E7 thetaE7 := isRoot_thetaE7
  have hback : ∀ A B : Subgroup M₇, conjSub x A = conjSub x B → A = B := fun A B h => by
    have := congrArg (conjSub x⁻¹) h
    rwa [Generic.conjSub_inv_conjSub, Generic.conjSub_inv_conjSub] at this
  have hback' : ∀ A B : Subgroup M₇, conjSub x₀ A = conjSub x₀ B → A = B := fun A B h => by
    have := congrArg (conjSub x₀⁻¹) h
    rwa [Generic.conjSub_inv_conjSub, Generic.conjSub_inv_conjSub] at this
  have hcomm_back : ∀ (A B : Subgroup M₇) (g : M₇), Commutes (conjSub g A) (conjSub g B) →
      Commutes A B := fun A B g h => by
    have := h.conjSub g⁻¹
    rwa [Generic.conjSub_inv_conjSub, Generic.conjSub_inv_conjSub] at this
  by_cases hγe : γ = Pi.single (e7Idx 0) 1 ∨ γ = -Pi.single (e7Idx 0) 1
  · have hY : conjSub x X = conjSub x (stdRankOne D₇ (Pi.single (e7Idx 0) 1)) := by
      rw [hxX, hxE]
      rcases hγe with h | h
      · rw [h]
      · rw [h, stdRankOne_neg]
    have hX1 : X = stdRankOne D₇ (Pi.single (e7Idx 0) 1) := hback _ _ hY
    have hR31 : R₃ = R₁ := hback' _ _ (hX1.trans hx₀1.symm)
    rw [hR31]
    obtain ⟨W, hW⟩ := hlin12
    exact ⟨W, linearBlockStandardPair_symm' hW⟩
  have hY_ne : stdRankOne D₇ γ ≠ stdRankOne D₇ thetaE7 := by
    intro h
    apply hne32
    have h1 : conjSub x X = conjSub x (stdRankOne D₇ thetaE7) := by rw [hxX, h, hxL]
    have h2 : X = conjSub x₀ R₂ := (hback _ _ h1).trans hx₀2.symm
    exact hback' _ _ h2
  have hLinv : conjSub x⁻¹ (stdRankOne D₇ thetaE7) = stdRankOne D₇ thetaE7 := by
    have := congrArg (conjSub x⁻¹) hxL
    rw [Generic.conjSub_inv_conjSub] at this
    exact this.symm
  have hY_nc : ¬ Commutes (stdRankOne D₇ γ) (stdRankOne D₇ thetaE7) := by
    intro h
    apply hnc32
    have h2 := h.conjSub x⁻¹
    rw [← hxX, Generic.conjSub_inv_conjSub, hLinv, ← hx₀2] at h2
    exact hcomm_back R₃ R₂ x₀ h2
  have hY_c0 : Commutes (stdRankOne D₇ (Pi.single (e7Idx 0) 1)) (stdRankOne D₇ γ) := by
    have := hcomm'.conjSub x
    rwa [hxE, hxX] at this
  have h0γ : iform (Pi.single (e7Idx 0) 1 : V7) γ = 0 := by
    by_contra hne
    have hb := abs_iform_le_two_E7 he0 hγ
    rw [abs_le] at hb
    have hcases : iform (Pi.single (e7Idx 0) 1 : V7) γ = -2 ∨
        iform (Pi.single (e7Idx 0) 1 : V7) γ = -1 ∨
        iform (Pi.single (e7Idx 0) 1 : V7) γ = 1 ∨ iform (Pi.single (e7Idx 0) 1 : V7) γ = 2 := by
      omega
    rcases hcases with h | h | h | h
    · exact hγe (eq_or_neg_of_iform_eq_two he0 hγ (Or.inr h))
    · obtain ⟨W, hW⟩ := linearPair_of_roots (GaloisField 3 1) he0 hγ (Or.inr h)
      exact not_commutes_of_linearBlockStandardPair hW hY_c0
    · obtain ⟨W, hW⟩ := linearPair_of_roots (GaloisField 3 1) he0 hγ (Or.inl h)
      exact not_commutes_of_linearBlockStandardPair hW hY_c0
    · exact hγe (eq_or_neg_of_iform_eq_two he0 hγ (Or.inl h))
  have hθγ : iform thetaE7 γ = 1 ∨ iform thetaE7 γ = -1 := by
    have hb := abs_iform_le_two_E7 hθ hγ
    rw [abs_le] at hb
    by_contra hne
    have hcases : iform thetaE7 γ = -2 ∨ iform thetaE7 γ = 0 ∨ iform thetaE7 γ = 2 := by omega
    have hneg : γ = thetaE7 ∨ γ = -thetaE7 → False := fun h' => hY_ne (by
      rcases h' with h' | h'
      · rw [h']
      · rw [h', stdRankOne_neg])
    rcases hcases with h | h | h
    · exact hneg (eq_or_neg_of_iform_eq_two hθ hγ (Or.inr h))
    · exact hY_nc (commutes_std3 hγ hθ (by rw [iform_comm]; exact h))
    · exact hneg (eq_or_neg_of_iform_eq_two hθ hγ (Or.inl h))
  obtain ⟨W, hW⟩ := linearPair_of_roots (GaloisField 3 1) hθ hγ hθγ
  have e2 : conjSub (x * x₀) R₂ = stdRankOne D₇ thetaE7 := by rw [conjSub_mul, hx₀2, hxL]
  have e3 : conjSub (x * x₀) R₃ = stdRankOne D₇ γ := by rw [conjSub_mul, ← hXdef, hxX]
  have h4 := linearBlockStandardPair_map_conj hW (x * x₀)⁻¹
  change LinearBlockStandardPair (GaloisField 3 1) _ (conjSub _ _) (conjSub _ _) at h4
  rw [← e2, ← e3, Generic.conjSub_inv_conjSub, Generic.conjSub_inv_conjSub] at h4
  exact ⟨_, h4⟩


theorem e7Perp2_3 : TypeE8.E7Perp2 3 1 := by
  intro R₁ hR₁ R₂ hR₂ hadj hlin
  have hadm : StatedLieAdmissible .E7 0 3 1 :=
    ⟨Nat.prime_three, le_rfl, rfl⟩
  have hl := ModelFacts.isLongestRoot_single .E7 0 3 1 Nat.prime_three trivial hadm
  obtain ⟨g, hg₁, hg₂⟩ := e7PairFrame3 R₁ hR₁ R₂ hR₂ hadj hlin 2 3 (by decide)
  have hfund : ∀ a : Fin 7,
      conjSub g (rankOne (TypeE8.D7 3 1).rootGroup a) ∈ TypeE8.F7 3 1 := fun a =>
    conjSub_mem_fundamentalSubgroups (rankOne_mem_fundamental _ (hl a trivial)) g
  have hnc : ∀ a b : Fin 7, edgeE 7 a b →
      ¬ Commutes (conjSub g (rankOne (TypeE8.D7 3 1).rootGroup a))
        (conjSub g (rankOne (TypeE8.D7 3 1).rootGroup b)) := fun a b hab h => by
    obtain ⟨W, hW⟩ := stdPair_edge_E7 (F := GaloisField 3 1) hab
    exact not_commutes_of_linearBlockStandardPair hW (commutes_of_conjSub_commutes g h)
  refine ⟨_, hfund 1, _, hfund 4, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have h14 : rankOne (TypeE8.D7 3 1).rootGroup (1 : Fin 7) =
        rankOne (TypeE8.D7 3 1).rootGroup (4 : Fin 7) := by
      have := congrArg (conjSub g⁻¹) h
      rw [Generic.conjSub_inv_conjSub, Generic.conjSub_inv_conjSub] at this
      exact this
    have h15 := ETCtx.commutes_rankOne_E7 (p := 3) (f := 1) hadm 1 5 (by decide) (by decide)
      (by decide)
    rw [h14] at h15
    obtain ⟨W, hW⟩ := stdPair_edge_E7 (F := GaloisField 3 1) (i := 4) (j := 5) (by decide)
    exact not_commutes_of_linearBlockStandardPair hW h15
  · rw [hg₁]
    exact (ETCtx.commutes_rankOne_E7 (p := 3) (f := 1) hadm 2 1 (by decide) (by decide)
      (by decide)).conjSub g
  · rw [hg₁]
    exact (ETCtx.commutes_rankOne_E7 (p := 3) (f := 1) hadm 2 4 (by decide) (by decide)
      (by decide)).conjSub g
  · rw [hg₂]
    intro h
    exact hnc 1 3 (by decide) h.symm
  · rw [hg₂]
    intro h
    exact hnc 3 4 (by decide) h


theorem e7Sign3 : TypeE8.E7Sign 3 1 := e7Sign_sc_3

theorem e7SignPerp3 : TypeE8.E7Sign 3 1 ∧ TypeE8.E7Perp2 3 1 := ⟨e7Sign3, e7Perp2_3⟩

end Sign

end CFSG.ClassicalInvolution.Q3.Q3W
