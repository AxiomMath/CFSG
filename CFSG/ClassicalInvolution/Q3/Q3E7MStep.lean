module

public import CFSG.ClassicalInvolution.Q3.Q3E7MSign
public import CFSG.ClassicalInvolution.ModelFacts.E7ModelFrame

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


section Rel

theorem not_commutes_self_std3 {γ : V7} (hγ : IsRoot .E7 γ) :
    ¬ Commutes (stdRankOne D₇ γ) (stdRankOne D₇ γ) := by
  intro h
  have hγF := std_mem_fund3 hγ
  obtain ⟨r, hr, hr2⟩ := exists_involution_std3 hγ
  have hbot : ⁅stdRankOne D₇ γ, stdRankOne D₇ γ⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact h y hy x hx
  have hr3 := pow3_fund3 hγF r hr
  rw [hbot, Subgroup.mem_bot] at hr3
  have hsq : r ^ 2 = 1 := by rw [← hr2]; exact pow_orderOf_eq_one r
  have hr13 : r ^ 3 = r := by
    calc r ^ 3 = r ^ 2 * r := pow_succ r 2
      _ = r := by rw [hsq, one_mul]
  have hr1 : r = 1 := hr13.symm.trans hr3
  rw [hr1, orderOf_one] at hr2
  omega

theorem iform_eq_zero_of_commutes3 {a b : V7} (ha : IsRoot .E7 a)
    (hb : IsRoot .E7 b) (h : Commutes (stdRankOne D₇ a) (stdRankOne D₇ b)) : iform a b = 0 := by
  have hbd := abs_iform_le_two_E7 ha hb
  rw [abs_le] at hbd
  by_contra hne
  have hcases : iform a b = -2 ∨ iform a b = -1 ∨ iform a b = 1 ∨ iform a b = 2 := by omega
  have hsq : iform a b = 2 ∨ iform a b = -2 → False := fun h2 => by
    rcases eq_or_neg_of_iform_eq_two ha hb h2 with rfl | rfl
    · exact not_commutes_self_std3 ha h
    · rw [stdRankOne_neg] at h
      exact not_commutes_self_std3 ha h
  rcases hcases with h' | h' | h' | h'
  · exact hsq (Or.inr h')
  · obtain ⟨W, hW⟩ := linearPair_of_roots (GaloisField 3 1) ha hb (Or.inr h')
    exact not_commutes_of_linearBlockStandardPair hW h
  · obtain ⟨W, hW⟩ := linearPair_of_roots (GaloisField 3 1) ha hb (Or.inl h')
    exact not_commutes_of_linearBlockStandardPair hW h
  · exact hsq (Or.inl h')

theorem iform_odd_of_rel3 {a b : V7} (ha : IsRoot .E7 a)
    (hb : IsRoot .E7 b) (hne : stdRankOne D₇ a ≠ stdRankOne D₇ b)
    (hnc : ¬ Commutes (stdRankOne D₇ a) (stdRankOne D₇ b)) :
    iform a b = 1 ∨ iform a b = -1 := by
  have hbd := abs_iform_le_two_E7 ha hb
  rw [abs_le] at hbd
  by_contra hne'
  have hcases : iform a b = -2 ∨ iform a b = 0 ∨ iform a b = 2 := by omega
  have hsq : iform a b = 2 ∨ iform a b = -2 → False := fun h2 => by
    rcases eq_or_neg_of_iform_eq_two ha hb h2 with rfl | rfl
    · exact hne rfl
    · exact hne (by rw [stdRankOne_neg])
  rcases hcases with h' | h' | h'
  · exact hsq (Or.inr h')
  · exact hnc (commutes_std3 ha hb h')
  · exact hsq (Or.inl h')


end Rel

section Step

theorem stage_step3 {X : Subgroup M₇}
    (hX : X ∈ Generic.fundamentalSubgroups .E7 D₇)
    (hθX : InvComm (stdRankOne D₇ thetaE7) X)
    (hcomm : Commutes (stdRankOne D₇ (Pi.single (e7Idx 0) 1)) X)
    {J : Set (Fin (Tag.rank .E7))} (hJ : J ⊆ Jsign) {l : V7} {B : ℕ}
    (hlJ : ∀ j ∈ J, iform l (Pi.single j 1) = 0) (hB : ∀ σ ∈ rootFinset .E7, |iform l σ| ≤ B)
    (hker : ∀ σ ∈ rootFinset .E7, iform l σ = 0 → σ ∈ parabolicRoots .E7 J)
    (Zs : List V7) (hZr : ∀ z ∈ Zs, IsRoot .E7 z)
    (hZJ : ∀ z ∈ Zs, ∀ j ∈ J, Even (iform z (Pi.single j 1)))
    (hZX : ∀ z ∈ Zs, InvComm (stdRankOne D₇ z) X)
    (hLevi : ∀ y : ModGL .E7 (GaloisField 3 1), y ∈ adjointGroup .E7 (GaloisField 3 1) →
      y * rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : (GaloisField 3 1)ˣ)) =
        rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : (GaloisField 3 1)ˣ)) * y →
      (∀ A : SL2 (GaloisField 3 1),
        y * rootSL2 .E7 (GaloisField 3 1) (Pi.single (e7Idx 0) 1) A =
          rootSL2 .E7 (GaloisField 3 1) (Pi.single (e7Idx 0) 1) A * y) →
      (∀ z ∈ Zs, y * rootDiagUnit .E7 (thetaDiag z (-1 : (GaloisField 3 1)ˣ)) =
        rootDiagUnit .E7 (thetaDiag z (-1 : (GaloisField 3 1)ˣ)) * y) →
      baseChangeGL (algebraMap (GaloisField 3 1) (AlgebraicClosure (GaloisField 3 1))) y ∈
        parabolicLevi .E7 (AlgebraicClosure (GaloisField 3 1)) J) :
    ∃ x : M₇, conjSub x (stdRankOne D₇ thetaE7) = stdRankOne D₇ thetaE7 ∧
      conjSub x (stdRankOne D₇ (Pi.single (e7Idx 0) 1)) = stdRankOne D₇ (Pi.single (e7Idx 0) 1) ∧
      (∀ z ∈ Zs, conjSub x (stdRankOne D₇ z) = stdRankOne D₇ z) ∧
      ∃ γ : V7, IsRoot .E7 γ ∧ conjSub x X = stdRankOne D₇ γ := by
  have hF : ringChar (GaloisField 3 1) ≠ 2 := ringChar_galoisField_ne_two (by norm_num)
  have hodd : Odd (Nat.card (GaloisField 3 1)) := odd_gf3
  obtain ⟨hsingle, hRθF⟩ := e7_fund_class3
  have he0 : IsRoot .E7 (Pi.single (e7Idx 0) 1 : V7) := isRoot_single .E7 (e7Idx 0)
  have he0F := std_mem_fund3 he0
  obtain ⟨r₁, hr₁, hr₁2⟩ := exists_involution_fund3 hX
  obtain ⟨r₂, hr₂, hr₂2⟩ := exists_involution_std3 isRoot_thetaE7
  have hr₁₂ : r₂ * r₁ = r₁ * r₂ := hθX r₂ hr₂ hr₂2 r₁ hr₁ hr₁2
  have hεr₂ := εm_involution_std3 isRoot_thetaE7 hr₂ hr₂2
  obtain ⟨h, hh⟩ := hsingle _ hRθF X hX
  have hεr₁ := εm_involution_of_mem_fund3 (h := h) (by rw [← hh]; exact hr₁) hr₁2
  set y := εm (GaloisField 3 1) r₁ with hy
  have hr1sq : r₁ * r₁ = 1 := by rw [← sq]; exact hr₁2 ▸ pow_orderOf_eq_one r₁
  have hy2 : y * y = 1 := by
    rw [hy, ← map_mul, hr1sq, map_one]
  have hyd : y * rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : (GaloisField 3 1)ˣ)) =
      rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : (GaloisField 3 1)ˣ)) * y := by
    rw [← hεr₂, hy, ← map_mul, ← map_mul, hr₁₂.symm]
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
  have hyz : ∀ z ∈ Zs, y * rootDiagUnit .E7 (thetaDiag z (-1 : (GaloisField 3 1)ˣ)) =
      rootDiagUnit .E7 (thetaDiag z (-1 : (GaloisField 3 1)ˣ)) * y := by
    intro z hz
    obtain ⟨rz, hrz, hrz2⟩ := exists_involution_std3 (hZr z hz)
    have hcz : rz * r₁ = r₁ * rz := hZX z hz rz hrz hrz2 r₁ hr₁ hr₁2
    rw [← εm_involution_std3 (hZr z hz) hrz hrz2, hy, ← map_mul, ← map_mul, hcz.symm]
  have hyJ := hLevi y (εm_mem r₁) hyd hye hyz
  obtain ⟨δ, hδ, u, huG, hu, hucomm⟩ := exists_rational_levi_conj hodd hlJ hB hker
    (εm_mem r₁) (εm_mem h) hy2 hyJ hεr₁.symm
  obtain ⟨x, hx⟩ := εm_surjective huG
  have hfix : ∀ z : V7, IsRoot .E7 z → (∀ j ∈ J, Even (iform z (Pi.single j 1))) →
      conjSub x (stdRankOne D₇ z) = stdRankOne D₇ z := by
    intro z hz hzJ
    have hzF := std_mem_fund3 hz
    apply eq_of_map_εm_eq3 (conjSub_mem_fundamentalSubgroups hzF x) hzF
    have hwd : u * rootTorusSL2 .E7 (GaloisField 3 1) z (-1) =
        rootTorusSL2 .E7 (GaloisField 3 1) z (-1) * u := by
      rw [rootTorusSL2_eq_thetaDiag hz]
      exact hucomm _ (fun j hj => by simp [thetaDiag, (hzJ j hj).neg_one_zpow])
    rw [map_conjSub, hx, map_stdRankOne_εm hz,
      map_conj_rootRankOneGroup_of_commute_gen hF hodd hz huG hwd]
  have hθJ : ∀ j ∈ J, Even (iform thetaE7 (Pi.single j 1)) := fun j hj => by
    rw [(Jsign_thetaDiag_one j (hJ hj)).1]
    exact ⟨0, by simp⟩
  have he0J : ∀ j ∈ J, Even (iform (Pi.single (e7Idx 0) 1 : V7) (Pi.single j 1)) := fun j hj => by
    rw [(Jsign_thetaDiag_one j (hJ hj)).2]
    exact ⟨0, by simp⟩
  refine ⟨x, hfix _ isRoot_thetaE7 hθJ, hfix _ he0 he0J,
    fun z hz => hfix z (hZr z hz) (hZJ z hz), ?_⟩
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
  refine ⟨γ, hγr, ?_⟩
  have hγF := std_mem_fund3 hγr
  rw [hh, ← conjSub_mul]
  apply eq_of_map_εm_eq3 (conjSub_mem_fundamentalSubgroups hRθF _) hγF
  rw [map_conjSub, map_mul, hx, map_stdRankOne_εm isRoot_thetaE7, map_stdRankOne_εm hγr]
  exact hLγ


end Step

end CFSG.ClassicalInvolution.Q3.Q3W
