module

public import CFSG.ClassicalInvolution.Q3.Q3TY15
public import CFSG.ClassicalInvolution.RouteD.TWT9Class

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TY

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.LieType.Universal CFSG.LieType CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.RouteD.TWE.B6
  CFSG.ClassicalInvolution.RouteD.TWT9 CFSG.ClassicalInvolution.WeakCT
  CFSG.LieType.Universal.Spin.Twisted
open CFSG.ClassicalInvolution.RouteD.TWE.B4 (normalized_span eigen_planes_of_inverted
  mem_negSpace_iff' mem_posSpace_iff')
open CFSG.ClassicalInvolution.ModelFacts.OrthAut CFSG.LieType.Universal.Spin
open scoped MatrixGroups

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

section Class

local notation "𝔔" => quadMinus 4 (GaloisField 3 1) (Prod.fst (minusCoeffs 3 1))
  (Prod.snd (minusCoeffs 3 1))

local notation "𝔽" => GaloisField 3 1

local notation "𝕍" => Vm 4 (GaloisField 3 1)


theorem leaf_planes_td4_3 {𝓕 : Set (Subgroup (spinGroup 𝔔))}
    (cq : CentralQuot3 (spinAction 𝔔) 𝓕 (fundSet 𝔔) (scalars 𝔽 𝕍))
    {g₀ : 𝕍 ≃ₗ[𝔽] 𝕍} (hgO : g₀ ∈ TauCeti.QuadraticMap.orthogonalGroup 𝔔) (hg2 : g₀ * g₀ = 1)
    {RJ : Subgroup (spinGroup 𝔔)} (hRJ : RJ ∈ 𝓕)
    (hnormJ : ∀ l ∈ RJ.map (spinAction 𝔔), g₀ * l * g₀ ∈ RJ.map (spinAction 𝔔))
    {x₀ : spinGroup 𝔔} (hx₀J : x₀ ∈ RJ) (hx₀1 : x₀ ≠ 1) (hx₀p : x₀ ^ 3 = 1)
    (hx₀inv : ∀ v, g₀ (spinAction 𝔔 x₀ v) = (spinAction 𝔔 x₀).symm (g₀ v))
    {ε : 𝔽} (hε : ε = 1 ∨ ε = -1) :
    ∃ (FJ : OFrame 𝔔) (π' ρ' : HypPair 𝔔), RJ.map (spinAction 𝔔) = FJ.La.range ∧
      π'.Orth ρ' ∧ hypPlane π' ⊔ hypPlane ρ' = FJ.span ∧
      (∀ x ∈ hypPlane π', g₀ x = (-ε) • x) ∧ (∀ x ∈ hypPlane ρ', g₀ x = ε • x) := by
  classical
  have h2 : (2 : 𝔽) ≠ 0 := two_ne_zero_gf3
  have hodd : Odd (Nat.card 𝔽) := odd_gf3
  have : Invertible (2 : 𝔽) := invertibleOfNonzero h2
  have hirr := minusCoeffs_irr 3 1
  have hQ' : (polarBilin 𝔔).Nondegenerate :=
    nondegenerate_polarBilin_quadMinus_of_finite 4 𝔽 hirr
  obtain ⟨iJ, hiJ⟩ := cq.map_mem _ hRJ
  obtain ⟨FJ, hFJ, hiJe⟩ := hiJ
  have hJspan : ∀ x ∈ FJ.span, g₀ x ∈ FJ.span :=
    normalized_span hodd hgO hg2 FJ (by rw [← hFJ]; exact hnormJ)
  have hx₀mem : spinAction 𝔔 x₀ ∈ FJ.La.range := by
    rw [← hFJ]
    exact ⟨x₀, hx₀J, rfl⟩
  obtain ⟨A, hA⟩ := hx₀mem
  have hAp : A ^ 3 = 1 := by
    apply FJ.La_injective
    rw [map_pow, hA, ← map_pow, hx₀p, map_one, map_one]
  have hA1 : A ≠ 1 := by
    rintro rfl
    rw [map_one] at hA
    exact hx₀1 (cq.inj RJ hRJ x₀ hx₀J hA.symm)
  have hinv : ∀ v, g₀ (FJ.La A v) = (FJ.La A).symm (g₀ v) := by
    intro v
    rw [hA]
    exact hx₀inv v
  obtain ⟨π, ρ, hπρ, hsup, hgπ, hgρ⟩ := eigen_planes_of_inverted hodd hQ' (p := 3) hgO hg2 FJ
    hJspan hA1 hAp hinv
  rcases hε with rfl | rfl
  · exact ⟨FJ, π, ρ, hFJ, hπρ, hsup, fun x hx => by rw [hgπ x hx]; simp, fun x hx => by
      rw [hgρ x hx]; simp⟩
  · exact ⟨FJ, ρ, π, hFJ, hπρ.symm, by rw [sup_comm]; exact hsup, fun x hx => by
      rw [hgρ x hx]; simp, fun x hx => by rw [hgπ x hx]; simp⟩

theorem adapted_frame_td4_3 {𝓕 : Set (Subgroup (spinGroup 𝔔))}
    (cq : CentralQuot3 (spinAction 𝔔) 𝓕 (fundSet 𝔔) (scalars 𝔽 𝕍))
    {RJ : Subgroup (spinGroup 𝔔)} (hRJ : RJ ∈ 𝓕) {FJ : OFrame 𝔔}
    (hFJ : RJ.map (spinAction 𝔔) = FJ.La.range) {π' ρ' : HypPair 𝔔} (hπρ' : π'.Orth ρ')
    (hsup' : hypPlane π' ⊔ hypPlane ρ' = FJ.span) {g₀ : 𝕍 ≃ₗ[𝔽] 𝕍} {ε : 𝔽}
    (hperp : ∀ y, y ∈ π'.perp → g₀ y = ε • y) :
    ∃ x' : spinGroup 𝔔,
      RJ = ((rootSL2 (minusFrame 4 (minusCoeffs 3 1).1 (minusCoeffs 3 1).2).toHypFrame 0 1
        (by omega) (by omega) (by omega) true false).map (MulAut.conj x').toMonoidHom) ∧
      ∀ y, polar 𝔔 (spinAction 𝔔 x'
          ((minusFrame 4 (minusCoeffs 3 1).1 (minusCoeffs 3 1).2).toHypFrame.vec ⟨0, by omega⟩
            true)) y = 0 →
        polar 𝔔 (spinAction 𝔔 x'
          ((minusFrame 4 (minusCoeffs 3 1).1 (minusCoeffs 3 1).2).toHypFrame.vec ⟨0, by omega⟩
            false)) y = 0 →
        g₀ y = ε • y := by
  classical
  have h2 : (2 : 𝔽) ≠ 0 := two_ne_zero_gf3
  have hodd : Odd (Nat.card 𝔽) := odd_gf3
  have : Invertible (2 : 𝔽) := invertibleOfNonzero h2
  have hirr := minusCoeffs_irr 3 1
  have hQ : (quadMinus 4 𝔽 (minusCoeffs 3 1).1 (minusCoeffs 3 1).2).Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mp
      (nondegenerate_polarBilin_quadMinus_of_finite 4 𝔽 hirr)
  have hQ' : (polarBilin 𝔔).Nondegenerate :=
    nondegenerate_polarBilin_quadMinus_of_finite 4 𝔽 hirr
  have hdimV : 2 * 2 + 3 ≤ Module.finrank 𝔽 (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → 𝔽) := by
    rw [finrank_minus 3 1 4 (by omega)]
    omega
  set F₀ : HypFrame 𝔔 (4 - 1) := (minusFrame 4 (minusCoeffs 3 1).1 (minusCoeffs 3 1).2).toHypFrame
    with hF₀
  have hspanG : FJ.span = (mkFrame π' ρ' hπρ').span := by
    rw [frame_span_eq (mkFrame π' ρ' hπρ')]
    exact hsup'.symm
  have hii : FJ.La (-1) = (mkFrame π' ρ' hπρ').La (-1) :=
    Frame.La_neg_one_eq_of_span_eq hspanG
  obtain ⟨P1, hP1o, hP1pl, hFJP1⟩ : ∃ (P1 : HypPair 𝔔) (h : π'.Orth (swapPair P1)),
      hypPlane P1 = hypPlane ρ' ∧ FJ.La.range = (mkFrame π' (swapPair P1) h).La.range := by
    rcases Frame.La_range_eq_or_eq_swap h2 hii with hA | hB
    · exact ⟨swapPair ρ', hπρ', by rw [hypPlane_swapPair], hA⟩
    · exact ⟨ρ', orth_swapPair hπρ', rfl, hB⟩
  have o01 : π'.Orth P1 := orth_swapPair hP1o
  let p₀ : ℕ → HypPair 𝔔 := fun k => if k = 0 then π' else P1
  have ho₀ : ∀ a b, a < 2 → b < 2 → a ≠ b → (p₀ a).Orth (p₀ b) := by
    intro a b ha hb hab
    interval_cases a <;> interval_cases b <;>
      first
      | exact absurd rfl hab
      | simp [p₀, o01, o01.symm]
  obtain ⟨Q3, hQ3⟩ := exists_pair_perp_fam hodd hQ' p₀ 2 ho₀ hdimV
  have o02 : π'.Orth Q3 := by simpa [p₀] using hQ3 0 (by omega)
  have o12 : P1.Orth Q3 := by simpa [p₀] using hQ3 1 (by omega)
  let Pn : ℕ → HypPair 𝔔 := fun k => if k = 0 then π' else if k = 1 then P1 else Q3
  have hPn : ∀ a b, a < 3 → b < 3 → a ≠ b → (Pn a).Orth (Pn b) := by
    intro a b ha hb hab
    interval_cases a <;> interval_cases b <;>
      first
      | exact absurd rfl hab
      | simp [Pn, o01, o01.symm, o02, o02.symm, o12, o12.symm]
  let P : Fin (4 - 1) → HypPair 𝔔 := fun i => Pn i.val
  have hPo : ∀ i j : Fin (4 - 1), i ≠ j → (P i).Orth (P j) := fun i j hij =>
    hPn i.val j.val i.isLt j.isLt (fun h => hij (Fin.ext h))
  obtain ⟨x', hx1, -⟩ := exists_spin_family hodd hQ F₀ hPo (⟨2, by omega⟩ : Fin (4 - 1))
  have hP0 : π'.e = spinAction 𝔔 x' (F₀.vec ⟨0, by omega⟩ true) ∧
      π'.f = spinAction 𝔔 x' (F₀.vec ⟨0, by omega⟩ false) := by
    have := hx1 ⟨0, by omega⟩ (fun h => by have := congrArg Fin.val h; simp at this)
    have e : P ⟨0, by omega⟩ = π' := by simp [P, Pn]
    rw [e] at this
    exact this
  have hP1 : P1.e = spinAction 𝔔 x' (F₀.vec ⟨1, by omega⟩ true) ∧
      P1.f = spinAction 𝔔 x' (F₀.vec ⟨1, by omega⟩ false) := by
    have := hx1 ⟨1, by omega⟩ (fun h => by have := congrArg Fin.val h; simp at this)
    have e : P ⟨1, by omega⟩ = P1 := by simp [P, Pn]
    rw [e] at this
    exact this
  have hrange := La_range_eq_of_pairs F₀ (a := 0) (b := 1) (by omega) (by omega) (by omega) true
    false x' hP1o hP0 ⟨hP1.2, hP1.1⟩
  refine ⟨x', cq.map_inj hRJ (cq.rootSL2_conj_mem F₀ _ _ _ true false x')
    (by rw [hFJ, hFJP1, hrange]), fun y h1 h2' => hperp y ?_⟩
  rw [← hP0.1] at h1
  rw [← hP0.2] at h2'
  exact HypPair.mem_perp.mpr ⟨h1, h2'⟩


theorem class_spin_td4a_3 {𝓕 : Set (Subgroup (spinGroup 𝔔))}
    (cq : CentralQuot3 (spinAction 𝔔) 𝓕 (fundSet 𝔔) (scalars 𝔽 𝕍))
    {g₀ h : 𝕍 ≃ₗ[𝔽] 𝕍} (hgO : g₀ ∈ TauCeti.QuadraticMap.orthogonalGroup 𝔔) (hg2 : g₀ * g₀ = 1)
    (hhO : h ∈ TauCeti.QuadraticMap.orthogonalGroup 𝔔) (hh2 : h * h = 1)
    {RM RJ RN : Subgroup (spinGroup 𝔔)} (hRJ : RJ ∈ 𝓕) (hRN : RN ∈ 𝓕)
    (FM : OFrame 𝔔) (hFM : RM.map (spinAction 𝔔) = FM.La.range)
    (hfixM : ∀ l ∈ RM.map (spinAction 𝔔), g₀ * l = l * g₀)
    (hfixN : ∀ l ∈ RN.map (spinAction 𝔔), g₀ * l = l * g₀)
    (hnormJ : ∀ l ∈ RJ.map (spinAction 𝔔), g₀ * l * g₀ ∈ RJ.map (spinAction 𝔔))
    {x₀ : spinGroup 𝔔} (hx₀J : x₀ ∈ RJ) (hx₀1 : x₀ ≠ 1) (hx₀p : x₀ ^ 3 = 1)
    (hx₀inv : ∀ v, g₀ (spinAction 𝔔 x₀ v) = (spinAction 𝔔 x₀).symm (g₀ v))
    (hhneg : negSpace h ≤ FM.span) (hhdim : Module.finrank 𝔽 (negSpace h) = 2)
    (hJh : ∀ l ∈ RJ.map (spinAction 𝔔), h * l = l * h)
    (hNh : ∀ l ∈ RN.map (spinAction 𝔔), h * l = l * h)
    (haniso : ∀ y ∈ FM.span, h y = y → y ≠ 0 → 𝔔 y ≠ 0) :
    ∃ (x' : spinGroup 𝔔) (ε : 𝔽), (ε = 1 ∨ ε = -1) ∧
      RJ = ((rootSL2 (minusFrame 4 (minusCoeffs 3 1).1 (minusCoeffs 3 1).2).toHypFrame 0 1
        (by omega) (by omega) (by omega) true false).map (MulAut.conj x').toMonoidHom) ∧
      ∀ y, polar 𝔔 (spinAction 𝔔 x'
          ((minusFrame 4 (minusCoeffs 3 1).1 (minusCoeffs 3 1).2).toHypFrame.vec ⟨0, by omega⟩
            true)) y = 0 →
        polar 𝔔 (spinAction 𝔔 x'
          ((minusFrame 4 (minusCoeffs 3 1).1 (minusCoeffs 3 1).2).toHypFrame.vec ⟨0, by omega⟩
            false)) y = 0 →
        g₀ y = ε • y := by
  classical
  have h2 : (2 : 𝔽) ≠ 0 := two_ne_zero_gf3
  have hodd : Odd (Nat.card 𝔽) := odd_gf3
  have : Invertible (2 : 𝔽) := invertibleOfNonzero h2
  have hdim8 : Module.finrank 𝔽 𝕍 = 8 := by
    rw [finrank_minus 3 1 4 (by omega)]
  have hiMf : IsFundamental 𝔔 (RM.map (spinAction 𝔔)) (FM.La (-1)) := by
    rw [hFM]
    exact IsFundamental.of_frame FM
  obtain ⟨εM, hεM, hgM⟩ := sign_of_commute h2 hiMf hgO hg2 hfixM
  have hgM' : ∀ x ∈ FM.span, g₀ x = εM • x := fun x hx =>
    hgM x (by rw [negSpace_La_neg_one h2]; exact hx)
  obtain ⟨FJ, π', ρ', hFJ, hπρ', hsup', hgπ', hgρ'⟩ := leaf_planes_td4_3 cq hgO hg2 hRJ
    hnormJ hx₀J hx₀1 hx₀p hx₀inv hεM
  have hiJf : IsFundamental 𝔔 (RJ.map (spinAction 𝔔)) (FJ.La (-1)) := by
    rw [hFJ]
    exact IsFundamental.of_frame FJ
  have hJspan : ∀ x ∈ FJ.span, h x = x := fun x hx =>
    isometry_fixes_of_commute hodd hhO hh2 hhdim hiJf hJh x
      (by rw [negSpace_La_neg_one h2]; exact hx)
  have hρ'h : ∀ x ∈ hypPlane ρ', h x = x := fun x hx =>
    hJspan x (by rw [← hsup']; exact Submodule.mem_sup_right hx)
  obtain ⟨s, hs⟩ := cq.map_mem _ hRN
  obtain ⟨εN, hεN, hgN⟩ := sign_of_commute h2 hs hgO hg2 hfixN
  have hperp := eq_smul_of_perp_td4a h2 hdim8 hgO hg2 hh2 FM.finrank_span hεM hgM' hhneg hhdim
    π' ρ' hgπ' hgρ' hρ'h (finrank_negSpace hodd hs) hεN hgN
    (isometry_fixes_of_commute hodd hhO hh2 hhdim hs hNh) haniso
  obtain ⟨x', hx'RJ, hx'⟩ := adapted_frame_td4_3 cq hRJ hFJ hπρ' hsup' hperp
  exact ⟨x', εM, hεM, hx'RJ, hx'⟩


end Class

end CFSG.ClassicalInvolution.Q3.Q3TY
