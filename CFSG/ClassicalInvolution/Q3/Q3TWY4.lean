module

public import CFSG.ClassicalInvolution.Q3.Q3TWY3
public import CFSG.ClassicalInvolution.RouteD.TWEB3PClass

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TWY

open CFSG.Open hiding StatedLieTag StatedLieAdmissible StatedSp
open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.RouteD.TWE.B6
  CFSG.ClassicalInvolution.RouteD.TWE.B4 CFSG.ClassicalInvolution.Q3.Q3W
open CFSG.ClassicalInvolution.RouteD.TWE.B3 (class_b3_model_sign)
open CFSG.ClassicalInvolution.ModelFacts.Orth15 (polarNondegOn_sup)
open CFSG.ClassicalInvolution.ModelFacts.OrthAut CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.WeakCT CFSG.LieType.Universal.Spin CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

local notation "𝔽₃" => GaloisField 3 1

theorem nsq_gf3 : ∀ c : 𝔽₃, c * c ≠ -1 := by
  intro c hc
  let _ : Fintype 𝔽₃ := Fintype.ofFinite _
  have hsq : IsSquare (-1 : 𝔽₃) := ⟨c, hc.symm⟩
  apply (FiniteField.isSquare_neg_one_iff (F := 𝔽₃)).mp hsq
  rw [← Nat.card_eq_fintype_card, card_gf3]


section Spin

theorem class_spin_b3_3
    {𝓕 : Set (Subgroup (spinGroup (quadOdd 3 𝔽₃)))}
    (cq : CentralQuot3 (spinAction (quadOdd 3 𝔽₃)) 𝓕 (fundSet (quadOdd 3 𝔽₃))
      (scalars 𝔽₃ (Fin 3 ⊕ Fin 3 ⊕ Unit → 𝔽₃)))
    {g₀ u J₁ : (Fin 3 ⊕ Fin 3 ⊕ Unit → 𝔽₃) ≃ₗ[𝔽₃] (Fin 3 ⊕ Fin 3 ⊕ Unit → 𝔽₃)}
    (hgO : g₀ ∈ TauCeti.QuadraticMap.orthogonalGroup (quadOdd 3 𝔽₃))
    (hg2 : g₀ * g₀ = 1)
    (huO : u ∈ TauCeti.QuadraticMap.orthogonalGroup (quadOdd 3 𝔽₃))
    (hu2 : u * u = 1)
    (hJ₁O : J₁ ∈ TauCeti.QuadraticMap.orthogonalGroup (quadOdd 3 𝔽₃))
    {RM RN : Subgroup (spinGroup (quadOdd 3 𝔽₃))}
    (hRN : RN ∈ 𝓕)
    (FM : OFrame (quadOdd 3 𝔽₃))
    (hFM : RM.map (spinAction (quadOdd 3 𝔽₃)) = FM.La.range)
    (hfixM : ∀ l ∈ RM.map (spinAction (quadOdd 3 𝔽₃)), g₀ * l = l * g₀)
    (hnormN : ∀ l ∈ RN.map (spinAction (quadOdd 3 𝔽₃)),
      g₀ * l * g₀ ∈ RN.map (spinAction (quadOdd 3 𝔽₃)))
    {x₀ : spinGroup (quadOdd 3 𝔽₃)} (hx₀N : x₀ ∈ RN) (hx₀1 : x₀ ≠ 1)
    (hx₀p : x₀ ^ 3 = 1)
    (hx₀inv : ∀ v, g₀ (spinAction (quadOdd 3 𝔽₃) x₀ v) =
      (spinAction (quadOdd 3 𝔽₃) x₀).symm (g₀ v))
    (hunegle : negSpace u ≤ FM.span) (hudim : Module.finrank 𝔽₃ (negSpace u) = 2)
    (huN : ∀ l ∈ RN.map (spinAction (quadOdd 3 𝔽₃)), u * l = l * u)
    (hJ₁span : ∀ y ∈ FM.span, J₁ y ∈ FM.span) (hJ₁sq : ∀ y ∈ FM.span, J₁ (J₁ y) = -y)
    (hJ₁comm : ∀ y, u (J₁ y) = J₁ (u y)) :
    ∃ (x' : spinGroup (quadOdd 3 𝔽₃)) (ε : 𝔽₃),
      (ε = 1 ∨ ε = -1) ∧
      RN = ((rootSL2 (oddFrame 3 𝔽₃).toHypFrame 0 1 (by omega) (by omega)
        (by omega) true false).map (MulAut.conj x').toMonoidHom) ∧
      ∀ y, polar (quadOdd 3 𝔽₃) (spinAction (quadOdd 3 𝔽₃) x'
          ((oddFrame 3 𝔽₃).toHypFrame.vec ⟨0, by omega⟩ true)) y = 0 →
        polar (quadOdd 3 𝔽₃) (spinAction (quadOdd 3 𝔽₃) x'
          ((oddFrame 3 𝔽₃).toHypFrame.vec ⟨0, by omega⟩ false)) y = 0 →
        g₀ y = ε • y := by
  classical
  have h2 : (2 : 𝔽₃) ≠ 0 := two_ne_zero_gf3
  have hodd : Odd (Nat.card 𝔽₃) := odd_gf3
  have : Invertible (2 : 𝔽₃) := invertibleOfNonzero h2
  have hQ : (quadOdd 3 𝔽₃).Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mp (nondegenerate_polarBilin_quadOdd 3 _ h2)
  have hQ' : (polarBilin (quadOdd 3 𝔽₃)).Nondegenerate :=
    nondegenerate_polarBilin_quadOdd 3 _ h2
  have hdim7 : Module.finrank 𝔽₃ (Fin 3 ⊕ Fin 3 ⊕ Unit → 𝔽₃) = 7 := by
    rw [finrank_odd]
  obtain ⟨iN, hiN⟩ := cq.map_mem _ hRN
  obtain ⟨FN, hFN, hiNe⟩ := hiN
  have hiMf : IsFundamental (quadOdd 3 𝔽₃) (RM.map (spinAction (quadOdd 3 𝔽₃)))
      (FM.La (-1)) := by
    rw [hFM]
    exact IsFundamental.of_frame FM
  have hiNf : IsFundamental (quadOdd 3 𝔽₃) (RN.map (spinAction (quadOdd 3 𝔽₃)))
      (FN.La (-1)) := by
    rw [hFN]
    exact IsFundamental.of_frame FN
  obtain ⟨εM, hεM, hgM⟩ := sign_of_commute h2 hiMf hgO hg2 hfixM
  have hgM' : ∀ x ∈ FM.span, g₀ x = εM • x := fun x hx =>
    hgM x (by rw [negSpace_La_neg_one h2]; exact hx)
  have hNspan : ∀ x ∈ FN.span, g₀ x ∈ FN.span :=
    normalized_span hodd hgO hg2 FN (by rw [← hFN]; exact hnormN)
  have hx₀mem : spinAction (quadOdd 3 𝔽₃) x₀ ∈ FN.La.range := by
    rw [← hFN]
    exact ⟨x₀, hx₀N, rfl⟩
  obtain ⟨A, hA⟩ := hx₀mem
  have hAp : A ^ 3 = 1 := by
    apply FN.La_injective
    rw [map_pow, hA, ← map_pow, hx₀p, map_one, map_one]
  have hA1 : A ≠ 1 := by
    rintro rfl
    rw [map_one] at hA
    exact hx₀1 (cq.inj RN hRN x₀ hx₀N hA.symm)
  have hinv : ∀ v, g₀ (FN.La A v) = (FN.La A).symm (g₀ v) := by
    intro v
    rw [hA]
    exact hx₀inv v
  have hu_ne : ∃ x ∈ FM.span, u x ≠ x := by
    obtain ⟨⟨x, hx⟩, hx0⟩ := Module.finrank_pos_iff_exists_ne_zero.mp
      (by omega : 0 < Module.finrank 𝔽₃ (negSpace u))
    have hx0' : x ≠ 0 := fun h => hx0 (Subtype.ext h)
    refine ⟨x, hunegle hx, fun h => hx0' ?_⟩
    have hneg := mem_negSpace_iff'.mp hx
    have h22 : (2 : 𝔽₃) • x = 0 := by
      rw [two_smul]
      nth_rewrite 1 [← h]
      rw [hneg, neg_add_cancel]
    exact (smul_eq_zero.mp h22).resolve_left h2
  have huN' : ∀ x ∈ FN.span, u x = x := by
    obtain ⟨ε', hε', he⟩ := sign_of_commute h2 hiNf huO hu2 huN
    rcases hε' with rfl | rfl
    · intro x hx
      simpa using he x (by rw [negSpace_La_neg_one h2]; exact hx)
    · exfalso
      have hle : FN.span ≤ negSpace u := fun x hx =>
        mem_negSpace_iff'.mpr (by
          rw [he x (by rw [negSpace_La_neg_one h2]; exact hx)]; simp)
      have h4 := Submodule.finrank_mono hle
      rw [FN.finrank_span, hudim] at h4
      omega
  obtain ⟨π, ρ, hπρ, hsup, hperp⟩ := class_b3_model_sign (p := 3) hodd hQ' nsq_gf3 hdim7 hgO hg2
    hJ₁O FM FN hεM hgM' hJ₁span hJ₁sq hJ₁comm hu_ne huN' hNspan hA1 hAp hinv
  set F₀ := (oddFrame 3 𝔽₃).toHypFrame with hF₀
  have hspanG : FN.span = (mkFrame π ρ hπρ).span := by
    rw [frame_span_eq (mkFrame π ρ hπρ)]
    exact hsup.symm
  have hii : FN.La (-1) = (mkFrame π ρ hπρ).La (-1) :=
    Frame.La_neg_one_eq_of_span_eq hspanG
  obtain ⟨P1, hP1o, hP1pl, hFNP1⟩ : ∃ (P1 : HypPair (quadOdd 3 𝔽₃))
      (h : π.Orth (swapPair P1)), hypPlane P1 = hypPlane ρ ∧
      FN.La.range = (mkFrame π (swapPair P1) h).La.range := by
    rcases Frame.La_range_eq_or_eq_swap h2 hii with hA | hB
    · exact ⟨swapPair ρ, hπρ, by rw [hypPlane_swapPair], hA⟩
    · exact ⟨ρ, orth_swapPair hπρ, rfl, hB⟩
  have o01 : π.Orth P1 := orth_swapPair hP1o
  let p₀ : ℕ → HypPair (quadOdd 3 𝔽₃) := fun k => if k = 0 then π else P1
  have ho₀ : ∀ a b, a < 2 → b < 2 → a ≠ b → (p₀ a).Orth (p₀ b) := by
    intro a b ha hb hab
    interval_cases a <;> interval_cases b <;> simp_all [p₀, o01.symm]
  obtain ⟨p', hp', ho'⟩ := exists_orth_ext hodd hQ' p₀ 2 ho₀ 1 (by omega)
  have hp'0 : p' 0 = π := by rw [hp' 0 (by omega)]; simp [p₀]
  have hp'1 : p' 1 = P1 := by rw [hp' 1 (by omega)]; simp [p₀]
  have o02 : π.Orth (p' 2) := by
    rw [← hp'0]; exact ho' 0 2 (by omega) (by omega) (by omega)
  have o12 : P1.Orth (p' 2) := by
    rw [← hp'1]; exact ho' 1 2 (by omega) (by omega) (by omega)
  let Pn : ℕ → HypPair (quadOdd 3 𝔽₃) := fun k =>
    if k = 0 then π else if k = 1 then P1 else p' 2
  have hPn : ∀ a b, a < 3 → b < 3 → a ≠ b → (Pn a).Orth (Pn b) := by
    intro a b ha hb hab
    interval_cases a <;> interval_cases b <;>
      first
      | exact absurd rfl hab
      | simp [Pn, o01, o01.symm, o02, o02.symm, o12, o12.symm]
  let P : Fin 3 → HypPair (quadOdd 3 𝔽₃) := fun i => Pn i.val
  have hPo : ∀ i j : Fin 3, i ≠ j → (P i).Orth (P j) := fun i j hij =>
    hPn i.val j.val i.isLt j.isLt (fun h => hij (Fin.ext h))
  obtain ⟨x', hx1, -⟩ := exists_spin_family hodd hQ F₀ hPo (⟨2, by omega⟩ : Fin 3)
  have hP0 : π.e = spinAction (quadOdd 3 𝔽₃) x' (F₀.vec ⟨0, by omega⟩ true) ∧
      π.f = spinAction (quadOdd 3 𝔽₃) x' (F₀.vec ⟨0, by omega⟩ false) := by
    have := hx1 ⟨0, by omega⟩ (fun h => by have := congrArg Fin.val h; simp at this)
    have e : P ⟨0, by omega⟩ = π := by simp [P, Pn]
    rw [e] at this
    exact this
  have hP1 : P1.e = spinAction (quadOdd 3 𝔽₃) x' (F₀.vec ⟨1, by omega⟩ true) ∧
      P1.f = spinAction (quadOdd 3 𝔽₃) x' (F₀.vec ⟨1, by omega⟩ false) := by
    have := hx1 ⟨1, by omega⟩ (fun h => by have := congrArg Fin.val h; simp at this)
    have e : P ⟨1, by omega⟩ = P1 := by simp [P, Pn]
    rw [e] at this
    exact this
  have hrange := La_range_eq_of_pairs F₀ (a := 0) (b := 1) (by omega) (by omega) (by omega) true
    false x' hP1o hP0 ⟨hP1.2, hP1.1⟩
  have hRNeq : RN = ((rootSL2 F₀ 0 1 (by omega) (by omega) (by omega) true false).map
      (MulAut.conj x').toMonoidHom) :=
    cq.map_inj hRN (cq.rootSL2_conj_mem F₀ _ _ _ true false x')
      (by rw [hFN, hFNP1, hrange])
  refine ⟨x', εM, hεM, hRNeq, fun y h1 h2' => hperp y ?_⟩
  rw [← hP0.1] at h1
  rw [← hP0.2] at h2'
  exact HypPair.mem_perp.mpr ⟨h1, h2'⟩

end Spin

end CFSG.ClassicalInvolution.Q3.Q3TWY
