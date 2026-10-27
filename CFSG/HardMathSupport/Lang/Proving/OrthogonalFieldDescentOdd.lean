module

public import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescentCore
public import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescentDisplayed
public import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescentTags

public section

namespace CFSG.HardMathSupport.Lang.Proving

open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCOrthogonalDescent TensorProduct Matrix Module
  CFSG.GroupTheory.SteinbergBK CFSG.Blueprint.EvenSource CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBHigherLinearField
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter CFSG.RankThree.Classical.SteinbergBY

variable {K : Type} [Field K] {d : ℕ}

theorem descent_core_aux' {ℓ f p : ℕ} [Finite K] (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Nat.card K = ℓ ^ f) (hd : 0 < d) (Q : QuadraticForm K (Fin d → K))
    (hnd : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hS3 : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hgates : OrthogonalGates Q f) (a : MulAut (matrixProjectiveDerived Q))
    (haD : a ∉ (linearConjugationHom Q).range) (hap : orderOf a = p) (g : similarityPairs Q)
    (hg : matrixProjectiveConjugationHom Q g = a) :
    p ∣ f ∧ orderOf g.val.right = p ∧
      Nat.card (semilinearFixedSubfield g.val.right) = ℓ ^ (f / p) ∧
      ∃ (U : similarityPairs Q) (c : Kˣ)
        (Q₀ : QuadraticForm (fixedField U.val) (fixedSpace U.val)),
        matrixProjectiveConjugationHom Q U = a ∧ U.val.right = g.val.right ∧
        FixedFormDescent p Q U c Q₀ ∧ Nonempty (DescentSplitting Q U c Q₀) := by
  classical
  obtain ⟨hker, ⟨ψ, hψg, hψker, -⟩, -⟩ := hgates
  have ha : a ∈ matrixProjectiveImage Q := ⟨g, hg⟩
  have hψa : ψ ⟨a, ha⟩ = g.val.right := by
    rw [← hψg g]
    congr 1
    exact Subtype.ext hg.symm
  have happ : a ^ p = 1 := by
    rw [← hap]
    exact pow_orderOf_eq_one a
  have hσp : g.val.right ^ p = 1 := by
    rw [← hψa, ← map_pow]
    have h1 : (⟨a, ha⟩ : matrixProjectiveImage Q) ^ p = 1 := Subtype.ext happ
    rw [h1, map_one]
  have hσne : g.val.right ≠ 1 := by
    intro h1
    apply haD
    have h2 : (⟨a, ha⟩ : matrixProjectiveImage Q) ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, hψa, h1]
    rw [hψker] at h2
    exact h2
  have hσord : orderOf g.val.right = p := by
    rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one hσp) with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hσne
    · exact h
  have hκ : matrixProjectiveConjugationHom Q (g ^ p) = 1 := by rw [map_pow, hg, happ]
  obtain ⟨-, b, hb⟩ := (hker (g ^ p)).mp hκ
  have hb' : (g.val ^ p).left = sc b := hb
  obtain ⟨U, hUr, hUp, hUκ⟩ := exists_normalized_pair Q hd g hσord hb'
  have hσ : orderOf U.val.right = p := by rw [hUr]; exact hσord
  have hap' : ∀ v, (⇑(coordinateSemilinearMap U.val))^[p] v = v := fun v => by
    rw [iterate_coordinateSemilinearMap, hUp, coordinateSemilinearMap_one]
  have hQa : ∀ v, Q (coordinateSemilinearMap U.val v) =
      (multiplier Q U : K) * U.val.right (Q v) := fun v => multiplier_spec Q U v
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  obtain ⟨hdvd, hcard, c, Q₀, hQ₀, hnd₀, hfr, Φ, hΦ1, hΦ2⟩ :=
    exists_descent hℓ hf hK U.val.right hσ (coordinateSemilinearMap U.val)
      (coordinateSemilinearMap_smul U.val) hap' Q hnd (multiplier Q U : K) hQa
  have hfr' : finrank (fixedField U.val) (fixedSpace U.val) = d := hfr.trans (by simp)
  have : Finite (fixedField U.val) := inferInstance
  have : FiniteDimensional (fixedField U.val) (fixedSpace U.val) := Module.Finite.of_finite
  have : FiniteDimensional (fixedField U.val) K := Module.Finite.of_finite
  obtain ⟨m, δ, hδ, ⟨H⟩⟩ := exists_regular_split Q₀ hnd₀
  let ι : fixedSpace U.val →+ (Fin d → K) := (fixedSpace U.val).subtype.toAddMonoidHom
  have hι : ∀ w, ((c : K) • Q) (ι w) = algebraMap (fixedField U.val) K (Q₀ w) := by
    intro w
    have h1 := hQ₀ w
    change (c : K) * Q (w : Fin d → K) = ((Q₀ w : fixedField U.val) : K)
    exact h1.symm
  have hodd : Odd (finrank (fixedField U.val) K) := by
    rw [finrank_fixedField_eq hℓ hf U.val.right hK hcard hdvd]
    exact hp.odd_of_ne_two hp2
  let bK : Basis (Fin m ⊕ Fin m ⊕ Fin δ) K (Fin d → K) := (H.b.baseChange K).map Φ
  have hbK : ∀ a, bK a = ι (H.b a) := by
    intro a
    show Φ ((H.b.baseChange K) a) = _
    rw [Basis.baseChange_apply, hΦ1, one_smul]
    rfl
  let HK : HypSplit ((c : K) • Q) m δ := H.extend ι hι hδ hodd bK hbK
  have hndR := polarBilin_smul_nondegenerate Q hnd c
  have hw₀ : sourceWittIndex ⇑Q₀ = m := H.sourceWittIndex_eq hnd₀
  have hw₁ : sourceWittIndex ⇑((c : K) • Q) = m := HK.sourceWittIndex_eq hndR
  have hw₂ : sourceWittIndex ⇑Q = m := by
    rw [← sourceWittIndex_smul Q c]
    exact hw₁
  have hdim : 2 * m + δ = d := H.finrank_eq.symm.trans hfr'
  have hm3 : 3 ≤ m := by
    obtain ⟨T, hT3, hT⟩ := hS3
    have h3 := le_sourceWittIndex (K := K) (V := Fin d → K) (⇑Q) hT
    omega
  refine ⟨hdvd, hσord, ?_, U, c, Q₀, hUκ.trans hg, hUr, ⟨hUp, hQ₀, hnd₀, ⟨Φ, hΦ1, hΦ2, ?_⟩, hfr',
    hw₀.trans hw₂.symm, H.exists_totallySingular_three hm3⟩,
    ⟨⟨m, δ, hδ, H, HK, fun a => hbK a, hdim, hw₂⟩⟩⟩
  · rw [← hUr]
    exact hcard
  · intro x y w w'
    have hpol : ((QuadraticMap.polar Q₀ w w' : fixedField U.val) : K) =
        c * QuadraticMap.polar Q (w : Fin d → K) (w' : Fin d → K) := by
      simp only [QuadraticMap.polar, Subfield.coe_sub, hQ₀, Submodule.coe_add]
      ring
    rw [hΦ1, hΦ1]
    refine ⟨?_, ?_⟩
    · rw [CFSG.ClassicalGroups.Orthogonal.map_smul_eq_sq, hQ₀]
      ring
    · rw [CFSG.ClassicalGroups.Orthogonal.polar_smul_left_eq,
        CFSG.ClassicalGroups.Orthogonal.polar_smul_right_eq, hpol]
      ring

theorem orthogonal_prime_semilinear_actual_fixed_form_descent' (G : Type) [Group G]
    (c : StatedLieTag) (hc : c = .POmegaOdd ∨ c = .POmegaPlus ∨ c = .POmegaMinus)
    (n ℓ f p : ℕ) (h : StatedClassicalModel G c n ℓ f) :
    p.Prime → p ≠ 2 →
    match c with
    | .POmegaOdd => ∀ (K : Type) [Field K] [Finite K], Nat.card K = ℓ ^ f →
        G ≃* StatedProj (StatedOmega (StatedQuadOdd n K)) →
          ∀ a ∈ matrixProjectiveImage (coordinateQuadOdd n K),
            a ∉ (linearConjugationHom (coordinateQuadOdd n K)).range → orderOf a = p →
              OrthogonalFieldDescent ℓ f p (coordinateQuadOdd n K)
                (fun U Q₀ => OddFieldDescent n ℓ f p (coordinateQuadOdd n K) U Q₀) a
    | .POmegaPlus => ∀ (K : Type) [Field K] [Finite K], Nat.card K = ℓ ^ f →
        G ≃* StatedProj (StatedOmega (StatedQuadPlus n K)) →
          ∀ a ∈ matrixProjectiveImage (coordinateQuadPlus n K),
            a ∉ (linearConjugationHom (coordinateQuadPlus n K)).range → orderOf a = p →
              OrthogonalFieldDescent ℓ f p (coordinateQuadPlus n K)
                (fun U Q₀ => PlusFieldDescent n ℓ f p (coordinateQuadPlus n K) U Q₀) a
    | .POmegaMinus => ∀ (hn : 1 ≤ n) (K : Type) [Field K] [Finite K], Nat.card K = ℓ ^ f →
        ∀ b c : K, (∀ s : K, s ^ 2 + b * s + c ≠ 0) →
        G ≃* StatedProj (StatedOmega (StatedQuadMinus n K b c)) →
          ∀ a ∈ matrixProjectiveImage (coordinateQuadMinus n K hn b c),
            a ∉ (linearConjugationHom (coordinateQuadMinus n K hn b c)).range → orderOf a = p →
              OrthogonalFieldDescent ℓ f p (coordinateQuadMinus n K hn b c)
                (fun U Q₀ => MinusFieldDescent n ℓ f p hn (coordinateQuadMinus n K hn b c) U Q₀) a
    | _ => False := by
  intro hp hp2
  rcases hc with rfl | rfl | rfl
  ·
    intro K _ _ hK e a ha haD hap
    obtain ⟨hℓ, hf, hn3, hℓ2⟩ := h.1
    obtain ⟨-, hnd, hS3, -⟩ := coordinate_model_witness_odd h K hK e
    have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates G .POmegaOdd
      (Or.inl rfl) n ℓ f h K hK e
    have hd : 0 < 2 * n + 1 := by omega
    obtain ⟨g₀, hg₀⟩ := ha
    refine ⟨(descent_core_aux' hℓ hf hp hp2 hK hd _ hnd hS3 hgates a haD hap g₀ hg₀).1, ?_⟩
    rintro σ ⟨g, hg, rfl⟩
    obtain ⟨hdvd, hord, hcard, U, cc, Q₀, hUκ, hUr, hFFD, ⟨ds⟩⟩ :=
      descent_core_aux' hℓ hf hp hp2 hK hd _ hnd hS3 hgates a haD hap g hg
    refine ⟨hord, hcard, U, cc, Q₀, hUκ, hUr, hFFD, ?_⟩
    have hfp : 1 ≤ f / p := Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) hp.pos
    have hcard' : Nat.card (fixedField U.val) = ℓ ^ (f / p) := by
      rw [← hUr] at hcard
      exact hcard
    obtain ⟨m, δ, hδ, H, HK, hbK, hdim, hw⟩ := ds
    obtain ⟨rfl, rfl⟩ : m = n ∧ δ = 1 := by omega
    exact odd_field_descent hFFD.2.1 ⟨hℓ, hfp, hn3, hℓ2⟩ hcard' H HK hbK
  ·
    intro K _ _ hK e a ha haD hap
    obtain ⟨hℓ, hf, hn4⟩ := h.1
    obtain ⟨-, hnd, hS3, -⟩ := coordinate_model_witness_plus h K hK e
    have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates G .POmegaPlus
      (Or.inr (Or.inl rfl)) n ℓ f h K hK e
    have hd : 0 < 2 * n := by omega
    obtain ⟨g₀, hg₀⟩ := ha
    refine ⟨(descent_core_aux' hℓ hf hp hp2 hK hd _ hnd hS3 hgates a haD hap g₀ hg₀).1, ?_⟩
    rintro σ ⟨g, hg, rfl⟩
    obtain ⟨hdvd, hord, hcard, U, cc, Q₀, hUκ, hUr, hFFD, ⟨ds⟩⟩ :=
      descent_core_aux' hℓ hf hp hp2 hK hd _ hnd hS3 hgates a haD hap g hg
    refine ⟨hord, hcard, U, cc, Q₀, hUκ, hUr, hFFD, ?_⟩
    have hfp : 1 ≤ f / p := Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) hp.pos
    have hcard' : Nat.card (fixedField U.val) = ℓ ^ (f / p) := by
      rw [← hUr] at hcard
      exact hcard
    obtain ⟨m, δ, hδ, H, HK, hbK, hdim, hw⟩ := ds
    have hle := le_sourceWittIndex_coordinateQuadPlus n K
    obtain ⟨rfl, rfl⟩ : m = n ∧ δ = 0 := by omega
    exact plus_field_descent ⟨hℓ, hfp, hn4⟩ hcard' H HK hbK
  ·
    intro hn K _ _ hK b c' hirr e a ha haD hap
    obtain ⟨hℓ, hf, hn4⟩ := h.1
    obtain ⟨-, hnd, hS3, -⟩ := coordinate_model_witness_minus h K hK b c' hirr e
    have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates G .POmegaMinus
      (Or.inr (Or.inr rfl)) n ℓ f h hn K hK b c' hirr e
    have hd : 0 < 2 * n := by omega
    obtain ⟨g₀, hg₀⟩ := ha
    refine ⟨(descent_core_aux' hℓ hf hp hp2 hK hd _ hnd hS3 hgates a haD hap g₀ hg₀).1, ?_⟩
    rintro σ ⟨g, hg, rfl⟩
    obtain ⟨hdvd, hord, hcard, U, cc, Q₀, hUκ, hUr, hFFD, ⟨ds⟩⟩ :=
      descent_core_aux' hℓ hf hp hp2 hK hd _ hnd hS3 hgates a haD hap g hg
    refine ⟨hord, hcard, U, cc, Q₀, hUκ, hUr, hFFD, ?_⟩
    have hfp : 1 ≤ f / p := Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) hp.pos
    have hcard' : Nat.card (fixedField U.val) = ℓ ^ (f / p) := by
      rw [← hUr] at hcard
      exact hcard
    obtain ⟨m, δ, hδ, H, HK, hbK, hdim, hw⟩ := ds
    have hw' := sourceWittIndex_coordinateQuadMinus n K hn b c' hirr hnd
    obtain ⟨rfl, rfl⟩ : m = n - 1 ∧ δ = 2 := by omega
    exact minus_field_descent hn b c' hFFD.2.1 ⟨hℓ, hfp, hn4⟩ hcard' H HK hbK

end CFSG.HardMathSupport.Lang.Proving
