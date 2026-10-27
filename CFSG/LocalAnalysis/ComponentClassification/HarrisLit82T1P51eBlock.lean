module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51eOrd
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUClOOrd
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LocalAnalysis.ComponentClassification.GSFMMaximal
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeSteps
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitFrontier46
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitKGFieldClass
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLit39b
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFourPresentation
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.Open.GorensteinHaradaSectionalRankFourMilestoneDefs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P51e

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
  CFSG.ComponentClassification.Burgoyne.O CFSG.ComponentClassification.Burgoyne.Proj
  CFSG.ComponentClassification.Burgoyne.C
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL)
open CFSG.GroupTheory.WeirSylow (IsPlusType natCard_orthogonalGroup_odd
  natCard_orthogonalGroup_of_type)

theorem cast_prod_pow_sub_one (q m : ℕ) (hq : 0 < q) :
    ((∏ i ∈ Finset.Icc 1 m, (q ^ (2 * i) - 1) : ℕ) : ℤ) =
      ∏ i ∈ Finset.Icc 1 m, (((q : ℤ) ^ 2) ^ i - 1) := by
  rw [Nat.cast_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Nat.cast_sub (Nat.one_le_pow _ _ hq), Nat.cast_pow, Nat.cast_one, pow_mul]

theorem natCard_orth_odd {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (hK : ringChar K ≠ 2) {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {m : ℕ}
    (hdim : Module.finrank K V = 2 * m + 1) :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) =
      2 * Nat.card K ^ (m ^ 2) * ∏ i ∈ Finset.Icc 1 m, (Nat.card K ^ (2 * i) - 1) := by
  have h := natCard_orthogonalGroup_odd hK hQ hdim
  rw [← cast_prod_pow_sub_one (Nat.card K) m Nat.card_pos] at h
  exact_mod_cast h

theorem natCard_orth_even {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {m : ℕ}
    (hdim : Module.finrank K V = 2 * (m + 1)) :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) = 2 * Nat.card K ^ (m * (m + 1)) *
        (Nat.card K ^ (m + 1) - 1) * ∏ i ∈ Finset.Icc 1 m, (Nat.card K ^ (2 * i) - 1) ∨
      Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) = 2 * Nat.card K ^ (m * (m + 1)) *
        (Nat.card K ^ (m + 1) + 1) * ∏ i ∈ Finset.Icc 1 m, (Nat.card K ^ (2 * i) - 1) := by
  by_cases hplus : IsPlusType Q
  · left
    have h := natCard_orthogonalGroup_of_type hQ hdim (Or.inl ⟨rfl, hplus⟩)
    rw [← cast_prod_pow_sub_one (Nat.card K) m Nat.card_pos] at h
    have h1 : ((Nat.card K ^ (m + 1) - 1 : ℕ) : ℤ) = (Nat.card K : ℤ) ^ (m + 1) - 1 := by
      rw [Nat.cast_sub (Nat.one_le_pow (m + 1) (Nat.card K) Nat.card_pos), Nat.cast_pow,
        Nat.cast_one]
    rw [← h1] at h
    exact_mod_cast h
  · right
    have h := natCard_orthogonalGroup_of_type hQ hdim (Or.inr ⟨rfl, hplus⟩)
    rw [← cast_prod_pow_sub_one (Nat.card K) m Nat.card_pos, sub_neg_eq_add] at h
    exact_mod_cast h

theorem orth_index_cases {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (hK : ringChar K ≠ 2) {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (h3 : 3 ≤ Module.finrank K V) :
    (∃ a, Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) =
      2 ^ a * Nat.card (commutator (TauCeti.QuadraticMap.orthogonalGroup Q))) ∨
    ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) →
      ℓ = 2 ∨ ℓ = 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) :=
    Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V)) fun _ _ h => LinearEquiv.ext (congrFun h)
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hodd : Odd (Nat.card K) := CatalogueBLinearHigherB.odd_card_of_ringChar_ne_two K hK
  by_cases hT : ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0
  ·
    left
    have : Invertible (2 : K) := invertibleOfNonzero h2
    obtain ⟨T, hT3, hTQ⟩ := hT
    obtain ⟨P₁, P₂, P₃, h12, h13, h23⟩ :=
      ClassicalGroups.Orthogonal.exists_three_hypPairs hQ hT3.ge hTQ
    obtain ⟨hcard, -⟩ := ClassicalInvolution.orthogonalGroup_index_four hQ h12 h13 h23
    have hΩ :=
      ClassicalGroups.Orthogonal.commutator_orthogonalGroup_eq_elementaryGroup_of_two_ne_zero
        h2 hQ h12 h13 h23
    refine ⟨2, ?_⟩
    rw [show (2 : ℕ) ^ 2 = 4 by norm_num]
    rw [hcard, ← hΩ, ← Subgroup.map_subtype_commutator,
      Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
  ·
    have hcases := CatalogueBOrthogonalAssembly.low_Witt_finrank_cases hodd Q hQ h3 hT
    obtain ⟨hexc, hnexc, -⟩ :=
      LocalAnalysis.ComponentInitial.orthogonal_low_dimensional_fixed_derived_component_coverage
        Q hQ (by
          rcases hcases with h | h | h | h
          · exact Or.inl ⟨hodd, Or.inl h⟩
          · exact Or.inl ⟨hodd, Or.inr (Or.inl h)⟩
          · exact Or.inl ⟨hodd, Or.inr (Or.inr h)⟩
          · exact Or.inr (Or.inl ⟨hodd, h, hT⟩))
    by_cases hE : (Module.finrank K V = 3 ∧ Nat.card K = 3) ∨
        ((Module.finrank K V = 4 ∧
          ∃ S : Submodule K V, Module.finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0) ∧
          (Nat.card K = 2 ∨ Nat.card K = 3))
    · exact Or.inr (hexc hE).1
    · left
      obtain ⟨-, hP2, -⟩ := hnexc hE
      obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 hP2
      refine ⟨a, ?_⟩
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
        (commutator (TauCeti.QuadraticMap.orthogonalGroup Q)), ha]

theorem noSpin7_blockP {K : Type} [Field K] [Finite K] (hK : ringChar K ≠ 2)
    {p f : ℕ} (hp : p.Prime) (hKc : Nat.card K = p ^ f) {d : ℕ} {w : Fin d → K}
    (hw : ∀ i, w i ≠ 0) {I : Finset (Fin d)} (hIc : Iᶜ.Nonempty)
    (hNF : BlockNF w I) : NoSpin7 p ↥(blockP K hw I) := by
  intro r _ hZ hLM
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := GSThmB.QPUCl.finite_linearEquiv K I.card
  obtain ⟨hp2, hf⟩ := GSThmB.QPUCl.prime_ne_two_and_one_le hK hp hKc
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hp0 : 0 < p := hp.pos
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hk3 : 3 ≤ I.card := by
    obtain ⟨I₀, hI₀, h3, -⟩ := hNF
    exact h3.trans (Finset.card_le_card hI₀)
  have hadm' := admissible_of_lieModel_pomegaOdd hLM
  have hr : 1 ≤ r := hadm'.2.1
  have hZ2 : IsPGroup 2 (center ↥(blockP K hw I)) := by
    intro z
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one, Subgroup.coe_pow, OneMemClass.coe_one]
    exact sq_eq_one_of_mem_center_blockP hw hK hIc hNF z.2
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 hZ2
  have hZc : Nat.card (center ↥(blockP K hw I)) = 2 := by
    rw [ha] at hZ ⊢
    rw [Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same] at hZ
    rw [hZ, pow_one]
  obtain ⟨hB1, hB2⟩ := CatLeafProof.X10Lin.lieOrder_of_lieModel_classical
    (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hp2 (by norm_num) hLM
  rw [CatLeafProof.lieOrderNumerator_eq hadm'] at hB1
  change Nat.card _ * 2 = (p ^ r) ^ 9 * ∏ i ∈ Finset.Icc 1 3, ((p ^ r) ^ (2 * i) - 1) at hB1
  have hPZ := Subgroup.card_eq_card_quotient_mul_card_subgroup (center ↥(blockP K hw I))
  rw [hZc] at hPZ
  have hP : Nat.card ↥(blockP K hw I) =
      (p ^ r) ^ 9 * ∏ i ∈ Finset.Icc 1 3, ((p ^ r) ^ (2 * i) - 1) := by
    rw [hPZ, hB1]
  have hp2' : ¬ p ∣ 2 := fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h)
  have hfacP : (Nat.card ↥(blockP K hw I)).factorization p = 9 * r := by
    rw [hPZ, Nat.factorization_mul Nat.card_pos.ne' two_ne_zero, Finsupp.add_apply, hB2,
      Nat.factorization_eq_zero_of_not_dvd hp2', add_zero]
    rfl
  have hR : ((diagGL (wRes_ne_zero hw I) : GL (Fin I.card) K) :
      Matrix (Fin I.card) (Fin I.card) K)ᵀ = diagGL (wRes_ne_zero hw I) := by
    rw [coe_diagGL]
    exact diagonal_transpose _
  have hQnd := CatalogueBLinearHigherB.polarBilin_matrixQuadraticForm_nondegenerate hK _ hR
  have hdim : Module.finrank K (Fin I.card → K) = I.card := Module.finrank_fin_fun K
  have hcardP := GSThmB.QPUCl.card_blockP_eq hK hw hIc
  set Q := CatalogueBLinearHigherB.matrixQuadraticForm (diagGL (wRes_ne_zero hw I)) with hQdef
  obtain ⟨ℓ₆, h₆⟩ := exists_isPrimDiv hp3 (show 3 ≤ r * (2 * 3) by omega)
  have h₆7 : 7 ≤ ℓ₆ := by
    have := h₆.lt hp0 (by omega)
    omega
  have h₆P : ℓ₆ ∣ Nat.card ↥(blockP K hw I) := by
    rw [hP]
    exact Dvd.dvd.mul_left (h₆.dvd_pow_pow_sub_one.trans
      (Finset.dvd_prod_of_mem (fun i => (p ^ r) ^ (2 * i) - 1)
        (Finset.mem_Icc.2 ⟨by norm_num, le_rfl⟩))) _
  have hΩO : Nat.card (commutator (TauCeti.QuadraticMap.orthogonalGroup Q)) ∣
      Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) := Subgroup.card_subgroup_dvd_card _
  have h₆O : ℓ₆ ∣ Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) := by
    rw [hcardP] at h₆P
    exact h₆P.trans hΩO
  obtain ⟨b, hb⟩ : ∃ b, Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) =
      2 ^ b * Nat.card (commutator (TauCeti.QuadraticMap.orthogonalGroup Q)) := by
    rcases orth_index_cases hK hQnd (by omega) with h | h
    · exact h
    · rcases h ℓ₆ h₆.1 h₆O with h2 | h3 <;> omega
  have hfacO := GSThmB.QPUCl.factorization_card_orthogonalGroup hK hp hKc hQnd (by omega)
  rw [hdim, hb, GSThmB.QPUCl.factorization_two_pow_mul hp2 b _ Nat.card_pos.ne', ← hcardP,
    hfacP] at hfacO
  have hOP : ∀ {ℓ : ℕ}, ℓ.Prime → ℓ ≠ 2 → ℓ ∣ Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) →
      ℓ ∣ Nat.card ↥(blockP K hw I) := by
    intro ℓ hℓ hℓ2 h
    rw [hb] at h
    rcases (Nat.Prime.dvd_mul hℓ).1 h with h | h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 (hℓ.dvd_of_dvd_pow h)) hℓ2
    · rw [hcardP]
      exact h
  have hPk : ∀ {ℓ k : ℕ}, IsPrimDiv ℓ p k → 0 < k → ℓ ∣ Nat.card ↥(blockP K hw I) →
      k ≤ r * 6 := by
    intro ℓ k hℓ hk h
    rw [hP] at h
    rcases (Nat.Prime.dvd_mul hℓ.1).1 h with h | h
    · rw [← pow_mul] at h
      exact absurd h (hℓ.not_dvd_pow_base hp0 hk _)
    · exact le_of_index (by omega) (index_b3 hℓ hp0 hk h)
  obtain ⟨ℓ₄, h₄⟩ := exists_isPrimDiv hp3 (show 3 ≤ r * (2 * 2) by omega)
  have h₄O : ℓ₄ ∣ Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) := by
    have h₄P : ℓ₄ ∣ Nat.card ↥(blockP K hw I) := by
      rw [hP]
      exact Dvd.dvd.mul_left (h₄.dvd_pow_pow_sub_one.trans
        (Finset.dvd_prod_of_mem (fun i => (p ^ r) ^ (2 * i) - 1)
          (Finset.mem_Icc.2 ⟨by norm_num, by norm_num⟩))) _
    rw [hcardP] at h₄P
    exact h₄P.trans hΩO
  have h₄7 : 5 ≤ ℓ₄ := by
    have := h₄.lt hp0 (by omega)
    omega
  obtain ⟨m', hm' | hm'⟩ := Nat.even_or_odd' I.card
  ·
    obtain ⟨m, rfl⟩ : ∃ m, m' = m + 1 := ⟨m' - 1, by omega⟩
    have he : (I.card - 1) ^ 2 / 4 = m * (m + 1) := by
      rw [hm', show 2 * (m + 1) - 1 = 2 * m + 1 by omega,
        show (2 * m + 1) ^ 2 = 4 * (m * (m + 1)) + 1 by ring]
      omega
    rw [he] at hfacO
    have hm1 : 1 ≤ m := by omega
    have hfm1 : 0 < f * (m + 1) := Nat.mul_pos (by omega) (by omega)
    rcases natCard_orth_even (m := m) hQnd (by omega) with hO | hO
    ·
      rw [hKc] at hO
      have e1 : r * (2 * 3) ≤ f * (2 * m) := by
        rw [hO] at h₆O
        rcases (Nat.Prime.dvd_mul h₆.1).1 h₆O with h | h
        · rcases (Nat.Prime.dvd_mul h₆.1).1 h with h | h
          · rcases (Nat.Prime.dvd_mul h₆.1).1 h with h | h
            · exact absurd (Nat.le_of_dvd two_pos h) (by omega)
            · rw [← pow_mul] at h
              exact absurd h (h₆.not_dvd_pow_base hp0 (by omega) _)
          · have h1 := Nat.le_of_dvd hfm1 ((h₆.dvd_pow_pow_sub_one_iff hp0 (by omega) f _).1 h)
            have h2 : f * (m + 1) ≤ f * (2 * m) := Nat.mul_le_mul_left _ (by omega)
            omega
        · obtain ⟨i, hi, hi6⟩ := index_sp h₆ hp0 (by omega) h
          obtain ⟨hi1, him⟩ := Finset.mem_Icc.1 hi
          have h1 := Nat.le_of_dvd (Nat.mul_pos (by omega) (by omega)) hi6
          have h2 : f * (2 * i) ≤ f * (2 * m) := Nat.mul_le_mul_left _ (by omega)
          omega
      obtain ⟨ℓ, hℓ⟩ := exists_isPrimDiv hp3 (show 3 ≤ f * (2 * m) by omega)
      have hℓO : ℓ ∣ Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) := by
        rw [hO]
        exact Dvd.dvd.mul_left (hℓ.dvd_pow_pow_sub_one.trans
          (Finset.dvd_prod_of_mem (fun i => (p ^ f) ^ (2 * i) - 1)
            (Finset.mem_Icc.2 ⟨hm1, le_rfl⟩))) _
      have e3 := hPk hℓ (by omega) (hOP hℓ.1 (hℓ.ne_two hodd (by omega)) hℓO)
      have hfm : f * m = r * 3 := by
        have : f * (2 * m) = 2 * (f * m) := by ring
        omega
      have hm2 : m = 2 := by
        have h1 : f * m * (m + 1) = f * m * 3 := by
          calc f * m * (m + 1) = f * (m * (m + 1)) := by ring
            _ = 9 * r := hfacO.symm
            _ = f * m * 3 := by rw [hfm]; ring
        have h2 := Nat.eq_of_mul_eq_mul_left (Nat.mul_pos (by omega) (by omega)) h1
        omega
      subst hm2
      have hfD : f * 4 = r * 6 := by omega
      rw [hO] at h₄O
      rcases (Nat.Prime.dvd_mul h₄.1).1 h₄O with h | h
      · rcases (Nat.Prime.dvd_mul h₄.1).1 h with h | h
        · rcases (Nat.Prime.dvd_mul h₄.1).1 h with h | h
          · exact absurd (Nat.le_of_dvd two_pos h) (by omega)
          · rw [← pow_mul] at h
            exact absurd h (h₄.not_dvd_pow_base hp0 (by omega) _)
        · obtain ⟨c, hc⟩ := exists_of_dvd_four (k := 3) (by omega) hfD
            ((h₄.dvd_pow_pow_sub_one_iff hp0 (by omega) f _).1 h)
          omega
      · obtain ⟨i, hi, hi4⟩ := index_sp h₄ hp0 (by omega) h
        obtain ⟨hi1, hi2⟩ := Finset.mem_Icc.1 hi
        obtain ⟨c, hc⟩ := exists_of_dvd_four (k := 2 * i) (by omega) hfD
          (show r * 4 ∣ f * (2 * i) from hi4)
        interval_cases i <;> omega
    ·
      rw [hKc] at hO
      have e1 : r * (2 * 3) ≤ 2 * (f * (m + 1)) := by
        rw [hO] at h₆O
        rcases (Nat.Prime.dvd_mul h₆.1).1 h₆O with h | h
        · rcases (Nat.Prime.dvd_mul h₆.1).1 h with h | h
          · rcases (Nat.Prime.dvd_mul h₆.1).1 h with h | h
            · exact absurd (Nat.le_of_dvd two_pos h) (by omega)
            · rw [← pow_mul] at h
              exact absurd h (h₆.not_dvd_pow_base hp0 (by omega) _)
          · exact Nat.le_of_dvd (by omega) (h₆.dvd_of_dvd_pow_pow_add_one hp0 (by omega) h)
        · obtain ⟨i, hi, hi6⟩ := index_sp h₆ hp0 (by omega) h
          obtain ⟨hi1, him⟩ := Finset.mem_Icc.1 hi
          have h1 := Nat.le_of_dvd (Nat.mul_pos (by omega) (by omega)) hi6
          have h2 : f * (2 * i) ≤ f * (2 * (m + 1)) := Nat.mul_le_mul_left _ (by omega)
          have h3 : f * (2 * (m + 1)) = 2 * (f * (m + 1)) := by ring
          omega
      obtain ⟨ℓ, hℓ⟩ := exists_isPrimDiv hp3 (show 3 ≤ 2 * (f * (m + 1)) by omega)
      have hℓO : ℓ ∣ Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) := by
        rw [hO]
        exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (hℓ.dvd_pow_pow_add_one hfm1) _) _
      have e3 := hPk hℓ (by omega) (hOP hℓ.1 (hℓ.ne_two hodd (by omega)) hℓO)
      have hfm : f * (m + 1) = r * 3 := by omega
      have hm3 : m = 3 := by
        have h1 : f * (m + 1) * m = f * (m + 1) * 3 := by
          calc f * (m + 1) * m = f * (m * (m + 1)) := by ring
            _ = 9 * r := hfacO.symm
            _ = f * (m + 1) * 3 := by rw [hfm]; ring
        exact Nat.eq_of_mul_eq_mul_left hfm1 h1
      subst hm3
      have hfD : f * 8 = r * 6 := by omega
      rw [hO] at h₄O
      rcases (Nat.Prime.dvd_mul h₄.1).1 h₄O with h | h
      · rcases (Nat.Prime.dvd_mul h₄.1).1 h with h | h
        · rcases (Nat.Prime.dvd_mul h₄.1).1 h with h | h
          · exact absurd (Nat.le_of_dvd two_pos h) (by omega)
          · rw [← pow_mul] at h
            exact absurd h (h₄.not_dvd_pow_base hp0 (by omega) _)
        · obtain ⟨c, hc⟩ := exists_of_dvd_four (k := 8) (by omega) hfD
            (by rw [show f * 8 = 2 * (f * (3 + 1)) by ring]
                exact h₄.dvd_of_dvd_pow_pow_add_one hp0 (by omega) h)
          omega
      · obtain ⟨i, hi, hi4⟩ := index_sp h₄ hp0 (by omega) h
        obtain ⟨hi1, hi3⟩ := Finset.mem_Icc.1 hi
        obtain ⟨c, hc⟩ := exists_of_dvd_four (k := 2 * i) (by omega) hfD
          (show r * 4 ∣ f * (2 * i) from hi4)
        interval_cases i <;> omega
  ·
    have he : (I.card - 1) ^ 2 / 4 = m' ^ 2 := by
      rw [hm', show 2 * m' + 1 - 1 = 2 * m' by omega, show (2 * m') ^ 2 = 4 * m' ^ 2 by ring]
      exact Nat.mul_div_cancel_left _ (by norm_num)
    rw [he] at hfacO
    have hm1 : 1 ≤ m' := by omega
    have hO := natCard_orth_odd (m := m') hK hQnd (by omega)
    rw [hKc] at hO
    have e1 : r * (2 * 3) ≤ f * (2 * m') := by
      rw [hO] at h₆O
      rcases (Nat.Prime.dvd_mul h₆.1).1 h₆O with h | h
      · rcases (Nat.Prime.dvd_mul h₆.1).1 h with h | h
        · exact absurd (Nat.le_of_dvd two_pos h) (by omega)
        · rw [← pow_mul] at h
          exact absurd h (h₆.not_dvd_pow_base hp0 (by omega) _)
      · obtain ⟨i, hi, hi6⟩ := index_sp h₆ hp0 (by omega) h
        obtain ⟨hi1, him⟩ := Finset.mem_Icc.1 hi
        have h1 := Nat.le_of_dvd (Nat.mul_pos (by omega) (by omega)) hi6
        have h2 : f * (2 * i) ≤ f * (2 * m') := Nat.mul_le_mul_left _ (by omega)
        omega
    obtain ⟨ℓ, hℓ⟩ := exists_isPrimDiv hp3 (show 3 ≤ f * (2 * m') by omega)
    have hℓO : ℓ ∣ Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) := by
      rw [hO]
      exact Dvd.dvd.mul_left (hℓ.dvd_pow_pow_sub_one.trans
        (Finset.dvd_prod_of_mem (fun i => (p ^ f) ^ (2 * i) - 1)
          (Finset.mem_Icc.2 ⟨hm1, le_rfl⟩))) _
    have e3 := hPk hℓ (by omega) (hOP hℓ.1 (hℓ.ne_two hodd (by omega)) hℓO)
    have hfm : f * m' = r * 3 := by
      have : f * (2 * m') = 2 * (f * m') := by ring
      omega
    have hm3 : m' = 3 := by
      have h1 : f * m' * m' = f * m' * 3 := by
        calc f * m' * m' = f * m' ^ 2 := by ring
          _ = 9 * r := hfacO.symm
          _ = f * m' * 3 := by rw [hfm]; ring
      exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos (by omega) (by omega)) h1
    subst hm3
    have hfr : f = r := by omega
    have h4 := GSThmB.QPUCl.card_orthogonalGroup_eq_four_mul hK hQnd (by omega)
    rw [← hfr] at hP
    rw [← hcardP, hP] at h4
    rw [h4, show (3 : ℕ) ^ 2 = 9 by norm_num] at hO
    have hS : 0 < (p ^ f) ^ 9 * ∏ i ∈ Finset.Icc 1 3, ((p ^ f) ^ (2 * i) - 1) := by
      rw [← hP]
      exact Nat.card_pos
    have h1 : 4 * ((p ^ f) ^ 9 * ∏ i ∈ Finset.Icc 1 3, ((p ^ f) ^ (2 * i) - 1)) =
        2 * ((p ^ f) ^ 9 * ∏ i ∈ Finset.Icc 1 3, ((p ^ f) ^ (2 * i) - 1)) := by
      rw [hO]
      ring
    omega

end CFSG.ComponentClassification.HarrisLit.T1.P51e
