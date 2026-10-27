module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatEvenOuterPSL
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenClassicalPSU
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenClassicalPSp

public noncomputable section

namespace CFSG.SeitzReduction.LinearPilot

open CFSG Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification
open CFSG.ComponentClassification.CatLeafProof (fixedSubgroupCongrEquiv)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

@[expose] def SpFixedOrNoPComponent (X : Type) [Group X] (g : ℕ) : Prop :=
  (∃ (k : Type) (_ : Field k) (_ : Finite k) (r : ℕ), Nat.card k = 2 ^ g ∧ 1 ≤ r ∧
      Nonempty (X ≃* StatedSp r k)) ∨ (∀ P : Subgroup X, ¬ IsPComponent 2 P)

theorem spFixedOrNoPComponent_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    {g : ℕ} (h : SpFixedOrNoPComponent Y g) : SpFixedOrNoPComponent X g := by
  rcases h with ⟨k, _, _, r, hk, hr, ⟨Φ⟩⟩ | h
  · exact Or.inl ⟨k, inferInstance, inferInstance, r, hk, hr, ⟨e.trans Φ⟩⟩
  · exact Or.inr fun P hP =>
      h _ (LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent 2 e hP)

theorem false_of_spFixedOrNoPComponent {m : ℕ} (hdet : SLmEvenTypeDetAt m) {X : Type} [Group X]
    [Finite X] {g : ℕ} (h : SpFixedOrNoPComponent X g) {D : Subgroup X} (hD : IsComponent D)
    {f : ℕ} (hm : 3 ≤ m) (hDm : LieModel (D ⧸ center D) .PSL m 2 f) : False := by
  rcases h with ⟨k, _, _, r, hk, hr, ⟨Φ⟩⟩ | h
  · exact no_component_statedSp hdet hk hr Φ hD hm hDm
  · exact h D (LocalAnalysis.ComponentInitial.isPComponent_two_of_isComponent hD)

section Unitary

open CFSG.LocalAnalysis.ComponentInitial FourGroupEvenCanonical UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.UnbalancedCatalog.UnitaryFieldTransfer

theorem psu_outer_fixed_exact {J : Type} [Group J] {n e : ℕ}
    (hadm : StatedLieAdmissible .PSU n 2 e) (hm : LieModel J .PSU n 2 e) (α : MulAut J)
    (hα : orderOf α = 2) (hαo : α ∉ (MulAut.conj : J →* MulAut J).range) :
    SpFixedOrNoPComponent (fixedSubgroup α) e := by
  obtain ⟨K, _, h, ⟨ψ⟩⟩ := CatLeafProof.nonempty_mulEquiv_primeFormP_of_lieModel hadm hm
  have hn : 3 ≤ n := hadm.2.2.1
  have hq : ¬(n = 3 ∧ 2 ^ e = 2) := fun h3 => hadm.2.2.2 (by rw [h3.1, h3.2])
  have : Finite K := h.finite
  have : Finite J := Finite.of_equiv _ ψ.symm.toEquiv
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  have hβ : orderOf (MulAut.congr ψ α) = 2 :=
    (orderOf_injective (MulAut.congr ψ).toMonoidHom (MulAut.congr ψ).injective α).trans hα
  have hβo : MulAut.congr ψ α ∉
      inner (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
    rw [FixedFourGroup.congr_mem_inner_iff]
    exact hαo
  obtain ⟨hcases, -, -, hDinner⟩ := even_unitary_involution_matrix_lifts h hC hn hq _ hβ
  rcases hcases with hid | hbar
  · exfalso
    apply hβo
    refine hDinner _ ?_ hβ
    rw [← ker_primeFormFieldFactor h hC hn hq, MonoidHom.mem_ker]
    exact hid
  obtain ⟨-, -, C₀, hC₀, hcase₀, -, -, -, -, ⟨θ, -, hθβ⟩, -⟩ :=
    even_unitary_antiunitary_involution_descent h hC hn hq _ hβ hbar
  have hc : MulAut.congr θ (primeFormFieldHom h hC₀ (primeFormFieldFactor h hC hn hq
      (MulAut.congr ψ α))) = MulAut.congr ψ α := MulEquiv.ext fun x => (hθβ x).symm
  refine spFixedOrNoPComponent_of_mulEquiv ((fixedSubgroupCongrEquiv ψ α).trans
    ((MulEquiv.subgroupCongr (congrArg fixedSubgroup hc)).symm.trans
      (fixedSubgroupCongrEquiv θ _).symm)) ?_
  have := fixedField_finite h
  rcases F4Pilot.psu_fieldBar_cases h hn hq hC₀ hcase₀ _ hbar with ⟨r, hr1, -, ⟨Φ⟩⟩ | hch
  · exact Or.inl ⟨h.fixedField, inferInstance, inferInstance, r, h.card_fixedField, hr1, ⟨Φ⟩⟩
  · exact Or.inr (CatLeafProof.not_isPComponent_of_isCharacteristicP hch)

theorem catSLmEvenOuterFamilyAt_PSU {m : ℕ} (hm : 3 ≤ m) (hdet : SLmEvenTypeDetAt m) :
    CatSLmEvenOuterFamilyAt .PSU m := by
  intro S _ _ _ _ n e hadm hmS σ hσ hout f D hD hDm _
  exact (false_of_spFixedOrNoPComponent hdet (psu_outer_fixed_exact hadm hmS σ hσ hout) hD hm
    hDm).elim

theorem catSLmEvenOuterFamily_PSU (hdet : SLmEvenTypeDet) : CatSLmEvenOuterFamily .PSU :=
  fun m hm => catSLmEvenOuterFamilyAt_PSU hm (hdet m hm)

end Unitary

section Symplectic

open CFSG.LocalAnalysis.ComponentInitial SymplecticFlag SymplecticHigher
open CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.UnbalancedCatalog.SpChain

variable {K : Type} [Field K]

theorem psp_suzuki_fixed {m : ℕ} (hm : 1 ≤ m)
    [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ (2 * m + 1))
    {a : MulAut (StatedProj (StatedSp 2 K))} (ha : a * a = 1) (s : StatedSp 2 K)
    (has : a = spInner 2 K s * exceptionalAut K ^ (2 * m + 1)) :
    IsSimpleGroup (fixedSubgroup a) ∧ StatedLieAdmissible .twistedB2 0 2 (2 * m + 1) ∧
      LieModel (fixedSubgroup a) .twistedB2 0 2 (2 * m + 1) := by
  subst has
  obtain ⟨χ, -, hχ⟩ := OutcomeLocal.exists_inner_conj_eta hK ha
  obtain ⟨ψ, -, hψinj, -, hrange, -⟩ :=
    even_symplectic_two_suzuki_full_centralizer_odd_core hm hK (exceptionalAut K)
      exceptionalAut_proj
  obtain ⟨-, -, hSz⟩ := LieType.Ree.suzuki_simple hm hK
  have hcj := CatLeafProof.conj_injective_statedProj_statedSp_charTwo (r := 2) (K := K)
  have hc : MulAut.congr χ (exceptionalAut K ^ (2 * m + 1)) =
      spInner 2 K s * exceptionalAut K ^ (2 * m + 1) :=
    (MulEquiv.ext fun _ => rfl : MulAut.congr χ (exceptionalAut K ^ (2 * m + 1)) = _).trans
      hχ.symm
  let Φ : fixedSubgroup (spInner 2 K s * exceptionalAut K ^ (2 * m + 1)) ≃*
      Blueprint.suzukiGroup m K :=
    (MulEquiv.subgroupCongr (congrArg fixedSubgroup hc)).symm.trans
      ((fixedSubgroupCongrEquiv _ _).symm.trans
        ((CatLeafProof.fixedInnerEquiv hcj _).trans
          ((MulEquiv.subgroupCongr hrange.symm).trans (MonoidHom.ofInjective hψinj).symm)))
  have hadm : StatedLieAdmissible .twistedB2 0 2 (2 * m + 1) :=
    ⟨Nat.prime_two, by omega, rfl, rfl, ⟨m, rfl⟩, by omega⟩
  have hLie : LieModel (Blueprint.suzukiGroup m K) .twistedB2 0 2 (2 * m + 1) :=
    Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, m, hm, K, inferInstance, inferInstance, rfl, hK,
      ⟨MulEquiv.refl _⟩⟩))
  exact ⟨Φ.isSimpleGroup, hadm, LieType.CurtisTits.lieModel_of_mulEquiv Φ.symm hLie⟩

theorem psp_outer_fixed_exact {J : Type} [Group J] {n e : ℕ}
    (hadm : StatedLieAdmissible .PSp n 2 e) (hm : LieModel J .PSp n 2 e) (α : MulAut J)
    (hα : orderOf α = 2) (hαo : α ∉ (MulAut.conj : J →* MulAut J).range) :
    SpFixedOrNoPComponent (fixedSubgroup α) (e / 2) ∨
      (IsSimpleGroup (fixedSubgroup α) ∧ StatedLieAdmissible .twistedB2 0 2 e ∧
        LieModel (fixedSubgroup α) .twistedB2 0 2 e) := by
  obtain ⟨K, _, _, hK, ⟨eJ⟩⟩ := CatLeafProof.nonempty_mulEquiv_psp_of_lieModel hadm hm
  have hf : 1 ≤ e := hadm.2.1
  have hn : 2 ≤ n := hadm.2.2.1
  have hnf : (n, 2 ^ e) ≠ (2, 2) := hadm.2.2.2
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  have : NeZero n := ⟨by omega⟩
  have : Finite J := Finite.of_equiv _ eJ.symm.toEquiv
  have hβ : orderOf (MulAut.congr eJ α) = 2 :=
    (orderOf_injective (MulAut.congr eJ).toMonoidHom (MulAut.congr eJ).injective α).trans hα
  have hβ2 : MulAut.congr eJ α * MulAut.congr eJ α = 1 := by
    rw [← sq, ← hβ, pow_orderOf_eq_one]
  have hβo : MulAut.congr eJ α ∉ inner (StatedProj (StatedSp n K)) := by
    rw [FixedFourGroup.congr_mem_inner_iff]
    exact hαo
  let Ψ := fixedSubgroupCongrEquiv eJ α
  have hE : MulAut.congr eJ α ∈ spSemilinearAutGroup n K →
      SpFixedOrNoPComponent (fixedSubgroup α) (e / 2) := by
    intro hmem
    obtain ⟨g, σ, hgσ⟩ := exists_eq_spInner_mul_fieldAut hmem
    have hσ : σ ≠ 1 := by
      rintro rfl
      rw [map_one, mul_one] at hgσ
      exact hβo (hgσ ▸ spInner_mem_inner g)
    obtain ⟨k, _, _, hk, -, ⟨Φ⟩⟩ := F4Pilot.psp_field_fixed hn hf hK hβ2 g σ hgσ hσ
    exact Or.inl ⟨k, inferInstance, inferInstance, n, hk, by omega, ⟨Ψ.trans Φ⟩⟩
  by_cases hn3 : 3 ≤ n
  · left
    apply hE
    rw [(SymplecticHigher.automorphism_generation (K := K) hn3).1]
    exact mem_top _
  · obtain rfl : n = 2 := by omega
    obtain ⟨-, -, -, -, ⟨γ, hγ⟩, hall⟩ := even_symplectic_two_exterior_square_automorphism hf hK
    obtain ⟨-, -, -, -, -, -, -, -, -, -, heven, hodd⟩ := hall γ hγ
    rcases Nat.even_or_odd e with hfe | hfo
    · exact Or.inl (hE (heven hfe _ hβ))
    · obtain ⟨s, hs⟩ := hodd hfo _ hβ hβo
      obtain ⟨m, rfl⟩ := hfo
      have hm : 1 ≤ m := by
        by_contra h0
        obtain rfl : m = 0 := by omega
        exact hnf rfl
      rw [eq_exceptionalAut hγ] at hs
      obtain ⟨hS, hadmB, hLie⟩ := psp_suzuki_fixed hm hK hβ2 s hs
      exact Or.inr ⟨Ψ.isSimpleGroup, hadmB, LieType.CurtisTits.lieModel_of_mulEquiv Ψ.symm hLie⟩

theorem catSLmEvenOuterFamilyAt_PSp {m : ℕ} (hm : 3 ≤ m)
    (hdet : SLmEvenTypeDetAt m) : CatSLmEvenOuterFamilyAt .PSp m := by
  intro S _ _ _ _ n e hadm hmS σ hσ hout f D hD hDm _
  rcases psp_outer_fixed_exact hadm hmS σ hσ hout with h | ⟨hS, hadmB, hLie⟩
  · exact (false_of_spFixedOrNoPComponent hdet h hD hm hDm).elim
  · have hDtop := F4Pilot.eq_top_of_isComponent_of_isSimpleGroup hD
    let eD : D ≃* fixedSubgroup σ := (MulEquiv.subgroupCongr hDtop).trans Subgroup.topEquiv
    have hDs : IsSimpleGroup D := eD.isSimpleGroup
    obtain ⟨htt, -, -⟩ := typeDet_of_simple hdet hD.1 hDs hDm hadmB
      (LieType.CurtisTits.lieModel_of_mulEquiv eD.symm hLie)
    exact absurd htt (by decide)

theorem catSLmEvenOuterFamily_PSp (hdet : SLmEvenTypeDet) :
    CatSLmEvenOuterFamily .PSp :=
  fun m hm => catSLmEvenOuterFamilyAt_PSp hm (hdet m hm)

end Symplectic

end CFSG.SeitzReduction.LinearPilot
