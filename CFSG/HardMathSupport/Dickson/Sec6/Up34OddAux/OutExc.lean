module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.Layer
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.G2
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.F4

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.HardMathSupport.Lang.E6Descent
  CFSG.RankThree.Chevalley CFSG.HardMathSupport.Dickson.Sec6.I923
  CFSG.HardMathSupport.Solomon.UniquenessMaximal CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

section Entrywise


theorem noL34Layer_entrywise {τ : Tag} {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    (hs : IsSimpleGroup ↥(adjointGroup τ (fixSubfield σ)))
    (hnab : ∃ a b : ↥(adjointGroup τ (fixSubfield σ)), a * b ≠ b * a)
    (hL34 : ¬ IsLThreeFour ↥(adjointGroup τ (fixSubfield σ))) :
    NoL34Layer (entrywiseAdjointAut τ σ) := by
  obtain ⟨-, hinj, -, hJΓ, -, hJnorm, hquot⟩ :=
    Chevalley_coordinate_field_fixed_normal_subgroup τ K σ
  have hJC : fixedFieldImage τ σ ≤ adjointGroup τ K := fun x hx => (hJΓ hx).1
  let S : Subgroup ↥(adjointGroup τ K) := (fixedFieldImage τ σ).subgroupOf (adjointGroup τ K)
  let eJ : ↥(adjointGroup τ (fixSubfield σ)) ≃* ↥(fixedFieldImage τ σ) :=
    (adjointGroup τ (fixSubfield σ)).equivMapOfInjective _ hinj
  let e : ↥S ≃* ↥(adjointGroup τ (fixSubfield σ)) :=
    (Subgroup.subgroupOfEquivOfLe hJC).trans eJ.symm
  haveI : IsSimpleGroup ↥S := e.isSimpleGroup
  refine noL34_of_simple_normal_comm _ S ?_ ?_ inferInstance ?_ ?_
  · rw [fixSubgroup_entrywiseAdjointAut]
    intro x hx
    exact Subgroup.mem_subgroupOf.2 (hJΓ (Subgroup.mem_subgroupOf.1 hx))
  · rw [fixSubgroup_entrywiseAdjointAut]
    refine Subgroup.commutator_le.2 fun a ha b hb => ?_
    let N : Subgroup ↥(entrywiseFixedGroup τ σ) :=
      (fixedFieldImage τ σ).subgroupOf (entrywiseFixedGroup τ σ)
    have hcN : ∀ x y : ↥(entrywiseFixedGroup τ σ), ⁅x, y⁆ ∈ N := by
      intro x y
      have h : (QuotientGroup.mk' N) ⁅x, y⁆ = 1 := by
        rw [map_commutatorElement]
        exact commutatorElement_eq_one_iff_mul_comm.2 (hquot _ _)
      exact (QuotientGroup.eq_one_iff _).1 h
    have h1 := hcN ⟨(a : ModGL τ K), Subgroup.mem_subgroupOf.1 ha⟩
      ⟨(b : ModGL τ K), Subgroup.mem_subgroupOf.1 hb⟩
    rw [Subgroup.mem_subgroupOf] at h1 ⊢
    simpa [commutatorElement_def] using h1
  · obtain ⟨a, b, hab⟩ := hnab
    exact ⟨e.symm a, e.symm b, fun h => hab (e.symm.injective (by simpa using h))⟩
  · intro hT
    exact hL34 (IsLThreeFour.of_mulEquiv e hT)

theorem noL34Layer_entrywise_of_model
    (hO : ComponentClassification.CatLeaf.LieOrderFormulasInput) {τ : Tag}
    {t : StatedLieTag} {K : Type} [Field K] [Finite K] (σ : K ≃+* K) {ℓ d : ℕ} (hℓ : ℓ ≠ 2)
    (hX : LieModel ↥(adjointGroup τ (fixSubfield σ)) t 0 ℓ d)
    (hs : IsSimpleGroup ↥(adjointGroup τ (fixSubfield σ)))
    (hnab : ∃ a b : ↥(adjointGroup τ (fixSubfield σ)), a * b ≠ b * a) :
    NoL34Layer (entrywiseAdjointAut τ σ) :=
  noL34Layer_entrywise σ hs hnab (not_isLThreeFour_of_lieModel_odd hO hℓ hX)

end Entrywise

section G2


theorem noL34OuterAt_g2 (hO : ComponentClassification.CatLeaf.LieOrderFormulasInput) :
    NoL34OuterAt FamG2 := by
  intro P _ _ t n p f hadm ht hF hp5 hm ψ hψ3 hψ
  have hp2 : p ≠ 2 := by omega
  obtain rfl := hF
  haveI : Fact p.Prime := ⟨hadm.1⟩
  have hf : 1 ≤ f := hadm.2.1
  have hU : UntwistedChevalleyModel P .G2 (p ^ f) := by
    rcases hm with ⟨ht', -⟩ | ⟨-, -, hE⟩ | ⟨-, ht', -⟩ | ⟨-, ht', -⟩
    · exact absurd ht' (by decide)
    · exact hE.2
    · exact absurd ht' (by decide)
    · exact absurd ht' (by decide)
  obtain ⟨F, hFf, hFin, hFcard, ⟨θ⟩⟩ := exists_equiv_adjointGroup_of_untwisted hU
  have hβ3 : MulAut.congr θ ψ ^ 3 = 1 := by rw [← map_pow, hψ3, map_one]
  have hβinn : MulAut.congr θ ψ ∉ inner ↥(adjointGroup Tag.G2 F) := fun hin =>
    hψ ((congr_mem_inner_iff_of_equiv θ ψ).mp hin)
  obtain ⟨d, T, δ, hfd, hTo, hTc, hδ⟩ :=
    G2_descent hadm.1 hf hadm.2.2.2 F hFcard _ hβ3 hβinn
  refine noL34Layer_congr θ (noL34Layer_of_conj_pow (r := 1) (j := 1) (by simp)
    (by simpa using hδ) ?_)
  have hd : 1 ≤ d := by omega
  haveI : Finite ↥(fixSubfield T) := Subtype.finite
  have h3 : 3 ≤ p ^ d := by
    have h2 := hadm.1.two_le
    have : 3 ≤ p := by omega
    exact this.trans (Nat.le_self_pow (by omega) p)
  have hM : ChevalleyExceptionalModel ↥(adjointGroup Tag.G2 ↥(fixSubfield T)) .G2 p d :=
    ⟨⟨hadm.1, hd, rfl, h3⟩, untwisted_adjointGroup hTc⟩
  obtain ⟨hnt, hsimp⟩ := CFSG.LieType.Simplicity.fam_g2_simplicity _ p d hM
  have hZ : Subgroup.center ↥(adjointGroup Tag.G2 ↥(fixSubfield T)) = ⊥ :=
    center_adjointGroup_eq_bot
  exact noL34Layer_entrywise_of_model hO T hp2 (Or.inr (Or.inl ⟨rfl, by decide, hM⟩))
    hsimp (exists_noncomm_of_center_bot hZ)

end G2

section F4


theorem noL34OuterAt_f4 (hO : ComponentClassification.CatLeaf.LieOrderFormulasInput) :
    NoL34OuterAt FamF4 := by
  intro P _ _ t n p f hadm ht hF hp5 hm ψ hψ3 hψ
  have hp2 : p ≠ 2 := by omega
  obtain rfl := hF
  haveI : Fact p.Prime := ⟨hadm.1⟩
  have hf : 1 ≤ f := hadm.2.1
  have hU : UntwistedChevalleyModel P .F4 (p ^ f) := by
    rcases hm with ⟨ht', -⟩ | ⟨-, -, hE⟩ | ⟨-, ht', -⟩ | ⟨-, ht', -⟩
    · exact absurd ht' (by decide)
    · exact hE.2
    · exact absurd ht' (by decide)
    · exact absurd ht' (by decide)
  obtain ⟨F, hFf, hFin, hFcard, ⟨θ⟩⟩ := exists_equiv_adjointGroup_of_untwisted hU
  have hβ3 : MulAut.congr θ ψ ^ 3 = 1 := by rw [← map_pow, hψ3, map_one]
  have hβinn : MulAut.congr θ ψ ∉ inner ↥(adjointGroup Tag.F4 F) := fun hin =>
    hψ ((congr_mem_inner_iff_of_equiv θ ψ).mp hin)
  obtain ⟨d, T, δ, hfd, hTo, hTc, hδ⟩ := F4_descent hf F hFcard _ hβ3 hβinn
  refine noL34Layer_congr θ (noL34Layer_of_conj_pow (r := 1) (j := 1) (by simp)
    (by simpa using hδ) ?_)
  have hd : 1 ≤ d := by omega
  haveI : Finite ↥(fixSubfield T) := Subtype.finite
  have h3 : 3 ≤ p ^ d := by
    have h2 := hadm.1.two_le
    have : 3 ≤ p := by omega
    exact this.trans (Nat.le_self_pow (by omega) p)
  have hM : ChevalleyExceptionalModel ↥(adjointGroup Tag.F4 ↥(fixSubfield T)) .F4 p d :=
    ⟨⟨hadm.1, hd, rfl⟩, untwisted_adjointGroup hTc⟩
  obtain ⟨hnt, hsimp⟩ := CFSG.LieType.Simplicity.fam_f4_simplicity _ p d hM
  have hZ : Subgroup.center ↥(adjointGroup Tag.F4 ↥(fixSubfield T)) = ⊥ :=
    center_adjointGroup_eq_bot
  exact noL34Layer_entrywise_of_model hO T hp2 (Or.inr (Or.inl ⟨rfl, by decide, hM⟩))
    hsimp (exists_noncomm_of_center_bot hZ)

end F4

section E7


theorem noL34OuterAt_e7 (hO : ComponentClassification.CatLeaf.LieOrderFormulasInput) :
    NoL34OuterAt FamE7 := by
  intro P _ _ t n p f hadm ht hF hp5 hm ψ hψ3 hψ
  have hp2 : p ≠ 2 := by omega
  obtain rfl := hF
  haveI : Fact p.Prime := ⟨hadm.1⟩
  have hf : 1 ≤ f := hadm.2.1
  have hU : UntwistedChevalleyModel P .E7 (p ^ f) := by
    rcases hm with ⟨ht', -⟩ | ⟨-, -, hE⟩ | ⟨-, ht', -⟩ | ⟨-, ht', -⟩
    · exact absurd ht' (by decide)
    · exact hE.2
    · exact absurd ht' (by decide)
    · exact absurd ht' (by decide)
  obtain ⟨F, hFf, hFin, hFcard, ⟨θ⟩⟩ := exists_equiv_adjointGroup_of_untwisted hU
  have hβ3 : MulAut.congr θ ψ ^ 3 = 1 := by rw [← map_pow, hψ3, map_one]
  have hβinn : MulAut.congr θ ψ ∉ inner ↥(adjointGroup Tag.E7 F) := fun hin =>
    hψ ((congr_mem_inner_iff_of_equiv θ ψ).mp hin)
  have hdet : ¬ 3 ∣ Tag.E7.cartan.det.natAbs := by
    rw [det_cartan_E7]
    decide
  obtain ⟨d, T, r, j, δ, hfd, hTo, hTc, hrj, hδ⟩ :=
    exists_conj_entrywise_of_outer_E Tag.E7 (Or.inr (Or.inl rfl)) hf F hFcard Nat.prime_three
      (by norm_num) hdet _ hβ3 hβinn
  refine noL34Layer_congr θ (noL34Layer_of_conj_pow hrj hδ ?_)
  have hd : 1 ≤ d := by omega
  haveI : Finite ↥(fixSubfield T) := Subtype.finite
  have h3 : 3 ≤ p ^ d := by
    have h2 := hadm.1.two_le
    have : 3 ≤ p := by omega
    exact this.trans (Nat.le_self_pow (by omega) p)
  have hM : ChevalleyExceptionalModel ↥(adjointGroup Tag.E7 ↥(fixSubfield T)) .E7 p d :=
    ⟨⟨hadm.1, hd, rfl⟩, untwisted_adjointGroup hTc⟩
  obtain ⟨hnt, hsimp⟩ := CFSG.LieType.Simplicity.fam_e7_simplicity _ p d hM
  have hZ : Subgroup.center ↥(adjointGroup Tag.E7 ↥(fixSubfield T)) = ⊥ :=
    center_adjointGroup_eq_bot
  exact noL34Layer_entrywise_of_model hO T hp2 (Or.inr (Or.inl ⟨rfl, by decide, hM⟩))
    hsimp (exists_noncomm_of_center_bot hZ)

end E7

section E8


theorem noL34OuterAt_e8 (hO : ComponentClassification.CatLeaf.LieOrderFormulasInput) :
    NoL34OuterAt FamE8 := by
  intro P _ _ t n p f hadm ht hF hp5 hm ψ hψ3 hψ
  have hp2 : p ≠ 2 := by omega
  obtain rfl := hF
  haveI : Fact p.Prime := ⟨hadm.1⟩
  have hf : 1 ≤ f := hadm.2.1
  have hU : UntwistedChevalleyModel P .E8 (p ^ f) := by
    rcases hm with ⟨ht', -⟩ | ⟨-, -, hE⟩ | ⟨-, ht', -⟩ | ⟨-, ht', -⟩
    · exact absurd ht' (by decide)
    · exact hE.2
    · exact absurd ht' (by decide)
    · exact absurd ht' (by decide)
  obtain ⟨F, hFf, hFin, hFcard, ⟨θ⟩⟩ := exists_equiv_adjointGroup_of_untwisted hU
  have hβ3 : MulAut.congr θ ψ ^ 3 = 1 := by rw [← map_pow, hψ3, map_one]
  have hβinn : MulAut.congr θ ψ ∉ inner ↥(adjointGroup Tag.E8 F) := fun hin =>
    hψ ((congr_mem_inner_iff_of_equiv θ ψ).mp hin)
  have hdet : ¬ 3 ∣ Tag.E8.cartan.det.natAbs := by
    rw [det_cartan_E8]
    decide
  obtain ⟨d, T, r, j, δ, hfd, hTo, hTc, hrj, hδ⟩ :=
    exists_conj_entrywise_of_outer_E Tag.E8 (Or.inr (Or.inr rfl)) hf F hFcard Nat.prime_three
      (by norm_num) hdet _ hβ3 hβinn
  refine noL34Layer_congr θ (noL34Layer_of_conj_pow hrj hδ ?_)
  have hd : 1 ≤ d := by omega
  haveI : Finite ↥(fixSubfield T) := Subtype.finite
  have h3 : 3 ≤ p ^ d := by
    have h2 := hadm.1.two_le
    have : 3 ≤ p := by omega
    exact this.trans (Nat.le_self_pow (by omega) p)
  have hM : ChevalleyExceptionalModel ↥(adjointGroup Tag.E8 ↥(fixSubfield T)) .E8 p d :=
    ⟨⟨hadm.1, hd, rfl⟩, untwisted_adjointGroup hTc⟩
  obtain ⟨hnt, hsimp⟩ := CFSG.LieType.Simplicity.fam_e8_simplicity _ p d hM
  have hZ : Subgroup.center ↥(adjointGroup Tag.E8 ↥(fixSubfield T)) = ⊥ :=
    center_adjointGroup_eq_bot
  exact noL34Layer_entrywise_of_model hO T hp2 (Or.inr (Or.inl ⟨rfl, by decide, hM⟩))
    hsimp (exists_noncomm_of_center_bot hZ)

end E8

end CFSG.HardMathSupport.Dickson.Sec6
