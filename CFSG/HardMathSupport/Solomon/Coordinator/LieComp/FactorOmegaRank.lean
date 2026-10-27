module

import all CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorOmega
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Export
public import CFSG.LieType.Universal.Spin.Forms
public import CFSG.LieType.Universal.SymplecticRoots
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddQuadraticIsotropy
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveKernel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveSymplectic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFourNonsplitAction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFourSplitAction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixAction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsUnitary
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroAction
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSemilinearInvolution
public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.RankThree.Classical2

@[expose] def OrthFactorRank (ℓ q : ℕ) (X : Type) [Group X] : Prop :=
  (∃ (m j : ℕ) (E : Type) (_ : Field E) (_ : Fintype E), (m = 2 ∨ m = 4) ∧ 1 ≤ j ∧
      ringChar E = ℓ ∧ Fintype.card E = q ^ j ∧ (m = 2 → 4 ≤ Fintype.card E) ∧
      Nonempty (X ≃* Matrix.SpecialLinearGroup (Fin m) E))
  ∨ (∃ (j q' : ℕ) (E : Type) (_ : Field E) (_ : Fintype E), 1 ≤ j ∧
      ringChar E = ℓ ∧ q' = q ^ j ∧ Fintype.card E = q' ^ 2 ∧
      Nonempty (X ≃* ↥(CFSG.Open.StatedSU 4 q' E)))
  ∨ (∃ (K' : Type) (_ : Field K') (_ : Fintype K'), Nat.card K' = q ∧ ringChar K' = ℓ ∧
      ∃ s : ℕ, 2 ≤ s ∧ (s, Nat.card K') ≠ (2, 2) ∧
        Nonempty (X ≃* ↥(CFSG.Open.StatedSp s K')))
  ∨ (∃ (K' : Type) (_ : Field K') (_ : Fintype K') (V : Type) (_ : AddCommGroup V)
        (_ : Module K' V) (_ : FiniteDimensional K' V) (Q : QuadraticForm K' V),
      Nat.card K' = q ∧ ringChar K' = ℓ ∧ (QuadraticMap.polarBilin Q).Nondegenerate ∧
      7 ≤ Module.finrank K' V ∧
      (∃ U : Submodule K' V, Module.finrank K' U = 3 ∧ ∀ u ∈ U, Q u = 0) ∧
      Nonempty (X ≃* ↥(orthDerived Q)))

private theorem orthFactorRank_sl {ℓ q : ℕ} {X E : Type} [Field E] [Fintype E] [Group X]
    {m j : ℕ} (hm : m = 2 ∨ m = 4) (hj : 1 ≤ j) (hchar : ringChar E = ℓ)
    (hcard : Fintype.card E = q ^ j) (h4 : m = 2 → 4 ≤ Fintype.card E)
    (e : X ≃* Matrix.SpecialLinearGroup (Fin m) E) : OrthFactorRank ℓ q X :=
  Or.inl ⟨m, j, E, inferInstance, inferInstance, hm, hj, hchar, hcard, h4, ⟨e⟩⟩

private theorem orthFactorRank_su {ℓ q : ℕ} {X E : Type} [Field E] [Fintype E] [Group X]
    {j q' : ℕ} (hj : 1 ≤ j) (hchar : ringChar E = ℓ) (hq' : q' = q ^ j)
    (hcard : Fintype.card E = q' ^ 2)
    (e : X ≃* ↥(CFSG.Open.StatedSU 4 q' E)) : OrthFactorRank ℓ q X :=
  Or.inr (Or.inl ⟨j, q', E, inferInstance, inferInstance, hj, hchar, hq', hcard, ⟨e⟩⟩)

private theorem orthFactorRank_sp {ℓ q : ℕ} {X K' : Type} [Field K'] [Fintype K'] [Group X]
    (hK : Nat.card K' = q) (hchar : ringChar K' = ℓ) {s : ℕ} (hs : 2 ≤ s)
    (hne : (s, Nat.card K') ≠ (2, 2)) (e : X ≃* ↥(CFSG.Open.StatedSp s K')) :
    OrthFactorRank ℓ q X :=
  Or.inr (Or.inr (Or.inl ⟨K', inferInstance, inferInstance, hK, hchar, s, hs, hne, ⟨e⟩⟩))

private theorem orthFactorRank_orth {ℓ q : ℕ} {X K' : Type} [Field K'] [Fintype K'] [Group X]
    {V : Type} [AddCommGroup V] [Module K' V] [FiniteDimensional K' V]
    {Q : QuadraticForm K' V} (hK : Nat.card K' = q) (hchar : ringChar K' = ℓ)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hd : 7 ≤ Module.finrank K' V)
    (hT : ∃ U : Submodule K' V, Module.finrank K' U = 3 ∧ ∀ u ∈ U, Q u = 0)
    (e : X ≃* ↥(orthDerived Q)) : OrthFactorRank ℓ q X :=
  Or.inr (Or.inr (Or.inr ⟨K', inferInstance, inferInstance, V, inferInstance, inferInstance,
    inferInstance, Q, hK, hchar, hQ, hd, hT, ⟨e⟩⟩))

namespace RankAux

private abbrev CoverRank (p q : ℕ) {G : Type} [Group G] (L : Subgroup G) : Prop :=
  ∃ (X : Type) (_ : Group X) (_ : Finite X), LieFactorData p X ∧ OrthFactorRank p q X ∧
    ∃ f : X →* ↥L, Function.Surjective f ∧ f.ker ≤ Subgroup.center X

private theorem coverRank_of_range {p q : ℕ} {G : Type} [Group G] {L : Subgroup G}
    (hL : CFSG.IsQuasisimple ↥L) {S : Type} [Group S] [Finite S]
    (hS : LieFactorData p S) (hSq : CFSG.IsQuasisimple S) (hfac : OrthFactorRank p q S)
    (ψ : S →* G) (hψ : ψ.range = L) : CoverRank p q L := by
  have hnt : ψ.range ≠ ⊥ := by
    rw [hψ]
    intro h
    have := CFSG.LocalCores.isQuasisimple_nontrivial hL
    rw [h] at this
    exact not_nontrivial_iff_subsingleton.mpr inferInstance this
  let f : S →* ↥L := (MulEquiv.subgroupCongr hψ).toMonoidHom.comp ψ.rangeRestrict
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨z, hz⟩ := ψ.rangeRestrict_surjective ((MulEquiv.subgroupCongr hψ).symm y)
    exact ⟨z, by simp [f, hz]⟩
  have hkerf : f.ker = ψ.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    change (MulEquiv.subgroupCongr hψ) (ψ.rangeRestrict x) = 1 ↔ ψ x = 1
    rw [MulEquiv.map_eq_one_iff]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have hker : f.ker ≤ Subgroup.center S := by
    rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups hSq
      (MonoidHom.normal_ker ψ).isSubnormal with h | h
    · exfalso
      apply hnt
      rw [eq_bot_iff]
      rintro _ ⟨x, rfl⟩
      exact Subgroup.mem_bot.mpr (MonoidHom.mem_ker.mp (h ▸ Subgroup.mem_top x))
    · rwa [hkerf]
  exact ⟨S, inferInstance, inferInstance, hS, hfac, f, hf, hker⟩

section Cases

variable {K : Type} [Field K] [Fintype K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

private theorem coverRank_of_phi {p q : ℕ} {L : Subgroup ↥(orthDerived Q)}
    (hL : CFSG.IsQuasisimple ↥L) {S : Type} [Group S] [Finite S]
    (hS : LieFactorData p S) (hSq : CFSG.IsQuasisimple S) (hfac : OrthFactorRank p q S)
    (φ : S →* ↥(TauCeti.QuadraticMap.orthogonalGroup Q))
    (h : φ.range = L.map (OmegaAux.ιO Q)) : CoverRank p q L := by
  obtain ⟨ψ, hψ⟩ := OmegaAux.exists_lift_of_range_eq φ L h
  exact coverRank_of_range hL hS hSq hfac ψ hψ

open CFSG.ComponentClassification CFSG.ComponentClassification.CatLeafProof
  CFSG.ComponentClassification.CatalogueBOrthogonal CFSG.LocalAnalysis.ComponentInitial in
private theorem rank_case_three (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hd : Module.finrank K V = 3) (L : Subgroup ↥(orthDerived Q)) (hLn : L.Normal)
    (hL : CFSG.IsQuasisimple ↥L) : CoverRank (ringChar K) (Nat.card K) L := by
  have h2 : ringChar K ≠ 2 := OmegaAux.A.ringChar_ne_two_of_finrank_odd hQ (by rw [hd]; decide)
  have hodd : Odd (Nat.card K) := CFSG.GroupTheory.WeirSylow.odd_card_of_ringChar_ne_two h2
  have hK2 : Nat.card K ≠ 2 := fun h => absurd (h ▸ hodd) (by decide)
  have hM : CFSG.IsComponent (L.map (OmegaAux.ιO Q)) := OmegaAux.isComponent_map_ιO Q hL
  by_cases hK3 : Nat.card K = 3
  · have := ((CatalogueBOrthogonalLowDimensionFrontiers.orthogonal_three_p_components_frontier
      hodd Q hQ hd).2 hK3).1
    exact (not_isComponent_of_isSolvable hM).elim
  obtain ⟨-, -, e', -, -, hcomm, hq, -⟩ := orthogonal_three_derived hodd hK3 Q hQ hd
  have hMeq := eq_commutator_of_isComponent hq hM
  have h1 : 1 < Nat.card K := Finite.one_lt_card
  have h4 : 4 ≤ Fintype.card K := by rw [← Nat.card_eq_fintype_card]; omega
  exact coverRank_of_phi hL (slFactorFacts_holds K 2 le_rfl (fun _ => h4))
    (CatalogueBGeneralLinear.specialLinear_quasisimple 2 K le_rfl (Or.inr hK2) (Or.inr hK3))
    (orthFactorRank_sl (ℓ := ringChar K) (q := Nat.card K) (E := K) (m := 2) (j := 1)
      (Or.inl rfl) le_rfl rfl (by rw [pow_one, Nat.card_eq_fintype_card]) (fun _ => h4)
      (MulEquiv.refl _))
    (e'.symm.toMonoidHom.comp (traceZeroOrthogonalAction.comp
      (Matrix.SpecialLinearGroup.toGL : Matrix.SpecialLinearGroup (Fin 2) K →* _)))
    (by rw [OmegaAux.A.range_comp_symm]; exact (hMeq.trans hcomm).symm)

open CFSG.ComponentClassification CFSG.ComponentClassification.CatLeafProof
  CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit CFSG.LocalAnalysis.ComponentInitial in
private theorem rank_case_four_split (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hd : Module.finrank K V = 4)
    (hS : ∃ S : Submodule K V, Module.finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0)
    (L : Subgroup ↥(orthDerived Q)) (hLn : L.Normal) (hL : CFSG.IsQuasisimple ↥L) :
    CoverRank (ringChar K) (Nat.card K) L := by
  have hM : CFSG.IsComponent (L.map (OmegaAux.ιO Q)) := OmegaAux.isComponent_map_ιO Q hL
  by_cases hK : Nat.card K = 2 ∨ Nat.card K = 3
  · haveI := OmegaAux.A.isSolvable_orthogonalGroup_of_smallFixedException Q hQ (by omega)
      (Or.inr ⟨⟨hd, hS⟩, hK⟩)
    exact (not_isComponent_of_isSolvable hM).elim
  push Not at hK
  obtain ⟨hK2, hK3⟩ := hK
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have : Finite ↥(TauCeti.QuadraticMap.orthogonalGroup Q) := inferInstance
  obtain ⟨-, e', -, -, hsup, hq₁, hq₂, hn₁, hn₂, -, -, -⟩ :=
    orthogonal_split_four_derived hK2 hK3 Q hQ hd hS
  have hMD : L.map (OmegaAux.ιO Q) ≤ commutator (TauCeti.QuadraticMap.orthogonalGroup Q) := by
    rw [← OmegaAux.range_ιO]
    exact Subgroup.map_le_range _ _
  have h1 : 1 < Nat.card K := Finite.one_lt_card
  have h4 : 4 ≤ Fintype.card K := by rw [← Nat.card_eq_fintype_card]; omega
  have hSL := CatalogueBGeneralLinear.specialLinear_quasisimple 2 K le_rfl (Or.inr hK2)
    (Or.inr hK3)
  rcases CatLeafProof.eq_or_eq_of_isComponent_le_sup hsup hq₁ hq₂ hn₁ hn₂ hM hMD with h | h
  · exact coverRank_of_phi hL (slFactorFacts_holds K 2 le_rfl (fun _ => h4)) hSL
      (orthFactorRank_sl (ℓ := ringChar K) (q := Nat.card K) (E := K) (m := 2) (j := 1)
        (Or.inl rfl) le_rfl rfl (by rw [pow_one, Nat.card_eq_fintype_card]) (fun _ => h4)
        (MulEquiv.refl _))
      (e'.symm.toMonoidHom.comp ((specialRho (K := K)).comp (MonoidHom.inl _ _)))
      (by rw [OmegaAux.A.range_comp_symm]; exact h.symm)
  · exact coverRank_of_phi hL (slFactorFacts_holds K 2 le_rfl (fun _ => h4)) hSL
      (orthFactorRank_sl (ℓ := ringChar K) (q := Nat.card K) (E := K) (m := 2) (j := 1)
        (Or.inl rfl) le_rfl rfl (by rw [pow_one, Nat.card_eq_fintype_card]) (fun _ => h4)
        (MulEquiv.refl _))
      (e'.symm.toMonoidHom.comp ((specialRho (K := K)).comp (MonoidHom.inr _ _)))
      (by rw [OmegaAux.A.range_comp_symm]; exact h.symm)

open CFSG.ComponentClassification CFSG.ComponentClassification.CatLeafProof
  CFSG.ComponentClassification.CatalogueBOrthogonalFourNonsplit
  CFSG.LocalAnalysis.ComponentInitial in
private theorem rank_case_four_nonsplit_odd (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hd : Module.finrank K V = 4) (h2 : ringChar K ≠ 2)
    (hno : ¬ ∃ S : Submodule K V, Module.finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0)
    (L : Subgroup ↥(orthDerived Q)) (hLn : L.Normal) (hL : CFSG.IsQuasisimple ↥L) :
    CoverRank (ringChar K) (Nat.card K) L := by
  have hodd : Odd (Nat.card K) := CFSG.GroupTheory.WeirSylow.odd_card_of_ringChar_ne_two h2
  have h2' := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  have hM : CFSG.IsComponent (L.map (OmegaAux.ιO Q)) := OmegaAux.isComponent_map_ιO Q hL
  obtain ⟨δ, hns, -, -, e', -, -, hcomm, hq, -⟩ :=
    orthogonal_nonsplit_four_derived hodd Q hQ hd hno
  have : Fact (¬ IsSquare (δ : K)) := ⟨hns⟩
  have : Finite (extension (δ : K)) :=
    Finite.of_equiv (K × K) (QuadraticAlgebra.equivProd (δ : K) 0).symm
  letI : Fintype (extension (δ : K)) := Fintype.ofFinite _
  have hMeq := eq_commutator_of_isComponent hq hM
  have hcard := extension_card (δ : K)
  have h1 : 1 < Nat.card K := Finite.one_lt_card
  have hE2 : Nat.card (extension (δ : K)) ≠ 2 := by
    rw [hcard]
    nlinarith
  have hE3 : Nat.card (extension (δ : K)) ≠ 3 := by
    rw [hcard]
    nlinarith
  have hE4 : 4 ≤ Fintype.card (extension (δ : K)) := by
    rw [← Nat.card_eq_fintype_card, hcard]
    nlinarith
  have hchar : ringChar (extension (δ : K)) = ringChar K := OmegaAux.A.ringChar_eq_of_algebra
  have hS : LieFactorData (ringChar K) (Matrix.SpecialLinearGroup (Fin 2) (extension (δ : K))) :=
    hchar ▸ slFactorFacts_holds (extension (δ : K)) 2 le_rfl (fun _ => hE4)
  exact coverRank_of_phi hL hS
    (CatalogueBGeneralLinear.specialLinear_quasisimple 2 (extension (δ : K)) le_rfl
      (Or.inr hE2) (Or.inr hE3))
    (orthFactorRank_sl (ℓ := ringChar K) (q := Nat.card K) (E := extension (δ : K)) (m := 2)
      (j := 2) (Or.inl rfl) (by norm_num) hchar
      (by rw [← Nat.card_eq_fintype_card]; exact hcard) (fun _ => hE4) (MulEquiv.refl _))
    (e'.symm.toMonoidHom.comp (specialRho (δ : K) h2'))
    (by rw [OmegaAux.A.range_comp_symm]; exact (hMeq.trans hcomm).symm)

open CFSG.ComponentClassification CFSG.ComponentClassification.CatLeafProof
  CFSG.ComponentClassification.CatalogueBOrthogonalFive CFSG.LocalAnalysis.ComponentInitial in
private theorem rank_case_five (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hd : Module.finrank K V = 5) (L : Subgroup ↥(orthDerived Q)) (hLn : L.Normal)
    (hL : CFSG.IsQuasisimple ↥L) : CoverRank (ringChar K) (Nat.card K) L := by
  have h2 : ringChar K ≠ 2 := OmegaAux.A.ringChar_ne_two_of_finrank_odd hQ (by rw [hd]; decide)
  have hodd : Odd (Nat.card K) := CFSG.GroupTheory.WeirSylow.odd_card_of_ringChar_ne_two h2
  have h2' := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  have hM : CFSG.IsComponent (L.map (OmegaAux.ιO Q)) := OmegaAux.isComponent_map_ιO Q hL
  obtain ⟨-, -, e', -, -, hcomm, hq, -⟩ := orthogonal_five_derived hodd Q hQ hd
  have hMeq := eq_commutator_of_isComponent hq hM
  let eSp : (symplecticMultiplier (K := K)).ker ≃* ↥(CFSG.Open.StatedSp 2 K) :=
    symplecticKernelEquivFin.trans (CFSG.LieType.Universal.Symplectic.equivStatedSp 2 K)
  have hne : (2, Fintype.card K) ≠ (2, 2) := fun h => by
    have h' : Fintype.card K = 2 := (Prod.mk.inj h).2
    rw [← Nat.card_eq_fintype_card] at h'
    exact absurd (h' ▸ hodd) (by decide)
  have hSq : CFSG.IsQuasisimple ↥(CFSG.Open.StatedSp 2 K) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv eSp (symplecticKernel_quasisimple hodd)
  exact coverRank_of_phi hL (spFactorFacts_holds K 2 le_rfl hne) hSq
    (orthFactorRank_sp (ℓ := ringChar K) (q := Nat.card K) (K' := K) rfl rfl (s := 2) le_rfl
      (by simpa [Nat.card_eq_fintype_card] using hne) (MulEquiv.refl _))
    (e'.symm.toMonoidHom.comp ((selfAdjointSymplecticAction h2').comp eSp.symm.toMonoidHom))
    (by
      rw [OmegaAux.A.range_comp_symm, MonoidHom.range_comp,
        MonoidHom.range_eq_top.mpr eSp.symm.surjective, ← MonoidHom.range_eq_map]
      exact (hMeq.trans hcomm).symm)

open CFSG.ComponentClassification CFSG.ComponentClassification.CatLeafProof
  CFSG.ComponentClassification.CatalogueBOrthogonalFourNonsplit
  CFSG.ComponentClassification.CatalogueBOrthogonalSix CFSG.LocalAnalysis.ComponentInitial in
private theorem rank_case_six_nonsplit_odd (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hd : Module.finrank K V = 6) (h2 : ringChar K ≠ 2)
    (hno : ¬ ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (L : Subgroup ↥(orthDerived Q)) (hLn : L.Normal) (hL : CFSG.IsQuasisimple ↥L) :
    CoverRank (ringChar K) (Nat.card K) L := by
  have hodd : Odd (Nat.card K) := CFSG.GroupTheory.WeirSylow.odd_card_of_ringChar_ne_two h2
  have h2' := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  have hM : CFSG.IsComponent (L.map (OmegaAux.ιO Q)) := OmegaAux.isComponent_map_ιO Q hL
  obtain ⟨δ, hfact, -, -, e', -, -, hcomm, hq, -⟩ :=
    orthogonal_nonsplit_six_derived hodd Q hQ hd hno
  have : Finite (extension (δ : K)) :=
    Finite.of_equiv (K × K) (QuadraticAlgebra.equivProd (δ : K) 0).symm
  letI : Fintype (extension (δ : K)) := Fintype.ofFinite _
  have hMeq := eq_commutator_of_isComponent hq hM
  obtain ⟨eU⟩ := exists_six_special_unitary_equiv (δ : K) h2'
  obtain ⟨n, hp, hn⟩ := FiniteField.card K (ringChar K)
  have he : 1 ≤ (n : ℕ) := n.pos
  have hK : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hn
  have hcardE : Nat.card (extension (δ : K)) = ringChar K ^ (2 * (n : ℕ)) := by
    rw [extension_card, hK, ← pow_mul, mul_comm]
  have hU : UnitaryFieldData (ringChar K) (n : ℕ) (extension (δ : K)) := ⟨hp, he, hcardE⟩
  have : Fact (ringChar K).Prime := ⟨hp⟩
  have : CharP (extension (δ : K)) (ringChar K) := hU.charP
  have hF : Nat.card (extension (δ : K)) = (ringChar K ^ (n : ℕ)) ^ 2 := by
    rw [hcardE, ← pow_mul, mul_comm]
  have hσ2 : (conjugation (δ : K)).toRingEquiv * (conjugation (δ : K)).toRingEquiv = 1 := by
    rw [← pow_two]
    exact conjugation_square (δ : K)
  have hconj : (conjugation (δ : K)).toRingEquiv =
      CFSG.LieType.BorelTits.unitaryInvolution (extension (δ : K)) (ringChar K) (n : ℕ) := by
    rcases UnitaryHigher.ringEquiv_eq_refl_or_bar hU hσ2 with h | h
    · exact absurd h (conjugation_ne_one (δ : K) h2')
    · exact RingEquiv.ext fun c =>
        (h c).trans (CFSG.LieType.BorelTits.unitaryInvolution_apply _ (ringChar K) (n : ℕ) c).symm
  have hSU : CFSG.LieType.Universal.Unitary.SUid (conjugation (δ : K)).toRingEquiv 4 =
      CFSG.Open.StatedSU 4 (ringChar K ^ (n : ℕ)) (extension (δ : K)) := by
    rw [hconj]
    exact CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hF 4
  have hq2 : 2 ≤ ringChar K ^ (n : ℕ) := hp.two_le.trans (Nat.le_self_pow (by omega) _)
  have hnq : ((4 : ℕ), ringChar K ^ (n : ℕ)) ≠ (3, 2) := fun h => by
    have := (Prod.mk.inj h).1
    omega
  have hFc : Fintype.card (extension (δ : K)) = (ringChar K ^ (n : ℕ)) ^ 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact hF
  obtain ⟨hSq, -⟩ := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hF
    (by norm_num) hnq
  let eSU := eU.trans (MulEquiv.subgroupCongr hSU)
  have hchar : ringChar (extension (δ : K)) = ringChar K := OmegaAux.A.ringChar_eq_of_algebra
  have hS : LieFactorData (ringChar K)
      ↥(CFSG.Open.StatedSU 4 (ringChar K ^ (n : ℕ)) (extension (δ : K))) :=
    hchar ▸ suFactorFacts_holds (extension (δ : K)) 4 (ringChar K ^ (n : ℕ)) hFc
      (by norm_num) hnq
  exact coverRank_of_phi hL hS hSq
    (orthFactorRank_su (ℓ := ringChar K) (q := Nat.card K) (E := extension (δ : K))
      (j := 1) (q' := ringChar K ^ (n : ℕ)) le_rfl hchar
      (by rw [pow_one, ← hK]) hFc (MulEquiv.refl _))
    (e'.symm.toMonoidHom.comp ((sixSpecialKappa (δ : K) h2').comp eSU.symm.toMonoidHom))
    (by
      rw [OmegaAux.A.range_comp_symm, MonoidHom.range_comp,
        MonoidHom.range_eq_top.mpr eSU.symm.surjective, ← MonoidHom.range_eq_map]
      exact (hMeq.trans hcomm).symm)

open CFSG.ComponentClassification CFSG.ComponentClassification.CatLeafProof
  CFSG.ComponentClassification.CatLeafProof.KleinSix CFSG.ClassicalGroups.Orthogonal
  CFSG.LieType.Universal.Spin in
private theorem rank_case_six_split_odd (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hd : Module.finrank K V = 6) (h2 : ringChar K ≠ 2)
    (hT : ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (L : Subgroup ↥(orthDerived Q)) (hLn : L.Normal) (hL : CFSG.IsQuasisimple ↥L) :
    CoverRank (ringChar K) (Nat.card K) L := by
  have hodd : Odd (Nat.card K) := CFSG.GroupTheory.WeirSylow.odd_card_of_ringChar_ne_two h2
  have h2' := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  have hqs : CFSG.IsQuasisimple ↥(orthDerived Q) :=
    CFSG.RankThree.PartOne.KCOrthogonal.isQuasisimple_orthDerived hQ hT
  have hLtop : L = ⊤ := OmegaAux.eq_top_of_isQuasisimple hqs hLn hL
  obtain ⟨e⟩ := CFSG.RankThree.PartOne.K159.Klein.exists_isometry_quadPlus_three Q hQ hd hT
  let e1 := CFSG.RankThree.PartOne.orthDerivedEquiv e
  have hrange := OmegaAux.A.rhoGL_range_eq_orthDerived (K := K) h2'
  let ρ' : Matrix.SpecialLinearGroup (Fin 4) K →* ↥(orthDerived (quadPlus 3 K)) :=
    (rhoGL (K := K)).codRestrict _ (fun g => by rw [← hrange]; exact ⟨g, rfl⟩)
  have hρ' : Function.Surjective ρ' := by
    intro y
    have : (y : (Fin 3 ⊕ Fin 3 → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 → K)) ∈ (rhoGL (K := K)).range := by
      rw [hrange]
      exact y.2
    obtain ⟨g, hg⟩ := this
    exact ⟨g, Subtype.ext hg⟩
  let ψ : Matrix.SpecialLinearGroup (Fin 4) K →* ↥(orthDerived Q) := e1.symm.toMonoidHom.comp ρ'
  have hψ : ψ.range = L := by
    rw [hLtop]
    exact MonoidHom.range_eq_top.mpr (e1.symm.surjective.comp hρ')
  have hS4 := CatalogueBGeneralLinear.specialLinear_quasisimple 4 K (by norm_num)
    (Or.inl (by norm_num)) (Or.inl (by norm_num))
  exact coverRank_of_range hL
    (slFactorFacts_holds K 4 (by norm_num) (fun h => absurd h (by norm_num))) hS4
    (orthFactorRank_sl (ℓ := ringChar K) (q := Nat.card K) (E := K) (m := 4) (j := 1)
      (Or.inr rfl) le_rfl rfl (by rw [pow_one, Nat.card_eq_fintype_card])
      (fun h => absurd h (by norm_num)) (MulEquiv.refl _)) ψ hψ

private theorem coverRank_of_orthDerived_mulEquiv {p q : ℕ} {S : Type} [Group S] [Finite S]
    (e : S ≃* ↥(orthDerived Q)) (L : Subgroup ↥(orthDerived Q)) (hLn : L.Normal)
    (hL : CFSG.IsQuasisimple ↥L) (hS : LieFactorData p S) (hSq : CFSG.IsQuasisimple S)
    (hfac : OrthFactorRank p q S) : CoverRank p q L := by
  have hqs : CFSG.IsQuasisimple ↥(orthDerived Q) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e hSq
  have hLtop : L = ⊤ := OmegaAux.eq_top_of_isQuasisimple hqs hLn hL
  refine coverRank_of_range hL hS hSq hfac e.toMonoidHom ?_
  rw [hLtop]
  exact MonoidHom.range_eq_top.mpr e.surjective

private theorem rank_case_four_nonsplit_even (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hd : Module.finrank K V = 4) (h2 : ringChar K = 2)
    (hno : ¬ ∃ S : Submodule K V, Module.finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0)
    (L : Subgroup ↥(orthDerived Q)) (hLn : L.Normal) (hL : CFSG.IsQuasisimple ↥L) :
    CoverRank (ringChar K) (Nat.card K) L := by
  haveI : CharP K 2 := ringChar.of_eq h2
  have hts : ∀ U : Submodule K V, Module.finrank K U = 2 → ∃ u ∈ U, Q u ≠ 0 := by
    intro U hU
    by_contra hcon
    push Not at hcon
    exact hno ⟨U, hU, hcon⟩
  obtain ⟨E, _, _, _, hE, ⟨e⟩⟩ :=
    CFSG.RankThree.PartOne.K159.exists_orthDerived_four_sl2 Q hQ hd hts
  haveI : Fintype E := Fintype.ofFinite E
  have hK2 : 2 ≤ Nat.card K := Nat.succ_le_of_lt Finite.one_lt_card
  have hE4 : 4 ≤ Nat.card E := by
    rw [hE]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ Nat.card K ^ 2 := Nat.pow_le_pow_left hK2 2
  have hEc : Fintype.card E = Nat.card E := Nat.card_eq_fintype_card.symm
  have hchar : ringChar E = ringChar K := by
    rw [h2]
    exact ringChar.eq E 2
  have hS : LieFactorData (ringChar K) (Matrix.SpecialLinearGroup (Fin 2) E) := by
    rw [← hchar]
    exact slFactorFacts_holds E 2 le_rfl (fun _ => by omega)
  have hSq : CFSG.IsQuasisimple (Matrix.SpecialLinearGroup (Fin 2) E) :=
    CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinear_quasisimple 2 E le_rfl
      (Or.inr (by omega)) (Or.inr (by omega))
  exact coverRank_of_orthDerived_mulEquiv e.symm L hLn hL hS hSq
    (orthFactorRank_sl (ℓ := ringChar K) (q := Nat.card K) (E := E) (m := 2) (j := 2)
      (Or.inl rfl) (by norm_num) hchar (by rw [← Nat.card_eq_fintype_card]; exact hE)
      (fun _ => by rw [← Nat.card_eq_fintype_card]; exact hE4) (MulEquiv.refl _))

private theorem rank_case_six_split_even (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hd : Module.finrank K V = 6) (h2 : ringChar K = 2)
    (hT : ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (L : Subgroup ↥(orthDerived Q)) (hLn : L.Normal) (hL : CFSG.IsQuasisimple ↥L) :
    CoverRank (ringChar K) (Nat.card K) L := by
  haveI : CharP K 2 := ringChar.of_eq h2
  obtain ⟨κ⟩ := OmegaAux.B.klein_commutator_orthogonal_six_of_charTwo Q hQ hd hT
  let e : ↥(orthDerived Q) ≃* Matrix.SpecialLinearGroup (Fin 4) K :=
    ((CFSG.RankThree.PartOne.orthDerivedEquivCommutator Q).symm.trans κ).trans
      (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 4 K).symm
  have hS : LieFactorData (ringChar K) (Matrix.SpecialLinearGroup (Fin 4) K) :=
    slFactorFacts_holds K 4 (by norm_num) (fun h => absurd h (by norm_num))
  have hSq : CFSG.IsQuasisimple (Matrix.SpecialLinearGroup (Fin 4) K) :=
    CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinear_quasisimple 4 K
      (by norm_num) (Or.inl (by norm_num)) (Or.inl (by norm_num))
  exact coverRank_of_orthDerived_mulEquiv e.symm L hLn hL hS hSq
    (orthFactorRank_sl (ℓ := ringChar K) (q := Nat.card K) (E := K) (m := 4) (j := 1)
      (Or.inr rfl) le_rfl rfl (by rw [pow_one, Nat.card_eq_fintype_card])
      (fun h => absurd h (by norm_num)) (MulEquiv.refl _))

private theorem rank_case_six_nonsplit_even (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hd : Module.finrank K V = 6) (h2 : ringChar K = 2)
    (hno : ¬ ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (L : Subgroup ↥(orthDerived Q)) (hLn : L.Normal) (hL : CFSG.IsQuasisimple ↥L) :
    CoverRank (ringChar K) (Nat.card K) L := by
  haveI : CharP K 2 := ringChar.of_eq h2
  have hts : ∀ U : Submodule K V, Module.finrank K U = 3 → ∃ u ∈ U, Q u ≠ 0 := by
    intro U hU
    by_contra hcon
    push Not at hcon
    exact hno ⟨U, hU, hcon⟩
  obtain ⟨E, _, _, D, ψ, hψ⟩ :=
    CFSG.RankThree.PartOne.KCOrthogonal.exists_evenMinus_model Q hQ (n := 3) (by norm_num)
      (by omega) hts
  haveI : CharP E 2 := CFSG.RankThree.PartOne.KCOrthogonal.charP_two_of_algebra (K := K)
  haveI := D.finite_E
  haveI : Fintype E := Fintype.ofFinite E
  let e1 : Q.IsometryEquiv (CFSG.RankThree.PartOne.KCOrthogonal.evenNormTailForm D.N 2) :=
    { toLinearEquiv := ψ
      map_app' := fun w => hψ w }
  let e2 : Q.IsometryEquiv D.sixForm := e1.trans D.sixIsometry
  obtain ⟨-, -, -, -, -, -, -, -, hinj, -, -, -, -, -, -, -, hcomm, -⟩ :=
    CFSG.RankThree.PartOne.even_minus_six_unitary_derived_model D
  have hrange : orthDerived D.sixForm = D.sixRho.range := hcomm
  let e3 : D.sixSU ≃* ↥(orthDerived D.sixForm) :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange.symm)
  obtain ⟨f, hU, hcard, hbar⟩ := D.exists_unitaryFieldData
  obtain ⟨e4⟩ := D.nonempty_sixSU_mulEquiv hU hbar
  let e5 : CFSG.Open.StatedSU 4 (2 ^ f) E ≃* ↥(orthDerived Q) :=
    e4.symm.trans (e3.trans (CFSG.RankThree.PartOne.orthDerivedEquiv e2).symm)
  haveI := OmegaAux.finite_orthDerived Q
  haveI : Finite ↥(CFSG.Open.StatedSU 4 (2 ^ f) E) := Finite.of_equiv _ e5.toEquiv.symm
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNat : Nat.card E = (2 ^ f) ^ 2 := by rw [D.card_E, hcard]
  have hF : Fintype.card E = (2 ^ f) ^ 2 := by rw [Nat.card_eq_fintype_card] at hNat; exact hNat
  have hnq : ((4 : ℕ), 2 ^ f) ≠ (3, 2) := by
    intro hh
    have := congrArg Prod.fst hh
    simp at this
  have hchar : ringChar E = ringChar K := by
    rw [h2]
    exact ringChar.eq E 2
  have hS : LieFactorData (ringChar K) ↥(CFSG.Open.StatedSU 4 (2 ^ f) E) := by
    rw [← hchar]
    exact suFactorFacts_holds E 4 (2 ^ f) hF (by norm_num) hnq
  have hSq : CFSG.IsQuasisimple ↥(CFSG.Open.StatedSU 4 (2 ^ f) E) :=
    (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hNat (by norm_num) hnq).1
  have hKf : Nat.card K = 2 ^ f := by
    have h1 : (2 ^ f) ^ 2 = Nat.card K ^ 2 := by rw [← hNat, D.card_E]
    exact (Nat.pow_left_injective (by norm_num) h1).symm
  exact coverRank_of_orthDerived_mulEquiv e5 L hLn hL hS hSq
    (orthFactorRank_su (ℓ := ringChar K) (q := Nat.card K) (E := E)
      (j := 1) (q' := 2 ^ f) le_rfl hchar (by rw [pow_one, ← hKf]) hF (MulEquiv.refl _))

end Cases

section Assembly

variable {K : Type} [Field K] [Fintype K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

private theorem rank_case_large (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hd : 7 ≤ Module.finrank K V) (L : Subgroup ↥(orthDerived Q)) (hLn : L.Normal)
    (hL : CFSG.IsQuasisimple ↥L) : CoverRank (ringChar K) (Nat.card K) L := by
  obtain ⟨T, hT3, hT⟩ := OmegaAux.C.large_exists_singular hQ hd
  have hqs : CFSG.IsQuasisimple ↥(orthDerived Q) :=
    CFSG.RankThree.PartOne.KCOrthogonal.isQuasisimple_orthDerived hQ ⟨T, hT3, hT⟩
  have hLtop : L = ⊤ := OmegaAux.eq_top_of_isQuasisimple hqs hLn hL
  haveI := OmegaAux.finite_orthDerived Q
  have hfd : LieFactorData (ringChar K) ↥(orthDerived Q) :=
    ⟨hqs.1.commutator_eq_top, OmegaAux.C.large_chev hQ hd, fun ⟨e⟩ =>
      ((OmegaAux.M.large_no_a6 hQ hd).false e).elim⟩
  exact coverRank_of_range hL hfd hqs
    (orthFactorRank_orth (ℓ := ringChar K) (q := Nat.card K) (K' := K) rfl rfl hQ hd
      ⟨T, hT3, hT⟩ (MulEquiv.refl _))
    (MonoidHom.id _) (by rw [MonoidHom.range_eq_top.mpr Function.surjective_id]; exact hLtop.symm)

private theorem omega_coverRank (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (L : Subgroup ↥(orthDerived Q)) (hLn : L.Normal) (hL : CFSG.IsQuasisimple ↥L) :
    CoverRank (ringChar K) (Nat.card K) L := by
  by_cases h2 : Module.finrank K V ≤ 2
  · exact (OmegaAux.M.case_le_two hQ h2 L hL).elim
  by_cases h3 : Module.finrank K V = 3
  · exact rank_case_three hQ h3 L hLn hL
  by_cases h4 : Module.finrank K V = 4
  · by_cases hS : ∃ S : Submodule K V, Module.finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0
    · exact rank_case_four_split hQ h4 hS L hLn hL
    · by_cases h2 : ringChar K = 2
      · exact rank_case_four_nonsplit_even hQ h4 h2 hS L hLn hL
      · exact rank_case_four_nonsplit_odd hQ h4 h2 hS L hLn hL
  by_cases h5 : Module.finrank K V = 5
  · exact rank_case_five hQ h5 L hLn hL
  by_cases h6 : Module.finrank K V = 6
  · by_cases hT : ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0
    · by_cases h2 : ringChar K = 2
      · exact rank_case_six_split_even hQ h6 h2 hT L hLn hL
      · exact rank_case_six_split_odd hQ h6 h2 hT L hLn hL
    · by_cases h2 : ringChar K = 2
      · exact rank_case_six_nonsplit_even hQ h6 h2 hT L hLn hL
      · exact rank_case_six_nonsplit_odd hQ h6 h2 hT L hLn hL
  exact rank_case_large hQ (by omega) L hLn hL

end Assembly

end RankAux

theorem omegaFactorRank_holds (K : Type) [Field K] [Fintype K] (V : Type) [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (Q : QuadraticForm K V)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (L : Subgroup ↥(orthDerived Q))
    (hLn : L.Normal) (hL : CFSG.IsQuasisimple ↥L) :
    ∃ (X : Type) (_ : Group X) (_ : Finite X),
      LieFactorData (ringChar K) X ∧ OrthFactorRank (ringChar K) (Nat.card K) X ∧
      ∃ f : X →* ↥L, Function.Surjective f ∧ f.ker ≤ Subgroup.center X := by
  exact RankAux.omega_coverRank (K := K) (V := V) (Q := Q) hQ L hLn hL

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp