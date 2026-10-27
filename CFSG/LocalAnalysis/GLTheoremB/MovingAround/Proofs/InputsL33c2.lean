module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.InputsL33c
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.InputsL33b
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.OrthInnerExport
import all CFSG.HardMathSupport.Solomon.Coordinator.LieComp.OrthInnerExport
import all CFSG.HardMathSupport.Solomon.Coordinator.LieComp.OrthFieldExport
import all CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorOmega
import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddOrthLow

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsL33c

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsL33 (isLpType_of_mulEquiv
  card_of_isLpType_three_three exists_card_eq_three_pow sl_l33 su_l33_false)

section Range

theorem not_isLpType_of_range {G : Type} [Group G] {L : Subgroup G} (hL : CFSG.IsQuasisimple ↥L)
    {S : Type} [Group S] (hSq : CFSG.IsQuasisimple S)
    (hS : ¬ IsLpType 3 3 (S ⧸ Subgroup.center S)) (ψ : S →* G) (hψ : ψ.range = L) :
    ¬ IsLpType 3 3 (↥L ⧸ Subgroup.center ↥L) := by
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
  exact not_isLpType_of_surj hSq.1.commutator_eq_top f hf hker hS

theorem not_isLpType_top {G : Type} [Group G] {L : Subgroup G} (hL : L = ⊤)
    (h : ¬ IsLpType 3 3 (G ⧸ Subgroup.center G)) : ¬ IsLpType 3 3 (↥L ⧸ Subgroup.center ↥L) := by
  subst hL
  let e : ↥(⊤ : Subgroup G) ≃* G := Subgroup.topEquiv
  exact fun hL => h (isLpType_of_mulEquiv
    (QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)).symm hL)

end Range

section Large

open CFSG.RankThree.Classical2 CFSG.HardMathSupport.Solomon.Coordinator.LieComp

variable {K : Type} [Field K] [Fintype K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem odd_case_contra_l33 {q a k W : ℕ} (hq : 3 ≤ q) (hqodd : Odd q) (ha : 6 ≤ a)
    (hdvd : q ^ a ∣ 2 ^ k * W) (hW : W ∣ 11232) : False := by
  have hcop : Nat.Coprime (q ^ a) (2 ^ k) := Nat.Coprime.pow _ _ (Nat.coprime_two_right.2 hqodd)
  have h1 : q ^ a ∣ W := hcop.dvd_of_dvd_mul_left hdvd
  have h2 : q ^ a ∣ 2 ^ 5 * 351 := by
    have : (11232 : ℕ) = 2 ^ 5 * 351 := by norm_num
    rw [← this]
    exact h1.trans hW
  have hcop2 : Nat.Coprime (q ^ a) (2 ^ 5) := Nat.Coprime.pow _ _ (Nat.coprime_two_right.2 hqodd)
  have h3 : q ^ a ∣ 351 := hcop2.dvd_of_dvd_mul_left h2
  have h4 : q ^ a ≤ 351 := Nat.le_of_dvd (by norm_num) h3
  have h5 : 3 ^ 6 ≤ q ^ a :=
    (Nat.pow_le_pow_left hq 6).trans (Nat.pow_le_pow_right (by omega) ha)
  norm_num at h5
  omega

theorem large_noL33 (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hodd : Odd (Nat.card K)) :
    ¬ IsLpType 3 3 (↥(orthDerived Q) ⧸ Subgroup.center ↥(orthDerived Q)) := by
  intro hL
  obtain ⟨-, hcenter, hZ2, -, -, hsq, -⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
  haveI := OmegaAux.finite_orthDerived Q
  set O := TauCeti.QuadraticMap.orthogonalGroup Q with hO
  have h5616 : Nat.card (↥(orthDerived Q) ⧸ Subgroup.center ↥(orthDerived Q)) = 5616 :=
    card_of_isLpType_three_three hL
  have hmul := (Subgroup.center ↥(orthDerived Q)).card_eq_card_quotient_mul_card_subgroup
  rw [h5616] at hmul
  have hz2 : Nat.card ↥(Subgroup.center ↥(orthDerived Q)) ≤ 2 := by rw [hcenter]; exact hZ2
  have hz0 : 0 < Nat.card ↥(Subgroup.center ↥(orthDerived Q)) := Nat.card_pos
  have hW : Nat.card ↥(orthDerived Q) ∣ 11232 := by
    rcases (show Nat.card ↥(Subgroup.center ↥(orthDerived Q)) = 1 ∨
        Nat.card ↥(Subgroup.center ↥(orthDerived Q)) = 2 by omega) with h | h
    · rw [hmul, h]
      norm_num
    · rw [hmul, h]
  have hsq' : ∀ g : ↥O, g ^ 2 ∈ commutator ↥O := by
    intro g
    rw [← OmegaAux.range_ιO]
    exact ⟨⟨(g : V ≃ₗ[K] V) ^ 2, hsq g g.2⟩, Subtype.ext rfl⟩
  have hp2 : IsPGroup 2 (↥O ⧸ commutator ↥O) :=
    CFSG.LocalAnalysis.ComponentInitial.isPGroup_two_of_forall_sq_mem hsq'
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite ↥O := by
    have : Finite V := Module.finite_of_finite K
    have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
      fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
    infer_instance
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp2
  have hN : Nat.card ↥O = 2 ^ k * Nat.card ↥(orthDerived Q) := by
    rw [(commutator ↥O).card_eq_card_quotient_mul_card_subgroup, hk]
    congr 1
    rw [← OmegaAux.range_ιO]
    exact (Nat.card_congr (MonoidHom.ofInjective (OmegaAux.ιO_injective Q)).toEquiv).symm
  have hq3 : 3 ≤ Nat.card K := by
    obtain ⟨t, ht⟩ := hodd
    have : 1 < Nat.card K := Finite.one_lt_card
    omega
  have hdim6 : 6 ≤ Module.finrank K V := by
    obtain ⟨T, hT3, hTQ⟩ := hT
    have := CFSG.ComponentClassification.UnbalancedCatalog.two_mul_finrank_le_of_singular hQ hTQ
    omega
  rcases Nat.even_or_odd (Module.finrank K V) with ⟨m, hm⟩ | ⟨m, hm⟩
  ·
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have hdim : Module.finrank K V = 2 * (m' + 1) := by omega
    have hm2 : 2 ≤ m' := by omega
    obtain ⟨ε, hε⟩ : ∃ ε : ℤ, (ε = 1 ∧ CFSG.GroupTheory.WeirSylow.IsPlusType Q) ∨
        (ε = -1 ∧ ¬ CFSG.GroupTheory.WeirSylow.IsPlusType Q) := by
      by_cases h : CFSG.GroupTheory.WeirSylow.IsPlusType Q
      · exact ⟨1, Or.inl ⟨rfl, h⟩⟩
      · exact ⟨-1, Or.inr ⟨rfl, h⟩⟩
    have hcard := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type hQ hdim hε
    have hdvdZ : ((Nat.card K : ℤ) ^ (m' * (m' + 1))) ∣ (Nat.card ↥O : ℤ) := by
      rw [hcard]
      exact Dvd.intro ((2 * ((Nat.card K : ℤ) ^ (m' + 1) - ε)) *
        ∏ i ∈ Finset.Icc 1 m', (((Nat.card K : ℤ) ^ 2) ^ i - 1)) (by ring)
    have hdvd : Nat.card K ^ (m' * (m' + 1)) ∣ Nat.card ↥O := by
      rw [← Int.natCast_dvd_natCast]
      push_cast
      exact hdvdZ
    rw [hN] at hdvd
    refine odd_case_contra_l33 hq3 hodd ?_ hdvd hW
    calc 6 = 2 * 3 := by norm_num
      _ ≤ m' * (m' + 1) := Nat.mul_le_mul hm2 (by omega)
  ·
    have hm3 : 3 ≤ m := by omega
    have h2 : ringChar K ≠ 2 := by
      intro h
      haveI : CharP K 2 := ringChar.of_eq h
      have hev := CFSG.ComponentClassification.UnbalancedCatalog.even_finrank_of_charTwo Q hQ
      rw [hm] at hev
      exact (Nat.not_even_iff_odd.2 ⟨m, rfl⟩) hev
    have hcard := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_odd h2 hQ (n := m)
      (by omega)
    have hdvdZ : ((Nat.card K : ℤ) ^ (m ^ 2)) ∣ (Nat.card ↥O : ℤ) := by
      rw [hcard]
      exact Dvd.intro (2 * ∏ i ∈ Finset.Icc 1 m, (((Nat.card K : ℤ) ^ 2) ^ i - 1)) (by ring)
    have hdvd : Nat.card K ^ (m ^ 2) ∣ Nat.card ↥O := by
      rw [← Int.natCast_dvd_natCast]
      push_cast
      exact hdvdZ
    rw [hN] at hdvd
    refine odd_case_contra_l33 hq3 hodd ?_ hdvd hW
    calc 6 ≤ 3 ^ 2 := by norm_num
      _ ≤ m ^ 2 := Nat.pow_le_pow_left hm3 2

end Large

section Low

open CFSG.RankThree.Classical2 CFSG.HardMathSupport.Solomon.Coordinator.LieComp

variable {K : Type} [Field K] [Fintype K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

private theorem not_isLpType_of_phi {L : Subgroup ↥(orthDerived Q)} (hL : CFSG.IsQuasisimple ↥L)
    {S : Type} [Group S] (hSq : CFSG.IsQuasisimple S)
    (hS : ¬ IsLpType 3 3 (S ⧸ Subgroup.center S))
    (φ : S →* ↥(TauCeti.QuadraticMap.orthogonalGroup Q)) (h : φ.range = L.map (OmegaAux.ιO Q)) :
    ¬ IsLpType 3 3 (↥L ⧸ Subgroup.center ↥L) := by
  obtain ⟨ψ, hψ⟩ := OmegaAux.exists_lift_of_range_eq φ L h
  exact not_isLpType_of_range hL hSq hS ψ hψ

private theorem not_isLpType_sl_two {E : Type} [Field E] [Finite E] (hE : ringChar E = 3) :
    ¬ IsLpType 3 3 (Matrix.SpecialLinearGroup (Fin 2) E ⧸
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) E)) :=
  not_isLpType_of_equiv_sl_two hE (MulEquiv.refl _)

open CFSG.ComponentClassification CFSG.ComponentClassification.CatLeafProof
  CFSG.ComponentClassification.CatalogueBOrthogonal CFSG.LocalAnalysis.ComponentInitial in
private theorem noL33_three (hK3 : ringChar K = 3) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hd : Module.finrank K V = 3) (L : Subgroup ↥(orthDerived Q)) (hLn : L.Normal)
    (hL : CFSG.IsQuasisimple ↥L) : ¬ IsLpType 3 3 (↥L ⧸ Subgroup.center ↥L) := by
  have h2 : ringChar K ≠ 2 := by rw [hK3]; norm_num
  have hodd : Odd (Nat.card K) := CFSG.GroupTheory.WeirSylow.odd_card_of_ringChar_ne_two h2
  have hK2 : Nat.card K ≠ 2 := fun h => absurd (h ▸ hodd) (by decide)
  have hM : CFSG.IsComponent (L.map (OmegaAux.ιO Q)) := OmegaAux.isComponent_map_ιO Q hL
  by_cases hK3' : Nat.card K = 3
  · have := ((CatalogueBOrthogonalLowDimensionFrontiers.orthogonal_three_p_components_frontier
      hodd Q hQ hd).2 hK3').1
    exact (not_isComponent_of_isSolvable hM).elim
  obtain ⟨-, -, e', -, -, hcomm, hq, -⟩ := orthogonal_three_derived hodd hK3' Q hQ hd
  have hMeq := eq_commutator_of_isComponent hq hM
  refine not_isLpType_of_phi hL
    (CatalogueBGeneralLinear.specialLinear_quasisimple 2 K le_rfl (Or.inr hK2) (Or.inr hK3'))
    (not_isLpType_sl_two hK3)
    (e'.symm.toMonoidHom.comp (traceZeroOrthogonalAction.comp
      (Matrix.SpecialLinearGroup.toGL : Matrix.SpecialLinearGroup (Fin 2) K →* _))) ?_
  rw [OmegaAux.A.range_comp_symm]
  exact (hMeq.trans hcomm).symm

open CFSG.ComponentClassification CFSG.ComponentClassification.CatLeafProof
  CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit CFSG.LocalAnalysis.ComponentInitial in
private theorem noL33_four_split (hK3 : ringChar K = 3)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hd : Module.finrank K V = 4)
    (hS : ∃ S : Submodule K V, Module.finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0)
    (L : Subgroup ↥(orthDerived Q)) (hLn : L.Normal) (hL : CFSG.IsQuasisimple ↥L) :
    ¬ IsLpType 3 3 (↥L ⧸ Subgroup.center ↥L) := by
  have hM : CFSG.IsComponent (L.map (OmegaAux.ιO Q)) := OmegaAux.isComponent_map_ιO Q hL
  by_cases hK : Nat.card K = 2 ∨ Nat.card K = 3
  · haveI := OmegaAux.A.isSolvable_orthogonalGroup_of_smallFixedException Q hQ (by omega)
      (Or.inr ⟨⟨hd, hS⟩, hK⟩)
    exact (not_isComponent_of_isSolvable hM).elim
  push Not at hK
  obtain ⟨hK2, hK3'⟩ := hK
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have : Finite ↥(TauCeti.QuadraticMap.orthogonalGroup Q) := inferInstance
  obtain ⟨-, e', -, -, hsup, hq₁, hq₂, hn₁, hn₂, -, -, -⟩ :=
    orthogonal_split_four_derived hK2 hK3' Q hQ hd hS
  have hMD : L.map (OmegaAux.ιO Q) ≤ commutator (TauCeti.QuadraticMap.orthogonalGroup Q) := by
    rw [← OmegaAux.range_ιO]
    exact Subgroup.map_le_range _ _
  have hSL := CatalogueBGeneralLinear.specialLinear_quasisimple 2 K le_rfl (Or.inr hK2)
    (Or.inr hK3')
  rcases CatLeafProof.eq_or_eq_of_isComponent_le_sup hsup hq₁ hq₂ hn₁ hn₂ hM hMD with h | h
  · refine not_isLpType_of_phi hL hSL (not_isLpType_sl_two hK3)
      (e'.symm.toMonoidHom.comp ((specialRho (K := K)).comp (MonoidHom.inl _ _))) ?_
    rw [OmegaAux.A.range_comp_symm]
    exact h.symm
  · refine not_isLpType_of_phi hL hSL (not_isLpType_sl_two hK3)
      (e'.symm.toMonoidHom.comp ((specialRho (K := K)).comp (MonoidHom.inr _ _))) ?_
    rw [OmegaAux.A.range_comp_symm]
    exact h.symm

open CFSG.ComponentClassification CFSG.ComponentClassification.CatLeafProof
  CFSG.ComponentClassification.CatalogueBOrthogonalFourNonsplit
  CFSG.LocalAnalysis.ComponentInitial in
private theorem noL33_four_nonsplit (hK3 : ringChar K = 3)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hd : Module.finrank K V = 4)
    (hno : ¬ ∃ S : Submodule K V, Module.finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0)
    (L : Subgroup ↥(orthDerived Q)) (hLn : L.Normal) (hL : CFSG.IsQuasisimple ↥L) :
    ¬ IsLpType 3 3 (↥L ⧸ Subgroup.center ↥L) := by
  have h2 : ringChar K ≠ 2 := by rw [hK3]; norm_num
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
  have hchar : ringChar (extension (δ : K)) = 3 := OmegaAux.A.ringChar_eq_of_algebra.trans hK3
  refine not_isLpType_of_phi hL
    (CatalogueBGeneralLinear.specialLinear_quasisimple 2 (extension (δ : K)) le_rfl
      (Or.inr hE2) (Or.inr hE3)) (not_isLpType_sl_two hchar)
    (e'.symm.toMonoidHom.comp (specialRho (δ : K) h2')) ?_
  rw [OmegaAux.A.range_comp_symm]
  exact (hMeq.trans hcomm).symm

open CFSG.ComponentClassification CFSG.ComponentClassification.CatLeafProof
  CFSG.ComponentClassification.CatalogueBOrthogonalFive CFSG.LocalAnalysis.ComponentInitial in
private theorem noL33_five (hK3 : ringChar K = 3) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hd : Module.finrank K V = 5) (L : Subgroup ↥(orthDerived Q)) (hLn : L.Normal)
    (hL : CFSG.IsQuasisimple ↥L) : ¬ IsLpType 3 3 (↥L ⧸ Subgroup.center ↥L) := by
  have h2 : ringChar K ≠ 2 := by rw [hK3]; norm_num
  have hodd : Odd (Nat.card K) := CFSG.GroupTheory.WeirSylow.odd_card_of_ringChar_ne_two h2
  have h2' := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  have hM : CFSG.IsComponent (L.map (OmegaAux.ιO Q)) := OmegaAux.isComponent_map_ιO Q hL
  obtain ⟨-, -, e', -, -, hcomm, hq, -⟩ := orthogonal_five_derived hodd Q hQ hd
  have hMeq := eq_commutator_of_isComponent hq hM
  let eSp : (symplecticMultiplier (K := K)).ker ≃* ↥(CFSG.Open.StatedSp 2 K) :=
    symplecticKernelEquivFin.trans (CFSG.LieType.Universal.Symplectic.equivStatedSp 2 K)
  have hSq : CFSG.IsQuasisimple ↥(CFSG.Open.StatedSp 2 K) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv eSp (symplecticKernel_quasisimple hodd)
  refine not_isLpType_of_phi hL hSq
    (fun hL' => sp_l33_false hK3 le_rfl (MulEquiv.refl _).toMonoidHom
      (MulEquiv.refl _).surjective (ker_mulEquiv_le_center _) hL')
    (e'.symm.toMonoidHom.comp ((selfAdjointSymplecticAction h2').comp eSp.symm.toMonoidHom)) ?_
  rw [OmegaAux.A.range_comp_symm, MonoidHom.range_comp,
    MonoidHom.range_eq_top.mpr eSp.symm.surjective, ← MonoidHom.range_eq_map]
  exact (hMeq.trans hcomm).symm

open CFSG.ComponentClassification CFSG.ComponentClassification.CatLeafProof
  CFSG.ComponentClassification.CatalogueBOrthogonalFourNonsplit
  CFSG.ComponentClassification.CatalogueBOrthogonalSix CFSG.LocalAnalysis.ComponentInitial in
private theorem noL33_six_nonsplit (hK3 : ringChar K = 3)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hd : Module.finrank K V = 6)
    (hno : ¬ ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (L : Subgroup ↥(orthDerived Q)) (hLn : L.Normal) (hL : CFSG.IsQuasisimple ↥L) :
    ¬ IsLpType 3 3 (↥L ⧸ Subgroup.center ↥L) := by
  have h2 : ringChar K ≠ 2 := by rw [hK3]; norm_num
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
  have hnq : ((4 : ℕ), ringChar K ^ (n : ℕ)) ≠ (3, 2) := fun h => by
    have := (Prod.mk.inj h).1
    omega
  obtain ⟨hSq, -⟩ := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hF
    (by norm_num) hnq
  let eSU := eU.trans (MulEquiv.subgroupCongr hSU)
  refine not_isLpType_of_phi hL hSq
    (fun hL' => su_l33_false hU hK3 (by norm_num) (MulEquiv.refl _).toMonoidHom
      (MulEquiv.refl _).surjective (ker_mulEquiv_le_center _) hL')
    (e'.symm.toMonoidHom.comp ((sixSpecialKappa (δ : K) h2').comp eSU.symm.toMonoidHom)) ?_
  rw [OmegaAux.A.range_comp_symm, MonoidHom.range_comp,
    MonoidHom.range_eq_top.mpr eSU.symm.surjective, ← MonoidHom.range_eq_map]
  exact (hMeq.trans hcomm).symm

private theorem noL33_singular (hK3 : ringChar K = 3)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (L : Subgroup ↥(orthDerived Q)) (hLn : L.Normal) (hL : CFSG.IsQuasisimple ↥L) :
    ¬ IsLpType 3 3 (↥L ⧸ Subgroup.center ↥L) := by
  have h2 : ringChar K ≠ 2 := by rw [hK3]; norm_num
  have hodd : Odd (Nat.card K) := CFSG.GroupTheory.WeirSylow.odd_card_of_ringChar_ne_two h2
  have hqs : CFSG.IsQuasisimple ↥(orthDerived Q) :=
    CFSG.RankThree.PartOne.KCOrthogonal.isQuasisimple_orthDerived hQ hT
  exact not_isLpType_top (OmegaAux.eq_top_of_isQuasisimple hqs hLn hL) (large_noL33 hQ hT hodd)

theorem omega_noL33 (hK3 : ringChar K = 3) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (L : Subgroup ↥(orthDerived Q)) (hLn : L.Normal) (hL : CFSG.IsQuasisimple ↥L) :
    ¬ IsLpType 3 3 (↥L ⧸ Subgroup.center ↥L) := by
  by_cases hd2 : Module.finrank K V ≤ 2
  · exact (OmegaAux.M.case_le_two hQ hd2 L hL).elim
  by_cases hT : ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0
  · exact noL33_singular hK3 hQ hT L hLn hL
  by_cases hd3 : Module.finrank K V = 3
  · exact noL33_three hK3 hQ hd3 L hLn hL
  by_cases hd4 : Module.finrank K V = 4
  · by_cases hS : ∃ S : Submodule K V, Module.finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0
    · exact noL33_four_split hK3 hQ hd4 hS L hLn hL
    · exact noL33_four_nonsplit hK3 hQ hd4 hS L hLn hL
  by_cases hd5 : Module.finrank K V = 5
  · exact noL33_five hK3 hQ hd5 L hLn hL
  by_cases hd6 : Module.finrank K V = 6
  · exact noL33_six_nonsplit hK3 hQ hd6 hT L hLn hL
  exact (hT (OmegaAux.C.large_exists_singular hQ (by omega))).elim

end Low

section OrthInner

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal CFSG.LocalAnalysis.ComponentInitial
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple CFSG.Assembly.LowTwoRank
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp

private def OrthL33 (H : Type) [Group H] : Prop :=
  ∃ (X : Type) (_ : Group X) (_ : Finite X) (f : X →* H), commutator X = ⊤ ∧
    Function.Surjective f ∧ f.ker ≤ Subgroup.center X ∧ ¬ IsLpType 3 3 (X ⧸ Subgroup.center X)

private theorem OrthL33.of_surj {H H' : Type} [Group H] [Group H'] (h : OrthL33 H)
    (φ : H →* H') (hφ : Function.Surjective φ) (hk : φ.ker ≤ Subgroup.center H) :
    OrthL33 H' := by
  obtain ⟨X, _, _, f, hX, hf, hfk, hA⟩ := h
  refine ⟨X, inferInstance, inferInstance, φ.comp f, hX, hφ.comp hf, ?_, hA⟩
  intro x hx
  have h1 : f x ∈ Subgroup.center H := hk hx
  rw [← comap_center_of_surjective hX f hf hfk]
  exact h1

private theorem OrthL33.of_quasisimple {H : Type} [Group H] [Finite H]
    (hq : CFSG.IsQuasisimple H) (hno : ¬ IsLpType 3 3 (H ⧸ Subgroup.center H)) : OrthL33 H :=
  ⟨H, inferInstance, inferInstance, (MulEquiv.refl H).toMonoidHom, hq.1.commutator_eq_top,
    (MulEquiv.refl H).surjective, ker_mulEquiv_le_center _, hno⟩

private theorem OrthL33.not_isLpType {H : Type} [Group H] (h : OrthL33 H) :
    ¬ IsLpType 3 3 (H ⧸ Subgroup.center H) := by
  obtain ⟨X, _, _, f, hX, hf, hfk, hA⟩ := h
  exact not_isLpType_of_surj hX f hf hfk hA

private theorem OrthL33.map_projective {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {F : Subgroup (V ≃ₗ[K] V)} (hFΩ : F ≤ orthDerived Q)
    (h : OrthL33 ↥F) :
    OrthL33 ↥((F.subgroupOf (orthDerived Q)).map
      (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)))) := by
  have h' : OrthL33 ↥(F.subgroupOf (orthDerived Q)) := by
    let e := (Subgroup.subgroupOfEquivOfLe hFΩ).symm
    refine h.of_surj e.toMonoidHom e.surjective ?_
    intro x hx
    have : x = 1 := e.injective (by rw [map_one]; exact hx)
    rw [this]
    exact one_mem _
  exact h'.of_surj _ (MonoidHom.subgroupMap_surjective _ _) (ker_subgroupMap_le_center _)

private theorem orthL33_specialBlock_paired {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K : Type}
    [Field K] [Finite K] (hK3 : ringChar K = 3) {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V}
    (hx : OddOrderIsometry Q p x) {h : K[X]} [Fact (Irreducible h)]
    (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    (hne : h ≠ reciprocalPolynomial h) (hq : CFSG.IsQuasisimple ↥(specialBlock Q x h)) :
    OrthL33 ↥(specialBlock Q x h) := by
  letI : Fintype (AdjoinRoot h) := Fintype.ofFinite _
  have hm : 2 ≤ primaryMultiplicity x.toLinearMap h := by
    by_contra hlt
    have hpos := hx.primaryMultiplicity_pos hh
    have h1 : primaryMultiplicity x.toLinearMap h = 1 := by omega
    exact ne_bot_of_isQuasisimple hq (hx.specialBlock_eq_bot_of_finrank_eq_one hh h1)
  have h4 : 4 ≤ Fintype.card (AdjoinRoot h) := by
    have := hx.p_lt_card_adjoinRoot hp hh hne1
    have := hp.two_le
    rw [Fintype.card_eq_nat_card]
    omega
  let b : Module.Basis (Fin (primaryMultiplicity x.toLinearMap h)) (AdjoinRoot h)
      (primaryComponent x.toLinearMap h) := Module.finBasisOfFinrankEq _ _ rfl
  let e₁ : ↥(specialBlock Q x h) ≃*
      Matrix.SpecialLinearGroup (Fin (primaryMultiplicity x.toLinearMap h)) (AdjoinRoot h) :=
    ((MulEquiv.ofBijective (specialToSL Q x h)
      ⟨hx.specialToSL_injective hh, hx.specialToSL_surjective_paired hh hne⟩).trans
      (Matrix.SpecialLinearGroup.toLin_equiv b).symm)
  have hchar : ringChar (AdjoinRoot h) = 3 :=
    (Algebra.ringChar_eq K (AdjoinRoot h)).symm.trans hK3
  have hfin : Finite ↥(specialBlock Q x h) := Finite.of_equiv _ e₁.symm.toEquiv
  refine OrthL33.of_quasisimple hq fun hL => ?_
  have := (sl_l33 hchar hm e₁.symm.toMonoidHom e₁.symm.surjective (ker_mulEquiv_le_center _)
    hL).2
  rw [Nat.card_eq_fintype_card] at this
  omega

private theorem orthL33_specialBlock_selfDual {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K : Type}
    [Field K] [Finite K] (hK3 : ringChar K = 3) {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V}
    (hx : OddOrderIsometry Q p x) {h : K[X]} [Fact (Irreducible h)]
    (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    (hself : h = reciprocalPolynomial h) (hq : CFSG.IsQuasisimple ↥(specialBlock Q x h)) :
    OrthL33 ↥(specialBlock Q x h) := by
  classical
  have hp2' : Odd p := hp.odd_of_ne_two hp2
  have hirr := irreducible_of_mem_primaryFactors hh
  obtain ⟨d, H, hdeg, hroot, hH, hadd1, hadd2, hleft, hright, hsymm⟩ :=
    hx.exists_selfDual_hermitian hp2' hh hne1 hself
  have hd : finrank K (AdjoinRoot h) = 2 * d := by
    rw [(AdjoinRoot.powerBasis hirr.ne_zero).finrank, AdjoinRoot.powerBasis_dim, hdeg]
  obtain ⟨ℓ, f, hU, hq0, hbar⟩ := exists_unitaryFieldData K (AdjoinRoot h) hd
  have hbar' : ∀ z, frobPow K (AdjoinRoot h) d z = hU.bar z := fun z => by
    rw [hbar, frobPow_apply]
  let B : primaryComponent x.toLinearMap h →ₛₗ[hU.bar]
      primaryComponent x.toLinearMap h →ₗ[AdjoinRoot h] AdjoinRoot h :=
    LinearMap.mk₂'ₛₗ hU.bar (RingHom.id _) H hadd1
      (fun c u w => by rw [hleft, smul_eq_mul, hbar']) hadd2
      (fun c u w => by rw [hright, smul_eq_mul, RingHom.id_apply])
  have hBH : ∀ u w, B u w = H u w := fun u w => rfl
  have hBsymm : B.IsSymm := ⟨fun u w => by rw [hBH, hBH, hsymm u w, hbar']⟩
  have hBl : B.SeparatingLeft := by
    intro u hu
    refine Subtype.ext (hx.eq_zero_of_polar_selfdual hh hself u.2 fun w hw => ?_)
    have h1 := hH u ⟨w, hw⟩ 1
    rw [mul_one, one_smul] at h1
    have h2 : H u ⟨w, hw⟩ = 0 := by rw [← hBH]; exact hu _
    rw [h2, map_zero] at h1
    exact h1.symm
  have hrange : (specialBlockGL Q x h).range = sesqSpecialUnitaryGroup B := by
    rw [range_specialBlockGL, sesqSpecialUnitaryGroup]
    congr 1
    ext γ
    rw [hx.mem_range_blockGL_selfDual_iff hh hne1 hself H hH, mem_sesqUnitaryGroup]
    exact Iff.rfl
  let e₁ : ↥(specialBlock Q x h) ≃* ↥(sesqSpecialUnitaryGroup B) :=
    (MonoidHom.ofInjective (hx.specialBlockGL_injective hh)).trans
      (MulEquiv.subgroupCongr hrange)
  haveI := hU.finite
  haveI : Fact ℓ.Prime := ⟨hU.prime⟩
  haveI := hU.charP
  letI : Fintype (AdjoinRoot h) := Fintype.ofFinite _
  have hE : Nat.card (AdjoinRoot h) = (ℓ ^ (f * d)) ^ 2 := by
    rw [hU.card, ← pow_mul, mul_comm]
  have hℓ : ringChar (AdjoinRoot h) = ℓ := ringChar.eq _ ℓ
  have hℓ3 : ℓ = 3 := by
    rw [← hℓ]
    exact (Algebra.ringChar_eq K (AdjoinRoot h)).symm.trans hK3
  have hm : 2 ≤ primaryMultiplicity x.toLinearMap h := by
    by_contra hlt
    have hpos := hx.primaryMultiplicity_pos hh
    have h1 : primaryMultiplicity x.toLinearMap h = 1 := by omega
    exact ne_bot_of_isQuasisimple hq (hx.specialBlock_eq_bot_of_finrank_eq_one hh h1)
  have hfinV : Finite ↥(sesqSpecialUnitaryGroup B) := by
    have : Finite V := Module.finite_of_finite K
    have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
      fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
    exact Finite.of_equiv _ e₁.toEquiv
  have hfinS : Finite ↥(specialBlock Q x h) := Finite.of_equiv _ e₁.symm.toEquiv
  refine OrthL33.of_quasisimple hq fun hL => ?_
  rcases Nat.lt_or_ge (primaryMultiplicity x.toLinearMap h) 3 with hm3 | hm3
  ·
    have hm2 : Module.finrank (AdjoinRoot h) (primaryComponent x.toLinearMap h) = 2 := by
      have : primaryMultiplicity x.toLinearMap h = 2 := by omega
      exact this
    obtain ⟨φ⟩ := CFSG.RankThree.Classical.nonempty_sesqSpecialUnitaryGroup_mulEquiv_SL2 hU hBsymm
      hBl hm2
    letI : Fintype ↥hU.fixedField := Fintype.ofFinite _
    have hcardF : Fintype.card ↥hU.fixedField = ℓ ^ (f * d) := by
      rw [Fintype.card_eq_nat_card, hU.card_fixedField]
    haveI : CharP ↥hU.fixedField ℓ := charP_of_card_eq_prime_pow hcardF
    have hcharF : ringChar ↥hU.fixedField = 3 := by rw [ringChar.eq _ ℓ, hℓ3]
    exact not_isLpType_of_equiv_sl_two hcharF (e₁.trans φ).symm hL
  ·
    obtain ⟨e₀, he₀⟩ := hU.exists_orthonormal_basis hBsymm hBl
    obtain ⟨e₂⟩ := CFSG.RankThree.CentralLiftU.nonempty_sesqSpecialUnitaryGroup_mulEquiv_SUid hU
      e₀ he₀
    have hS : CFSG.LieType.Universal.Unitary.SUid hU.barEquiv
        (primaryMultiplicity x.toLinearMap h) =
        CFSG.Open.StatedSU (primaryMultiplicity x.toLinearMap h) (ℓ ^ (f * d))
          (AdjoinRoot h) := by
      rw [CFSG.RankThree.CentralLiftU.barEquiv_eq_unitaryInvolution hU]
      exact CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hE _
    let e₃ : ↥(CFSG.Open.StatedSU (primaryMultiplicity x.toLinearMap h) (ℓ ^ (f * d))
        (AdjoinRoot h)) ≃* ↥(sesqSpecialUnitaryGroup B) :=
      (e₂.trans (MulEquiv.subgroupCongr hS)).symm
    let e₄ := e₃.trans e₁.symm
    exact su_l33_false hU hℓ3 hm3 e₄.toMonoidHom e₄.surjective (ker_mulEquiv_le_center _) hL

private theorem orthL33_fixedFactor {p : ℕ} {K : Type} [Field K] [Finite K]
    (hK3 : ringChar K = 3) {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x)
    {F : Subgroup (V ≃ₗ[K] V)} (hFq : CFSG.IsQuasisimple ↥F)
    (hFle : F ≤ supportedFixedDerived Q x)
    (hFn : (F.subgroupOf (supportedFixedDerived Q x)).Normal) : OrthL33 ↥F := by
  have hQW := hx.polarBilin_fixed_nondegenerate
  letI : Fintype K := Fintype.ofFinite K
  let e := supportedFixedDerivedEquiv hx
  let A : Subgroup ↥(supportedFixedDerived Q x) := F.subgroupOf (supportedFixedDerived Q x)
  let L : Subgroup ↥(orthDerived (Q.comp (fixedSpace x).subtype)) := A.map e.toMonoidHom
  have hLn : L.Normal := hFn.map e.toMonoidHom e.surjective
  let eAF : ↥A ≃* ↥F := Subgroup.subgroupOfEquivOfLe hFle
  let eAL : ↥A ≃* ↥L := A.equivMapOfInjective e.toMonoidHom e.injective
  have hLq : CFSG.IsQuasisimple ↥L :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (eAF.symm.trans eAL) hFq
  have hno := omega_noL33 hK3 hQW L hLn hLq
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  refine OrthL33.of_quasisimple hFq fun hL => hno ?_
  let eLF : ↥L ≃* ↥F := eAL.symm.trans eAF
  exact isLpType_of_mulEquiv (QuotientGroup.congr _ _ eLF (Subgroup.map_center_eq eLF)) hL

private theorem orthL33_component {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K : Type} [Field K]
    [Finite K] (hK3 : ringChar K = 3) {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) (hpℓ : p ≠ ringChar K)
    (a : ProjOrthDerived Q) (ha : a ^ p = 1) (J : Subgroup (ProjOrthDerived Q))
    (hJ : CFSG.Open.IsComponentOf J (Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)))) :
    OrthL33 ↥J := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  set ρ : ↥(orthDerived Q) →* ProjOrthDerived Q :=
    QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) with hρ
  obtain ⟨x, hxa, hx, hcent⟩ : ∃ x : ↥(orthDerived Q), ρ x = a ∧
      OddOrderIsometry Q p (x : V ≃ₗ[K] V) ∧
      Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)) =
        (Subgroup.centralizer ({x} : Set ↥(orthDerived Q))).map ρ := by
    by_cases h1 : a = 1
    · refine ⟨1, by rw [h1, map_one], oddOrderIsometry_of_pow_eq_one hp hpℓ hQ 1 (one_pow p),
        ?_⟩
      have e1 : Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)) = ⊤ := by
        ext g
        simp [h1, Subgroup.mem_centralizer_iff]
      have e2 : Subgroup.centralizer ({(1 : ↥(orthDerived Q))} : Set ↥(orthDerived Q)) = ⊤ := by
        ext g
        simp [Subgroup.mem_centralizer_iff]
      rw [e1, e2, Subgroup.map_top, MonoidHom.range_eq_top.2 (QuotientGroup.mk'_surjective _)]
    · obtain ⟨-, -, -, -, -, -, -, -, hlift⟩ :=
        CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
      obtain ⟨x, ⟨hxa, hxp⟩, -, hcent⟩ := hlift p hp hp2 a (orderOf_eq_prime ha h1)
      exact ⟨x, hxa, oddOrderIsometry_of_orthDerived hp hpℓ hQ x hxp, hcent⟩
  obtain ⟨Rep, hRep⟩ := hx.exists_orbitRepresentatives
  set xe : V ≃ₗ[K] V := (x : V ≃ₗ[K] V) with hxe
  set N : Subgroup (ProjOrthDerived Q) := centralizerImage Q xe with hN
  have hNeq : Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)) = N := by
    rw [hcent]
    exact CFSG.RankThree.PartOne.map_centralizer_eq_centralizerImage x
  rw [hNeq] at hJ
  obtain ⟨n, F, hFq, hFsup, hFn0⟩ := exists_fixedFactors hx
  have hFΩ : ∀ i, F i ≤ orthDerived Q := fun i =>
    (hFq i).2.1.trans hx.supportedFixedDerived_le_orthDerived
  set C : Fin n → Subgroup (ProjOrthDerived Q) := fun i => ((F i).subgroupOf (orthDerived Q)).map ρ
    with hC
  have hCsup : (⨆ i, C i) = fixedLayerImage Q xe := by
    by_cases hlist : FixedLayerListed Q xe
    · rw [fixedLayerImage_of_listed hlist]
      unfold fixedComponentImage
      rw [← hFsup hlist, subgroupOf_iSup_of_le F _ hFΩ, Subgroup.map_iSup]
    · have hn := hFn0 hlist
      subst hn
      simp [fixedLayerImage, hlist]
  have hCle : ∀ i, C i ≤ fixedComponentImage Q xe := fun i =>
    Subgroup.map_mono fun g hg => Subgroup.mem_subgroupOf.mpr
      ((hFq i).2.1 (Subgroup.mem_subgroupOf.mp hg))
  have hCcomp : ∀ i, CFSG.Open.IsComponentOf (C i) N := by
    intro i
    have hconj := map_conj_mem ρ (F := (F i).subgroupOf (orthDerived Q))
      (F' := (supportedFixedDerived Q xe).subgroupOf (orthDerived Q)) (fun h k hh hk => by
        have := (Subgroup.normal_subgroupOf_iff (hFq i).2.1).mp (hFq i).2.2 (h : V ≃ₗ[K] V)
          (k : V ≃ₗ[K] V) (Subgroup.mem_subgroupOf.mp hh) (Subgroup.mem_subgroupOf.mp hk)
        exact Subgroup.mem_subgroupOf.mpr this)
    refine isComponentOf_of_normal_normal (hCle i) fixedComponentImage_le_centralizerImage ?_
      hx.normal_fixedComponentImage (isQuasisimple_map_projective (hFΩ i) (hFq i).1)
    rw [Subgroup.normal_subgroupOf_iff (hCle i)]
    intro h k hh hk
    exact hconj _ _ hh hk
  let ι₁ := {r : ↥Rep // r.1 ≠ X - 1 ∧ CFSG.IsQuasisimple ↥(specialBlock Q xe r.1)}
  have hspecΩ : ∀ r : ι₁, specialBlock Q xe r.1.1 ≤ orthDerived Q := fun r =>
    specialBlock_le_orthDerived_of_perfect r.2.2.1
      ((specialBlock_le_isometryCentralizer r.1.1).trans (fun _ hg => (Subgroup.mem_inf.mp hg).1))
  let S : ι₁ → Subgroup (ProjOrthDerived Q) := fun r => componentImage Q xe r.1.1
  have hScomp : ∀ r, CFSG.Open.IsComponentOf (S r) N := fun r =>
    isComponentOf_of_normal_normal componentImage_le_centralizerImage le_rfl normal_componentImage
      (by rw [Subgroup.subgroupOf_self]; exact Subgroup.normal_top)
      (isQuasisimple_map_projective (hspecΩ r) r.2.2)
  set EN : Subgroup (ProjOrthDerived Q) := (⨆ r, S r) ⊔ fixedLayerImage Q xe with hEN
  have hSN : ∀ r, S r ≤ N := fun r => componentImage_le_centralizerImage
  have hENN : EN ≤ N :=
    sup_le (iSup_le hSN) fixedLayerImage_le_centralizerImage
  have hENnormal : (EN.subgroupOf N).Normal :=
    normal_subgroupOf_sup (iSup_le hSN) fixedLayerImage_le_centralizerImage
      (normal_subgroupOf_iSup S hSN fun r => normal_componentImage) hx.normal_fixedLayerImage
  have hENn : ∀ c ∈ N, ∀ e ∈ EN, c * e * c⁻¹ ∈ EN := fun c hc e he =>
    (Subgroup.normal_subgroupOf_iff hENN).mp hENnormal e c he hc
  have hperf : ∀ P : Subgroup (ProjOrthDerived Q), P ≤ N → commutator ↥P = ⊤ → P ≤ EN := by
    intro P hPN hP
    obtain ⟨S₀, hS₀N, hS₀sol, hcomm⟩ := exists_solvable_comm_le hQ hp hp2 x hx hRep EN
      (fun h hh hne hq => le_sup_of_le_left
        (le_iSup S (⟨⟨h, hh⟩, hne, hq⟩ : ι₁)))
      (fun hlist => by
        rw [← fixedLayerImage_of_listed hlist]
        exact le_sup_right)
    haveI := hS₀sol
    exact perfect_le_of_le_sup_solvable hENN hS₀N hENn hcomm hPN (Subgroup.isPerfect_iff.1 ⟨hP⟩)
  let Fm : ι₁ ⊕ Fin n → Subgroup (ProjOrthDerived Q) := Sum.elim S C
  have hFm : ∀ i, CFSG.Open.IsComponentOf (Fm i) N := by
    rintro (r | i)
    · exact hScomp r
    · exact hCcomp i
  have hiSup : (⨆ i, Fm i) = EN := by
    rw [iSup_sum]
    simp only [Fm, Sum.elim_inl, Sum.elim_inr]
    rw [hCsup]
  obtain ⟨i, rfl⟩ := component_mem_named_factors Fm hFm
    (fun P hPN hP => hiSup ▸ hperf P hPN hP) hJ
  rcases i with ⟨⟨h, hh⟩, hne, hq⟩ | i
  · have hh' : h ∈ primaryFactors xe.toLinearMap := hRep.1 hh
    haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh'⟩
    refine OrthL33.map_projective (hspecΩ ⟨⟨h, hh⟩, hne, hq⟩) ?_
    by_cases hself : h = reciprocalPolynomial h
    · exact orthL33_specialBlock_selfDual hp hp2 hK3 hx hh' hne hself hq
    · exact orthL33_specialBlock_paired hp hp2 hK3 hx hh' hne hself hq
  · exact OrthL33.map_projective (hFΩ i)
      (orthL33_fixedFactor hK3 hx (hFq i).1 (hFq i).2.1 (hFq i).2.2)

theorem noL33_conj_omega {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) {t : StatedLieTag}
    (ht : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) {G : Type} [Group G]
    {n f : ℕ} (hG : StatedClassicalModel G t n 3 f) (a : G) (ha : a ^ p = 1)
    (J : Subgroup G)
    (hJ : CFSG.Open.IsComponentOf J
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.conj a))) :
    ¬ IsLpType 3 3 (↥J ⧸ Subgroup.center ↥J) := by
  obtain ⟨K, _, _, V, _, _, _, Q, hQ, hT, hring, ⟨e⟩⟩ := exists_projOrth_model ht hG
  have hfix : CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup
      (MulAut.congr e (MulAut.conj a)) =
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.conj a)).map
        (e : G →* ProjOrthDerived Q) := by
    ext x
    rw [CFSG.HardMathSupport.Solomon.Coordinator.mem_fixSubgroup]
    refine Iff.trans ?_ (Subgroup.mem_map_equiv (f := e)).symm
    rw [CFSG.HardMathSupport.Solomon.Coordinator.mem_fixSubgroup]
    show e (MulAut.conj a (e.symm x)) = x ↔ MulAut.conj a (e.symm x) = e.symm x
    exact e.eq_symm_apply.symm
  have hJ' : CFSG.Open.IsComponentOf (J.map (e : G →* ProjOrthDerived Q))
      (Subgroup.centralizer ({e a} : Set (ProjOrthDerived Q))) := by
    have h1 := CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map e hJ
    rw [← hfix, congr_conj, fixSubgroup_conj_eq_centralizer] at h1
    exact h1
  have hJL := orthL33_component hp hp2 hring hQ hT (by rw [hring]; exact hp3) (e a)
    (by rw [← map_pow, ha, map_one]) _ hJ'
  intro hL
  exact hJL.not_isLpType
    (CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsL33.isLpType_center_map e hL)

end OrthInner

section OrthOuter

open CFSG.HardMathSupport.Solomon.Coordinator.LieComp

theorem noL33_omega_outer {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) {t : StatedLieTag}
    (ht : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) {G : Type} [Group G]
    {n f : ℕ} (hG : StatedClassicalModel G t n 3 f) (β : MulAut G) (hβ : β ^ p = 1)
    (hout : ∀ a : G, MulAut.conj a ≠ β) (J : Subgroup G)
    (hJ : CFSG.Open.IsComponentOf J (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup β)) :
    ¬ IsLpType 3 3 (↥J ⧸ Subgroup.center ↥J) := by
  have hconj : OmegaFieldConj G β 3 p := by
    rcases ht with rfl | rfl | rfl
    · exact omegaFieldConj_odd hp hp2 hG β hβ hout
    · exact omegaFieldConj_plus hp hp2 hG (fun _ => hp3) β hβ hout
    · exact omegaFieldConj_minus hp hp2 hG β hβ hout
  obtain ⟨K, _, _, k, d, Q₀, Q, σ, S, e, hd, hch, he⟩ := hconj.out
  have hd0 : 0 < d := by omega
  obtain ⟨-, hK⟩ := fieldAutT_layer_and_eq S hd0
  obtain ⟨hqT, π, hπ, hπk⟩ := exists_central_epi_omega S hd0
  have hJ1 := CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsL33.isComponentOf_map_congr e hJ
  rw [he] at hJ1
  have hJeq := hK _ hJ1
  intro hL
  have hL1 := CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsL33.isLpType_center_map e hL
  rw [hJeq] at hL1
  have : Finite k := Finite.of_injective (algebraMap k K) (algebraMap k K).injective
  letI : Fintype k := Fintype.ofFinite k
  have hk3 : ringChar k = 3 := (Algebra.ringChar_eq k K).trans hch
  have hodd : Odd (Nat.card k) :=
    CFSG.GroupTheory.WeirSylow.odd_card_of_ringChar_ne_two (by rw [hk3]; norm_num)
  exact not_isLpType_of_surj hqT.1.commutator_eq_top π hπ hπk
    (not_isLpType_top rfl (large_noL33 S.hnd₀ S.hT₀ hodd)) hL1

end OrthOuter

section OrthCatalogue

theorem exists_model_orth {S : Type} [Group S] (idx : TauCeti.ValidLieTypeIndex)
    (hor : (∃ r q, idx.1 = .B r q ∧ 3 ≤ r) ∨ (∃ r q, idx.1 = .D r q) ∨
      ∃ r q, idx.1 = .twistedD r q) (hc3 : idx.1.characteristic = 3)
    (e : S ≃* (TauCeti.CFSGIndex.lie idx).Group) :
    ∃ (t : StatedLieTag) (n f : ℕ), (t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) ∧
      StatedClassicalModel S t n 3 f := by
  obtain ⟨d, hv⟩ := idx
  rcases hor with ⟨r, q, hd, hr3⟩ | ⟨r, q, hd⟩ | ⟨r, q, hd⟩
  · dsimp only at hd
    subst hd
    have hq3 : q.p = 3 := by simpa using hc3
    have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_odd r q hv
      (by rw [hq3]; norm_num) hr3 e
    rw [hq3] at h
    exact ⟨.POmegaOdd, r, q.exponent, Or.inl rfl, h⟩
  · dsimp only at hd
    subst hd
    have hq3 : q.p = 3 := by simpa using hc3
    have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD r q hv e
    rw [hq3] at h
    exact ⟨.POmegaPlus, r, q.exponent, Or.inr (Or.inl rfl), h⟩
  · dsimp only at hd
    subst hd
    have hq3 : q.p = 3 := by simpa using hc3
    have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD r q hv e
    rw [hq3] at h
    exact ⟨.POmegaMinus, r, q.exponent, Or.inr (Or.inr rfl), h⟩

theorem noL33_orthogonal {S : Type} [Group S] [Finite S] (hs : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (idx : TauCeti.ValidLieTypeIndex)
    (hor : (∃ r q, idx.1 = .B r q ∧ 3 ≤ r) ∨ (∃ r q, idx.1 = .D r q) ∨
      ∃ r q, idx.1 = .twistedD r q) (hc3 : idx.1.characteristic = 3)
    (he : Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group)) {α : MulAut S} (hα : α ^ 13 = 1)
    {K : Subgroup S}
    (hK : CFSG.Open.IsComponentOf K (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup α)) :
    ¬ IsLpType 3 3 (↥K ⧸ Subgroup.center ↥K) := by
  haveI := hs
  obtain ⟨e⟩ := he
  obtain ⟨t, n, f, ht, hG⟩ := exists_model_orth idx hor hc3 e
  have hp13 : (13 : ℕ).Prime := by norm_num
  by_cases hin : ∃ a : S, MulAut.conj a = α
  · obtain ⟨a, rfl⟩ := hin
    exact noL33_conj_omega hp13 (by norm_num) (by norm_num) ht hG a
      (pow_eq_one_of_conj_pow (center_eq_bot_of_simple hna) hα) K hK
  · exact noL33_omega_outer hp13 (by norm_num) (by norm_num) ht hG α hα
      (fun a h => hin ⟨a, h⟩) K hK

end OrthCatalogue

section Final

theorem noL33CompSympOrth_holds : InputsL33.NoL33CompSympOrth := by
  intro S _ _ hs hna idx hP hc3 hfo he α hα _ K hK
  obtain ⟨d, hv⟩ := idx
  have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
    ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  cases d with
  | B r q =>
    by_cases hr2 : r = 2
    · subst hr2
      exact noL33_symplectic hs hna ⟨_, hv⟩ (Or.inl ⟨q, rfl⟩) hc3 hfo he hα hK
    · exact noL33_orthogonal hs hna ⟨_, hv⟩ (Or.inl ⟨r, q, rfl, by simp only at hr; omega⟩) hc3
        he hα hK
  | C r q => exact noL33_symplectic hs hna ⟨_, hv⟩ (Or.inr ⟨r, q, rfl⟩) hc3 hfo he hα hK
  | D r q => exact noL33_orthogonal hs hna ⟨_, hv⟩ (Or.inr (Or.inl ⟨r, q, rfl⟩)) hc3 he hα hK
  | twistedD r q =>
    exact noL33_orthogonal hs hna ⟨_, hv⟩ (Or.inr (Or.inr ⟨r, q, rfl⟩)) hc3 he hα hK
  | _ => simp [CFSG.Yardstones.Md42047359a2a.lieFamily] at hP

theorem noL33CompRest_of_exc (hE : InputsL33.NoL33CompExc) : InputsL33.NoL33CompRest :=
  ⟨noL33CompSympOrth_holds, hE⟩

end Final

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsL33c
