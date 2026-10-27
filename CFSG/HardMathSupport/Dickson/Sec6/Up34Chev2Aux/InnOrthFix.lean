module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.OrthBlocksComp
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.ExcOuter
public import CFSG.RankThree.PartOne.S11d.OrthCaseH
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporLocal
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnLin

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.OrthBlocks

open Polynomial Module CFSG CFSG.Open CFSG.Blueprint CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.Classical2 CFSG.LocalAnalysis.ComponentInitial
  CFSG.HardMathSupport.Solomon.UniquenessMaximal CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2
open CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit (DeterminantIsometries specialRho specialRho_eq_one_iff)

section Models

variable {K : Type} [Field K] [Finite K] [CharP K 2] {W : Type} [AddCommGroup W] [Module K W]
  [FiniteDimensional K W]

theorem klein_commutator_orthogonal_six_all (Q : QuadraticForm K W)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hd : Module.finrank K W = 6)
    (hts : ∃ U : Submodule K W, Module.finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) :
    Nonempty (commutator (TauCeti.QuadraticMap.orthogonalGroup Q) ≃* StatedSL 4 K) := by
  obtain ⟨e⟩ := CFSG.RankThree.PartOne.K159.Klein.exists_isometry_quadPlus_three Q hQ hd hts
  obtain ⟨hs, hp⟩ := CFSG.RankThree.PartOne.K159.Klein.sl4_isSimpleGroup_and_perfect (K := K)
  have hρinj := CFSG.RankThree.PartOne.KCOrthogonal.transportHom_injective e
    (CFSG.RankThree.PartOne.K159.Klein.rho : Matrix.SpecialLinearGroup (Fin 4) K →* _)
    CFSG.RankThree.PartOne.K159.Klein.rho_injective
  have hρmem := CFSG.RankThree.PartOne.KCOrthogonal.transportHom_mem e
    (CFSG.RankThree.PartOne.K159.Klein.rho : Matrix.SpecialLinearGroup (Fin 4) K →* _)
    CFSG.RankThree.PartOne.K159.Klein.rho_mem
  set O := TauCeti.QuadraticMap.orthogonalGroup Q with hO
  set ρ := CFSG.RankThree.PartOne.KCOrthogonal.transportHom e
    (CFSG.RankThree.PartOne.K159.Klein.rho : Matrix.SpecialLinearGroup (Fin 4) K →* _) with hρ
  have hle : ρ.range ≤ O := by
    rintro _ ⟨g, rfl⟩
    exact hρmem g
  have hcard : Nat.card O = 2 * Nat.card (Matrix.SpecialLinearGroup (Fin 4) K) := by
    rw [CFSG.Timmesfeld.ClassicalOrders.card_orthogonalGroup_congr e,
      CFSG.RankThree.PartOne.K159.Klein.card_orthogonalGroup_quadPlus_three]
  obtain ⟨-, -, -, -, -, -, hcomm, -⟩ :=
    CFSG.RankThree.PartOne.KCOrthogonal.derived_of_index_two_model O ρ hρinj hle hcard
  have h1 : (commutator ↥O).map O.subtype = ρ.range := by
    rw [Subgroup.map_subtype_commutator, hcomm]
  let e1 : commutator ↥O ≃* ρ.range :=
    (Subgroup.equivMapOfInjective _ O.subtype O.subtype_injective).trans
      (MulEquiv.subgroupCongr h1)
  let e2 : ρ.range ≃* Matrix.SpecialLinearGroup (Fin 4) K := (MonoidHom.ofInjective hρinj).symm
  exact ⟨e1.trans (e2.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 4 K))⟩

theorem lieModel_quotient_orthDerived_pm {R : QuadraticForm K W} {G : Type} [Group G] {m f : ℕ}
    (hR : (QuadraticMap.polarBilin R).Nondegenerate) (hm : 4 ≤ m)
    (hdim : Module.finrank K W = 2 * m) (hf : 1 ≤ f) (hcard : Nat.card K = 2 ^ f)
    (φ : G ≃* ↥(orthDerived R)) :
    LieModel (G ⧸ Subgroup.center G) .POmegaPlus m 2 f ∨
      LieModel (G ⧸ Subgroup.center G) .POmegaMinus m 2 f := by
  rcases CFSG.GroupTheory.WeirSylow.exists_isometry_quadPlus_or_quadMinus R hR (by omega) hdim with
    he | ⟨b, c, hirr, he⟩
  · obtain ⟨e⟩ := he
    obtain ⟨hnd, hT⟩ := CFSG.ClassicalGroups.Orthogonal.regular_quadPlus (K := K) (n := m)
      (by omega)
    have : Inhabited (Fin m ⊕ Fin m) := ⟨Sum.inl ⟨0, by omega⟩⟩
    have : Nontrivial (Fin m ⊕ Fin m → K) := Pi.nontrivial
    have hZ : Subgroup.center ↥(orthDerived (CFSG.LieType.Universal.Spin.quadPlus m K)) = ⊥ :=
      CFSG.RankThree.PartOne.center_orthDerived_eq_bot hnd hT
    let φ' := φ.trans (CFSG.RankThree.PartOne.orthDerivedEquiv e)
    have hZG : Subgroup.center G = ⊥ := by
      have h1 := Subgroup.map_center_eq φ'
      rw [hZ] at h1
      exact (Subgroup.map_eq_bot_iff_of_injective _ φ'.injective).mp h1
    exact Or.inl (CFSG.LieType.CurtisTits.lieModel_of_mulEquiv
      (CFSG.RankThree.PartOne.Sec66T.centerQuotientEquivSelf hZG).symm
      (CFSG.RankThree.PartOne.lieModel_of_orthDerived_plus hm hf hcard e φ))
  · obtain ⟨e⟩ := he
    obtain ⟨hnd, hT⟩ := CFSG.ClassicalGroups.Orthogonal.regular_quadMinus (n := m) hm hirr
    have : Inhabited (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) := ⟨Sum.inl ⟨0, by omega⟩⟩
    have : Nontrivial (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) := Pi.nontrivial
    have hZ : Subgroup.center ↥(orthDerived (CFSG.LieType.Universal.Spin.quadMinus m K b c)) =
        ⊥ := CFSG.RankThree.PartOne.center_orthDerived_eq_bot hnd hT
    let φ' := φ.trans (CFSG.RankThree.PartOne.orthDerivedEquiv e)
    have hZG : Subgroup.center G = ⊥ := by
      have h1 := Subgroup.map_center_eq φ'
      rw [hZ] at h1
      exact (Subgroup.map_eq_bot_iff_of_injective _ φ'.injective).mp h1
    exact Or.inr (CFSG.LieType.CurtisTits.lieModel_of_mulEquiv
      (CFSG.RankThree.PartOne.Sec66T.centerQuotientEquivSelf hZG).symm
      (CFSG.RankThree.PartOne.lieModel_of_orthDerived_minus hm hf hcard hirr e φ))

end Models

section DeterminantTransport

variable {K : Type} [Field K] [CharP K 2]

theorem nonempty_mulEquiv_determinantFactor (F : Subgroup (DeterminantIsometries K))
    (hF : F = determinantLeftFactor K ∨ F = determinantRightFactor K) :
    Nonempty (Matrix.SpecialLinearGroup (Fin 2) K ≃* ↥F) := by
  have hsq : ∀ c : Kˣ, c ^ 2 = 1 → c = 1 := by
    intro c hc
    have h1 : ((c : K) - 1) ^ 2 = 0 := by
      have h2 : (c : K) ^ 2 = 1 := by rw [← Units.val_pow_eq_pow_val, hc, Units.val_one]
      have h3 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
      linear_combination h2 - (c : K) * h3 + h3
    exact Units.ext (sub_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 h1))
  rcases hF with rfl | rfl
  · have hinj : Function.Injective
        ((specialRho (K := K)).comp
          (MonoidHom.inl _ _)) := by
      rw [injective_iff_map_eq_one]
      intro A hA
      obtain ⟨c, hc2, hcA, -⟩ :=
        (specialRho_eq_one_iff
          (A, (1 : Matrix.SpecialLinearGroup (Fin 2) K))).1 hA
      rw [hsq c hc2, map_one] at hcA
      exact Matrix.SpecialLinearGroup.toGL_injective (hcA.trans (map_one _).symm)
    exact ⟨MonoidHom.ofInjective hinj⟩
  · have hinj : Function.Injective
        ((specialRho (K := K)).comp
          (MonoidHom.inr _ _)) := by
      rw [injective_iff_map_eq_one]
      intro A hA
      obtain ⟨c, hc2, -, hcA⟩ :=
        (specialRho_eq_one_iff
          ((1 : Matrix.SpecialLinearGroup (Fin 2) K), A)).1 hA
      rw [hsq c hc2, map_one] at hcA
      exact Matrix.SpecialLinearGroup.toGL_injective (hcA.trans (map_one _).symm)
    exact ⟨MonoidHom.ofInjective hinj⟩

end DeterminantTransport

theorem isComponentOf_map_subtype_of_normal {A : Type*} [Group A] (O : Subgroup A)
    (C F : Subgroup ↥O) (hFC : F ≤ C) (hn : (F.subgroupOf C).Normal)
    (hq : CFSG.IsQuasisimple ↥F) :
    CFSG.Open.IsComponentOf (F.map O.subtype) (C.map O.subtype) := by
  have hle : F.map O.subtype ≤ C.map O.subtype := Subgroup.map_mono hFC
  refine CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.isComponentOf_of_normal_normal
    (C := C.map O.subtype) (N := C.map O.subtype) hle le_rfl ?_
    (by rw [Subgroup.subgroupOf_self]; infer_instance)
    (CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (F.equivMapOfInjective O.subtype O.subtype_injective) hq)
  rw [Subgroup.normal_subgroupOf_iff hle]
  intro h k hh hk
  obtain ⟨f, hf, rfl⟩ := hh
  obtain ⟨c, hc, rfl⟩ := hk
  exact ⟨c * f * c⁻¹, (Subgroup.normal_subgroupOf_iff hFC).1 hn f c hf hc, by simp⟩

theorem eq_or_eq_of_component_join {A : Type*} [Group A] [Finite A] {J LA RA I : Subgroup A}
    (hLA : CFSG.Open.IsComponentOf LA J) (hRA : CFSG.Open.IsComponentOf RA J)
    (hJ : J = LA ⊔ RA) (hI : CFSG.Open.IsComponentOf I J) : I = LA ∨ I = RA := by
  obtain ⟨b, hb⟩ := exists_eq_of_isComponentOf_le_iSup (N := J)
    (fun b : Bool => if b then LA else RA)
    (fun b => by cases b <;> simpa using ‹_›) hI (by
      rw [iSup_bool_eq]
      exact hJ ▸ hI.1)
  cases b
  · exact Or.inr hb.symm
  · exact Or.inl hb.symm

section Abstract


variable {K : Type} [Field K] [Finite K] [CharP K 2] {W : Type} [AddCommGroup W] [Module K W]
  [FiniteDimensional K W]

theorem false_of_isComponent_orthDerived_high (hO : LieOrderFormulasInput) {f₀ : ℕ}
    (hf₀ : 1 ≤ f₀) (hK : Nat.card K = 2 ^ f₀) (R : QuadraticForm K W)
    (hR : (QuadraticMap.polarBilin R).Nondegenerate)
    (hT : ∃ U : Submodule K W, finrank K U = 3 ∧ ∀ u ∈ U, R u = 0)
    {M : Subgroup ↥(orthDerived R)} (hM : CFSG.IsComponent M)
    (hL : IsLThreeFour (↥M ⧸ Subgroup.center ↥M)) : False := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Nontrivial W := by
    obtain ⟨U, hU3, -⟩ := hT
    exact Module.nontrivial_of_finrank_pos (R := K) (by
      have := Submodule.finrank_le U
      omega)
  have hqs := CFSG.RankThree.PartOne.KCOrthogonal.isQuasisimple_orthDerived hR hT
  have hMtop : M = ⊤ :=
    CFSG.ComponentClassification.RestrictedStd.Spor.eq_top_of_isComponent_of_isQuasisimple hqs hM
  subst hMtop
  let eT : ↥(⊤ : Subgroup ↥(orthDerived R)) ≃* ↥(orthDerived R) := Subgroup.topEquiv
  have hL' : IsLThreeFour (↥(orthDerived R) ⧸ Subgroup.center ↥(orthDerived R)) :=
    IsLThreeFour.of_mulEquiv (QuotientGroup.congr _ _ eT (Subgroup.map_center_eq eT)) hL
  obtain ⟨m, hm⟩ := CFSG.ComponentClassification.UnbalancedCatalog.even_finrank_of_charTwo R hR
  have h6 : 2 * 3 ≤ finrank K W := by
    obtain ⟨U, hU3, hUs⟩ := hT
    have := CFSG.ComponentClassification.UnbalancedCatalog.two_mul_finrank_le_of_singular hR hUs
    omega
  by_cases hm4 : 4 ≤ m
  · rcases lieModel_quotient_orthDerived_pm hR hm4 (by omega) hf₀ hK (MulEquiv.refl _) with
      hmodel | hmodel
    · exact not_isLThreeFour_of_lieModel_two hmodel (by decide) hL'
    · exact not_isLThreeFour_of_lieModel_two hmodel (by decide) hL'
  · have hd6 : finrank K W = 6 := by omega
    obtain ⟨κ⟩ := klein_commutator_orthogonal_six_all R hR hd6 hT
    let e1 : ↥(orthDerived R) ≃* Matrix.SpecialLinearGroup (Fin 4) K :=
      ((CFSG.RankThree.PartOne.orthDerivedEquivCommutator R).symm.trans κ).trans
        (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 4 K).symm
    have hadm : StatedLieAdmissible .PSL 4 2 f₀ :=
      ⟨Nat.prime_two, hf₀, by norm_num, fun hc => absurd (Prod.mk.inj hc).1 (by norm_num),
        fun hc => absurd (Prod.mk.inj hc).1 (by norm_num)⟩
    obtain ⟨h43, -⟩ := block_central_of_isLThreeFour hO hK e1 hadm hL'
    exact absurd h43 (by norm_num)

theorem false_of_isComponent_orthDerived_minus (f₀ : ℕ) (hf₀ : 1 ≤ f₀)
    (hK : Nat.card K = 2 ^ f₀) (R : QuadraticForm K W)
    (hR : (QuadraticMap.polarBilin R).Nondegenerate)
    (hd : finrank K W = 4 ∨ finrank K W = 6)
    (hts : ∀ U : Submodule K W, finrank K U = finrank K W / 2 → ∃ u ∈ U, R u ≠ 0)
    {M : Subgroup ↥(orthDerived R)} (hM : CFSG.IsComponent M)
    (hL : IsLThreeFour (↥M ⧸ Subgroup.center ↥M)) : False := by
  classical
  obtain ⟨hs, hperf, hnonab, hidx, hodd, h4, h6⟩ :=
    CFSG.RankThree.PartOne.even_minus_four_six_actual_derived_extraction R hR hd hts
  change IsSimpleGroup ↥(orthDerived R) at hs
  haveI := hs
  have hqs : CFSG.IsQuasisimple ↥(orthDerived R) :=
    CFSG.RankThree.PartOne.KCOrthogonal.isQuasisimple_of_simple_nonabelian hnonab
  have hMtop : M = ⊤ :=
    CFSG.ComponentClassification.RestrictedStd.Spor.eq_top_of_isComponent_of_isQuasisimple hqs hM
  subst hMtop
  let eT : ↥(⊤ : Subgroup ↥(orthDerived R)) ≃* ↥(orthDerived R) := Subgroup.topEquiv
  have hL' : IsLThreeFour (↥(orthDerived R) ⧸ Subgroup.center ↥(orthDerived R)) :=
    IsLThreeFour.of_mulEquiv (QuotientGroup.congr _ _ eT (Subgroup.map_center_eq eT)) hL
  have hnab : ∃ a b : ↥(orthDerived R), a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    exact hnonab hcon
  have hZ : Subgroup.center ↥(orthDerived R) = ⊥ := up34_center_eq_bot_of_simple hnab
  have hcard : Nat.card ↥(orthDerived R) = 20160 := by
    have h1 := card_eq_of_isLThreeFour hL'
    have h2 : Nat.card (↥(orthDerived R) ⧸ Subgroup.center ↥(orthDerived R)) =
        Nat.card ↥(orthDerived R) := by
      refine Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hZ |>.trans
        QuotientGroup.quotientBot).toEquiv
    omega
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  rcases hd with hd4 | hd6
  · obtain ⟨E, _, _, D, ψ, ρ, -, -, -, hrange, hρcard⟩ := h4 hd4
    have h1 : Nat.card ↥(orthDerived R) = Nat.card K ^ 2 * (Nat.card K ^ 4 - 1) := by
      rw [← hρcard]
      exact (congrArg Nat.card (congrArg (fun H : Subgroup (W ≃ₗ[K] W) => (↥H : Type _))
        hrange.symm)).trans rfl
    rw [hcard] at h1
    generalize Nat.card K = q at h1 hq2
    by_cases hq8 : 8 ≤ q
    · have h2 : 64 ≤ q ^ 2 :=
        calc 64 = 8 ^ 2 := by norm_num
          _ ≤ q ^ 2 := Nat.pow_le_pow_left hq8 2
      have h3 : 4096 ≤ q ^ 4 :=
        calc 4096 = 8 ^ 4 := by norm_num
          _ ≤ q ^ 4 := Nat.pow_le_pow_left hq8 4
      have h4' : 64 * 4095 ≤ q ^ 2 * (q ^ 4 - 1) := Nat.mul_le_mul h2 (by omega)
      omega
    · push Not at hq8
      interval_cases q <;> omega
  · obtain ⟨E, _, _, D, ψ, ρ, -, -, -, hrange, hρcard⟩ := h6 hd6
    have h1 : Nat.card ↥(orthDerived R) = Nat.card K ^ 6 * (Nat.card K ^ 2 - 1) *
        (Nat.card K ^ 3 + 1) * (Nat.card K ^ 4 - 1) := by
      rw [← hρcard]
      exact (congrArg Nat.card (congrArg (fun H : Subgroup (W ≃ₗ[K] W) => (↥H : Type _))
        hrange.symm)).trans rfl
    rw [hcard] at h1
    generalize Nat.card K = q at h1 hq2
    have h2 : 64 ≤ q ^ 6 :=
      calc 64 = 2 ^ 6 := by norm_num
        _ ≤ q ^ 6 := Nat.pow_le_pow_left hq2 6
    have h3 : 4 ≤ q ^ 2 :=
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ q ^ 2 := Nat.pow_le_pow_left hq2 2
    have h4' : 8 ≤ q ^ 3 :=
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ q ^ 3 := Nat.pow_le_pow_left hq2 3
    have h5 : 16 ≤ q ^ 4 :=
      calc 16 = 2 ^ 4 := by norm_num
        _ ≤ q ^ 4 := Nat.pow_le_pow_left hq2 4
    have h6' : 64 * 3 * 9 * 15 ≤ q ^ 6 * (q ^ 2 - 1) * (q ^ 3 + 1) * (q ^ 4 - 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul h2 (by omega)) (by omega)) (by omega)
    omega


theorem false_of_isComponent_orthDerived_split (hO : LieOrderFormulasInput) {f₀ : ℕ}
    (hf₀ : 1 ≤ f₀) (hK : Nat.card K = 2 ^ f₀) (R : QuadraticForm K W)
    (hR : (QuadraticMap.polarBilin R).Nondegenerate) (hdim : finrank K W = 4)
    (hS : ∃ S : Submodule K W, finrank K S = 2 ∧ ∀ x ∈ S, R x = 0) (hK2 : Nat.card K ≠ 2)
    (hK3 : Nat.card K ≠ 3) {M : Subgroup ↥(orthDerived R)} (hM : CFSG.IsComponent M)
    (hL : IsLThreeFour (↥M ⧸ Subgroup.center ↥M)) : False := by
  classical
  obtain ⟨ψ, e, -, -, hsup, hqL, hqR, hnL, hnR, -, -, -⟩ :=
    orthogonal_split_four_derived hK2 hK3 R hR hdim hS
  have hJ : (commutator ↥(TauCeti.QuadraticMap.orthogonalGroup R)).map
      (TauCeti.QuadraticMap.orthogonalGroup R).subtype = orthDerived R :=
    Subgroup.map_subtype_commutator _
  have hLle : (determinantLeftFactor K).map e.symm.toMonoidHom ≤
      commutator ↥(TauCeti.QuadraticMap.orthogonalGroup R) := hsup ▸ le_sup_left
  have hRle : (determinantRightFactor K).map e.symm.toMonoidHom ≤
      commutator ↥(TauCeti.QuadraticMap.orthogonalGroup R) := hsup ▸ le_sup_right
  have hcL := isComponentOf_map_subtype_of_normal (TauCeti.QuadraticMap.orthogonalGroup R) _ _
    hLle hnL hqL
  have hcR := isComponentOf_map_subtype_of_normal (TauCeti.QuadraticMap.orthogonalGroup R) _ _
    hRle hnR hqR
  rw [hJ] at hcL hcR
  have hjoin : orthDerived R = ((determinantLeftFactor K).map e.symm.toMonoidHom).map
      (TauCeti.QuadraticMap.orthogonalGroup R).subtype ⊔
      ((determinantRightFactor K).map e.symm.toMonoidHom).map
        (TauCeti.QuadraticMap.orthogonalGroup R).subtype := by
    rw [← hJ, hsup, Subgroup.map_sup]
  have hIle : M.map (orthDerived R).subtype ≤ orthDerived R := Subgroup.map_subtype_le M
  have hsubM : (M.map (orthDerived R).subtype).subgroupOf (orthDerived R) = M :=
    Subgroup.comap_map_eq_self_of_injective (orthDerived R).subtype_injective M
  have hIc : CFSG.Open.IsComponentOf (M.map (orthDerived R).subtype) (orthDerived R) :=
    CFSG.Assembly.isComponentOf_iff_open.1
      ((isComponentOf_iff_isComponent_subgroupOf hIle).2 (by rw [hsubM]; exact hM))
  have hadm : StatedLieAdmissible .PSL 2 2 f₀ :=
    ⟨Nat.prime_two, hf₀, le_rfl, fun hc => hK2 (by rw [hK]; exact (Prod.mk.inj hc).2),
      fun hc => hK3 (by rw [hK]; exact (Prod.mk.inj hc).2)⟩
  have hF : ∀ F : Subgroup (DeterminantIsometries K),
      (F = determinantLeftFactor K ∨ F = determinantRightFactor K) →
      (M.map (orthDerived R).subtype =
        (F.map e.symm.toMonoidHom).map (TauCeti.QuadraticMap.orthogonalGroup R).subtype) →
      False := by
    intro F hFF hFM
    obtain ⟨eSL⟩ := nonempty_mulEquiv_determinantFactor F hFF
    let e1 : ↥M ≃* Matrix.SpecialLinearGroup (Fin 2) K :=
      ((M.equivMapOfInjective (orthDerived R).subtype (orthDerived R).subtype_injective).trans
        (MulEquiv.subgroupCongr hFM)).trans
        (((F.map e.symm.toMonoidHom).equivMapOfInjective
          (TauCeti.QuadraticMap.orthogonalGroup R).subtype
          (TauCeti.QuadraticMap.orthogonalGroup R).subtype_injective).symm.trans
          ((F.equivMapOfInjective e.symm.toMonoidHom e.symm.injective).symm.trans eSL.symm))
    obtain ⟨h23, -⟩ := block_central_of_isLThreeFour hO hK e1 hadm hL
    exact absurd h23 (by norm_num)
  haveI : Finite W := Module.finite_of_finite K
  haveI : Finite (W ≃ₗ[K] W) := Finite.of_injective (fun e : W ≃ₗ[K] W => (e : W → W))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  rcases eq_or_eq_of_component_join hcL hcR hjoin hIc with h | h
  · exact hF _ (Or.inl rfl) h
  · exact hF _ (Or.inr rfl) h

theorem false_of_isComponent_orthDerived (hO : LieOrderFormulasInput) {f₀ : ℕ}
    (hf₀ : 1 ≤ f₀) (hK : Nat.card K = 2 ^ f₀) (R : QuadraticForm K W)
    (hR : (QuadraticMap.polarBilin R).Nondegenerate) (h3 : 3 ≤ finrank K W)
    (hnex : ¬ SmallFixedException R) {M : Subgroup ↥(orthDerived R)} (hM : CFSG.IsComponent M)
    (hL : IsLThreeFour (↥M ⧸ Subgroup.center ↥M)) : False := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hT : ∃ U : Submodule K W, finrank K U = 3 ∧ ∀ x ∈ U, R x = 0
  · exact false_of_isComponent_orthDerived_high hO hf₀ hK R hR hT hM hL
  · obtain ⟨⟨n, hn⟩, -, hnf, -⟩ :=
      CFSG.ComponentClassification.UnbalancedCatalog.finite_even_regular_quadratic_normal_forms R hR
    by_cases hS : ∃ U : Submodule K W, finrank K U = n ∧ ∀ u ∈ U, R u = 0
    ·
      obtain ⟨U, hUn, hUQ⟩ := hS
      have hn2 : n = 2 := by
        by_contra hne
        exact hT (CFSG.RankThree.PartOne.KCOrthogonal.exists_threeSingular_of_le R hUQ (by omega))
      subst hn2
      have hc2 : Nat.card K ≠ 2 := fun hc =>
        hnex (Or.inr ⟨⟨by omega, U, hUn, hUQ⟩, Or.inl hc⟩)
      have hc3 : Nat.card K ≠ 3 := fun hc =>
        hnex (Or.inr ⟨⟨by omega, U, hUn, hUQ⟩, Or.inr hc⟩)
      exact false_of_isComponent_orthDerived_split hO hf₀ hK R hR (by omega) ⟨U, hUn, hUQ⟩ hc2 hc3
        hM hL
    · have hts : ∀ U : Submodule K W, finrank K U = n → ∃ u ∈ U, R u ≠ 0 := by
        intro U hU
        by_contra hcon
        push Not at hcon
        exact hS ⟨U, hU, hcon⟩
      rcases hnf n (by omega) hn with ⟨b, hb⟩ | ⟨β, γ, -, -, b, hb⟩
      · exfalso
        refine hS ⟨Submodule.span K (Set.range fun i : Fin n => b (Sum.inl i)), ?_, ?_⟩
        · exact (finrank_span_eq_card (b.linearIndependent.comp _ Sum.inl_injective)).trans
            (by simp)
        · intro u hu
          obtain ⟨x, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hu
          simpa using hb x 0
      ·
        have hU : ∀ u ∈ Submodule.span K (Set.range fun i : Fin (n - 1) => b (Sum.inl i)),
            R u = 0 := by
          intro u hu
          obtain ⟨x, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hu
          simpa using hb x 0 0 0
        have hdU : finrank K (Submodule.span K (Set.range fun i : Fin (n - 1) =>
            b (Sum.inl i))) = n - 1 :=
          (finrank_span_eq_card (b.linearIndependent.comp _ Sum.inl_injective)).trans (by simp)
        have hn23 : n = 2 ∨ n = 3 := by
          by_contra hne
          exact hT (CFSG.RankThree.PartOne.KCOrthogonal.exists_threeSingular_of_le R hU
            (by omega))
        exact false_of_isComponent_orthDerived_minus f₀ hf₀ hK R hR (by omega)
          (fun U hU => hts U (by omega)) hM hL

end Abstract

section Fixed


variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V}

theorem false_of_isComponentOf_fixedLayer (hO : LieOrderFormulasInput) {f₀ : ℕ} (hf₀ : 1 ≤ f₀)
    (hK : Nat.card K = 2 ^ f₀) [CharP K 2] [Nontrivial V]
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {p : ℕ} (hx : OddOrderIsometry Q p x)
    (hlist : FixedLayerListed Q x) {I : Subgroup (ProjOrthDerived Q)}
    (hI : CFSG.Open.IsComponentOf I (centralizerImage Q x)) (hIle : I ≤ fixedComponentImage Q x)
    (hL : IsLThreeFour (↥I ⧸ Subgroup.center ↥I)) : False := by
  have hLN : fixedComponentImage Q x ≤ centralizerImage Q x :=
    fixedComponentImage_le_centralizerImage
  have hIc : CFSG.Assembly.IsComponentOf I (fixedComponentImage Q x) :=
    (CFSG.Assembly.isComponentOf_iff_open.2 hI).of_le_of_le hIle hLN
  have hIc' : CFSG.IsComponent (I.subgroupOf (fixedComponentImage Q x)) :=
    (isComponentOf_iff_isComponent_subgroupOf hIle).1 hIc
  let φ := fixedComponentImageEquiv hQ hx
  have hM : CFSG.IsComponent ((I.subgroupOf (fixedComponentImage Q x)).map φ.toMonoidHom) :=
    CFSG.LocalCores.isComponent_map_mulEquiv φ hIc'
  let eI : ↥I ≃* ↥(I.subgroupOf (fixedComponentImage Q x)) :=
    (Subgroup.subgroupOfEquivOfLe hIle).symm
  let eM := (I.subgroupOf (fixedComponentImage Q x)).equivMapOfInjective φ.toMonoidHom φ.injective
  let e := eI.trans eM
  have hL' : IsLThreeFour (↥((I.subgroupOf (fixedComponentImage Q x)).map φ.toMonoidHom) ⧸
      Subgroup.center ↥((I.subgroupOf (fixedComponentImage Q x)).map φ.toMonoidHom)) :=
    IsLThreeFour.of_mulEquiv (QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)) hL
  exact false_of_isComponent_orthDerived hO hf₀ hK _ hx.polarBilin_fixed_nondegenerate hlist.1
    hlist.2 hM hL'

end Fixed

end CFSG.HardMathSupport.Dickson.Sec6.OrthBlocks
