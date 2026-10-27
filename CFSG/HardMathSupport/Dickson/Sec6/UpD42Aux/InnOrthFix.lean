module

public import CFSG.HardMathSupport.Dickson.Sec6.UpD42Aux.Defs
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnOrthFix
public import CFSG.RankThree.PartOne.KC.OrthogonalCommutatorRot
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotSwapPair
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatTypeDetOrders

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.Classical2 CFSG.LocalAnalysis.ComponentInitial
  CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit

theorem card_catalogLie_of_isD42 {d : TauCeti.ValidLieTypeIndex} (hd : IsD42Index d.1) :
    Nat.card (TauCeti.CFSGIndex.lie d).Group = CFSG.Open.ordD 4 2 := by
  obtain ⟨idx, hv⟩ := d
  cases idx with
  | D r q =>
      obtain ⟨rfl, hp, he⟩ := hd
      have hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
          (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.D 4 q, hv⟩).Group .POmegaPlus 4 q.p
          q.exponent :=
        CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD 4 q hv (MulEquiv.refl _)
      rw [hp, he] at hmodel
      have hcard := (CFSG.Timmesfeld.card_statedClassicalModel_two hmodel).2.2.2.1 rfl
      simpa using hcard
  | _ => exact hd.elim

theorem card_centralQuotient_of_isD42 {Q : Type} [Group Q]
    (h : IsCatalogLieIso Q IsD42Index) : Nat.card Q = CFSG.Open.ordD 4 2 := by
  obtain ⟨d, hd, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv]
  exact card_catalogLie_of_isD42 hd

theorem factorization_two_ordD_four_two : (CFSG.Open.ordD 4 2).factorization 2 = 12 := by
  have h := CFSG.SeitzReduction.OmegaPilot.factorization_two_ordD (g := 1) (n := 4)
    (by norm_num) (by norm_num)
  simpa using h

theorem five_dvd_ordD_four_two : 5 ∣ CFSG.Open.ordD 4 2 := by
  decide +kernel

theorem center_eq_bot_of_isSimpleGroup_noncomm {X : Type*} [Group X] [IsSimpleGroup X]
    (hnc : ∃ a b : X, a * b ≠ b * a) : Subgroup.center X = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnc
    exact hab (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top a) b).symm

theorem one_le_fieldExponent_of_card_eq_two_pow {K : Type} [Field K] [Finite K] {f : ℕ}
    (hK : Nat.card K = 2 ^ f) : 1 ≤ f := by
  rcases Nat.eq_zero_or_pos f with rfl | h
  · rw [pow_zero] at hK
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    omega
  · exact h

theorem factorization_two_card_sl2 {K : Type} [Field K] [Finite K] {f : ℕ}
    (hK : Nat.card K = 2 ^ f) (hf : 1 ≤ f) :
    (Nat.card (Matrix.SpecialLinearGroup (Fin 2) K)).factorization 2 = f := by
  rw [CFSG.GorensteinWalter.sl2_card_formula K, hK]
  have hne : (2 ^ f) ^ 2 - 1 ≠ 0 := by
    have h2 : 1 < (2 ^ f) ^ 2 := by
      have h1 : 2 ≤ 2 ^ f := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
      nlinarith
    exact (Nat.sub_pos_of_lt h2).ne'
  have hpow : ((2 ^ f)).factorization 2 = f := by
    rw [Nat.Prime.factorization_pow Nat.prime_two]
    simp
  have hodd0 : (((2 ^ f) ^ 2 - 1)).factorization 2 = 0 := by
    refine Nat.factorization_eq_zero_of_not_dvd (fun h2 => ?_)
    have hodd : Odd (((2 ^ f) ^ 2) - 1) := by
      have h := CFSG.Timmesfeld.ClassicalOrders.odd_two_pow_pow_sub_one (f := f) (n := 2)
        hf (by norm_num)
      simpa using h
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
  rw [Nat.factorization_mul (by positivity) hne, Finsupp.add_apply, hpow, hodd0, add_zero]

theorem exists_threeSingular_of_four_le {K : Type} [Field K] [Finite K] [CharP K 2]
    {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    {R : QuadraticForm K W} (hR : (QuadraticMap.polarBilin R).Nondegenerate)
    {n : ℕ} (hdim : Module.finrank K W = 2 * n) (hn : 4 ≤ n) :
    ∃ U : Submodule K W, Module.finrank K U = 3 ∧ ∀ u ∈ U, R u = 0 := by
  obtain ⟨-, -, -, -, -, hthree⟩ :=
    CFSG.ComponentClassification.UnbalancedCatalog.finite_even_regular_quadratic_normal_forms
      R hR
  obtain ⟨P₁, P₂, P₃, h12, h13, h23⟩ := hthree n hdim hn
  exact CFSG.ClassicalGroups.Orthogonal.exists_totallySingular_of_hypPairs h12 h13 h23

theorem card_orthDerived_of_top
    {K : Type} [Field K] [Finite K] [CharP K 2] {W : Type} [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] {R : QuadraticForm K W}
    {M : Subgroup ↥(orthDerived R)}
    (hcat : IsCatalogLieIso (↥M ⧸ Subgroup.center ↥M) IsD42Index)
    (hMtop : M = ⊤) (hZ : Subgroup.center ↥(orthDerived R) = ⊥) :
    Nat.card ↥(orthDerived R) = CFSG.Open.ordD 4 2 := by
  have hquotM : Nat.card (↥M ⧸ Subgroup.center ↥M) =
      Nat.card (↥(orthDerived R) ⧸ Subgroup.center ↥(orthDerived R)) := by
    refine Nat.card_congr ?_
    let eu : ↥M ≃* ↥(orthDerived R) :=
      (MulEquiv.subgroupCongr hMtop).trans Subgroup.topEquiv
    exact (QuotientGroup.congr _ _ eu (Subgroup.map_center_eq eu)).toEquiv
  have hq : Nat.card (↥(orthDerived R) ⧸ Subgroup.center ↥(orthDerived R)) =
      Nat.card ↥(orthDerived R) := by
    rw [hZ]
    exact Nat.card_congr QuotientGroup.quotientBot.toEquiv
  rw [← hq, ← hquotM]
  exact card_centralQuotient_of_isD42 hcat

theorem d42_orthogonal_high
    {K : Type} [Field K] [Finite K] [CharP K 2] {W : Type} [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] {f n : ℕ} (hK : Nat.card K = 2 ^ f) (hf : 1 ≤ f)
    {R : QuadraticForm K W} (hR : (QuadraticMap.polarBilin R).Nondegenerate)
    (hn : 4 ≤ n) (hdim : Module.finrank K W = 2 * n)
    (hT : ∃ U : Submodule K W, Module.finrank K U = 3 ∧ ∀ u ∈ U, R u = 0)
    {M : Subgroup ↥(orthDerived R)} (hM : CFSG.IsComponent M)
    (hcat : IsCatalogLieIso (↥M ⧸ Subgroup.center ↥M) IsD42Index) :
    f = 1 ∧ Module.finrank K W = 8 := by
  classical
  haveI : Nontrivial W := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  have hqs : CFSG.IsQuasisimple ↥(orthDerived R) :=
    CFSG.RankThree.PartOne.KCOrthogonal.isQuasisimple_orthDerived hR hT
  have hMtop : M = ⊤ :=
    CFSG.ComponentClassification.RestrictedStd.Spor.eq_top_of_isComponent_of_isQuasisimple hqs hM
  have hZ : Subgroup.center ↥(orthDerived R) = ⊥ :=
    CFSG.RankThree.PartOne.center_orthDerived_eq_bot hR hT
  have hN : Nat.card (↥M ⧸ Subgroup.center ↥M) = CFSG.Open.ordD 4 2 :=
    card_centralQuotient_of_isD42 hcat
  have hquotM : Nat.card (↥M ⧸ Subgroup.center ↥M) =
      Nat.card (↥(orthDerived R) ⧸ Subgroup.center ↥(orthDerived R)) := by
    refine Nat.card_congr ?_
    let eu : ↥M ≃* ↥(orthDerived R) :=
      (MulEquiv.subgroupCongr hMtop).trans Subgroup.topEquiv
    exact (QuotientGroup.congr _ _ eu (Subgroup.map_center_eq eu)).toEquiv
  have hq : Nat.card (↥(orthDerived R) ⧸ Subgroup.center ↥(orthDerived R)) =
      Nat.card ↥(orthDerived R) := by
    rw [hZ]
    exact Nat.card_congr QuotientGroup.quotientBot.toEquiv
  rcases CFSG.HardMathSupport.Dickson.Sec6.OrthBlocks.lieModel_quotient_orthDerived_pm
      (K := K) (W := W) hR hn hdim hf hK
      (MulEquiv.refl ↥(orthDerived R)) with hplus | hminus
  · have hsc : CFSG.Open.StatedClassicalModel
        (↥(orthDerived R) ⧸ Subgroup.center ↥(orthDerived R)) .POmegaPlus n 2 f :=
      CFSG.Blueprint.LieModel.statedClassicalModel hplus (by decide)
    have hcard := (CFSG.Timmesfeld.card_statedClassicalModel_two hsc).2.2.2.1 rfl
    have horder : CFSG.Open.ordD 4 2 = CFSG.Open.ordD n (2 ^ f) := by
      rw [← hN, hquotM, hcard]
    obtain ⟨h4, hf1⟩ := CFSG.SeitzReduction.OmegaPilot.ordD_eq_ordD (n := 4) (g := 1)
      (m := n) (f := f) (by norm_num) (by norm_num) hn hf horder
    have hn4 : n = 4 := h4.symm
    have hf' : f = 1 := hf1.symm
    rw [hn4] at hdim
    exact ⟨hf', by omega⟩
  · have hsc : CFSG.Open.StatedClassicalModel
        (↥(orthDerived R) ⧸ Subgroup.center ↥(orthDerived R)) .POmegaMinus n 2 f :=
      CFSG.Blueprint.LieModel.statedClassicalModel hminus (by decide)
    have hcard := (CFSG.Timmesfeld.card_statedClassicalModel_two hsc).2.2.2.2 rfl
    have horder : CFSG.Open.ordD 4 2 = CFSG.Open.ordTwistedD n (2 ^ f) := by
      rw [← hN, hquotM, hcard]
    exact ((CFSG.SeitzReduction.OmegaPilot.ordTwistedD_ne_ordD (n := n) (g := f) (m := 4)
      (f := 1) hn hf (by norm_num) (by norm_num)) (by simpa using horder.symm)).elim

theorem d42_orthogonal_dim_zero
    {K : Type} [Field K] [Finite K] [CharP K 2] {W : Type} [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] {R : QuadraticForm K W}
    {M : Subgroup ↥(orthDerived R)} (hM : CFSG.IsComponent M)
    (hdim : Module.finrank K W = 0) : False := by
  classical
  haveI : Group.IsSolvable ↥(TauCeti.QuadraticMap.orthogonalGroup R) :=
    CFSG.ComponentClassification.CatalogueBOrthogonal.orthogonal_zero_solvable R hdim
  haveI : Group.IsSolvable ↥M :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.inclusion
        (CFSG.RankThree.PartOne.KCOrthogonal.orthDerived_le_orthogonalGroup (Q := R))).comp
        M.subtype)
      (by
        intro x y h
        have hamb : ((M.subtype x : ↥(orthDerived R)) : W ≃ₗ[K] W) =
            ((M.subtype y : ↥(orthDerived R)) : W ≃ₗ[K] W) :=
          congrArg (fun z : ↥(TauCeti.QuadraticMap.orthogonalGroup R) =>
            (z : W ≃ₗ[K] W)) h
        exact Subtype.ext (Subtype.ext hamb))
  haveI : Nontrivial ↥M := CFSG.LocalCores.isQuasisimple_nontrivial hM.1
  haveI : Group.IsPerfect ↥M := hM.1.1
  exact Group.IsPerfect.not_isSolvable (↥M) inferInstance

theorem d42_orthogonal_dim_two
    {K : Type} [Field K] [Finite K] [CharP K 2] {W : Type} [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] {R : QuadraticForm K W}
    (hR : (QuadraticMap.polarBilin R).Nondegenerate)
    {M : Subgroup ↥(orthDerived R)} (hM : CFSG.IsComponent M)
    (hdim : Module.finrank K W = 2) : False := by
  classical
  let O := TauCeti.QuadraticMap.orthogonalGroup R
  have hJ : (commutator ↥O).map O.subtype = orthDerived R :=
    Subgroup.map_subtype_commutator _
  have hrot : ∀ x ∈ orthDerived R, x ∈ CFSG.RankThree.PartOne.KCOrthComm.rotGroup R hR := by
    intro x hx
    rw [← hJ, Subgroup.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨y, (Abelianization.commutator_subset_ker
      (CFSG.RankThree.OrthogonalInvolutions.dicksonHom R hR)) hy, rfl⟩
  have hcommΩ : ∀ a b : ↥(orthDerived R), a * b = b * a := by
    intro a b
    exact Subtype.ext (CFSG.RankThree.PartOne.KCOrthComm.commute_of_mem_rotGroup hdim
      (hrot a a.2) (hrot b b.2))
  haveI : Group.IsSolvable ↥M :=
    Group.isSolvable_of_comm (fun a b : ↥M => Subtype.ext (hcommΩ _ _))
  haveI : Nontrivial ↥M := CFSG.LocalCores.isQuasisimple_nontrivial hM.1
  haveI : Group.IsPerfect ↥M := hM.1.1
  exact Group.IsPerfect.not_isSolvable (↥M) inferInstance

theorem d42_orthogonal_minus_four
    {K : Type} [Field K] [Finite K] [CharP K 2] {W : Type} [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf : 1 ≤ f)
    {R : QuadraticForm K W} (hR : (QuadraticMap.polarBilin R).Nondegenerate)
    (hdim : Module.finrank K W = 4)
    (hts : ∀ U : Submodule K W, Module.finrank K U = 4 / 2 → ∃ u ∈ U, R u ≠ 0)
    {M : Subgroup ↥(orthDerived R)} (hM : CFSG.IsComponent M)
    (hcat : IsCatalogLieIso (↥M ⧸ Subgroup.center ↥M) IsD42Index) : False := by
  classical
  obtain ⟨hs, -, hnonab, -, -, h4, -⟩ :=
    CFSG.RankThree.PartOne.even_minus_four_six_actual_derived_extraction R hR
      (Or.inl hdim) (fun U hU => hts U (by simpa [hdim] using hU))
  haveI := hs
  have hnonab' : ∃ a b : ↥(orthDerived R), a * b ≠ b * a := by
    simpa only [not_forall] using hnonab
  have hZ : Subgroup.center ↥(orthDerived R) = ⊥ :=
    center_eq_bot_of_isSimpleGroup_noncomm hnonab'
  have hqs : CFSG.IsQuasisimple ↥(orthDerived R) :=
    CFSG.RankThree.PartOne.KCOrthogonal.isQuasisimple_of_simple_nonabelian hnonab
  have hMtop : M = ⊤ :=
    CFSG.ComponentClassification.RestrictedStd.Spor.eq_top_of_isComponent_of_isQuasisimple hqs hM
  have hcardN : Nat.card ↥(orthDerived R) = CFSG.Open.ordD 4 2 :=
    card_orthDerived_of_top hcat hMtop hZ
  obtain ⟨E, _, _, D, ψ, ρ, -, -, -, hrange, hcardρ⟩ := h4 hdim
  have hΩord : Nat.card ↥(orthDerived R) = Nat.card K ^ 2 * (Nat.card K ^ 4 - 1) := by
    rw [Nat.card_congr (MulEquiv.subgroupCongr hrange).symm.toEquiv]
    exact hcardρ
  have hfac : (Nat.card ↥(orthDerived R)).factorization 2 = 2 * f := by
    rw [hΩord, hK]
    have hne : ((2 ^ f) ^ 4 - 1) ≠ 0 := by
      have h2 : 1 < (2 ^ f) ^ 4 := by
        have h1 : 2 ≤ 2 ^ f := by
          calc 2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
        calc 1 < 2 := by norm_num
          _ ≤ 2 ^ f := h1
          _ ≤ (2 ^ f) ^ 4 := by
            simpa using Nat.pow_le_pow_right (Nat.one_le_pow _ _ (by norm_num : 1 ≤ 2))
              (by norm_num : 1 ≤ 4)
      exact (Nat.sub_pos_of_lt h2).ne'
    have hpow : (((2 ^ f) ^ 2)).factorization 2 = 2 * f := by
      rw [show (2 ^ f) ^ 2 = 2 ^ (f * 2) by rw [pow_mul],
        Nat.Prime.factorization_pow Nat.prime_two]
      simp [mul_comm]
    have hodd0 : (((2 ^ f) ^ 4 - 1)).factorization 2 = 0 := by
      refine Nat.factorization_eq_zero_of_not_dvd (fun h2 => ?_)
      have hodd : Odd (((2 ^ f) ^ 4) - 1) := by
        have h := CFSG.Timmesfeld.ClassicalOrders.odd_two_pow_pow_sub_one (f := f) (n := 4)
          hf (by norm_num)
        simpa using h
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
    rw [Nat.factorization_mul (by positivity) hne, Finsupp.add_apply, hpow, hodd0, add_zero]
  have hfacN : (CFSG.Open.ordD 4 2).factorization 2 = 2 * f := by
    rw [← hcardN]
    exact hfac
  rw [factorization_two_ordD_four_two] at hfacN
  have hf6 : f = 6 := by omega
  subst hf6
  have hEq : CFSG.Open.ordD 4 2 = Nat.card K ^ 2 * (Nat.card K ^ 4 - 1) := by
    rw [← hcardN, hΩord]
  rw [hK] at hEq
  have hNval : CFSG.Open.ordD 4 2 = 174182400 := by decide +kernel
  rw [hNval] at hEq
  norm_num at hEq

theorem d42_orthogonal_minus_six
    {K : Type} [Field K] [Finite K] [CharP K 2] {W : Type} [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf : 1 ≤ f)
    {R : QuadraticForm K W} (hR : (QuadraticMap.polarBilin R).Nondegenerate)
    (hdim : Module.finrank K W = 6)
    (hts : ∀ U : Submodule K W, Module.finrank K U = 6 / 2 → ∃ u ∈ U, R u ≠ 0)
    {M : Subgroup ↥(orthDerived R)} (hM : CFSG.IsComponent M)
    (hcat : IsCatalogLieIso (↥M ⧸ Subgroup.center ↥M) IsD42Index) : False := by
  classical
  obtain ⟨hs, -, hnonab, -, -, -, h6⟩ :=
    CFSG.RankThree.PartOne.even_minus_four_six_actual_derived_extraction R hR
      (Or.inr hdim) (fun U hU => hts U (by simpa [hdim] using hU))
  haveI := hs
  have hnonab' : ∃ a b : ↥(orthDerived R), a * b ≠ b * a := by
    simpa only [not_forall] using hnonab
  have hZ : Subgroup.center ↥(orthDerived R) = ⊥ :=
    center_eq_bot_of_isSimpleGroup_noncomm hnonab'
  have hqs : CFSG.IsQuasisimple ↥(orthDerived R) :=
    CFSG.RankThree.PartOne.KCOrthogonal.isQuasisimple_of_simple_nonabelian hnonab
  have hMtop : M = ⊤ :=
    CFSG.ComponentClassification.RestrictedStd.Spor.eq_top_of_isComponent_of_isQuasisimple hqs hM
  have hcardN : Nat.card ↥(orthDerived R) = CFSG.Open.ordD 4 2 :=
    card_orthDerived_of_top hcat hMtop hZ
  obtain ⟨E, _, _, D, ψ, ρ, -, -, -, hrange, hcardρ⟩ := h6 hdim
  have hΩord : Nat.card ↥(orthDerived R) =
      Nat.card K ^ 6 * (Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 + 1) *
        (Nat.card K ^ 4 - 1) := by
    rw [Nat.card_congr (MulEquiv.subgroupCongr hrange).symm.toEquiv]
    exact hcardρ
  have hfac : (Nat.card ↥(orthDerived R)).factorization 2 = 6 * f := by
    rw [hΩord, hK]
    have h2ne : ((2 ^ f) ^ 2 - 1) ≠ 0 := by
      have h2 : 1 < (2 ^ f) ^ 2 := by
        have h1 : 2 ≤ 2 ^ f := by
          calc 2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
        nlinarith
      exact (Nat.sub_pos_of_lt h2).ne'
    have h3ne : ((2 ^ f) ^ 3 + 1) ≠ 0 := by positivity
    have h4ne : ((2 ^ f) ^ 4 - 1) ≠ 0 := by
      have h2 : 1 < (2 ^ f) ^ 4 := by
        have h1 : 2 ≤ 2 ^ f := by
          calc 2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
        calc 1 < 2 := by norm_num
          _ ≤ 2 ^ f := h1
          _ ≤ (2 ^ f) ^ 4 := by
            simpa using Nat.pow_le_pow_right (Nat.one_le_pow _ _ (by norm_num : 1 ≤ 2))
              (by norm_num : 1 ≤ 4)
      exact (Nat.sub_pos_of_lt h2).ne'
    have h2odd : Odd (((2 ^ f) ^ 2) - 1) := by
      have h := CFSG.Timmesfeld.ClassicalOrders.odd_two_pow_pow_sub_one (f := f) (n := 2)
        hf (by norm_num)
      simpa using h
    have h3odd : Odd (((2 ^ f) ^ 3) + 1) := by
      have h := CFSG.Timmesfeld.ClassicalOrders.odd_two_pow_pow_add_one (f := f) (n := 3)
        hf (by norm_num)
      simpa using h
    have h4odd : Odd (((2 ^ f) ^ 4) - 1) := by
      have h := CFSG.Timmesfeld.ClassicalOrders.odd_two_pow_pow_sub_one (f := f) (n := 4)
        hf (by norm_num)
      simpa using h
    have hodd : Odd ((((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 + 1)) * ((2 ^ f) ^ 4 - 1)) :=
      (h2odd.mul h3odd).mul h4odd
    have hassoc : (2 ^ f) ^ 6 * ((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 + 1) * ((2 ^ f) ^ 4 - 1) =
        (2 ^ f) ^ 6 * ((((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 + 1)) * ((2 ^ f) ^ 4 - 1)) := by
      ring_nf
    rw [hassoc, Nat.factorization_mul (by positivity) hodd.pos.ne']
    simp only [Finsupp.add_apply]
    rw [Nat.factorization_eq_zero_of_not_dvd
      (fun h => (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h)), add_zero]
    rw [show (2 ^ f) ^ 6 = 2 ^ (f * 6) by rw [pow_mul],
      Nat.Prime.factorization_pow Nat.prime_two]
    simp [mul_comm]
  have hfacN : (CFSG.Open.ordD 4 2).factorization 2 = 6 * f := by
    rw [← hcardN]
    exact hfac
  rw [factorization_two_ordD_four_two] at hfacN
  have hf2 : f = 2 := by omega
  subst hf2
  have hEq : CFSG.Open.ordD 4 2 =
      Nat.card K ^ 6 * (Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 + 1) *
        (Nat.card K ^ 4 - 1) := by
    rw [← hcardN, hΩord]
  rw [hK] at hEq
  have hNval : CFSG.Open.ordD 4 2 = 174182400 := by decide +kernel
  rw [hNval] at hEq
  norm_num at hEq

theorem d42_orthogonal_split_six
    {K : Type} [Field K] [Finite K] [CharP K 2] {W : Type} [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf : 1 ≤ f)
    {R : QuadraticForm K W} (hR : (QuadraticMap.polarBilin R).Nondegenerate)
    (hdim : Module.finrank K W = 6)
    (hT : ∃ U : Submodule K W, Module.finrank K U = 3 ∧ ∀ u ∈ U, R u = 0)
    {M : Subgroup ↥(orthDerived R)} (hM : CFSG.IsComponent M)
    (hcat : IsCatalogLieIso (↥M ⧸ Subgroup.center ↥M) IsD42Index) : False := by
  classical
  haveI : Nontrivial W := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  have hqs : CFSG.IsQuasisimple ↥(orthDerived R) :=
    CFSG.RankThree.PartOne.KCOrthogonal.isQuasisimple_orthDerived hR hT
  have hMtop : M = ⊤ :=
    CFSG.ComponentClassification.RestrictedStd.Spor.eq_top_of_isComponent_of_isQuasisimple hqs hM
  have hZ : Subgroup.center ↥(orthDerived R) = ⊥ :=
    CFSG.RankThree.PartOne.center_orthDerived_eq_bot hR hT
  have hcardN : Nat.card ↥(orthDerived R) = CFSG.Open.ordD 4 2 :=
    card_orthDerived_of_top hcat hMtop hZ
  obtain ⟨eSL⟩ :=
    CFSG.HardMathSupport.Dickson.Sec6.OrthBlocks.klein_commutator_orthogonal_six_all R hR hdim hT
  have hJ : (commutator ↥(TauCeti.QuadraticMap.orthogonalGroup R)).map
      (TauCeti.QuadraticMap.orthogonalGroup R).subtype = orthDerived R :=
    Subgroup.map_subtype_commutator _
  let eMap : ↥(commutator ↥(TauCeti.QuadraticMap.orthogonalGroup R)) ≃*
      ↥((commutator ↥(TauCeti.QuadraticMap.orthogonalGroup R)).map
        (TauCeti.QuadraticMap.orthogonalGroup R).subtype) :=
    Subgroup.equivMapOfInjective _ _ (TauCeti.QuadraticMap.orthogonalGroup R).subtype_injective
  have hcardSL : Nat.card ↥(orthDerived R) = Nat.card ↥(StatedSL 4 K) :=
    Nat.card_congr ((eMap.trans (MulEquiv.subgroupCongr hJ)).symm.trans eSL).toEquiv
  have hcardSL4 : Nat.card ↥(StatedSL 4 K) =
      Nat.card K ^ 6 * ∏ j ∈ Finset.Icc 2 4, (Nat.card K ^ j - 1) := by
    rw [CFSG.Open.StatedAPI.card_statedSL,
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (n := 4) (by norm_num)]
  have hfac : (Nat.card ↥(orthDerived R)).factorization 2 = 6 * f := by
    rw [hcardSL, hcardSL4, hK]
    have hprod_odd : Odd (∏ j ∈ Finset.Icc 2 4, ((2 ^ f) ^ j - 1)) := by
      refine Finset.prod_induction _ _ (fun a b ha hb => ha.mul hb) odd_one ?_
      intro j hj
      exact CFSG.Timmesfeld.ClassicalOrders.odd_two_pow_pow_sub_one hf (by
        have := (Finset.mem_Icc.mp hj).1
        omega)
    rw [Nat.factorization_mul (by positivity) hprod_odd.pos.ne']
    simp only [Finsupp.add_apply]
    rw [Nat.factorization_eq_zero_of_not_dvd
      (fun h => (Nat.not_even_iff_odd.mpr hprod_odd) (even_iff_two_dvd.mpr h)), add_zero]
    rw [show (2 ^ f) ^ 6 = 2 ^ (f * 6) by rw [pow_mul],
      Nat.Prime.factorization_pow Nat.prime_two]
    simp [mul_comm]
  have hfacN : (CFSG.Open.ordD 4 2).factorization 2 = 6 * f := by
    rw [← hcardN]
    exact hfac
  rw [factorization_two_ordD_four_two] at hfacN
  have hf2 : f = 2 := by omega
  subst hf2
  have hEq : CFSG.Open.ordD 4 2 =
      Nat.card K ^ 6 * ∏ j ∈ Finset.Icc 2 4, (Nat.card K ^ j - 1) := by
    rw [← hcardN, hcardSL, hcardSL4]
  rw [hK] at hEq
  exact absurd hEq (by decide +kernel)

theorem d42_orthogonal_split_four_big
    {K : Type} [Field K] [Finite K] [CharP K 2] {W : Type} [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf : 1 ≤ f)
    {R : QuadraticForm K W} (hR : (QuadraticMap.polarBilin R).Nondegenerate)
    (hdim : Module.finrank K W = 4)
    (hS : ∃ S : Submodule K W, Module.finrank K S = 2 ∧ ∀ x ∈ S, R x = 0)
    (hK2 : Nat.card K ≠ 2)
    {M : Subgroup ↥(orthDerived R)} (hM : CFSG.IsComponent M)
    (hcat : IsCatalogLieIso (↥M ⧸ Subgroup.center ↥M) IsD42Index) : False := by
  classical
  have hK3 : Nat.card K ≠ 3 := by
    intro h3
    have h2f : 2 ^ f = 3 := by omega
    have heven : Even (2 ^ f) := Nat.even_pow.mpr ⟨even_two, by omega⟩
    rw [h2f] at heven
    norm_num at heven
  obtain ⟨ψ, e, -, -, hsup, hqL, hqR, hnL, hnR, -, -, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.orthogonal_split_four_derived hK2 hK3 R hR hdim hS
  have hJ : (commutator ↥(TauCeti.QuadraticMap.orthogonalGroup R)).map
      (TauCeti.QuadraticMap.orthogonalGroup R).subtype = orthDerived R :=
    Subgroup.map_subtype_commutator _
  have hLle : (determinantLeftFactor K).map
      e.symm.toMonoidHom ≤ commutator ↥(TauCeti.QuadraticMap.orthogonalGroup R) :=
    hsup ▸ le_sup_left
  have hRle : (determinantRightFactor K).map
      e.symm.toMonoidHom ≤ commutator ↥(TauCeti.QuadraticMap.orthogonalGroup R) :=
    hsup ▸ le_sup_right
  have hcL := CFSG.HardMathSupport.Dickson.Sec6.OrthBlocks.isComponentOf_map_subtype_of_normal
    (TauCeti.QuadraticMap.orthogonalGroup R) _ _ hLle hnL hqL
  have hcR := CFSG.HardMathSupport.Dickson.Sec6.OrthBlocks.isComponentOf_map_subtype_of_normal
    (TauCeti.QuadraticMap.orthogonalGroup R) _ _ hRle hnR hqR
  rw [hJ] at hcL hcR
  have hjoin : orthDerived R =
      ((determinantLeftFactor K).map
        e.symm.toMonoidHom).map (TauCeti.QuadraticMap.orthogonalGroup R).subtype ⊔
      ((determinantRightFactor K).map
        e.symm.toMonoidHom).map (TauCeti.QuadraticMap.orthogonalGroup R).subtype := by
    rw [← hJ, hsup, Subgroup.map_sup]
  have hIle : M.map (orthDerived R).subtype ≤ orthDerived R := Subgroup.map_subtype_le M
  have hsubM : (M.map (orthDerived R).subtype).subgroupOf (orthDerived R) = M :=
    Subgroup.comap_map_eq_self_of_injective (orthDerived R).subtype_injective M
  have hIc : CFSG.Open.IsComponentOf (M.map (orthDerived R).subtype) (orthDerived R) :=
    CFSG.Assembly.isComponentOf_iff_open.1
      ((isComponentOf_iff_isComponent_subgroupOf hIle).2 (by rw [hsubM]; exact hM))
  have hF : ∀ F : Subgroup (DeterminantIsometries K),
      (F = determinantLeftFactor K ∨
        F = determinantRightFactor K) →
      (M.map (orthDerived R).subtype =
        (F.map e.symm.toMonoidHom).map
          (TauCeti.QuadraticMap.orthogonalGroup R).subtype) →
      Nonempty (↥M ≃* Matrix.SpecialLinearGroup (Fin 2) K) := by
    intro F hFF hFM
    obtain ⟨eSL⟩ := CFSG.HardMathSupport.Dickson.Sec6.OrthBlocks.nonempty_mulEquiv_determinantFactor
      F hFF
    exact ⟨((M.equivMapOfInjective (orthDerived R).subtype
        (orthDerived R).subtype_injective).trans
      (MulEquiv.subgroupCongr hFM)).trans
      (((F.map e.symm.toMonoidHom).equivMapOfInjective
        (TauCeti.QuadraticMap.orthogonalGroup R).subtype
        (TauCeti.QuadraticMap.orthogonalGroup R).subtype_injective).symm.trans
        ((F.equivMapOfInjective e.symm.toMonoidHom e.symm.injective).symm.trans eSL.symm))⟩
  haveI : Finite W := Module.finite_of_finite K
  haveI : Finite (W ≃ₗ[K] W) := Finite.of_injective (fun e : W ≃ₗ[K] W => (e : W → W))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  obtain ⟨e1⟩ : Nonempty (↥M ≃* Matrix.SpecialLinearGroup (Fin 2) K) := by
    rcases CFSG.HardMathSupport.Dickson.Sec6.OrthBlocks.eq_or_eq_of_component_join
      hcL hcR hjoin hIc with h | h
    · exact hF _ (Or.inl rfl) h
    · exact hF _ (Or.inr rfl) h
  have hcenterM : Subgroup.center ↥M = ⊥ := by
    have hcen := Subgroup.map_center_eq e1
    rw [CFSG.Timmesfeld.RankOne.center_SL2_eq_bot] at hcen
    exact (Subgroup.map_eq_bot_iff_of_injective (Subgroup.center ↥M) e1.injective).mp hcen
  have hcardMZ : Nat.card (↥M ⧸ Subgroup.center ↥M) = Nat.card ↥M := by
    rw [hcenterM]
    exact Nat.card_congr QuotientGroup.quotientBot.toEquiv
  have hN : Nat.card (↥M ⧸ Subgroup.center ↥M) = CFSG.Open.ordD 4 2 :=
    card_centralQuotient_of_isD42 hcat
  have hfacSL2 : (Nat.card ↥M).factorization 2 = f := by
    rw [Nat.card_congr e1.toEquiv]
    exact factorization_two_card_sl2 hK hf
  have hfac : (CFSG.Open.ordD 4 2).factorization 2 = f := by
    rw [← hN, hcardMZ, hfacSL2]
  rw [factorization_two_ordD_four_two] at hfac
  have hf12 : f = 12 := by omega
  subst hf12
  have hEq : CFSG.Open.ordD 4 2 = Nat.card ↥M := by rw [← hN, hcardMZ]
  have hcardSL2 : Nat.card ↥M = Nat.card K * (Nat.card K ^ 2 - 1) := by
    rw [Nat.card_congr e1.toEquiv]
    exact CFSG.GorensteinWalter.sl2_card_formula K
  rw [hcardSL2] at hEq
  rw [hK] at hEq
  have hNval : CFSG.Open.ordD 4 2 = 174182400 := by decide +kernel
  rw [hNval] at hEq
  norm_num at hEq

theorem d42_orthogonal_split_four_two
    {K : Type} [Field K] [Finite K] [CharP K 2] {W : Type} [AddCommGroup W] [Module K W]
    [FiniteDimensional K W]
    {R : QuadraticForm K W} (hR : (QuadraticMap.polarBilin R).Nondegenerate)
    (hdim : Module.finrank K W = 4)
    (hS : ∃ S : Submodule K W, Module.finrank K S = 2 ∧ ∀ x ∈ S, R x = 0)
    (hK2 : Nat.card K = 2)
    {M : Subgroup ↥(orthDerived R)} (hM : CFSG.IsComponent M)
    (hcat : IsCatalogLieIso (↥M ⧸ Subgroup.center ↥M) IsD42Index) : False := by
  classical
  obtain ⟨S, hSdim, hSQ⟩ := hS
  obtain ⟨ψ, e, -, -, -⟩ :=
    CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit.split_four_determinant_form_isometry
      R hR hdim S hSdim hSQ
  have h5 : 5 ∣ Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup R) := by
    have h5N : 5 ∣ CFSG.Open.ordD 4 2 := five_dvd_ordD_four_two
    have hN : Nat.card (↥M ⧸ Subgroup.center ↥M) = CFSG.Open.ordD 4 2 :=
      card_centralQuotient_of_isD42 hcat
    have h1 : 5 ∣ Nat.card (↥M ⧸ Subgroup.center ↥M) := hN ▸ h5N
    have hΩdvdO : Nat.card ↥(orthDerived R) ∣
        Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup R) := by
      rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (CFSG.RankThree.PartOne.KCOrthogonal.orthDerived_le_orthogonalGroup (Q := R))).toEquiv]
      exact Subgroup.card_subgroup_dvd_card ((orthDerived R).subgroupOf
        (TauCeti.QuadraticMap.orthogonalGroup R))
    exact h1.trans ((Subgroup.card_quotient_dvd_card (Subgroup.center ↥M)).trans
      ((Subgroup.card_subgroup_dvd_card M).trans hΩdvdO))
  have hOcard : Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup R) =
      Nat.card (DeterminantIsometries K) :=
    Nat.card_congr e.toEquiv
  have h5' : 5 ∣ Nat.card
      (DeterminantIsometries K) := by
    rwa [← hOcard]
  have hle : Nat.card K ≤ 3 := by omega
  rcases CFSG.LocalAnalysis.ComponentInitial.determinant_prime_dvd_card
    (K := K) hle (by norm_num : Nat.Prime 5) h5' with h | h <;> omega

theorem d42_orthogonal_layer
    {K : Type} [Field K] [Finite K] [CharP K 2] {W : Type} [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] {f : ℕ} (hK : Nat.card K = 2 ^ f)
    (R : QuadraticForm K W) (hR : (QuadraticMap.polarBilin R).Nondegenerate)
    {M : Subgroup ↥(orthDerived R)} (hM : CFSG.IsComponent M)
    (hcat : IsCatalogLieIso (↥M ⧸ Subgroup.center ↥M) IsD42Index) :
    f = 1 ∧ Module.finrank K W = 8 := by
  classical
  have hf : 1 ≤ f := one_le_fieldExponent_of_card_eq_two_pow hK
  obtain ⟨n, hdim⟩ :=
    CFSG.ComponentClassification.UnbalancedCatalog.even_finrank_of_charTwo R hR
  rcases Nat.lt_or_ge n 2 with hn2 | hn2
  · interval_cases n
    · exact (d42_orthogonal_dim_zero hM hdim).elim
    · exact (d42_orthogonal_dim_two hR hM hdim).elim
  rcases Nat.lt_or_ge n 3 with hn3 | hn3
  · have hdim4 : Module.finrank K W = 4 := by omega
    by_cases hS : ∃ S : Submodule K W, Module.finrank K S = 2 ∧ ∀ x ∈ S, R x = 0
    · by_cases hK2 : Nat.card K = 2
      · exact (d42_orthogonal_split_four_two hR hdim4 hS hK2 hM hcat).elim
      · exact (d42_orthogonal_split_four_big hK hf hR hdim4 hS hK2 hM hcat).elim
    · have hts : ∀ U : Submodule K W, Module.finrank K U = 4 / 2 → ∃ u ∈ U, R u ≠ 0 := by
        intro U hU
        by_contra h
        push Not at h
        exact hS ⟨U, by omega, fun u hu => h u hu⟩
      exact (d42_orthogonal_minus_four hK hf hR hdim4 hts hM hcat).elim
  rcases Nat.lt_or_ge n 4 with hn4 | hn4
  · have hdim6 : Module.finrank K W = 6 := by omega
    by_cases hT : ∃ U : Submodule K W, Module.finrank K U = 3 ∧ ∀ u ∈ U, R u = 0
    · exact (d42_orthogonal_split_six hK hf hR hdim6 hT hM hcat).elim
    · have hts : ∀ U : Submodule K W, Module.finrank K U = 6 / 2 → ∃ u ∈ U, R u ≠ 0 := by
        intro U hU
        by_contra h
        push Not at h
        exact hT ⟨U, by omega, fun u hu => h u hu⟩
      exact (d42_orthogonal_minus_six hK hf hR hdim6 hts hM hcat).elim
  · have hdim2n : Module.finrank K W = 2 * n := by omega
    have hT := exists_threeSingular_of_four_le hR hdim2n hn4
    exact d42_orthogonal_high hK hf hR hn4 hdim2n hT hM hcat

end CFSG.HardMathSupport.Dickson.Sec6

end
