module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2020Common
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019LinOuter
public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.OuterFixedPSLDescent
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherConjAutInner
public import CFSG.LocalAnalysis.ComponentInitial.QTNQRLinearUnitaryOuterDerivedLinear
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherLinearAutNormal
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019Outer
public import CFSG.RankThree.PartOne.KC.LinearSubfieldPointwise
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.LocalAnalysis.SeitzReduction.RankOneHallTwoArithLieOddFactor
public import CFSG.NumberTheory.OddPowAddSubOne
public import CFSG.GroupTheory.CyclicSubgroup.PowerCriterion
public import CFSG.Algebra.FiniteFieldFrobeniusPower
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherConjAutFieldAutCommutator
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma52

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2020

open CFSG.Open Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.RankThree.PartOne
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open scoped commutatorElement

private theorem ordProj_card_projectiveSL_eq_of_card_eq_pow {F₀ F : Type} [Field F₀] [Finite F₀]
    [Field F] [Finite F] {n p : ℕ} (hn : n = 3 ∨ n = 4) (hp : p.Prime) (hp2 : p ≠ 2)
    (hN0odd : Odd (Nat.card F₀)) (hcard : Nat.card F = Nat.card F₀ ^ p) :
    ordProj[2] (Nat.card (projectiveSL n F)) =
      ordProj[2] (Nat.card (projectiveSL n F₀)) := by
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  set N := Nat.card F with hNdef
  set N0 := Nat.card F₀ with hN0def
  have hNodd : Odd N := by rw [hcard]; exact hN0odd.pow
  have hN0pos : 1 ≤ N0 := by obtain ⟨m, hm⟩ := hN0odd; omega
  have hd2 : ordProj[2] (Nat.gcd n (N - 1)) = ordProj[2] (Nat.gcd n (N0 - 1)) := by
    rcases hn with rfl | rfl
    ·
      have h1 : ¬ 2 ∣ Nat.gcd 3 (N - 1) := by
        intro h2
        have := h2.trans (Nat.gcd_dvd_left 3 (N - 1))
        omega
      have h2 : ¬ 2 ∣ Nat.gcd 3 (N0 - 1) := by
        intro h
        have := h.trans (Nat.gcd_dvd_left 3 (N0 - 1))
        omega
      rw [Nat.factorization_eq_zero_of_not_dvd h1,
        Nat.factorization_eq_zero_of_not_dvd h2]
    ·
      have h4mod : N ≡ N0 [MOD 4] := by
        rw [hcard]
        obtain ⟨k, rfl⟩ := hpodd
        have h8 : 4 ∣ N0 ^ 2 - 1 :=
          (by norm_num : 4 ∣ 8).trans (Nat.eight_dvd_sq_sub_one_of_odd hN0odd)
        have hsq : N0 ^ 2 ≡ 1 [MOD 4] :=
          (Nat.modEq_iff_dvd' (Nat.one_le_pow 2 N0 hN0pos)).mpr h8 |>.symm
        rw [pow_succ, pow_mul]
        simpa using (hsq.pow k).mul (Nat.ModEq.refl N0)
      have hN0N : N0 ≤ N := by
        have h : N = (Nat.card F₀) ^ p := hcard
        have hN0pos' : 0 < Nat.card F₀ := by
          rw [show N0 = Nat.card F₀ from hN0def] at hN0pos
          omega
        rw [show N0 = Nat.card F₀ from hN0def] at *
        rw [h]
        have hp1 : 2 ≤ p := hp.two_le
        obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
        rw [pow_succ]
        exact Nat.le_mul_of_pos_left _ (pow_pos hN0pos' k)
      have h4N : 4 ∣ N - N0 := (Nat.modEq_iff_dvd' hN0N).mp h4mod.symm
      have hdiv4 : 4 ∣ N - 1 ↔ 4 ∣ N0 - 1 := by
        constructor
        · intro h
          obtain ⟨a, ha⟩ := h
          obtain ⟨b, hb⟩ := h4N
          exact ⟨a - b, by omega⟩
        · intro h
          obtain ⟨a, ha⟩ := h
          obtain ⟨b, hb⟩ := h4N
          exact ⟨a + b, by omega⟩
      have hgn : Nat.gcd 4 (N - 1) = if 4 ∣ N - 1 then 4 else 2 := by
        have hle : Nat.gcd 4 (N - 1) ≤ 4 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)
        have heven : 2 ∣ Nat.gcd 4 (N - 1) := by
          refine Nat.dvd_gcd (by norm_num) ?_
          obtain ⟨m, hm⟩ := hNodd
          exact ⟨m, by omega⟩
        split_ifs with h
        · exact Nat.gcd_eq_left_iff_dvd.mpr h
        · set g := Nat.gcd 4 (N - 1) with hg
          have hgle : g ≤ 4 := hle
          have hg2 : 2 ∣ g := heven
          have hg0 : 0 < g := Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_left _ _) (by norm_num)
          have hgne : g ≠ 4 := fun hg4 => h (Nat.gcd_eq_left_iff_dvd.mp hg4)
          interval_cases g <;> omega
      have hgn0 : Nat.gcd 4 (N0 - 1) = if 4 ∣ N0 - 1 then 4 else 2 := by
        have hle : Nat.gcd 4 (N0 - 1) ≤ 4 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)
        have heven : 2 ∣ Nat.gcd 4 (N0 - 1) := by
          refine Nat.dvd_gcd (by norm_num) ?_
          obtain ⟨m, hm⟩ := hN0odd
          exact ⟨m, by omega⟩
        split_ifs with h
        · exact Nat.gcd_eq_left_iff_dvd.mpr h
        · set g := Nat.gcd 4 (N0 - 1) with hg
          have hgle : g ≤ 4 := hle
          have hg2 : 2 ∣ g := heven
          have hg0 : 0 < g := Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_left _ _) (by norm_num)
          have hgne : g ≠ 4 := fun hg4 => h (Nat.gcd_eq_left_iff_dvd.mp hg4)
          interval_cases g <;> omega
      rw [hgn, hgn0]
      by_cases h : 4 ∣ N - 1
      · rw [if_pos h, if_pos (hdiv4.mp h)]
      · rw [if_neg h, if_neg (fun h0 => h (hdiv4.mpr h0))]
  have hprod : ∀ (K : Type) [Field K] [Finite K], Odd (Nat.card K) →
      ordProj[2] (Nat.card (SpecialLinearGroup (Fin n) K)) =
        ∏ j ∈ Finset.Icc 2 n, ordProj[2] (Nat.card K ^ j - 1) := by
    intro K _ _ hKodd
    have hn1 : 1 ≤ n := by rcases hn with rfl | rfl <;> norm_num
    rw [card_SL_eq hn1]
    rw [Nat.ordProj_mul 2 (pow_ne_zero _ (Finite.card_pos (α := K)).ne')
      (Finset.prod_ne_zero_iff.mpr (fun j hj => by
        have h2 : 2 ≤ j := (Finset.mem_Icc.mp hj).1
        have : 1 < Nat.card K := Finite.one_lt_card
        exact Nat.sub_ne_zero_of_lt (Nat.one_lt_pow (by omega) this)))]
    have hodd : ordProj[2] (Nat.card K ^ (n * (n - 1) / 2)) = 1 :=
      ordProj_two_eq_one_of_odd hKodd.pow
    rw [hodd, one_mul, ordProj_two_prod]
    exact fun j hj => Nat.sub_ne_zero_of_lt (Nat.one_lt_pow (by
      have h2 : 2 ≤ j := (Finset.mem_Icc.mp hj).1; omega) Finite.one_lt_card)
  have hSL : ordProj[2] (Nat.card (SpecialLinearGroup (Fin n) F)) =
      ordProj[2] (Nat.card (SpecialLinearGroup (Fin n) F₀)) := by
    rw [hprod F hNodd, hprod F₀ hN0odd]
    refine Finset.prod_congr rfl ?_
    intro j hj
    have h2 : 2 ≤ j := (Finset.mem_Icc.mp hj).1
    have hge : 3 ≤ N0 ^ j := by
      have h3 : 3 ≤ N0 := by
        have := Finite.one_lt_card (α := F₀)
        obtain ⟨m, hm⟩ := hN0odd
        omega
      calc 3 ≤ N0 := h3
        _ = N0 ^ 1 := (pow_one _).symm
        _ ≤ N0 ^ j := Nat.pow_le_pow_right (by omega) (by omega)
    rw [show Nat.card F = N0 ^ p from hcard]
    rw [show (N0 ^ p) ^ j = (N0 ^ j) ^ p by rw [← pow_mul, ← pow_mul, mul_comm]]
    exact CFSG.SeitzReduction.RankOne.LieOdd.ordProj_pow_odd_sub_one hge (hN0odd.pow) hpodd
  have hX : Nat.card (SpecialLinearGroup (Fin n) F) =
      Nat.card (projectiveSL n F) * Nat.card (scalars n F) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (scalars n F)
  have hX0 : Nat.card (SpecialLinearGroup (Fin n) F₀) =
      Nat.card (projectiveSL n F₀) * Nat.card (scalars n F₀) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (scalars n F₀)
  have hsc : Nat.card (scalars n F) = Nat.gcd n (N - 1) :=
    card_scalars_eq_gcd F (by omega)
  have hsc0 : Nat.card (scalars n F₀) = Nat.gcd n (N0 - 1) :=
    card_scalars_eq_gcd F₀ (by omega)
  have hPne : Nat.card (projectiveSL n F) ≠ 0 := (Nat.card_pos).ne'
  have hP0ne : Nat.card (projectiveSL n F₀) ≠ 0 := (Nat.card_pos).ne'
  have hSne : Nat.card (scalars n F) ≠ 0 := (Nat.card_pos).ne'
  have hS0ne : Nat.card (scalars n F₀) ≠ 0 := (Nat.card_pos).ne'
  have hmain : ordProj[2] (Nat.card (projectiveSL n F)) *
      ordProj[2] (Nat.card (scalars n F)) =
      ordProj[2] (Nat.card (projectiveSL n F₀)) *
        ordProj[2] (Nat.card (scalars n F₀)) := by
    rw [← Nat.ordProj_mul 2 hPne hSne, ← hX,
      ← Nat.ordProj_mul 2 hP0ne hS0ne, ← hX0, hSL]
  have hSF : ordProj[2] (Nat.card (scalars n F)) =
      ordProj[2] (Nat.card (scalars n F₀)) := by
    rw [hsc, hsc0]; exact hd2
  rw [hSF] at hmain
  exact Nat.mul_right_cancel (pow_pos (by norm_num) _) hmain

theorem i2020LinOuter : I2020LinOuter := by
  intro p q hp hp2 hq hq2 hqp F _ _ _ n hn hn4 β hβp hβ
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := Fintype.ofFinite F
  haveI : Finite (SpecialLinearGroup (Fin n) F) :=
    Finite.of_injective (fun g : SpecialLinearGroup (Fin n) F =>
      (g : Matrix (Fin n) (Fin n) F)) Subtype.val_injective
  haveI : Finite (projectiveSL n F) := Finite.of_surjective (proj n F) (proj_surjective n F)
  obtain ⟨f, -, hcard⟩ := FiniteField.card F q
  have hcard' : Nat.card F = q ^ (f : ℕ) := by
    rw [Nat.card_eq_fintype_card, hcard]
  have hf : 1 ≤ (f : ℕ) := f.pos
  have hβE : β ∈ semilinearAutGroup n F :=
    mem_semilinearAutGroup_of_pow_odd hn (hp.odd_of_ne_two hp2) hβp
  have hβD : β ∉ linearAutGroup n F := by
    rw [linearAutGroup, ← MonoidHom.coe_range, Subgroup.closure_eq]
    rintro ⟨A, hA⟩
    exact hβ A hA.symm
  have hβ1 : β ≠ 1 := fun h1 => hβ 1 (by rw [h1, map_one])
  obtain ⟨hpf, σ, hσord, ⟨γ, hγD, hγ⟩, hF₀card⟩ :=
    CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.higher_linear_prime_semilinear_field_descent'
      hq hf hn hcard' hp β hβE hβD (orderOf_eq_prime hβp hβ1)
  obtain ⟨j, hQ3, hQodd, hσform⟩ :=
    CFSG.FiniteField.exists_pow_apply_eq_of_orderOf_eq_prime hq hq2 hf hcard' hp hp2 hpf σ hσord
  set Q := q ^ ((f : ℕ) / p) with hQdef
  have hF₀card' : Nat.card (semilinearFixedSubfield σ) = Q := by
    rw [hF₀card, hQdef]
  have hFpow : Nat.card F = Nat.card (semilinearFixedSubfield σ) ^ p := by
    rw [hF₀card', hcard']
    have hfd : (f : ℕ) = p * ((f : ℕ) / p) := by
      rw [mul_comm]
      exact (Nat.div_mul_cancel hpf).symm
    conv_lhs => rw [hfd]
    rw [mul_comm p, pow_mul]
  let J₀ := (linearSubfieldInclusion n (semilinearFixedSubfield σ)).range
  have hJ₀fix : J₀ ≤ fixSubgroup (fieldAut n F σ) := by
    rintro _ ⟨x, rfl⟩
    exact fieldAut_linearSubfieldInclusion
      (fun c hc => RingHom.mem_eqLocusField.mp hc) x
  let J₁ := J₀.map γ.toMonoidHom
  have hJ₁C : J₁ ≤ fixSubgroup β := by
    rw [hγ, CFSG.LocalAnalysis.GLTheoremA.S2019.fixSubgroup_conj]
    exact Subgroup.map_mono hJ₀fix
  have hcomm₁ : ⁅fixSubgroup β, fixSubgroup β⁆ ≤ J₁ := by
    rw [hγ, CFSG.LocalAnalysis.GLTheoremA.S2019.fixSubgroup_conj,
      ← Subgroup.map_commutator]
    exact Subgroup.map_mono
      (CFSG.LocalAnalysis.GLTheoremA.S2019.commutator_fixSubgroup_fieldAut_le σ)
  have hJ₀s : IsSimpleGroup ↥J₀ :=
    (CFSG.RankThree.PartOne.simple_nonabelian_range_linearSubfieldInclusion
      hn (semilinearFixedSubfield σ)).1
  have hJ₁s : IsSimpleGroup ↥J₁ := by
    change IsSimpleGroup ↥(J₀.map γ.toMonoidHom)
    exact (J₀.equivMapOfInjective γ.toMonoidHom γ.injective).symm.isSimpleGroup
  have hZ : Subgroup.center (projectiveSL n F) = ⊥ :=
    CFSG.RankThree.RegularUnipotent.center_projectiveSL_eq_bot hn
  haveI : (linearAutGroup n F).Normal := linearAutGroup_normal_of_three_le hn
  haveI : ((MulAut.conj : projectiveSL n F →* MulAut (projectiveSL n F)).range).Normal :=
    CFSG.Fischer.innerAut_normal
  have hdvd : (Nat.card Fˣ).gcd n ∣ Q ^ j - 1 := by
    have hdvdQ : (Nat.card Fˣ).gcd n ∣ Q - 1 := by
      refine CFSG.NumberTheory.dvd_sub_one_of_dvd_odd_pow_sub_one ?_ (hp.odd_of_ne_two hp2) hQodd ?_
      · rcases (show n = 3 ∨ n = 4 by omega) with rfl | rfl
        · exact Or.inl (Nat.gcd_dvd_right _ _)
        · exact Or.inr (Nat.gcd_dvd_right _ _)
      · rw [Nat.card_units, hFpow, hF₀card']
        exact Nat.gcd_dvd_left _ _
    exact hdvdQ.trans (Nat.sub_one_dvd_pow_sub_one Q j)
  have hDβ : ∀ d ∈ linearAutGroup n F, ⁅d, β⁆ ∈
      (MulAut.conj : projectiveSL n F →* MulAut (projectiveSL n F)).range := by
    intro d hd
    obtain ⟨A, rfl⟩ := mem_linearAutGroup_iff.mp hd
    have hmem : γ⁻¹ * conjAut n F A * γ ∈ linearAutGroup n F :=
      (inferInstance : (linearAutGroup n F).Normal).conj_mem' _ hd γ
    obtain ⟨A', hA'⟩ := mem_linearAutGroup_iff.mp hmem
    have hconj :=
      conjugate_commutatorElement (γ⁻¹ * conjAut n F A * γ) (fieldAut n F σ) γ
    rw [show γ * (γ⁻¹ * conjAut n F A * γ) * γ⁻¹ = conjAut n F A by group,
      show γ * fieldAut n F σ * γ⁻¹ = γ * fieldAut n F σ * γ⁻¹ by rfl] at hconj
    rw [hγ, ← hconj, ← hA',
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.commutator_conjAut_fieldAut]
    have hdet : GeneralLinearGroup.det (A' * GeneralLinearGroup.map (σ : F →+* F) A'⁻¹) =
        GeneralLinearGroup.det A' *
          (Units.map σ.toRingHom.toMonoidHom (GeneralLinearGroup.det A'))⁻¹ := by
      calc GeneralLinearGroup.det (A' * GeneralLinearGroup.map (σ : F →+* F) A'⁻¹)
          = GeneralLinearGroup.det A' *
              GeneralLinearGroup.det (GeneralLinearGroup.map (σ : F →+* F) A'⁻¹) :=
              map_mul _ _ _
        _ = GeneralLinearGroup.det A' *
              GeneralLinearGroup.det ((GeneralLinearGroup.map (σ : F →+* F) A')⁻¹) := by
              rw [show GeneralLinearGroup.map (σ : F →+* F) A'⁻¹ =
                (GeneralLinearGroup.map (σ : F →+* F) A')⁻¹ from map_inv _ _]
        _ = GeneralLinearGroup.det A' *
              (GeneralLinearGroup.det (GeneralLinearGroup.map (σ : F →+* F) A'))⁻¹ := by
              rw [show GeneralLinearGroup.det ((GeneralLinearGroup.map (σ : F →+* F) A')⁻¹) =
                (GeneralLinearGroup.det (GeneralLinearGroup.map (σ : F →+* F) A'))⁻¹
                from map_inv _ _]
        _ = _ := by
              rw [Matrix.GeneralLinearGroup.map_det]
              rfl
    obtain ⟨μ, hμ⟩ := CFSG.GroupTheory.CyclicSubgroup.exists_pow_eq_mul_inv_of_pow_form
      (Units.map σ.toRingHom.toMonoidHom) (fun x => by
        apply Units.ext
        rw [Units.coe_map, Units.val_pow_eq_pow_val]
        exact hσform (x : F)) (by omega) hdvd (GeneralLinearGroup.det A')
    have hinner : conjAut n F (A' * GeneralLinearGroup.map (σ : F →+* F) A'⁻¹) ∈
        (MulAut.conj : projectiveSL n F →* MulAut (projectiveSL n F)).range := by
      refine conjAut_mem_range_conj_of_det_eq_pow (μ := μ) ?_
      rw [hdet, ← hμ]
    exact
      (inferInstance :
        ((MulAut.conj : projectiveSL n F →* MulAut (projectiveSL n F)).range).Normal)
        |>.conj_mem _ hinner γ
  intro J hJ _
  have hJperf : ⁅J, J⁆ = J := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hJ
  have hJle : J ≤ J₁ := by
    rw [← hJperf]
    exact (Subgroup.commutator_mono hJ.1 hJ.1).trans hcomm₁
  have hsn : IsSubnormal J J₁ := by
    have h1 := hJ.2.1.inf_of_le hJ₁C
    rwa [inf_eq_left.2 hJle] at h1
  have hJne : J ≠ ⊥ := CFSG.HardMathSupport.Solomon.LocalBalance.glaPComponent_ne_bot hJ
  have hJeq : J = J₁ := (hsn.eq_bot_or_eq_of_isSimpleGroup hJ₁s).resolve_left hJne
  rw [hJeq]
  have hJ₁card : Nat.card J₁ = Nat.card J₀ := Subgroup.card_map_of_injective γ.injective
  have hJ₀card : Nat.card J₀ = Nat.card (projectiveSL n (semilinearFixedSubfield σ)) :=
    (Nat.card_congr (MonoidHom.ofInjective
      (linearSubfieldInclusion_injective (by omega) _)).toEquiv).symm
  have hF0odd : Odd (Nat.card (semilinearFixedSubfield σ)) := by
    rw [hF₀card']; exact hQodd
  have hord : ordProj[2] (Nat.card J₁) = ordProj[2] (Nat.card (projectiveSL n F)) := by
    rw [hJ₁card, hJ₀card]
    exact (ordProj_card_projectiveSL_eq_of_card_eq_pow
      (F₀ := ↥(semilinearFixedSubfield σ)) (F := F) (n := n) (p := p)
      (by omega : n = 3 ∨ n = 4) hp hp2 hF0odd hFpow).symm
  have hsyl : (Nat.card J₁).factorization 2 =
      (Nat.card (projectiveSL n F)).factorization 2 :=
    Nat.pow_right_injective (by norm_num : 2 ≤ 2) hord
  exact i2020FixCentAt_of_sylow hZ (linearAutGroup n F)
    (fun α => CFSG.LocalAnalysis.ComponentInitial.OuterDerived.commutator_mem_linearAutGroup
      (K := F) (n := n) hn α β)
    hDβ hJ₁C hsyl

end CFSG.LocalAnalysis.GLTheoremA.I2020

end
