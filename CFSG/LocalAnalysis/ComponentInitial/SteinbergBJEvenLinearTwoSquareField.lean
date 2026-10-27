module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldFull
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldFullAutomorphism
public import CFSG.CharacterTheory.Semidihedral.OddFieldLift
public import CFSG.Walter.PSL2Facts.Even
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.Timmesfeld.ARS.NaturalModule

public section

namespace CFSG.LocalAnalysis.ComponentInitial.EvenLinearTwoSquareField

open scoped MatrixGroups
open Matrix CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField
open CFSG.Timmesfeld.RankOne (upperElt lowerElt)
open CFSG.Timmesfeld.ARS.NaturalModule (coe_upperElt coe_lowerElt)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.Semidihedral.OddFieldLift (fixedSL2Inclusion fixedSL2Inclusion_injective
  fixedSL2Inclusion_range fixedEntrySL2 fixedSL2EquivRange)

section SL2

variable {F : Type*} [Field F]

theorem upperElt_one_mul_lowerElt_one_ne :
    upperElt F 1 * lowerElt F 1 ≠ lowerElt F 1 * upperElt F 1 := by
  intro h
  have h00 := congrArg (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F) 0 0) h
  simp [coe_upperElt, coe_lowerElt, Matrix.mul_apply, Fin.sum_univ_two] at h00

theorem map_upperElt {F' : Type*} [Field F'] (f : F →+* F') (t : F) :
    Matrix.SpecialLinearGroup.map f (upperElt F t) = upperElt F' (f t) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_upperElt, Matrix.SpecialLinearGroup.map_apply_coe]

theorem map_lowerElt_one {F' : Type*} [Field F'] (f : F →+* F') :
    Matrix.SpecialLinearGroup.map f (lowerElt F 1) = lowerElt F' 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_lowerElt, Matrix.SpecialLinearGroup.map_apply_coe]

theorem eq_one_of_commute_upperElt_lowerElt [CharP F 2] {M : SL(2, F)}
    (h1 : M * upperElt F 1 = upperElt F 1 * M) (h2 : M * lowerElt F 1 = lowerElt F 1 * M) :
    M = 1 := by
  have e (i j : Fin 2) (h : M * upperElt F 1 = upperElt F 1 * M) :=
    congrArg (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F) i j) h
  have e' (i j : Fin 2) (h : M * lowerElt F 1 = lowerElt F 1 * M) :=
    congrArg (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F) i j) h
  have h10 := e 0 0 h1
  have h01 := e' 0 0 h2
  have hd := e 0 1 h1
  simp [coe_upperElt, coe_lowerElt, Matrix.mul_apply, Fin.sum_univ_two] at h10 h01 hd
  have hdet := M.2
  rw [Matrix.det_fin_two] at hdet
  have hc : (M : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := h10
  have hb : (M : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := h01
  have had : (M : Matrix (Fin 2) (Fin 2) F) 0 0 = (M : Matrix (Fin 2) (Fin 2) F) 1 1 := by
    linear_combination hd
  have ha : (M : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by
    have hsq : (M : Matrix (Fin 2) (Fin 2) F) 0 0 ^ 2 = 1 := by
      rw [hc, hb, ← had] at hdet
      linear_combination hdet
    exact CharTwo.sq_injective (by simpa using hsq)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ha, hb, hc, ← had]

private theorem le_of_mul_sq_sub_one_le' {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (h : a * (a ^ 2 - 1) ≤ b * (b ^ 2 - 1)) : a ≤ b := by
  by_contra hlt
  push Not at hlt
  have hsq : b ^ 2 < a ^ 2 := Nat.pow_lt_pow_left hlt two_ne_zero
  have hb1 : 1 ≤ b ^ 2 := Nat.one_le_pow _ _ hb
  have : b * (b ^ 2 - 1) < a * (a ^ 2 - 1) :=
    Nat.mul_lt_mul_of_le_of_lt hlt.le (by omega) (by omega)
  omega

end SL2

theorem even_linear_two_fixed_SL2_subgroup_determines_square_field {n m : ℕ}
    {K F : Type*} [Field K] [Field F] (hK : Nat.card K = 2 ^ n) (hF : Nat.card F = 2 ^ m)
    {D : Type*} [Group D] (η : D ≃* SL(2, F)) (α : MulAut D) (hα : orderOf α = 2)
    (J : Subgroup D) (hJα : J ≤ fixedSubgroup α) (hJ : (J.subgroupOf (fixedSubgroup α)).Normal)
    (κ : J ≃* SL(2, K)) :
    m = 2 * n ∧ J = fixedSubgroup α ∧ α ∉ (MulAut.conj : D →* MulAut D).range ∧
      (∃ ι : K →+* F, Function.Injective ι ∧ Set.range ι = {x : F | x ^ 2 ^ n = x} ∧
        ∃ P : SL(2, F),
          (∀ (d : D) (i j : Fin 2),
            ((P * η (α d) * P⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) i j =
              ((P * η d * P⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) i j ^ 2 ^ n) ∧
          ∀ j : J, P * η j * P⁻¹ = Matrix.SpecialLinearGroup.map ι (κ j)) ∧
      (∀ β : MulAut D, (∀ j ∈ J, β j = j) ↔ β ∈ Subgroup.zpowers α) ∧
      ∀ S : Subgroup D, Nat.card S = (2 ^ n) ^ 2 → ∃ Q : Sylow 2 D, (Q : Subgroup D) = S := by
  classical
  have hFf : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; positivity)
  have hKf : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have hF2 : CharP F 2 := char_two_of_card hF
  have hK2 : CharP K 2 := char_two_of_card hK
  have hDf : Finite D := Finite.of_equiv _ η.symm.toEquiv
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · have := Finite.one_lt_card (α := F)
      rw [hF, h, pow_zero] at this
      exact absurd this (lt_irrefl 1)
    · exact h
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · have := Finite.one_lt_card (α := K)
      rw [hK, h, pow_zero] at this
      exact absurd this (lt_irrefl 1)
    · exact h
  have hmemC : ∀ d : D, d ∈ fixedSubgroup α ↔ α d = d := fun d => Iff.rfl
  set α' : MulAut SL(2, F) := MulAut.congr η α with hα'
  have hα'app : ∀ d : D, α' (η d) = η (α d) := fun d => by
    simp [hα', MulAut.congr_apply]
  have hbij := gammaToMulAut_bijective_of_card hF
  obtain ⟨a, ha⟩ := hbij.2 α'
  have hao : orderOf a = 2 := by
    rw [← orderOf_injective (gammaToMulAut F) hbij.1, ha, hα', MulEquiv.orderOf_eq, hα]
  have hJnc : ∃ x y : J, x * y ≠ y * x := by
    refine ⟨κ.symm (upperElt K 1), κ.symm (lowerElt K 1), fun h => ?_⟩
    apply upperElt_one_mul_lowerElt_one_ne (F := K)
    have := congrArg κ h
    simpa only [map_mul, MulEquiv.apply_symm_apply] using this
  have houter : a ∉ linearKernel F := by
    intro hlin
    rw [mem_linearKernel_iff] at hlin
    have haeq : a = SemidirectProduct.inl a.left := SemidirectProduct.ext rfl hlin
    have hga : gammaToMulAut F a = MulAut.conj a.left := by
      conv_lhs => rw [haeq]
      exact gammaToMulAut_inl a.left
    have hconj : ∀ g : SL(2, F), α' g = a.left * g * a.left⁻¹ := fun g => by
      rw [← ha, hga, MulAut.conj_apply]
    have ha2 : a.left * a.left = 1 := by
      have h := pow_orderOf_eq_one a
      rw [hao, haeq, pow_two, ← map_mul] at h
      exact SemidirectProduct.inl_injective (by rw [h, map_one])
    have ha1 : a.left ≠ 1 := by
      intro h1
      rw [h1, map_one] at haeq
      rw [haeq, orderOf_one] at hao
      exact absurd hao (by decide)
    have hsq : ∀ j : J, j * j = 1 := by
      intro j
      have hj : α j = j := hJα j.2
      have hcomm : a.left * η j = η j * a.left := by
        have h := hα'app j
        rw [hj, hconj] at h
        calc a.left * η j = a.left * η j * a.left⁻¹ * a.left := by group
          _ = η j * a.left := by rw [h]
      have := CFSG.Walter.sl2_mul_self_eq_one_of_commute ha1 ha2 hcomm
      apply Subtype.ext
      apply η.injective
      rw [Subgroup.coe_mul, map_mul, this, Subgroup.coe_one, map_one]
    obtain ⟨x, y, hxy⟩ := hJnc
    apply hxy
    have hx := hsq x
    have hy := hsq y
    have hxy' := hsq (x * y)
    calc x * y = (x * y)⁻¹ := (inv_eq_of_mul_eq_one_right hxy').symm
      _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
      _ = y * x := by rw [inv_eq_of_mul_eq_one_right hx, inv_eq_of_mul_eq_one_right hy]
  have hαout : α ∉ (MulAut.conj : D →* MulAut D).range := by
    rintro ⟨g, hg⟩
    apply houter
    have hcg : gammaToMulAut F (SemidirectProduct.inl (η g)) = gammaToMulAut F a := by
      rw [gammaToMulAut_inl, ha, hα', ← hg]
      exact (CFSG.ComponentClassification.OuterAutomorphisms.congr_conj η g).symm
    rw [← hbij.1 hcg, mem_linearKernel_iff, SemidirectProduct.right_inl]
  obtain ⟨s, hs1, hms, hσpow, hk₀card, x, hax, -⟩ :=
    original_outer_involution_field_conjugacy_and_centralizer hm1 hF a hao houter
  set σ : RingAut F := a.right with hσ
  obtain ⟨hσ1, hσ2, -⟩ := outer_involution_cocycle a hao houter
  set ψ₀ : D ≃* SL(2, F) := η.trans (MulAut.conj x⁻¹) with hψ₀
  have hψ₀app : ∀ d : D, ψ₀ d = x⁻¹ * η d * x := fun d => by
    rw [hψ₀, MulEquiv.trans_apply, MulAut.conj_apply, inv_inv]
  have hgam : ∀ g : SL(2, F), α' g = x * sl2FieldAction σ (x⁻¹ * g * x) * x⁻¹ := by
    intro g
    rw [← ha, hax, map_mul, map_mul, map_inv, gammaToMulAut_inl, gammaToMulAut_inr,
      MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply, MulAut.conj_symm_apply,
      MulAut.conj_apply]
  have hψα : ∀ d : D, ψ₀ (α d) = sl2FieldAction σ (ψ₀ d) := by
    intro d
    rw [hψ₀app, hψ₀app, ← hα'app, hgam]
    group
  have hfixC : ∀ d : D, d ∈ fixedSubgroup α ↔ sl2FieldAction σ (ψ₀ d) = ψ₀ d := by
    intro d
    rw [hmemC, ← hψα]
    exact ψ₀.injective.eq_iff.symm
  have hfixRange : ∀ A : SL(2, F), sl2FieldAction σ A = A ↔
      A ∈ (fixedSL2Inclusion F (Subgroup.zpowers σ)).range := by
    intro A
    rw [fixedSL2Inclusion_range]
    constructor
    · intro hA i j
      rw [← fixedField, mem_fixedField_iff]
      exact congrArg (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F) i j) hA
    · intro hA
      ext i j
      have := hA i j
      rw [← fixedField, mem_fixedField_iff] at this
      exact this
  have hmap : (fixedSubgroup α).map ψ₀.toMonoidHom = fixedEntrySL2 F (Subgroup.zpowers σ) := by
    ext A
    rw [Subgroup.mem_map_equiv, fixedEntrySL2, ← hfixRange, hfixC, MulEquiv.apply_symm_apply]
  set k₀ := FixedPoints.subfield (Subgroup.zpowers σ) F with hk₀
  have hk₀card' : Nat.card k₀ = 2 ^ s := hk₀card
  set eC : fixedSubgroup α ≃* SL(2, k₀) :=
    (ψ₀.subgroupMap (fixedSubgroup α)).trans
      ((MulEquiv.subgroupCongr hmap).trans (fixedSL2EquivRange F (Subgroup.zpowers σ)).symm)
    with heC
  have heCapp : ∀ c : fixedSubgroup α,
      fixedSL2Inclusion F (Subgroup.zpowers σ) (eC c) = ψ₀ c := by
    intro c
    have h := (fixedSL2EquivRange F (Subgroup.zpowers σ)).apply_symm_apply
      ((MulEquiv.subgroupCongr hmap) (ψ₀.subgroupMap (fixedSubgroup α) c))
    have h' := congrArg Subtype.val h
    exact h'
  have hcardC : Nat.card (fixedSubgroup α) = 2 ^ s * ((2 ^ s) ^ 2 - 1) := by
    rw [Nat.card_congr eC.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two,
      hk₀card']
  have hcardJ : Nat.card J = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
    rw [Nat.card_congr κ.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hK]
  have hJle : Nat.card J ≤ Nat.card (fixedSubgroup α) := Subgroup.card_le_of_le hJα
  have hqs : 2 ^ n ≤ 2 ^ s := by
    rw [hcardJ, hcardC] at hJle
    exact le_of_mul_sq_sub_one_le' Nat.one_le_two_pow Nat.one_le_two_pow hJle
  have hJC : J = fixedSubgroup α := by
    rcases Nat.eq_or_lt_of_le hs1 with hs | hs
    · subst hs
      have hn : n = 1 := by
        have := Nat.pow_le_pow_iff_right (by norm_num : 1 < 2) |>.mp hqs
        omega
      subst hn
      exact Subgroup.eq_of_le_of_card_ge hJα (by rw [hcardJ, hcardC])
    · have h4 : ∃ t : Finset k₀, t.card = 4 := by
        have := Fintype.ofFinite k₀
        have hle : 4 ≤ (Finset.univ : Finset k₀).card := by
          rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hk₀card']
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs
        obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq hle
        exact ⟨t, ht⟩
      obtain ⟨-, hsimple, -⟩ :=
        CFSG.LinearGroups.linear_projective_simple (K := k₀) (n := 2) le_rfl (Or.inr h4)
      have : IsSimpleGroup SL(2, k₀) :=
        (CFSG.Walter.psl2MulEquivSL2OfCharTwo (K := k₀)).symm.isSimpleGroup
      have : IsSimpleGroup (fixedSubgroup α) := eC.isSimpleGroup
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (J.subgroupOf (fixedSubgroup α)) with h | h
      · exfalso
        rw [Subgroup.subgroupOf_eq_bot] at h
        have hJbot : J = ⊥ := disjoint_iff.mp h |>.symm ▸ (inf_eq_left.mpr hJα).symm
        have := hcardJ
        rw [hJbot, Subgroup.card_bot] at this
        have h1 : 2 ≤ 2 ^ n := Nat.le_self_pow (by omega) 2
        have h2 : 3 ≤ (2 ^ n) ^ 2 - 1 := by
          have : 4 ≤ (2 ^ n) ^ 2 := by nlinarith
          omega
        nlinarith
      · rw [Subgroup.subgroupOf_eq_top] at h
        exact le_antisymm hJα h
  have hsn : s = n := by
    have hcard := congrArg (fun H : Subgroup D => Nat.card H) hJC
    rw [hcardJ, hcardC] at hcard
    have h1 := le_of_mul_sq_sub_one_le' Nat.one_le_two_pow Nat.one_le_two_pow hcard.le
    have h2 := le_of_mul_sq_sub_one_le' Nat.one_le_two_pow Nat.one_le_two_pow hcard.ge
    exact (Nat.pow_right_injective le_rfl (le_antisymm h2 h1))
  have : Fintype K := Fintype.ofFinite K
  have : Fintype k₀ := Fintype.ofFinite k₀
  have hKk : Fintype.card K = Fintype.card k₀ := by
    rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, hK, hk₀card', hsn]
  set ι₀ : K ≃+* k₀ := FiniteField.ringEquivOfCardEq hKk with hι₀
  set eJ : J ≃* SL(2, k₀) := (MulEquiv.subgroupCongr hJC).trans eC with heJ
  have heJapp : ∀ j : J, fixedSL2Inclusion F (Subgroup.zpowers σ) (eJ j) = ψ₀ j :=
    fun j => heCapp _
  set I₀ : SL(2, K) ≃* SL(2, k₀) := sl2RingEquiv ι₀ with hI₀
  set β : MulAut SL(2, K) := (κ.symm.trans eJ).trans I₀.symm with hβ
  obtain ⟨b, hb⟩ := (gammaToMulAut_bijective_of_card hK).2 β
  set M' : SL(2, F) := fixedSL2Inclusion F (Subgroup.zpowers σ) (I₀ b.left) with hM'
  set ι : K →+* F := k₀.subtype.comp (ι₀.toRingHom.comp b.right.toRingHom) with hι
  have hincl : ∀ A : SL(2, K), fixedSL2Inclusion F (Subgroup.zpowers σ)
      (I₀ (Matrix.SpecialLinearGroup.map b.right.toRingHom A)) =
        Matrix.SpecialLinearGroup.map ι A := by
    intro A
    ext i j
    rfl
  have hψJ : ∀ j : J, ψ₀ j = M' * Matrix.SpecialLinearGroup.map ι (κ j) * M'⁻¹ := by
    intro j
    rw [← heJapp]
    have h1 : eJ j = I₀ (β (κ j)) := by
      simp only [hβ, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
        MulEquiv.apply_symm_apply]
    rw [h1, ← hb, gammaToMulAut_apply, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv,
      hincl]
  have hM'fix : sl2FieldAction σ M' = M' := (hfixRange M').mpr ⟨_, rfl⟩
  have hP : ∀ e : D, (M'⁻¹ * x⁻¹) * η e * (M'⁻¹ * x⁻¹)⁻¹ = M'⁻¹ * ψ₀ e * M' := fun e => by
    rw [hψ₀app]
    group
  refine ⟨by rw [hms, hsn], hJC, hαout, ⟨ι, ι.injective, ?_, M'⁻¹ * x⁻¹, ?_, ?_⟩, ?_, ?_⟩
  ·
    ext y
    constructor
    · rintro ⟨t, rfl⟩
      have hmem : ι t ∈ k₀ := (ι₀ (b.right t)).2
      rw [Set.mem_ofPred_eq, ← hsn, ← hσpow]
      exact (mem_fixedField_iff σ _).mp hmem
    · intro hy
      have hyk : y ∈ k₀ := (mem_fixedField_iff σ y).mpr (by
        rw [hσpow, hsn]
        exact hy)
      refine ⟨b.right.symm (ι₀.symm ⟨y, hyk⟩), ?_⟩
      simp [hι]
  ·
    intro d i j
    rw [hP, hP, hψα]
    have h : M'⁻¹ * sl2FieldAction σ (ψ₀ d) * M' = sl2FieldAction σ (M'⁻¹ * ψ₀ d * M') := by
      rw [map_mul, map_mul, map_inv, hM'fix]
    rw [h, sl2FieldAction_apply, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply, ← hsn]
    exact hσpow _
  ·
    intro j
    rw [hP, hψJ]
    group
  ·
    intro β'
    constructor
    · intro hβ'
      have hβC : ∀ d ∈ fixedSubgroup α, β' d = d := fun d hd => hβ' d (hJC ▸ hd)
      set γ : MulAut SL(2, F) := MulAut.congr ψ₀ β' with hγdef
      have hγ : ∀ A, sl2FieldAction σ A = A → γ A = A := by
        intro A hA
        have hd : ψ₀.symm A ∈ fixedSubgroup α := by
          rw [hfixC, MulEquiv.apply_symm_apply]
          exact hA
        simp only [hγdef, MulAut.congr_apply, MulEquiv.trans_apply]
        rw [hβC _ hd, MulEquiv.apply_symm_apply]
      obtain ⟨c, hc⟩ := hbij.2 γ
      have hcapp : ∀ A, sl2FieldAction σ A = A →
          c.left * Matrix.SpecialLinearGroup.map c.right.toRingHom A * c.left⁻¹ = A := by
        intro A hA
        rw [← gammaToMulAut_apply, hc]
        exact hγ A hA
      have hu1 : sl2FieldAction σ (upperElt F 1) = upperElt F 1 := by
        rw [sl2FieldAction_apply, map_upperElt, map_one]
      have hl1 : sl2FieldAction σ (lowerElt F 1) = lowerElt F 1 := by
        rw [sl2FieldAction_apply, map_lowerElt_one]
      have hcu := hcapp _ hu1
      rw [map_upperElt, map_one] at hcu
      have hcl := hcapp _ hl1
      rw [map_lowerElt_one] at hcl
      have hM1 : c.left = 1 := by
        refine eq_one_of_commute_upperElt_lowerElt ?_ ?_
        · calc c.left * upperElt F 1 = c.left * upperElt F 1 * c.left⁻¹ * c.left := by group
            _ = upperElt F 1 * c.left := by rw [hcu]
        · calc c.left * lowerElt F 1 = c.left * lowerElt F 1 * c.left⁻¹ * c.left := by group
            _ = lowerElt F 1 * c.left := by rw [hcl]
      have hτ : ∀ t : F, σ t = t → c.right t = t := by
        intro t ht
        have hut : sl2FieldAction σ (upperElt F t) = upperElt F t := by
          rw [sl2FieldAction_apply, map_upperElt]
          exact congrArg (upperElt F) ht
        have h := hcapp _ hut
        rw [hM1, one_mul, inv_one, mul_one, map_upperElt] at h
        exact CFSG.Timmesfeld.RankOne.upperElt_injective F h
      have hτσ : c.right = 1 ∨ c.right = σ := by
        have hle : (k₀ : Set F) ⊆ (fixedField c.right : Set F) := by
          intro t ht
          rw [SetLike.mem_coe, mem_fixedField_iff]
          exact hτ t ((mem_fixedField_iff σ t).mp ht)
        have hcardle : 2 ^ n ≤ Nat.card (fixedField c.right) := by
          rw [← hsn, ← hk₀card', ← SetLike.coe_sort_coe,
            ← SetLike.coe_sort_coe (fixedField c.right), Nat.card_coe_set_eq, Nat.card_coe_set_eq]
          exact Set.ncard_le_ncard hle (Set.toFinite _)
        have hpow := fixedField_card_pow_order c.right
        rw [hF, hms, hsn] at hpow
        have hpos : 0 < orderOf c.right := orderOf_pos c.right
        have hord : orderOf c.right ≤ 2 := by
          by_contra hgt
          push Not at hgt
          have h3 : (2 ^ n) ^ 3 ≤ Nat.card (fixedField c.right) ^ orderOf c.right :=
            calc (2 ^ n) ^ 3 ≤ (2 ^ n) ^ orderOf c.right :=
                  Nat.pow_le_pow_right (by positivity) hgt
              _ ≤ _ := Nat.pow_le_pow_left hcardle _
          rw [← hpow, ← pow_mul] at h3
          have h4 : 2 ^ (2 * n) < 2 ^ (n * 3) := Nat.pow_lt_pow_right (by norm_num) (by omega)
          omega
        rcases (by omega : orderOf c.right = 1 ∨ orderOf c.right = 2) with h | h
        · exact Or.inl (orderOf_eq_one_iff.mp h)
        · have : IsCyclic (RingAut F) := finite_field_ringAut_isCyclic 2
          exact Or.inr (cyclic_involutions_eq _ _ h (orderOf_eq_prime hσ2 hσ1))
      have hc' : c = SemidirectProduct.inr c.right := SemidirectProduct.ext hM1 rfl
      rcases hτσ with h | h
      · have hγ1 : γ = 1 := by rw [← hc, hc', h, map_one, map_one]
        have hβ1 : β' = 1 := (MulAut.congr ψ₀).injective (by rw [← hγdef, hγ1, map_one])
        rw [hβ1]
        exact one_mem _
      · have hγσ : γ = sl2FieldAction σ := by rw [← hc, hc', h, gammaToMulAut_inr]
        have hασ : MulAut.congr ψ₀ α = sl2FieldAction σ := by
          refine MulEquiv.ext fun A => ?_
          simp only [MulAut.congr_apply, MulEquiv.trans_apply]
          rw [hψα, MulEquiv.apply_symm_apply]
        have hβα : β' = α := (MulAut.congr ψ₀).injective (by rw [← hγdef, hγσ, hασ])
        rw [hβα]
        exact Subgroup.mem_zpowers α
    · intro hβ' j hj
      have hstab : Subgroup.zpowers α ≤ MulAction.stabilizer (MulAut D) j := by
        rw [Subgroup.zpowers_le]
        exact hJα hj
      exact hstab hβ'
  ·
    intro S hS
    have hcardD : Nat.card D = 2 ^ m * ((2 ^ m) ^ 2 - 1) := by
      rw [Nat.card_congr η.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hF]
    have hS' : Nat.card S = 2 ^ m := by rw [hS, ← pow_mul, hms, hsn, mul_comm]
    have hp : IsPGroup 2 S := IsPGroup.of_card hS'
    have hidx : ¬ 2 ∣ S.index := by
      have hmul := S.card_mul_index
      rw [hcardD, hS'] at hmul
      rw [Nat.eq_of_mul_eq_mul_left (by positivity) hmul]
      have hd : 2 ∣ (2 ^ m) ^ 2 := dvd_pow (dvd_pow_self 2 (by omega)) two_ne_zero
      have hpos : 1 ≤ (2 ^ m) ^ 2 := Nat.one_le_iff_ne_zero.mpr (by positivity)
      generalize (2 ^ m) ^ 2 = Q at hd hpos ⊢
      omega
    exact ⟨hp.toSylow hidx, rfl⟩

end CFSG.LocalAnalysis.ComponentInitial.EvenLinearTwoSquareField
