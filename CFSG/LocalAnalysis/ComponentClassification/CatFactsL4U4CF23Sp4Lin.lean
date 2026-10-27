module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4CF23Wit
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4TCClass
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4LayerC
public import CFSG.GroupTheory.OrderBelowSixtySolvable

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB.CF23I

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag Subgroup
open CFSG.ComponentClassification.CatFactsSp4
open CFSG.ComponentClassification.OddClassSelector (NoTightWitness)

variable {K : Type} [Field K]

theorem even_card_center_SL2 [Finite K] (h2 : (2 : K) ≠ 0) :
    Even (Nat.card (center (Matrix.SpecialLinearGroup (Fin 2) K))) := by
  have hm : (-1 : Matrix.SpecialLinearGroup (Fin 2) K) ∈
      center (Matrix.SpecialLinearGroup (Fin 2) K) := by
    rw [mem_center_iff]
    intro g
    rw [mul_neg_one, neg_one_mul]
  have hne : (-1 : Matrix.SpecialLinearGroup (Fin 2) K) ≠ 1 := by
    intro h
    have h1 := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) K =>
      (g : Matrix (Fin 2) (Fin 2) K) 0 0) h
    simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
      Matrix.neg_apply, Matrix.one_apply_eq] at h1
    apply h2
    linear_combination -h1
  have ho : orderOf (-1 : Matrix.SpecialLinearGroup (Fin 2) K) = 2 :=
    orderOf_eq_prime (by rw [neg_one_sq]) hne
  have hle : zpowers (-1 : Matrix.SpecialLinearGroup (Fin 2) K) ≤
      center (Matrix.SpecialLinearGroup (Fin 2) K) := zpowers_le.mpr hm
  have hd := Subgroup.card_dvd_of_le hle
  rw [Nat.card_zpowers, ho] at hd
  exact even_iff_two_dvd.mpr hd

theorem sp4_linear {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) [Finite K]
    (hK : Nat.card K = p ^ f) (hZ : center (StatedProj (StatedSp 2 K)) = ⊥)
    {α : MulAut (StatedProj (StatedSp 2 K))} (hα2 : α * α = 1) (hα1 : α ≠ 1) (A : gsp 2 K)
    (hα : α = conjAut 2 K A * fieldAut 2 K 1)
    (hd : ∃ d : Kˣ, (A : GL (Fin 2 ⊕ Fin 2) K) *
        CatalogueBHigherLinearField.glFieldEquiv (Fin 2 ⊕ Fin 2) (1 : K ≃+* K) A =
      GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) d)
    {X : Subgroup (StatedProj (StatedSp 2 K))} (hXq : CFSG.IsQuasisimple X) (hXα : X ≤ fixOf α)
    (hX : CFSG.IsPComponent 2 (X.subgroupOf (fixOf α))) (hnt : NoTightWitness X)
    (hZX : Odd (Nat.card (center X))) :
    IsSimpleGroup X ∧ Nat.card X * 2 = (p ^ f) ^ 2 * (((p ^ f) ^ 2) ^ 2 - 1) := by
  have hodd : Odd (Nat.card K) := odd_card_of_card_eq hp hp2 hK
  have h2 := CatFactsSp4.two_ne_zero_of_odd_card hodd
  have hXφ : ∀ x ∈ X, α x = x := fun x hx => hXα hx
  obtain ⟨d, hd⟩ := hd
  have hα' : α = conjAut 2 K A := by rw [hα, map_one, mul_one]
  set Am : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
    ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) with hAm
  have hAA : Am * Am = (d : K) • 1 := by
    have h1 := congrArg (fun M : GL (Fin 2 ⊕ Fin 2) K =>
      (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) hd
    simp only [Units.val_mul, GeneralLinearGroup.coe_scalar] at h1
    have h1' : ((CatalogueBHigherLinearField.glFieldEquiv (Fin 2 ⊕ Fin 2) (1 : K ≃+* K)
        (A : GL (Fin 2 ⊕ Fin 2) K) : GL (Fin 2 ⊕ Fin 2) K) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = Am := by
      ext i j
      rfl
    rw [h1'] at h1
    rw [h1, Matrix.smul_one_eq_diagonal]
    rfl
  set μ := multiplierUnit A with hμdef
  have hμ : Amᵀ * formJ 2 K * Am = (μ : K) • formJ 2 K := multiplierUnit_spec A
  have hdμ : (d : K) = μ ∨ (d : K) = -μ := by
    have e1 : (Am * Am)ᵀ * formJ 2 K * (Am * Am) = ((μ : K) * μ) • formJ 2 K := by
      rw [transpose_mul, show Amᵀ * Amᵀ * formJ 2 K * (Am * Am) =
        Amᵀ * (Amᵀ * formJ 2 K * Am) * Am by simp only [Matrix.mul_assoc], hμ,
        Matrix.mul_smul, Matrix.smul_mul, hμ, smul_smul]
    rw [hAA, transpose_smul, transpose_one, Matrix.smul_mul, Matrix.one_mul,
      Matrix.mul_smul, Matrix.mul_one, smul_smul] at e1
    exact mul_self_eq_mul_self_iff.mp (smul_formJ_injective 2 e1)
  by_cases hsq : ∃ l : K, l ^ 2 = (μ : K)
  ·
    exfalso
    obtain ⟨l, hl⟩ := hsq
    have hl0 : l ≠ 0 := by
      rintro rfl
      rw [zero_pow two_ne_zero] at hl
      exact μ.ne_zero hl.symm
    have hA'sp : (l⁻¹ • Am)ᵀ * formJ 2 K * (l⁻¹ • Am) = formJ 2 K := by
      rw [transpose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, hμ, smul_smul,
        smul_smul, ← hl]
      rw [show l⁻¹ * l⁻¹ * l ^ 2 = 1 by field_simp, one_smul]
    set A' : StatedSp 2 K := toSp (l⁻¹ • Am) hA'sp with hA'def
    have hAz : (A : GL (Fin 2 ⊕ Fin 2) K) =
        GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) (Units.mk0 l hl0) *
          (A' : GL (Fin 2 ⊕ Fin 2) K) := by
      apply Units.ext
      rw [Units.val_mul, GeneralLinearGroup.coe_scalar, hA'def, coe_toSp, Units.val_mk0,
        Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul,
        Matrix.one_mul, smul_smul, mul_inv_cancel₀ hl0, one_smul]
    have hαu : α = MulAut.conj (proj 2 K A') :=
      hα'.trans (conjAut_eq_conj_of_scalar_mul A _ A' hAz)
    set u := proj 2 K A' with hudef
    have hu1 : u ≠ 1 := fun h => hα1 (by rw [hαu, h, map_one])
    have hu2 : u * u = 1 := by
      have hc : MulAut.conj (u * u) = 1 := by rw [map_mul, ← hαu, hα2]
      have hz : u * u ∈ center (StatedProj (StatedSp 2 K)) := by
        rw [mem_center_iff]
        intro g
        have := congrArg (fun φ : MulAut (StatedProj (StatedSp 2 K)) => φ g) hc
        simp only [MulAut.conj_apply, MulAut.one_apply] at this
        calc g * (u * u) = u * u * g * (u * u)⁻¹ * (u * u) := by rw [this]
          _ = u * u * g := by group
      rw [hZ] at hz
      exact mem_bot.mp hz
    have hu : orderOf u = 2 := orderOf_eq_prime (by rw [pow_two]; exact hu2) hu1
    obtain ⟨φ, hφ⟩ := exists_model_conj hodd hu
    have hcomm : ∀ x, φ (α x) = MulAut.conj (φ u) (φ x) := fun x => by
      rw [hαu]
      exact conj_comm φ u x
    obtain ⟨hJ0X, hJ0⟩ := isPComponent_map_fixOf hcomm hXα hX
    rw [fixOf_conj] at hJ0X hJ0
    rcases hφ with h | h
    ·
      rw [h] at hJ0X hJ0
      obtain ⟨hE, -⟩ := pComponent_centralizer_u1 hodd hJ0X hJ0
      have hev : Even (Nat.card (center ↥(X.map φ.toMonoidHom))) := by
        rcases hE with hE | hE
        · rw [hE, ← Nat.card_congr (Subgroup.centerCongr (E1Equiv h2)).toEquiv]
          exact even_card_center_SL2 h2
        · rw [hE, ← Nat.card_congr (Subgroup.centerCongr (E2Equiv h2)).toEquiv]
          exact even_card_center_SL2 h2
      rw [← Nat.card_congr (Subgroup.centerCongr
        (X.equivMapOfInjective φ.toMonoidHom φ.injective)).toEquiv] at hev
      exact (Nat.not_even_iff_odd.mpr hZX) hev
    ·
      rw [h] at hJ0X hJ0 hcomm
      obtain ⟨hL, h5⟩ := pComponent_centralizer_u2 hodd hJ0X hJ0
      refine false_of_tcWitness hXq hXφ (TCWitness.of_comm hcomm ?_) hnt
      rw [hL]
      exact tcWitness_u2 h2 (by omega)
  · push Not at hsq
    rcases hdμ with hdm | hdm
    ·
      have hdsq : ∀ l : K, l ^ 2 ≠ (d : K) := by rw [hdm]; exact hsq
      have hμd : Amᵀ * formJ 2 K * Am = (d : K) • formJ 2 K := by rw [hdm]; exact hμ
      obtain ⟨hQ, hcard⟩ := fixOf_conjSp_nonsquare hp hp2 hf hK A d.ne_zero hdsq hAA hμd
      have hθα : ∀ g, α (proj 2 K g) = proj 2 K (conjSp 2 K A g) := fun g => by
        rw [hα', conjAut_proj]
      have hJeq := eq_map_fixOf_of_isPComponent (conjSp 2 K A) hθα hQ hXα hX
      have hc2 := card_center_fixOf_nonsquare hp hp2 hf hK A d.ne_zero hdsq hAA hμd
      have hsc : ∀ z ∈ spScalars 2 K, conjSp 2 K A z = z := fun z hz => conjSp_scalar A hz
      have hs := isSimpleGroup_map_fixOf h2 (conjSp 2 K A) hsc hQ hc2
      have h2c := card_map_fixOf_mul_two h2 (conjSp 2 K A) hsc
      rw [hJeq]
      exact ⟨hs, h2c.trans hcard⟩
    ·
      exfalso
      have ha : (d : K) ≠ 0 := d.ne_zero
      have hA : Amᵀ * formJ 2 K * Am = (-(d : K)) • formJ 2 K := by
        rw [hμ, hdm, neg_neg]
      obtain ⟨g, hg⟩ := exists_frame_typeI h2 ha hA hAA
      have hGL : (A : GL (Fin 2 ⊕ Fin 2) K) * (g : GL (Fin 2 ⊕ Fin 2) K) =
          (g : GL (Fin 2 ⊕ Fin 2) K) * ((aIgsp ha : gsp 2 K) : GL (Fin 2 ⊕ Fin 2) K) := by
        apply Units.ext
        rw [Units.val_mul, Units.val_mul, coe_aIgsp]
        exact hg
      have hcomm : ∀ x, (MulAut.conj (proj 2 K g))⁻¹ (α x) =
          alphaI ha ((MulAut.conj (proj 2 K g))⁻¹ x) := fun x => by
        rw [hα']
        exact conj_inv_conjAut A (aIgsp ha) g hGL x
      obtain ⟨hJ0X, hJ0⟩ := isPComponent_map_fixOf hcomm hXα hX
      by_cases h4 : 4 ≤ Nat.card K
      · have hJI := pComponent_fix_alphaI ha h2 h4 hJ0X hJ0
        refine false_of_tcWitness hXq hXφ (TCWitness.of_comm hcomm ?_) hnt
        rw [hJI]
        exact tcWitness_alphaI ha h2 h4
      ·
        have hK3 : Nat.card K = 3 := by
          have h1 : 1 < Nat.card K := Finite.one_lt_card
          obtain ⟨k, hk⟩ := hodd
          omega
        have hperf := commutator_eq_of_isPComponent hJ0X hJ0
        have hne := ne_bot_of_isPComponent hJ0
        have hle := perfect_le_JI ha h2 (fun x hx => hJ0X hx) hperf
        have hJI : Nat.card (JI ha) ≤ 24 := by
          rw [← Nat.card_congr (JIEquiv ha).toEquiv]
          have h1 := Nat.le_of_dvd Nat.card_pos
            (Subgroup.card_quotient_dvd_card (center (Matrix.SpecialLinearGroup (Fin 2) K)))
          rw [card_SL2, hK3] at h1
          exact h1
        have hcard : Nat.card ↥(X.map ((MulAut.conj (proj 2 K g))⁻¹).toMonoidHom) < 60 := by
          have h1 := Subgroup.card_le_of_le hle
          omega
        have hsolv := CFSG.GroupTheory.groups_order_below_sixty_solvable hcard
        have : Nontrivial ↥(X.map ((MulAut.conj (proj 2 K g))⁻¹).toMonoidHom) :=
          (Subgroup.nontrivial_iff_ne_bot _).mpr hne
        have := Subgroup.isPerfect_iff.mpr hperf
        exact Group.IsPerfect.not_isSolvable _ hsolv

end CFSG.ComponentClassification.GSThmB.CF23I
