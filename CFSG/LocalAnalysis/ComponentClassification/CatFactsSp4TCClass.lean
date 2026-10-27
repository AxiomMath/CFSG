module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4OutF
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4OutIFrame
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4OutII

public noncomputable section

namespace CFSG.ComponentClassification.CatFactsSp4

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher SymplecticFlag Subgroup

section General

variable {G G' : Type*} [Group G] [Group G']

theorem map_fixOf_of_comm {β : G ≃* G'} {α : MulAut G} {α₀ : MulAut G'}
    (h : ∀ x, β (α x) = α₀ (β x)) : (fixOf α).map β.toMonoidHom = fixOf α₀ := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change α₀ (β x) = β x
    rw [← h]
    exact congrArg β hx
  · intro hy
    refine ⟨β.symm y, ?_, β.apply_symm_apply y⟩
    change α (β.symm y) = β.symm y
    apply β.injective
    rw [h, β.apply_symm_apply]
    exact hy

theorem TCWitness.of_comm {β : G ≃* G'} {α : MulAut G} {α₀ : MulAut G'}
    (h : ∀ x, β (α x) = α₀ (β x)) {J : Subgroup G} (hw : TCWitness α₀ (J.map β.toMonoidHom)) :
    TCWitness α J := by
  have hm := hw.map β.symm
  have e1 : β.symm.symm.trans (α₀.trans β.symm) = α := by
    ext x
    simp only [MulEquiv.trans_apply, MulEquiv.symm_symm]
    rw [← h, MulEquiv.symm_apply_apply]
  have e2 : (J.map β.toMonoidHom).map β.symm.toMonoidHom = J := by
    rw [Subgroup.map_map]
    convert Subgroup.map_id J
    ext x
    simp
  rw [e1, e2] at hm
  exact hm

theorem isPComponent_map_fixOf {β : G ≃* G'} {α : MulAut G} {α₀ : MulAut G'}
    (h : ∀ x, β (α x) = α₀ (β x)) {J : Subgroup G} (hJX : J ≤ fixOf α)
    (hJ : CFSG.IsPComponent 2 (J.subgroupOf (fixOf α))) :
    J.map β.toMonoidHom ≤ fixOf α₀ ∧
      CFSG.IsPComponent 2 ((J.map β.toMonoidHom).subgroupOf (fixOf α₀)) := by
  have hm := isPComponent_map_subgroupOf 2 β hJX hJ
  rw [map_fixOf_of_comm h] at hm
  refine ⟨?_, hm⟩
  rw [← map_fixOf_of_comm h]
  exact map_mono hJX

theorem conj_comm (φ : G ≃* G') (u x : G) : φ (MulAut.conj u x) = MulAut.conj (φ u) (φ x) := by
  simp only [MulAut.conj_apply, map_mul, map_inv]

end General

section Arithmetic

theorem two_mul_ordL2 {q : ℕ} (hq : Odd q) : 2 * (q * (q ^ 2 - 1) / 2) = q * (q ^ 2 - 1) := by
  apply Nat.mul_div_cancel'
  apply Even.two_dvd
  apply Nat.even_mul.mpr
  right
  obtain ⟨k, rfl⟩ := hq
  refine ⟨2 * k ^ 2 + 2 * k, ?_⟩
  have : (2 * k + 1) ^ 2 = 4 * k ^ 2 + 4 * k + 1 := by ring
  omega

theorem ordL2_pos {q : ℕ} (hq : 3 ≤ q) : 0 < q * (q ^ 2 - 1) / 2 := by
  have h1 : 1 < q ^ 2 := by nlinarith
  have h2 : 2 ≤ q * (q ^ 2 - 1) := by
    have : 1 ≤ q ^ 2 - 1 := by omega
    nlinarith
  omega

theorem card_ne_SL2 {q o : ℕ} (hq : Odd q) (hq3 : 3 ≤ q) (ho : Odd o) :
    o * (q * (q ^ 2 - 1) / 2) ≠ q * (q ^ 2 - 1) := by
  intro h
  have hpos := ordL2_pos hq3
  set N := q * (q ^ 2 - 1) / 2 with hNdef
  have hN : q * (q ^ 2 - 1) = 2 * N := (two_mul_ordL2 hq).symm
  rw [hN] at h
  have := Nat.eq_of_mul_eq_mul_right hpos h
  rw [this] at ho
  exact (Nat.not_odd_iff_even.mpr even_two) ho

theorem card_ne_L2sq {q o : ℕ} (hq : Odd q) (hq3 : 3 ≤ q) (ho : Odd o) :
    o * (q * (q ^ 2 - 1) / 2) * 2 ≠ q ^ 2 * ((q ^ 2) ^ 2 - 1) := by
  intro h
  have h1 : q ^ 2 * ((q ^ 2) ^ 2 - 1) = (q * (q ^ 2 + 1)) * (2 * (q * (q ^ 2 - 1) / 2)) := by
    rw [two_mul_ordL2 hq]
    have : 1 ≤ q ^ 2 := by nlinarith
    zify [this, show 1 ≤ (q ^ 2) ^ 2 by nlinarith]
    ring
  rw [h1, mul_assoc, mul_comm (q * (q ^ 2 - 1) / 2) 2, ← mul_assoc,
    show o * 2 * (q * (q ^ 2 - 1) / 2) = (2 * o) * (q * (q ^ 2 - 1) / 2) by ring,
    show q * (q ^ 2 + 1) * (2 * (q * (q ^ 2 - 1) / 2)) =
      (q * (q ^ 2 + 1) * 2) * (q * (q ^ 2 - 1) / 2) by ring] at h
  have h2 := Nat.eq_of_mul_eq_mul_right (ordL2_pos hq3) h
  have h3 : o = q * (q ^ 2 + 1) := by omega
  rw [h3] at ho
  obtain ⟨-, h4⟩ := Nat.odd_mul.mp ho
  have h5 : Odd (q ^ 2) := hq.pow
  have := Nat.even_add_one.mpr (Nat.not_even_iff_odd.mpr h5)
  exact (Nat.not_even_iff_odd.mpr h4) this

theorem card_ne_PSp4sqrt {k o : ℕ} (hk : Odd k) (hk3 : 3 ≤ k) (ho : Odd o) :
    o * (k ^ 2 * ((k ^ 2) ^ 2 - 1) / 2) * 2 ≠ k ^ 4 * ((k ^ 2 - 1) * (k ^ 4 - 1)) := by
  intro h
  have hq : Odd (k ^ 2) := hk.pow
  have hq3 : 3 ≤ k ^ 2 := by nlinarith
  have hpos := ordL2_pos hq3
  have hN := two_mul_ordL2 hq
  have e : (k ^ 2) ^ 2 = k ^ 4 := by ring
  rw [e] at h hpos hN
  set N := k ^ 2 * (k ^ 4 - 1) / 2 with hNdef
  have h1 : k ^ 4 * ((k ^ 2 - 1) * (k ^ 4 - 1)) = (k ^ 2 * (k ^ 2 - 1) * 2) * N := by
    calc k ^ 4 * ((k ^ 2 - 1) * (k ^ 4 - 1)) = (k ^ 2 * (k ^ 2 - 1)) * (k ^ 2 * (k ^ 4 - 1)) := by
          ring
      _ = (k ^ 2 * (k ^ 2 - 1)) * (2 * N) := by rw [hN]
      _ = (k ^ 2 * (k ^ 2 - 1) * 2) * N := by ring
  rw [h1, show o * N * 2 = (o * 2) * N by ring] at h
  have h2 := Nat.eq_of_mul_eq_mul_right hpos h
  have h3 : o = k ^ 2 * (k ^ 2 - 1) := by omega
  rw [h3] at ho
  obtain ⟨-, h4⟩ := Nat.odd_mul.mp ho
  obtain ⟨m, hm⟩ := hq
  rw [hm, Nat.add_sub_cancel] at h4
  exact (Nat.not_odd_iff_even.mpr (even_two_mul m)) h4

end Arithmetic

variable {K : Type} [Field K]

theorem card_SL2 [Finite K] :
    Nat.card (SpecialLinearGroup (Fin 2) K) = Nat.card K * (Nat.card K ^ 2 - 1) := by
  let := Fintype.ofFinite K
  have hq : 1 < Fintype.card K := Fintype.one_lt_card
  rw [Matrix.card_SL_field, Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
    Nat.card_eq_fintype_card, show Fintype.card K ^ 2 - Fintype.card K =
      Fintype.card K * (Fintype.card K - 1) by rw [Nat.mul_sub_one, sq], ← mul_assoc,
    Nat.mul_div_cancel _ (by omega), mul_comm]

theorem conjAut_eq_conj_of_scalar_mul (A : gsp 2 K) (z : Kˣ) (y : StatedSp 2 K)
    (hA : (A : GL (Fin 2 ⊕ Fin 2) K) =
      GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) z * (y : GL (Fin 2 ⊕ Fin 2) K)) :
    conjAut 2 K A = MulAut.conj (proj 2 K y) := by
  have hz : GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) z ∈
      Subgroup.center (GL (Fin 2 ⊕ Fin 2) K) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨_, rfl⟩
  ext t
  obtain ⟨g, rfl⟩ := proj_surjective t
  rw [conjAut_proj, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  rw [coe_conjSp, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hA]
  set z' := GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) z
  set u := (y : GL (Fin 2 ⊕ Fin 2) K)
  have hzc := Subgroup.mem_center_iff.mp hz (u * (g : GL (Fin 2 ⊕ Fin 2) K) * u⁻¹)
  calc z' * u * (g : GL (Fin 2 ⊕ Fin 2) K) * (z' * u)⁻¹ =
        u * (g : GL (Fin 2 ⊕ Fin 2) K) * u⁻¹ * z' * z'⁻¹ := by
        rw [hzc]
        group
    _ = u * (g : GL (Fin 2 ⊕ Fin 2) K) * u⁻¹ := by rw [mul_inv_cancel_right]

theorem conj_inv_conjAut (A B : gsp 2 K) (g : StatedSp 2 K)
    (h : (A : GL (Fin 2 ⊕ Fin 2) K) * (g : GL (Fin 2 ⊕ Fin 2) K) =
      (g : GL (Fin 2 ⊕ Fin 2) K) * (B : GL (Fin 2 ⊕ Fin 2) K))
    (x : StatedProj (StatedSp 2 K)) :
    (MulAut.conj (proj 2 K g))⁻¹ (conjAut 2 K A x) =
      conjAut 2 K B ((MulAut.conj (proj 2 K g))⁻¹ x) := by
  obtain ⟨y, rfl⟩ := proj_surjective x
  rw [MulAut.conj_inv_apply, MulAut.conj_inv_apply, conjAut_proj, ← map_inv, ← map_mul,
    ← map_mul, ← map_mul, ← map_mul, conjAut_proj]
  congr 1
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_conjSp, coe_conjSp,
    Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  have hA : (A : GL (Fin 2 ⊕ Fin 2) K) =
      (g : GL (Fin 2 ⊕ Fin 2) K) * (B : GL (Fin 2 ⊕ Fin 2) K) * (g : GL (Fin 2 ⊕ Fin 2) K)⁻¹ := by
    rw [← h, mul_inv_cancel_right]
  rw [hA]
  group

theorem eq_one_of_mem_center_P [Finite K] (h2 : (2 : K) ≠ 0) (h4 : 4 ≤ Nat.card K)
    (hs : IsSimpleGroup (StatedProj (StatedSp 2 K))) {z : StatedProj (StatedSp 2 K)}
    (hz : z ∈ center (StatedProj (StatedSp 2 K))) : z = 1 := by
  rcases (center (StatedProj (StatedSp 2 K))).normal_of_characteristic.eq_bot_or_eq_top with
    hb | ht
  · rw [hb] at hz
    exact hz
  · exfalso
    obtain ⟨x, -, y, -, hxy⟩ := exists_mul_ne_of_isQuasisimple (isQuasisimple_E1 h2 h4)
    have hx : x ∈ center (StatedProj (StatedSp 2 K)) := ht ▸ Subgroup.mem_top x
    exact hxy (mem_center_iff.mp hx y).symm

theorem conjSp_fieldSp_scalar (A : gsp 2 K) (σ : K ≃+* K) {z : StatedSp 2 K}
    (hz : z ∈ spScalars 2 K) : (conjSp 2 K A * fieldSp 2 K σ) z = z := by
  rcases (mem_spScalars_iff z).mp hz with h | h
  · have : z = 1 := sp_ext (by rw [h]; rfl)
    rw [this, map_one]
  · apply sp_ext
    have hm : (-1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).map σ = -1 := by
      ext i j
      by_cases hij : i = j <;> simp [hij]
    rw [MulAut.mul_apply, coe_conjSp, Units.val_mul, Units.val_mul, coe_fieldSp, h, hm,
      Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul, Units.mul_inv]

theorem conjSp_scalar (A : gsp 2 K) {z : StatedSp 2 K} (hz : z ∈ spScalars 2 K) :
    conjSp 2 K A z = z := by
  have := conjSp_fieldSp_scalar A 1 hz
  rwa [map_one, mul_one] at this

theorem tcWitness_of_involution {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) [Finite K]
    (hK : Nat.card K = p ^ f) (h5 : 5 ≤ p ^ f)
    (hs : IsSimpleGroup (StatedProj (StatedSp 2 K)))
    (α : MulAut (StatedProj (StatedSp 2 K))) (hα2 : α * α = 1) (hα1 : α ≠ 1)
    {J : Subgroup (StatedProj (StatedSp 2 K))} (hJX : J ≤ fixOf α)
    (hJ : CFSG.IsPComponent 2 (J.subgroupOf (fixOf α)))
    (hJcard : ∃ o, Odd o ∧ Nat.card J = o * (p ^ f * ((p ^ f) ^ 2 - 1) / 2)) :
    TCWitness α J := by
  have hodd : Odd (Nat.card K) := odd_card_of_card_eq hp hp2 hK
  have hqodd : Odd (p ^ f) := hK ▸ hodd
  have h2 := two_ne_zero_of_odd_card hodd
  have h4 : 4 ≤ Nat.card K := by omega
  have hq3 : 3 ≤ p ^ f := by omega
  have hchar : ringChar K ≠ 2 := by
    intro h
    apply h2
    have := ringChar.Nat.cast_ringChar (R := K)
    rw [h] at this
    exact_mod_cast this
  obtain ⟨o, ho, hJc⟩ := hJcard
  obtain ⟨A, σ, hα, hσ2, ⟨d, hd⟩, hlin, hfield⟩ :=
    (CatalogueBSymplecticRepresentation.odd_symplectic_automorphism_semilinear_representation
      hchar le_rfl).2.2 α hα2 hα1
  by_cases hσ : σ = 1
  · subst hσ
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
        apply eq_one_of_mem_center_P h2 h4 hs
        rw [mem_center_iff]
        intro g
        have := congrArg (fun φ : MulAut (StatedProj (StatedSp 2 K)) => φ g) hc
        simp only [MulAut.conj_apply, MulAut.one_apply] at this
        calc g * (u * u) = u * u * g * (u * u)⁻¹ * (u * u) := by rw [this]
          _ = u * u * g := by group
      have hu : orderOf u = 2 := orderOf_eq_prime (by rw [pow_two]; exact hu2) hu1
      obtain ⟨φ, hφ⟩ := exists_model_conj hodd hu
      have hcomm : ∀ x, φ (α x) = MulAut.conj (φ u) (φ x) := fun x => by
        rw [hαu]
        exact conj_comm φ u x
      obtain ⟨hJ0X, hJ0⟩ := isPComponent_map_fixOf hcomm hJX hJ
      rw [fixOf_conj] at hJ0X hJ0
      have hcardJ : Nat.card (J.map φ.toMonoidHom) = Nat.card J :=
        (Nat.card_congr (J.equivMapOfInjective _ φ.injective).toEquiv).symm
      rcases hφ with h | h
      · exfalso
        rw [h] at hJ0X hJ0
        obtain ⟨hE, -⟩ := pComponent_centralizer_u1 hodd hJ0X hJ0
        have hc : Nat.card J = Nat.card K * (Nat.card K ^ 2 - 1) := by
          rcases hE with hE | hE
          · rw [← hcardJ, hE, ← Nat.card_congr (E1Equiv h2).toEquiv, card_SL2]
          · rw [← hcardJ, hE, ← Nat.card_congr (E2Equiv h2).toEquiv, card_SL2]
        rw [hJc, hK] at hc
        exact card_ne_SL2 hqodd hq3 ho hc
      · rw [h] at hJ0X hJ0 hcomm
        obtain ⟨hL, -⟩ := pComponent_centralizer_u2 hodd hJ0X hJ0
        refine TCWitness.of_comm hcomm ?_
        rw [hL]
        exact tcWitness_u2 h2 h4
    · push Not at hsq
      rcases hdμ with hdm | hdm
      ·
        exfalso
        have hdsq : ∀ l : K, l ^ 2 ≠ (d : K) := by rw [hdm]; exact hsq
        have hμd : Amᵀ * formJ 2 K * Am = (d : K) • formJ 2 K := by rw [hdm]; exact hμ
        obtain ⟨hQ, hcard⟩ := fixOf_conjSp_nonsquare hp hp2 hf hK A d.ne_zero hdsq hAA hμd
        have hθα : ∀ g, α (proj 2 K g) = proj 2 K (conjSp 2 K A g) := fun g => by
          rw [hα', conjAut_proj]
        have hJeq := eq_map_fixOf_of_isPComponent (conjSp 2 K A) hθα hQ hJX hJ
        have h2c := card_map_fixOf_mul_two h2 (conjSp 2 K A) fun z hz => conjSp_scalar A hz
        rw [← hJeq, hcard, hJc] at h2c
        exact card_ne_L2sq hqodd hq3 ho h2c
      ·
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
        obtain ⟨hJ0X, hJ0⟩ := isPComponent_map_fixOf hcomm hJX hJ
        have hJI := pComponent_fix_alphaI ha h2 h4 hJ0X hJ0
        refine TCWitness.of_comm hcomm ?_
        rw [hJI]
        exact tcWitness_alphaI ha h2 h4
  ·
    exfalso
    have hθα : ∀ g, α (proj 2 K g) = proj 2 K ((conjSp 2 K A * fieldSp 2 K σ) g) := fun g => by
      rw [hα]
      rfl
    obtain ⟨hQ, hcard⟩ := fixOf_conjSp_fieldSp hodd A σ hσ2 hσ d hd
    have hJeq := eq_map_fixOf_of_isPComponent _ hθα hQ hJX hJ
    have h2c := card_map_fixOf_mul_two h2 (conjSp 2 K A * fieldSp 2 K σ)
      fun z hz => conjSp_fieldSp_scalar A σ hz
    rw [← hJeq, hcard, hJc] at h2c
    obtain ⟨hKk, -⟩ := hfield hσ
    have hk : Nat.card {c : K // σ c = c} =
        Nat.card (CatalogueBLinearTwoDescent.fixedSubfield K σ) :=
      Nat.card_congr (Equiv.subtypeEquivRight fun c =>
        (CatalogueBLinearTwoDescent.mem_fixedSubfield K σ c).symm)
    rw [hk, hK] at hKk
    set k := Nat.card (CatalogueBLinearTwoDescent.fixedSubfield K σ)
    have hkodd : Odd k := by
      have : Odd (k ^ 2) := hKk ▸ hqodd
      exact (Nat.odd_mul.mp (by rwa [sq] at this)).1
    have hk3 : 3 ≤ k := by
      by_contra hlt
      push Not at hlt
      interval_cases k <;> simp_all
    rw [hKk] at h2c
    exact card_ne_PSp4sqrt hkodd hk3 ho h2c

end CFSG.ComponentClassification.CatFactsSp4
