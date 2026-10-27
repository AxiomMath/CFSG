module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4PSpL4
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4NoPSpUGraph

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace StabU

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  UnitaryOut UnitaryConj HBlocks ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank
  CFSG.LinearGroups CFSG.ComponentClassification.CatalogueBAlternatingIsometry PSpL

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

include h in
theorem exists_real_frame (hp2 : p ≠ 2) (hq : p ^ f % 4 = 1) {A : GL (Fin 4) K}
    (hAu : uStar h (A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K) = 1)
    (hAA : (A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K).map h.bar = -1) :
    ∃ (R : Matrix (Fin 4) (Fin 4) K) (t l : K), t ≠ 0 ∧ h.bar t = -t ∧ l ≠ 0 ∧
      uStar h R * R = t • omg ∧ l • ((A : Matrix (Fin 4) (Fin 4) K) * R.map h.bar) = R := by
  classical
  have : Finite K := h.finite
  obtain ⟨l, hl⟩ : ∃ l : K, l ^ 2 = -1 := by
    let : Fintype K := Fintype.ofFinite K
    have hcK : Fintype.card K % 4 = 1 := by
      rw [Fintype.card_eq_nat_card, h.card, pow_mul, Nat.pow_mod]
      rw [show p ^ 2 % 4 = 1 by
        rcases Nat.even_or_odd p with he | ho
        · exfalso
          exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two h.prime).1
            (even_iff_two_dvd.1 he)).symm
        · obtain ⟨t, rfl⟩ := ho
          ring_nf
          omega]
      simp
    obtain ⟨r, hr⟩ := (FiniteField.isSquare_neg_one_iff (F := K)).2 (by omega)
    exact ⟨r, by rw [sq, ← hr]⟩
  have hl0 : l ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num)] at hl
    exact one_ne_zero (by linear_combination hl : (1 : K) = 0)
  have hNl : h.norm l = -1 := norm_eq_neg_one_of_sq h hq hl
  set τ₀ := antiunitaryMap h (A : Matrix (Fin 4) (Fin 4) K) with hτ₀
  have hμ : ∀ v, τ₀ (τ₀ v) = ((-1 : Kˣ) : K) • v := fun v => by
    rw [Units.val_neg, Units.val_one]
    exact antiunitaryMap_sq h _ (by rw [hAA, neg_one_smul]) v
  obtain ⟨-, -, ⟨t, ht⟩, hmain⟩ := odd_unitary_conjugate_semilinear_involution_descent h
    (h.prime.odd_of_ne_two hp2) (by rw [Module.finrank_fin_fun]; norm_num)
    (stdHermForm_isSymm h 4) (stdHermForm_separatingLeft h 4) τ₀ (antiunitaryMap_bijective h A)
    (stdHermForm_antiunitaryMap h hAu) (-1) hμ
  set b : Kˣ := Units.mk0 l hl0 with hb
  have hbN : h.norm (b : K) = ((-1 : Kˣ)⁻¹ : Kˣ) := by
    rw [hb, Units.val_mk0, hNl, inv_neg, inv_one, Units.val_neg, Units.val_one]
  obtain ⟨-, hfinW, -, -, halt⟩ := hmain b t hbN ht
  obtain ⟨B, hBv, hBalt, hBnd, -, -⟩ := halt rfl
  obtain ⟨m, bW, hm, hb1, hb2, hb3⟩ := exists_blueprint_symplectic_basis B hBalt hBnd
  rw [hfinW, Module.finrank_fin_fun] at hm
  obtain rfl : m = 2 := by omega
  set bas : Fin 4 → conjFixed h ((b : K) • τ₀) :=
    ![bW (Sum.inl 0), bW (Sum.inl 1), bW (Sum.inr 0), bW (Sum.inr 1)] with hbas
  have hgram : ∀ j k : Fin 4, ((B (bas j) (bas k) : h.fixedField) : K) = omg j k := by
    have e3 := fun i j => congrArg (fun z : h.fixedField => (z : K)) (hb3 i j)
    have e1 := fun i j => congrArg (fun z : h.fixedField => (z : K)) (hb1 i j)
    have e2 := fun i j => congrArg (fun z : h.fixedField => (z : K)) (hb2 i j)
    have e4 : ∀ i j : Fin 2, ((B (bW (Sum.inr j)) (bW (Sum.inl i)) : h.fixedField) : K) =
        -(if i = j then 1 else 0) := by
      intro i j
      rw [← hBalt.neg_eq, Subfield.coe_neg, hb3]
      split_ifs <;> simp
    intro j k
    fin_cases j <;> fin_cases k <;>
      simp [hbas, omg, e1, e2, e3, e4]
  have hherm : ∀ j k : Fin 4, stdHermForm h 4 (bas j) (bas k) = t * omg j k := by
    intro j k
    rw [← hgram j k, hBv]
    field_simp
  have hfix : ∀ j : Fin 4, l • ((A : Matrix (Fin 4) (Fin 4) K) *ᵥ
      fun i => h.bar ((bas j : Fin 4 → K) i)) = bas j := by
    intro j
    have := (mem_conjFixed.1 (bas j).2)
    rw [LinearMap.smul_apply] at this
    exact this
  set R : Matrix (Fin 4) (Fin 4) K := Matrix.of fun i j => (bas j : Fin 4 → K) i with hR
  have hR1 : uStar h R * R = (t : K) • omg := by
    ext j k
    rw [Matrix.smul_apply, smul_eq_mul, ← hherm j k, stdHermForm_apply]
    simp [uStar, Matrix.mul_apply, hR]
  refine ⟨R, t, l, Units.ne_zero t, ht, hl0, hR1, ?_⟩
  ext i j
  have := congrFun (hfix j) i
  rw [Pi.smul_apply, smul_eq_mul] at this
  rw [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply]
  change _ = (bas j : Fin 4 → K) i
  rw [← this]
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, hR, Matrix.of_apply]

@[expose] noncomputable def glIncl : GL (Fin 4) h.fixedField →* GL (Fin 4) K :=
  Units.map (RingHom.mapMatrix h.fixedField.subtype).toMonoidHom

theorem coe_glIncl (g : GL (Fin 4) h.fixedField) :
    ((glIncl h g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      (g : Matrix (Fin 4) (Fin 4) h.fixedField).map h.fixedField.subtype := rfl

theorem map_bar_glIncl (g : GL (Fin 4) h.fixedField) :
    ((glIncl h g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map h.bar =
      ((glIncl h g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
  rw [coe_glIncl, Matrix.map_map]
  congr 1
  funext c
  exact (h.mem_fixedField.1 c.2)

omit [Field K] in
theorem omg_map {L L' : Type} [Field L] [Field L'] (φ : L →+* L') :
    (omg : Matrix (Fin 4) (Fin 4) L).map φ = omg := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [omg]

include h in
theorem exists_psp_of_alt_U4 (hp2 : p ≠ 2) (hq : p ^ f % 4 = 1) {A : GL (Fin 4) K}
    (hAu : uStar h (A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K) = 1)
    (hAA : (A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K).map h.bar = -1)
    (ψ : unitarySU p f K 4 →* unitarySU p f K 4)
    (hψv : ∀ g, ((ψ g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      (A : Matrix (Fin 4) (Fin 4) K) * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map h.bar *
        (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K))
    {α : MulAut (StatedProj (StatedSU 4 (p ^ f) K))}
    (hψ : ∀ g, (QuotientGroup.mk (ψ g) : StatedProj (StatedSU 4 (p ^ f) K)) =
      α (QuotientGroup.mk g)) :
    ∃ M : Subgroup (StatedProj (StatedSU 4 (p ^ f) K)), (∀ y ∈ M, α y = y) ∧
      Blueprint.LieModel ↥M .PSp 2 p f := by
  classical
  obtain ⟨Rm, t, l, ht0, ht, hl0, hR1, hR2⟩ := exists_real_frame h hp2 hq hAu hAA
  have hRdet : Rm.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hR1
    rw [det_mul, h0, mul_zero, det_smul, Fintype.card_fin] at this
    have hω : (omg : Matrix (Fin 4) (Fin 4) K).det = 1 := by
      rw [Matrix.det_succ_row_zero]
      simp [omg, Fin.sum_univ_succ, Matrix.det_succ_row_zero, Matrix.submatrix, Fin.succAbove]
    rw [hω, mul_one] at this
    exact pow_ne_zero 4 ht0 this.symm
  set R : GL (Fin 4) K := GeneralLinearGroup.mkOfDetNeZero Rm hRdet with hRdef
  have hRv : (R : Matrix (Fin 4) (Fin 4) K) = Rm := GeneralLinearGroup.val_mkOfDetNeZero _ _
  have hRR : (R : Matrix (Fin 4) (Fin 4) K) * (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hRiR : (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) * (R : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  set ι₀ : StatedSp 2 h.fixedField →* GL (Fin 4) K :=
    (MulAut.conj R).toMonoidHom.comp ((glIncl h).comp (spGL h.fixedField)) with hι₀
  have hι₀v : ∀ M, ((ι₀ M : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      (R : Matrix (Fin 4) (Fin 4) K) *
        ((glIncl h (spGL h.fixedField M) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
          (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) := fun M => by
    rw [hι₀, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Units.val_mul,
      Units.val_mul, MonoidHom.comp_apply]
  have hspec : ∀ M : StatedSp 2 h.fixedField,
      ((glIncl h (spGL h.fixedField M) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)ᵀ * omg *
          ((glIncl h (spGL h.fixedField M) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = omg ∧
        ((glIncl h (spGL h.fixedField M) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det = 1 := by
    intro M
    obtain ⟨h1, h2⟩ := spGL_spec h.fixedField M
    rw [coe_glIncl]
    refine ⟨?_, ?_⟩
    · rw [← omg_map h.fixedField.subtype, ← Matrix.transpose_map, ← Matrix.map_mul,
        ← Matrix.map_mul, h1]
    · rw [show ((spGL h.fixedField M : GL (Fin 4) h.fixedField) :
          Matrix (Fin 4) (Fin 4) h.fixedField).map h.fixedField.subtype =
          h.fixedField.subtype.mapMatrix ((spGL h.fixedField M : GL (Fin 4) h.fixedField) :
            Matrix (Fin 4) (Fin 4) h.fixedField) from rfl, ← RingHom.map_det, h2, map_one]
  have hmem : ∀ M, ι₀ M ∈ unitarySU p f K 4 := by
    intro M
    rw [mem_unitarySU_iff h]
    obtain ⟨hs, hd⟩ := hspec M
    refine ⟨?_, ?_⟩
    · rw [hι₀v, det_mul, det_mul, hd, mul_one, ← det_mul, hRR, det_one]
    · change uStar h _ * _ = 1
      have hX : uStar h ((glIncl h (spGL h.fixedField M) : GL (Fin 4) K) :
          Matrix (Fin 4) (Fin 4) K) =
          ((glIncl h (spGL h.fixedField M) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)ᵀ := by
        rw [uStar, map_bar_glIncl]
      have hRi : uStar h (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) * uStar h (R : Matrix (Fin 4) (Fin 4) K)
          = 1 := by rw [← uStar_mul, hRR, uStar_one]
      have hR1' : uStar h (R : Matrix (Fin 4) (Fin 4) K) * (R : Matrix (Fin 4) (Fin 4) K) =
          t • omg := by rw [hRv]; exact hR1
      rw [hι₀v, uStar_mul, uStar_mul, hX]
      calc uStar h (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) *
            (((glIncl h (spGL h.fixedField M) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)ᵀ *
            uStar h (R : Matrix (Fin 4) (Fin 4) K)) *
            ((R : Matrix (Fin 4) (Fin 4) K) *
              ((glIncl h (spGL h.fixedField M) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
              (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K)) =
          uStar h (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) *
            (((glIncl h (spGL h.fixedField M) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)ᵀ *
              (uStar h (R : Matrix (Fin 4) (Fin 4) K) * (R : Matrix (Fin 4) (Fin 4) K)) *
              ((glIncl h (spGL h.fixedField M) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) *
            (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) := by simp only [Matrix.mul_assoc]
        _ = uStar h (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) *
            (uStar h (R : Matrix (Fin 4) (Fin 4) K) * (R : Matrix (Fin 4) (Fin 4) K)) *
            (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) := by
            rw [hR1', Matrix.mul_smul, Matrix.smul_mul, hs]
        _ = 1 := by
            rw [← Matrix.mul_assoc, hRi, Matrix.one_mul, hRR]
  set ι : StatedSp 2 h.fixedField →* unitarySU p f K 4 := ι₀.codRestrict _ hmem with hι
  have hιv : ∀ M, (((ι M : unitarySU p f K 4) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      (R : Matrix (Fin 4) (Fin 4) K) *
        ((glIncl h (spGL h.fixedField M) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
          (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) := fun M => hι₀v M
  set φ : StatedSp 2 h.fixedField →* StatedProj (StatedSU 4 (p ^ f) K) :=
    (QuotientGroup.mk' (scal p f K)).comp ι with hφ
  have hA1 : (A : Matrix (Fin 4) (Fin 4) K) * (R : Matrix (Fin 4) (Fin 4) K).map h.bar =
      l⁻¹ • (R : Matrix (Fin 4) (Fin 4) K) := by
    rw [hRv]
    conv_rhs => rw [← hR2]
    rw [smul_smul, inv_mul_cancel₀ hl0, one_smul]
  have hAA' : (A : Matrix (Fin 4) (Fin 4) K) * (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hRb : (R : Matrix (Fin 4) (Fin 4) K).map h.bar *
      (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K).map h.bar = 1 := by
    rw [← Matrix.map_mul, hRR, Matrix.map_one _ (map_zero _) (map_one _)]
  have hB : (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K).map h.bar * (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) =
      l • (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) := by
    calc (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K).map h.bar * (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) =
        (l • (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K)) * (l⁻¹ • (R : Matrix (Fin 4) (Fin 4) K)) *
          ((↑R⁻¹ : Matrix (Fin 4) (Fin 4) K).map h.bar * (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K)) := by
          rw [Matrix.smul_mul, Matrix.mul_smul, hRiR, smul_smul, mul_inv_cancel₀ hl0, one_smul,
            Matrix.one_mul]
      _ = (l • (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K)) * ((A : Matrix (Fin 4) (Fin 4) K) *
          ((R : Matrix (Fin 4) (Fin 4) K).map h.bar * (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K).map h.bar) *
            (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K)) := by
          rw [← hA1]
          simp only [Matrix.mul_assoc]
      _ = l • (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) := by rw [hRb, Matrix.mul_one, hAA', Matrix.mul_one]
  refine ⟨φ.range, ?_, ?_⟩
  · rintro _ ⟨M, rfl⟩
    rw [hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, ← hψ]
    congr 1
    apply ext_val
    rw [hψv, hιv, Matrix.map_mul, Matrix.map_mul, map_bar_glIncl]
    calc (A : Matrix (Fin 4) (Fin 4) K) * ((R : Matrix (Fin 4) (Fin 4) K).map h.bar *
          ((glIncl h (spGL h.fixedField M) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
          (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K).map h.bar) * (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) =
        ((A : Matrix (Fin 4) (Fin 4) K) * (R : Matrix (Fin 4) (Fin 4) K).map h.bar) *
          ((glIncl h (spGL h.fixedField M) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
          ((↑R⁻¹ : Matrix (Fin 4) (Fin 4) K).map h.bar * (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K)) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by
          rw [hA1, hB, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul,
            mul_inv_cancel₀ hl0, one_smul]
  · have : Finite K := h.finite
    refine lieModel_range_of_ker h.prime h.one_le h.card_fixedField (fun h2 => ?_) φ ?_
    · have := h.prime.two_le
      have h3 : 3 ≤ p := by omega
      have : p ≤ p ^ f := Nat.le_self_pow (by have := h.one_le; omega) p
      omega
    · ext M
      rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      constructor
      · intro hM
        obtain ⟨c, hc⟩ := hM
        have hc' := congrArg (fun Y : GL (Fin 4) K => (Y : Matrix (Fin 4) (Fin 4) K)) hc
        simp only [GeneralLinearGroup.coe_scalar] at hc'
        change _ = ((ι M : unitarySU p f K 4) : GL (Fin 4) K).val at hc'
        rw [hιv] at hc'
        have hX : ((glIncl h (spGL h.fixedField M) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
            (c : K) • 1 := by
          calc ((glIncl h (spGL h.fixedField M) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
              (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) * ((R : Matrix (Fin 4) (Fin 4) K) *
                ((glIncl h (spGL h.fixedField M) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
                  (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K)) * (R : Matrix (Fin 4) (Fin 4) K) := by
                simp only [← Matrix.mul_assoc]
                rw [hRiR, Matrix.one_mul, Matrix.mul_assoc, hRiR, Matrix.mul_one]
            _ = (c : K) • 1 := by
                rw [← hc', Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul,
                  Matrix.mul_one, Matrix.smul_mul, hRiR]
        set c' : h.fixedField := ((spGL h.fixedField M : GL (Fin 4) h.fixedField) :
          Matrix (Fin 4) (Fin 4) h.fixedField) 0 0 with hc'def
        apply mem_statedScalars_of_spGL (c := c')
        ext i j
        have e1 := congrFun (congrFun hX i) j
        have e0 := congrFun (congrFun hX 0) 0
        rw [coe_glIncl, Matrix.map_apply] at e1 e0
        simp only [Subfield.coe_subtype, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul,
          mul_one] at e1 e0
        rw [e1, Matrix.smul_apply, smul_eq_mul, Subfield.coe_mul, hc'def, e0]
        by_cases hij : i = j
        · subst hij
          simp
        · simp [hij]
      · intro hM
        obtain ⟨c, hc⟩ := spGL_of_mem_statedScalars hM
        refine ⟨Units.map h.fixedField.subtype.toMonoidHom c, ?_⟩
        apply Units.ext
        rw [GeneralLinearGroup.coe_scalar]
        change _ = ((ι M : unitarySU p f K 4) : GL (Fin 4) K).val
        rw [hιv, coe_glIncl, hc]
        have : ((c : h.fixedField) • (1 : Matrix (Fin 4) (Fin 4) h.fixedField)).map
            h.fixedField.subtype = ((c : h.fixedField) : K) • 1 := by
          ext i j
          by_cases hij : i = j
          · subst hij
            simp
          · simp [hij]
        rw [this, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hRR, Matrix.scalar_apply,
          Matrix.smul_one_eq_diagonal]
        rfl

end StabU

end CFSG.ComponentClassification.CatFactsL4U4
