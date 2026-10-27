module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4TU4Bound
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4PSpJU4
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4PSpTL4

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace StabU

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  UnitaryOut UnitaryConj HBlocks ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank TBlocks
  Subgroup PSpL

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem cP_bdHomU {R : GL (Fin 4) K} {t : K}
    (hR : uStar h (R : Matrix (Fin 4) (Fin 4) K) * (R : Matrix (Fin 4) (Fin 4) K) = t • bJ 1 1)
    (x : SpecialLinearGroup (Fin 2) h.fixedField × SpecialLinearGroup (Fin 2) h.fixedField) :
    cP R (bdHomU h hR x) = bdK h x := by
  rw [cP, val_bdHomU, inv_mul_val_mul]

theorem bdHomU_comm {R : GL (Fin 4) K} {t : K}
    (hR : uStar h (R : Matrix (Fin 4) (Fin 4) K) * (R : Matrix (Fin 4) (Fin 4) K) = t • bJ 1 1)
    {X : unitarySU p f K 4}
    (hXR : ((X : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (R : Matrix (Fin 4) (Fin 4) K) =
      (R : Matrix (Fin 4) (Fin 4) K) * X1 (1 : K))
    (x : SpecialLinearGroup (Fin 2) h.fixedField × SpecialLinearGroup (Fin 2) h.fixedField) :
    bdHomU h hR x * X = X * bdHomU h hR x := by
  apply eq_of_cP_eq R
  rw [cP_mul, cP_mul, cP_bdHomU, cP_X hXR, bdK, bd_comm_X1]

theorem map_uu (c : h.fixedField) : (uu c).map h.fixedField.subtype = uu (c : K) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uu]

theorem map_ll (c : h.fixedField) : (ll c).map h.fixedField.subtype = ll (c : K) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ll]

theorem map_one_fixed :
    (1 : Matrix (Fin 2) (Fin 2) h.fixedField).map h.fixedField.subtype = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

theorem bdK_gens :
    bdK h (slU 1, 1) = bd (uu 1) 1 ∧ bdK h (slL 1, 1) = bd (ll 1) 1 ∧
      bdK h (1, slU 1) = bd 1 (uu 1) ∧ bdK h (1, slL 1) = bd 1 (ll 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · rw [bdK]
    simp only [slU, slL, Matrix.SpecialLinearGroup.coe_one]
    rw [map_one_fixed]
    first
      | rw [show ((⟨uu 1, det_uu 1⟩ : SpecialLinearGroup (Fin 2) h.fixedField) :
          Matrix (Fin 2) (Fin 2) h.fixedField) = uu 1 from rfl, map_uu, OneMemClass.coe_one]
      | rw [show ((⟨ll 1, det_ll 1⟩ : SpecialLinearGroup (Fin 2) h.fixedField) :
          Matrix (Fin 2) (Fin 2) h.fixedField) = ll 1 from rfl, map_ll, OneMemClass.coe_one]
      | rw [map_uu, OneMemClass.coe_one]
      | rw [map_ll, OneMemClass.coe_one]

theorem trace_bdHomU_gens {R : GL (Fin 4) K} {t : K}
    (hR : uStar h (R : Matrix (Fin 4) (Fin 4) K) * (R : Matrix (Fin 4) (Fin 4) K) = t • bJ 1 1)
    {x : SpecialLinearGroup (Fin 2) h.fixedField × SpecialLinearGroup (Fin 2) h.fixedField}
    (hx : x ∈ bdGens) :
    (((bdHomU h hR x : unitarySU p f K 4) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).trace =
      4 := by
  rw [val_bdHomU, trace_conj']
  obtain ⟨g1, g2, g3, g4⟩ := bdK_gens h
  have h1 : (1 : Matrix (Fin 2) (Fin 2) K).trace = 2 := by
    rw [Matrix.trace_one, Fintype.card_fin]
    norm_num
  rcases hx with rfl | rfl | rfl | rfl
  · rw [g1, trace_bd, trace_uu, h1]; norm_num
  · rw [g2, trace_bd, trace_ll, h1]; norm_num
  · rw [g3, trace_bd, trace_uu, h1]; norm_num
  · rw [g4, trace_bd, trace_ll, h1]; norm_num

theorem bJ_mul_bJ : (bJ (1 : K) 1) * bJ 1 1 = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bJ, Matrix.mul_apply, Fin.sum_univ_four]

theorem map_bar_mul_eq_one {R : GL (Fin 4) K} {t : K} (ht0 : t ≠ 0)
    (hR : uStar h (R : Matrix (Fin 4) (Fin 4) K) * (R : Matrix (Fin 4) (Fin 4) K) = t • bJ 1 1) :
    (R : Matrix (Fin 4) (Fin 4) K).map h.bar * (t⁻¹ • (bJ 1 1 * (R : Matrix (Fin 4) (Fin 4) K)ᵀ))
      = 1 := by
  apply mul_eq_one_comm.mp
  have h1 : (R : Matrix (Fin 4) (Fin 4) K)ᵀ * (R : Matrix (Fin 4) (Fin 4) K).map h.bar =
      -(t • bJ 1 1) := by
    have := congrArg Matrix.transpose hR
    rw [uStar, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_smul,
      transpose_bJ, smul_neg] at this
    exact this
  rw [Matrix.smul_mul, Matrix.mul_assoc, h1, Matrix.mul_neg, Matrix.mul_smul, bJ_mul_bJ]
  simp only [smul_neg, neg_neg, smul_smul, inv_mul_cancel₀ ht0, one_smul]

theorem bd_smul_mul_bJ (x y : K) : bd (x • 1) (y • 1) * bJ 1 1 = bJ x y := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bd, bJ, Matrix.mul_apply, Fin.sum_univ_four]

omit [Field K] in
theorem gens_mem {F : Type} [Field F] :
    ((slU 1, 1) : SpecialLinearGroup (Fin 2) F × SpecialLinearGroup (Fin 2) F) ∈ bdGens ∧
      ((slL 1, 1) : SpecialLinearGroup (Fin 2) F × SpecialLinearGroup (Fin 2) F) ∈ bdGens ∧
      ((1, slU 1) : SpecialLinearGroup (Fin 2) F × SpecialLinearGroup (Fin 2) F) ∈ bdGens ∧
      ((1, slL 1) : SpecialLinearGroup (Fin 2) F × SpecialLinearGroup (Fin 2) F) ∈ bdGens :=
  ⟨Set.mem_insert _ _, Set.mem_insert_of_mem _ (Set.mem_insert _ _),
    Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)),
    Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
      (Set.mem_singleton _)))⟩

theorem map_bar_bd_gens (M : Matrix (Fin 4) (Fin 4) K)
    (hM : M = bd (uu 1) 1 ∨ M = bd (ll 1) 1 ∨ M = bd 1 (uu 1) ∨ M = bd 1 (ll 1)) :
    M.map h.bar = M := by
  rcases hM with rfl | rfl | rfl | rfl <;>
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [bd, uu, ll]

include h in
theorem inner_or_psp_t (hp2 : p ≠ 2) (hq : p ^ f % 4 = 1) {R : GL (Fin 4) K} {t : K}
    (ht0 : t ≠ 0)
    (hR : uStar h (R : Matrix (Fin 4) (Fin 4) K) * (R : Matrix (Fin 4) (Fin 4) K) = t • bJ 1 1)
    {X : unitarySU p f K 4}
    (hXR : ((X : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (R : Matrix (Fin 4) (Fin 4) K) =
      (R : Matrix (Fin 4) (Fin 4) K) * X1 (1 : K))
    (α : MulAut (StatedProj (StatedSU 4 (p ^ f) K))) (hα2 : α ^ 2 = 1)
    (hfix : ∀ x ∈ bdGens, α (QuotientGroup.mk (bdHomU h hR x)) =
      QuotientGroup.mk (bdHomU h hR x)) :
    α = 1 ∨ α = MulAut.conj (QuotientGroup.mk X) ∨
      ∃ M : Subgroup (StatedProj (StatedSU 4 (p ^ f) K)), (∀ y ∈ M, α y = y) ∧
        Blueprint.LieModel ↥M .PSp 2 p f := by
  classical
  have : Finite K := h.finite
  have h2K : (2 : K) ≠ 0 := two_ne_zero_of_odd h hp2
  have h4 : (4 : K) ≠ 0 := by
    have : (4 : K) = 2 * 2 := by norm_num
    rw [this]
    exact mul_ne_zero h2K h2K
  have hRR : (R : Matrix (Fin 4) (Fin 4) K) * (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hRR' : (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) * (R : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  obtain ⟨A, ψ, hAu, hψ, hcase⟩ := exists_steinberg_U4 h hp2 hq α hα2
  have key : ∀ g : unitarySU p f K 4, α (QuotientGroup.mk g) = QuotientGroup.mk g →
      ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).trace = 4 →
      ((ψ g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).trace = 4 → ψ g = g :=
    fun g hg ht ht' => eq_of_mk_eq_of_trace h4 (by rw [hψ, hg]) ht' ht
  have hαψ : ∀ φ : unitarySU p f K 4 →* unitarySU p f K 4, (∀ g, φ g = ψ g) →
      ∀ β : MulAut (StatedProj (StatedSU 4 (p ^ f) K)),
        (∀ g, β (QuotientGroup.mk g) = QuotientGroup.mk (φ g)) → α = β := by
    intro φ hφ β hβ
    ext z
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective z
    rw [← hψ, hβ, hφ]
  have hgens := gens_mem (F := h.fixedField)
  obtain ⟨k1, k2, k3, k4⟩ := hgens
  obtain ⟨g1, g2, g3, g4⟩ := bdK_gens h
  rcases hcase with ⟨hψv, c, hc⟩ | ⟨hψv, hA⟩
  ·
    have htrψ : ∀ g, ((ψ g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).trace =
        ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).trace := fun g => by
      rw [hψv, trace_conj']
    have e : ∀ x ∈ bdGens, (A : Matrix (Fin 4) (Fin 4) K) *
        (((bdHomU h hR x : unitarySU p f K 4) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
          (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) =
        (((bdHomU h hR x : unitarySU p f K 4) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) :=
      fun x hx => by
        rw [← hψv, key _ (hfix x hx) (trace_bdHomU_gens h hR hx)
          (by rw [htrψ]; exact trace_bdHomU_gens h hR hx)]
    have c1 := comm_cP_of_fix R (e _ k1)
    have c2 := comm_cP_of_fix R (e _ k2)
    have c3 := comm_cP_of_fix R (e _ k3)
    have c4 := comm_cP_of_fix R (e _ k4)
    rw [cP_bdHomU, g1] at c1
    rw [cP_bdHomU, g2] at c2
    rw [cP_bdHomU, g3] at c3
    rw [cP_bdHomU, g4] at c4
    obtain ⟨A', hA'⟩ : ∃ M : Matrix (Fin 4) (Fin 4) K,
        M = (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) * A * R := ⟨_, rfl⟩
    rw [← hA'] at c1 c2 c3 c4
    have hA'd := eq_of_comm_bd c1 c2 c3 c4
    set x := A' 0 0 with hx
    set y := A' 2 2 with hy
    have hAeq : (A : Matrix (Fin 4) (Fin 4) K) = (R : Matrix (Fin 4) (Fin 4) K) * A' *
        (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) := by
      rw [hA']
      exact eq_conj_of_mul_eq_one R hRR
    have hA'2 : A' * A' = c • 1 := by
      rw [hA']
      calc (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) * A * R * ((↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) * A * R)
          = (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) * ((A : Matrix (Fin 4) (Fin 4) K) * A) * R := by
            simp only [Matrix.mul_assoc]
            rw [← Matrix.mul_assoc (R : Matrix (Fin 4) (Fin 4) K), hRR, Matrix.one_mul]
        _ = c • 1 := by rw [hc, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hRR']
    rw [hA'd, bd_mul] at hA'2
    have ex := congrFun (congrFun hA'2 0) 0
    have ey := congrFun (congrFun hA'2 2) 2
    simp [bd] at ex ey
    have hxy : (y - x) * (y + x) = 0 := by linear_combination ey - ex
    have hx0 : x ≠ 0 := by
      intro h0
      have := congrArg Matrix.det hAeq
      rw [det_mul, det_mul, hA'd, det_bd, h0] at this
      simp at this
      exact (GeneralLinearGroup.det A).ne_zero
        (by rw [GeneralLinearGroup.val_det_apply]; exact this)
    have hψA : ∀ g : unitarySU p f K 4, ((ψ g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
        (A : Matrix (Fin 4) (Fin 4) K) =
        (A : Matrix (Fin 4) (Fin 4) K) * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
      intro g
      have hAi : (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K) = 1 := by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
      rw [hψv, Matrix.mul_assoc _ (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K), hAi, Matrix.mul_one]
    rcases mul_eq_zero.1 hxy with hh | hh
    · left
      have hyx : y = x := sub_eq_zero.1 hh
      have hAs : (A : Matrix (Fin 4) (Fin 4) K) = x • 1 := by
        rw [hAeq, hA'd, hyx]
        have hb : bd (x • (1 : Matrix (Fin 2) (Fin 2) K)) (x • 1) =
            x • (1 : Matrix (Fin 4) (Fin 4) K) := by
          ext i j
          fin_cases i <;> fin_cases j <;> simp [bd]
        rw [hb, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hRR]
      refine hαψ (MonoidHom.id _) (fun g => ?_) 1 (fun g => rfl)
      apply ext_val
      have := hψA g
      rw [hAs, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul] at this
      exact (smul_right_injective _ hx0 this).symm
    · right; left
      have hyx : y = -x := by linear_combination hh
      have hXv : ((X : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
          (R : Matrix (Fin 4) (Fin 4) K) * X1 (1 : K) * (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) := by
        rw [← hXR, Matrix.mul_assoc, hRR, Matrix.mul_one]
      have hAs : (A : Matrix (Fin 4) (Fin 4) K) =
          x • ((X : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
        rw [hAeq, hA'd, hyx, hXv]
        have hb : bd (x • (1 : Matrix (Fin 2) (Fin 2) K)) ((-x) • 1) = x • X1 (1 : K) := by
          ext i j
          fin_cases i <;> fin_cases j <;> simp [bd, X1]
        rw [hb, Matrix.mul_smul, Matrix.smul_mul]
      refine hαψ (MulAut.conj X).toMonoidHom (fun g => ?_) (MulAut.conj (QuotientGroup.mk X))
        (fun g => ?_)
      · apply ext_val
        have e1 := hψA g
        rw [hAs, Matrix.mul_smul, Matrix.smul_mul] at e1
        have e2 := smul_right_injective _ hx0 e1
        rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
          Subgroup.coe_inv, Units.val_mul, Units.val_mul]
        rw [← e2, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
          Matrix.mul_one]
      · rw [MulAut.conj_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, QuotientGroup.mk_mul,
          QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  ·
    right; right
    have htrψ : ∀ g, ((ψ g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).trace =
        h.bar ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).trace := fun g => by
      rw [hψv, trace_conj', trace_map_bar]
    have h4' : h.bar 4 = 4 := map_ofNat h.bar 4
    have e : ∀ x ∈ bdGens, (A : Matrix (Fin 4) (Fin 4) K) *
        (((bdHomU h hR x : unitarySU p f K 4) : GL (Fin 4) K) :
          Matrix (Fin 4) (Fin 4) K).map h.bar * (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) =
        (((bdHomU h hR x : unitarySU p f K 4) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) :=
      fun x hx => by
        rw [← hψv, key _ (hfix x hx) (trace_bdHomU_gens h hR hx)
          (by rw [htrψ, trace_bdHomU_gens h hR hx, h4'])]
    have c1 := comm_cP_of_fix_bar h R (e _ k1)
    have c2 := comm_cP_of_fix_bar h R (e _ k2)
    have c3 := comm_cP_of_fix_bar h R (e _ k3)
    have c4 := comm_cP_of_fix_bar h R (e _ k4)
    rw [cP_bdHomU, g1, map_bar_bd_gens h _ (Or.inl rfl)] at c1
    rw [cP_bdHomU, g2, map_bar_bd_gens h _ (Or.inr (Or.inl rfl))] at c2
    rw [cP_bdHomU, g3, map_bar_bd_gens h _ (Or.inr (Or.inr (Or.inl rfl)))] at c3
    rw [cP_bdHomU, g4, map_bar_bd_gens h _ (Or.inr (Or.inr (Or.inr rfl)))] at c4
    obtain ⟨A', hA'⟩ : ∃ M : Matrix (Fin 4) (Fin 4) K,
        M = (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) * A * (R : Matrix (Fin 4) (Fin 4) K).map h.bar :=
      ⟨_, rfl⟩
    rw [← hA'] at c1 c2 c3 c4
    have hA'd := eq_of_comm_bd c1 c2 c3 c4
    have hAeq : (A : Matrix (Fin 4) (Fin 4) K) = (R : Matrix (Fin 4) (Fin 4) K) * A' *
        (t⁻¹ • (bJ 1 1 * (R : Matrix (Fin 4) (Fin 4) K)ᵀ)) := by
      rw [hA']
      exact eq_conj_of_mul_eq_one R (map_bar_mul_eq_one h ht0 hR)
    set x := A' 0 0 with hx
    set y := A' 2 2 with hy
    have hAt : (A : Matrix (Fin 4) (Fin 4) K)ᵀ = -(A : Matrix (Fin 4) (Fin 4) K) := by
      have e1 : (A : Matrix (Fin 4) (Fin 4) K) = t⁻¹ • ((R : Matrix (Fin 4) (Fin 4) K) *
          bJ x y * (R : Matrix (Fin 4) (Fin 4) K)ᵀ) := by
        rw [hAeq, hA'd, Matrix.mul_smul, ← bd_smul_mul_bJ x y]
        simp only [Matrix.mul_assoc]
      rw [e1, Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_mul,
        Matrix.transpose_transpose, TBlocks.transpose_bJ, Matrix.neg_mul, Matrix.mul_neg,
        ← Matrix.mul_assoc, smul_neg]
    rcases hA with ⟨hAA, -⟩ | ⟨-, hAs⟩
    · exact exists_psp_of_alt_U4 h hp2 hq hAu hAA ψ hψv hψ
    · exfalso
      rw [hAs] at hAt
      have h0 : (A : Matrix (Fin 4) (Fin 4) K) = 0 := by
        have : (2 : K) • (A : Matrix (Fin 4) (Fin 4) K) = 0 := by
          rw [two_smul]
          nth_rewrite 1 [hAt]
          rw [neg_add_cancel]
        exact (smul_eq_zero.1 this).resolve_left h2K
      have := (GeneralLinearGroup.det A).ne_zero
      rw [GeneralLinearGroup.val_det_apply, h0, Matrix.det_zero] at this
      exact this rfl

end StabU

end CFSG.ComponentClassification.CatFactsL4U4
