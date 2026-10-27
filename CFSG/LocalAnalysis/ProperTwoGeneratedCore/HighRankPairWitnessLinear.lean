module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.HighRankPairStatements
import all CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldCentralizer
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldFull
public import CFSG.Walter.PSL2Facts.Even
public import CFSG.LinearAlgebra.LinearGroups.Generation

public noncomputable section

open scoped MatrixGroups

namespace CFSG.ProperTwoGeneratedCore.HighRankPair

open CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField

universe u v

section CharTwo

variable {K : Type v} [Field K] [CharP K 2]

theorem sl2_transvection_mul_self {i j : Fin 2} (hij : i ≠ j) (c : K) :
    Matrix.SpecialLinearGroup.transvection hij c *
      Matrix.SpecialLinearGroup.transvection hij c = 1 := by
  apply Subtype.ext
  change Matrix.transvection i j c * Matrix.transvection i j c = 1
  rw [Matrix.transvection_mul_transvection_same i j hij, CharTwo.add_self_eq_zero,
    Matrix.transvection_zero]

theorem sl2_closure_mul_self_eq_one :
    Subgroup.closure {x : SL(2, K) | x * x = 1} = ⊤ := by
  rw [eq_top_iff, ← CFSG.LinearGroups.special_linear_elementary_generation (n := 2) (K := K)]
  apply Subgroup.closure_mono
  rintro _ ⟨i, j, hij, c, rfl⟩
  exact sl2_transvection_mul_self hij c

omit [CharP K 2] in
theorem sl2_diag_eq_of_mul_self {g : SL(2, K)} (hg2 : g * g = 1) : g 0 0 = g 1 1 := by
  have hginv : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg2
  have h := congrArg (fun C : SL(2, K) => C 0 0) hginv
  simp only [Matrix.SpecialLinearGroup.SL2_inv_expl, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.empty_val', Matrix.cons_val_fin_one] at h
  exact h.symm

theorem sl2_det_one_add_smul {g : SL(2, K)} (hg2 : g * g = 1) (c : K) :
    (1 + c • ((g : Matrix (Fin 2) (Fin 2) K) + 1)).det = 1 := by
  have hdiag := sl2_diag_eq_of_mul_self hg2
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    have := g.2
    rwa [Matrix.det_fin_two] at this
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [Matrix.det_fin_two]
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul,
    Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)]
  rw [← hdiag] at hdet ⊢
  linear_combination c ^ 2 * hdet + (c * (g 0 0 + 1) + c ^ 2 * (g 0 0 + 1)) * h2


omit [CharP K 2] in
theorem sl2_root_commute (g : SL(2, K)) (c : K) :
    (g : Matrix (Fin 2) (Fin 2) K) * (1 + c • ((g : Matrix (Fin 2) (Fin 2) K) + 1)) =
      (1 + c • ((g : Matrix (Fin 2) (Fin 2) K) + 1)) * g := by
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul]

theorem sl2_centralizer_involution_eq_root {g : SL(2, K)} (hg1 : g ≠ 1) (hg2 : g * g = 1)
    (h : SL(2, K)) (hgh : g * h = h * g) :
    ∃ c : K, (h : Matrix (Fin 2) (Fin 2) K) = 1 + c • ((g : Matrix (Fin 2) (Fin 2) K) + 1) := by
  have hh2 : h * h = 1 := CFSG.Walter.sl2_mul_self_eq_one_of_commute hg1 hg2 hgh
  have hgd := sl2_diag_eq_of_mul_self hg2
  have hhd := sl2_diag_eq_of_mul_self hh2
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hdetg : g 0 0 * g 0 0 - g 0 1 * g 1 0 = 1 := by
    have := g.2
    rwa [Matrix.det_fin_two, ← hgd] at this
  have hdeth : h 0 0 * h 0 0 - h 0 1 * h 1 0 = 1 := by
    have := h.2
    rwa [Matrix.det_fin_two, ← hhd] at this
  have h00 : g 0 1 * h 1 0 = h 0 1 * g 1 0 := by
    have := congrArg (fun C : SL(2, K) => C 0 0) hgh
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two] at this
    linear_combination this
  have hoff : g 0 1 ≠ 0 ∨ g 1 0 ≠ 0 := by
    by_contra hz
    push Not at hz
    apply hg1
    have ha : g 0 0 = 1 := CharTwo.sq_injective (by
      simp only [one_pow]
      rw [hz.1, hz.2] at hdetg
      linear_combination hdetg)
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ha, ← hgd, hz.1, hz.2]
  obtain ⟨l, hlb, hlc⟩ : ∃ l : K, l * g 0 1 = h 0 1 ∧ l * g 1 0 = h 1 0 := by
    by_cases hb : g 0 1 = 0
    · have hc : g 1 0 ≠ 0 := hoff.resolve_left (not_not.mpr hb)
      have hy : h 0 1 = 0 := by
        rw [hb, zero_mul] at h00
        exact (mul_eq_zero.mp h00.symm).resolve_right hc
      exact ⟨h 1 0 / g 1 0, by rw [hb, hy, mul_zero], div_mul_cancel₀ _ hc⟩
    · refine ⟨h 0 1 / g 0 1, div_mul_cancel₀ _ hb, ?_⟩
      field_simp
      linear_combination -h00
  have hx : h 0 0 = 1 + l * (g 0 0 + 1) := by
    apply CharTwo.sq_injective
    simp only
    rw [← hlb, ← hlc] at hdeth
    linear_combination hdeth - l ^ 2 * hdetg - (l ^ 2 + l ^ 2 * g 0 0 + l * (g 0 0 + 1)) * h2
  refine ⟨l, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j
  · simp [hx, mul_add]
  · simpa using hlb.symm
  · simpa using hlc.symm
  · simp [← hhd, ← hgd, hx, mul_add]

theorem sl2_card_centralizer_involution [Finite K] {g : SL(2, K)} (hg1 : g ≠ 1)
    (hg2 : g * g = 1) :
    Nat.card (Subgroup.centralizer ({g} : Set SL(2, K))) = Nat.card K := by
  let N : Matrix (Fin 2) (Fin 2) K := (g : Matrix (Fin 2) (Fin 2) K) + 1
  have hN : N ≠ 0 := by
    intro hN
    apply hg1
    apply Subtype.ext
    have : (g : Matrix (Fin 2) (Fin 2) K) = -1 := eq_neg_of_add_eq_zero_left hN
    rw [this, CharTwo.neg_eq]
    rfl
  let r : K → SL(2, K) := fun c => ⟨1 + c • N, sl2_det_one_add_smul hg2 c⟩
  have hr : ∀ c, r c ∈ Subgroup.centralizer ({g} : Set SL(2, K)) := fun c =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext (sl2_root_commute g c).symm)
  let f : K → Subgroup.centralizer ({g} : Set SL(2, K)) := fun c => ⟨r c, hr c⟩
  have hinj : Function.Injective f := by
    intro c d hcd
    have hm := congrArg (fun x : Subgroup.centralizer ({g} : Set SL(2, K)) =>
      ((x : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)) hcd
    simp only [f, r, add_right_inj] at hm
    exact smul_left_injective K hN hm
  have hsurj : Function.Surjective f := by
    rintro ⟨h, hh⟩
    obtain ⟨c, hc⟩ := sl2_centralizer_involution_eq_root hg1 hg2 h
      (Subgroup.mem_centralizer_singleton_iff.mp hh).symm
    exact ⟨c, Subtype.ext (Subtype.ext hc.symm)⟩
  exact (Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)).symm


end CharTwo

section Field

theorem frobenius_pow_apply {F : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F] (s : ℕ)
    (c : F) : (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) F ^ s) c = c ^ 2 ^ s := by
  rw [AlgEquiv.coe_pow]
  simpa using congrFun (FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate (ZMod 2) F s) c

theorem exists_pow_two_pow_ne_self {F : Type*} [Field F] {a : ℕ} (ha : 1 ≤ a)
    (hF : Nat.card F = 2 ^ (2 * a)) : ∃ c : F, c ^ 2 ^ a ≠ c := by
  have : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; positivity)
  have : CharP F 2 := char_two_of_card hF
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  by_contra hall
  push Not at hall
  have hgorder : orderOf (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) F) = 2 * a :=
    (FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic (ZMod 2) F).trans
      (binary_degree_of_card hF)
  have hga : FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) F ^ a = 1 := by
    ext c
    rw [frobenius_pow_apply]
    exact hall c
  exact pow_ne_one_of_lt_orderOf (by omega) (by omega) hga

theorem sl2_trace_conj {F : Type*} [Field F] (P M : SL(2, F)) :
    Matrix.trace ((P * M * P⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
      Matrix.trace (M : Matrix (Fin 2) (Fin 2) F) := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.trace_mul_comm,
    ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel_left]

theorem fieldInvolutionOn_nonInnerOn {G : Type*} [Group G] {L : Subgroup G} {v : G} {a : ℕ}
    (ha : 1 ≤ a) (hv : FieldInvolutionOn L v a) : NonInnerOn L v := by
  obtain ⟨F, _, hF, φ, hφ⟩ := hv
  rintro ⟨g, hgL, hg⟩
  have : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; positivity)
  have : CharP F 2 := char_two_of_card hF
  obtain ⟨c, hc⟩ := exists_pow_two_pow_ne_self ha hF
  apply hc
  let M : SL(2, F) := ⟨!![c, 1; 1, 0], by
    rw [Matrix.det_fin_two_of]
    simp [CharTwo.neg_eq]⟩
  let gL : L := ⟨g, hgL⟩
  let x : L := φ.symm M
  let y : L := gL * x * gL⁻¹
  have hxy : (y : G) = v * x * v⁻¹ := by
    rw [hg x x.2]
    rfl
  have hent := hφ x y hxy
  have hx : φ x = M := φ.apply_symm_apply M
  have hy : φ y = φ gL * M * (φ gL)⁻¹ := by
    simp only [y, map_mul, map_inv, hx]
  have htrace := sl2_trace_conj (φ gL) M
  rw [← hy, Matrix.trace_fin_two, Matrix.trace_fin_two, hent 0 0, hent 1 1, hx] at htrace
  have h0 : (0 : F) ^ 2 ^ a = 0 := zero_pow (by positivity)
  simpa [M, h0] using htrace


theorem subfieldCentralizer_of_fieldInvolution {G : Type*} [Group G] {L : Subgroup G}
    {f y t : G} {a : ℕ} (ha : 1 ≤ a) (hf : FieldInvolutionOn L f a)
    (hfL : f ∈ Subgroup.normalizer (L : Set G)) (hy : ∀ x ∈ L, y * x = x * y)
    (htL : t ∈ L) (hft : Commute f t) (ht : orderOf t = 2) :
    SubfieldCentralizer L (y * f * t) a := by
  obtain ⟨F, _, hF, φ, hφ⟩ := hf
  have : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; positivity)
  have : CharP F 2 := char_two_of_card hF
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let σ : RingAut F := (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) F ^ a).toRingEquiv
  have hσ : ∀ c : F, σ c = c ^ 2 ^ a := fun c => frobenius_pow_apply a c
  have hfconj : ∀ l : L, f * (l : G) * f⁻¹ ∈ L := fun l =>
    (Subgroup.mem_normalizer_iff.mp hfL l).mp l.2
  have hφf : ∀ l : L, φ ⟨f * l * f⁻¹, hfconj l⟩ = sl2FieldAction σ (φ l) := by
    intro l
    ext i j
    rw [hφ l ⟨_, hfconj l⟩ rfl i j, sl2FieldAction_apply,
      Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
    exact (hσ _).symm
  let tL : L := ⟨t, htL⟩
  let T : SL(2, F) := φ tL
  have hσT : sl2FieldAction σ T = T := by
    have h1 : (⟨f * t * f⁻¹, hfconj tL⟩ : L) = tL :=
      Subtype.ext (show f * t * f⁻¹ = t by rw [hft.eq, mul_inv_cancel_right])
    rw [← hφf tL, h1]
  have hσ1 : σ ≠ 1 := by
    obtain ⟨c, hc⟩ := exists_pow_two_pow_ne_self ha hF
    intro h1
    apply hc
    rw [← hσ, h1]
    rfl
  have hσσ : σ * σ = 1 := by
    let : Fintype F := Fintype.ofFinite F
    ext c
    change σ (σ c) = c
    rw [hσ, hσ, ← pow_mul, ← pow_add, ← two_mul]
    have hcard : Fintype.card F = 2 ^ (2 * a) := by rw [Fintype.card_eq_nat_card, hF]
    rw [← hcard]
    exact FiniteField.pow_card c
  have hTT : T * T = 1 := by
    rw [← map_mul]
    have htt : tL * tL = 1 := Subtype.ext (by
      change t * t = 1
      rw [← pow_two, ← ht, pow_orderOf_eq_one])
    rw [htt, map_one]
  let Γ : Gamma F := ⟨T, σ⟩
  have hΓ2 : Γ ^ 2 = 1 := by
    rw [pow_two]
    apply SemidirectProduct.ext
    · rw [SemidirectProduct.mul_left]
      change T * sl2FieldAction σ T = 1
      rw [hσT, hTT]
    · rw [SemidirectProduct.mul_right]
      exact hσσ
  have hΓ1 : Γ ≠ 1 := fun h => hσ1 (congrArg SemidirectProduct.right h)
  have hΓorder : orderOf Γ = 2 := orderOf_eq_prime hΓ2 hΓ1
  have hΓout : Γ ∉ linearKernel F := by
    rw [mem_linearKernel_iff]
    exact hσ1
  obtain ⟨s', _hs', hns, -, hfixed, x, -, hcent⟩ :=
    original_outer_involution_field_conjugacy_and_centralizer (n := 2 * a) (by omega) hF
      Γ hΓorder hΓout
  have hs'a : s' = a := by omega
  have hΓmem : ∀ h : SL(2, F), h ∈ centralizerS Γ ↔ T * sl2FieldAction σ h * T⁻¹ = h := by
    intro h
    rw [mem_centralizerS_iff, SemidirectProduct.ext_iff, SemidirectProduct.mul_left,
      SemidirectProduct.mul_left, SemidirectProduct.mul_right, SemidirectProduct.mul_right]
    simp only [SemidirectProduct.left_inl, SemidirectProduct.right_inl, map_one, one_mul,
      mul_one, and_true, MulAut.one_apply]
    change h * T = T * sl2FieldAction σ h ↔ _
    constructor
    · intro hh
      rw [← hh, mul_inv_cancel_right]
    · intro hh
      calc h * T = T * sl2FieldAction σ h * T⁻¹ * T := by rw [hh]
        _ = T * sl2FieldAction σ h := inv_mul_cancel_right _ _
  have hmem : ∀ l : L, (l : G) ∈ Subgroup.centralizer ({y * f * t} : Set G) ↔
      φ l ∈ centralizerS Γ := by
    intro l
    have htl : t * (l : G) * t⁻¹ ∈ L :=
      L.mul_mem (L.mul_mem htL l.2) (L.inv_mem htL)
    let l₁ : L := ⟨t * l * t⁻¹, htl⟩
    have hl₁ : l₁ = tL * l * tL⁻¹ := rfl
    have hm := hφf l₁
    have hmL : f * (l₁ : G) * f⁻¹ ∈ L := hfconj l₁
    have hconj : (y * f * t) * (l : G) * (y * f * t)⁻¹ = f * (l₁ : G) * f⁻¹ := by
      have hyc := hy _ hmL
      calc (y * f * t) * (l : G) * (y * f * t)⁻¹
          = y * (f * (l₁ : G) * f⁻¹) * y⁻¹ := by
            simp only [l₁, mul_inv_rev]; group
        _ = f * (l₁ : G) * f⁻¹ := by rw [hyc, mul_inv_cancel_right]
    rw [Subgroup.mem_centralizer_singleton_iff, hΓmem]
    have hφl₁ : φ l₁ = T * φ l * T⁻¹ := by rw [hl₁, map_mul, map_mul, map_inv]
    rw [hφl₁, map_mul, map_mul, map_inv, hσT] at hm
    rw [← hm]
    constructor
    · intro hc
      congr 1
      apply Subtype.ext
      change f * (l₁ : G) * f⁻¹ = l
      rw [← hconj, ← hc, mul_inv_cancel_right]
    · intro hc
      have hc' : (⟨f * (l₁ : G) * f⁻¹, hmL⟩ : L) = l := φ.injective hc
      have hc'' : f * (l₁ : G) * f⁻¹ = l := congrArg Subtype.val hc'
      rw [← hconj] at hc''
      exact (mul_inv_eq_iff_eq_mul.mp hc'').symm
  let M := L ⊓ Subgroup.centralizer ({y * f * t} : Set G)
  let e₁ : M →* centralizerS Γ :=
    { toFun := fun m => ⟨φ ⟨m, m.2.1⟩, (hmem ⟨m, m.2.1⟩).mp m.2.2⟩
      map_one' := Subtype.ext (map_one φ)
      map_mul' := fun m n => Subtype.ext (map_mul φ ⟨m, m.2.1⟩ ⟨n, n.2.1⟩) }
  have he₁ : Function.Bijective e₁ := by
    constructor
    · intro m n hmn
      have h1 := φ.injective (congrArg Subtype.val hmn)
      exact Subtype.ext (congrArg (fun l : L => (l : G)) h1)
    · rintro ⟨h, hh⟩
      have hl := (hmem (φ.symm h)).mpr (by rw [φ.apply_symm_apply]; exact hh)
      refine ⟨⟨φ.symm h, (φ.symm h).2, hl⟩, Subtype.ext ?_⟩
      change φ ⟨(φ.symm h : G), (φ.symm h).2⟩ = h
      exact φ.apply_symm_apply h
  have hcent' : centralizerS Γ = (fixedSL2 σ).map (MulAut.conj x).toMonoidHom := hcent
  let e₂ : centralizerS Γ ≃* fixedSL2 σ :=
    (MulEquiv.subgroupCongr hcent').trans ((fixedSL2 σ).equivMapOfInjective _
      (MulAut.conj x).injective).symm
  let e₃ : fixedSL2 σ ≃* SL(2, fixedField σ) :=
    (MonoidHom.ofInjective (sl2_map_injective (fixedField σ).subtype)).symm
  refine ⟨fixedField σ, inferInstance, ?_, ⟨(MulEquiv.ofBijective e₁ he₁).trans (e₂.trans e₃)⟩⟩
  rw [← hs'a]
  exact hfixed

end Field

end CFSG.ProperTwoGeneratedCore.HighRankPair
