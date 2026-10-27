module

public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.Algebra.Ring.Commute
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Data.Matrix.Basic
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KDRank3SmallL3
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KDRank3Defs
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.Open.StatedDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KDRank3SmallFU3

open Matrix CFSG.Open CFSG.Assembly.LowTwoRank

section Gen

variable {K : Type} [Field K]

@[expose] def qM (x : K) : Matrix (Fin 3) (Fin 3) K := !![1, 0, -1; 0, 1, 0; x, 0, x]

@[expose] def qI (y : K) : Matrix (Fin 3) (Fin 3) K := !![-1, 0, y; 0, 1, 0; 1, 0, y]

@[expose] def uM (a μ δ : K) : Matrix (Fin 3) (Fin 3) K :=
  !![1, a, a ^ 2 + μ * δ; 0, 1, -a; 0, 0, 1]

@[expose] def J0 : Matrix (Fin 3) (Fin 3) K := !![0, 0, 1; 0, 1, 0; 1, 0, 0]

lemma qM_mul_qI {x y : K} (h3 : (3 : K) = 0) (h : x * y = -1) : qM x * qI y = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [qM, qI, Matrix.mul_apply, Fin.sum_univ_three] <;>
    first
      | ring1
      | linear_combination h
      | linear_combination h - h3
      | linear_combination 2 * h - h3
      | linear_combination -h3
      | linear_combination h3
      | linear_combination -h
      | linear_combination -h - h3

lemma qI_mul_qM {x y : K} (h3 : (3 : K) = 0) (h : x * y = -1) : qI y * qM x = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [qM, qI, Matrix.mul_apply, Fin.sum_univ_three] <;>
    first
      | ring1
      | linear_combination h
      | linear_combination h - h3
      | linear_combination 2 * h - h3
      | linear_combination -h3
      | linear_combination h3
      | linear_combination -h
      | linear_combination -h - h3

lemma qM_transpose_mul_qM {x y : K} (h3 : (3 : K) = 0) (h : x * y = -1) :
    (qM x)ᵀ * qM y = J0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [qM, J0, Matrix.mul_apply, Fin.sum_univ_three] <;>
    first
      | ring1
      | linear_combination h
      | linear_combination h - h3
      | linear_combination 2 * h - h3
      | linear_combination -h3
      | linear_combination h3
      | linear_combination -h
      | linear_combination -h - h3

lemma uM_mul (h3 : (3 : K) = 0) (a μ δ a' μ' : K) :
    uM a μ δ * uM a' μ' δ = uM (a + a') (μ + μ') δ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uM, Matrix.mul_apply, Fin.sum_univ_three] <;>
    first | ring1 | linear_combination (-(a * a')) * h3

lemma uM_transpose_J0_mul (h3 : (3 : K) = 0) (a μ δ : K) :
    (uM a μ (-δ))ᵀ * J0 * uM a μ δ = J0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uM, J0, Matrix.mul_apply, Fin.sum_univ_three] <;>
    first | ring1 | linear_combination (a ^ 2) * h3

lemma qM_map (σ : K →+* K) (x : K) : (qM x).map σ = qM (σ x) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [qM]

lemma qI_map (σ : K →+* K) (y : K) : (qI y).map σ = qI (σ y) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [qI]

lemma uM_map (σ : K →+* K) (a μ δ : K) :
    (uM a μ δ).map σ = uM (σ a) (σ μ) (σ δ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uM]

@[expose] def gM (β β' a μ δ : K) : Matrix (Fin 3) (Fin 3) K := qM β * uM a μ δ * qI β'

lemma gM_mul (h3 : (3 : K) = 0) {β β' : K} (hβ : β * β' = -1) (a μ δ a' μ' : K) :
    gM β β' a μ δ * gM β β' a' μ' δ = gM β β' (a + a') (μ + μ') δ := by
  have hQ : qI β' * qM β = 1 := qI_mul_qM h3 hβ
  have hQ' : qM β * qI β' = 1 := qM_mul_qI h3 hβ
  unfold gM
  calc qM β * uM a μ δ * qI β' * (qM β * uM a' μ' δ * qI β')
      = qM β * uM a μ δ * (qI β' * qM β) * uM a' μ' δ * qI β' := by
        simp only [Matrix.mul_assoc]
    _ = qM β * (uM a μ δ * uM a' μ' δ) * qI β' := by
        rw [hQ]; simp only [Matrix.mul_assoc, Matrix.mul_one]
    _ = _ := by rw [uM_mul h3]

lemma gM_one (h3 : (3 : K) = 0) {β β' : K} (hβ : β * β' = -1) (δ : K) :
    gM β β' 0 0 δ = 1 := by
  have hQ' : qM β * qI β' = 1 := qM_mul_qI h3 hβ
  unfold gM
  have hU : uM 0 0 δ = 1 := by ext i j; fin_cases i <;> fin_cases j <;> simp [uM]
  rw [hU, Matrix.mul_one, hQ']

lemma gM_inv (h3 : (3 : K) = 0) {β β' : K} (hβ : β * β' = -1) (a μ δ : K) :
    gM β β' (-a) (-μ) δ * gM β β' a μ δ = 1 := by
  rw [gM_mul h3 hβ]
  simp only [neg_add_cancel]
  exact gM_one h3 hβ δ

lemma gM_map (σ : K →+* K) {β β' a μ δ : K} (hσβ : σ β = β') (ha : σ a = a) (hμ : σ μ = μ)
    (hδ : σ δ = -δ) (hσβ' : σ β' = β) :
    (gM β β' a μ δ).map σ = gM β' β a μ (-δ) := by
  unfold gM
  rw [Matrix.map_mul, Matrix.map_mul, qM_map, uM_map, qI_map, hσβ, hσβ', ha, hμ, hδ]

lemma gM_gram (σ : K →+* K) (h3 : (3 : K) = 0) {β β' a μ δ : K} (hβ : β * β' = -1)
    (hσβ : σ β = β') (hσβ' : σ β' = β) (ha : σ a = a) (hμ : σ μ = μ) (hδ : σ δ = -δ) :
    ((gM β β' a μ δ).map σ)ᵀ * gM β β' a μ δ = 1 := by
  rw [gM_map σ hσβ ha hμ hδ hσβ']
  have hβ' : β' * β = -1 := by rw [mul_comm]; exact hβ
  have A1 : (qM β')ᵀ * qM β = J0 := qM_transpose_mul_qM h3 hβ'
  have A2 := uM_transpose_J0_mul h3 a μ δ
  have A3 : qM β' * qI β = 1 := qM_mul_qI h3 hβ'
  have A4 : qM β * qI β' = 1 := qM_mul_qI h3 hβ
  unfold gM
  rw [Matrix.transpose_mul, Matrix.transpose_mul]
  calc (qI β)ᵀ * ((uM a μ (-δ))ᵀ * (qM β')ᵀ) * (qM β * uM a μ δ * qI β')
      = (qI β)ᵀ * ((uM a μ (-δ))ᵀ * ((qM β')ᵀ * qM β) * uM a μ δ) * qI β' := by
        simp only [Matrix.mul_assoc]
    _ = (qI β)ᵀ * ((uM a μ (-δ))ᵀ * J0 * uM a μ δ) * qI β' := by rw [A1]
    _ = (qI β)ᵀ * J0 * qI β' := by rw [A2]
    _ = (qI β)ᵀ * ((qM β')ᵀ * qM β) * qI β' := by rw [A1]
    _ = (qM β' * qI β)ᵀ * (qM β * qI β') := by
        rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
    _ = 1 := by rw [A3, A4, Matrix.transpose_one, Matrix.one_mul]

lemma uM_det (a μ δ : K) : (uM a μ δ).det = 1 := by
  simp [uM, Matrix.det_fin_three]

lemma gM_det (h3 : (3 : K) = 0) {β β' : K} (hβ : β * β' = -1) (a μ δ : K) :
    (gM β β' a μ δ).det = 1 := by
  have hQ' : qM β * qI β' = 1 := qM_mul_qI h3 hβ
  unfold gM
  rw [Matrix.det_mul, Matrix.det_mul, uM_det, mul_one, ← Matrix.det_mul, hQ', Matrix.det_one]

end Gen

abbrev GF729 := GaloisField 3 (2 * 3)
abbrev GF27 := GaloisField 3 3

lemma h3GF729 : (3 : GF729) = 0 := by exact_mod_cast CharP.cast_eq_zero GF729 3

lemma card_GF729 : Nat.card GF729 = 3 ^ 6 := by
  rw [GaloisField.card 3 (2 * 3) (by norm_num)]

lemma card_GF27 : Nat.card GF27 = 27 := by
  rw [GaloisField.card 3 3 (by norm_num)]; norm_num

noncomputable def embGF27 : GF27 →+* GF729 :=
  (FiniteField.nonempty_algHom_of_finrank_dvd (F := ZMod 3) (K := GF27) (L := GF729) (by
    rw [GaloisField.finrank 3 (by norm_num), GaloisField.finrank 3 (by norm_num)]
    norm_num)).some.toRingHom

lemma embGF27_injective : Function.Injective embGF27 := embGF27.injective

lemma pow_GF27 (y : GF27) : y ^ (3 ^ 3) = y := by
  haveI := Fintype.ofFinite GF27
  have hc : Fintype.card GF27 = 3 ^ 3 := by
    rw [← Nat.card_eq_fintype_card, card_GF27]; norm_num
  have := FiniteField.pow_card y
  rw [hc] at this
  exact this

lemma pow_GF729 (x : GF729) : x ^ 729 = x := by
  haveI := Fintype.ofFinite GF729
  have hc : Fintype.card GF729 = 729 := by
    rw [← Nat.card_eq_fintype_card, card_GF729]; norm_num
  have := FiniteField.pow_card x
  rw [hc] at this
  exact this

noncomputable def frob27 : GF729 →+* GF729 := iterateFrobenius GF729 3 3

lemma frob27_apply (x : GF729) : frob27 x = x ^ (3 ^ 3) := by
  unfold frob27; rw [iterateFrobenius_def]

lemma frob27_frob27 (x : GF729) : frob27 (frob27 x) = x := by
  rw [frob27_apply, frob27_apply, ← pow_mul]
  norm_num
  exact pow_GF729 x

lemma frob27_emb (y : GF27) : frob27 (embGF27 y) = embGF27 y := by
  rw [frob27_apply, ← map_pow, pow_GF27]

lemma exists_beta_delta : ∃ β δ : GF729, β * frob27 β = -1 ∧ δ ≠ 0 ∧ frob27 δ = -δ := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := GF729ˣ)
  have hord : orderOf g = 728 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, card_GF729]
    norm_num
  have h728 : (g : GF729) ^ 728 = 1 := by
    have h := pow_orderOf_eq_one g
    rw [hord] at h
    have := congrArg Units.val h
    simpa using this
  have h364 : (g : GF729) ^ 364 = -1 := by
    have hne : (g : GF729) ^ 364 ≠ 1 := by
      intro h
      have h' : g ^ 364 = 1 := Units.ext (by simpa using h)
      have hd := orderOf_dvd_iff_pow_eq_one.2 h'
      rw [hord] at hd
      norm_num at hd
    have hsq : ((g : GF729) ^ 364) * ((g : GF729) ^ 364) = 1 := by
      rw [← pow_add]; exact h728
    rcases mul_self_eq_one_iff.1 hsq with h | h
    · exact absurd h hne
    · exact h
  refine ⟨(g : GF729) ^ 13, (g : GF729) ^ 14, ?_, ?_, ?_⟩
  · rw [frob27_apply, ← pow_mul, ← pow_add]
    norm_num
    exact h364
  · exact pow_ne_zero _ g.ne_zero
  · rw [frob27_apply, ← pow_mul]
    norm_num
    have : (g : GF729) ^ 378 = (g : GF729) ^ 364 * (g : GF729) ^ 14 := by rw [← pow_add]
    rw [this, h364]
    ring

section Hom

lemma h3GF27 : (3 : GF27) = 0 := by exact_mod_cast CharP.cast_eq_zero GF27 3

noncomputable def gUnit (β δ : GF729) (hβ : β * frob27 β = -1) (a μ : GF729) :
    (Matrix (Fin 3) (Fin 3) GF729)ˣ where
  val := gM β (frob27 β) a μ δ
  inv := gM β (frob27 β) (-a) (-μ) δ
  val_inv := by
    rw [gM_mul h3GF729 hβ, add_neg_cancel, add_neg_cancel]
    exact gM_one h3GF729 hβ δ
  inv_val := gM_inv h3GF729 hβ a μ δ

lemma gUnit_mem (β δ : GF729) (hβ : β * frob27 β = -1) (hδ : frob27 δ = -δ) (a μ : GF729)
    (ha : frob27 a = a) (hμ : frob27 μ = μ) :
    gUnit β δ hβ a μ ∈ StatedSU 3 (3 ^ 3) GF729 := by
  apply Subgroup.subset_closure
  refine ⟨gM_det h3GF729 hβ a μ δ, ?_⟩
  exact gM_gram frob27 h3GF729 hβ rfl (frob27_frob27 β) ha hμ hδ

noncomputable def gHom (β δ : GF729) (hβ : β * frob27 β = -1) :
    Multiplicative (GF27 × GF27) →* (Matrix (Fin 3) (Fin 3) GF729)ˣ where
  toFun x :=
    gUnit β δ hβ (embGF27 (Multiplicative.toAdd x).1) (embGF27 (Multiplicative.toAdd x).2)
  map_one' := by
    apply Units.ext
    simp only [gUnit, map_zero, Prod.fst_zero, Prod.snd_zero, toAdd_one]
    exact gM_one h3GF729 hβ δ
  map_mul' x y := by
    apply Units.ext
    simp only [gUnit, toAdd_mul, Prod.fst_add, Prod.snd_add, map_add]
    exact (gM_mul h3GF729 hβ _ _ _ _ _).symm

end Hom

section Psi

lemma gHom_mem (β δ : GF729) (hβ : β * frob27 β = -1) (hδ : frob27 δ = -δ)
    (x : Multiplicative (GF27 × GF27)) : gHom β δ hβ x ∈ StatedSU 3 (3 ^ 3) GF729 :=
  gUnit_mem β δ hβ hδ _ _ (frob27_emb _) (frob27_emb _)

noncomputable def psiHom (β δ : GF729) (hβ : β * frob27 β = -1) (hδ : frob27 δ = -δ) :
    Multiplicative (GF27 × GF27) →* StatedProj (StatedSU 3 (3 ^ 3) GF729) :=
  (QuotientGroup.mk'
    ((StatedScalars (Fin 3) GF729).subgroupOf (StatedSU 3 (3 ^ 3) GF729))).comp
    ((gHom β δ hβ).codRestrict (StatedSU 3 (3 ^ 3) GF729) (gHom_mem β δ hβ hδ))

lemma uM_eq_of_gM_scalar (β δ : GF729) (hβ : β * frob27 β = -1) (a μ c : GF729)
    (h : gM β (frob27 β) a μ δ = c • (1 : Matrix (Fin 3) (Fin 3) GF729)) :
    uM a μ δ = c • (1 : Matrix (Fin 3) (Fin 3) GF729) := by
  have hQ : qI (frob27 β) * qM β = 1 := qI_mul_qM h3GF729 hβ
  have key : uM a μ δ = qI (frob27 β) * gM β (frob27 β) a μ δ * qM β := by
    unfold gM
    calc uM a μ δ = (qI (frob27 β) * qM β) * uM a μ δ * (qI (frob27 β) * qM β) := by
          rw [hQ, Matrix.one_mul, Matrix.mul_one]
      _ = qI (frob27 β) * (qM β * uM a μ δ * qI (frob27 β)) * qM β := by
          simp only [Matrix.mul_assoc]
  rw [key, h, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hQ]

lemma psiHom_injective (β δ : GF729) (hβ : β * frob27 β = -1) (hδ : frob27 δ = -δ)
    (hδ0 : δ ≠ 0) : Function.Injective (psiHom β δ hβ hδ) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  simp only [psiHom, MonoidHom.comp_apply, MonoidHom.codRestrict_apply,
    QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hx
  obtain ⟨c, hc⟩ := hx
  have hv : gM β (frob27 β) (embGF27 (Multiplicative.toAdd x).1)
      (embGF27 (Multiplicative.toAdd x).2) δ =
      (c : GF729) • (1 : Matrix (Fin 3) (Fin 3) GF729) := by
    have := congrArg Units.val hc
    simp [gHom, gUnit, Matrix.GeneralLinearGroup.scalar] at this
    rw [← this]
    ext i j
    by_cases h : i = j <;> simp [Matrix.diagonal_apply, Matrix.smul_apply, h]
  have hU := uM_eq_of_gM_scalar β δ hβ _ _ _ hv
  have h01 := congrFun (congrFun hU 0) 1
  have h02 := congrFun (congrFun hU 0) 2
  simp only [uM, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul, Fin.isValue] at h01 h02
  have ha : embGF27 (Multiplicative.toAdd x).1 = 0 := by simpa using h01
  have hμ : embGF27 (Multiplicative.toAdd x).2 * δ = 0 := by
    rw [ha] at h02
    simpa using h02
  have hz : embGF27 (Multiplicative.toAdd x).2 = 0 := (mul_eq_zero.1 hμ).resolve_right hδ0
  have hy' := (map_eq_zero_iff embGF27 embGF27_injective).1 ha
  have hz' := (map_eq_zero_iff embGF27 embGF27_injective).1 hz
  exact toAdd_eq_zero.1 (Prod.ext hy' hz')

end Psi

section Final

lemma exists_psi_six (β δ : GF729) (hβ : β * frob27 β = -1) (hδ0 : δ ≠ 0) (hδ : frob27 δ = -δ) :
    ∃ P : Subgroup (StatedProj (StatedSU 3 (3 ^ 3) GF729)),
      IsElemAbelian 3 P ∧ Nat.card P = 3 ^ 6 := by
  refine ⟨(psiHom β δ hβ hδ).range, ?_, ?_⟩
  · apply CFSG.LocalAnalysis.GLTheoremA.KDRank3SmallL3.isElemAbelian_three_range
    intro a
    apply Multiplicative.toAdd.injective
    ext
    · simp [toAdd_pow, h3GF27]
    · simp [toAdd_pow, h3GF27]
  · rw [CFSG.LocalAnalysis.GLTheoremA.KDRank3SmallL3.card_range_eq _
      (psiHom_injective β δ hβ hδ hδ0),
      (Nat.card_congr (Multiplicative.ofAdd : GF27 × GF27 ≃ Multiplicative (GF27 × GF27))).symm,
      Nat.card_prod, card_GF27]
    norm_num

lemma exists_six_of_param {S : Type} [Group S] (c fe : ℕ) [Fact c.Prime] (hc : c = 3)
    (hfe : fe = 3) (E : S ≃* StatedProj (StatedSU 3 (c ^ fe) (GaloisField c (2 * fe)))) :
    ∃ P : Subgroup S, IsElemAbelian 3 P ∧ Nat.card P = 3 ^ 6 := by
  subst hc hfe
  obtain ⟨β, δ, hβ, hδ0, hδ⟩ := exists_beta_delta
  obtain ⟨P, hP, hcard⟩ := exists_psi_six β δ hβ hδ0 hδ
  refine ⟨P.map E.symm.toMonoidHom, CFSG.SectionRank.isElemAbelian_map hP _, ?_⟩
  rw [Subgroup.card_map_of_injective E.symm.injective, hcard]

end Final

open TauCeti in
theorem exists_six_of_twistedA2 {S : Type} [Group S] (q : PrimePower)
    (hv : (LieTypeIndex.twistedA 2 q).Valid) (hq : q.card = 27)
    (e : S ≃* (ValidLieTypeIndex.Group ⟨LieTypeIndex.twistedA 2 q, hv⟩)) :
    ∃ P : Subgroup S, IsElemAbelian 3 P ∧ Nat.card P = 3 ^ 6 := by
  have hpow : q.p ^ q.exponent = 3 ^ 3 := by
    rw [← PrimePower.card_def, hq]; norm_num
  have hp3 : q.p = 3 :=
    CFSG.LocalAnalysis.GLTheoremA.KDRank3SmallL3.prime_eq_three_of_card_eq_27 q hq
  have hf3 : q.exponent = 3 := by
    rw [hp3] at hpow
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) hpow
  have hc : ValidLieTypeIndex.characteristic ⟨LieTypeIndex.twistedA 2 q, hv⟩ = 3 := by
    simp [ValidLieTypeIndex.characteristic, hp3]
  have hfe : ValidLieTypeIndex.fieldExponent ⟨LieTypeIndex.twistedA 2 q, hv⟩ = 3 := by
    simp [ValidLieTypeIndex.fieldExponent, hf3]
  exact exists_six_of_param _ _ hc hfe
    (e.trans (CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj 2 q hv))

end CFSG.LocalAnalysis.GLTheoremA.KDRank3SmallFU3
