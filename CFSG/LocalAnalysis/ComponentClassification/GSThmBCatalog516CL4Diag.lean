module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog516CL4Tools
public import CFSG.LieType.Steinberg.CentralExt.Model
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorAut
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorBasic

public section

namespace CFSG.ComponentClassification.GSThmB.Cent516

open CFSG Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.CatFactsL4U4 InvClassL TBlocks HBlocks
open CFSG.ComponentClassification.OddSelector (conjAut_mem_inner_iff)

variable {Y : Type} [Group Y] {K : Type} [Field K] {p f : ℕ}

@[expose] def t2GL : GL (Fin 4) K :=
  ⟨X1 1, X1 1, by ext i j; fin_cases i <;> fin_cases j <;> simp [X1, Matrix.mul_apply,
    Fin.sum_univ_four], by ext i j; fin_cases i <;> fin_cases j <;> simp [X1, Matrix.mul_apply,
    Fin.sum_univ_four]⟩

@[expose] def t1GL : GL (Fin 4) K := ⟨dOne, dOne, dOne_mul_dOne, dOne_mul_dOne⟩

@[expose] noncomputable def nGL (c : K) (hc : c ≠ 0) : GL (Fin 4) K :=
  ⟨stdN c, c⁻¹ • stdN c, by rw [Matrix.mul_smul, stdN_mul_stdN, smul_smul,
    inv_mul_cancel₀ hc, one_smul], by rw [Matrix.smul_mul, stdN_mul_stdN, smul_smul,
    inv_mul_cancel₀ hc, one_smul]⟩

theorem det_t1GL : ((t1GL : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det = -1 := by
  change (dOne : Matrix (Fin 4) (Fin 4) K).det = -1
  rw [dOne, det_diagonal, Fin.prod_univ_four]
  norm_num

@[expose] noncomputable def frameHom {G : Type*} [Group G] (e : Y ⧸ center Y ≃* projectiveSL 4 K)
    (P : GL (Fin 4) K) (φ : G →* SpecialLinearGroup (Fin 4) K) : G →* Y ⧸ center Y :=
  e.symm.toMonoidHom.comp ((conjAut 4 K P).toMonoidHom.comp ((proj 4 K).comp φ))

theorem frameHom_apply {G : Type*} [Group G] (e : Y ⧸ center Y ≃* projectiveSL 4 K)
    (P : GL (Fin 4) K) (φ : G →* SpecialLinearGroup (Fin 4) K) (g : G) :
    frameHom e P φ g = (((conjAut 4 K P).trans e.symm) (proj 4 K (φ g))) := rfl

theorem frameHom_fixed {G : Type*} [Group G] (e : Y ⧸ center Y ≃* projectiveSL 4 K)
    (α : MulAut Y) {A P D : GL (Fin 4) K} {μ : Kˣ}
    (hα' : MulAut.congr e (barAut α) = conjAut 4 K A)
    (hAP : A * P = GeneralLinearGroup.scalar (Fin 4) μ * (P * D))
    (φ : G →* SpecialLinearGroup (Fin 4) K)
    (hφ : ∀ g, ((φ g : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
      (D : Matrix (Fin 4) (Fin 4) K) = (D : Matrix (Fin 4) (Fin 4) K) * (φ g)) :
    ∀ g, barAut α (frameHom e P φ g) = frameHom e P φ g := fun g =>
  barAut_symm_fixed e α hα' (fixed_of_frame hAP (φ g) (hφ g))

theorem range_perfect {G H : Type*} [Group G] [Group H] [Group.IsPerfect G] (ρ : G →* H) :
    ⁅ρ.range, ρ.range⁆ = ρ.range := by
  rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← commutator_def,
    Group.IsPerfect.commutator_eq_top]

theorem z4z2_of_iso {L₁ L₂ : Type*} [Group L₁] [Group L₂] [Finite L₂] (τ : L₁ ≃* L₂)
    {G : Type*} [Group G] (ρ : G →* L₂) {x w : L₁} {gx gw : G} (hx : ρ gx = τ x)
    (hw : ρ gw = τ w) (hx4 : orderOf x = 4) (hw2 : orderOf w = 2) (hxw : Commute x w)
    (hne : w ≠ x ^ 2) :
    ∃ B : Subgroup L₂, B ≤ ρ.range ∧ (∀ u ∈ B, ∀ v ∈ B, u * v = v * u) ∧ Nat.card B = 8 ∧
      ∃ u ∈ B, ∃ v ∈ B, u ≠ v ∧ orderOf u = 2 ∧ orderOf v = 2 :=
  exists_z4z2 ⟨gx, hx⟩ ⟨gw, hw⟩ (by rw [MulEquiv.orderOf_eq]; exact hx4)
    (by rw [MulEquiv.orderOf_eq]; exact hw2) (hxw.map τ)
    (fun h => hne (τ.injective (by rw [h, map_pow])))

variable [Finite Y] [Finite K] (hZ : Nat.card (center Y) = 2) (hp : p.Prime) (hp2 : p ≠ 2)
  (hK : Nat.card K = p ^ f)
  (e : Y ⧸ center Y ≃* projectiveSL 4 K) (α : MulAut Y) {A : GL (Fin 4) K}
  (hα' : MulAut.congr e (barAut α) = conjAut 4 K A)

include hZ hp hp2 hK hα' in
theorem diag_t2 {P : GL (Fin 4) K} {μ : Kˣ}
    (hAP : A * P = GeneralLinearGroup.scalar (Fin 4) μ * (P * t2GL)) :
    Concl516 Y α (p ^ f) := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (LieType.Steinberg.ringChar_ne_two_of_card_eq_pow
    hp hp2 hK)
  set ρ := frameHom e P bdSL
  have hfix := frameHom_fixed e α hα' hAP bdSL bdSL_comm
  obtain ⟨hx, hw, hxw, hne⟩ := bd_z4z2 (F := K) h2
  obtain ⟨B, hBM, hBab, hB8, hBinv⟩ :=
    z4z2_of_iso ((conjAut 4 K P).trans e.symm) ρ rfl rfl hx hw hxw hne
  exact concl516_abelian hZ α ρ hfix (hgood_SL2SL2 hp hp2 hK) hBM hBab hB8 hBinv

include hZ hp hp2 hK hα' in
theorem diag_t1 {P : GL (Fin 4) K} {μ : Kˣ}
    (hAP : A * P = GeneralLinearGroup.scalar (Fin 4) μ * (P * t1GL)) :
    Concl516 Y α (p ^ f) := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (LieType.Steinberg.ringChar_ne_two_of_card_eq_pow
    hp hp2 hK)
  set ρ := frameHom e P (blockSL K 3 1)
  have hfix := frameHom_fixed e α hα' hAP (blockSL K 3 1) block_comm
  have := perfect_SL3 (K := K)
  by_cases hin : ∃ x, barAut α = MulAut.conj x
  ·
    obtain ⟨c, hc⟩ := (conjAut_mem_inner_iff (by norm_num : 3 ≤ 4) A).mp
      (hα' ▸ (inner_iff_congr e α).mp hin)
    have hdet : (GeneralLinearGroup.det A : K) = -(μ : K) ^ 4 := by
      have h1 := congrArg (fun g : GL (Fin 4) K => (GeneralLinearGroup.det g : K)) hAP
      simp only [map_mul, Units.val_mul, GeneralLinearGroup.det_scalar, Fintype.card_fin,
        Units.val_pow_eq_pow_val] at h1
      have ht : (GeneralLinearGroup.det (t1GL : GL (Fin 4) K) : K) = -1 := by
        rw [GeneralLinearGroup.val_det_apply, det_t1GL]
      rw [ht] at h1
      have hP : (GeneralLinearGroup.det P : K) ≠ 0 := Units.ne_zero _
      apply mul_right_cancel₀ hP
      linear_combination h1
    have hc4 : ((c : K) / μ) ^ 2 * (((c : K) / μ) ^ 2) = -1 := by
      have hcK : (c : K) ^ 4 = -(μ : K) ^ 4 := by
        rw [← hdet, hc, Units.val_pow_eq_pow_val]
      rw [← pow_add, div_pow, hcK]
      field_simp
    obtain ⟨hx, hw, hxw, hne⟩ := block_z4z2 (F := K) h2 hc4
    obtain ⟨B, hBM, hBab, hB8, hBinv⟩ :=
      z4z2_of_iso ((conjAut 4 K P).trans e.symm) ρ rfl rfl hx hw hxw hne
    exact concl516_abelian hZ α ρ hfix (Or.inl this) hBM hBab hB8 hBinv
  · have hout : ∀ x, barAut α ≠ MulAut.conj x := fun x h => hin ⟨x, h⟩
    have h2d : 2 ∣ Nat.card ρ.range := by
      have hord := block_involution (F := K) h2
      have hmem : ((conjAut 4 K P).trans e.symm) (proj 4 K (blockSL K 3 1 (diag3 (-1) (-1) 1
          (by ring)))) ∈ ρ.range := ⟨_, rfl⟩
      have := orderOf_dvd_natCard (⟨_, hmem⟩ : ρ.range)
      rwa [Subgroup.orderOf_mk, MulEquiv.orderOf_eq, hord] at this
    exact concl516_outer hZ α ρ hfix (Or.inl this) hout
      (four_dvd_card_of_perfect (range_perfect ρ) h2d)

include hZ hp hp2 hK hα' in
theorem diag_N [Group.IsPerfect Y] {P : GL (Fin 4) K} {c : K} (hc : ¬ IsSquare c)
    (hc0 : c ≠ 0)
    (hAP : A * P = GeneralLinearGroup.scalar (Fin 4) 1 * (P * nGL c hc0)) :
    Concl516 Y α (p ^ f) := by
  have hK2 := LieType.Steinberg.ringChar_ne_two_of_card_eq_pow hp hp2 hK
  set ρ := frameHom e P kronSL
  have hfix := frameHom_fixed e α hα' hAP kronSL fun g => kronSL_comm g c
  have hdet : (GeneralLinearGroup.det A : K) = c ^ 2 := by
    have h1 := congrArg (fun g : GL (Fin 4) K => (GeneralLinearGroup.det g : K)) hAP
    simp only [map_mul, Units.val_mul, map_one, one_mul] at h1
    have hN : (GeneralLinearGroup.det (nGL c hc0) : K) = c ^ 2 := by
      rw [GeneralLinearGroup.val_det_apply]
      exact det_stdN c
    rw [hN] at h1
    have hP : (GeneralLinearGroup.det P : K) ≠ 0 := Units.ne_zero _
    apply mul_right_cancel₀ hP
    linear_combination h1
  by_cases hin : ∃ x, barAut α = MulAut.conj x
  · obtain ⟨c₀, hc₀⟩ := (conjAut_mem_inner_iff (by norm_num : 3 ≤ 4) A).mp
      (hα' ▸ (inner_iff_congr e α).mp hin)
    have hcc : c ^ 2 = ((c₀ : K) ^ 2) ^ 2 := by
      rw [← hdet, hc₀, Units.val_pow_eq_pow_val, ← pow_mul]
    have hm1 : ¬ IsSquare (-1 : K) := by
      rintro ⟨r, hr⟩
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hcc with h | h
      · exact hc ⟨c₀, by rw [h, sq]⟩
      · exact hc ⟨r * c₀, by rw [h, show -(c₀ : K) ^ 2 = (-1) * (c₀ : K) ^ 2 by ring, hr]; ring⟩
    obtain ⟨σ', hσ', hσZ⟩ := exists_cover_L4 hZ hK2 e
    obtain ⟨hmem, hne⟩ := cover_negOne hZ hm1 hσZ
    set σ := σ'.comp ((CatalogueBHigherLinearAction.slConjugation 4 K P).toMonoidHom.comp kronSL)
    have hσ : ∀ g, piZ (σ g) = ρ g := fun g => by
      change piZ (σ' _) = _
      rw [hσ', frameHom_apply, MulEquiv.trans_apply, conjAut_proj]
      rfl
    have hneg : σ negOne2 = σ' negOne4 := by
      change σ' (CatalogueBHigherLinearAction.slConjugation 4 K P (kronSL negOne2)) = _
      rw [kronSL_negOne]
      congr 1
      exact Matrix.SpecialLinearGroup.ext _ _ fun i j => by
        rw [coe_slConjugation]
        change ((P : Matrix (Fin 4) (Fin 4) K) * (-1) * ((P⁻¹ : GL (Fin 4) K) :
          Matrix (Fin 4) (Fin 4) K)) i j = (-1 : Matrix (Fin 4) (Fin 4) K) i j
        rw [Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul, ← Units.val_mul, mul_inv_cancel,
          Units.val_one]
    exact concl516_center hZ α ρ hfix (hgood_SL2 hp hp2 hK) σ hσ negOne2 (hneg ▸ hmem)
      (hneg ▸ hne)
  · have hout : ∀ x, barAut α ≠ MulAut.conj x := fun x h => hin ⟨x, h⟩
    have h3 : p ^ f ≠ 3 := by
      intro h3
      apply hin
      apply (inner_iff_congr e α).mpr
      rw [hα']
      refine (conjAut_mem_inner_iff (by norm_num : 3 ≤ 4) A).mpr ⟨1, ?_⟩
      apply Units.ext
      have := Fintype.ofFinite K
      have hcard : Fintype.card K = 3 := by rw [← Nat.card_eq_fintype_card, hK, h3]
      have hc2 : c ^ 2 = 1 := by
        have := FiniteField.pow_card_sub_one_eq_one c hc0
        rwa [hcard] at this
      rw [hdet, hc2, one_pow, Units.val_one]
    have hperf := LinearGroups.special_linear_dimension_two_perfect
      (exists_finset_four (K := K) hp hp2 hK h3)
    have h2d : 2 ∣ Nat.card ρ.range := by
      have hord := kron_involution (F := K)
      have hmem : ((conjAut 4 K P).trans e.symm) (proj 4 K (kronSL jSL)) ∈ ρ.range := ⟨_, rfl⟩
      have := orderOf_dvd_natCard (⟨_, hmem⟩ : ρ.range)
      rwa [Subgroup.orderOf_mk, MulEquiv.orderOf_eq, hord] at this
    exact concl516_outer hZ α ρ hfix (Or.inl hperf) hout
      (four_dvd_card_of_perfect (range_perfect ρ) h2d)

end CFSG.ComponentClassification.GSThmB.Cent516
