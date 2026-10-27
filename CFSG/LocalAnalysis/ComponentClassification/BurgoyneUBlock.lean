module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLBlocks
public import CFSG.LieType.Universal.Unitary.Clause0
public import CFSG.LieType.Steinberg.CentralExt.SUTwo
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneProj
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherHermitian

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.U

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.PSL (blockOn blockOn_one blockOn_mul det_blockOn
  blockOn_apply_mem blockOn_apply_not_mem compInd compInd_mul_apply mul_compInd_apply
  compInd_apply)

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {n : ℕ}

theorem blockOn_map (J : Finset (Fin n)) (φ : K →+* K) (X : Matrix (Fin J.card) (Fin J.card) K) :
    (blockOn K J X).map φ = blockOn K J (X.map φ) := by
  ext i j
  by_cases hi : i ∈ J <;> by_cases hj : j ∈ J
  · rw [Matrix.map_apply, blockOn_apply_mem J _ hi hj, blockOn_apply_mem J _ hi hj,
      Matrix.map_apply]
  · rw [Matrix.map_apply, blockOn_apply_not_mem J _ (Or.inr hj),
      blockOn_apply_not_mem J _ (Or.inr hj)]
    split_ifs <;> simp
  · rw [Matrix.map_apply, blockOn_apply_not_mem J _ (Or.inl hi),
      blockOn_apply_not_mem J _ (Or.inl hi)]
    split_ifs <;> simp
  · rw [Matrix.map_apply, blockOn_apply_not_mem J _ (Or.inl hi),
      blockOn_apply_not_mem J _ (Or.inl hi)]
    split_ifs <;> simp

theorem blockOn_transpose (J : Finset (Fin n)) (X : Matrix (Fin J.card) (Fin J.card) K) :
    (blockOn K J X)ᵀ = blockOn K J Xᵀ := by
  ext i j
  rw [transpose_apply]
  by_cases hi : i ∈ J <;> by_cases hj : j ∈ J
  · rw [blockOn_apply_mem J _ hj hi, blockOn_apply_mem J _ hi hj, transpose_apply]
  · rw [blockOn_apply_not_mem J _ (Or.inl hj), blockOn_apply_not_mem J _ (Or.inr hj)]
    simp only [eq_comm]
  · rw [blockOn_apply_not_mem J _ (Or.inr hi), blockOn_apply_not_mem J _ (Or.inl hi)]
    simp only [eq_comm]
  · rw [blockOn_apply_not_mem J _ (Or.inl hj), blockOn_apply_not_mem J _ (Or.inl hi)]
    simp only [eq_comm]

variable (K) in
@[expose] def blockGL (J : Finset (Fin n)) : GL (Fin J.card) K →* GL (Fin n) K where
  toFun X := ⟨blockOn K J X, blockOn K J (X⁻¹ : GL (Fin J.card) K), by
      rw [← blockOn_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, blockOn_one], by
      rw [← blockOn_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, blockOn_one]⟩
  map_one' := Units.ext (by simp [blockOn_one])
  map_mul' X Y := Units.ext (by simp [blockOn_mul])

theorem coe_blockGL (J : Finset (Fin n)) (X : GL (Fin J.card) K) :
    ((blockGL K J X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = blockOn K J X := rfl

include h in
theorem blockGL_mem (J : Finset (Fin n)) {X : GL (Fin J.card) K}
    (hX : X ∈ StatedSU J.card (p ^ f) K) : blockGL K J X ∈ StatedSU n (p ^ f) K := by
  rw [mem_unitarySU_iff h] at hX ⊢
  refine ⟨by rw [coe_blockGL, det_blockOn]; exact hX.1, ?_⟩
  rw [coe_blockGL, blockOn_map, blockOn_transpose, ← blockOn_mul, hX.2, blockOn_one]

variable (p f K) in
@[expose] def uBlock (J : Finset (Fin n)) : Subgroup (StatedSU n (p ^ f) K) where
  carrier := {g | compInd K J * ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = compInd K J ∧
    ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * compInd K J = compInd K J}
  one_mem' := by simp
  mul_mem' := by
    rintro g g' ⟨hg1, hg2⟩ ⟨hg1', hg2'⟩
    refine ⟨?_, ?_⟩
    · change compInd K J * (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((g' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) = compInd K J
      rw [← Matrix.mul_assoc, hg1, hg1']
    · change (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((g' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) * compInd K J = compInd K J
      rw [Matrix.mul_assoc, hg2', hg2]
  inv_mem' := by
    rintro g ⟨hg1, hg2⟩
    set gi := (((g⁻¹ : StatedSU n (p ^ f) K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
    have h1 : ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * gi = 1 := by
      rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, Units.val_one]
    have h2 : gi * ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
      rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, Units.val_one]
    refine ⟨?_, ?_⟩
    · calc compInd K J * gi = (compInd K J * ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *
          gi := by rw [hg1]
        _ = compInd K J := by rw [Matrix.mul_assoc, h1, Matrix.mul_one]
    · calc gi * compInd K J = gi * (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          compInd K J) := by rw [hg2]
        _ = compInd K J := by rw [← Matrix.mul_assoc, h2, Matrix.one_mul]

@[expose] def blockSU (J : Finset (Fin n)) :
    StatedSU J.card (p ^ f) K →* StatedSU n (p ^ f) K :=
  ((blockGL K J).comp (StatedSU J.card (p ^ f) K).subtype).codRestrict _
    fun X => blockGL_mem h J X.2

theorem coe_blockSU (J : Finset (Fin n)) (X : StatedSU J.card (p ^ f) K) :
    (((blockSU h J X : StatedSU n (p ^ f) K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      blockOn K J ((X : GL (Fin J.card) K) : Matrix (Fin J.card) (Fin J.card) K) := rfl

theorem blockSU_injective (J : Finset (Fin n)) : Function.Injective (blockSU h J) := by
  intro X Y hXY
  apply Subtype.ext
  apply Units.ext
  ext a b
  have h1 := congrArg (fun g : StatedSU n (p ^ f) K => ((g : GL (Fin n) K) :
    Matrix (Fin n) (Fin n) K) (J.equivFin.symm a) (J.equivFin.symm b)) hXY
  simp only [coe_blockSU] at h1
  rw [blockOn_apply_mem J _ (J.equivFin.symm a).2 (J.equivFin.symm b).2,
    blockOn_apply_mem J _ (J.equivFin.symm a).2 (J.equivFin.symm b).2] at h1
  simpa using h1

theorem mem_uBlock_iff {J : Finset (Fin n)} {g : StatedSU n (p ^ f) K} :
    g ∈ uBlock p f K J ↔ ∀ i j, (i ∉ J ∨ j ∉ J) →
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j = if i = j then 1 else 0 := by
  constructor
  · rintro ⟨h1, h2⟩ i j hij
    rcases hij with hi | hj
    · have := congrFun (congrFun h1 i) j
      simp only [compInd_mul_apply, compInd_apply, hi, not_false_eq_true, true_and,
        ite_false] at this
      rw [this]
    · have := congrFun (congrFun h2 i) j
      simp only [mul_compInd_apply, compInd_apply, hj, ite_false] at this
      rw [this]
      by_cases hij : i = j
      · subst hij
        simp [hj]
      · simp [hij]
  · intro hg
    refine ⟨?_, ?_⟩
    · ext i j
      rw [compInd_mul_apply, compInd_apply]
      by_cases hi : i ∈ J
      · simp [hi]
      · simp only [hi, ite_false, not_false_eq_true, true_and]
        exact hg i j (Or.inl hi)
    · ext i j
      rw [mul_compInd_apply, compInd_apply]
      by_cases hj : j ∈ J
      · by_cases hij : i = j
        · subst hij
          simp [hj]
        · simp [hj, hij]
      · simp only [hj, ite_false]
        rw [hg i j (Or.inr hj)]
        by_cases hij : i = j
        · subst hij
          simp [hj]
        · simp [hij]

theorem range_blockSU (J : Finset (Fin n)) : (blockSU h J).range = uBlock p f K J := by
  apply le_antisymm
  · rintro _ ⟨X, rfl⟩
    rw [mem_uBlock_iff]
    intro i j hij
    rw [coe_blockSU, blockOn_apply_not_mem J _ hij]
  · intro g hg
    rw [mem_uBlock_iff] at hg
    set X : Matrix (Fin J.card) (Fin J.card) K := Matrix.of fun a b =>
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) (J.equivFin.symm a) (J.equivFin.symm b)
      with hX
    have hXg : blockOn K J X = ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
      ext i j
      by_cases hi : i ∈ J <;> by_cases hj : j ∈ J
      · rw [blockOn_apply_mem J X hi hj, hX, of_apply, Equiv.symm_apply_apply,
          Equiv.symm_apply_apply]
      · rw [blockOn_apply_not_mem J X (Or.inr hj), hg i j (Or.inr hj)]
      · rw [blockOn_apply_not_mem J X (Or.inl hi), hg i j (Or.inl hi)]
      · rw [blockOn_apply_not_mem J X (Or.inl hi), hg i j (Or.inl hi)]
    set Y : Matrix (Fin J.card) (Fin J.card) K := Matrix.of fun a b =>
      (((g⁻¹ : StatedSU n (p ^ f) K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
        (J.equivFin.symm a) (J.equivFin.symm b) with hY
    have hgi : g⁻¹ ∈ uBlock p f K J := inv_mem (mem_uBlock_iff.2 hg)
    rw [mem_uBlock_iff] at hgi
    have hYg : blockOn K J Y = (((g⁻¹ : StatedSU n (p ^ f) K) : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) := by
      ext i j
      by_cases hi : i ∈ J <;> by_cases hj : j ∈ J
      · rw [blockOn_apply_mem J Y hi hj, hY, of_apply, Equiv.symm_apply_apply,
          Equiv.symm_apply_apply]
      · rw [blockOn_apply_not_mem J Y (Or.inr hj), hgi i j (Or.inr hj)]
      · rw [blockOn_apply_not_mem J Y (Or.inl hi), hgi i j (Or.inl hi)]
      · rw [blockOn_apply_not_mem J Y (Or.inl hi), hgi i j (Or.inl hi)]
    have hinjB : ∀ M N : Matrix (Fin J.card) (Fin J.card) K, blockOn K J M = blockOn K J N →
        M = N := by
      intro M N hMN
      ext a b
      have := congrFun (congrFun hMN (J.equivFin.symm a)) (J.equivFin.symm b)
      rw [blockOn_apply_mem J _ (J.equivFin.symm a).2 (J.equivFin.symm b).2,
        blockOn_apply_mem J _ (J.equivFin.symm a).2 (J.equivFin.symm b).2] at this
      simpa using this
    have hXY : X * Y = 1 := hinjB _ _ (by
      rw [blockOn_mul, hXg, hYg, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel,
        Subgroup.coe_one, Units.val_one, blockOn_one])
    have hYX : Y * X = 1 := hinjB _ _ (by
      rw [blockOn_mul, hXg, hYg, ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel,
        Subgroup.coe_one, Units.val_one, blockOn_one])
    set XG : GL (Fin J.card) K := ⟨X, Y, hXY, hYX⟩
    have hmem : XG ∈ StatedSU J.card (p ^ f) K := by
      have hg2 := (mem_unitarySU_iff h).1 g.2
      rw [mem_unitarySU_iff h]
      refine ⟨by rw [← det_blockOn J X, hXg]; exact hg2.1, hinjB _ _ ?_⟩
      change blockOn K J ((X.map h.bar)ᵀ * X) = blockOn K J 1
      rw [blockOn_mul, ← blockOn_transpose, ← blockOn_map, hXg, hg2.2, blockOn_one]
    exact ⟨⟨XG, hmem⟩, Subtype.ext (Units.ext hXg)⟩

@[expose] def uBlockEquiv (J : Finset (Fin n)) : StatedSU J.card (p ^ f) K ≃* uBlock p f K J :=
  (MonoidHom.ofInjective (blockSU_injective h J)).trans
    (MulEquiv.subgroupCongr (range_blockSU h J))

theorem isQuasisimple_statedSU_of_two_le [Finite K] [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2)
    (hK : Nat.card K = (p ^ f) ^ 2) {k : ℕ} (hk : 2 ≤ k) (hq : 3 ≤ k ∨ 5 ≤ p ^ f) :
    IsQuasisimple (StatedSU k (p ^ f) K) := by
  have hqodd : Odd (p ^ f) := ((Fact.out : p.Prime).odd_of_ne_two hp2).pow
  rcases Nat.lt_or_ge k 3 with hk3 | hk3
  · obtain rfl : k = 2 := by omega
    have h5 : 5 ≤ p ^ f := hq.resolve_left (by omega)
    obtain ⟨ζ, hζ0, hζ⟩ := CFSG.LieType.BorelTits.exists_unitaryInvolution_eq_neg hK
    have hcard := CFSG.LieType.Steinberg.card_fixedSubfield hK
    refine LocalCores.isQuasisimple_of_mulEquiv
      ((CFSG.LieType.Steinberg.hypEquiv hζ0 hζ).trans
        (CFSG.LieType.Universal.Unitary.equivStatedSU hK 2))
      (CatalogueBGeneralLinear.specialLinear_quasisimple 2 _ le_rfl ?_ ?_)
    · right; rw [hcard]; omega
    · right; rw [hcard]; omega
  · refine (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hK hk3 ?_).1
    intro h32
    have := congrArg Prod.snd h32
    simp only at this
    rw [this] at hqodd
    exact (by decide : ¬ Odd 2) hqodd

include h in
theorem isQuasisimple_uBlock (hp2 : p ≠ 2) {J : Finset (Fin n)} (hJ : 2 ≤ J.card)
    (hq : 3 ≤ J.card ∨ 5 ≤ p ^ f) : IsQuasisimple (uBlock p f K J) := by
  have := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have := h.charP
  exact LocalCores.isQuasisimple_of_mulEquiv (uBlockEquiv h J)
    (isQuasisimple_statedSU_of_two_le hp2 h.card_eq_sq hJ hq)

end CFSG.ComponentClassification.Burgoyne.U
