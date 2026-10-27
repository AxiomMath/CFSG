module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOSiegel

public section

namespace CFSG.ComponentClassification.RankTwoClassical.ORigid

open Matrix QuadraticMap Subgroup CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
open scoped MatrixGroups

section Coords

variable {ι₂ ι : Type} (oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι)

abbrev ox (s : Fin 2) : ι := oe (.inr (.inl s))

abbrev oy (s : Fin 2) : ι := oe (.inr (.inr s))

abbrev ou (a : ι₂) : ι := oe (.inl a)

theorem ox_ne_oy (s t : Fin 2) : ox oe s ≠ oy oe t := oe.injective.ne (by simp)

theorem oy_ne_ox (s t : Fin 2) : oy oe s ≠ ox oe t := oe.injective.ne (by simp)

theorem ou_ne_ox (a : ι₂) (s : Fin 2) : ou oe a ≠ ox oe s := oe.injective.ne (by simp)

theorem ou_ne_oy (a : ι₂) (s : Fin 2) : ou oe a ≠ oy oe s := oe.injective.ne (by simp)

theorem ox_ne_ox {s t : Fin 2} (h : s ≠ t) : ox oe s ≠ ox oe t := oe.injective.ne (by simp [h])

theorem oy_ne_oy {s t : Fin 2} (h : s ≠ t) : oy oe s ≠ oy oe t := oe.injective.ne (by simp [h])

theorem sum_oe {M : Type} [AddCommMonoid M] [Fintype ι₂] [Fintype ι] (f : ι → M) :
    ∑ i, f i = ∑ a, f (ou oe a) + (∑ s, f (ox oe s) + ∑ s, f (oy oe s)) := by
  rw [← Equiv.sum_comp oe, Fintype.sum_sum_type, Fintype.sum_sum_type]

end Coords

section Root

variable {K : Type} [Field K] {ι₂ ι : Type} [Fintype ι₂] [DecidableEq ι₂] [Fintype ι]
  [DecidableEq ι] (oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι)

variable (K) in
@[expose] def oN₀ : Matrix ι ι K := single (ox oe 1) (oy oe 0) 1 + single (ox oe 0) (oy oe 1) 1

theorem oblk_apply (Y : Matrix ι₂ ι₂ K) (X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
    (c d : ι₂ ⊕ (Fin 2 ⊕ Fin 2)) : oblk oe Y X (oe c) (oe d) = fromBlocks Y 0 0 X c d := by
  simp [oblk, coe_reindexAlgEquiv, reindex_apply]

theorem oRhoOneGL_slTr_one :
    ((oRhoOneGL oe (slTr 1) : GL ι K) : Matrix ι ι K) = 1 + oN₀ K oe := by
  ext i j
  obtain ⟨c, rfl⟩ := oe.surjective i
  obtain ⟨d, rfl⟩ := oe.surjective j
  rw [coe_oRhoOneGL, oblk_apply, rhoOneMat_apply]
  rcases c with a | s | s <;> rcases d with b | t | t
  all_goals (try fin_cases s) <;> (try fin_cases t) <;>
    simp [oN₀, slTr, swapM, Matrix.one_apply, fromBlocks]

omit [Fintype ι₂] [DecidableEq ι₂] in
theorem mul_oN₀_apply (g : Matrix ι ι K) (i j : ι) :
    (g * oN₀ K oe) i j = (if j = oy oe 0 then g i (ox oe 1) else 0) +
      (if j = oy oe 1 then g i (ox oe 0) else 0) := by
  rw [oN₀, Matrix.mul_add, Matrix.add_apply]
  congr 1
  · by_cases hj : j = oy oe 0
    · rw [ite_eq_left hj, hj, mul_single_apply_same, mul_one]
    · rw [ite_eq_right hj, mul_single_apply_of_ne _ _ _ _ _ hj]
  · by_cases hj : j = oy oe 1
    · rw [ite_eq_left hj, hj, mul_single_apply_same, mul_one]
    · rw [ite_eq_right hj, mul_single_apply_of_ne _ _ _ _ _ hj]

omit [Fintype ι₂] [DecidableEq ι₂] in
theorem oN₀_mul_apply (g : Matrix ι ι K) (i j : ι) :
    (oN₀ K oe * g) i j = (if i = ox oe 1 then g (oy oe 0) j else 0) +
      (if i = ox oe 0 then g (oy oe 1) j else 0) := by
  rw [oN₀, Matrix.add_mul, Matrix.add_apply]
  congr 1
  · by_cases hi : i = ox oe 1
    · rw [ite_eq_left hi, hi, single_mul_apply_same, one_mul]
    · rw [ite_eq_right hi, single_mul_apply_of_ne _ _ _ _ _ hi]
  · by_cases hi : i = ox oe 0
    · rw [ite_eq_left hi, hi, single_mul_apply_same, one_mul]
    · rw [ite_eq_right hi, single_mul_apply_of_ne _ _ _ _ _ hi]

variable {oe} {g : Matrix ι ι K} (hg : g * oN₀ K oe = oN₀ K oe * g)
include hg

omit [Fintype ι₂] [DecidableEq ι₂] in
theorem commute_oN₀_col {i : ι} (hi : ∀ s, i ≠ ox oe s) (s : Fin 2) : g i (ox oe s) = 0 := by
  fin_cases s
  · have h := congrFun (congrFun hg i) (oy oe 1)
    rw [mul_oN₀_apply, oN₀_mul_apply, ite_eq_right (oy_ne_oy oe (by decide)), ite_eq_left rfl,
      ite_eq_right (hi 1), ite_eq_right (hi 0)] at h
    simpa using h
  · have h := congrFun (congrFun hg i) (oy oe 0)
    rw [mul_oN₀_apply, oN₀_mul_apply, ite_eq_left rfl, ite_eq_right (oy_ne_oy oe (by decide)),
      ite_eq_right (hi 1), ite_eq_right (hi 0)] at h
    simpa using h

omit [Fintype ι₂] [DecidableEq ι₂] in
theorem commute_oN₀_row {j : ι} (hj : ∀ s, j ≠ oy oe s) (s : Fin 2) : g (oy oe s) j = 0 := by
  fin_cases s
  · have h := congrFun (congrFun hg (ox oe 1)) j
    rw [mul_oN₀_apply, oN₀_mul_apply, ite_eq_right (hj 0), ite_eq_right (hj 1), ite_eq_left rfl,
      ite_eq_right (ox_ne_ox oe (by decide))] at h
    simpa using h.symm
  · have h := congrFun (congrFun hg (ox oe 0)) j
    rw [mul_oN₀_apply, oN₀_mul_apply, ite_eq_right (hj 0), ite_eq_right (hj 1),
      ite_eq_right (ox_ne_ox oe (by decide)), ite_eq_left rfl] at h
    simpa using h.symm

omit [Fintype ι₂] [DecidableEq ι₂] in
theorem commute_oN₀_diag : g (oy oe 0) (oy oe 0) = g (ox oe 1) (ox oe 1) ∧
    g (oy oe 1) (oy oe 1) = g (ox oe 0) (ox oe 0) ∧
    g (oy oe 1) (oy oe 0) = g (ox oe 0) (ox oe 1) ∧
    g (oy oe 0) (oy oe 1) = g (ox oe 1) (ox oe 0) := by
  have h10 := congrFun (congrFun hg (ox oe 1)) (oy oe 0)
  have h01 := congrFun (congrFun hg (ox oe 0)) (oy oe 1)
  have h00 := congrFun (congrFun hg (ox oe 0)) (oy oe 0)
  have h11 := congrFun (congrFun hg (ox oe 1)) (oy oe 1)
  simp only [mul_oN₀_apply, oN₀_mul_apply, ↓reduceIte,
    ite_eq_right (oy_ne_oy oe (by decide : (0 : Fin 2) ≠ 1)),
    ite_eq_right (oy_ne_oy oe (by decide : (1 : Fin 2) ≠ 0)),
    ite_eq_right (ox_ne_ox oe (by decide : (0 : Fin 2) ≠ 1)),
    ite_eq_right (ox_ne_ox oe (by decide : (1 : Fin 2) ≠ 0)), add_zero, zero_add] at h10 h01 h00 h11
  exact ⟨h10.symm, h01.symm, h00.symm, h11.symm⟩

end Root

section Blocks

variable {K : Type} [Field K] {ι₂ ι : Type} [Fintype ι₂] [DecidableEq ι₂] [Fintype ι]
  [DecidableEq ι] (oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι)

@[expose] def eBlk (g : Matrix ι ι K) : Matrix (Fin 2) (Fin 2) K :=
  fun s t => g (ox oe s) (ox oe t)

@[expose] def uBlk (g : Matrix ι ι K) : Matrix ι₂ ι₂ K := fun a b => g (ou oe a) (ou oe b)

@[expose] def IsEShape (g : Matrix ι ι K) : Prop :=
  (∀ i, (∀ s, i ≠ ox oe s) → ∀ s, g i (ox oe s) = 0) ∧
    ∀ j, (∀ s, j ≠ oy oe s) → ∀ s, g (oy oe s) j = 0

variable {oe}

omit [Fintype ι₂] [DecidableEq ι₂] in
theorem isEShape_of_commute {g : Matrix ι ι K} (hg : g * oN₀ K oe = oN₀ K oe * g) :
    IsEShape oe g :=
  ⟨fun _ hi s => commute_oN₀_col hg hi s, fun _ hj s => commute_oN₀_row hg hj s⟩

omit [Fintype ι₂] [DecidableEq ι₂] [Fintype ι] in
theorem eBlk_one : eBlk oe (1 : Matrix ι ι K) = 1 := by
  ext s t
  simp [eBlk, Matrix.one_apply]

omit [Fintype ι₂] [Fintype ι] in
theorem uBlk_one : uBlk oe (1 : Matrix ι ι K) = 1 := by
  ext a b
  simp [uBlk, Matrix.one_apply]

omit [DecidableEq ι₂] [DecidableEq ι] in
theorem eBlk_mul (g : Matrix ι ι K) {g' : Matrix ι ι K} (hg' : IsEShape oe g') :
    eBlk oe (g * g') = eBlk oe g * eBlk oe g' := by
  ext s t
  have h1 : ∀ a, g' (ou oe a) (ox oe t) = 0 := fun a => hg'.1 _ (ou_ne_ox oe a) t
  have h2 : ∀ r, g' (oy oe r) (ox oe t) = 0 := fun r => hg'.1 _ (oy_ne_ox oe r) t
  simp only [eBlk, Matrix.mul_apply]
  rw [sum_oe oe]
  simp [h1, h2]

omit [DecidableEq ι₂] [DecidableEq ι] in
theorem uBlk_mul {g g' : Matrix ι ι K} (hg : IsEShape oe g) (hg' : IsEShape oe g') :
    uBlk oe (g * g') = uBlk oe g * uBlk oe g' := by
  ext a b
  have h1 : ∀ r, g (ou oe a) (ox oe r) = 0 := fun r => hg.1 _ (ou_ne_ox oe a) r
  have h2 : ∀ r, g' (oy oe r) (ou oe b) = 0 := fun r => hg'.2 _ (ou_ne_oy oe b) r
  simp only [uBlk, Matrix.mul_apply]
  rw [sum_oe oe]
  simp [h1, h2]

variable (K oe) in
abbrev cenM₀ : Subgroup (GL ι K) := centralizer {oRhoOneGL oe (slTr 1)}

theorem commute_oN₀_of_mem {g : GL ι K} (hg : g ∈ cenM₀ K oe) :
    (g : Matrix ι ι K) * oN₀ K oe = oN₀ K oe * g := by
  have h := congrArg (fun x : GL ι K => (x : Matrix ι ι K)) (mem_centralizer_singleton_iff.mp hg)
  simp only [Units.val_mul, oRhoOneGL_slTr_one] at h
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul] at h
  exact add_left_cancel h

theorem isEShape_of_mem {g : GL ι K} (hg : g ∈ cenM₀ K oe) : IsEShape oe (g : Matrix ι ι K) :=
  isEShape_of_commute (commute_oN₀_of_mem hg)

variable (K oe) in
@[expose] noncomputable def eBlkHom : cenM₀ K oe →* Matrix (Fin 2) (Fin 2) K where
  toFun g := eBlk oe ((g : GL ι K) : Matrix ι ι K)
  map_one' := eBlk_one
  map_mul' _ h := eBlk_mul _ (isEShape_of_mem h.2)

variable (K oe) in
@[expose] noncomputable def uBlkHom : cenM₀ K oe →* Matrix ι₂ ι₂ K where
  toFun g := uBlk oe ((g : GL ι K) : Matrix ι ι K)
  map_one' := uBlk_one
  map_mul' g h := uBlk_mul (isEShape_of_mem g.2) (isEShape_of_mem h.2)

theorem eBlkHom_apply (g : cenM₀ K oe) :
    eBlkHom K oe g = eBlk oe ((g : GL ι K) : Matrix ι ι K) := rfl

theorem uBlkHom_apply (g : cenM₀ K oe) :
    uBlkHom K oe g = uBlk oe ((g : GL ι K) : Matrix ι ι K) := rfl

end Blocks

end CFSG.ComponentClassification.RankTwoClassical.ORigid
