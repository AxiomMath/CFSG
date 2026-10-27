module

public import CFSG.LinearAlgebra.SelfAdjointIdempotent
public import Mathlib.LinearAlgebra.Matrix.Echelon.Basic

public section

namespace CFSG.LinearAlgebra

open Matrix

variable {K : Type*} [Field K] {n k : ℕ}

theorem submatrix_pivot_eq_one {H : Matrix (Fin k) (Fin n) K} (hH : H.IsReducedRowEchelon)
    {p : Fin k → Fin n} (hp : ∀ i, H.IsLeadingEntry i (p i)) : H.submatrix id p = 1 := by
  ext i j
  rw [submatrix_apply, id, one_apply]
  split_ifs with hij
  · rw [hij]
    exact hH.eq_one (hp j)
  · exact hH.eq_zero_of_ne_of_isLeadingEntry hij (hp j)

theorem strictMono_pivot {H : Matrix (Fin k) (Fin n) K} (hH : H.IsRowEchelon)
    {p : Fin k → Fin n} (hp : ∀ i, H.IsLeadingEntry i (p i)) : StrictMono p := by
  intro i₁ i₂ hlt
  by_contra hle
  push Not at hle
  exact (hp i₂).2 (hH hlt fun j hj => (hp i₁).1 j (lt_of_lt_of_le hj hle))

theorem exists_pivots {H : Matrix (Fin k) (Fin n) K}
    (hH : Module.finrank K (Submodule.span K (Set.range H)) = k) :
    ∃ p : Fin k → Fin n, ∀ i, H.IsLeadingEntry i (p i) := by
  have hli : LinearIndependent K H :=
    linearIndependent_iff_card_eq_finrank_span.mpr (by rw [Fintype.card_fin]; exact hH.symm)
  have hp : ∀ i, ∃ c, H.IsLeadingEntry i c := fun i =>
    row_ne_zero_iff_exists_isLeadingEntry.mp (hli.ne_zero i)
  choose p hp using hp
  exact ⟨p, hp⟩

theorem eq_sum_of_mem_span_rref {H : Matrix (Fin k) (Fin n) K} (hH : H.IsReducedRowEchelon)
    {p : Fin k → Fin n} (hp : ∀ i, H.IsLeadingEntry i (p i)) {v : Fin n → K}
    (hv : v ∈ Submodule.span K (Set.range H)) : v = ∑ i, v (p i) • H i := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hv
  have hc : ∀ j, (∑ i, c i • H i) (p j) = c j := by
    intro j
    rw [Finset.sum_apply, Finset.sum_eq_single j]
    · rw [Pi.smul_apply, smul_eq_mul, hH.eq_one (hp j), mul_one]
    · intro i _ hij
      rw [Pi.smul_apply, smul_eq_mul, hH.eq_zero_of_ne_of_isLeadingEntry hij (hp j), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ j) h
  simp only [hc]

theorem exists_isLeading_pivot_of_mem_span {H : Matrix (Fin k) (Fin n) K}
    (hH : H.IsReducedRowEchelon) {p : Fin k → Fin n} (hp : ∀ i, H.IsLeadingEntry i (p i))
    {v : Fin n → K} (hv : v ∈ Submodule.span K (Set.range H)) (hv0 : v ≠ 0) :
    ∃ i, (∀ j < p i, v j = 0) ∧ v (p i) ≠ 0 := by
  have hsum := eq_sum_of_mem_span_rref hH hp hv
  have hex : ∃ i, v (p i) ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hv0
    rw [hsum]
    simp [hall]
  obtain ⟨i₀, hi₀, hmin⟩ := WellFounded.has_min wellFounded_lt {i | v (p i) ≠ 0} hex
  refine ⟨i₀, fun j hj => ?_, hi₀⟩
  rw [hsum, Finset.sum_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Pi.smul_apply, smul_eq_mul]
  by_cases hi : v (p i) = 0
  · rw [hi, zero_mul]
  · have hle : i₀ ≤ i := not_lt.mp (hmin i hi)
    rw [(hp i).1 j (lt_of_lt_of_le hj ((strictMono_pivot hH.isRowEchelon hp).monotone hle)),
      mul_zero]

theorem rref_unique {H₁ H₂ : Matrix (Fin k) (Fin n) K} (h₁ : H₁.IsReducedRowEchelon)
    (h₂ : H₂.IsReducedRowEchelon) {p₁ p₂ : Fin k → Fin n}
    (hp₁ : ∀ i, H₁.IsLeadingEntry i (p₁ i)) (hp₂ : ∀ i, H₂.IsLeadingEntry i (p₂ i))
    (hspan : Submodule.span K (Set.range H₁) = Submodule.span K (Set.range H₂)) : H₁ = H₂ := by
  have hrange : ∀ {Ha Hb : Matrix (Fin k) (Fin n) K} {pa pb : Fin k → Fin n},
      Ha.IsReducedRowEchelon → (∀ i, Ha.IsLeadingEntry i (pa i)) →
      (∀ i, Hb.IsLeadingEntry i (pb i)) →
      Submodule.span K (Set.range Hb) ≤ Submodule.span K (Set.range Ha) →
        Set.range pb ⊆ Set.range pa := by
    rintro Ha Hb pa pb ha hpa hpb hle _ ⟨i, rfl⟩
    have hmem : Hb i ∈ Submodule.span K (Set.range Ha) :=
      hle (Submodule.subset_span ⟨i, rfl⟩)
    obtain ⟨j, hj⟩ := exists_isLeading_pivot_of_mem_span ha hpa hmem (hpb i).row_ne_zero
    exact ⟨j, IsLeadingEntry.unique (A := Hb) hj (hpb i)⟩
  have hp : p₁ = p₂ := (StrictMono.range_inj_of_wellFoundedLT
    (strictMono_pivot h₁.isRowEchelon hp₁) (strictMono_pivot h₂.isRowEchelon hp₂)).mp
    ((hrange h₂ hp₂ hp₁ hspan.le).antisymm (hrange h₁ hp₁ hp₂ hspan.ge))
  subst hp
  funext i
  have hmem : H₂ i ∈ Submodule.span K (Set.range H₁) :=
    hspan ▸ Submodule.subset_span ⟨i, rfl⟩
  rw [eq_sum_of_mem_span_rref h₁ hp₁ hmem, Finset.sum_eq_single i]
  · rw [h₂.eq_one (hp₂ i), one_smul]
  · intro j _ hji
    rw [h₂.eq_zero_of_ne_of_isLeadingEntry hji.symm (hp₂ j), zero_smul]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem exists_rref (V : Submodule K (Fin n → K)) (hV : Module.finrank K V = k) :
    ∃ H : Matrix (Fin k) (Fin n) K, H.IsReducedRowEchelon ∧
      Submodule.span K (Set.range H) = V := by
  classical
  set Lead : Finset (Fin n) :=
    Finset.univ.filter fun c => ∃ v ∈ V, (∀ j < c, v j = 0) ∧ v c ≠ 0 with hLeaddef
  have hLead : ∀ c, c ∈ Lead ↔ ∃ v ∈ V, (∀ j < c, v j = 0) ∧ v c ≠ 0 := fun c => by
    simp [hLeaddef]
  have hlead : ∀ v ∈ V, v ≠ 0 → ∃ c ∈ Lead, (∀ j < c, v j = 0) ∧ v c ≠ 0 := by
    intro v hv hv0
    obtain ⟨c, hc, hmin⟩ := WellFounded.has_min wellFounded_lt {j | v j ≠ 0}
      (Function.ne_iff.mp hv0)
    have h1 : ∀ j < c, v j = 0 := fun j hj => by
      by_contra h
      exact hmin j h hj
    exact ⟨c, (hLead c).mpr ⟨v, hv, h1, hc⟩, h1, hc⟩
  have hinj : ∀ v ∈ V, (∀ c : Lead, v c = 0) → v = 0 := by
    intro v hv h0
    by_contra hv0
    obtain ⟨c, hc, -, hvc⟩ := hlead v hv hv0
    exact hvc (h0 ⟨c, hc⟩)
  have hw : ∀ c : Lead, ∃ w ∈ V, (∀ j < (c : Fin n), w j = 0) ∧ w c ≠ 0 :=
    fun c => (hLead c).mp c.2
  choose w hwV hw0 hwc using hw
  set M : Matrix Lead Lead K := fun c c' => w c c' with hMdef
  have hMtri : M.IsUpperTriangular := fun c c' hlt => hw0 c c' hlt
  have hMdet : IsUnit M.det := by
    rw [det_of_isUpperTriangular hMtri]
    exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun c _ => hwc c)
  set u : Lead → Fin n → K := fun c₀ => ∑ c, M⁻¹ c₀ c • w c with hudef
  have huV : ∀ c₀, u c₀ ∈ V := fun c₀ =>
    Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (hwV c)
  have huδ : ∀ c₀ c' : Lead, u c₀ c' = (1 : Matrix Lead Lead K) c₀ c' := by
    intro c₀ c'
    rw [← nonsing_inv_mul M hMdet, Matrix.mul_apply]
    simp only [hudef, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rfl
  have hexp : ∀ v ∈ V, v = ∑ c : Lead, v c • u c := by
    intro v hv
    refine sub_eq_zero.mp (hinj _ (sub_mem hv (Submodule.sum_mem _ fun c _ =>
      Submodule.smul_mem _ _ (huV c))) fun c' => ?_)
    rw [Pi.sub_apply, Finset.sum_apply, sub_eq_zero, Finset.sum_eq_single c']
    · rw [Pi.smul_apply, smul_eq_mul, huδ, one_apply_eq, mul_one]
    · intro c _ hc
      rw [Pi.smul_apply, smul_eq_mul, huδ, one_apply_ne hc, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hli : LinearIndependent K u := by
    refine Fintype.linearIndependent_iff.mpr fun g hg c₀ => ?_
    have h1 := congrFun hg c₀
    rw [Finset.sum_apply, Finset.sum_eq_single c₀] at h1
    · rwa [Pi.smul_apply, smul_eq_mul, huδ, one_apply_eq, mul_one] at h1
    · intro c _ hc
      rw [Pi.smul_apply, smul_eq_mul, huδ, one_apply_ne hc, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hspan : Submodule.span K (Set.range u) = V := by
    refine le_antisymm (Submodule.span_le.mpr ?_) fun v hv => ?_
    · rintro _ ⟨c, rfl⟩
      exact huV c
    · rw [hexp v hv]
      exact Submodule.sum_mem _ fun c _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, rfl⟩)
  have hcard : Lead.card = k := by
    rw [← hV, ← hspan, finrank_span_eq_card hli, Fintype.card_coe]
  set e := Lead.orderIsoOfFin hcard with he
  have hLE : ∀ i : Fin k, (∀ j < ((e i : Lead) : Fin n), u (e i) j = 0) ∧
      u (e i) (e i) ≠ 0 := by
    intro i
    have h1 : u (e i) (e i) = 1 := by rw [huδ, one_apply_eq]
    have hne : u (e i) ≠ 0 := fun h0 => by
      rw [h0, Pi.zero_apply] at h1
      exact zero_ne_one h1
    obtain ⟨c, hc, hc0, hcne⟩ := hlead _ (huV (e i)) hne
    have hce : (⟨c, hc⟩ : Lead) = e i := by
      by_contra hne'
      apply hcne
      rw [show c = ((⟨c, hc⟩ : Lead) : Fin n) from rfl, huδ, one_apply_ne (Ne.symm hne')]
    have hce' : c = ((e i : Lead) : Fin n) := congrArg Subtype.val hce
    rw [← hce']
    exact ⟨hc0, hcne⟩
  set H : Matrix (Fin k) (Fin n) K := fun i => u (e i) with hHdef
  have hHlead : ∀ i, H.IsLeadingEntry i ((e i : Lead) : Fin n) := hLE
  have hHuniq : ∀ i c, H.IsLeadingEntry i c → c = ((e i : Lead) : Fin n) :=
    fun i c hc => IsLeadingEntry.unique hc (hHlead i)
  have hmono : StrictMono fun i => ((e i : Lead) : Fin n) := fun i₁ i₂ hlt => e.strictMono hlt
  refine ⟨H, ⟨fun i₁ i₂ hlt j₂ hz => ?_, fun i c hc => ?_, fun i₁ i₂ c hlt hc => ?_⟩, ?_⟩
  · have hj : j₂ ≤ ((e i₁ : Lead) : Fin n) := by
      by_contra hgt
      push Not at hgt
      exact (hHlead i₁).2 (hz _ hgt)
    exact (hHlead i₂).1 j₂ (lt_of_le_of_lt hj (hmono hlt))
  · rw [hHuniq i c hc]
    change u (e i) (e i) = 1
    rw [huδ, one_apply_eq]
  · rw [hHuniq i₂ c hc]
    change u (e i₁) (e i₂) = 0
    rw [huδ, one_apply_ne (e.injective.ne hlt.ne)]
  · rw [← hspan]
    refine le_antisymm (Submodule.span_le.mpr ?_) (Submodule.span_le.mpr ?_)
    · rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨e i, rfl⟩
    · rintro _ ⟨c, rfl⟩
      exact Submodule.subset_span ⟨e.symm c, by simp [hHdef]⟩

theorem existsUnique_canonical_basis (V : Submodule K (Fin n → K))
    (hV : Module.finrank K V = k) :
    ∃! U : Matrix (Fin n) (Fin k) K, Uᵀ.IsReducedRowEchelon ∧
      Submodule.span K (Set.range U.col) = V := by
  obtain ⟨H, hH, hHV⟩ := exists_rref V hV
  refine ⟨Hᵀ, ⟨by rwa [transpose_transpose], hHV⟩, fun U' ⟨hU', hU'V⟩ => ?_⟩
  have hfin : ∀ {H' : Matrix (Fin k) (Fin n) K}, Submodule.span K (Set.range H') = V →
      Module.finrank K (Submodule.span K (Set.range H')) = k := fun h => by rw [h, hV]
  obtain ⟨p, hp⟩ := exists_pivots (hfin hHV)
  obtain ⟨p', hp'⟩ := exists_pivots (H := U'ᵀ) (hfin hU'V)
  rw [← transpose_transpose U', rref_unique hU' hH hp' hp ((show Submodule.span K
    (Set.range U'ᵀ) = V from hU'V).trans hHV.symm)]

theorem isUnit_of_rank_eq {S : Matrix (Fin k) (Fin k) K} (h : S.rank = k) : IsUnit S := by
  have htop : LinearMap.range S.mulVecLin = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by rw [Module.finrank_fin_fun]; exact h)
  exact mulVec_injective_iff_isUnit.mp
    (LinearMap.injective_iff_surjective.mpr (LinearMap.range_eq_top.mp htop))

theorem range_mul_of_isUnit {m : ℕ} (A : Matrix (Fin m) (Fin n) K) {B : Matrix (Fin n) (Fin n) K}
    (hB : IsUnit B) : LinearMap.range (A * B).mulVecLin = LinearMap.range A.mulVecLin := by
  have htop : LinearMap.range B.mulVecLin = ⊤ :=
    LinearMap.range_eq_top.mpr (mulVec_surjective_iff_isUnit.mpr hB)
  rw [mulVecLin_mul, LinearMap.range_comp_of_range_eq_top _ htop]

theorem submatrix_mul_mul {l m o p q : ℕ} (A : Matrix (Fin l) (Fin m) K)
    (B : Matrix (Fin m) (Fin o) K) (C : Matrix (Fin o) (Fin p) K) (r : Fin q → Fin l)
    (c : Fin k → Fin p) :
    (A * B * C).submatrix r c = A.submatrix r id * B * C.submatrix id c := by
  ext i j
  simp [Matrix.mul_apply]

theorem submatrix_mul_id {l m o : ℕ} (A : Matrix (Fin l) (Fin m) K)
    (B : Matrix (Fin m) (Fin o) K) (r : Fin k → Fin l) :
    (A * B).submatrix r id = A.submatrix r id * B := by
  ext i j
  simp [Matrix.mul_apply]

theorem rank_eq_finrank_span_col (U : Matrix (Fin n) (Fin k) K) :
    U.rank = Module.finrank K (Submodule.span K (Set.range U.col)) := by
  show Module.finrank K (LinearMap.range U.mulVecLin) = _
  rw [range_mulVecLin]

theorem exists_pivots_of_rank {U : Matrix (Fin n) (Fin k) K} (hU : Uᵀ.IsReducedRowEchelon)
    (hUr : U.rank = k) :
    ∃ p : Fin k → Fin n, (∀ i, Uᵀ.IsLeadingEntry i (p i)) ∧ U.submatrix p id = 1 := by
  obtain ⟨p, hp⟩ := exists_pivots (H := Uᵀ) ((rank_eq_finrank_span_col U).symm.trans hUr)
  refine ⟨p, hp, ?_⟩
  rw [← transpose_transpose (U.submatrix p id), transpose_submatrix,
    submatrix_pivot_eq_one hU hp, transpose_one]

variable {F E : Matrix (Fin n) (Fin n) K}

theorem transpose_mul_inv (hFsymm : Fᵀ = F) (hF : IsUnit F) (hEF : Eᵀ * F = F * E) :
    (E * F⁻¹)ᵀ = E * F⁻¹ := by
  have hdet := (isUnit_iff_isUnit_det F).mp hF
  have hEt : Eᵀ = F * E * F⁻¹ := by
    calc Eᵀ = Eᵀ * F * F⁻¹ := by rw [Matrix.mul_assoc, mul_nonsing_inv _ hdet, Matrix.mul_one]
      _ = F * E * F⁻¹ := by rw [hEF]
  rw [transpose_mul, transpose_nonsing_inv, hFsymm, hEt, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    nonsing_inv_mul _ hdet, Matrix.one_mul]

theorem selfAdjoint_factorization_spec (hFsymm : Fᵀ = F) (hF : IsUnit F) (hrank : E.rank = k)
    (hEF : Eᵀ * F = F * E) {U : Matrix (Fin n) (Fin k) K} {p : Fin k → Fin n}
    (hp1 : U.submatrix p id = 1)
    (hUE : LinearMap.range U.mulVecLin = LinearMap.range E.mulVecLin) :
    ((E * F⁻¹).submatrix p p)ᵀ = (E * F⁻¹).submatrix p p ∧
      IsUnit ((E * F⁻¹).submatrix p p) ∧ E = U * (E * F⁻¹).submatrix p p * Uᵀ * F := by
  have hdet := (isUnit_iff_isUnit_det F).mp hF
  have hFi : IsUnit F⁻¹ := (isUnit_iff_isUnit_det _).mpr (isUnit_nonsing_inv_det F hdet)
  set T := E * F⁻¹ with hTdef
  have hT : Tᵀ = T := transpose_mul_inv hFsymm hF hEF
  have hTU : LinearMap.range T.mulVecLin = LinearMap.range U.mulVecLin := by
    rw [hTdef, range_mul_of_isUnit _ hFi, hUE]
  obtain ⟨M, hM⟩ := exists_mul_eq_of_range_le hTU.le
  have hX : T = U * T.submatrix p id := by
    rw [← hM, submatrix_mul_id, hp1, Matrix.one_mul]
  have hY : T = T.submatrix id p * Uᵀ := by
    calc T = Tᵀ := hT.symm
      _ = T.submatrix id p * Uᵀ := by
          conv_lhs => rw [hX]
          rw [transpose_mul, transpose_submatrix, hT]
  have hS : T = U * T.submatrix p p * Uᵀ := by
    have h1 : T.submatrix p id = T.submatrix p p * Uᵀ := by
      conv_lhs => rw [hY]
      rw [submatrix_mul_id, submatrix_submatrix]
      rfl
    rw [Matrix.mul_assoc, ← h1, ← hX]
  have hET : E = T * F := by
    rw [hTdef, Matrix.mul_assoc, nonsing_inv_mul _ hdet, Matrix.mul_one]
  refine ⟨by rw [transpose_submatrix, hT], ?_, ?_⟩
  · refine isUnit_of_rank_eq (le_antisymm (rank_le_width _) ?_)
    calc k = T.rank := by
          rw [← hrank, hTdef, rank_mul_eq_left_of_isUnit_det _ _ (isUnit_nonsing_inv_det F hdet)]
      _ = (U * T.submatrix p p * Uᵀ).rank := by rw [← hS]
      _ ≤ (U * T.submatrix p p).rank := rank_mul_le_left _ _
      _ ≤ (T.submatrix p p).rank := rank_mul_le_right _ _
  · conv_lhs => rw [hET, hS]

theorem eq_submatrix_of_eq_mul (hF : IsUnit F) {U : Matrix (Fin n) (Fin k) K}
    {p : Fin k → Fin n} (hp1 : U.submatrix p id = 1) {S : Matrix (Fin k) (Fin k) K}
    (hE : E = U * S * Uᵀ * F) : S = (E * F⁻¹).submatrix p p := by
  have hdet := (isUnit_iff_isUnit_det F).mp hF
  have hUt : Uᵀ.submatrix id p = 1 := by
    rw [← transpose_transpose (Uᵀ.submatrix id p), transpose_submatrix, transpose_transpose,
      hp1, transpose_one]
  rw [hE, Matrix.mul_assoc _ F, mul_nonsing_inv _ hdet, Matrix.mul_one, submatrix_mul_mul, hp1,
    hUt, Matrix.one_mul, Matrix.mul_one]

theorem selfAdjoint_factorization_converse (hFsymm : Fᵀ = F) (hF : IsUnit F)
    {U : Matrix (Fin n) (Fin k) K} (hU : Uᵀ.IsReducedRowEchelon) (hUr : U.rank = k)
    {S : Matrix (Fin k) (Fin k) K} (hS : IsUnit S) (hSsymm : Sᵀ = S) :
    (U * S * Uᵀ * F).rank = k ∧ (U * S * Uᵀ * F)ᵀ * F = F * (U * S * Uᵀ * F) ∧
      LinearMap.range (U * S * Uᵀ * F).mulVecLin = LinearMap.range U.mulVecLin := by
  obtain ⟨p, -, hp1⟩ := exists_pivots_of_rank hU hUr
  have hSp := eq_submatrix_of_eq_mul (E := U * S * Uᵀ * F) hF hp1 rfl
  have hrank : (U * S * Uᵀ * F).rank = k := by
    refine le_antisymm ?_ ?_
    · calc (U * S * Uᵀ * F).rank ≤ (U * S * Uᵀ).rank := rank_mul_le_left _ _
        _ ≤ (U * S).rank := rank_mul_le_left _ _
        _ ≤ U.rank := rank_mul_le_left _ _
        _ = k := hUr
    · calc k = S.rank := by rw [rank_of_isUnit _ hS, Fintype.card_fin]
        _ = ((U * S * Uᵀ * F * F⁻¹).submatrix p p).rank := by rw [← hSp]
        _ ≤ (U * S * Uᵀ * F * F⁻¹).rank := rank_submatrix_le _ _ _
        _ ≤ (U * S * Uᵀ * F).rank := rank_mul_le_left _ _
  refine ⟨hrank, ?_, ?_⟩
  · rw [transpose_mul, transpose_mul, transpose_mul, transpose_transpose, hFsymm, hSsymm]
    simp only [Matrix.mul_assoc]
  · have hle : LinearMap.range (U * S * Uᵀ * F).mulVecLin ≤ LinearMap.range U.mulVecLin := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc]
      exact range_mul_le _ _
    refine Submodule.eq_of_le_of_finrank_eq hle ?_
    change (U * S * Uᵀ * F).rank = U.rank
    rw [hrank, hUr]

theorem selfAdjoint_factorization_pair_unique (hFsymm : Fᵀ = F) (hF : IsUnit F)
    {U₁ U₂ : Matrix (Fin n) (Fin k) K} {S₁ S₂ : Matrix (Fin k) (Fin k) K}
    (hU₁ : U₁ᵀ.IsReducedRowEchelon)
    (hU₂ : U₂ᵀ.IsReducedRowEchelon) (hr₁ : U₁.rank = k) (hr₂ : U₂.rank = k) (hS₁ : IsUnit S₁)
    (hS₁s : S₁ᵀ = S₁) (hS₂ : IsUnit S₂) (hS₂s : S₂ᵀ = S₂)
    (h : U₁ * S₁ * U₁ᵀ * F = U₂ * S₂ * U₂ᵀ * F) : U₁ = U₂ ∧ S₁ = S₂ := by
  obtain ⟨p₁, hp₁, hp₁1⟩ := exists_pivots_of_rank hU₁ hr₁
  obtain ⟨p₂, hp₂, -⟩ := exists_pivots_of_rank hU₂ hr₂
  have hrange : LinearMap.range U₁.mulVecLin = LinearMap.range U₂.mulVecLin := by
    rw [← (selfAdjoint_factorization_converse hFsymm hF hU₁ hr₁ hS₁ hS₁s).2.2, h,
      (selfAdjoint_factorization_converse hFsymm hF hU₂ hr₂ hS₂ hS₂s).2.2]
  have hU : U₁ = U₂ := by
    refine transpose_inj.mp (rref_unique hU₁ hU₂ hp₁ hp₂ ?_)
    change Submodule.span K (Set.range U₁.col) = Submodule.span K (Set.range U₂.col)
    rw [← range_mulVecLin, ← range_mulVecLin, hrange]
  rw [← hU] at h
  exact ⟨hU, (eq_submatrix_of_eq_mul (E := U₁ * S₁ * U₁ᵀ * F) hF hp₁1 rfl).trans
    (eq_submatrix_of_eq_mul hF hp₁1 h).symm⟩

theorem selfAdjoint_factorization_conj {gm gi : Matrix (Fin n) (Fin n) K} (h1 : gm * gi = 1)
    (hg : gmᵀ * F * gm = F) {U : Matrix (Fin n) (Fin k) K} (hUr : U.rank = k)
    {S : Matrix (Fin k) (Fin k) K} (hE : E = U * S * Uᵀ * F) {U' : Matrix (Fin n) (Fin k) K}
    (hU' : U'ᵀ.IsReducedRowEchelon)
    (hU'W : LinearMap.range U'.mulVecLin = LinearMap.range (gm * U).mulVecLin)
    {p' : Fin k → Fin n} (hp' : ∀ i, U'ᵀ.IsLeadingEntry i (p' i)) :
    IsUnit ((gm * U).submatrix p' id) ∧ U' = gm * U * ((gm * U).submatrix p' id)⁻¹ ∧
      gm * E * gi = U' * ((gm * U).submatrix p' id * S * ((gm * U).submatrix p' id)ᵀ) * U'ᵀ * F
      := by
  have hp'1 : U'.submatrix p' id = 1 := by
    rw [← transpose_transpose (U'.submatrix p' id), transpose_submatrix,
      submatrix_pivot_eq_one hU' hp', transpose_one]
  obtain ⟨H, hH⟩ := exists_mul_eq_of_range_le hU'W.ge
  have hP : (gm * U).submatrix p' id = H := by
    rw [← hH, submatrix_mul_id, hp'1, Matrix.one_mul]
  rw [hP]
  have hWr : (gm * U).rank = k := by
    rw [rank_mul_eq_right_of_isUnit_det _ _ (isUnit_det_of_right_inverse h1), hUr]
  have hHu : IsUnit H := by
    refine isUnit_of_rank_eq (le_antisymm (rank_le_width _) ?_)
    calc k = (gm * U).rank := hWr.symm
      _ = (U' * H).rank := by rw [hH]
      _ ≤ H.rank := rank_mul_le_right _ _
  have hHdet := (isUnit_iff_isUnit_det H).mp hHu
  refine ⟨hHu, ?_, ?_⟩
  · rw [← hH, Matrix.mul_assoc, mul_nonsing_inv _ hHdet, Matrix.mul_one]
  · have hFgi : F * gi = gmᵀ * F := (transpose_mul_eq_mul_inv h1 hg).symm
    calc gm * E * gi = gm * U * S * (gm * U)ᵀ * F := by
          rw [hE, transpose_mul]
          simp only [Matrix.mul_assoc]
          rw [hFgi]
      _ = U' * (H * S * Hᵀ) * U'ᵀ * F := by
          rw [← hH, transpose_mul]
          simp only [Matrix.mul_assoc]

theorem canonical_selfadjoint_rank_factorization {F : Matrix (Fin n) (Fin n) K}
    (hFsymm : Fᵀ = F) (hF : IsUnit F) {E : Matrix (Fin n) (Fin n) K} (hrank : E.rank = k)
    (hEF : Eᵀ * F = F * E) :
    (∃! U : Matrix (Fin n) (Fin k) K, Uᵀ.IsReducedRowEchelon ∧
      Submodule.span K (Set.range U.col) = LinearMap.range E.mulVecLin) ∧
    (∀ U : Matrix (Fin n) (Fin k) K, Uᵀ.IsReducedRowEchelon →
      Submodule.span K (Set.range U.col) = LinearMap.range E.mulVecLin →
        (∃ p : Fin k → Fin n, ∀ i, Uᵀ.IsLeadingEntry i (p i)) ∧
        ∀ p : Fin k → Fin n, (∀ i, Uᵀ.IsLeadingEntry i (p i)) →
          StrictMono p ∧ U.submatrix p id = 1 ∧
          (∃! S : Matrix (Fin k) (Fin k) K, IsUnit S ∧ Sᵀ = S ∧ E = U * S * Uᵀ * F) ∧
          IsUnit ((E * F⁻¹).submatrix p p) ∧
          ((E * F⁻¹).submatrix p p)ᵀ = (E * F⁻¹).submatrix p p ∧
          E = U * (E * F⁻¹).submatrix p p * Uᵀ * F) ∧
    (∀ (U : Matrix (Fin n) (Fin k) K) (S : Matrix (Fin k) (Fin k) K), U.rank = k →
      Uᵀ.IsReducedRowEchelon → IsUnit S → Sᵀ = S →
        (U * S * Uᵀ * F).rank = k ∧ (U * S * Uᵀ * F)ᵀ * F = F * (U * S * Uᵀ * F)) ∧
    (∀ (U₁ U₂ : Matrix (Fin n) (Fin k) K) (S₁ S₂ : Matrix (Fin k) (Fin k) K),
      U₁.rank = k → U₁ᵀ.IsReducedRowEchelon → IsUnit S₁ → S₁ᵀ = S₁ →
      U₂.rank = k → U₂ᵀ.IsReducedRowEchelon → IsUnit S₂ → S₂ᵀ = S₂ →
        U₁ * S₁ * U₁ᵀ * F = U₂ * S₂ * U₂ᵀ * F → U₁ = U₂ ∧ S₁ = S₂) ∧
    ∀ g : GL (Fin n) K,
      (g : Matrix (Fin n) (Fin n) K)ᵀ * F * (g : Matrix (Fin n) (Fin n) K) = F →
      ∀ (U : Matrix (Fin n) (Fin k) K) (S : Matrix (Fin k) (Fin k) K),
        Uᵀ.IsReducedRowEchelon →
        Submodule.span K (Set.range U.col) = LinearMap.range E.mulVecLin →
        IsUnit S → Sᵀ = S → E = U * S * Uᵀ * F →
        ∀ W : Matrix (Fin n) (Fin k) K, W = (g : Matrix (Fin n) (Fin n) K) * U →
          (∃! U' : Matrix (Fin n) (Fin k) K, U'ᵀ.IsReducedRowEchelon ∧
            Submodule.span K (Set.range U'.col) = LinearMap.range W.mulVecLin) ∧
          ∀ U' : Matrix (Fin n) (Fin k) K, U'ᵀ.IsReducedRowEchelon →
            Submodule.span K (Set.range U'.col) = LinearMap.range W.mulVecLin →
            ∀ p' : Fin k → Fin n, (∀ i, U'ᵀ.IsLeadingEntry i (p' i)) →
              IsUnit (W.submatrix p' id) ∧ U' = W * (W.submatrix p' id)⁻¹ ∧
              (g : Matrix (Fin n) (Fin n) K) * E *
                  ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
                U' * (W.submatrix p' id * S * (W.submatrix p' id)ᵀ) * U'ᵀ * F ∧
              (W.submatrix p' id * S * (W.submatrix p' id)ᵀ)ᵀ =
                W.submatrix p' id * S * (W.submatrix p' id)ᵀ ∧
              IsUnit (W.submatrix p' id * S * (W.submatrix p' id)ᵀ) := by
  have hV : Module.finrank K (LinearMap.range E.mulVecLin) = k := hrank
  have hUspec : ∀ U : Matrix (Fin n) (Fin k) K,
      Submodule.span K (Set.range U.col) = LinearMap.range E.mulVecLin →
        U.rank = k ∧ LinearMap.range U.mulVecLin = LinearMap.range E.mulVecLin := fun U hspan =>
    ⟨by rw [rank_eq_finrank_span_col, hspan, hV], by rw [range_mulVecLin, hspan]⟩
  refine ⟨existsUnique_canonical_basis _ hV, fun U hU hspan => ?_,
    fun U S hUr hU hS hSs => ?_,
    fun U₁ U₂ S₁ S₂ hr₁ hU₁ hS₁ hS₁s hr₂ hU₂ hS₂ hS₂s h =>
      selfAdjoint_factorization_pair_unique hFsymm hF hU₁ hU₂ hr₁ hr₂ hS₁ hS₁s hS₂ hS₂s h,
    fun g hg U S hU hspan hS hSs hE W hW => ?_⟩
  · obtain ⟨hUr, hUE⟩ := hUspec U hspan
    refine ⟨(exists_pivots_of_rank hU hUr).imp fun p hp => hp.1, fun p hp => ?_⟩
    have hp1 : U.submatrix p id = 1 := by
      rw [← transpose_transpose (U.submatrix p id), transpose_submatrix,
        submatrix_pivot_eq_one hU hp, transpose_one]
    obtain ⟨hSsymm, hSunit, hEU⟩ := selfAdjoint_factorization_spec hFsymm hF hrank hEF hp1 hUE
    exact ⟨strictMono_pivot hU.isRowEchelon hp, hp1, ⟨_, ⟨hSunit, hSsymm, hEU⟩,
      fun S' hS' => eq_submatrix_of_eq_mul hF hp1 hS'.2.2⟩, hSunit, hSsymm, hEU⟩
  · obtain ⟨h1, h2, -⟩ := selfAdjoint_factorization_converse hFsymm hF hU hUr hS hSs
    exact ⟨h1, h2⟩
  · subst hW
    obtain ⟨hUr, -⟩ := hUspec U hspan
    have h1 : (g : Matrix (Fin n) (Fin n) K) *
        ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hWr : ((g : Matrix (Fin n) (Fin n) K) * U).rank = k := by
      rw [rank_mul_eq_right_of_isUnit_det _ _ (isUnit_det_of_right_inverse h1), hUr]
    refine ⟨existsUnique_canonical_basis _ hWr, fun U' hU' hU'span p' hp' => ?_⟩
    have hU'W : LinearMap.range U'.mulVecLin =
        LinearMap.range ((g : Matrix (Fin n) (Fin n) K) * U).mulVecLin := by
      rw [range_mulVecLin, hU'span]
    obtain ⟨hPu, hU'eq, hconj⟩ := selfAdjoint_factorization_conj h1 hg hUr hE hU' hU'W hp'
    refine ⟨hPu, hU'eq, hconj, ?_, (hPu.mul hS).mul ((isUnit_transpose _).mpr hPu)⟩
    rw [transpose_mul, transpose_mul, transpose_transpose, hSs, ← Matrix.mul_assoc]

end CFSG.LinearAlgebra
