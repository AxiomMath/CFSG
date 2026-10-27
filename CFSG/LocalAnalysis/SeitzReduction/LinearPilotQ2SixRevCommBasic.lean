module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2RowSeven

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open scoped commutatorElement

section Matrices

variable {n : ℕ} {F : Type*} [Field F]

theorem commute_transvection_of_col_row {M : SpecialLinearGroup (Fin n) F} {i j : Fin n}
    (hij : i ≠ j)
    (hcol : ∀ k, (M : Matrix (Fin n) (Fin n) F) k i = (1 : Matrix (Fin n) (Fin n) F) k i)
    (hrow : ∀ l, (M : Matrix (Fin n) (Fin n) F) j l = (1 : Matrix (Fin n) (Fin n) F) j l)
    (c : F) :
    M * SpecialLinearGroup.transvection hij c = SpecialLinearGroup.transvection hij c * M := by
  apply Subtype.ext
  change (M : Matrix (Fin n) (Fin n) F) *
      ((SpecialLinearGroup.transvection hij c : SpecialLinearGroup (Fin n) F) :
        Matrix (Fin n) (Fin n) F) =
    ((SpecialLinearGroup.transvection hij c : SpecialLinearGroup (Fin n) F) :
      Matrix (Fin n) (Fin n) F) * (M : Matrix (Fin n) (Fin n) F)
  rw [SpecialLinearGroup.transvection_coe, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
    Matrix.one_mul]
  congr 1
  ext k l
  by_cases hl : l = j
  · subst hl
    rw [mul_single_apply_same]
    by_cases hk : k = i
    · subst hk
      rw [single_mul_apply_same, hcol, hrow, Matrix.one_apply_eq, Matrix.one_apply_eq, one_mul,
        mul_one]
    · rw [single_mul_apply_of_ne (h := hk), hcol, Matrix.one_apply_ne hk, zero_mul]
  · rw [mul_single_apply_of_ne (hbj := hl)]
    by_cases hk : k = i
    · subst hk
      rw [single_mul_apply_same, hrow, Matrix.one_apply_ne (Ne.symm hl), mul_zero]
    · rw [single_mul_apply_of_ne (h := hk)]

theorem eq_one_of_ne_zero_of_natCard_two {K : Type*} [Field K] (hK : Nat.card K = 2) {x : K}
    (hx : x ≠ 0) : x = 1 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype K := Fintype.ofFinite K
  have h := FiniteField.pow_card_sub_one_eq_one x hx
  rwa [← Nat.card_eq_fintype_card, hK, show 2 - 1 = 1 from rfl, pow_one] at h

theorem proj_injective_of_card_two {K : Type*} [Field K] (hK : Nat.card K = 2) :
    Function.Injective (LinearFlag.proj n K) := by
  rw [injective_iff_map_eq_one]
  intro A hA
  rw [LinearFlag.proj_eq_one_iff, LinearFlag.mem_scalars] at hA
  obtain ⟨c, -, hc⟩ := hA
  have hc1 : (c : K) = 1 := eq_one_of_ne_zero_of_natCard_two hK c.ne_zero
  apply Subtype.ext
  change (A : Matrix (Fin n) (Fin n) K) = 1
  rw [hc, hc1, map_one]

theorem eq_transvection_of_commute_row_col {K : Type*} [Field K] (hK : Nat.card K = 2)
    {p q : Fin n} (hpq : p ≠ q) {M : SpecialLinearGroup (Fin n) K}
    (h1 : ∀ m (hm : p ≠ m),
      M * SpecialLinearGroup.transvection hm 1 = SpecialLinearGroup.transvection hm 1 * M)
    (h2 : ∀ m (hm : m ≠ q),
      M * SpecialLinearGroup.transvection hm 1 = SpecialLinearGroup.transvection hm 1 * M) :
    M = SpecialLinearGroup.transvection hpq ((M : Matrix (Fin n) (Fin n) K) p q) := by
  have e1 := fun m (hm : p ≠ m) => entries_of_commute_transvection hm (h1 m hm)
  have e2 := fun m (hm : m ≠ q) => entries_of_commute_transvection hm (h2 m hm)
  have hpp : (M : Matrix (Fin n) (Fin n) K) p p = 1 := by
    apply eq_one_of_ne_zero_of_natCard_two hK
    intro h0
    have hrow : ∀ l, (M : Matrix (Fin n) (Fin n) K) q l = 0 := by
      intro l
      by_cases hl : l = q
      · rw [hl, ← (e1 q hpq).2.2, h0]
      · exact (e2 p hpq).2.1 l hl
    have hdet := M.2
    rw [Matrix.det_eq_zero_of_row_eq_zero q hrow] at hdet
    exact zero_ne_one hdet
  have hdiag : ∀ i, (M : Matrix (Fin n) (Fin n) K) i i = 1 := by
    intro i
    by_cases hi : p = i
    · rw [← hi, hpp]
    · rw [← (e1 i hi).2.2, hpp]
  apply Subtype.ext
  ext i j
  rw [SpecialLinearGroup.transvection_coe, Matrix.add_apply, single_apply]
  by_cases hij : i = j
  · subst hij
    rw [hdiag, Matrix.one_apply_eq, ite_eq_right (fun h => absurd (h.1.trans h.2.symm) hpq),
      add_zero]
  · rw [Matrix.one_apply_ne hij, zero_add]
    by_cases hpi : p = i
    · subst hpi
      by_cases hqj : q = j
      · subst hqj
        rw [ite_eq_left ⟨rfl, rfl⟩]
      · rw [ite_eq_right (fun h => hqj h.2)]
        exact (e2 j (Ne.symm hqj)).1 p hij
    · rw [ite_eq_right (fun h => hpi h.1)]
      exact (e1 i hpi).2.1 j (Ne.symm hij)

theorem commute_transvection_of_block_sq (h2 : (2 : F) = 0) {p q : Fin n} (hpq : p ≠ q)
    {Y : SpecialLinearGroup (Fin n) F}
    (hY : Y ∈ blockSpecialLinear (K := F) ({p, q} : Finset (Fin n)))
    (hc : Y * SpecialLinearGroup.transvection hpq 1 = SpecialLinearGroup.transvection hpq 1 * Y)
    (hsq : Y * Y = 1) {m : Fin n} (hmp : m ≠ p) (hmq : m ≠ q) (c : F) :
    Y * SpecialLinearGroup.transvection (Ne.symm hmp) c =
        SpecialLinearGroup.transvection (Ne.symm hmp) c * Y ∧
      Y * SpecialLinearGroup.transvection hmq c = SpecialLinearGroup.transvection hmq c * Y := by
  obtain ⟨hcolp, hrowq, hpq'⟩ := entries_of_commute_transvection hpq hc
  have hpp : (Y : Matrix (Fin n) (Fin n) F) p p = 1 := by
    have hsq' : ((Y * Y : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) p p = 1 := by
      rw [hsq]
      exact Matrix.one_apply_eq p
    rw [coe_mul_specialLinear, Matrix.mul_apply, Finset.sum_eq_single p] at hsq'
    · have hx : ((Y : Matrix (Fin n) (Fin n) F) p p + 1) ^ 2 = 0 := by
        linear_combination hsq' + ((Y : Matrix (Fin n) (Fin n) F) p p) * h2 + h2
      have hx1 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hx
      linear_combination hx1 - h2
    · intro k _ hk
      rw [hcolp k hk, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ p) h
  have hmN : m ∉ ({p, q} : Finset (Fin n)) := by simp [hmp, hmq]
  have hcolp' : ∀ k, (Y : Matrix (Fin n) (Fin n) F) k p = (1 : Matrix (Fin n) (Fin n) F) k p := by
    intro k
    by_cases hk : k = p
    · rw [hk, hpp, Matrix.one_apply_eq]
    · rw [hcolp k hk, Matrix.one_apply_ne hk]
  have hrowq' : ∀ l, (Y : Matrix (Fin n) (Fin n) F) q l = (1 : Matrix (Fin n) (Fin n) F) q l := by
    intro l
    by_cases hl : l = q
    · rw [hl, ← hpq', hpp, Matrix.one_apply_eq]
    · rw [hrowq l hl, Matrix.one_apply_ne (Ne.symm hl)]
  exact ⟨commute_transvection_of_col_row (Ne.symm hmp) hcolp' (fun l => hY m l (Or.inl hmN)) c,
    commute_transvection_of_col_row hmq (fun k => hY k m (Or.inr hmN)) hrowq' c⟩

end Matrices

theorem commutatorElement_mul_right_mul_right_of_commute {H : Type*} [Group H] {a b w₁ w₂ : H}
    (h1b : Commute w₁ b) (h2a : Commute w₂ a) (h12 : Commute w₁ w₂) :
    ⁅a * w₁, b * w₂⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  calc a * w₁ * (b * w₂) * (a * w₁)⁻¹ * (b * w₂)⁻¹
      = a * (w₁ * b) * w₂ * w₁⁻¹ * a⁻¹ * w₂⁻¹ * b⁻¹ := by group
    _ = a * (b * w₁) * w₂ * w₁⁻¹ * a⁻¹ * w₂⁻¹ * b⁻¹ := by rw [h1b.eq]
    _ = a * b * (w₁ * w₂) * w₁⁻¹ * a⁻¹ * w₂⁻¹ * b⁻¹ := by group
    _ = a * b * (w₂ * w₁) * w₁⁻¹ * a⁻¹ * w₂⁻¹ * b⁻¹ := by rw [h12.eq]
    _ = a * b * (w₂ * a⁻¹) * w₂⁻¹ * b⁻¹ := by group
    _ = a * b * (a⁻¹ * w₂) * w₂⁻¹ * b⁻¹ := by rw [h2a.inv_right.eq]
    _ = a * b * a⁻¹ * b⁻¹ := by group

section Param

variable {G : Type*} [Group G] {L : Subgroup G} {n : ℕ} {K : Type*} [Field K] {F : Type*}
  [Field F]

theorem conj_fieldParam_transvection {e : L ≃* LinearFlag.projectiveSL n K} {t : G} {ι : K →+* F}
    {σ : F ≃+* F} {X : Subgroup G} {N : Finset (Fin n)} (P : FieldNeighbourParam e t ι σ X N)
    {p q : Fin n} (hpq : p ≠ q) (hp : p ∈ N) (hq : q ∈ N) {s : F} {k : K}
    (hk : σ s = s + ι k) :
    t * P.Φ ⟨SpecialLinearGroup.transvection hpq s,
        transvection_mem_blockSpecialLinear hpq hp hq s⟩ * t⁻¹ =
      P.Φ ⟨SpecialLinearGroup.transvection hpq s,
        transvection_mem_blockSpecialLinear hpq hp hq s⟩ *
        ((e.symm (LinearFlag.proj n K (SpecialLinearGroup.transvection hpq k)) : L) : G) := by
  rw [P.N3]
  have h1 : mapBlock σ N ⟨SpecialLinearGroup.transvection hpq s,
      transvection_mem_blockSpecialLinear hpq hp hq s⟩ =
      ⟨SpecialLinearGroup.transvection hpq s, transvection_mem_blockSpecialLinear hpq hp hq s⟩ *
        ⟨SpecialLinearGroup.transvection hpq (ι k),
          transvection_mem_blockSpecialLinear hpq hp hq (ι k)⟩ := by
    apply Subtype.ext
    rw [coe_mapBlock_apply, Subgroup.coe_mul, SpecialLinearGroup.map_transvection,
      ← SpecialLinearGroup.transvection_add]
    exact congrArg _ hk
  rw [h1, map_mul, ← P.N1 ⟨SpecialLinearGroup.transvection hpq k,
    transvection_mem_blockSpecialLinear hpq hp hq k⟩]
  congr 2
  exact Subtype.ext (SpecialLinearGroup.map_transvection ι hpq k).symm

theorem commute_map_of_commute {e : L ≃* LinearFlag.projectiveSL n K} {t : G} {ι : K →+* F}
    {σ : F ≃+* F} {X : Subgroup G} {N : Finset (Fin n)} (P : FieldNeighbourParam e t ι σ X N)
    {x : blockSpecialLinear (K := F) N} {g : SpecialLinearGroup (Fin n) K}
    (hg : g ∈ blockSpecialLinear (K := K) N)
    (hxg : (x : SpecialLinearGroup (Fin n) F) * SpecialLinearGroup.map ι g =
      SpecialLinearGroup.map ι g * x) :
    P.Φ x * ((e.symm (LinearFlag.proj n K g) : L) : G) =
      ((e.symm (LinearFlag.proj n K g) : L) : G) * P.Φ x := by
  rw [← P.N1 ⟨g, hg⟩, ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext hxg

theorem map_le_map_of_disjoint_roots_of_perfect [Finite G] [Finite F]
    (e : L ≃* LinearFlag.projectiveSL n K) {t : G} {ι : K →+* F} {σ : F ≃+* F}
    {Xr : Fin n → Fin n → Subgroup (LinearFlag.projectiveSL n K)}
    (hXr : ∀ a b, Xr a b ≤ rootSL2 a b)
    (hXy : ∀ (a b : Fin n) (hab : a ≠ b), order3Elt K hab ∈ Xr a b)
    (P : ∀ a b : Fin n, a ≠ b →
      FieldNeighbourParam e t ι σ (modelToG e (Xr a b)) ({a, b}ᶜ : Finset (Fin n)))
    {a b c d : Fin n} (hab : a ≠ b) (hcd : c ≠ d) (h1 : Disjoint ({a, b} : Finset (Fin n)) {c, d})
    (hperf : ⁅blockSpecialLinear (K := F) (({a, b}ᶜ : Finset (Fin n)) \ {c, d}),
      blockSpecialLinear (K := F) (({a, b}ᶜ : Finset (Fin n)) \ {c, d})⁆ =
        blockSpecialLinear (K := F) (({a, b}ᶜ : Finset (Fin n)) \ {c, d})) :
    ((blockSpecialLinear (K := F) (({a, b}ᶜ : Finset (Fin n)) \ {c, d})).subgroupOf
      (blockSpecialLinear ({a, b}ᶜ : Finset (Fin n)))).map (P a b hab).Φ ≤
    ((blockSpecialLinear (K := F) (({c, d}ᶜ : Finset (Fin n)) \ {a, b})).subgroupOf
      (blockSpecialLinear ({c, d}ᶜ : Finset (Fin n)))).map (P c d hcd).Φ := by
  have hMN : (({a, b}ᶜ : Finset (Fin n)) \ {c, d}) ⊆ ({a, b}ᶜ : Finset (Fin n)) :=
    Finset.sdiff_subset
  have hcdN : ({c, d} : Finset (Fin n)) ⊆ ({a, b}ᶜ : Finset (Fin n)) :=
    Finset.subset_compl_iff_disjoint_right.2 h1.symm
  have habN : ({a, b} : Finset (Fin n)) ⊆ ({c, d}ᶜ : Finset (Fin n)) :=
    Finset.subset_compl_iff_disjoint_right.2 h1
  refine le_trans (b := centralizerPerfectCore (modelToG e (Xr a b) ⊔ modelToG e (Xr c d))) ?_ ?_
  · refine F4Pilot.le_centralizerPerfectCore (by
      rw [← map_commutator, commutator_subgroupOf_eq_self (blockSpecialLinear_mono hMN) hperf]) ?_
    rw [le_centralizer_iff]
    refine sup_le ?_ ?_
    · rw [← le_centralizer_iff]
      exact (map_le_range _ _).trans ((P a b hab).range_eq.le.trans
        (F4Pilot.centralizerPerfectCore_le_centralizer _))
    · refine (modelToG_mono e ((hXr c d).trans le_rfl)).trans ?_
      refine (modelToG_blockSL_le_map (P a b hab) hcdN).trans ?_
      exact map_le_centralizer_map_of_disjoint _ Finset.disjoint_sdiff
  · exact centralizerPerfectCore_le_map_of_order3_pair (P c d hcd) hab (habN (by simp))
      (habN (by simp)) le_sup_right (mem_sup_left (symm_mem_modelToG e (hXy a b hab)))

end Param

end CFSG.SeitzReduction.LinearPilot
