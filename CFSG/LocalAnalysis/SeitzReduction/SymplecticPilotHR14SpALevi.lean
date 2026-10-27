module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14SpARadicalComm
public import CFSG.ClassicalGroups.Symplectic.ProjectivePerfect

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective mat_apply)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (upperUnipotentSp)

variable {K : Type} [Field K] {n j : ℕ}

section Index

variable (hjn : 2 * j ≤ n)

@[expose] def spAIndexEquiv : (Fin j ⊕ Fin j) ⊕ Fin (n - 2 * j) ≃ Fin n where
  toFun := Sum.elim (Sum.elim (fun i => ⟨2 * i.val, by have := i.isLt; omega⟩)
    (fun i => ⟨2 * i.val + 1, by have := i.isLt; omega⟩))
    (fun m => ⟨2 * j + m.val, by have := m.isLt; omega⟩)
  invFun k := if h : k.val < 2 * j then
      (if k.val % 2 = 0 then Sum.inl (Sum.inl ⟨k.val / 2, by omega⟩)
        else Sum.inl (Sum.inr ⟨k.val / 2, by omega⟩))
    else Sum.inr ⟨k.val - 2 * j, by have := k.isLt; omega⟩
  left_inv := by
    rintro ((i | i) | m)
    · have h1 : 2 * i.val < 2 * j := by have := i.isLt; omega
      simp [h1]
    · have h1 : 2 * i.val + 1 < 2 * j := by have := i.isLt; omega
      simp [h1, Fin.ext_iff]
      omega
    · simp
  right_inv k := by
    by_cases h : k.val < 2 * j
    · by_cases h2 : k.val % 2 = 0
      · simp [h, h2, Fin.ext_iff]
        omega
      · simp [h, h2, Fin.ext_iff]
        omega
    · simp [h, Fin.ext_iff]
      omega

theorem spAIndexEquiv_inl_lt (r : Fin j ⊕ Fin j) : (spAIndexEquiv hjn (Sum.inl r)).val < 2 * j := by
  rcases r with i | i
  · simp [spAIndexEquiv]
  · simp [spAIndexEquiv]
    omega

theorem spAIndexEquiv_inr_val (m : Fin (n - 2 * j)) :
    (spAIndexEquiv hjn (Sum.inr m)).val = 2 * j + m.val := rfl

theorem spAIndexEquiv_symm_of_lt {k : Fin n} (hk : k.val < 2 * j) :
    ∃ r, (spAIndexEquiv hjn).symm k = Sum.inl r := by
  rcases h : (spAIndexEquiv hjn).symm k with r | m
  · exact ⟨r, rfl⟩
  · have := spAIndexEquiv_inr_val hjn m
    rw [← h, Equiv.apply_symm_apply] at this
    omega

theorem spAIndexEquiv_symm_of_ge {k : Fin n} (hk : 2 * j ≤ k.val) :
    ∃ m, (spAIndexEquiv hjn).symm k = Sum.inr m := by
  rcases h : (spAIndexEquiv hjn).symm k with r | m
  · have := spAIndexEquiv_inl_lt hjn r
    rw [← h, Equiv.apply_symm_apply] at this
    omega
  · exact ⟨m, rfl⟩

end Index

section Spread

variable (hjn : 2 * j ≤ n)

@[expose] def spASpread (x : Matrix (Fin j ⊕ Fin j) (Fin j ⊕ Fin j) K) :
    Matrix (Fin n) (Fin n) K :=
  (fromBlocks x 0 0 1).submatrix (spAIndexEquiv hjn).symm (spAIndexEquiv hjn).symm

theorem spASpread_mul (x y : Matrix (Fin j ⊕ Fin j) (Fin j ⊕ Fin j) K) :
    spASpread hjn (x * y) = spASpread hjn x * spASpread hjn y := by
  rw [spASpread, spASpread, spASpread, submatrix_mul_equiv, fromBlocks_multiply]
  simp

theorem spASpread_one : spASpread hjn (1 : Matrix (Fin j ⊕ Fin j) (Fin j ⊕ Fin j) K) = 1 := by
  rw [spASpread, fromBlocks_one, submatrix_one_equiv]

@[expose] def spASpreadHom :
    Matrix (Fin j ⊕ Fin j) (Fin j ⊕ Fin j) K →* Matrix (Fin n) (Fin n) K where
  toFun := spASpread hjn
  map_one' := spASpread_one hjn
  map_mul' := spASpread_mul hjn

theorem spASpread_injective : Function.Injective (spASpread (K := K) hjn) := by
  intro x y h
  have h' := congrArg (fun M => M.submatrix (spAIndexEquiv hjn) (spAIndexEquiv hjn)) h
  simp only [spASpread, submatrix_submatrix, Equiv.symm_comp_self, submatrix_id_id] at h'
  exact (fromBlocks_inj.1 h').1

theorem spASpread_apply_eq_zero (x : Matrix (Fin j ⊕ Fin j) (Fin j ⊕ Fin j) K) {k l : Fin n}
    (h : ¬ (k.val < 2 * j ↔ l.val < 2 * j)) : spASpread hjn x k l = 0 := by
  rw [spASpread, submatrix_apply]
  by_cases hk : k.val < 2 * j
  · obtain ⟨r, hr⟩ := spAIndexEquiv_symm_of_lt hjn hk
    obtain ⟨m, hm⟩ := spAIndexEquiv_symm_of_ge hjn (k := l)
      (by by_contra hl; exact h ⟨fun _ => by omega, fun _ => hk⟩)
    rw [hr, hm, fromBlocks_apply₁₂, Matrix.zero_apply]
  · obtain ⟨m, hm⟩ := spAIndexEquiv_symm_of_ge hjn (k := k) (by omega)
    obtain ⟨r, hr⟩ := spAIndexEquiv_symm_of_lt hjn (k := l)
      (by by_contra hl; exact h ⟨fun h' => absurd h' hk, fun h' => absurd h' hl⟩)
    rw [hr, hm, fromBlocks_apply₂₁, Matrix.zero_apply]

theorem spARepMat_eq_submatrix [CharP K 2] :
    (spARepMat n j : Matrix (Fin n) (Fin n) K) =
      (fromBlocks (CFSG.ClassicalInvolution.Models.SymplecticPairs.gram K j) 0 0 0).submatrix
        (spAIndexEquiv hjn).symm (spAIndexEquiv hjn).symm := by
  ext k l
  rw [submatrix_apply, spARepMat, of_apply]
  by_cases hk : k.val < 2 * j
  · by_cases hl : l.val < 2 * j
    · have ek : (spAIndexEquiv hjn).symm k = if k.val % 2 = 0 then
          Sum.inl (Sum.inl ⟨k.val / 2, by omega⟩) else Sum.inl (Sum.inr ⟨k.val / 2, by omega⟩) := by
        simp [spAIndexEquiv, hk]
      have el : (spAIndexEquiv hjn).symm l = if l.val % 2 = 0 then
          Sum.inl (Sum.inl ⟨l.val / 2, by omega⟩) else Sum.inl (Sum.inr ⟨l.val / 2, by omega⟩) := by
        simp [spAIndexEquiv, hl]
      have hne : k ≠ l ↔ k.val ≠ l.val := ⟨fun h h' => h (Fin.ext h'), fun h h' => h (h' ▸ rfl)⟩
      rw [ek, el]
      by_cases hk2 : k.val % 2 = 0 <;> by_cases hl2 : l.val % 2 = 0 <;>
        simp only [hk2, hl2, ↓reduceIte, fromBlocks_apply₁₁,
          CFSG.ClassicalInvolution.Models.SymplecticPairs.gram_apply, par_inl, par_inr,
          sgn_inl, sgn_inr, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, Fin.mk.injEq,
          CharTwo.neg_eq, hne] <;>
        split_ifs <;> first | rfl | omega
    · obtain ⟨m, hm⟩ := spAIndexEquiv_symm_of_ge hjn (k := l) (by omega)
      rw [hm, ite_eq_right (fun h => hl h.2.2.2)]
      rcases (spAIndexEquiv hjn).symm k with r | r <;> simp
  · obtain ⟨m, hm⟩ := spAIndexEquiv_symm_of_ge hjn (k := k) (by omega)
    rw [hm, ite_eq_right (fun h => hk h.2.2.1)]
    rcases (spAIndexEquiv hjn).symm l with r | r <;> simp

end Spread

section Transpose

theorem spA_mat_mul_gram_mul_transpose {m : ℕ} (x : StatedSp m K) :
    mat m K x * gram K m * (mat m K x)ᵀ = gram K m := by
  have h := mat_transpose_mul_gram_mul x
  rw [gram_eq_neg_J] at h ⊢
  have h' : (mat m K x)ᵀ * Matrix.J (Fin m) K * mat m K x = Matrix.J (Fin m) K := by
    have := congrArg Neg.neg h
    simpa [Matrix.mul_neg, Matrix.neg_mul] using this
  have h2 := SymplecticGroup.mem_iff.1 (SymplecticGroup.mem_iff'.2 h')
  rw [Matrix.mul_neg, Matrix.neg_mul, h2]

theorem spA_transpose_mul_gram_mul_of {m : ℕ} {x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K}
    (hx : x * gram K m * xᵀ = gram K m) : xᵀ * gram K m * x = gram K m ∧ IsUnit x.det := by
  rw [gram_eq_neg_J] at hx ⊢
  have h' : x * Matrix.J (Fin m) K * xᵀ = Matrix.J (Fin m) K := by
    have := congrArg Neg.neg hx
    simpa [Matrix.mul_neg, Matrix.neg_mul] using this
  have hm := SymplecticGroup.mem_iff.2 h'
  refine ⟨?_, SymplecticGroup.symplectic_det hm⟩
  rw [Matrix.mul_neg, Matrix.neg_mul, SymplecticGroup.mem_iff'.1 hm]

end Transpose

section LeviOne

variable (hjn : 2 * j ≤ n)

@[expose] noncomputable def spALeviOne : StatedSp j K →* StatedSp n K :=
  (leviEmbedGL K n).comp ((Units.map (spASpreadHom (K := K) hjn)).comp (StatedSp j K).subtype)

theorem mat_spALeviOne (x : StatedSp j K) :
    mat n K (spALeviOne hjn x) =
      fromBlocks (spASpread hjn (mat j K x)) 0 0 (spASpread hjn (mat j K x⁻¹))ᵀ := by
  rw [spALeviOne, MonoidHom.comp_apply, mat_leviEmbedGL]
  rfl

theorem spALeviOne_injective : Function.Injective (spALeviOne (K := K) hjn) := by
  intro x y h
  have h' := congrArg (mat n K) h
  rw [mat_spALeviOne, mat_spALeviOne, fromBlocks_inj] at h'
  exact mat_injective (spASpread_injective hjn h'.1)

theorem spALeviOne_mem_centralizer [CharP K 2] (x : StatedSp j K) :
    spALeviOne hjn x ∈ centralizer ({spARep n j} : Set (StatedSp n K)) := by
  rw [spALeviOne, MonoidHom.comp_apply]
  refine leviEmbedGL_mem_centralizer_spARep ?_
  show spASpread hjn (mat j K x) * spARepMat n j * (spASpread hjn (mat j K x))ᵀ = spARepMat n j
  rw [spARepMat_eq_submatrix hjn, spASpread, transpose_submatrix, submatrix_mul_equiv,
    submatrix_mul_equiv, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply]
  simp [spA_mat_mul_gram_mul_transpose]

theorem spALeviPart_fromBlocks {A D : Matrix (Fin n) (Fin n) K}
    (hA : ∀ k l : Fin n, ¬ (k.val < 2 * j ↔ l.val < 2 * j) → A k l = 0)
    (hD : ∀ k l : Fin n, ¬ (k.val < 2 * j ↔ l.val < 2 * j) → D k l = 0) :
    spALeviPart j (fromBlocks A 0 0 D) = fromBlocks A 0 0 D := by
  ext r t
  rw [spALeviPart_apply]
  split_ifs with h
  · rfl
  · rcases r with k | k <;> rcases t with l | l
    · rw [fromBlocks_apply₁₁, hA k l (fun hkl => h (by
        simp only [spABlk_inl]; by_cases hk : k.val < 2 * j
        · rw [ite_eq_left hk, ite_eq_left (hkl.1 hk)]
        · rw [ite_eq_right hk, ite_eq_right (fun hl => hk (hkl.2 hl))]))]
    · rfl
    · rfl
    · rw [fromBlocks_apply₂₂, hD k l (fun hkl => h (by
        simp only [spABlk_inr]; by_cases hk : k.val < 2 * j
        · rw [ite_eq_left hk, ite_eq_left (hkl.1 hk)]
        · rw [ite_eq_right hk, ite_eq_right (fun hl => hk (hkl.2 hl))]))]

theorem mem_range_spALeviHom_of {g : StatedSp n K}
    (hg : g ∈ centralizer ({spARep n j} : Set (StatedSp n K)))
    (hL : spALeviPart j (mat n K g) = mat n K g) : g ∈ (spALeviHom hjn).range :=
  ⟨⟨g, hg⟩, mat_injective (by rw [mat_spALeviHom]; exact hL)⟩

theorem spALeviOne_mem_range [CharP K 2] (x : StatedSp j K) :
    spALeviOne hjn x ∈ (spALeviHom hjn).range := by
  refine mem_range_spALeviHom_of hjn (spALeviOne_mem_centralizer hjn x) ?_
  rw [mat_spALeviOne]
  exact spALeviPart_fromBlocks (fun k l h => spASpread_apply_eq_zero hjn _ h)
    (fun k l h => by
      rw [transpose_apply]
      exact spASpread_apply_eq_zero hjn _ (fun h' => h h'.symm))

end LeviOne

section LeviTwo

variable (n j) in
@[expose] def spAMidPlane (m : Fin (n - 2 * j)) : Fin n :=
  ⟨2 * j + m.val, by have := m.isLt; omega⟩

theorem spAMidPlane_injective : Function.Injective (spAMidPlane n j) := fun a b h =>
  Fin.ext (by have := congrArg Fin.val h; simp only [spAMidPlane] at this; omega)

variable (K n j) in
@[expose] noncomputable def spALeviTwo : StatedSp (n - 2 * j) K →* StatedSp n K :=
  spEmbed (spAMidPlane n j) spAMidPlane_injective

theorem mem_range_sumMap_spAMidPlane {r : Fin n ⊕ Fin n} :
    r ∈ Set.range (Sum.map (spAMidPlane n j) (spAMidPlane n j)) ↔ spABlk j r = 2 := by
  constructor
  · rintro ⟨m | m, rfl⟩ <;> simp [spAMidPlane]
  · intro h
    rcases r with k | k
    · have hk : 2 * j ≤ k.val := by
        by_contra hk
        simp [show k.val < 2 * j by omega] at h
      exact ⟨Sum.inl ⟨k.val - 2 * j, by omega⟩, by
        simp only [Sum.map_inl, Sum.inl.injEq]
        exact Fin.ext (by simp [spAMidPlane]; omega)⟩
    · have hk : 2 * j ≤ k.val := by
        by_contra hk
        simp [show k.val < 2 * j by omega] at h
      exact ⟨Sum.inr ⟨k.val - 2 * j, by omega⟩, by
        simp only [Sum.map_inr, Sum.inr.injEq]
        exact Fin.ext (by simp [spAMidPlane]; omega)⟩

theorem spALeviTwo_injective : Function.Injective (spALeviTwo K n j) :=
  spEmbed_injective spAMidPlane_injective

theorem isSupp_spALeviTwo (y : StatedSp (n - 2 * j) K) :
    CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.IsSupp {r | spABlk j r = 2}
      (mat n K (spALeviTwo K n j y)) := by
  intro r t h
  apply isSupp_spEmbed spAMidPlane_injective y r t
  rintro ⟨hr, ht⟩
  rcases h with h | h
  · exact h (mem_range_sumMap_spAMidPlane.1 hr)
  · exact h (mem_range_sumMap_spAMidPlane.1 ht)

theorem isSupp_spARep :
    CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.IsSupp {r | spABlk j r ≠ 2}
      (mat n K (spARep n j)) := by
  intro r t h
  rw [mat_spARep_eq, Matrix.add_apply, add_eq_left, spANil]
  simp only [Set.mem_ofPred_eq, not_not] at h
  rcases r with k | k <;> rcases t with l | l
  · rfl
  · rw [fromBlocks_apply₁₂, spARepMat, of_apply, ite_eq_right]
    rintro ⟨-, -, hk, hl⟩
    rcases h with h | h <;> simp [hk, hl] at h
  · rfl
  · rfl

theorem spALeviTwo_mem_centralizer (y : StatedSp (n - 2 * j) K) :
    spALeviTwo K n j y ∈ centralizer ({spARep n j} : Set (StatedSp n K)) := by
  rw [mem_centralizer_singleton_iff]
  apply mat_injective
  rw [map_mul, map_mul]
  exact ((isSupp_spALeviTwo y).commute isSupp_spARep
    (Set.disjoint_left.2 fun r hr hr' => hr' hr)).eq

variable (hjn : 2 * j ≤ n) in
theorem spALeviTwo_mem_range (y : StatedSp (n - 2 * j) K) :
    spALeviTwo K n j y ∈ (spALeviHom hjn).range := by
  refine mem_range_spALeviHom_of hjn (spALeviTwo_mem_centralizer y) ?_
  ext r t
  rw [spALeviPart_apply]
  split_ifs with h
  · rfl
  · have hrt : ¬ (r ∈ Set.range (Sum.map (spAMidPlane n j) (spAMidPlane n j)) ∧
        t ∈ Set.range (Sum.map (spAMidPlane n j) (spAMidPlane n j))) := fun h' =>
      h (by rw [mem_range_sumMap_spAMidPlane.1 h'.1, mem_range_sumMap_spAMidPlane.1 h'.2])
    have e1 : mat n K (spALeviTwo K n j y) r t =
        (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) r t :=
      isSupp_spEmbed spAMidPlane_injective y r t hrt
    rw [e1, Matrix.one_apply_ne (fun e => h (by rw [e]))]

end LeviTwo

section Restrict

@[expose] def spARestrict (p : Fin n ⊕ Fin n → Prop) [DecidablePred p]
    (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
  Matrix.of fun r t =>
    if p r ∧ p t then M r t else (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) r t

variable {p : Fin n ⊕ Fin n → Prop} [DecidablePred p] {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K}

theorem spARestrict_apply_of {r t : Fin n ⊕ Fin n} (hr : p r) (ht : p t) :
    spARestrict p M r t = M r t := by
  rw [spARestrict, of_apply, ite_eq_left ⟨hr, ht⟩]

theorem spARestrict_apply_of_not_left {r : Fin n ⊕ Fin n} (hr : ¬ p r) (t : Fin n ⊕ Fin n) :
    spARestrict p M r t = (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) r t := by
  rw [spARestrict, of_apply, ite_eq_right (fun h => hr h.1)]

theorem spARestrict_apply_of_not_right (r : Fin n ⊕ Fin n) {t : Fin n ⊕ Fin n} (ht : ¬ p t) :
    spARestrict p M r t = (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) r t := by
  rw [spARestrict, of_apply, ite_eq_right (fun h => ht h.2)]

theorem spARestrict_symplectic (hp : ∀ r, p (par r) ↔ p r) (hM : Mᵀ * gram K n * M = gram K n)
    (hblk : ∀ r t, ¬ (p r ↔ p t) → M r t = 0) :
    (spARestrict p M)ᵀ * gram K n * spARestrict p M = gram K n := by
  ext a b
  rw [transpose_mul_gram_mul_apply]
  by_cases ha : p a
  · by_cases hb : p b
    · rw [← congrFun (congrFun hM a) b, transpose_mul_gram_mul_apply]
      refine Finset.sum_congr rfl fun c _ => ?_
      by_cases hc : p c
      · rw [spARestrict_apply_of hc ha, spARestrict_apply_of ((hp c).2 hc) hb]
      · rw [spARestrict_apply_of_not_left hc,
          Matrix.one_apply_ne (fun e : c = a => hc (by rw [e]; exact ha)),
          hblk c a (fun h => hc (h.2 ha)), zero_mul, zero_mul]
    · rw [CFSG.ClassicalInvolution.Models.SymplecticPairs.gram_apply,
        ite_eq_right (fun e => hb (by rw [e]; exact (hp a).2 ha))]
      refine Finset.sum_eq_zero fun c _ => ?_
      by_cases hc : p c
      · rw [spARestrict_apply_of_not_right _ hb,
          Matrix.one_apply_ne (fun e => hb (by rw [← e]; exact (hp c).2 hc)), mul_zero, mul_zero]
      · rw [spARestrict_apply_of_not_left hc,
          Matrix.one_apply_ne (fun e : c = a => hc (by rw [e]; exact ha)),
          zero_mul]
  · by_cases hb : p b
    · rw [CFSG.ClassicalInvolution.Models.SymplecticPairs.gram_apply,
        ite_eq_right (fun e => ha ((hp a).1 (by rw [← e]; exact hb)))]
      refine Finset.sum_eq_zero fun c _ => ?_
      by_cases hc : p c
      · rw [spARestrict_apply_of_not_right _ ha,
          Matrix.one_apply_ne (fun e : c = a => ha (by rw [← e]; exact hc)),
          zero_mul]
      · rw [spARestrict_apply_of_not_left (p := p) (r := par c) (fun h => hc ((hp c).1 h)),
          Matrix.one_apply_ne (fun e => hc ((hp c).1 (by rw [e]; exact hb))), mul_zero, mul_zero]
    · have h1 : ∀ c, spARestrict p M c a = (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) c a :=
        fun c => spARestrict_apply_of_not_right _ ha
      have h2 : ∀ c, spARestrict p M (par c) b =
          (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) (par c) b :=
        fun c => spARestrict_apply_of_not_right _ hb
      simp only [h1, h2]
      rw [← transpose_mul_gram_mul_apply]
      simp

theorem spARestrict_mul (hblk : ∀ r t, ¬ (p r ↔ p t) → M r t = 0) :
    spARestrict p M * spARestrict (fun r => ¬ p r) M = M := by
  ext r t
  rw [Matrix.mul_apply]
  by_cases hr : p r
  · rw [Finset.sum_eq_single t]
    · by_cases ht : p t
      · rw [spARestrict_apply_of hr ht,
          spARestrict_apply_of_not_left (p := fun r => ¬ p r) (not_not.2 ht), Matrix.one_apply_eq,
          mul_one]
      · rw [spARestrict_apply_of_not_right _ ht,
          Matrix.one_apply_ne (fun e : r = t => ht (by rw [← e]; exact hr)),
          zero_mul, hblk r t (fun h => ht (h.1 hr))]
    · intro u _ hu
      by_cases hu' : p u
      · rw [spARestrict_apply_of_not_left (p := fun r => ¬ p r) (not_not.2 hu'),
          Matrix.one_apply_ne hu, mul_zero]
      · rw [spARestrict_apply_of_not_right _ hu',
          Matrix.one_apply_ne (fun e : r = u => hu' (by rw [← e]; exact hr)),
          zero_mul]
    · simp
  · rw [Finset.sum_eq_single r]
    · rw [spARestrict_apply_of_not_left hr, Matrix.one_apply_eq, one_mul]
      by_cases ht : p t
      · rw [spARestrict_apply_of_not_right (p := fun r => ¬ p r) _ (not_not.2 ht),
          Matrix.one_apply_ne (fun e : r = t => hr (by rw [e]; exact ht)),
          hblk r t (fun h => hr (h.2 ht))]
      · rw [spARestrict_apply_of (p := fun r => ¬ p r) hr ht]
    · intro u _ hu
      rw [spARestrict_apply_of_not_left hr, Matrix.one_apply_ne (Ne.symm hu), zero_mul]
    · simp

end Restrict

section Decomp

theorem spABlk_eq_two_of_inr_eq_inl {k l : Fin n}
    (h : spABlk j (Sum.inr k : Fin n ⊕ Fin n) = spABlk j (Sum.inl l)) :
    spABlk j (Sum.inr k : Fin n ⊕ Fin n) = 2 := by
  simp only [spABlk_inr, spABlk_inl] at h ⊢
  by_cases hk : k.val < 2 * j <;> by_cases hl : l.val < 2 * j <;> simp [hk, hl] at h ⊢

variable [CharP K 2] (hjn : 2 * j ≤ n)
include hjn

theorem exists_spALeviOne_eq {g : StatedSp n K}
    (hgC : g ∈ centralizer ({spARep n j} : Set (StatedSp n K)))
    (hsupp : ∀ r t, ¬ (spABlk j r ≠ 2 ∧ spABlk j t ≠ 2) →
      mat n K g r t = (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) r t)
    (hblk : ∀ r t, spABlk j r ≠ spABlk j t → mat n K g r t = 0) :
    ∃ x, spALeviOne hjn x = g := by
  set M := mat n K g with hMdef
  have h21 : M.toBlocks₂₁ = 0 := by
    ext k l
    rw [toBlocks₂₁, of_apply, Matrix.zero_apply]
    by_cases h : spABlk j (Sum.inr k : Fin n ⊕ Fin n) = spABlk j (Sum.inl l)
    · have h2 := spABlk_eq_two_of_inr_eq_inl h
      rw [hsupp _ _ (fun h' => h'.1 h2)]
      simp
    · exact hblk _ _ h
  have h12 : M.toBlocks₁₂ = 0 := by
    ext k l
    rw [toBlocks₁₂, of_apply, Matrix.zero_apply]
    by_cases h : spABlk j (Sum.inl k : Fin n ⊕ Fin n) = spABlk j (Sum.inr l)
    · have h2 := spABlk_eq_two_of_inr_eq_inl h.symm
      rw [hsupp _ _ (fun h' => h'.2 h2)]
      simp
    · exact hblk _ _ h
  rw [hMdef, mat_apply] at h21
  obtain ⟨hdet, C, -, hMe⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.exists_blockMat_of_toBlocks₂₁_eq_zero h21
  rw [← mat_apply, ← hMdef] at hMe hdet
  set A := M.toBlocks₁₁ with hA
  have hC0 : C = 0 := by
    have hAC : A * C = 0 := by
      have := congrArg Matrix.toBlocks₁₂ hMe
      rwa [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.blockMat, toBlocks_fromBlocks₁₂,
        h12, eq_comm] at this
    rw [← nonsing_inv_mul_cancel_left A C hdet, hAC, Matrix.mul_zero]
  have hMA : M = fromBlocks A 0 0 A⁻¹ᵀ := by
    rw [hMe, CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.blockMat, hC0, Matrix.mul_zero]
  set Au : GL (Fin n) K := ⟨A, A⁻¹, mul_nonsing_inv A hdet, nonsing_inv_mul A hdet⟩
  have hgL : g = leviEmbedGL K n Au := mat_injective (by rw [mat_leviEmbedGL, ← hMdef, hMA]; rfl)
  have hAC : A * spARepMat n j * Aᵀ = spARepMat n j := by
    have h1 := leviEmbedGL_conj_upperUnipotentSp Au (spARepMat_transpose (K := K) n j)
    have h2 : leviEmbedGL K n Au * spARep n j * (leviEmbedGL K n Au)⁻¹ = spARep n j := by
      rw [← hgL]
      rw [mem_centralizer_singleton_iff] at hgC
      rw [hgC]
      group
    have h3 := congrArg (mat n K) (h1.symm.trans h2)
    rw [mat_upperUnipotentSp, spARep, mat_upperUnipotentSp, fromBlocks_inj] at h3
    exact h3.2.1
  set x₀ := (A.submatrix (spAIndexEquiv hjn) (spAIndexEquiv hjn)).toBlocks₁₁ with hx₀
  have hAe : A.submatrix (spAIndexEquiv hjn) (spAIndexEquiv hjn) = fromBlocks x₀ 0 0 1 := by
    rw [← fromBlocks_toBlocks (A.submatrix (spAIndexEquiv hjn) (spAIndexEquiv hjn))]
    congr 1
    · ext r m
      rw [toBlocks₁₂, of_apply, submatrix_apply, Matrix.zero_apply]
      refine hblk _ _ ?_
      have hr := spAIndexEquiv_inl_lt hjn r
      have hm := spAIndexEquiv_inr_val hjn m
      simp [hr, hm]
    · ext m r
      rw [toBlocks₂₁, of_apply, submatrix_apply, Matrix.zero_apply]
      refine hblk _ _ ?_
      have hr := spAIndexEquiv_inl_lt hjn r
      have hm := spAIndexEquiv_inr_val hjn m
      simp [hr, hm]
    · ext m m'
      rw [toBlocks₂₂, of_apply, submatrix_apply]
      have hm := spAIndexEquiv_inr_val hjn m
      have hm' := spAIndexEquiv_inr_val hjn m'
      rw [show A (spAIndexEquiv hjn (Sum.inr m)) (spAIndexEquiv hjn (Sum.inr m')) =
        M (Sum.inl (spAIndexEquiv hjn (Sum.inr m))) (Sum.inl (spAIndexEquiv hjn (Sum.inr m')))
        from rfl, hsupp _ _ (by simp [hm, hm'])]
      simp [Matrix.one_apply, (spAIndexEquiv hjn).injective.eq_iff]
  have hAs : A = spASpread hjn x₀ := by
    rw [spASpread, ← hAe, submatrix_submatrix, Equiv.self_comp_symm, submatrix_id_id]
  have hx₀J : x₀ * gram K j * x₀ᵀ = gram K j := by
    rw [hAs, spARepMat_eq_submatrix hjn, spASpread, transpose_submatrix, submatrix_mul_equiv,
      submatrix_mul_equiv, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply]
      at hAC
    have := congrArg (fun N => (N.submatrix (spAIndexEquiv hjn) (spAIndexEquiv hjn)).toBlocks₁₁)
      hAC
    simpa [submatrix_submatrix] using this
  obtain ⟨hsym, hdet₀⟩ := spA_transpose_mul_gram_mul_of hx₀J
  set xu : GL (Fin j ⊕ Fin j) K := ⟨x₀, x₀⁻¹, mul_nonsing_inv x₀ hdet₀, nonsing_inv_mul x₀ hdet₀⟩
  refine ⟨⟨xu, mem_statedSp_iff.2 hsym⟩, mat_injective ?_⟩
  rw [mat_spALeviOne, ← hMdef, hMA]
  have hinv : spASpread hjn (mat j K (⟨xu, mem_statedSp_iff.2 hsym⟩ : StatedSp j K)⁻¹) = A⁻¹ := by
    symm
    apply Matrix.inv_eq_right_inv
    rw [hAs, ← spASpread_mul, ← spASpread_one hjn]
    congr 1
    exact mul_nonsing_inv x₀ hdet₀
  rw [hinv]
  show fromBlocks (spASpread hjn x₀) 0 0 A⁻¹ᵀ = _
  rw [← hAs]

theorem exists_spALeviOne_mul_spALeviTwo {g : StatedSp n K} (hg : g ∈ (spALeviHom hjn).range) :
    ∃ x y, spALeviOne hjn x * spALeviTwo K n j y = g := by
  obtain ⟨c, rfl⟩ := hg
  have hgC := spALeviHom_mem_centralizer hjn c
  have hL : spALeviPart j (mat n K (spALeviHom hjn c)) = mat n K (spALeviHom hjn c) := by
    rw [mat_spALeviHom, spALeviPart_spALeviPart]
  set g := spALeviHom hjn c with hgdef
  set M := mat n K g with hMdef
  have hblk0 : ∀ r t, spABlk j r ≠ spABlk j t → M r t = 0 := fun r t h => by
    rw [← hL, spALeviPart_apply, ite_eq_right h]
  have hp : ∀ r : Fin n ⊕ Fin n, spABlk j (par r) ≠ 2 ↔ spABlk j r ≠ 2 := fun r => by
    rw [spABlk_par]
    rcases spABlk_fin_three_cases (spABlk j r) with h | h | h <;> rw [h] <;> decide
  have hblk : ∀ r t, ¬ (spABlk j r ≠ 2 ↔ spABlk j t ≠ 2) → M r t = 0 := fun r t h =>
    hblk0 r t (fun e => h (by rw [e]))
  have hM := mat_transpose_mul_gram_mul g
  set g₁ := ofSymplecticMat (spARestrict (fun r => spABlk j r ≠ 2) M)
    (spARestrict_symplectic hp hM hblk)
  set g₂ := ofSymplecticMat (spARestrict (fun r => ¬ spABlk j r ≠ 2) M)
    (spARestrict_symplectic (fun r => (hp r).not) hM
      (fun r t h => hblk r t (fun h' => h (not_congr h'))))
  have hg12 : g₁ * g₂ = g := mat_injective (by
    rw [map_mul, mat_ofSymplecticMat, mat_ofSymplecticMat, spARestrict_mul hblk])
  have hg₂ : g₂ ∈ (spALeviTwo K n j).range := by
    rw [spALeviTwo, range_spEmbed, mem_suppGroup]
    intro r t hrt
    rw [mat_ofSymplecticMat]
    by_cases hr : spABlk j r = 2
    · have ht : spABlk j t ≠ 2 := fun ht =>
        hrt ⟨mem_range_sumMap_spAMidPlane.2 hr, mem_range_sumMap_spAMidPlane.2 ht⟩
      exact spARestrict_apply_of_not_right _ (by simpa using ht)
    · exact spARestrict_apply_of_not_left (by simpa using hr) t
  obtain ⟨y, hy⟩ := hg₂
  have hg₁C : g₁ ∈ centralizer ({spARep n j} : Set (StatedSp n K)) := by
    have e : g₁ = g * g₂⁻¹ := by rw [← hg12, mul_inv_cancel_right]
    rw [e]
    exact mul_mem hgC (inv_mem (hy ▸ spALeviTwo_mem_centralizer y))
  obtain ⟨x, hx⟩ := exists_spALeviOne_eq hjn hg₁C
    (fun r t h => by
      rw [mat_ofSymplecticMat, spARestrict, of_apply, ite_eq_right h])
    (fun r t h => by
      rw [mat_ofSymplecticMat]
      by_cases hrt : spABlk j r ≠ 2 ∧ spABlk j t ≠ 2
      · rw [spARestrict_apply_of hrt.1 hrt.2, hblk0 r t h]
      · rw [spARestrict, of_apply, ite_eq_right hrt, Matrix.one_apply_ne (fun e => h (by rw [e]))])
  exact ⟨x, y, by rw [hx, hy, hg12]⟩

omit [CharP K 2] in
theorem isSupp_spALeviOne (x : StatedSp j K) :
    CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.IsSupp {r | spABlk j r ≠ 2}
      (mat n K (spALeviOne hjn x)) := by
  have key : ∀ (z : Matrix (Fin j ⊕ Fin j) (Fin j ⊕ Fin j) K) (k l : Fin n),
      (2 * j ≤ k.val ∨ 2 * j ≤ l.val) →
        spASpread hjn z k l = (1 : Matrix (Fin n) (Fin n) K) k l := by
    intro z k l h
    rw [← spASpread_one hjn]
    by_cases hkl : (k.val < 2 * j ↔ l.val < 2 * j)
    · have hk : 2 * j ≤ k.val := by
        rcases h with h | h
        · exact h
        · by_contra hk
          exact absurd (hkl.1 (by omega)) (by omega)
      obtain ⟨m, hm⟩ := spAIndexEquiv_symm_of_ge hjn hk
      obtain ⟨m', hm'⟩ := spAIndexEquiv_symm_of_ge hjn (k := l)
        (by by_contra hl; exact absurd (hkl.2 (by omega)) (by omega))
      rw [spASpread, spASpread, submatrix_apply, submatrix_apply, hm, hm', fromBlocks_apply₂₂,
        fromBlocks_apply₂₂]
    · rw [spASpread_apply_eq_zero hjn _ hkl, spASpread_apply_eq_zero hjn _ hkl]
  intro r t h
  simp only [Set.mem_ofPred_eq, not_not] at h
  rw [mat_spALeviOne]
  rcases r with k | k <;> rcases t with l | l
  · rw [fromBlocks_apply₁₁, key _ k l (by rcases h with h | h <;> simp_all)]
    simp [Matrix.one_apply]
  · simp
  · simp
  · rw [fromBlocks_apply₂₂, transpose_apply,
      key _ l k (by rcases h with h | h <;> simp_all)]
    simp [Matrix.one_apply, eq_comm]

@[expose] noncomputable def spALeviParam (p : StatedSp j K × StatedSp (n - 2 * j) K) :
    (spALeviHom (K := K) hjn).range :=
  ⟨spALeviOne hjn p.1 * spALeviTwo K n j p.2,
    mul_mem (spALeviOne_mem_range hjn _) (spALeviTwo_mem_range hjn _)⟩

theorem spALeviParam_bijective : Function.Bijective (spALeviParam (K := K) hjn) := by
  refine ⟨fun p q h => ?_, fun g => ?_⟩
  · have h' : spALeviOne hjn p.1 * spALeviTwo K n j p.2 =
        spALeviOne hjn q.1 * spALeviTwo K n j q.2 := congrArg Subtype.val h
    have e : spALeviOne hjn (q.1⁻¹ * p.1) = spALeviTwo K n j (q.2 * p.2⁻¹) := by
      calc spALeviOne hjn (q.1⁻¹ * p.1) = (spALeviOne hjn q.1)⁻¹ *
            (spALeviOne hjn p.1 * spALeviTwo K n j p.2) * (spALeviTwo K n j p.2)⁻¹ := by
            rw [map_mul, map_inv]
            group
        _ = (spALeviOne hjn q.1)⁻¹ * (spALeviOne hjn q.1 * spALeviTwo K n j q.2) *
            (spALeviTwo K n j p.2)⁻¹ := by rw [h']
        _ = spALeviTwo K n j (q.2 * p.2⁻¹) := by
            rw [map_mul, map_inv]
            group
    have h1 : spALeviOne hjn (q.1⁻¹ * p.1) = 1 := by
      apply mat_injective
      ext r t
      rw [map_one]
      by_cases hr : spABlk j r = 2
      · exact isSupp_spALeviOne hjn _ r t (Or.inl (by simpa using hr))
      · rw [e]
        exact isSupp_spALeviTwo _ r t (Or.inl hr)
    have h2 : spALeviTwo K n j (q.2 * p.2⁻¹) = 1 := by rw [← e, h1]
    have e1 : q.1⁻¹ * p.1 = 1 := spALeviOne_injective hjn (by rw [h1, map_one])
    have e2 : q.2 * p.2⁻¹ = 1 := spALeviTwo_injective (by rw [h2, map_one])
    exact Prod.ext (by rw [← inv_mul_eq_one.1 e1]) (mul_inv_eq_one.1 e2).symm
  · obtain ⟨x, y, hxy⟩ := exists_spALeviOne_mul_spALeviTwo hjn g.2
    exact ⟨(x, y), Subtype.ext hxy⟩

theorem card_range_spALeviHom :
    Nat.card (spALeviHom (K := K) hjn).range =
      Nat.card (StatedSp j K) * Nat.card (StatedSp (n - 2 * j) K) := by
  rw [← Nat.card_prod]
  exact (Nat.card_congr (Equiv.ofBijective _ (spALeviParam_bijective hjn))).symm

omit [CharP K 2] hjn in
theorem spA_apply_mem_commutator_of_perfect {G H : Type*} [Group G] [Group.IsPerfect G]
    [Group H] (f : G →* H) {C : Subgroup H} (hf : f.range ≤ C) (x : G) : f x ∈ ⁅C, C⁆ := by
  have hx : x ∈ commutator G := Group.IsPerfect.mem_commutator
  have h1 : f x ∈ Subgroup.map f ⁅(⊤ : Subgroup G), ⊤⁆ := Subgroup.mem_map_of_mem f hx
  rw [Subgroup.map_commutator, Subgroup.map_top] at h1
  exact Subgroup.commutator_mono hf hf h1

theorem range_spALeviHom_le_commutator [Finite K] (hK : 4 ≤ Nat.card K) :
    (spALeviHom hjn).range ≤ ⁅centralizer ({spARep n j} : Set (StatedSp n K)),
      centralizer ({spARep n j} : Set (StatedSp n K))⁆ := by
  have : Fintype K := Fintype.ofFinite K
  have h4 : ∃ s : Finset K, s.card = 4 := by
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset K))
      (n := 4) (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact hK)
    exact ⟨s, hs⟩
  have : Group.IsPerfect (StatedSp j K) :=
    CFSG.ClassicalGroups.Symplectic.isPerfect_statedSp j K (Or.inl h4)
  have : Group.IsPerfect (StatedSp (n - 2 * j) K) :=
    CFSG.ClassicalGroups.Symplectic.isPerfect_statedSp (n - 2 * j) K (Or.inl h4)
  intro g hg
  obtain ⟨x, y, rfl⟩ := exists_spALeviOne_mul_spALeviTwo hjn hg
  refine mul_mem (spA_apply_mem_commutator_of_perfect _ ?_ x)
    (spA_apply_mem_commutator_of_perfect _ ?_ y)
  · rintro _ ⟨z, rfl⟩
    exact spALeviOne_mem_centralizer hjn z
  · rintro _ ⟨z, rfl⟩
    exact spALeviTwo_mem_centralizer z

end Decomp

end CFSG.SeitzReduction.SymplecticPilot
