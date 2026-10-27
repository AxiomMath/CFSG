module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaMinusLevels
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OrthEscape

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaMinus

open Matrix CFSG.Assembly.LowTwoRank CFSG.Open CFSG.LieType.BorelTits
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.SpCell
  (cnt cnt_le_card cnt_mono exists_cut_of_cnt_lt cnt_lt_of_cut exists_cut_of_cnt_lt_card StepCoord
    topN topEmb cnt_topEmb exists_topEmb_eq topEmb_injective)

variable {r : ℕ} {F : Type} [Field F] {b c : F} {S : Finset ℕ}

@[expose] def βm (r : ℕ) (F : Type) [Field F] (b c : F) (v w : Idx r → F) : F :=
  quadMinusPolar (r + 1) F b c v w

theorem Qm_eq (v : Idx r → F) :
    Qm r F b c v = ∑ i : Fin r, v (Sum.inl i) * v (Sum.inr (Sum.inl i)) +
      v (Sum.inr (Sum.inr 0)) ^ 2 + b * v (Sum.inr (Sum.inr 0)) * v (Sum.inr (Sum.inr 1)) +
      c * v (Sum.inr (Sum.inr 1)) ^ 2 := rfl

theorem βm_eq (v w : Idx r → F) :
    βm r F b c v w = ∑ i : Fin r, (v (Sum.inl i) * w (Sum.inr (Sum.inl i)) +
      w (Sum.inl i) * v (Sum.inr (Sum.inl i))) +
      (2 * v (Sum.inr (Sum.inr 0)) * w (Sum.inr (Sum.inr 0)) +
        b * (v (Sum.inr (Sum.inr 0)) * w (Sum.inr (Sum.inr 1)) +
          w (Sum.inr (Sum.inr 0)) * v (Sum.inr (Sum.inr 1))) +
        2 * c * v (Sum.inr (Sum.inr 1)) * w (Sum.inr (Sum.inr 1))) := rfl

theorem Qm_add (v w : Idx r → F) :
    Qm r F b c (v + w) = Qm r F b c v + Qm r F b c w + βm r F b c v w := by
  simp only [Qm_eq, βm_eq, Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib]
  ring

theorem βm_single_inl (v : Idx r → F) (a : Fin r) :
    βm r F b c v (Pi.single (Sum.inl a) 1) = v (Sum.inr (Sum.inl a)) := by
  simp [βm_eq, Pi.single_apply]

theorem Qm_mulVec {A : GL (Idx r) F} (hA : A ∈ Ωm r F b c) (v : Idx r → F) :
    Qm r F b c ((A : Matrix (Idx r) (Idx r) F) *ᵥ v) = Qm r F b c v :=
  CFSG.LieType.Steinberg.preserves_of_mem_statedOmega hA v

theorem βm_mulVec {A : GL (Idx r) F} (hA : A ∈ Ωm r F b c) (v w : Idx r → F) :
    βm r F b c ((A : Matrix (Idx r) (Idx r) F) *ᵥ v) ((A : Matrix (Idx r) (Idx r) F) *ᵥ w) =
      βm r F b c v w := by
  have h1 := Qm_add (b := b) (c := c) ((A : Matrix (Idx r) (Idx r) F) *ᵥ v)
    ((A : Matrix (Idx r) (Idx r) F) *ᵥ w)
  rw [← Matrix.mulVec_add, Qm_mulVec hA, Qm_mulVec hA, Qm_mulVec hA, Qm_add] at h1
  linear_combination -h1

theorem single_inl_mem_eSub {i : ℕ} {d : Fin r} (h : (d : ℕ) < i) :
    (Pi.single (Sum.inl d) 1 : Idx r → F) ∈ eSub r F i :=
  fun _ hu => Pi.single_eq_of_ne (hu d h) _

theorem Qm_eq_zero_of_mem_eSub {i : ℕ} {w : Idx r → F} (hw : w ∈ eSub r F i) :
    Qm r F b c w = 0 := by
  have hf : ∀ a : Fin r, w (Sum.inr (Sum.inl a)) = 0 := fun a => hw _ (fun a' _ => by simp)
  have hk : ∀ k : Fin 2, w (Sum.inr (Sum.inr k)) = 0 := fun k => hw _ (fun a' _ => by simp)
  simp [Qm_eq, hf, hk]

theorem βm_perp_eSub {i : ℕ} {w y : Idx r → F}
    (hw : ∀ a : Fin r, (a : ℕ) < i → w (Sum.inr (Sum.inl a)) = 0) (hy : y ∈ eSub r F i) :
    βm r F b c w y = 0 := by
  have hf : ∀ a : Fin r, y (Sum.inr (Sum.inl a)) = 0 := fun a => hy _ (fun a' _ => by simp)
  have hk : ∀ k : Fin 2, y (Sum.inr (Sum.inr k)) = 0 := fun k => hy _ (fun a' _ => by simp)
  have he : ∀ a : Fin r, ¬ (a : ℕ) < i → y (Sum.inl a) = 0 := fun a ha =>
    hy _ (fun a' ha' h => ha (by have := Sum.inl_injective h; subst this; exact ha'))
  rw [βm_eq]
  simp only [hk, mul_zero, zero_mul, add_zero, hf]
  refine Finset.sum_eq_zero fun a _ => ?_
  by_cases ha : (a : ℕ) < i
  · simp [hw a ha]
  · simp [he a ha]

theorem JΩ_perp {A : GL (Idx r) F} (hA : A ∈ JΩ r F b c S) {i : ℕ} (hi : i ∈ S)
    {w : Idx r → F} (hw : ∀ a : Fin r, (a : ℕ) < i → w (Sum.inr (Sum.inl a)) = 0)
    (a : Fin r) (ha : (a : ℕ) < i) :
    ((A : Matrix (Idx r) (Idx r) F) *ᵥ w) (Sum.inr (Sum.inl a)) = 0 := by
  set y : Idx r → F := ((A⁻¹ : GL (Idx r) F) : Matrix (Idx r) (Idx r) F) *ᵥ Pi.single (Sum.inl a) 1
    with hy
  have hAy : (A : Matrix (Idx r) (Idx r) F) *ᵥ y = Pi.single (Sum.inl a) 1 := by
    rw [hy, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec]
  have hyE : y ∈ eSub r F i := by
    rw [hA.2 i hi y, hAy]
    exact single_inl_mem_eSub ha
  have h := βm_single_inl (b := b) (c := c) ((A : Matrix (Idx r) (Idx r) F) *ᵥ w) a
  rw [← h, ← hAy, βm_mulVec hA.1]
  exact βm_perp_eSub hw hyE

theorem single_perp_inl {i : ℕ} (d : Fin r) :
    ∀ a : Fin r, (a : ℕ) < i → (Pi.single (Sum.inl d) 1 : Idx r → F) (Sum.inr (Sum.inl a)) = 0 :=
  fun a _ => Pi.single_eq_of_ne (by simp) _

theorem single_perp_inr {i : ℕ} (d : Fin r) (hd : i ≤ (d : ℕ)) :
    ∀ a : Fin r, (a : ℕ) < i →
      (Pi.single (Sum.inr (Sum.inl d)) 1 : Idx r → F) (Sum.inr (Sum.inl a)) = 0 := by
  intro a ha
  refine Pi.single_eq_of_ne ?_ _
  intro h
  have := Sum.inl_injective (Sum.inr_injective h)
  subst this
  omega

theorem single_perp_aniso {i : ℕ} (k : Fin 2) :
    ∀ a : Fin r, (a : ℕ) < i →
      (Pi.single (Sum.inr (Sum.inr k)) 1 : Idx r → F) (Sum.inr (Sum.inl a)) = 0 :=
  fun a _ => Pi.single_eq_of_ne (by simp) _

theorem JΩ_blockTriangular (hS : ∀ i ∈ S, 1 ≤ i ∧ i ≤ r) {A : GL (Idx r) F}
    (hA : A ∈ JΩ r F b c S) :
    ((A : GL _ F) : Matrix (Idx r) (Idx r) F).BlockTriangular (omLev r S) := by
  have _ := hS
  have hcard : ∀ a : ℕ, cnt S a ≤ S.card := cnt_le_card S
  have hE : ∀ i ∈ S, ∀ d : Fin r, (d : ℕ) < i →
      (A : Matrix (Idx r) (Idx r) F) *ᵥ Pi.single (Sum.inl d) 1 ∈ eSub r F i :=
    fun i hi d hd => (hA.2 i hi _).1 (single_inl_mem_eSub hd)
  intro u v huv
  have hent : (A : Matrix (Idx r) (Idx r) F) u v =
      ((A : Matrix (Idx r) (Idx r) F) *ᵥ Pi.single v 1) u := by
    rw [Matrix.mulVec_single_one]; rfl
  rw [hent]
  rcases u with a | a | k <;> rcases v with d | d | k'
  ·
    have huv' : cnt S d < cnt S a := huv
    obtain ⟨i, hiS, hdi, hia⟩ := exists_cut_of_cnt_lt S huv'
    exact hE i hiS d hdi _ (fun a' ha' h => by
      have := Sum.inl_injective h; subst this; omega)
  · have huv' : 2 * S.card - cnt S d < cnt S a := huv
    have := hcard a; have := hcard d
    omega
  · have huv' : S.card < cnt S a := huv
    have := hcard a
    omega
  ·
    have huv' : cnt S d < 2 * S.card - cnt S a := huv
    by_cases hb : ∃ i ∈ S, (d : ℕ) < i
    · obtain ⟨i, hiS, hdi⟩ := hb
      exact hE i hiS d hdi _ (fun a' _ => by simp)
    · push Not at hb
      have hcb : cnt S d = S.card := le_antisymm (hcard d) (not_lt.1 fun h => by
        obtain ⟨i, hiS, hdi⟩ := exists_cut_of_cnt_lt_card S h
        exact absurd (hb i hiS) (not_le.2 hdi))
      have hca : cnt S a < S.card := by
        have := hcard a
        omega
      obtain ⟨i, hiS, hai⟩ := exists_cut_of_cnt_lt_card S hca
      exact JΩ_perp hA hiS (single_perp_inl d) a hai
  ·
    have huv' : 2 * S.card - cnt S d < 2 * S.card - cnt S a := huv
    have hab : cnt S a < cnt S d := by
      have := hcard a; have := hcard d
      omega
    obtain ⟨i, hiS, hai, hid⟩ := exists_cut_of_cnt_lt S hab
    exact JΩ_perp hA hiS (single_perp_inr d hid) a hai
  ·
    have huv' : S.card < 2 * S.card - cnt S a := huv
    have hca : cnt S a < S.card := by
      have := hcard a
      omega
    obtain ⟨i, hiS, hai⟩ := exists_cut_of_cnt_lt_card S hca
    exact JΩ_perp hA hiS (single_perp_aniso k') a hai
  ·
    have huv' : cnt S d < S.card := huv
    obtain ⟨i, hiS, hdi⟩ := exists_cut_of_cnt_lt_card S huv'
    exact hE i hiS d hdi _ (fun a' _ => by simp)
  · have huv' : 2 * S.card - cnt S d < S.card := huv
    have := hcard d
    omega
  · exact absurd huv (lt_irrefl _)

section Blocks

variable (r F b c S)

@[expose] def πJ : ↥(JΩ r F b c S) →* GL (Idx r) F := (JΩ r F b c S).subtype

variable {r F b c S}

theorem πJ_blockTriangular (hS : ∀ i ∈ S, 1 ≤ i ∧ i ≤ r) (g : ↥(JΩ r F b c S)) :
    ((πJ r F b c S g : GL (Idx r) F) : Matrix (Idx r) (Idx r) F).BlockTriangular (omLev r S) :=
  JΩ_blockTriangular hS g.2

@[expose] noncomputable def stepHom (hS : ∀ i ∈ S, 1 ≤ i ∧ i ≤ r) {ℓ : ℕ} (hℓ : ℓ < S.card) :
    ↥(JΩ r F b c S) →* GL (StepCoord r S ℓ) F :=
  levelHom (πJ r F b c S) (πJ_blockTriangular hS) (step_injective ℓ) (step_range hℓ)

theorem coe_stepHom (hS : ∀ i ∈ S, 1 ≤ i ∧ i ≤ r) {ℓ : ℕ} (hℓ : ℓ < S.card)
    (g : ↥(JΩ r F b c S)) :
    ((stepHom hS hℓ g : GL (StepCoord r S ℓ) F) : Matrix (StepCoord r S ℓ) (StepCoord r S ℓ) F) =
      ((g : GL (Idx r) F) : Matrix (Idx r) (Idx r) F).submatrix (fun a => Sum.inl a.1)
        (fun a => Sum.inl a.1) :=
  coe_levelHom _ _ _ _ g

@[expose] noncomputable def topHomGL (hS : ∀ i ∈ S, 1 ≤ i ∧ i ≤ r) :
    ↥(JΩ r F b c S) →* GL (Idx (topN r S)) F :=
  levelHom (πJ r F b c S) (πJ_blockTriangular hS) topσ_injective top_range

theorem coe_topHomGL (hS : ∀ i ∈ S, 1 ≤ i ∧ i ≤ r) (g : ↥(JΩ r F b c S)) :
    ((topHomGL hS g : GL (Idx (topN r S)) F) : Matrix (Idx (topN r S)) (Idx (topN r S)) F) =
      ((g : GL (Idx r) F) : Matrix (Idx r) (Idx r) F).submatrix (topσ r S) (topσ r S) :=
  coe_levelHom _ _ _ _ g

theorem Qm_eq_top {y : Idx r → F}
    (hy : ∀ a : Fin r, cnt S a < S.card → y (Sum.inr (Sum.inl a)) = 0) :
    Qm r F b c y = Qm (topN r S) F b c (y ∘ topσ r S) := by
  rw [Qm_eq, Qm_eq]
  have hsum : ∑ a : Fin r, y (Sum.inl a) * y (Sum.inr (Sum.inl a)) =
      ∑ j : Fin (topN r S), y (Sum.inl (topEmb r S j)) * y (Sum.inr (Sum.inl (topEmb r S j))) := by
    refine (Fintype.sum_of_injective (topEmb r S) topEmb_injective
      (fun j => y (Sum.inl (topEmb r S j)) * y (Sum.inr (Sum.inl (topEmb r S j))))
      (fun a => y (Sum.inl a) * y (Sum.inr (Sum.inl a))) (fun a ha => ?_) (fun j => rfl)).symm
    have hlt : cnt S a < S.card := by
      have := cnt_le_card S a
      refine lt_of_le_of_ne this fun h => ha ?_
      obtain ⟨j, hj⟩ := exists_topEmb_eq (S := S) (a := a) h
      exact ⟨j, hj⟩
    rw [hy a hlt, mul_zero]
  rw [hsum]
  rfl

theorem topHomGL_mem_orthGroup (hS : ∀ i ∈ S, 1 ≤ i ∧ i ≤ r) (g : ↥(JΩ r F b c S)) :
    topHomGL hS g ∈ orthGroup (Qm (topN r S) F b c) := by
  apply Subgroup.subset_closure
  intro w
  set M : Matrix (Idx r) (Idx r) F := ((g : GL (Idx r) F) : Matrix (Idx r) (Idx r) F) with hM
  have hbt : M.BlockTriangular (omLev r S) := JΩ_blockTriangular hS g.2
  set w' : Idx r → F := Function.extend (topσ r S) w 0 with hw'
  have hw'σ : ∀ u, w' (topσ r S u) = w u := fun u => topσ_injective.extend_apply w 0 u
  have hw'off : ∀ u, u ∉ Set.range (topσ r S) → w' u = 0 := fun u hu => by
    rw [hw', Function.extend_apply' _ _ _ (fun h => hu h)]
    rfl
  have hlev : ∀ a : Fin r, cnt S a < S.card → Sum.inr (Sum.inl a) ∉ Set.range (topσ r S) := by
    intro a ha hmem
    have := (top_range _).2 hmem
    have h2 : 2 * S.card - cnt S a = S.card := this
    omega
  have hMw : ∀ u, (M *ᵥ w') (topσ r S u) =
      (((topHomGL hS g : GL (Idx (topN r S)) F) : Matrix (Idx (topN r S)) (Idx (topN r S)) F) *ᵥ
        w) u := by
    intro u
    rw [coe_topHomGL]
    simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply]
    refine (Fintype.sum_of_injective (topσ r S) topσ_injective
      (fun v => M (topσ r S u) (topσ r S v) * w v) (fun v => M (topσ r S u) v * w' v)
      (fun v hv => ?_) (fun v => by rw [hw'σ])).symm
    rw [hw'off v hv, mul_zero]
  have hMw0 : ∀ a : Fin r, cnt S a < S.card → (M *ᵥ w') (Sum.inr (Sum.inl a)) = 0 := by
    intro a ha
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_eq_zero fun v _ => ?_
    by_cases hv : v ∈ Set.range (topσ r S)
    · have h1 : omLev r S v = S.card := (top_range v).2 hv
      have h2 : omLev r S (Sum.inr (Sum.inl a)) = 2 * S.card - cnt S a := rfl
      have := cnt_le_card S a
      rw [hbt (show omLev r S v < omLev r S (Sum.inr (Sum.inl a)) by omega), zero_mul]
    · rw [hw'off v hv, mul_zero]
  have h1 : Qm r F b c w' = Qm (topN r S) F b c w := by
    rw [Qm_eq_top (fun a ha => hw'off _ (hlev a ha))]
    congr 1
    funext u
    exact hw'σ u
  have h2 : Qm r F b c (M *ᵥ w') = Qm (topN r S) F b c
      (((topHomGL hS g : GL (Idx (topN r S)) F) : Matrix (Idx (topN r S)) (Idx (topN r S)) F) *ᵥ
        w) := by
    rw [Qm_eq_top hMw0]
    congr 1
    funext u
    exact hMw u
  rw [← h2, ← h1]
  exact Qm_mulVec g.2.1 w'

@[expose] noncomputable def topHom (hS : ∀ i ∈ S, 1 ≤ i ∧ i ≤ r) :
    ↥(JΩ r F b c S) →* ↥(orthGroup (Qm (topN r S) F b c)) :=
  (topHomGL hS).codRestrict (orthGroup (Qm (topN r S) F b c)) (topHomGL_mem_orthGroup hS)

theorem coe_topHom (hS : ∀ i ∈ S, 1 ≤ i ∧ i ≤ r) (g : ↥(JΩ r F b c S)) :
    (((topHom hS g : ↥(orthGroup (Qm (topN r S) F b c))) : GL (Idx (topN r S)) F) :
      Matrix (Idx (topN r S)) (Idx (topN r S)) F) =
      ((g : GL (Idx r) F) : Matrix (Idx r) (Idx r) F).submatrix (topσ r S) (topσ r S) :=
  coe_topHomGL hS g

end Blocks

section Kernel

theorem mat_apply_eq_of_stepHom_eq_one (hS : ∀ i ∈ S, 1 ≤ i ∧ i ≤ r) {ℓ : ℕ} (hℓ : ℓ < S.card)
    {g : ↥(JΩ r F b c S)} (hg : stepHom hS hℓ g = 1) (u v : Idx r) (hu : omLev r S u = ℓ)
    (hv : omLev r S v = ℓ) :
    ((g : GL (Idx r) F) : Matrix (Idx r) (Idx r) F) u v = (1 : Matrix (Idx r) (Idx r) F) u v := by
  obtain ⟨a, rfl⟩ := (step_range hℓ u).1 hu
  obtain ⟨a', rfl⟩ := (step_range hℓ v).1 hv
  have h1 : ((g : GL (Idx r) F) : Matrix (Idx r) (Idx r) F) (Sum.inl a.1) (Sum.inl a'.1) =
      ((stepHom hS hℓ g : GL (StepCoord r S ℓ) F) :
        Matrix (StepCoord r S ℓ) (StepCoord r S ℓ) F) a a' := by
    rw [coe_stepHom]; rfl
  rw [h1, hg, Units.val_one]
  simp [Matrix.one_apply, Subtype.ext_iff]

theorem mat_apply_eq_of_topHom_eq_one (hS : ∀ i ∈ S, 1 ≤ i ∧ i ≤ r)
    {g : ↥(JΩ r F b c S)} (hg : topHom hS g = 1) (u v : Idx r) (hu : omLev r S u = S.card)
    (hv : omLev r S v = S.card) :
    ((g : GL (Idx r) F) : Matrix (Idx r) (Idx r) F) u v = (1 : Matrix (Idx r) (Idx r) F) u v := by
  obtain ⟨a, rfl⟩ := (top_range u).1 hu
  obtain ⟨a', rfl⟩ := (top_range v).1 hv
  have h1 : ((g : GL (Idx r) F) : Matrix (Idx r) (Idx r) F) (topσ r S a) (topσ r S a') =
      (((topHom hS g : ↥(orthGroup (Qm (topN r S) F b c))) : GL (Idx (topN r S)) F) :
        Matrix (Idx (topN r S)) (Idx (topN r S)) F) a a' := by
    rw [coe_topHom]; rfl
  rw [h1, hg]
  simp [Matrix.one_apply, topσ_injective.eq_iff]

theorem eq_one_of_blocks_trivial (hS : ∀ i ∈ S, 1 ≤ i ∧ i ≤ r) {p : ℕ} (hp : (p : F) ≠ 0)
    {g : ↥(JΩ r F b c S)} (hgp : g ^ p = 1) (hstep : ∀ ℓ (hℓ : ℓ < S.card), stepHom hS hℓ g = 1)
    (htop : topHom hS g = 1) : g = 1 := by
  set M : Matrix (Idx r) (Idx r) F := ((g : GL (Idx r) F) : Matrix (Idx r) (Idx r) F) with hM
  have hMp : M ^ p = 1 := by
    have : (g : GL (Idx r) F) ^ p = 1 := congrArg Subtype.val hgp
    rw [hM, ← Units.val_pow_eq_pow_val, this, Units.val_one]
  have hbt : M.BlockTriangular (omLev r S) := JΩ_blockTriangular hS g.2
  have hcard : ∀ a : ℕ, cnt S a ≤ S.card := cnt_le_card S
  have hblk : ∀ u v, omLev r S u = omLev r S v → omLev r S u < S.card + 1 →
      M u v = (1 : Matrix (Idx r) (Idx r) F) u v := by
    intro u v huv hu
    rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hlt | heq
    · exact mat_apply_eq_of_stepHom_eq_one hS hlt (hstep _ hlt) u v rfl huv.symm
    · exact mat_apply_eq_of_topHom_eq_one hS htop u v heq (huv.symm.trans heq)
  have hfix := mulVec_eq_of_blocks_one hbt hp hMp (S.card + 1) hblk
  have hall : ∀ w : Idx r → F, M *ᵥ w = w := by
    let U : ℕ → Submodule F (Idx r → F) := fun j =>
      if j = 0 then ⊥ else if j = 1 then levelSpace (omLev r S) (S.card + 1) else ⊤
    have key := fixes_of_chain hp (mulVecLin_pow_eq_one hMp) U (by simp [U]) 2 (by
      intro j hj v hv
      interval_cases j
      · have hv' : v ∈ levelSpace (K := F) (omLev r S) (S.card + 1) := by simpa [U] using hv
        have : M *ᵥ v = v := hfix v hv'
        simp [U, this]
      · simp only [U] at hv ⊢
        simp only [one_ne_zero, ↓reduceIte]
        rw [mem_levelSpace]
        intro u hu
        rcases u with a | d | k
        · exact absurd hu (by show ¬ S.card + 1 ≤ cnt S a; have := hcard a; omega)
        ·
          have hmem : (Pi.single (Sum.inl d) 1 : Idx r → F) ∈
              levelSpace (K := F) (omLev r S) (S.card + 1) := by
            rw [mem_levelSpace]
            intro u hu
            refine Pi.single_eq_of_ne ?_ _
            rintro rfl
            exact absurd hu (by show ¬ S.card + 1 ≤ cnt S d; have := hcard d; omega)
          have h1 : M *ᵥ (Pi.single (Sum.inl d) 1 : Idx r → F) = Pi.single (Sum.inl d) 1 :=
            hfix _ hmem
          have h2 : βm r F b c (M *ᵥ v) (M *ᵥ (Pi.single (Sum.inl d) 1 : Idx r → F)) =
              βm r F b c v (Pi.single (Sum.inl d) 1) := βm_mulVec g.2.1 _ _
          rw [h1, βm_single_inl, βm_single_inl] at h2
          rw [Matrix.mulVecLin_apply]
          exact sub_eq_zero.2 h2
        · exact absurd hu (by show ¬ S.card + 1 ≤ S.card; omega))
    intro w
    exact key w (by simp [U])
  have hM1 : M = 1 := by
    ext i j
    have := congrFun (hall (Pi.single j 1)) i
    rw [Matrix.mulVec_single_one, Matrix.col_apply] at this
    rw [this]
    simp [Matrix.one_apply, Pi.single_apply]
  exact Subtype.ext (Units.ext hM1)

end Kernel

section Escape

theorem exists_avg {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {p : ℕ} (hp : (p : K) ≠ 0)
    {g : V →ₗ[K] V} (hg : g ^ p = 1) {A B : Submodule K V} (hAB : A ≤ B)
    (hstep : ∀ b ∈ B, g b - b ∈ A) {b : V} (hb : b ∈ B) :
    ∃ a ∈ B, g a = a ∧ a - (p : K) • b ∈ A := by
  have hmem : ∀ j : ℕ, (g ^ j) b ∈ B ∧ (g ^ j) b - b ∈ A := by
    intro j
    induction j with
    | zero => exact ⟨by simpa using hb, by simp⟩
    | succ j ih =>
      have h1 : g ((g ^ j) b) - (g ^ j) b ∈ A := hstep _ ih.1
      have h2 : (g ^ (j + 1)) b = g ((g ^ j) b) := by rw [pow_succ', Module.End.mul_apply]
      refine ⟨?_, ?_⟩
      · rw [h2]
        have : g ((g ^ j) b) = (g ((g ^ j) b) - (g ^ j) b) + (g ^ j) b := by abel
        rw [this]
        exact B.add_mem (hAB h1) ih.1
      · rw [h2]
        have : g ((g ^ j) b) - b = (g ((g ^ j) b) - (g ^ j) b) + ((g ^ j) b - b) := by abel
        rw [this]
        exact A.add_mem h1 ih.2
  set a : V := ∑ j ∈ Finset.range p, (g ^ j) b with ha
  have haB : a ∈ B := B.sum_mem fun j _ => (hmem j).1
  have hgsum : g a = a := by
    obtain ⟨n, hn⟩ : ∃ n, p = n + 1 := ⟨p - 1, by
      have : p ≠ 0 := fun h0 => hp (by simp [h0])
      omega⟩
    have hpb : (g ^ p) b = b := by rw [hg]; rfl
    have h1 : g a = ∑ j ∈ Finset.range p, (g ^ (j + 1)) b := by
      rw [ha, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [pow_succ', Module.End.mul_apply]
    rw [h1, ha, hn, Finset.sum_range_succ, Finset.sum_range_succ' (fun j => (g ^ j) b) n]
    have : (g ^ (n + 1)) b = (g ^ 0) b := by rw [← hn, hpb]; simp
    rw [this]
  have hdiff : a - (p : K) • b ∈ A := by
    have : a - (p : K) • b = ∑ j ∈ Finset.range p, ((g ^ j) b - b) := by
      rw [Finset.sum_sub_distrib, ha]
      simp [Nat.cast_smul_eq_nsmul K]
    rw [this]
    exact A.sum_mem fun j _ => (hmem j).2
  exact ⟨a, haB, hgsum, hdiff⟩

@[expose] noncomputable def Φm (r : ℕ) (F : Type) [Field F] [Finite F] (b c : F)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) : QuadForm F (Idx r → F) :=
  quadMinusForm (r + 1) F b c hirr

theorem false_of_step_escape [Finite F] [CharP F 2] (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (hr : 3 ≤ r) (hS : ∀ i ∈ S, 1 ≤ i ∧ i ≤ r) {p : ℕ} (hpodd : Odd p) {x : GL (Idx r) F}
    (hxΩ : x ∈ Ωm r F b c) (hxp : x ^ p = 1)
    (hfix : ∀ g ∈ Ωm r F b c, g * x = x * g → g ∈ JΩ r F b c S) {ℓ : ℕ} (hℓ : ℓ < S.card)
    (hxJ : x ∈ JΩ r F b c S) (hx1 : stepHom hS hℓ ⟨x, hxJ⟩ = 1)
    (hk : 2 ≤ Fintype.card (StepCoord r S ℓ)) : False := by
  have hp : (p : F) ≠ 0 := natCast_ne_zero_of_odd hpodd
  obtain ⟨a1, a2, hne⟩ := Fintype.exists_pair_of_one_lt_card
    (by omega : 1 < Fintype.card (StepCoord r S ℓ))
  have hne' : a1.1 ≠ a2.1 := fun h => hne (Subtype.ext h)
  set M : Matrix (Idx r) (Idx r) F := (x : Matrix (Idx r) (Idx r) F) with hM
  have hMp : M ^ p = 1 := by rw [hM, ← Units.val_pow_eq_pow_val, hxp, Units.val_one]
  have hbt : M.BlockTriangular (omLev r S) := JΩ_blockTriangular hS hxJ
  have hT : (S.filter (fun j => (a1.1 : ℕ) < j)).Nonempty := by
    obtain ⟨i, hiS, hai⟩ := exists_cut_of_cnt_lt_card S (a := a1.1) (by rw [a1.2]; exact hℓ)
    exact ⟨i, Finset.mem_filter.2 ⟨hiS, hai⟩⟩
  set i := (S.filter (fun j => (a1.1 : ℕ) < j)).min' hT with hi
  have hi' := Finset.min'_mem _ hT
  rw [← hi] at hi'
  obtain ⟨hiS, hai⟩ := Finset.mem_filter.1 hi'
  have hmin : ∀ i' ∈ S, (a1.1 : ℕ) < i' → i ≤ i' := fun i' hi'S hai' =>
    Finset.min'_le _ _ (Finset.mem_filter.2 ⟨hi'S, hai'⟩)
  have ha2i : (a2.1 : ℕ) < i := by
    by_contra h
    push Not at h
    have := cnt_lt_of_cut S hiS hai h
    rw [a1.2, a2.2] at this
    exact lt_irrefl _ this
  set B : Submodule F (Idx r → F) := eSub r F i with hB
  set A : Submodule F (Idx r → F) := B ⊓ levelSpace (omLev r S) ℓ with hA
  have hsubB : ∀ b' ∈ B, b' ∈ levelSpace (K := F) (omLev r S) (ℓ + 1) := by
    intro b' hb'
    rw [mem_levelSpace]
    intro u hu
    refine hb' u (fun d hd hud => ?_)
    subst hud
    have hlt : cnt S a1.1 < cnt S d := by
      have : omLev r S (Sum.inl d) = cnt S d := rfl
      rw [a1.2]; omega
    obtain ⟨i', hi'S, hai', hi'j⟩ := exists_cut_of_cnt_lt S hlt
    have := hmin i' hi'S hai'
    omega
  have hblk : ∀ u v, omLev r S u = ℓ → omLev r S v = ℓ → M u v =
      (1 : Matrix (Idx r) (Idx r) F) u v := fun u v hu hv =>
    mat_apply_eq_of_stepHom_eq_one hS hℓ hx1 u v hu hv
  have hstep : ∀ b' ∈ B, M.mulVecLin b' - b' ∈ A := by
    intro b' hb'
    refine ⟨?_, ?_⟩
    · have h1 : M *ᵥ b' ∈ B := (hxJ.2 i hiS b').1 hb'
      rw [Matrix.mulVecLin_apply]
      exact B.sub_mem h1 hb'
    · rw [Matrix.mulVecLin_apply]
      exact mulVec_sub_mem_levelSpace hbt hblk (hsubB b' hb')
  have hAB : A ≤ B := inf_le_left
  set e1 : Idx r → F := Pi.single (Sum.inl a1.1) 1 with he1
  set e2 : Idx r → F := Pi.single (Sum.inl a2.1) 1 with he2
  have he1B : e1 ∈ B := single_inl_mem_eSub hai
  have he2B : e2 ∈ B := single_inl_mem_eSub ha2i
  obtain ⟨c1, hc1B, hc1fix, hc1⟩ := exists_avg hp (mulVecLin_pow_eq_one hMp) hAB hstep he1B
  obtain ⟨c2, hc2B, hc2fix, hc2⟩ := exists_avg hp (mulVecLin_pow_eq_one hMp) hAB hstep he2B
  set W₁ : Submodule F (Idx r → F) := LinearMap.ker (M.mulVecLin - LinearMap.id) with hW₁
  have hW₁mem : ∀ v, v ∈ W₁ ↔ M *ᵥ v = v := fun v => by
    rw [hW₁, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, Matrix.mulVecLin_apply]
    rfl
  have hc1W : c1 ∈ W₁ := (hW₁mem _).2 (by rw [← Matrix.mulVecLin_apply]; exact hc1fix)
  have hc2W : c2 ∈ W₁ := (hW₁mem _).2 (by rw [← Matrix.mulVecLin_apply]; exact hc2fix)
  let v : Fin 2 → ↥(B ⊓ W₁) := ![⟨c1, hc1B, hc1W⟩, ⟨c2, hc2B, hc2W⟩]
  have hli : LinearIndependent F v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have h : g 0 • c1 + g 1 • c2 = 0 := by
      have := congrArg Subtype.val hg
      simpa [Fin.sum_univ_two, v] using this
    have hmem : (g 0 * p) • e1 + (g 1 * p) • e2 ∈ levelSpace (K := F) (omLev r S) ℓ := by
      have h1 : g 0 • (c1 - (p : F) • e1) + g 1 • (c2 - (p : F) • e2) ∈ A :=
        A.add_mem (A.smul_mem _ hc1) (A.smul_mem _ hc2)
      have h2 : (g 0 * p) • e1 + (g 1 * p) • e2 =
          -(g 0 • (c1 - (p : F) • e1) + g 1 • (c2 - (p : F) • e2)) := by
        apply eq_neg_of_add_eq_zero_left
        rw [← h]
        simp only [smul_sub, smul_smul]
        abel
      rw [h2]
      exact (levelSpace (K := F) (omLev r S) ℓ).neg_mem h1.2
    have hcoord : ∀ u, omLev r S u = ℓ → ((g 0 * p) • e1 + (g 1 * p) • e2) u = 0 :=
      fun u hu => hmem u (le_of_eq hu.symm)
    have hg0 : g 0 = 0 := by
      have := hcoord (Sum.inl a1.1) a1.2
      simpa [e1, e2, Pi.single_apply, hne', hp] using this
    have hg1 : g 1 = 0 := by
      have := hcoord (Sum.inl a2.1) a2.2
      simpa [e1, e2, Pi.single_apply, hne'.symm, hp] using this
    intro j
    fin_cases j
    · exact hg0
    · exact hg1
  have hdim : 2 ≤ Module.finrank F ↥(B ⊓ W₁) := by
    have := hli.fintype_card_le_finrank
    simpa using this
  have hι : 5 ≤ Fintype.card (Idx r) := by
    simp [Fintype.card_sum]
    omega
  exact false_of_fixed_escape_omega (Φm r F b c hirr) x hι hpodd hxp
    (fun w => Qm_mulVec hxΩ w) hW₁mem (fun w hw => Qm_eq_zero_of_mem_eSub hw) hdim
    (fun g hg hcomm w hw => ((hfix g hg hcomm).2 i hiS w).1 hw)

end Escape

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaMinus
