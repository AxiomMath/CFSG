module

public import CFSG.LieType.SpecialLinear.ExteriorModel.Minor

public section

open Module

namespace CFSG.LieType.SpecialLinear.ExteriorModel

open Matrix

variable {R : Type*} [CommRing R] {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ι → ℕ}

abbrev KIdx (n : ℕ) (d : ι → ℕ) : Type _ := (i : ι) → Set.powersetCard (Fin n) (d i)

@[expose] noncomputable def kronMinor (g : ι → Matrix (Fin n) (Fin n) R) :
    Matrix (KIdx n d) (KIdx n d) R :=
  Matrix.of fun s t => ∏ i, minor (g i) (s i) (t i)

omit [DecidableEq ι] in
theorem kronMinor_apply (g : ι → Matrix (Fin n) (Fin n) R) (s t : KIdx n d) :
    kronMinor g s t = ∏ i, minor (g i) (s i) (t i) := rfl

theorem kronMinor_mul (g h : ι → Matrix (Fin n) (Fin n) R) :
    kronMinor (d := d) (fun i => g i * h i) = kronMinor g * kronMinor h := by
  ext s t
  rw [kronMinor_apply, Matrix.mul_apply]
  calc ∏ i, minor (g i * h i) (s i) (t i)
      = ∏ i, ∑ u : Set.powersetCard (Fin n) (d i),
          minor (g i) (s i) u * minor (h i) u (t i) :=
        Finset.prod_congr rfl fun i _ => minor_mul (g i) (h i) (s i) (t i)
    _ = ∑ u : KIdx n d, ∏ i, minor (g i) (s i) (u i) * minor (h i) (u i) (t i) :=
        Fintype.prod_sum _
    _ = ∑ u : KIdx n d, kronMinor g s u * kronMinor h u t := by
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [Finset.prod_mul_distrib, kronMinor_apply, kronMinor_apply]

omit [DecidableEq ι] in
theorem kronMinor_one :
    kronMinor (d := d) (fun _ => (1 : Matrix (Fin n) (Fin n) R)) = 1 := by
  ext s t
  rw [kronMinor_apply, Matrix.one_apply]
  simp only [minor_one]
  rw [Fintype.prod_boole]
  by_cases h : ∀ i, s i = t i
  · simp only [if_pos h, if_pos (funext h)]
  · simp only [if_neg h, if_neg fun hst => h (congrFun hst)]

omit [DecidableEq ι] in
theorem kronMinor_transpose (g : ι → Matrix (Fin n) (Fin n) R) :
    kronMinor (d := d) (fun i => (g i)ᵀ) = (kronMinor g)ᵀ := by
  ext s t
  rw [kronMinor_apply, Matrix.transpose_apply, kronMinor_apply]
  simp only [minor_transpose]

omit [DecidableEq ι] in
theorem kronMinor_map {S : Type*} [CommRing S] (φ : R →+* S)
    (g : ι → Matrix (Fin n) (Fin n) R) :
    kronMinor (d := d) (fun i => (g i).map φ) = (kronMinor g).map φ := by
  ext s t
  rw [kronMinor_apply, Matrix.map_apply, kronMinor_apply, map_prod]
  exact Finset.prod_congr rfl fun i _ => minor_map φ (g i) (s i) (t i)

omit [DecidableEq ι] in
theorem kronMinor_diagonal (e : ι → Fin n → R) :
    kronMinor (d := d) (fun i => Matrix.diagonal (e i)) =
      Matrix.diagonal fun s => ∏ i, ∏ a ∈ ((s i : Set.powersetCard (Fin n) (d i)) : Finset (Fin n)), e i a := by
  ext s t
  rw [kronMinor_apply, Matrix.diagonal_apply]
  simp only [minor_diagonal, Fintype.prod_ite_zero]
  by_cases h : ∀ i, s i = t i
  · simp only [if_pos h, if_pos (funext h)]
  · simp only [if_neg h, if_neg fun hst => h (congrFun hst)]

theorem kronMinor_mul_eq_one {g h : ι → Matrix (Fin n) (Fin n) R} (hgh : ∀ i, g i * h i = 1) :
    kronMinor (d := d) g * kronMinor h = 1 := by
  rw [← kronMinor_mul]
  have hfun : (fun i => g i * h i) = fun _ => (1 : Matrix (Fin n) (Fin n) R) := funext hgh
  rw [hfun, kronMinor_one]

omit [DecidableEq ι] in
theorem kronMinor_one_add_single (h2 : (2 : R) = 0) {a b : Fin n} (hab : a ≠ b) (x : ι → R)
    (s t : KIdx n d) :
    kronMinor (fun i => 1 + Matrix.single a b (x i)) s t =
      ∏ i, (if s i = t i then 1
        else if b ∈ ((t i : Set.powersetCard (Fin n) (d i)) : Finset (Fin n)) ∧
            a ∉ ((t i : Set.powersetCard (Fin n) (d i)) : Finset (Fin n)) ∧
            ((s i : Set.powersetCard (Fin n) (d i)) : Finset (Fin n)) =
              insert a (((t i : Set.powersetCard (Fin n) (d i)) : Finset (Fin n)).erase b)
          then x i else 0) := by
  rw [kronMinor_apply]
  exact Finset.prod_congr rfl fun i _ => minor_one_add_single h2 hab (x i) (s i) (t i)

@[expose] def kdeg (s : KIdx n d) : ℕ :=
  ∑ i, ∑ a ∈ ((s i : Set.powersetCard (Fin n) (d i)) : Finset (Fin n)), (a : ℕ)

@[expose] def initSeg {k : ℕ} (hk : k ≤ n) : Set.powersetCard (Fin n) k :=
  ⟨Finset.univ.filter fun a : Fin n => (a : ℕ) < k, by
    have h : Finset.univ.filter (fun a : Fin n => (a : ℕ) < k) =
        Finset.univ.map (Fin.castLEEmb hk) := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
      constructor
      · intro ha
        exact ⟨⟨a.val, ha⟩, by simp⟩
      · rintro ⟨j, hj⟩
        rw [← hj]
        simp
    change (Finset.univ.filter (fun a : Fin n => (a : ℕ) < k)).card = k
    rw [h, Finset.card_map, Finset.card_univ, Fintype.card_fin]⟩

theorem mem_initSeg {k : ℕ} (hk : k ≤ n) (a : Fin n) :
    a ∈ ((initSeg hk : Set.powersetCard (Fin n) k) : Finset (Fin n)) ↔ (a : ℕ) < k := by
  simp [initSeg]

theorem val_initSeg {k : ℕ} (hk : k ≤ n) :
    ((initSeg hk : Set.powersetCard (Fin n) k) : Finset (Fin n)) =
      Finset.univ.map (Fin.castLEEmb hk) := by
  ext a
  rw [mem_initSeg]
  simp only [Finset.mem_map, Finset.mem_univ, true_and]
  constructor
  · intro ha
    exact ⟨⟨a.val, ha⟩, by simp⟩
  · rintro ⟨j, hj⟩
    rw [← hj]
    simp

@[expose] def ktop (hd : ∀ i, d i ≤ n) : KIdx n d := fun i => initSeg (hd i)

theorem initSeg_sum_le_and_lt {k : ℕ} (hk : k ≤ n) (s : Set.powersetCard (Fin n) k) :
    (∑ a ∈ ((initSeg hk : Set.powersetCard (Fin n) k) : Finset (Fin n)), (a : ℕ) ≤
        ∑ a ∈ (s : Finset (Fin n)), (a : ℕ)) ∧
      (s ≠ initSeg hk →
        ∑ a ∈ ((initSeg hk : Set.powersetCard (Fin n) k) : Finset (Fin n)), (a : ℕ) <
          ∑ a ∈ (s : Finset (Fin n)), (a : ℕ)) := by
  classical
  let e : Fin k ↪o Fin n := s.val.orderEmbOfFin s.prop
  have hkey : ∀ j : Fin k, (j : ℕ) ≤ (e j : ℕ) := by
    intro j
    induction j using Fin.strong_induction_on with
    | h j ih =>
      obtain ⟨jv, hjv⟩ := j
      cases jv with
      | zero => exact Nat.zero_le _
      | succ m =>
        have hi : (⟨m, Nat.lt_of_succ_lt hjv⟩ : Fin k) < ⟨m + 1, hjv⟩ := by simp
        have hprev := ih ⟨m, Nat.lt_of_succ_lt hjv⟩ hi
        have hlt : e ⟨m, Nat.lt_of_succ_lt hjv⟩ < e ⟨m + 1, hjv⟩ := e.strictMono hi
        have hval : (e ⟨m, Nat.lt_of_succ_lt hjv⟩ : ℕ) < (e ⟨m + 1, hjv⟩ : ℕ) := hlt
        have hprev' : m ≤ (e ⟨m, Nat.lt_of_succ_lt hjv⟩ : ℕ) := hprev
        change m + 1 ≤ (e ⟨m + 1, hjv⟩ : ℕ)
        omega
  have hsum_s : ∑ a ∈ (s : Finset (Fin n)), (a : ℕ) = ∑ j : Fin k, (e j : ℕ) := by
    rw [show (s : Finset (Fin n)) = Finset.univ.map e.toEmbedding from
      (Finset.map_orderEmbOfFin_univ s.val s.prop).symm]
    simp [Finset.sum_map]
  have hsum_i : ∑ a ∈ ((initSeg hk : Set.powersetCard (Fin n) k) : Finset (Fin n)), (a : ℕ) =
      ∑ j : Fin k, (j : ℕ) := by
    rw [val_initSeg]
    simp [Finset.sum_map]
  have hmem_s : ∀ a, a ∈ (s : Finset (Fin n)) ↔ ∃ j : Fin k, e j = a := by
    intro a
    rw [show (s : Finset (Fin n)) = Finset.univ.map e.toEmbedding from
      (Finset.map_orderEmbOfFin_univ s.val s.prop).symm]
    simp
  constructor
  · rw [hsum_i, hsum_s]
    exact Finset.sum_le_sum fun j _ => hkey j
  · intro hne
    rw [hsum_i, hsum_s]
    have hex : ∃ j : Fin k, (j : ℕ) < (e j : ℕ) := by
      by_contra hall
      have hall' : ∀ j : Fin k, (e j : ℕ) ≤ (j : ℕ) := by
        intro j
        by_contra h
        exact hall ⟨j, Nat.not_le.mp h⟩
      have hee : (e : Fin k → Fin n) = Fin.castLE hk := by
        funext j
        exact Fin.ext (le_antisymm (by simpa using hall' j) (hkey j))
      apply hne
      apply Subtype.ext
      ext a
      rw [hmem_s a, mem_initSeg]
      constructor
      · rintro ⟨j, rfl⟩
        rw [hee]
        exact j.isLt
      · intro ha
        exact ⟨⟨a.val, ha⟩, by rw [hee]; exact Fin.ext (by simp)⟩
    obtain ⟨j, hj⟩ := hex
    exact Finset.sum_lt_sum (fun i _ => hkey i) ⟨j, Finset.mem_univ _, hj⟩

theorem initSeg_sum_le {k : ℕ} (hk : k ≤ n) (s : Set.powersetCard (Fin n) k) :
    ∑ a ∈ ((initSeg hk : Set.powersetCard (Fin n) k) : Finset (Fin n)), (a : ℕ) ≤
      ∑ a ∈ (s : Finset (Fin n)), (a : ℕ) :=
  (initSeg_sum_le_and_lt hk s).1

theorem eq_initSeg_of_sum_le {k : ℕ} (hk : k ≤ n) {s : Set.powersetCard (Fin n) k}
    (h : ∑ a ∈ (s : Finset (Fin n)), (a : ℕ) ≤
      ∑ a ∈ ((initSeg hk : Set.powersetCard (Fin n) k) : Finset (Fin n)), (a : ℕ)) :
    s = initSeg hk := by
  by_contra hne
  exact not_lt_of_ge h ((initSeg_sum_le_and_lt hk s).2 hne)

omit [DecidableEq ι] in
theorem kdeg_ktop_le (hd : ∀ i, d i ≤ n) (s : KIdx n d) : kdeg (ktop hd) ≤ kdeg s := by
  simp only [kdeg, ktop]
  exact Finset.sum_le_sum fun i _ => initSeg_sum_le (hd i) (s i)

omit [DecidableEq ι] in
theorem eq_ktop_of_kdeg_le (hd : ∀ i, d i ≤ n) {s : KIdx n d}
    (h : kdeg s ≤ kdeg (ktop hd)) : s = ktop hd := by
  have hle : ∀ i, ∑ a ∈ ((initSeg (hd i) : Set.powersetCard (Fin n) (d i)) : Finset (Fin n)),
      (a : ℕ) ≤ ∑ a ∈ ((s i : Set.powersetCard (Fin n) (d i)) : Finset (Fin n)), (a : ℕ) :=
    fun i => initSeg_sum_le (hd i) (s i)
  have htot : kdeg s = kdeg (ktop hd) := le_antisymm h (kdeg_ktop_le hd s)
  have hper : ∀ i, ∑ a ∈ ((s i : Set.powersetCard (Fin n) (d i)) : Finset (Fin n)), (a : ℕ) =
      ∑ a ∈ ((initSeg (hd i) : Set.powersetCard (Fin n) (d i)) : Finset (Fin n)), (a : ℕ) := by
    intro i
    by_contra hne
    have hlt : ∑ a ∈ ((initSeg (hd i) : Set.powersetCard (Fin n) (d i)) : Finset (Fin n)),
        (a : ℕ) < ∑ a ∈ ((s i : Set.powersetCard (Fin n) (d i)) : Finset (Fin n)), (a : ℕ) :=
      lt_of_le_of_ne (hle i) (Ne.symm hne)
    have hstrict : kdeg (ktop hd) < kdeg s := by
      simp only [kdeg, ktop]
      exact Finset.sum_lt_sum (fun j _ => hle j) ⟨i, Finset.mem_univ _, hlt⟩
    omega
  funext i
  exact eq_initSeg_of_sum_le (hd i) (le_of_eq (hper i))

theorem minor_permMatrix (h2 : (2 : R) = 0) (σ : Equiv.Perm (Fin n)) {k : ℕ}
    (s t : Set.powersetCard (Fin n) k) :
    minor (σ.permMatrix R) s t =
      if ((s : Finset (Fin n))).map σ.toEmbedding = (t : Finset (Fin n)) then 1 else 0 := by
  classical
  have hneg : (-1 : R) = 1 := by
    have h : (1 : R) + 1 = 0 := by rw [one_add_one_eq_two]; exact h2
    exact neg_eq_of_add_eq_zero_left h
  have hsign : ∀ τ : Equiv.Perm (Fin k), (Equiv.Perm.sign τ : R) = 1 := by
    intro τ
    rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h | h
    · rw [h]; simp
    · rw [h]; simpa using hneg
  set es : Fin k → Fin n := (Set.powersetCard.ofFinEmbEquiv.symm s : Fin k → Fin n) with hes
  set et : Fin k → Fin n := (Set.powersetCard.ofFinEmbEquiv.symm t : Fin k → Fin n) with het
  have hes_inj : Function.Injective es := by
    rw [hes]; exact (Set.powersetCard.ofFinEmbEquiv.symm s).injective
  have het_inj : Function.Injective et := by
    rw [het]; exact (Set.powersetCard.ofFinEmbEquiv.symm t).injective
  have hes_mem : ∀ i, es i ∈ (s : Finset (Fin n)) := by
    intro i
    rw [hes]
    simpa [Set.powersetCard.ofFinEmbEquiv_symm_apply] using
      Finset.orderEmbOfFin_mem s.val s.prop i
  have het_mem : ∀ j, et j ∈ (t : Finset (Fin n)) := by
    intro j
    rw [het]
    simpa [Set.powersetCard.ofFinEmbEquiv_symm_apply] using
      Finset.orderEmbOfFin_mem t.val t.prop j
  have hA : (σ.permMatrix R).submatrix es et =
      Matrix.of fun i j => if σ (es i) = et j then (1 : R) else 0 := by
    ext i j
    change (σ.toPEquiv.toMatrix : Matrix (Fin n) (Fin n) R) (es i) (et j) =
      (if σ (es i) = et j then (1 : R) else 0)
    rw [PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
    simp only [Option.mem_some]
  rw [minor, ← hes, ← het, hA]
  by_cases hst : ((s : Finset (Fin n))).map σ.toEmbedding = (t : Finset (Fin n))
  · rw [if_pos hst]
    have hmem : ∀ i, σ (es i) ∈ (t : Finset (Fin n)) := by
      intro i
      have h1 : σ (es i) ∈ ((s : Finset (Fin n))).map σ.toEmbedding :=
        Finset.mem_map.mpr ⟨es i, hes_mem i, rfl⟩
      rwa [hst] at h1
    let f : Fin k → Fin k := fun i =>
      (t.val.orderIsoOfFin (Set.powersetCard.card_eq t)).symm ⟨σ (es i), hmem i⟩
    have hf : ∀ i, et (f i) = σ (es i) := by
      intro i
      rw [het, Set.powersetCard.ofFinEmbEquiv_symm_apply]
      change ↑((t.val.orderIsoOfFin (Set.powersetCard.card_eq t))
        ((t.val.orderIsoOfFin (Set.powersetCard.card_eq t)).symm ⟨σ (es i), hmem i⟩)) = σ (es i)
      rw [OrderIso.apply_symm_apply]
    have hf_inj : Function.Injective f := by
      intro i i' hii
      have h1 : σ (es i) = σ (es i') := by rw [← hf i, ← hf i', hii]
      exact hes_inj (σ.injective h1)
    have hmat : (Matrix.of fun i j => if σ (es i) = et j then (1 : R) else 0) =
        Matrix.of fun i j => if j = f i then (1 : R) else 0 := by
      ext i j
      have hiff : (σ (es i) = et j) ↔ (j = f i) := by
        constructor
        · intro h
          apply het_inj
          rw [hf i]
          exact h.symm
        · intro h
          rw [h, hf i]
      change (if σ (es i) = et j then (1 : R) else 0) = (if j = f i then (1 : R) else 0)
      by_cases h : σ (es i) = et j
      · have hji : j = f i := hiff.mp h
        simp only [if_pos h, if_pos hji]
      · have hji : ¬ (j = f i) := fun hji => h (hiff.mpr hji)
        simp only [if_neg h, if_neg hji]
    rw [hmat, det_of_row_eq_ite_single_of_injective f hf_inj]
    exact hsign _
  · rw [if_neg hst]
    have hex : ∃ i, σ (es i) ∉ (t : Finset (Fin n)) := by
      by_contra hall
      have hall' : ∀ i, σ (es i) ∈ (t : Finset (Fin n)) := by
        intro i
        by_contra h
        exact hall ⟨i, h⟩
      apply hst
      refine Finset.eq_of_subset_of_card_le ?_ ?_
      · intro a ha
        rw [Finset.mem_map] at ha
        obtain ⟨b, hb, rfl⟩ := ha
        obtain ⟨i, hi⟩ := exists_ofFinEmbEquiv_symm_eq_of_mem s
          (Set.powersetCard.mem_coe_iff.mp hb)
        have hb' : es i = b := by rw [hes]; exact hi
        rw [← hb']
        exact hall' i
      · rw [Finset.card_map, s.prop, t.prop]
    obtain ⟨i, hi⟩ := hex
    refine Matrix.det_eq_zero_of_row_eq_zero i fun j => ?_
    have hne : σ (es i) ≠ et j := fun h => hi (h ▸ het_mem j)
    simp [hne]

omit [DecidableEq ι] in
theorem kronMinor_permMatrix (h2 : (2 : R) = 0) (σ : ι → Equiv.Perm (Fin n))
    (s t : KIdx n d) :
    kronMinor (fun i => (σ i).permMatrix R) s t =
      if ∀ i, ((s i : Set.powersetCard (Fin n) (d i)) : Finset (Fin n)).map (σ i).toEmbedding =
          ((t i : Set.powersetCard (Fin n) (d i)) : Finset (Fin n)) then 1 else 0 := by
  rw [kronMinor_apply]
  simp only [minor_permMatrix h2]
  rw [Fintype.prod_boole]

theorem sum_le_and_eq_of_minor_ne_zero_of_upper {m : ℕ} {g : Matrix (Fin m) (Fin m) R}
    (hg : ∀ a b, b < a → g a b = 0) {k : ℕ} {s t : Set.powersetCard (Fin m) k}
    (h : minor g s t ≠ 0) :
    (∑ a ∈ (s : Finset (Fin m)), (a : ℕ) ≤ ∑ a ∈ (t : Finset (Fin m)), (a : ℕ)) ∧
      (∑ a ∈ (t : Finset (Fin m)), (a : ℕ) ≤ ∑ a ∈ (s : Finset (Fin m)), (a : ℕ) → s = t) := by
  classical
  let es : Fin k → Fin m :=
    ((Set.powersetCard.ofFinEmbEquiv.symm s : Fin k ↪o Fin m) : Fin k → Fin m)
  let et : Fin k → Fin m :=
    ((Set.powersetCard.ofFinEmbEquiv.symm t : Fin k ↪o Fin m) : Fin k → Fin m)
  have hes : es = (Set.powersetCard.ofFinEmbEquiv.symm s : Fin k → Fin m) := rfl
  have het : et = (Set.powersetCard.ofFinEmbEquiv.symm t : Fin k → Fin m) := rfl
  have hdet : (g.submatrix es et).det ≠ 0 := by
    simpa only [minor, hes, het] using h
  rw [Matrix.det_apply'] at hdet
  obtain ⟨σ, -, hσ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hdet
  have hprod : ∏ i, g (es (σ i)) (et i) ≠ 0 := by
    intro h0
    exact hσ (by simp [h0])
  have hne : ∀ i, g (es (σ i)) (et i) ≠ 0 := by
    intro i h0
    exact hprod (Finset.prod_eq_zero (Finset.mem_univ i) h0)
  have hle : ∀ i, (es (σ i) : ℕ) ≤ (et i : ℕ) := by
    intro i
    by_contra hlt
    exact hne i (hg _ _ (Fin.lt_def.mpr (Nat.not_le.mp hlt)))
  have hsum_es : ∑ i, (es i : ℕ) = ∑ a ∈ (s : Finset (Fin m)), (a : ℕ) := by
    rw [show (s : Finset (Fin m)) = Finset.univ.map
        (s.val.orderEmbOfFin s.prop).toEmbedding from
      (Finset.map_orderEmbOfFin_univ s.val s.prop).symm]
    rw [Finset.sum_map]
    rfl
  have hsum_et : ∑ i, (et i : ℕ) = ∑ a ∈ (t : Finset (Fin m)), (a : ℕ) := by
    rw [show (t : Finset (Fin m)) = Finset.univ.map
        (t.val.orderEmbOfFin t.prop).toEmbedding from
      (Finset.map_orderEmbOfFin_univ t.val t.prop).symm]
    rw [Finset.sum_map]
    rfl
  have hsum_sigma : ∑ i, (es (σ i) : ℕ) = ∑ i, (es i : ℕ) :=
    Equiv.sum_comp σ (fun i => (es i : ℕ))
  have hle_sum : ∑ i, (es (σ i) : ℕ) ≤ ∑ i, (et i : ℕ) :=
    Finset.sum_le_sum fun i _ => hle i
  have hle_sum' : ∑ a ∈ (s : Finset (Fin m)), (a : ℕ) ≤
      ∑ a ∈ (t : Finset (Fin m)), (a : ℕ) := by
    rw [← hsum_es, ← hsum_et, ← hsum_sigma]
    exact hle_sum
  refine ⟨hle_sum', ?_⟩
  · intro hle_rev
    have hsum_eq : ∑ i, (es (σ i) : ℕ) = ∑ i, (et i : ℕ) := by
      rw [hsum_sigma, hsum_es, hsum_et]
      exact le_antisymm hle_sum' hle_rev
    have hterm : ∀ i, (es (σ i) : ℕ) = (et i : ℕ) := fun i =>
      (Finset.sum_eq_sum_iff_of_le fun i _ => hle i).1 hsum_eq i (Finset.mem_univ i)
    have hfun : (fun i => et i) = fun i => es (σ i) :=
      funext fun i => Fin.ext (hterm i).symm
    have hrange_es : Set.range es = (s : Set (Fin m)) := by
      simpa [hes, Set.powersetCard.ofFinEmbEquiv_symm_apply] using
        s.val.range_orderEmbOfFin s.prop
    have hrange_et : Set.range et = (t : Set (Fin m)) := by
      simpa [het, Set.powersetCard.ofFinEmbEquiv_symm_apply] using
        t.val.range_orderEmbOfFin t.prop
    have hrange : Set.range et = Set.range es := by
      have h2 : Set.range et = Set.range (es ∘ σ) := by
        change Set.range (fun i => et i) = Set.range (fun i => es (σ i))
        rw [hfun]
      rw [h2, Set.range_comp, σ.surjective.range_eq, Set.image_univ]
    have hset : (t : Set (Fin m)) = (s : Set (Fin m)) := by
      rw [← hrange_et, ← hrange_es, hrange]
    exact (Subtype.ext (Finset.coe_injective (by simpa using hset))).symm

theorem minor_eq_zero_of_upper {m : ℕ} {g : Matrix (Fin m) (Fin m) R}
    (hg : ∀ a b, b < a → g a b = 0) {k : ℕ} {s t : Set.powersetCard (Fin m) k}
    (h : ∑ a ∈ (t : Finset (Fin m)), (a : ℕ) < ∑ a ∈ (s : Finset (Fin m)), (a : ℕ)) :
    minor g s t = 0 := by
  by_contra hne
  exact not_lt_of_ge (sum_le_and_eq_of_minor_ne_zero_of_upper hg hne).1 h

omit [DecidableEq ι] in
theorem kronMinor_eq_zero_of_upper {g : ι → Matrix (Fin n) (Fin n) R}
    (hg : ∀ i a b, b < a → g i a b = 0) {s t : KIdx n d} (h : kdeg t < kdeg s) :
    kronMinor g s t = 0 := by
  rw [kronMinor_apply]
  have hex : ∃ i, ∑ a ∈ ((t i : Set.powersetCard (Fin n) (d i)) : Finset (Fin n)), (a : ℕ) <
      ∑ a ∈ ((s i : Set.powersetCard (Fin n) (d i)) : Finset (Fin n)), (a : ℕ) := by
    by_contra hall
    have hall' : ∀ i, ∑ a ∈ ((s i : Set.powersetCard (Fin n) (d i)) : Finset (Fin n)), (a : ℕ) ≤
        ∑ a ∈ ((t i : Set.powersetCard (Fin n) (d i)) : Finset (Fin n)), (a : ℕ) := by
      intro i
      by_contra h'
      exact hall ⟨i, Nat.not_le.mp h'⟩
    have hle : kdeg s ≤ kdeg t := by
      simp only [kdeg]
      exact Finset.sum_le_sum fun i _ => hall' i
    omega
  obtain ⟨i, hi⟩ := hex
  exact Finset.prod_eq_zero (Finset.mem_univ i) (minor_eq_zero_of_upper (hg i) hi)

omit [DecidableEq ι] in
theorem kronMinor_eq_zero_of_upper_of_ne {g : ι → Matrix (Fin n) (Fin n) R}
    (hg : ∀ i a b, b < a → g i a b = 0) {s t : KIdx n d} (hne : s ≠ t) (h : kdeg t ≤ kdeg s) :
    kronMinor g s t = 0 := by
  rcases lt_or_ge (kdeg t) (kdeg s) with hlt | hge
  · exact kronMinor_eq_zero_of_upper hg hlt
  · have heq : kdeg s = kdeg t := le_antisymm hge h
    rw [kronMinor_apply]
    by_contra hprod
    have hfac : ∀ i, minor (g i) (s i) (t i) ≠ 0 := by
      intro i h0
      exact hprod (Finset.prod_eq_zero (Finset.mem_univ i) h0)
    have hle : ∀ i, ∑ a ∈ ((s i : Set.powersetCard (Fin n) (d i)) : Finset (Fin n)), (a : ℕ) ≤
        ∑ a ∈ ((t i : Set.powersetCard (Fin n) (d i)) : Finset (Fin n)), (a : ℕ) :=
      fun i => (sum_le_and_eq_of_minor_ne_zero_of_upper (hg i) (hfac i)).1
    have hsum : ∑ i, ∑ a ∈ ((s i : Set.powersetCard (Fin n) (d i)) : Finset (Fin n)), (a : ℕ) =
        ∑ i, ∑ a ∈ ((t i : Set.powersetCard (Fin n) (d i)) : Finset (Fin n)), (a : ℕ) := by
      simpa only [kdeg] using heq
    have hterm := fun i =>
      (Finset.sum_eq_sum_iff_of_le fun i _ => hle i).1 hsum i (Finset.mem_univ i)
    apply hne
    funext i
    exact (sum_le_and_eq_of_minor_ne_zero_of_upper (hg i) (hfac i)).2
      (le_of_eq (hterm i).symm)

omit [DecidableEq ι] in
theorem kronMinor_self_of_unitriangular {g : ι → Matrix (Fin n) (Fin n) R}
    (hg : ∀ i a b, b < a → g i a b = 0) (hg1 : ∀ i a, g i a a = 1) (s : KIdx n d) :
    kronMinor g s s = 1 := by
  rw [kronMinor_apply]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [minor]
  have htri : ((g i).submatrix (Set.powersetCard.ofFinEmbEquiv.symm (s i))
      (Set.powersetCard.ofFinEmbEquiv.symm (s i))).IsUpperTriangular := by
    intro j k hkj
    rw [Matrix.submatrix_apply]
    exact hg i _ _ ((Set.powersetCard.ofFinEmbEquiv.symm (s i)).strictMono hkj)
  rw [Matrix.det_of_isUpperTriangular htri]
  exact Finset.prod_eq_one fun j _ => by
    rw [Matrix.submatrix_apply]
    exact hg1 i _

theorem kronMinor_mulVec_single_ktop {g : ι → Matrix (Fin n) (Fin n) R}
    (hg : ∀ i a b, b < a → g i a b = 0) (hg1 : ∀ i a, g i a a = 1) (hd : ∀ i, d i ≤ n) :
    kronMinor g *ᵥ Pi.single (ktop hd) 1 = Pi.single (ktop hd) 1 := by
  rw [Matrix.mulVec_single_one]
  ext s
  change kronMinor g s (ktop hd) = (Pi.single (ktop hd) (1 : R) : KIdx n d → R) s
  by_cases hs : s = ktop hd
  · subst hs
    rw [kronMinor_self_of_unitriangular hg hg1]
    simp
  · rw [kronMinor_eq_zero_of_upper hg]
    · simp [Pi.single, hs]
    · rcases lt_or_ge (kdeg (ktop hd)) (kdeg s) with hlt | hge
      · exact hlt
      · exact absurd (eq_ktop_of_kdeg_le hd hge) hs

end CFSG.LieType.SpecialLinear.ExteriorModel
