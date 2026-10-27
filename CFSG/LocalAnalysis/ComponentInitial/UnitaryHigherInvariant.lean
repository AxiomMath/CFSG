module

public import CFSG.ClassicalGroups.UnitaryFlag.Triangular
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherRootData
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherFlagExtension

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open scoped Pointwise

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ}

theorem mem_hypUnitriangular_of_strict {h : UnitaryFieldData p f K} {g : hypSU h r ε}
    {N : Matrix (HypIndex r ε) (HypIndex r ε) K}
    (hg : ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) = 1 + N)
    (hN : ∀ x y, N x y ≠ 0 → fullPos x < fullPos y) : g ∈ hypUnitriangular h r ε := by
  rw [mem_hypUnitriangular, hg]
  refine ⟨fun x y hxy => ?_, fun x => ?_⟩
  · have hne : x ≠ y := fun h' => by
      rw [h'] at hxy
      exact lt_irrefl _ hxy
    rw [Matrix.add_apply, one_apply_ne hne, zero_add]
    by_contra h0
    exact absurd (hN x y h0) (not_lt.mpr hxy.le)
  · rw [Matrix.add_apply, one_apply_eq]
    by_contra h0
    have h0' : N x x ≠ 0 := fun h' => h0 (by rw [h', add_zero])
    exact lt_irrefl _ (hN x x h0')

theorem single_ne_zero_imp {a b x y : HypIndex r ε} {c : K} (hxy : single a b c x y ≠ 0) :
    x = a ∧ y = b := by
  rw [single_apply] at hxy
  split_ifs at hxy with h'
  · exact ⟨h'.1.symm, h'.2.symm⟩
  · exact absurd rfl hxy

theorem uRootElt_long_mem (h : UnitaryFieldData p f K) (j : Fin r)
    (t : uRootDom h (.inl j) (.inr j)) :
    uRootElt (ε := ε) h (inl_ne_inr j) t ∈ hypUnitriangular h r ε := by
  refine mem_hypUnitriangular_of_strict (N := single (.inl j) (.inr (.inr j)) (t : K)) ?_
    fun x y hxy => ?_
  · rw [coe_uRootElt, uRootMat_inl_inr_self]
  · obtain ⟨rfl, rfl⟩ := single_ne_zero_imp hxy
    have := j.2
    simp only [fullPos_inl, fullPos_inr_inr]
    omega

theorem uRootElt_short_mem (h : UnitaryFieldData p f K) {d j : Fin r} (hdj : d < j)
    (t : uRootDom h (.inl d) (.inl j)) :
    uRootElt (ε := ε) h (a := .inl d) (b := .inl j) (by simpa using hdj.ne) t ∈
      hypUnitriangular h r ε := by
  refine mem_hypUnitriangular_of_strict (N := single (.inl d) (.inl j) (t : K) -
    single (.inr (.inr j)) (.inr (.inr d)) (h.bar t)) ?_ fun x y hxy => ?_
  · rw [coe_uRootElt, uRootMat_inl_inl, add_sub_assoc]
  · rw [Matrix.sub_apply] at hxy
    have hj := j.2
    have hdj' : (d : ℕ) < j := hdj
    by_cases h1 : single (.inl d) (.inl j) (t : K) x y = 0
    · rw [h1, zero_sub, neg_ne_zero] at hxy
      obtain ⟨rfl, rfl⟩ := single_ne_zero_imp hxy
      simp only [fullPos_inr_inr]
      omega
    · obtain ⟨rfl, rfl⟩ := single_ne_zero_imp h1
      simpa using hdj'

@[expose] noncomputable def zHeisNil (d : Fin r) (k : Fin ε) (b : K) :
    Matrix (HypIndex r ε) (HypIndex r ε) K :=
  single (.inr (.inl k)) (.inr (.inr d)) 1 - single (.inl d) (.inr (.inl k)) 1 +
    single (.inl d) (.inr (.inr d)) b

theorem zHeis_gram (h : UnitaryFieldData p f K) (d : Fin r) (k : Fin ε) {b : K}
    (hb : b + h.bar b = -1) :
    (((1 : Matrix (HypIndex r ε) (HypIndex r ε) K) + zHeisNil d k b).map h.bar)ᵀ *
      hypGram r ε K * (1 + zHeisNil d k b) = hypGram r ε K := by
  set N := zHeisNil (ε := ε) d k b with hN
  have hT : (((1 : Matrix (HypIndex r ε) (HypIndex r ε) K) + N).map h.bar)ᵀ =
      1 + (N.map h.bar)ᵀ := by
    rw [Matrix.map_add _ (map_add h.bar), Matrix.map_one _ (map_zero _) (map_one _),
      transpose_add, transpose_one]
  have hexp : (1 + (N.map h.bar)ᵀ) * hypGram r ε K * (1 + N) = hypGram r ε K +
      ((N.map h.bar)ᵀ * hypGram r ε K + hypGram r ε K * N) +
      (N.map h.bar)ᵀ * hypGram r ε K * N := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
    abel
  have hNs : (N.map h.bar)ᵀ = single (.inr (.inr d)) (.inr (.inl k)) 1 -
      single (.inr (.inl k)) (.inl d) 1 + single (.inr (.inr d)) (.inl d) (h.bar b) := by
    rw [hN, zHeisNil, Matrix.map_add _ (map_add h.bar), Matrix.map_sub _ (map_sub h.bar),
      transpose_add, transpose_sub, conjTranspose_single, conjTranspose_single,
      conjTranspose_single, map_one]
  have h1 : (N.map h.bar)ᵀ * hypGram r ε K + hypGram r ε K * N =
      single (.inr (.inr d)) (.inr (.inr d)) (-1) := by
    rw [hNs, hN, zHeisNil]
    simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub,
      single_mul_hypGram, hypGram_mul_single, hypPartner_inl, hypPartner_inr_inl]
    rw [← hb, single_add]
    abel
  have h2 : (N.map h.bar)ᵀ * hypGram r ε K * N = single (.inr (.inr d)) (.inr (.inr d)) 1 := by
    rw [hNs, hN, zHeisNil]
    simp only [Matrix.add_mul, Matrix.sub_mul, single_mul_hypGram, hypPartner_inl,
      hypPartner_inr_inl, Matrix.mul_add, Matrix.mul_sub, single_mul_single_same, mul_one]
    simp [single_mul_single_of_ne]
  rw [hT, hexp, h1, h2, add_assoc, ← single_add, neg_add_cancel, single_zero, add_zero]

theorem det_zHeis (d : Fin r) (k : Fin ε) (b : K) :
    ((1 : Matrix (HypIndex r ε) (HypIndex r ε) K) + zHeisNil d k b).det = 1 := by
  set e : HypIndex r ε := .inl d
  set z : HypIndex r ε := .inr (.inl k)
  set f : HypIndex r ε := .inr (.inr d)
  have hez : e ≠ z := by simp [e, z]
  have hzf : z ≠ f := by simp [z, f]
  have hef : e ≠ f := by simp [e, f]
  have h12 : transvection e z (-1 : K) * transvection z f 1 =
      1 + (single e z (-1) + single z f 1 + single e f (-1)) := by
    rw [transvection, transvection, Matrix.add_mul, Matrix.one_mul, Matrix.mul_add,
      Matrix.mul_one, single_mul_single_same, mul_one]
    abel
  have hAC : (single e z (-1 : K) + single z f 1 + single e f (-1)) * single e f (b + 1) = 0 := by
    rw [Matrix.add_mul, Matrix.add_mul, single_mul_single_of_ne _ _ _ _ hez.symm,
      single_mul_single_of_ne _ _ _ _ hef.symm, single_mul_single_of_ne _ _ _ _ hef.symm,
      add_zero, add_zero]
  have hfac : (1 : Matrix (HypIndex r ε) (HypIndex r ε) K) + zHeisNil d k b =
      transvection e z (-1) * transvection z f 1 * transvection e f (b + 1) := by
    rw [h12, transvection, Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, hAC,
      add_zero, zHeisNil, single_add, ← single_neg, ← single_neg]
    abel
  rw [hfac, det_mul, det_mul, det_transvection_of_ne _ _ hez, det_transvection_of_ne _ _ hzf,
    det_transvection_of_ne _ _ hef, mul_one, mul_one]

@[expose] noncomputable def zHeisElt (h : UnitaryFieldData p f K) (d : Fin r) (k : Fin ε) {b : K}
    (hb : b + h.bar b = -1) : hypSU h r ε :=
  mkHypSU h (1 + zHeisNil d k b) (zHeis_gram h d k hb) (det_zHeis d k b)

theorem zHeisElt_mem (h : UnitaryFieldData p f K) (d : Fin r) (k : Fin ε) {b : K}
    (hb : b + h.bar b = -1) : zHeisElt h d k hb ∈ hypUnitriangular h r ε := by
  refine mem_hypUnitriangular_of_strict (N := zHeisNil d k b) rfl fun x y hxy => ?_
  have hd := d.2
  have hk := k.2
  rw [zHeisNil, Matrix.add_apply, Matrix.sub_apply] at hxy
  by_cases h1 : single (Sum.inr (Sum.inl k)) (Sum.inr (Sum.inr d)) (1 : K) x y = 0
  · rw [h1, zero_sub] at hxy
    by_cases h2 : single (Sum.inl d) (Sum.inr (Sum.inl k)) (1 : K) x y = 0
    · rw [h2, neg_zero, zero_add] at hxy
      obtain ⟨rfl, rfl⟩ := single_ne_zero_imp hxy
      simp only [fullPos_inl, fullPos_inr_inr]
      omega
    · obtain ⟨rfl, rfl⟩ := single_ne_zero_imp h2
      simp only [fullPos_inl, fullPos_inr_inl]
      omega
  · obtain ⟨rfl, rfl⟩ := single_ne_zero_imp h1
    simp only [fullPos_inr_inl, fullPos_inr_inr]
    omega

theorem unitriangular_sub_mem_posFlag {h : UnitaryFieldData p f K} {u : hypSU h r ε}
    (hu : u ∈ hypUnitriangular h r ε) {i : ℕ} {v : HypIndex r ε → K}
    (hv : v ∈ posFlag r ε K (i + 1)) :
    ((u : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ v - v ∈
      posFlag r ε K i := by
  obtain ⟨hbt, hdiag⟩ := mem_hypUnitriangular.mp hu
  intro a ha
  rw [Pi.sub_apply, sub_eq_zero]
  simp only [mulVec, dotProduct]
  rw [Finset.sum_eq_single a]
  · rw [hdiag, one_mul]
  · intro b _ hba
    rcases lt_or_gt_of_ne (fun h' => hba (fullPos_injective h')) with hlt | hgt
    · rw [hbt hlt, zero_mul]
    · rw [hv b (by omega), mul_zero]
  · simp

theorem mem_posFlag_succ_of_forall (h : UnitaryFieldData p f K) {d : ℕ} (hd : d < r)
    {v : HypIndex r ε → K} (hperp : ∀ j : Fin r, (j : ℕ) < d → v (.inr (.inr j)) = 0)
    (hU : ∀ u ∈ hypUnitriangular h r ε,
      ((u : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ v - v ∈
        posFlag r ε K d) :
    v ∈ posFlag r ε K (d + 1) := by
  set dd : Fin r := ⟨d, hd⟩
  obtain ⟨c, hcE, hc0⟩ := exists_mem_traceZero_ne_zero' h
  have hf : ∀ j : Fin r, v (.inr (.inr j)) = 0 := by
    intro j
    by_cases hj : (j : ℕ) < d
    · exact hperp j hj
    · have hmem : c ∈ uRootDom h (.inl j) (.inr j) := by
        rw [show (Sum.inr j : Fin r ⊕ Fin r) = (Sum.inl j).swap from rfl, uRootDom_swap]
        exact hcE
      have := hU _ (uRootElt_long_mem (ε := ε) h j ⟨c, hmem⟩) (.inl j) (by simp; omega)
      rw [coe_uRootElt, uRootMat_inl_inr_self, Matrix.add_mulVec, Matrix.one_mulVec,
        add_sub_cancel_left, single_mulVec] at this
      simpa [hc0] using this
  obtain ⟨b, hb⟩ := exists_add_bar_eq_neg_one h
  have hz : ∀ k : Fin ε, v (.inr (.inl k)) = 0 := by
    intro k
    have := hU _ (zHeisElt_mem h dd k hb) (.inl dd) (by simp [dd])
    change (((1 : Matrix (HypIndex r ε) (HypIndex r ε) K) + zHeisNil dd k b) *ᵥ v - v)
      (.inl dd) = 0 at this
    rw [Matrix.add_mulVec, Matrix.one_mulVec, add_sub_cancel_left, zHeisNil, Matrix.add_mulVec,
      Matrix.sub_mulVec, single_mulVec, single_mulVec, single_mulVec] at this
    simpa [hf] using this
  have he : ∀ j : Fin r, d < (j : ℕ) → v (.inl j) = 0 := by
    intro j hj
    have hdj : dd < j := hj
    have hmem : (1 : K) ∈ uRootDom h (.inl dd) (.inl j) := by
      rw [uRootDom_of_ne h (by simp)]
      trivial
    have := hU _ (uRootElt_short_mem (ε := ε) h hdj ⟨1, hmem⟩) (.inl dd) (by simp [dd])
    rw [coe_uRootElt, uRootMat_inl_inl, add_sub_assoc, Matrix.add_mulVec, Matrix.one_mulVec,
      add_sub_cancel_left, Matrix.sub_mulVec, single_mulVec, single_mulVec] at this
    simpa [hf] using this
  intro a ha
  rcases a with j | k | j
  · exact he j (by simpa using ha)
  · exact hz k
  · exact hf j

theorem sub_single_mem_posFlag {d : ℕ} (hd : d < r) {v : HypIndex r ε → K}
    (hv : v ∈ posFlag r ε K (d + 1)) :
    v - v (.inl ⟨d, hd⟩) • Pi.single (.inl ⟨d, hd⟩) (1 : K) ∈ posFlag r ε K d := by
  intro a ha
  by_cases had : a = .inl ⟨d, hd⟩
  · subst had
    simp
  · have hpos : d + 1 ≤ fullPos a := by
      have hne : fullPos a ≠ d := fun h' => had (fullPos_injective (by simpa using h'))
      omega
    simp [hv a hpos, had]

theorem eq_posFlag_or_succ_le (h : UnitaryFieldData p f K) {W : Submodule K (HypIndex r ε → K)}
    (hinv : ∀ u ∈ hypUnitriangular h r ε, ∀ v ∈ W,
      ((u : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ v ∈ W)
    (hiso : ∀ x ∈ W, ∀ y ∈ W, hypForm h r ε x y = 0) {d : ℕ} (hd : d < r)
    (hdW : posFlag r ε K d ≤ W) : W = posFlag r ε K d ∨ posFlag r ε K (d + 1) ≤ W := by
  classical
  by_cases hW : W ≤ posFlag r ε K d
  · exact Or.inl (le_antisymm hW hdW)
  right
  have hex : ∃ m, ∃ v ∈ W, v ∉ posFlag r ε K d ∧ v ∈ posFlag r ε K (m + 1) := by
    obtain ⟨v, hvW, hvd⟩ := Set.not_subset.mp hW
    exact ⟨2 * r + ε, v, hvW, hvd, fun a ha => absurd ha (by have := fullPos_lt a; omega)⟩
  obtain ⟨v, hvW, hvd, hvm⟩ := Nat.find_spec hex
  have hmin : ∀ m' < Nat.find hex,
      ¬ ∃ v ∈ W, v ∉ posFlag r ε K d ∧ v ∈ posFlag r ε K (m' + 1) :=
    fun m' hm' => Nat.find_min hex hm'
  have hdm : d ≤ Nat.find hex := by
    by_contra hlt
    exact hvd fun a ha => hvm a (by omega)
  rcases hdm.eq_or_lt with hdm | hdm
  ·
    rw [← hdm] at hvm
    have hrest := sub_single_mem_posFlag hd hvm
    have hc : v (.inl ⟨d, hd⟩) ≠ 0 := fun h0 => hvd (by simpa [h0] using hrest)
    have heW : (Pi.single (.inl ⟨d, hd⟩) (1 : K) : HypIndex r ε → K) ∈ W := by
      have : (Pi.single (.inl ⟨d, hd⟩) (1 : K) : HypIndex r ε → K) = (v (.inl ⟨d, hd⟩))⁻¹ •
          (v - (v - v (.inl ⟨d, hd⟩) • Pi.single (.inl ⟨d, hd⟩) 1)) := by
        rw [sub_sub_cancel, smul_smul, inv_mul_cancel₀ hc, one_smul]
      rw [this]
      exact W.smul_mem _ (W.sub_mem hvW (hdW hrest))
    intro w hw
    have := sub_single_mem_posFlag hd hw
    rw [show w = (w - w (.inl ⟨d, hd⟩) • Pi.single (.inl ⟨d, hd⟩) 1) +
      w (.inl ⟨d, hd⟩) • Pi.single (.inl ⟨d, hd⟩) 1 by abel]
    exact W.add_mem (hdW this) (W.smul_mem _ heW)
  · exfalso
    obtain ⟨m', hm'⟩ : ∃ m', Nat.find hex = m' + 1 := ⟨Nat.find hex - 1, by omega⟩
    have hU : ∀ u ∈ hypUnitriangular h r ε,
        ((u : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ v - v ∈
          posFlag r ε K d := by
      intro u hu
      by_contra hnot
      have hlow := unitriangular_sub_mem_posFlag hu hvm
      rw [hm'] at hlow
      exact hmin m' (by omega) ⟨_, W.sub_mem (hinv u hu v hvW) hvW, hnot, hlow⟩
    have hperp : ∀ j : Fin r, (j : ℕ) < d → v (.inr (.inr j)) = 0 := fun j hj => by
      rw [← hypForm_single_inl h j v]
      refine hiso _ (hdW fun a ha => ?_) v hvW
      have : a ≠ .inl j := by
        rintro rfl
        simp only [fullPos_inl] at ha
        omega
      simp [this]
    have hv1 := mem_posFlag_succ_of_forall h hd hperp hU
    exact hmin m' (by omega) ⟨v, hvW, hvd, fun a ha => hv1 a (by omega)⟩

theorem posFlag_isotropic (h : UnitaryFieldData p f K) {d : ℕ} (hd : d ≤ r) :
    ∀ x ∈ posFlag r ε K d, ∀ y ∈ posFlag r ε K d, hypForm h r ε x y = 0 := by
  intro x hx y hy
  rw [hypForm_apply]
  refine Finset.sum_eq_zero fun a _ => ?_
  rcases a with j | k | j
  · rw [hypPartner_inl, hy _ (by simp; omega), mul_zero]
  · rw [hx _ (by simp; omega), map_zero, zero_mul]
  · rw [hx _ (by simp; omega), map_zero, zero_mul]

theorem smul_posFlag {h : UnitaryFieldData p f K} {u : hypSU h r ε}
    (hu : u ∈ hypUnitriangular h r ε) (d : ℕ) : u • posFlag r ε K d = posFlag r ε K d := by
  rw [Subgroup.smul_def]
  exact smul_eq_of_mulVec_mem
    (blockTriangular_fullPos_iff.mp (mem_hypUnitriangular.mp hu).1 d)
    (blockTriangular_fullPos_iff.mp (mem_hypUnitriangular.mp (inv_mem hu)).1 d)

theorem posFlag_zero : posFlag r ε K 0 = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  exact (Submodule.mem_bot K).mpr (funext fun a => hv a (Nat.zero_le _))

theorem finrank_posFlag {d : ℕ} (hd : d ≤ r) : Module.finrank K (posFlag r ε K d) = d := by
  rw [← isoFlag_eq_posFlag hd, isoFlag]
  have hli : LinearIndependent K
      (fun j : Fin r => (Pi.single (Sum.inl j) (1 : K) : HypIndex r ε → K)) := by
    have := (Pi.basisFun K (HypIndex r ε)).linearIndependent.comp Sum.inl Sum.inl_injective
    convert this using 1
    funext j
    simp
  have hset : {j : Fin r | (j : ℕ) < d} = Set.range (Fin.castLE hd) := by
    ext j
    constructor
    · intro hj
      exact ⟨⟨j, hj⟩, rfl⟩
    · rintro ⟨k, rfl⟩
      exact k.2
  rw [hset, ← Set.range_comp, finrank_span_eq_card (hli.comp _ (Fin.castLE_injective hd)),
    Fintype.card_fin]

theorem posFlag_one (hr : 1 ≤ r) :
    posFlag r ε K 1 = K ∙ (Pi.single (.inl ⟨0, hr⟩) (1 : K) : HypIndex r ε → K) := by
  apply le_antisymm
  · intro v hv
    have hrest := sub_single_mem_posFlag hr hv
    rw [posFlag_zero, Submodule.mem_bot, sub_eq_zero] at hrest
    rw [hrest]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · rw [Submodule.span_singleton_le_iff_mem]
    intro a ha
    have : a ≠ .inl ⟨0, hr⟩ := by
      rintro rfl
      simp at ha
    simp [this]

theorem le_posFlag_of_isotropic (h : UnitaryFieldData p f K) (hε : ε ≤ 1)
    {W : Submodule K (HypIndex r ε → K)} (hiso : ∀ x ∈ W, ∀ y ∈ W, hypForm h r ε x y = 0)
    (hrW : posFlag r ε K r ≤ W) : W ≤ posFlag r ε K r := by
  intro x hx
  have hf : ∀ j : Fin r, x (.inr (.inr j)) = 0 := fun j => by
    rw [← hypForm_single_inl h j x]
    refine hiso _ (hrW fun a ha => ?_) x hx
    have : a ≠ .inl j := by
      rintro rfl
      simp only [fullPos_inl] at ha
      omega
    simp [this]
  have hz : ∀ k : Fin ε, x (.inr (.inl k)) = 0 := by
    intro k
    have hxx := hiso x hx x hx
    rw [hypForm_apply, Fintype.sum_sum_type, Fintype.sum_sum_type] at hxx
    simp only [hypPartner_inl, hypPartner_inr_inl, hypPartner_inr_inr, hf, mul_zero,
      Finset.sum_const_zero, zero_add, map_zero, zero_mul, add_zero] at hxx
    obtain rfl : ε = 1 := by have := k.2; omega
    rw [Fin.sum_univ_one] at hxx
    have hk : k = 0 := Fin.fin_one_eq_zero k
    subst hk
    rcases mul_eq_zero.mp hxx with h0 | h0
    · exact (map_eq_zero h.bar).mp h0
    · exact h0
  intro a ha
  rcases a with j | k | j
  · simp at ha
    omega
  · exact hz k
  · exact hf j

theorem unitriangular_invariant_isotropic_subspaces (h : UnitaryFieldData p f K) (hr : 1 ≤ r)
    (hε : ε ≤ 1) :
    hypFlag h r ε 1 = K ∙ (Pi.single (.inl ⟨0, hr⟩) (1 : K) : HypIndex r ε → K) ∧
    (∀ v : HypIndex r ε → K, (∀ u ∈ hypUnitriangular h r ε,
      ((u : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ v = v) ↔
        v ∈ hypFlag h r ε 1) ∧
    (∀ W : Submodule K (HypIndex r ε → K), (∀ x ∈ W, ∀ y ∈ W, hypForm h r ε x y = 0) →
      (∀ u ∈ hypUnitriangular h r ε, u • W = W) → ∃ d ≤ r, W = hypFlag h r ε d) ∧
    (∀ d ≤ r, (∀ x ∈ hypFlag h r ε d, ∀ y ∈ hypFlag h r ε d, hypForm h r ε x y = 0) ∧
      ∀ u ∈ hypUnitriangular h r ε, u • hypFlag h r ε d = hypFlag h r ε d) ∧
    ∀ W : ℕ → Submodule K (HypIndex r ε → K), IsIsotropicChain (hypForm h r ε) r W →
      (∀ i ≤ r, ∀ u ∈ hypUnitriangular h r ε, u • W i = W i) →
      ∀ i ≤ r, W i = hypFlag h r ε i := by
  have hF : ∀ d ≤ r, hypFlag h r ε d = posFlag r ε K d := fun d hd =>
    hypFlag_eq_posFlag h hε (by omega)
  have hclass : ∀ W : Submodule K (HypIndex r ε → K),
      (∀ x ∈ W, ∀ y ∈ W, hypForm h r ε x y = 0) →
      (∀ u ∈ hypUnitriangular h r ε, u • W = W) → ∃ d ≤ r, W = posFlag r ε K d := by
    intro W hiso hW
    have hinv : ∀ u ∈ hypUnitriangular h r ε, ∀ v ∈ W,
        ((u : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ v ∈ W :=
      fun u hu v hv => by
        have h1 : ((u : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ v ∈
            u • W := (Submodule.mem_smul_pointwise_iff_exists _ u W).mpr ⟨v, hv, rfl⟩
        rw [hW u hu] at h1
        exact h1
    have key : ∀ n d, d + n = r → posFlag r ε K d ≤ W → ∃ d' ≤ r, W = posFlag r ε K d' := by
      intro n
      induction n with
      | zero =>
        intro d hd hdW
        have hdr : d = r := by omega
        rw [hdr] at hdW
        exact ⟨r, le_rfl, le_antisymm (le_posFlag_of_isotropic h hε hiso hdW) hdW⟩
      | succ n ih =>
        intro d hd hdW
        rcases eq_posFlag_or_succ_le h hinv hiso (by omega) hdW with hWd | hle
        · exact ⟨d, by omega, hWd⟩
        · exact ih (d + 1) (by omega) hle
    exact key r 0 (by omega) (by rw [posFlag_zero]; exact bot_le)
  refine ⟨by rw [hF 1 hr, posFlag_one hr], fun v => ⟨fun hv => ?_, fun hv u hu => ?_⟩,
    fun W hiso hW => ?_, fun d hd => ?_, fun W hW hinv i hi => ?_⟩
  · rw [hF 1 hr]
    refine mem_posFlag_succ_of_forall h hr (fun j hj => absurd hj (Nat.not_lt_zero _))
      fun u hu => ?_
    rw [hv u hu, sub_self]
    exact Submodule.zero_mem _
  · rw [hF 1 hr] at hv
    have := unitriangular_sub_mem_posFlag hu hv
    rw [posFlag_zero, Submodule.mem_bot, sub_eq_zero] at this
    exact this
  · obtain ⟨d, hd, rfl⟩ := hclass W hiso hW
    exact ⟨d, hd, (hF d hd).symm⟩
  · rw [hF d hd]
    exact ⟨posFlag_isotropic h hd, fun u hu => smul_posFlag hu d⟩
  · obtain ⟨d, hd, hWd⟩ := hclass (W i) (hW.2.2 i hi) (hinv i hi)
    have hdim := hW.1 i hi
    rw [hWd, finrank_posFlag hd] at hdim
    rw [hWd, hdim, hF i hi]

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
