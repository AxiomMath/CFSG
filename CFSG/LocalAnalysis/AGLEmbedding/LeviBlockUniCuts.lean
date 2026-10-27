module

public import CFSG.ClassicalGroups.UnitaryFlag.Triangular
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherParabolicData
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockUniMatrix

public section

namespace CFSG.AGLEmbedding.LeviBlock

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open scoped Pointwise

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ}

@[expose] def IsHypCut {h : UnitaryFieldData p f K} (Q : Subgroup (hypSU h r ε)) (c : ℕ) : Prop :=
  ∀ g ∈ Q, ∀ u w : HypIndex r ε, fullPos w < c → c ≤ fullPos u →
    ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) u w = 0

theorem apply_eq_zero_of_mulVec_mem_posFlag {M : Matrix (HypIndex r ε) (HypIndex r ε) K} {c : ℕ}
    (hM : ∀ v ∈ posFlag r ε K c, M *ᵥ v ∈ posFlag r ε K c) {u w : HypIndex r ε}
    (hw : fullPos w < c) (hu : c ≤ fullPos u) : M u w = 0 := by
  have hv : (Pi.single w 1 : HypIndex r ε → K) ∈ posFlag r ε K c := by
    intro a ha
    have : a ≠ w := by
      rintro rfl
      omega
    simp [this]
  have := hM _ hv u hu
  rwa [mulVec_single_one, col_apply] at this

theorem isHypCut_zero {h : UnitaryFieldData p f K} (Q : Subgroup (hypSU h r ε)) : IsHypCut Q 0 :=
  fun _ _ _ _ hw => absurd hw (Nat.not_lt_zero _)

theorem isHypCut_flagStabilizer (h : UnitaryFieldData p f K) (hε : ε ≤ 1) {I : Set ℕ} {c : ℕ}
    (hc : c ∈ I) (hcr : c ≤ r) : IsHypCut (flagStabilizer h r ε I) c := by
  intro g hg u w hw hu
  have hfix := mem_flagStabilizer.mp hg c hc
  rw [hypFlag_eq_posFlag h hε (by omega)] at hfix
  refine apply_eq_zero_of_mulVec_mem_posFlag (fun v hv => ?_) hw hu
  rw [← hfix]
  exact Submodule.smul_mem_pointwise_smul v g _ hv

theorem isHypCut_flagStabilizer_orth (h : UnitaryFieldData p f K) (hε : ε ≤ 1) {I : Set ℕ}
    {t : ℕ} (ht : t ∈ I) (htr : t ≤ r) : IsHypCut (flagStabilizer h r ε I) (2 * r + ε - t) := by
  intro g hg u w hw hu
  have hfix := mem_flagStabilizer.mp hg t ht
  rw [hypFlag, ite_eq_left htr] at hfix
  refine apply_eq_zero_of_mulVec_mem_posFlag (fun v hv => ?_) hw hu
  rw [← orthogonal_isoFlag h hε htr] at hv ⊢
  exact mulVec_mem_orthogonal h hfix hv

theorem mulVec_mem_posFlag_of_apply_eq_zero {M : Matrix (HypIndex r ε) (HypIndex r ε) K} {c : ℕ}
    (hM : ∀ u w, fullPos w < c → c ≤ fullPos u → M u w = 0) {v : HypIndex r ε → K}
    (hv : v ∈ posFlag r ε K c) : M *ᵥ v ∈ posFlag r ε K c := by
  intro u hu
  simp only [mulVec, dotProduct]
  refine Finset.sum_eq_zero fun w _ => ?_
  by_cases hw : c ≤ fullPos w
  · rw [hv w hw, mul_zero]
  · rw [hM u w (not_le.mp hw) hu, zero_mul]

theorem smul_hypFlag_eq_of_apply_eq_zero (h : UnitaryFieldData p f K) (hε : ε ≤ 1)
    {g : hypSU h r ε} {c : ℕ} (hcr : c ≤ r)
    (hg : ∀ u w, fullPos w < c → c ≤ fullPos u →
      ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) u w = 0)
    (hg' : ∀ u w, fullPos w < c → c ≤ fullPos u →
      ((g⁻¹ : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) u w = 0) :
    g • hypFlag h r ε c = hypFlag h r ε c := by
  rw [hypFlag_eq_posFlag h hε (by omega), Subgroup.smul_def]
  exact smul_eq_of_mulVec_mem (fun v hv => mulVec_mem_posFlag_of_apply_eq_zero hg hv)
    fun v hv => mulVec_mem_posFlag_of_apply_eq_zero hg' hv

@[expose] noncomputable def hypBlockHom {h : UnitaryFieldData p f K} {Q : Subgroup (hypSU h r ε)}
    {ι : Type} [Fintype ι] [DecidableEq ι] {φ : ι → HypIndex r ε} (hφ : Function.Injective φ)
    {a b : ℕ} (hrange : ∀ x, x ∈ Set.range φ ↔ a ≤ fullPos x ∧ fullPos x < b)
    (ha : IsHypCut Q a) (hb : IsHypCut Q b) : ↥Q →* GL ι K :=
  MonoidHom.toHomUnits
    { toFun := fun g =>
        (((g : hypSU h r ε) : GL (HypIndex r ε) K) :
          Matrix (HypIndex r ε) (HypIndex r ε) K).submatrix φ φ
      map_one' := by
        simp only [OneMemClass.coe_one, Units.val_one]
        exact submatrix_one _ hφ
      map_mul' := fun g g' => by
        simp only [Subgroup.coe_mul, Units.val_mul]
        exact submatrix_mul_of_cuts hφ hrange (ha g g.2) (hb g' g'.2) }

@[expose] def eIdx (r ε : ℕ) {a b : ℕ} (hbr : b ≤ r) (k : Fin (b - a)) : HypIndex r ε :=
  Sum.inl ⟨a + k, by have := k.isLt; omega⟩

theorem eIdx_injective {a b : ℕ} (hbr : b ≤ r) : Function.Injective (eIdx r ε (a := a) hbr) := by
  intro k k' hk
  simp only [eIdx, Sum.inl.injEq, Fin.mk.injEq, Nat.add_left_cancel_iff] at hk
  exact Fin.ext hk

theorem fullPos_eIdx {a b : ℕ} (hbr : b ≤ r) (k : Fin (b - a)) :
    fullPos (eIdx r ε hbr k) = a + k :=
  rfl

theorem mem_range_eIdx {a b : ℕ} (hbr : b ≤ r) (x : HypIndex r ε) :
    x ∈ Set.range (eIdx r ε (a := a) hbr) ↔ a ≤ fullPos x ∧ fullPos x < b := by
  constructor
  · rintro ⟨k, rfl⟩
    rw [fullPos_eIdx]
    have := k.isLt
    omega
  · intro hx
    rcases x with ⟨i, hi⟩ | ⟨l, hl⟩ | ⟨i, hi⟩
    · simp only [fullPos_inl] at hx
      exact ⟨⟨i - a, by omega⟩, by simp only [eIdx, Sum.inl.injEq, Fin.mk.injEq]; omega⟩
    · simp only [fullPos_inr_inl] at hx
      omega
    · simp only [fullPos_inr_inr] at hx
      omega

@[expose] def predCut (I : Finset ℕ) (b : ℕ) : ℕ :=
  (I.filter (· < b)).sup id

theorem predCut_lt {I : Finset ℕ} {b : ℕ} (hb : 1 ≤ b) : predCut I b < b := by
  rw [predCut, Finset.sup_lt_iff (by rw [Nat.bot_eq_zero]; omega)]
  intro c hc
  exact (Finset.mem_filter.mp hc).2

theorem le_predCut {I : Finset ℕ} {b c : ℕ} (hc : c ∈ I) (hcb : c < b) : c ≤ predCut I b :=
  Finset.le_sup (f := id) (Finset.mem_filter.mpr ⟨hc, hcb⟩)

theorem predCut_eq_zero_or_mem (I : Finset ℕ) (b : ℕ) : predCut I b = 0 ∨ predCut I b ∈ I := by
  rcases (I.filter (· < b)).eq_empty_or_nonempty with he | hne
  · left
    rw [predCut, he, Finset.sup_empty]
    rfl
  · right
    obtain ⟨c, hc, hce⟩ := Finset.exists_mem_eq_sup _ hne id
    rw [predCut, hce]
    exact (Finset.mem_filter.mp hc).1

theorem isHypCut_predCut (h : UnitaryFieldData p f K) (hε : ε ≤ 1) {I : Finset ℕ} {b : ℕ}
    (hb : 1 ≤ b) (hbr : b ≤ r) : IsHypCut (flagStabilizer h r ε ↑I) (predCut I b) := by
  rcases predCut_eq_zero_or_mem I b with h0 | hmem
  · rw [h0]
    exact isHypCut_zero _
  · exact isHypCut_flagStabilizer h hε (Finset.mem_coe.mpr hmem)
      ((predCut_lt hb).le.trans hbr)

@[expose] noncomputable def eBlockHom (h : UnitaryFieldData p f K) (hε : ε ≤ 1) {I : Finset ℕ}
    {b : ℕ} (hb : b ∈ I) (hb1 : 1 ≤ b) (hbr : b ≤ r) :
    ↥(flagStabilizer h r ε ↑I) →* GL (Fin (b - predCut I b)) K :=
  hypBlockHom (eIdx_injective hbr) (mem_range_eIdx hbr) (isHypCut_predCut h hε hb1 hbr)
    (isHypCut_flagStabilizer h hε (Finset.mem_coe.mpr hb) hbr)

theorem coe_eBlockHom (h : UnitaryFieldData p f K) (hε : ε ≤ 1) {I : Finset ℕ} {b : ℕ}
    (hb : b ∈ I) (hb1 : 1 ≤ b) (hbr : b ≤ r) (g : ↥(flagStabilizer h r ε ↑I)) :
    ((eBlockHom h hε hb hb1 hbr g : GL (Fin (b - predCut I b)) K) :
      Matrix (Fin (b - predCut I b)) (Fin (b - predCut I b)) K) =
      (((g : hypSU h r ε) : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K).submatrix (eIdx r ε hbr) (eIdx r ε hbr) :=
  rfl

variable {s : ℕ}

@[expose] def resIdx (t : ℕ) : HypIndex s ε → HypIndex (t + s) ε
  | .inl i => .inl (Fin.natAdd t i)
  | .inr (.inl l) => .inr (.inl l)
  | .inr (.inr i) => .inr (.inr (Fin.natAdd t i))

theorem resIdx_injective (t : ℕ) : Function.Injective (resIdx (s := s) (ε := ε) t) := by
  intro x y hxy
  rcases x with ⟨i, hi⟩ | ⟨l, hl⟩ | ⟨i, hi⟩ <;> rcases y with ⟨j, hj⟩ | ⟨m, hm⟩ | ⟨j, hj⟩ <;>
    simp_all [resIdx, Fin.ext_iff]

theorem fullPos_resIdx (t : ℕ) (x : HypIndex s ε) : fullPos (resIdx t x) = t + fullPos x := by
  rcases x with ⟨i, hi⟩ | ⟨l, hl⟩ | ⟨i, hi⟩ <;> simp [resIdx] <;> omega

theorem hypPartner_resIdx (t : ℕ) (x : HypIndex s ε) :
    hypPartner (resIdx t x) = resIdx t (hypPartner x) := by
  rcases x with i | l | i <;> rfl

theorem mem_range_resIdx (t : ℕ) (x : HypIndex (t + s) ε) :
    x ∈ Set.range (resIdx (s := s) (ε := ε) t) ↔
      t ≤ fullPos x ∧ fullPos x < 2 * (t + s) + ε - t := by
  constructor
  · rintro ⟨y, rfl⟩
    rw [fullPos_resIdx]
    have := fullPos_lt y
    omega
  · intro hx
    rcases x with ⟨i, hi⟩ | ⟨l, hl⟩ | ⟨i, hi⟩
    · simp only [fullPos_inl] at hx
      refine ⟨.inl ⟨i - t, by omega⟩, ?_⟩
      simp only [resIdx, Sum.inl.injEq, Fin.ext_iff, Fin.natAdd_mk]
      omega
    · exact ⟨.inr (.inl ⟨l, hl⟩), rfl⟩
    · simp only [fullPos_inr_inr] at hx
      refine ⟨.inr (.inr ⟨i - t, by omega⟩), ?_⟩
      simp only [resIdx, Sum.inr.injEq, Fin.ext_iff, Fin.natAdd_mk]
      omega

theorem hypGram_resIdx (t : ℕ) (x y : HypIndex s ε) :
    hypGram (t + s) ε K (resIdx t x) (resIdx t y) = hypGram s ε K x y := by
  simp only [hypGram_apply, hypPartner_resIdx, (resIdx_injective t).eq_iff]

@[expose] noncomputable def resBlockHom (h : UnitaryFieldData p f K) (hε : ε ≤ 1) {I : Set ℕ}
    {t : ℕ} (ht : t ∈ I) : ↥(flagStabilizer h (t + s) ε I) →* GL (HypIndex s ε) K :=
  hypBlockHom (resIdx_injective t) (mem_range_resIdx t)
    (isHypCut_flagStabilizer h hε ht (Nat.le_add_right t s))
    (isHypCut_flagStabilizer_orth h hε ht (Nat.le_add_right t s))

theorem coe_resBlockHom (h : UnitaryFieldData p f K) (hε : ε ≤ 1) {I : Set ℕ} {t : ℕ}
    (ht : t ∈ I) (g : ↥(flagStabilizer h (t + s) ε I)) :
    ((resBlockHom h hε ht g : GL (HypIndex s ε) K) : Matrix (HypIndex s ε) (HypIndex s ε) K) =
      (((g : hypSU h (t + s) ε) : GL (HypIndex (t + s) ε) K) :
        Matrix (HypIndex (t + s) ε) (HypIndex (t + s) ε) K).submatrix (resIdx t) (resIdx t) :=
  rfl

theorem resBlock_gram (h : UnitaryFieldData p f K) (hε : ε ≤ 1) {I : Set ℕ} {t : ℕ} (ht : t ∈ I)
    (g : ↥(flagStabilizer h (t + s) ε I)) :
    let R := ((resBlockHom h hε ht g : GL (HypIndex s ε) K) :
      Matrix (HypIndex s ε) (HypIndex s ε) K)
    (R.map h.bar)ᵀ * hypGram s ε K * R = hypGram s ε K := by
  intro R
  set G := (((g : hypSU h (t + s) ε) : GL (HypIndex (t + s) ε) K) :
    Matrix (HypIndex (t + s) ε) (HypIndex (t + s) ε) K) with hG
  have hR : R = G.submatrix (resIdx t) (resIdx t) := rfl
  have hcut := isHypCut_flagStabilizer_orth h hε ht (Nat.le_add_right t s) g g.2
  have hgram := ((g : hypSU h (t + s) ε)).2.1
  ext a b
  have e1 := congrFun (congrFun hgram (resIdx t a)) (resIdx t b)
  rw [conjTranspose_hypGram_mul_apply, hypGram_resIdx] at e1
  rw [conjTranspose_hypGram_mul_apply, ← e1]
  refine Fintype.sum_of_injective (resIdx t) (resIdx_injective t) _ _ (fun y hy => ?_)
    fun x => by rw [hR, submatrix_apply, submatrix_apply, hypPartner_resIdx]
  rw [mem_range_resIdx, not_and_or, not_le, not_lt] at hy
  have ha := (mem_range_resIdx t (resIdx t a)).mp ⟨a, rfl⟩
  have hb := (mem_range_resIdx t (resIdx t b)).mp ⟨b, rfl⟩
  rcases hy with hy | hy
  · rw [hcut (hypPartner y) (resIdx t b) hb.2 (by rw [fullPos_hypPartner hε]; omega), mul_zero]
  · rw [hcut y (resIdx t a) ha.2 hy, map_zero, zero_mul]

end CFSG.AGLEmbedding.LeviBlock
