module

public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockUniCuts
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusTwistedALevi

public section

namespace CFSG.AGLEmbedding.LeviBlock

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open scoped Pointwise

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ}

@[expose] def finIdx {a b : ℕ} (hbr : b ≤ r) (k : Fin (b - a)) : Fin r :=
  ⟨a + k, by have := k.isLt; omega⟩

theorem finIdx_injective {a b : ℕ} (hbr : b ≤ r) : Function.Injective (finIdx (a := a) hbr) := by
  intro k k' hk
  simp only [finIdx, Fin.mk.injEq, Nat.add_left_cancel_iff] at hk
  exact Fin.ext hk

theorem mem_range_finIdx {a b : ℕ} (hbr : b ≤ r) (i : Fin r) :
    i ∈ Set.range (finIdx (a := a) hbr) ↔ a ≤ i ∧ (i : ℕ) < b := by
  constructor
  · rintro ⟨k, rfl⟩
    have := k.isLt
    simp only [finIdx]
    omega
  · intro hi
    exact ⟨⟨i - a, by omega⟩, Fin.ext (by simp only [finIdx]; omega)⟩

theorem eIdx_eq_inl_finIdx {a b : ℕ} (hbr : b ≤ r) (k : Fin (b - a)) :
    eIdx r ε hbr k = Sum.inl (finIdx hbr k) :=
  rfl

theorem barInvT_extendMat (h : UnitaryFieldData p f K) {m : ℕ} {φ : Fin m → Fin r}
    (hφ : Function.Injective φ) {A : Matrix (Fin m) (Fin m) K} (hA : IsUnit A.det) :
    barInvT h (extendMat hφ A) = extendMat hφ (barInvT h A) := by
  rw [barInvT, barInvT, extendMat_map hφ h.bar,
    extendMat_inv hφ (isUnit_det_map (h := h) hA), extendMat_transpose]

theorem leviMatTwistedA_one (h : UnitaryFieldData p f K) :
    ToralCensus.leviMatTwistedA (ε := ε) h (1 : Matrix (Fin r) (Fin r) K) = 1 := by
  simp [ToralCensus.leviMatTwistedA, barInvT, blk3]

@[expose] noncomputable def leviEHom (h : UnitaryFieldData p f K) (ε : ℕ) {a b : ℕ}
    (hbr : b ≤ r) : Matrix.SpecialLinearGroup (Fin (b - a)) K →* hypSU h r ε where
  toFun A := mkHypSU h (ToralCensus.leviMatTwistedA h
      (extendMat (finIdx_injective (a := a) hbr) (A : Matrix (Fin (b - a)) (Fin (b - a)) K)))
    (ToralCensus.leviMatTwistedA_gram h (by rw [det_extendMat, A.2]; exact isUnit_one))
    (ToralCensus.det_leviMatTwistedA h (by rw [det_extendMat, A.2]))
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    rw [coe_mkHypSU, Matrix.SpecialLinearGroup.coe_one, extendMat_one, leviMatTwistedA_one]
    rfl
  map_mul' A B := by
    apply Subtype.ext
    apply Units.ext
    rw [coe_mkHypSU, Subgroup.coe_mul, Units.val_mul, coe_mkHypSU, coe_mkHypSU,
      Matrix.SpecialLinearGroup.coe_mul, extendMat_mul, ToralCensus.leviMatTwistedA_mul]

theorem coe_leviEHom (h : UnitaryFieldData p f K) {a b : ℕ} (hbr : b ≤ r)
    (A : Matrix.SpecialLinearGroup (Fin (b - a)) K) :
    (((leviEHom h ε hbr A : hypSU h r ε) : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K) =
      ToralCensus.leviMatTwistedA h
        (extendMat (finIdx_injective (a := a) hbr) (A : Matrix (Fin (b - a)) (Fin (b - a)) K)) :=
  rfl

theorem leviEMat_apply_eq_zero (h : UnitaryFieldData p f K) {a b c : ℕ} (hbr : b ≤ r)
    (hcr : c ≤ r) (hc : c ≤ a ∨ b ≤ c) (A : Matrix (Fin (b - a)) (Fin (b - a)) K)
    {u w : HypIndex r ε} (hw : fullPos w < c) (hu : c ≤ fullPos u) :
    ToralCensus.leviMatTwistedA (ε := ε) h (extendMat (finIdx_injective hbr) A) u w = 0 := by
  rcases w with ⟨j, hj⟩ | ⟨l, hl⟩ | ⟨j, hj⟩
  · simp only [fullPos_inl] at hw
    rcases u with ⟨i, hi⟩ | ⟨l, hl⟩ | ⟨i, hi⟩
    · simp only [fullPos_inl] at hu
      rw [ToralCensus.leviMatTwistedA, blk3_inl_inl, extendMat_apply_of_not_mem]
      · exact one_apply_ne (fun he => by simp only [Fin.mk.injEq] at he; omega)
      · rcases hc with hc | hc
        · exact Or.inr fun hm => by rw [mem_range_finIdx] at hm; simp at hm; omega
        · exact Or.inl fun hm => by rw [mem_range_finIdx] at hm; simp at hm; omega
    · rw [ToralCensus.leviMatTwistedA, blk3_inr_inl_inl]
    · rw [ToralCensus.leviMatTwistedA, blk3_inr_inr_inl]
  · simp only [fullPos_inr_inl] at hw
    omega
  · simp only [fullPos_inr_inr] at hw
    omega

theorem leviEHom_mem_flagStabilizer (h : UnitaryFieldData p f K) (hε : ε ≤ 1) {a b : ℕ}
    (hbr : b ≤ r) {I : Set ℕ} (hIr : ∀ c ∈ I, c ≤ r) (hI : ∀ c ∈ I, c ≤ a ∨ b ≤ c)
    (A : Matrix.SpecialLinearGroup (Fin (b - a)) K) :
    leviEHom h ε hbr A ∈ flagStabilizer h r ε I := by
  refine mem_flagStabilizer.mpr fun c hc => smul_hypFlag_eq_of_apply_eq_zero h hε (hIr c hc)
    (fun u w hw hu => leviEMat_apply_eq_zero h hbr (hIr c hc) (hI c hc) _ hw hu)
    fun u w hw hu => ?_
  have : ((leviEHom h ε hbr A : hypSU h r ε) : GL (HypIndex r ε) K)⁻¹ =
      ((leviEHom h ε hbr A⁻¹ : hypSU h r ε) : GL (HypIndex r ε) K) := by
    rw [map_inv, Subgroup.coe_inv]
  rw [this, coe_leviEHom]
  exact leviEMat_apply_eq_zero h hbr (hIr c hc) (hI c hc) _ hw hu

variable {s : ℕ}

theorem hypPartner_not_mem_range_resIdx (hε : ε ≤ 1) (t : ℕ) {x : HypIndex (t + s) ε}
    (hx : x ∉ Set.range (resIdx (s := s) t)) : hypPartner x ∉ Set.range (resIdx (s := s) t) := by
  rw [mem_range_resIdx] at hx ⊢
  rw [fullPos_hypPartner hε]
  have := fullPos_lt x
  omega

theorem extendMat_resIdx_gram (h : UnitaryFieldData p f K) (hε : ε ≤ 1) (t : ℕ)
    {B : Matrix (HypIndex s ε) (HypIndex s ε) K}
    (hB : (B.map h.bar)ᵀ * hypGram s ε K * B = hypGram s ε K) :
    ((extendMat (resIdx_injective t) B).map h.bar)ᵀ * hypGram (t + s) ε K *
      extendMat (resIdx_injective t) B = hypGram (t + s) ε K := by
  set M := extendMat (resIdx_injective (s := s) (ε := ε) t) B with hM
  have hoff : ∀ x y, x ∉ Set.range (resIdx (s := s) (ε := ε) t) ∨
      y ∉ Set.range (resIdx (s := s) (ε := ε) t) → M x y = (1 : Matrix _ _ K) x y :=
    fun x y hxy => extendMat_apply_of_not_mem _ B hxy
  ext x y
  rw [conjTranspose_hypGram_mul_apply]
  by_cases hx : x ∈ Set.range (resIdx (s := s) (ε := ε) t)
  · by_cases hy : y ∈ Set.range (resIdx (s := s) (ε := ε) t)
    · obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      have e1 := congrFun (congrFun hB a) b
      rw [conjTranspose_hypGram_mul_apply] at e1
      rw [hypGram_resIdx, ← e1]
      symm
      refine Fintype.sum_of_injective (resIdx t) (resIdx_injective t) _ _ (fun w hw => ?_)
        fun c => by rw [hM, hypPartner_resIdx, extendMat_apply_map, extendMat_apply_map]
      rw [hoff w _ (Or.inl hw), one_apply_ne fun he => hw ⟨a, he.symm⟩, map_zero, zero_mul]
    · rw [Finset.sum_eq_single (hypPartner y)]
      · rw [hypPartner_hypPartner, hoff _ _ (Or.inr hy), one_apply_eq, mul_one,
          hoff _ _ (Or.inl (hypPartner_not_mem_range_resIdx hε t hy)), hypGram_apply]
        by_cases he : y = hypPartner x
        · rw [he, hypPartner_hypPartner, one_apply_eq, map_one, ite_eq_left rfl]
        · rw [one_apply_ne fun h' => he (by rw [← h', hypPartner_hypPartner]), map_zero,
            ite_eq_right he]
      · intro w _ hw
        rw [hoff _ _ (Or.inr hy), one_apply_ne fun h' => hw (by rw [← h',
          hypPartner_hypPartner]), mul_zero]
      · simp
  · rw [Finset.sum_eq_single x]
    · rw [hoff _ _ (Or.inl hx), one_apply_eq, map_one, one_mul,
        hoff _ _ (Or.inl (hypPartner_not_mem_range_resIdx hε t hx)), hypGram_apply]
      by_cases he : y = hypPartner x
      · rw [he, one_apply_eq, ite_eq_left rfl]
      · rw [one_apply_ne fun h' => he h'.symm, ite_eq_right he]
    · intro w _ hw
      rw [hoff w x (Or.inr hx), one_apply_ne hw, map_zero, zero_mul]
    · simp

@[expose] noncomputable def leviResHom (h : UnitaryFieldData p f K) (hε : ε ≤ 1) (t : ℕ) :
    hypSU h s ε →* hypSU h (t + s) ε where
  toFun B := mkHypSU h (extendMat (resIdx_injective t)
      ((B : GL (HypIndex s ε) K) : Matrix (HypIndex s ε) (HypIndex s ε) K))
    (extendMat_resIdx_gram h hε t (mem_hypSU.mp B.2).1)
    (by rw [det_extendMat]; exact (mem_hypSU.mp B.2).2)
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    rw [coe_mkHypSU, OneMemClass.coe_one, Units.val_one, extendMat_one]
    rfl
  map_mul' B B' := by
    apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul, coe_mkHypSU]
    exact extendMat_mul _ _ _

theorem coe_leviResHom (h : UnitaryFieldData p f K) (hε : ε ≤ 1) (t : ℕ) (B : hypSU h s ε) :
    (((leviResHom h hε t B : hypSU h (t + s) ε) : GL (HypIndex (t + s) ε) K) :
      Matrix (HypIndex (t + s) ε) (HypIndex (t + s) ε) K) =
      extendMat (resIdx_injective t)
        ((B : GL (HypIndex s ε) K) : Matrix (HypIndex s ε) (HypIndex s ε) K) :=
  rfl

theorem extendMat_resIdx_apply_eq_zero (t : ℕ) (B : Matrix (HypIndex s ε) (HypIndex s ε) K)
    {c : ℕ} (hct : c ≤ t) {u w : HypIndex (t + s) ε} (hw : fullPos w < c)
    (hu : c ≤ fullPos u) : extendMat (resIdx_injective t) B u w = 0 := by
  rw [extendMat_apply_of_not_mem _ B (Or.inr fun hm => by rw [mem_range_resIdx] at hm; omega),
    one_apply_ne fun he => by rw [he] at hu; omega]

theorem leviResHom_mem_flagStabilizer (h : UnitaryFieldData p f K) (hε : ε ≤ 1) (t : ℕ)
    {I : Set ℕ} (hI : ∀ c ∈ I, c ≤ t) (B : hypSU h s ε) :
    leviResHom h hε t B ∈ flagStabilizer h (t + s) ε I := by
  refine mem_flagStabilizer.mpr fun c hc => smul_hypFlag_eq_of_apply_eq_zero h hε
    ((hI c hc).trans (Nat.le_add_right t s))
    (fun u w hw hu => extendMat_resIdx_apply_eq_zero t _ (hI c hc) hw hu) fun u w hw hu => ?_
  have : ((leviResHom h hε t B : hypSU h (t + s) ε) : GL (HypIndex (t + s) ε) K)⁻¹ =
      ((leviResHom h hε t B⁻¹ : hypSU h (t + s) ε) : GL (HypIndex (t + s) ε) K) := by
    rw [map_inv, Subgroup.coe_inv]
  rw [this, coe_leviResHom]
  exact extendMat_resIdx_apply_eq_zero t _ (hI c hc) hw hu

end CFSG.AGLEmbedding.LeviBlock
