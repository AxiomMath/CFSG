module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylD8Check
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylFrame

public noncomputable section

namespace CFSG.EvenSmallLie.OmegaEight.Weyl

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.RankThree.Native

structure DFacts : Prop where
  sFix : ∀ r < 240, r < 112 ∨ ∀ m < 256, framePop m % 2 = 0 → m ≠ 0 → (signArrs[m]!)[r]! ≠ r
  conj : ∀ p ∈ dPairs, ∀ m < 256, framePop m % 2 = 0 →
    eqA 240 (compA 240 (compA 240 reflArrs[4 * dPairs.idxOf p + 1]! signArrs[m]!)
      reflArrs[4 * dPairs.idxOf p + 1]!)
      signArrs[permMask (Equiv.swap (Fin.ofNat 8 p.1) (Fin.ofNat 8 p.2)) m]! = true
  idx : ∀ r < 240, rootIdx (rootVec r) = r
  len : rootList.length = 240
  vlen : ∀ r < 240, (rootVec r).length = 8
  perm : ∀ p ∈ dPairs, ∀ r < 240,
    rootIdx (permVecL (Equiv.swap (Fin.ofNat 8 p.1) (Fin.ofNat 8 p.2)) (rootVec r)) < 240
  permRefl : ∀ p ∈ dPairs, eqA 240 (permArr (Equiv.swap (Fin.ofNat 8 p.1) (Fin.ofNat 8 p.2)))
    reflArrs[4 * dPairs.idxOf p + 1]! = true

theorem d_facts : DFacts := by
  have h := d_check
  rw [dCheck, dCheckWith] at h
  obtain ⟨h, hG⟩ := Bool.and_eq_true_iff.1 h
  obtain ⟨h, hF⟩ := Bool.and_eq_true_iff.1 h
  obtain ⟨h, hE⟩ := Bool.and_eq_true_iff.1 h
  obtain ⟨h, hD⟩ := Bool.and_eq_true_iff.1 h
  obtain ⟨h, hC⟩ := Bool.and_eq_true_iff.1 h
  obtain ⟨hA, -⟩ := Bool.and_eq_true_iff.1 h
  rw [List.all_eq_true] at hA hC hG
  rw [allLt_iff] at hD hF
  refine ⟨fun r hr => ?_, fun p hp m hm he => ?_, fun r hr => ?_, ?_, fun r hr => ?_,
    fun p hp r hr => ?_, fun p hp => ?_⟩
  · have := hA r (List.mem_range.2 hr)
    rw [Bool.or_eq_true, decide_eq_true_eq, List.all_eq_true] at this
    refine this.imp id fun h' m hm he hm0 => ?_
    have := h' m (List.mem_range.2 hm)
    simpa [he, hm0] using this
  · have := hC p hp
    rw [List.all_eq_true] at this
    have := this 1 (by simp)
    rw [List.all_eq_true] at this
    have := this m (List.mem_range.2 hm)
    simpa [he] using this
  · simpa using hD r hr
  · simpa using hE
  · simpa using hF r hr
  · have := (Bool.and_eq_true_iff.1 (hG p hp)).1
    rw [allLt_iff] at this
    simpa using this r hr
  · exact (Bool.and_eq_true_iff.1 (hG p hp)).2

theorem permVecL_length (σ : Equiv.Perm (Fin 8)) (x : List ℤ) : (permVecL σ x).length = 8 := by
  simp [permVecL]

theorem permVecL_getD (σ : Equiv.Perm (Fin 8)) (x : List ℤ) {k : ℕ} (hk : k < 8) :
    (permVecL σ x).getD k 0 = x.getD (σ.symm ⟨k, hk⟩ : ℕ) 0 := by
  rw [List.getD_eq_getElem _ _ (by rw [permVecL_length]; exact hk)]
  simp [permVecL]

theorem list_ext_getD {x y : List ℤ} (hx : x.length = 8) (hy : y.length = 8)
    (h : ∀ k < 8, x.getD k 0 = y.getD k 0) : x = y := by
  refine List.ext_getElem (by rw [hx, hy]) fun k h1 h2 => ?_
  have := h k (by rw [← hx]; exact h1)
  rwa [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at this

theorem permVecL_permVecL (σ τ : Equiv.Perm (Fin 8)) {x : List ℤ} :
    permVecL σ (permVecL τ x) = permVecL (σ * τ) x := by
  refine list_ext_getD (permVecL_length _ _) (permVecL_length _ _) fun k hk => ?_
  rw [permVecL_getD _ _ hk, permVecL_getD _ _ (σ.symm ⟨k, hk⟩).2, permVecL_getD _ _ hk]
  rfl

theorem permVecL_one {x : List ℤ} (hx : x.length = 8) : permVecL 1 x = x :=
  list_ext_getD (permVecL_length _ _) hx fun k hk => by rw [permVecL_getD _ _ hk]; rfl

theorem rootVec_mem {r : ℕ} (hr : r < 240) : rootVec r ∈ rootList := by
  rw [rootVec, List.getD_eq_getElem _ _ (by rw [d_facts.len]; exact hr)]
  exact List.getElem_mem _

theorem rootIdx_lt {x : List ℤ} (hx : x ∈ rootList) : rootIdx x < 240 := by
  rw [← d_facts.len]
  exact List.idxOf_lt_length_of_mem hx

theorem rootVec_rootIdx {x : List ℤ} (hx : x ∈ rootList) : rootVec (rootIdx x) = x := by
  rw [rootVec, rootIdx, List.getD_eq_getElem _ _ (List.idxOf_lt_length_of_mem hx),
    List.getElem_idxOf]

theorem mem_of_rootIdx_lt {x : List ℤ} (h : rootIdx x < 240) : x ∈ rootList := by
  have h' : rootList.idxOf x < rootList.length := by rw [d_facts.len]; exact h
  rw [← List.getElem_idxOf h']
  exact List.getElem_mem _

theorem length_of_mem_rootList {x : List ℤ} (hx : x ∈ rootList) : x.length = 8 := by
  rw [← rootVec_rootIdx hx]
  exact d_facts.vlen _ (rootIdx_lt hx)

theorem mem_dPairs : ∀ {i j : Fin 8}, i < j → ((i : ℕ), (j : ℕ)) ∈ dPairs := by decide

theorem fin_ofNat_val (i : Fin 8) : Fin.ofNat 8 (i : ℕ) = i := by
  fin_cases i <;> rfl

theorem swap_perm_root (a b : Fin 8) {x : List ℤ} (hx : x ∈ rootList) :
    permVecL (Equiv.swap a b) x ∈ rootList := by
  have key : ∀ {i j : Fin 8}, i < j → permVecL (Equiv.swap i j) x ∈ rootList := by
    intro i j h
    have := d_facts.perm _ (mem_dPairs h) (rootIdx x) (rootIdx_lt hx)
    rw [fin_ofNat_val, fin_ofNat_val, rootVec_rootIdx hx] at this
    exact mem_of_rootIdx_lt this
  rcases lt_trichotomy a b with h | rfl | h
  · exact key h
  · rwa [Equiv.swap_self, Equiv.Perm.one_def.symm, permVecL_one (length_of_mem_rootList hx)]
  · rw [Equiv.swap_comm]
    exact key h

theorem permVecL_mem (σ : Equiv.Perm (Fin 8)) {x : List ℤ} (hx : x ∈ rootList) :
    permVecL σ x ∈ rootList := by
  revert x
  refine Equiv.Perm.swap_induction_on (motive := fun σ => ∀ {x : List ℤ}, x ∈ rootList →
    permVecL σ x ∈ rootList) σ (fun hx => ?_) (fun f a b _ ih x hx => ?_)
  · rwa [permVecL_one (length_of_mem_rootList hx)]
  · rw [← permVecL_permVecL]
    exact swap_perm_root a b (ih hx)

theorem permArr_get (σ : Equiv.Perm (Fin 8)) {i : ℕ} (hi : i < 240) :
    (permArr σ)[i]! = rootIdx (permVecL σ (rootVec i)) := by
  rw [permArr, getElem!_ofFn_nat _ hi]
  rfl

theorem rep_permArr (σ : Equiv.Perm (Fin 8)) : Rep 240 (permArr σ) (permMat σ) := by
  have hlt : ∀ i < 240, (permArr σ)[i]! < 240 := fun i hi => by
    rw [permArr_get σ hi]
    exact rootIdx_lt (permVecL_mem σ (rootVec_mem hi))
  have hinj : ∀ i < 240, ∀ j < 240, (permArr σ)[i]! = (permArr σ)[j]! → i = j := by
    intro i hi j hj h
    rw [permArr_get σ hi, permArr_get σ hj] at h
    have h2 := congrArg rootVec h
    rw [rootVec_rootIdx (permVecL_mem σ (rootVec_mem hi)),
      rootVec_rootIdx (permVecL_mem σ (rootVec_mem hj))] at h2
    have h3 := congrArg (permVecL σ⁻¹) h2
    rw [permVecL_permVecL, permVecL_permVecL, inv_mul_cancel,
      permVecL_one (d_facts.vlen i hi), permVecL_one (d_facts.vlen j hj)] at h3
    rw [← d_facts.idx i hi, ← d_facts.idx j hj, h3]
  intro x
  rw [permMat, permOfArr, dite_eq_left ⟨hlt, hinj⟩]
  rfl

theorem permMat_apply (σ : Equiv.Perm (Fin 8)) (r : Fin 240) :
    ((permMat σ r : Fin 240) : ℕ) = rootIdx (permVecL σ (rootVec r)) := by
  rw [← rep_permArr σ r, permArr_get σ r.2]

theorem permMat_mul (σ τ : Equiv.Perm (Fin 8)) : permMat (σ * τ) = permMat σ * permMat τ := by
  refine Equiv.ext fun r => Fin.ext ?_
  rw [Equiv.Perm.mul_apply, permMat_apply, permMat_apply, permMat_apply,
    rootVec_rootIdx (permVecL_mem τ (rootVec_mem r.2)), permVecL_permVecL]

theorem permMat_one : permMat 1 = 1 := by
  refine Equiv.ext fun r => Fin.ext ?_
  rw [permMat_apply, permVecL_one (d_facts.vlen r r.2), d_facts.idx r r.2]
  rfl

@[expose] def permMatHom : Equiv.Perm (Fin 8) →* Equiv.Perm (Fin 240) where
  toFun := permMat
  map_one' := permMat_one
  map_mul' := permMat_mul

theorem permMat_inv (σ : Equiv.Perm (Fin 8)) : (permMat σ)⁻¹ = permMat σ⁻¹ :=
  (map_inv permMatHom σ).symm

theorem dPairs_idxOf_lt {i j : Fin 8} (h : i < j) :
    4 * dPairs.idxOf ((i : ℕ), (j : ℕ)) + 1 < 240 := by
  have := List.idxOf_lt_length_of_mem (mem_dPairs h)
  have hl : dPairs.length = 28 := by decide
  omega

theorem permMat_swap_lt {i j : Fin 8} (h : i < j) :
    permMat (Equiv.swap i j) = refl (4 * dPairs.idxOf ((i : ℕ), (j : ℕ)) + 1) := by
  have he := d_facts.permRefl _ (mem_dPairs h)
  rw [fin_ofNat_val, fin_ofNat_val, reflArrs_get (dPairs_idxOf_lt h)] at he
  exact eq_of_eqA (rep_permArr _) (rep_refl (dPairs_idxOf_lt h)) he

theorem exists_permMat_swap (a b : Fin 8) (hab : a ≠ b) :
    ∃ r < 240, permMat (Equiv.swap a b) = refl r := by
  rcases lt_or_gt_of_ne hab with h | h
  · exact ⟨_, dPairs_idxOf_lt h, permMat_swap_lt h⟩
  · rw [Equiv.swap_comm]
    exact ⟨_, dPairs_idxOf_lt h, permMat_swap_lt h⟩

theorem permMat_mem_wE8 (σ : Equiv.Perm (Fin 8)) : permMat σ ∈ wE8 := by
  refine Equiv.Perm.swap_induction_on (motive := fun σ => permMat σ ∈ wE8) σ ?_
    (fun f a b hab ih => ?_)
  · rw [permMat_one]
    exact one_mem _
  · obtain ⟨r, hr, he⟩ := exists_permMat_swap a b hab
    rw [permMat_mul, he]
    exact mul_mem (refl_mem hr) ih

theorem sign_permMat (σ : Equiv.Perm (Fin 8)) :
    Equiv.Perm.sign (permMat σ) = Equiv.Perm.sign σ := by
  refine Equiv.Perm.swap_induction_on (motive := fun σ =>
    Equiv.Perm.sign (permMat σ) = Equiv.Perm.sign σ) σ ?_ (fun f a b hab ih => ?_)
  · rw [permMat_one, map_one, map_one]
  · obtain ⟨r, hr, he⟩ := exists_permMat_swap a b hab
    rw [permMat_mul, he, map_mul, map_mul, ih, sign_refl hr, Equiv.Perm.sign_swap hab]

theorem permMat_mem_wPlus_iff (σ : Equiv.Perm (Fin 8)) :
    permMat σ ∈ wPlus ↔ σ ∈ alternatingGroup (Fin 8) := by
  rw [mem_wPlus_iff, Equiv.Perm.mem_alternatingGroup, sign_permMat]
  exact and_iff_right (permMat_mem_wE8 σ)

theorem signArrs_permMask {v : FrameVec} (σ : Equiv.Perm (Fin 8)) :
    signArrs[permMask σ (frameEncode v)]! = signArr (permVec σ v) := by
  rw [permMask, frameDecode_frameEncode, signArrs_encode]

theorem permMat_swap_conj {i j : Fin 8} (h : i < j) {v : FrameVec} (hv : v ∈ evenSub) :
    permMat (Equiv.swap i j) * signPerm v * (permMat (Equiv.swap i j))⁻¹ =
      signPerm (permVec (Equiv.swap i j) v) := by
  have hlt := dPairs_idxOf_lt h
  have hc := d_facts.conj _ (mem_dPairs h) (frameEncode v) (frameEncode_lt v)
    (by simpa using framePop_even hv)
  rw [fin_ofNat_val, fin_ofNat_val, reflArrs_get hlt, signArrs_encode, signArrs_permMask] at hc
  rw [permMat_swap_lt h, refl_inv hlt]
  exact eq_of_eqA (rep_compA (rep_compA (rep_refl hlt) (rep_signArr hv)) (rep_refl hlt))
    (rep_signArr (permVec_mem_evenSub _ hv)) hc

theorem permMat_conj_signPerm (σ : Equiv.Perm (Fin 8)) {v : FrameVec} (hv : v ∈ evenSub) :
    permMat σ * signPerm v * (permMat σ)⁻¹ = signPerm (permVec σ v) := by
  revert v
  refine Equiv.Perm.swap_induction_on (motive := fun σ => ∀ {v : FrameVec}, v ∈ evenSub →
    permMat σ * signPerm v * (permMat σ)⁻¹ = signPerm (permVec σ v)) σ ?_
    (fun f a b hab ih v hv => ?_)
  · intro v _
    rw [permMat_one, one_mul, inv_one, mul_one, permVec_one]
  · have key : ∀ {i j : Fin 8}, i < j → permMat (Equiv.swap i j * f) * signPerm v *
        (permMat (Equiv.swap i j * f))⁻¹ = signPerm (permVec (Equiv.swap i j * f) v) := by
      intro i j h
      rw [permMat_mul, show permMat (Equiv.swap i j) * permMat f * signPerm v *
        (permMat (Equiv.swap i j) * permMat f)⁻¹ = permMat (Equiv.swap i j) *
        (permMat f * signPerm v * (permMat f)⁻¹) * (permMat (Equiv.swap i j))⁻¹ by group,
        ih hv, permMat_swap_conj h (permVec_mem_evenSub f hv), permVec_mul]
    rcases lt_or_gt_of_ne hab with h | h
    · exact key h
    · rw [Equiv.swap_comm]
      exact key h

end CFSG.EvenSmallLie.OmegaEight.Weyl
