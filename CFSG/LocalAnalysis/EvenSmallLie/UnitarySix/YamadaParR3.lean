module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParModel
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParFormsCheck

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaPar

open Matrix

theorem aM_conj (j i : ℕ) (hj : j < 2) (hi : i < 4) :
    n0M j * aM i * n1M j = ∑ l : Fin 4, cM j l i • aM l := by
  have h := aConjCheck_eq_true
  simp only [aConjCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  have := congrArg (toMat 8 8) (h.1 j hj i hi)
  rw [toMat_bmul, toMat_bmul, toMat_msum, msumM, Finset.sum_range] at this
  exact this

theorem tM_n0M (j : ℕ) (hj : j < 2) : tM * n0M j = n0M j * tM := (embedCheck_spec.2.2.2 j hj).1

theorem tM_n1M (j : ℕ) (hj : j < 2) : tM * n1M j = n1M j * tM := (embedCheck_spec.2.2.2 j hj).2

@[expose] def candM (z i : ℕ) : Mat8 := toMat 8 8 (candBits z i)

@[expose] def candBlock (z : ℕ) (c : Fin 8) : Mat8 :=
  if (c : ℕ) < 4 then aM c else candM z ((c : ℕ) - 4)

theorem blocksOf_candCols (z : ℕ) (c : Fin 8) :
    blocksOf 1 (toVec (1 * 64) ((candCols z).getD c 0)) 0 = candBlock z c := by
  rw [candCols, getD_ofFn, blocksOf_packBlks]
  simp only [candBlock]
  split_ifs <;> rfl

theorem candBlock_indep (z : ℕ) (hz : z < 8) (e : Fin 8 → ZMod 2)
    (he : ∑ c, e c • candBlock z c = 0) : e = 0 := by
  have h := indepCheck_eq_true
  simp only [indepCheck, List.all_eq_true, List.mem_range] at h
  have hR : toMat 64 8 (btr 8 64 (candCols z)) *ᵥ e = 0 := by
    rw [toMat_btr, toMat_transpose_mulVec]
    apply (blocksEquiv 1).injective
    rw [map_zero, blocksEquiv_apply, blocksOf_sum]
    ext1 s
    have hs : s = 0 := Subsingleton.elim _ _
    subst hs
    rw [Finset.sum_apply, Pi.zero_apply]
    refine Eq.trans (Finset.sum_congr rfl fun c _ => ?_) he
    rw [← blocksOf_candCols z c]
    ext a b
    rfl
  exact eq_zero_of_injCheck (h z hz) hR

theorem mat8_add_self (x : Mat8) : x + x = 0 := by
  ext a b
  simp only [Matrix.add_apply, Matrix.zero_apply]
  generalize x a b = c
  revert c; decide

theorem zmod2_eq_of_add_eq_zero {a b : ZMod 2} (h : a + b = 0) : a = b := by
  revert a b; decide

theorem mat8_add_self16 (x : Mat16) : x + x = 0 := by
  ext a b
  simp only [Matrix.add_apply, Matrix.zero_apply]
  generalize x a b = c
  revert c; decide

theorem mat8_sub_eq_add (x y : Mat8) : x - y = x + y := by
  ext a b
  simp only [Matrix.sub_apply, Matrix.add_apply]
  generalize x a b = c
  generalize y a b = d
  revert c d; decide

theorem mat8_eq_of_add_eq_zero {x y : Mat8} (h : x + y = 0) : x = y := by
  ext a b
  exact zmod2_eq_of_add_eq_zero (by simpa using congrFun (congrFun h a) b)

theorem card_span_of_indep {n : ℕ} (v : Fin n → Mat8)
    (hv : ∀ e : Fin n → ZMod 2, ∑ c, e c • v c = 0 → e = 0) :
    Nat.card (Submodule.span (ZMod 2) (Set.range v)) = 2 ^ n := by
  rw [← Fintype.range_linearCombination]
  have hinj : Function.Injective (Fintype.linearCombination (ZMod 2) v) := by
    intro e₁ e₂ h
    rw [Fintype.linearCombination_apply, Fintype.linearCombination_apply] at h
    have h2 := hv (e₁ + e₂) (by
      simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, h]
      exact mat8_add_self _)
    ext c
    have := congrFun h2 c
    simp only [Pi.add_apply, Pi.zero_apply] at this
    exact zmod2_eq_of_add_eq_zero this
  rw [LinearMap.range_eq_map, Nat.card_congr ((Submodule.equivMapOfInjective _ hinj ⊤).symm.trans
    Submodule.topEquiv).toEquiv]
  simp [Nat.card_eq_fintype_card, ZMod.card]

@[expose] def psiZ (z : ℕ) : Submodule (ZMod 2) Mat8 :=
  Submodule.span (ZMod 2) (Set.range (candBlock z))

theorem card_psiZ (z : ℕ) (hz : z < 8) : Nat.card (psiZ z) = 2 ^ 8 :=
  card_span_of_indep _ (candBlock_indep z hz)

theorem aSpan_le_psiZ (z : ℕ) : aSpan ≤ psiZ z := by
  rw [aSpan, psiZ, Submodule.span_le]
  rintro _ ⟨m, rfl⟩
  exact Submodule.subset_span ⟨⟨m, by omega⟩, by simp [candBlock]⟩

theorem candM_mem_psiZ (z : ℕ) (i : Fin 4) : candM z i ∈ psiZ z :=
  Submodule.subset_span ⟨⟨(i : ℕ) + 4, by omega⟩, by simp [candBlock]⟩

theorem sum_smul_mem {Ψ : Set Mat8} (h0 : (0 : Mat8) ∈ Ψ)
    (hadd : ∀ x ∈ Ψ, ∀ y ∈ Ψ, x + y ∈ Ψ) {ι : Type} (s : Finset ι) (c : ι → ZMod 2)
    (v : ι → Mat8) (hv : ∀ i ∈ s, v i ∈ Ψ) : ∑ i ∈ s, c i • v i ∈ Ψ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h0
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    refine hadd _ ?_ _ (ih fun i hi => hv i (Finset.mem_insert_of_mem hi))
    have hva := hv a (Finset.mem_insert_self a s)
    rcases (show ∀ e : ZMod 2, e = 0 ∨ e = 1 by decide) (c a) with h | h
    · rw [h, zero_smul]; exact h0
    · rw [h, one_smul]; exact hva

theorem bitsOf_lt (n : ℕ) (f : ℕ → Bool) : bitsOf n f < 2 ^ n := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [testBit_bitsOf]
  simp [Nat.not_lt.mpr hi]

@[expose] def zIndex (z : Fin 3 → ZMod 2) : ℕ :=
  bitsOf 3 fun q => if h : q < 3 then z ⟨q, h⟩ == 1 else false

theorem zIndex_lt (z : Fin 3 → ZMod 2) : zIndex z < 8 := bitsOf_lt 3 _

theorem candM_zIndex (z : Fin 3 → ZMod 2) (i : ℕ) :
    candM (zIndex z) i = y0M i + ∑ q : Fin 3, z q • dirM q i := by
  rw [candM, candBits, toMat_bxor, toMat_msum, msumM, Finset.sum_range]
  congr 1
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [zIndex, testBit_bitsOf]
  simp only [q.isLt, decide_true, Bool.true_and, dite_true, Fin.eta, bz_beq_one]
  rfl

theorem aSpan_subset {Ψ : Set Mat8} (h0 : (0 : Mat8) ∈ Ψ)
    (hadd : ∀ x ∈ Ψ, ∀ y ∈ Ψ, x + y ∈ Ψ) (ha : ∀ m : Fin 4, aM m ∈ Ψ) :
    (aSpan : Set Mat8) ⊆ Ψ := by
  intro x hx
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).mp hx
  exact sum_smul_mem h0 hadd _ c _ fun m _ => ha m

theorem psiZ_subset {Ψ : Set Mat8} (h0 : (0 : Mat8) ∈ Ψ)
    (hadd : ∀ x ∈ Ψ, ∀ y ∈ Ψ, x + y ∈ Ψ) {z : ℕ} (hb : ∀ c : Fin 8, candBlock z c ∈ Ψ) :
    (psiZ z : Set Mat8) ⊆ Ψ := by
  intro x hx
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).mp hx
  exact sum_smul_mem h0 hadd _ c _ fun m _ => hb m

theorem delta_conj_step {t n0 n1 : Mat8} {φ a : Fin 4 → Mat8} {c : Fin 4 → ZMod 2}
    (ht0 : t * n0 = n0 * t) (ht1 : t * n1 = n1 * t) (hφ : ∀ l, t * φ l * t + φ l = a l)
    (i : Fin 4) :
    t * (n0 * φ i * n1 + ∑ l, c l • φ l) * t + (n0 * φ i * n1 + ∑ l, c l • φ l) =
      n0 * a i * n1 + ∑ l, c l • a l := by
  have hφ' : ∀ l, t * φ l * t = a l + φ l := fun l => by
    rw [← hφ l, add_assoc, mat8_add_self, add_zero]
  have e1 : t * (n0 * φ i * n1) * t = n0 * (t * φ i * t) * n1 := by
    rw [show t * (n0 * φ i * n1) * t = (t * n0) * φ i * (n1 * t) by noncomm_ring, ht0,
      ← ht1]
    noncomm_ring
  have e2 : t * (∑ l, c l • φ l) * t = ∑ l, c l • (t * φ l * t) := by
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [mul_smul_comm, smul_mul_assoc]
  rw [mul_add, add_mul, e1, e2, hφ' i]
  simp only [hφ', smul_add, Finset.sum_add_distrib, mul_add, add_mul]
  rw [show ∀ p p' q q' : Mat8, p' + p + (q' + q) + (p + q) = p' + q' + (p + p) + (q + q) by
    intro p p' q q'; abel, mat8_add_self, mat8_add_self, add_zero, add_zero]

theorem exists_eq_psiZ {Ψ : Set Mat8} (h0 : (0 : Mat8) ∈ Ψ)
    (hadd : ∀ x ∈ Ψ, ∀ y ∈ Ψ, x + y ∈ Ψ) (hcard : Nat.card Ψ ≤ 2 ^ 8)
    (ha : ∀ m : Fin 4, aM m ∈ Ψ) (hν : ∀ j < 2, ∀ ψ ∈ Ψ, n0M j * ψ * n1M j ∈ Ψ)
    (hfix : ∀ ψ ∈ Ψ, tM * ψ * tM = ψ → ψ ∈ aSpan)
    (hsurj : ∀ m : Fin 4, ∃ ψ ∈ Ψ, tM * ψ * tM + ψ = aM m) :
    ∃ z < 8, Ψ = (psiZ z : Set Mat8) := by
  choose φ hφΨ hφ using hsurj
  have hX : ∀ (j : Fin 2) (i : Fin 4), ∃ lam : Fin 4 → ZMod 2,
      n0M j * φ i * n1M j + ∑ l : Fin 4, cM j l i • φ l + ∑ m : Fin 4, lam m • aM m = 0 := by
    intro j i
    obtain ⟨X, hXdef⟩ : ∃ X, X = n0M j * φ i * n1M j + ∑ l : Fin 4, cM j l i • φ l := ⟨_, rfl⟩
    have hXΨ : X ∈ Ψ := hXdef ▸ hadd _ (hν j j.isLt _ (hφΨ i)) _
      (sum_smul_mem h0 hadd _ _ _ fun l _ => hφΨ l)
    have hδX : tM * X * tM + X = 0 := by
      rw [hXdef, delta_conj_step (tM_n0M j j.isLt) (tM_n1M j j.isLt) hφ i,
        aM_conj j i j.isLt i.isLt]
      exact mat8_add_self _
    have hXa : X ∈ aSpan := hfix X hXΨ (mat8_eq_of_add_eq_zero hδX)
    obtain ⟨lam, hlam⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).mp hXa
    exact ⟨lam, by rw [← hXdef, hlam]; exact mat8_add_self _⟩
  choose lam hlam using hX
  obtain ⟨z, hz⟩ := exists_candidate φ lam (fun i => hφ i) hlam
  refine ⟨zIndex z, zIndex_lt z, ?_⟩
  have hsub := aSpan_subset h0 hadd ha
  have hcand : ∀ c : Fin 8, candBlock (zIndex z) c ∈ Ψ := by
    intro c
    rw [candBlock]
    split_ifs with hc
    · exact ha ⟨c, hc⟩
    · have hi : (c : ℕ) - 4 < 4 := by omega
      have h1 := hz ⟨_, hi⟩
      rw [candM_zIndex]
      have h2 := hadd _ (hφΨ ⟨_, hi⟩) _ (hsub h1)
      rwa [mat8_sub_eq_add, ← add_assoc, mat8_add_self, zero_add] at h2
  have hle := psiZ_subset h0 hadd hcand
  refine (Set.eq_of_subset_of_ncard_le hle ?_ (Set.toFinite _)).symm
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
  exact hcard.trans (card_psiZ _ (zIndex_lt z)).ge

@[expose] def diagM (B : Mat16) : Mat16 := Matrix.of fun r c => if r = c then B r c else 0

theorem toMat_diag16 (B : Array ℕ) : toMat 16 16 (diag16 B) = diagM (toMat 16 16 B) := by
  ext r c
  rw [toMat_apply, diag16, getD_ofFn, Nat.testBit_and, Nat.testBit_two_pow, diagM, Matrix.of_apply,
    toMat_apply]
  by_cases h : r = c
  · subst h; simp
  · have : (r : ℕ) ≠ c := Fin.val_ne_of_ne h
    simp [h, this]

@[expose] def formGenM (z k : ℕ) : Mat16 := toMat 16 16 (formGen z k)

theorem formGenM_eq (z k : ℕ) :
    formGenM z k = if k = 0 then rhoM (genMat 0) else if k = 1 then rhoM (genMat 1) else
      1 + embedM (if k - 2 < 4 then aM (k - 2) else candM z (k - 2 - 4)) := by
  rw [formGenM, formGen]
  split_ifs with h0 h1 h2
  · rw [toMat_rho16]; rfl
  · rw [toMat_rho16]; rfl
  · rw [dGen, ite_eq_left h2, toMat_bxor, toMat_id16, toMat_embed16]; rfl
  · rw [dGen, ite_eq_right h2, toMat_bxor, toMat_id16, toMat_embed16]; rfl

@[expose] def formBlockM (z : ℕ) (B : Mat16) (k : ℕ) : Mat16 :=
  if k = 0 then B + Bᵀ else if k = 1 then diagM B
  else (formGenM z (k - 2))ᵀ * B * formGenM z (k - 2) + B

theorem toMat_formBlock (z : ℕ) (B : Array ℕ) (k : ℕ) :
    toMat 16 16 (formBlock z B k) = formBlockM z (toMat 16 16 B) k := by
  unfold formBlock formBlockM
  split_ifs
  · rw [toMat_bxor, toMat_btr]
  · rw [toMat_diag16]
  · rw [toMat_bxor, toMat_bmul, toMat_bmul, toMat_btr]; rfl

theorem formBlockM_add (z : ℕ) (B B' : Mat16) (k : ℕ) :
    formBlockM z (B + B') k = formBlockM z B k + formBlockM z B' k := by
  unfold formBlockM
  split_ifs
  · rw [transpose_add]; abel
  · ext r c; simp only [diagM, Matrix.of_apply, Matrix.add_apply]; split_ifs <;> simp
  · rw [mul_add, add_mul]; abel

theorem formBlockM_smul (z : ℕ) (a : ZMod 2) (B : Mat16) (k : ℕ) :
    formBlockM z (a • B) k = a • formBlockM z B k := by
  unfold formBlockM
  split_ifs
  · rw [transpose_smul, smul_add]
  · ext r c; simp only [diagM, Matrix.of_apply, Matrix.smul_apply]; split_ifs <;> simp
  · rw [mul_smul_comm, smul_mul_assoc, smul_add]

@[expose] def formLin (z : ℕ) : Mat16 →ₗ[ZMod 2] (Fin 12 → Mat16) where
  toFun B k := formBlockM z B k
  map_add' B B' := by ext1 k; exact formBlockM_add z B B' k
  map_smul' a B := by ext1 k; exact formBlockM_smul z a B k

@[expose] def formF (z : ℕ) :
    (Fin (1 * (16 * 16)) → ZMod 2) →ₗ[ZMod 2] (Fin (12 * (16 * 16)) → ZMod 2) :=
  (blocksEquivN 16 12).symm.toLinearMap ∘ₗ formLin z ∘ₗ
    (LinearMap.proj 0 ∘ₗ (blocksEquivN 16 1).toLinearMap)

theorem toVec_formFb (z v : ℕ) : toVec (12 * (16 * 16)) (formFb z v) =
    formF z (toVec (1 * (16 * 16)) v) := by
  rw [formFb, toVec_packN]
  simp only [formF, LinearMap.comp_apply, LinearEquiv.coe_coe, blocksEquivN_symm_apply,
    blocksEquivN_apply, LinearMap.proj_apply, formLin, LinearMap.coe_mk, AddHom.coe_mk]
  congr 1
  ext1 k
  rw [toMat_formBlock]
  exact congrArg (formBlockM z · k) (toMat_unpackN 16 1 v 0)

theorem lt_four_of_form {z : ℕ} (hz : z < 8) {B : Mat16} (hB : B ≠ 0) (hsymm : Bᵀ = B)
    (hdiag : ∀ r, B r r = 0)
    (hK0 : (rhoM (genMat 0))ᵀ * B * rhoM (genMat 0) = B)
    (hK1 : (rhoM (genMat 1))ᵀ * B * rhoM (genMat 1) = B)
    (hD : ∀ ψ ∈ psiZ z, (1 + embedM ψ)ᵀ * B * (1 + embedM ψ) = B) : z < 4 := by
  by_contra hz4
  have hcheck : formCheckW z = true := by
    have h := formsCheckW_eq_true
    simp only [formsCheckW, Bool.and_eq_true] at h
    interval_cases z
    · exact h.1.1.1
    · exact h.1.1.2
    · exact h.1.2
    · exact h.2
  have hR : toMat (12 * 256) 256 (linBits 256 (12 * 256) (formFb z)) *ᵥ
      vecOfN 16 1 (fun _ => B) = 0 := by
    rw [toMat_linBits_mulVec (formFb z) (formF z) (fun j => by rw [toVec_formFb, toVec_two_pow])]
    simp only [formF, LinearMap.comp_apply, LinearEquiv.coe_coe, blocksEquivN_symm_apply,
      blocksEquivN_apply, LinearMap.proj_apply, formLin, LinearMap.coe_mk, AddHom.coe_mk,
      blocksOfN_vecOfN]
    have : (fun k : Fin 12 => formBlockM z B k) = 0 := by
      ext1 k
      rw [Pi.zero_apply, formBlockM]
      split_ifs with h0 h1
      · rw [hsymm, mat8_add_self16]
      · ext r c; simp only [diagM, Matrix.of_apply, Matrix.zero_apply]; split_ifs with h
        · subst h; exact hdiag r
        · rfl
      · rw [formGenM_eq]
        split_ifs with h2 h3 h4
        · rw [hK0, mat8_add_self16]
        · rw [hK1, mat8_add_self16]
        · rw [hD _ (aSpan_le_psiZ z (aM_mem_aSpan ⟨_, h4⟩)), mat8_add_self16]
        · rw [hD _ (candM_mem_psiZ z ⟨(k : ℕ) - 2 - 2 - 4, by omega⟩), mat8_add_self16]
    rw [this]
    ext i
    simp [vecOfN]
  have := eq_zero_of_injCheckWith hcheck hR
  apply hB
  have h2 := congrArg (blocksOfN 16 1) this
  rw [blocksOfN_vecOfN] at h2
  have h3 := congrFun h2 0
  rw [h3]
  ext r c
  simp [blocksOfN]

end CFSG.EvenSmallLie.UnitarySix.YamadaPar
