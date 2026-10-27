module

public import CFSG.ClassicalInvolution.Models.LinearPairs.Frame
public import CFSG.ClassicalInvolution.Phan.Frames.Action

public section

namespace CFSG.ClassicalInvolution.Models

open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.ClassicalInvolution.Phan
  Module Matrix
open scoped MatrixGroups

variable {K : Type} [Field K] {σ : K ≃+* K} {n : ℕ}

@[expose] def suMat (x : SUid σ n) : Matrix (Fin n) (Fin n) K :=
  ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)

@[simp] theorem suMat_mul (x y : SUid σ n) : suMat (x * y) = suMat x * suMat y := rfl

@[simp] theorem suMat_one : suMat (1 : SUid σ n) = 1 := rfl

theorem suMat_mul_suMat_inv (x : SUid σ n) : suMat x * suMat x⁻¹ = 1 := by
  rw [← suMat_mul, mul_inv_cancel, suMat_one]

theorem suMat_inv_mul_suMat (x : SUid σ n) : suMat x⁻¹ * suMat x = 1 := by
  rw [← suMat_mul, inv_mul_cancel, suMat_one]

theorem suMat_injective : Function.Injective (suMat : SUid σ n → Matrix (Fin n) (Fin n) K) :=
  fun _ _ h => Subtype.ext (Units.ext h)

theorem suMat_smul (x : SUid σ n) (v : Fin n → K) : x • v = suMat x *ᵥ v := rfl

theorem det_suMat (x : SUid σ n) : (suMat x).det = 1 := x.2.1

@[expose] def suToSL (σ : K ≃+* K) (n : ℕ) : SUid σ n →* SL(n, K) where
  toFun x := ⟨suMat x, det_suMat x⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

theorem coe_suToSL (x : SUid σ n) :
    ((suToSL σ n x : SL(n, K)) : Matrix (Fin n) (Fin n) K) = suMat x := rfl

theorem suToSL_injective : Function.Injective (suToSL σ n) := fun _ _ h =>
  suMat_injective (congrArg (fun z : SL(n, K) => (z : Matrix (Fin n) (Fin n) K)) h)

theorem herm_eq_zero_of_eigen (x : SUid σ n) {v w : Fin n → K} {a b : K}
    (hv : suMat x *ᵥ v = a • v) (hw : suMat x *ᵥ w = b • w) (hab : σ a * b ≠ 1) :
    herm σ v w = 0 := by
  have h := herm_smul_smul σ x v w
  rw [suMat_smul, suMat_smul, hv, hw, herm_smul_left, herm_smul_right, ← mul_assoc] at h
  have h' : (σ a * b - 1) * herm σ v w = 0 := by linear_combination h
  exact (mul_eq_zero.mp h').resolve_left (sub_ne_zero.mpr hab)

theorem map_signOf_eq_self (b : Bool) : σ (signOf K b) = signOf K b := by
  cases b <;> simp

theorem neg_one_ne_one_of_two_ne_zero (h2 : (2 : K) ≠ 0) : (-1 : K) ≠ 1 := by
  intro h
  apply h2
  linear_combination -h

theorem map_signOf_mul_signOf_ne_one (h2 : (2 : K) ≠ 0) {a b : Bool} (hab : a ≠ b) :
    σ (signOf K a) * signOf K b ≠ 1 := by
  rw [map_signOf_eq_self]
  cases a <;> cases b <;> simp_all [neg_one_ne_one_of_two_ne_zero h2]

theorem orth_eigSpace_neg_one_one (h2 : (2 : K) ≠ 0) (x : SUid σ n) :
    Orth σ (eigSpace (suMat x) (-1)) (eigSpace (suMat x) 1) := by
  intro v hv w hw
  rw [mem_eigSpace] at hv hw
  refine herm_eq_zero_of_eigen x hv hw ?_
  rw [map_neg, map_one, neg_mul, one_mul]
  exact neg_one_ne_one_of_two_ne_zero h2

theorem orth_jointEig (h2 : (2 : K) ≠ 0) (i₁ i₂ : SUid σ n) {s t : Bool × Bool} (hst : s ≠ t) :
    Orth σ (jointEig (suMat i₁) (suMat i₂) s) (jointEig (suMat i₁) (suMat i₂) t) := by
  intro v hv w hw
  rw [mem_jointEig] at hv hw
  by_cases h1 : s.1 = t.1
  · have h2' : s.2 ≠ t.2 := fun h => hst (Prod.ext h1 h)
    exact herm_eq_zero_of_eigen i₂ hv.2 hw.2 (map_signOf_mul_signOf_ne_one h2 h2')
  · exact herm_eq_zero_of_eigen i₁ hv.1 hw.1 (map_signOf_mul_signOf_ne_one h2 h1)

theorem nondeg_of_orth_of_iSup_eq_top {S : Type*} (E : S → Submodule K (Fin n → K))
    (hE : ⨆ s, E s = ⊤) (horth : ∀ s t, s ≠ t → Orth σ (E s) (E t)) (s : S) :
    Nondeg σ (E s) := by
  intro v hv hv'
  refine eq_zero_of_herm σ fun u => ?_
  have hle : (⨆ t, E t) ≤ LinearMap.ker (hermL σ v) := iSup_le fun t w hw => by
    rw [LinearMap.mem_ker, hermL_apply]
    by_cases hts : t = s
    · subst hts
      exact hv' w hw
    · exact horth s t (Ne.symm hts) v hv w hw
  have hu : u ∈ ⨆ t, E t := by
    rw [hE]
    trivial
  have := hle hu
  rwa [LinearMap.mem_ker, hermL_apply] at this

theorem nondeg_jointEig (h2 : (2 : K) ≠ 0) {i₁ i₂ : SUid σ n} (h₁ : suMat i₁ * suMat i₁ = 1)
    (h₂ : suMat i₂ * suMat i₂ = 1) (hc : suMat i₁ * suMat i₂ = suMat i₂ * suMat i₁)
    (s : Bool × Bool) : Nondeg σ (jointEig (suMat i₁) (suMat i₂) s) :=
  nondeg_of_orth_of_iSup_eq_top _
    (iSup_jointEigenspace h2 (toLin'_mul_self h₁) (toLin'_mul_self h₂) (toLin'_mul_comm hc))
    (fun _ _ => orth_jointEig h2 i₁ i₂) s

theorem exists_herm_orthonormal_family (hσ : IsUnitaryInvolution σ) :
    ∀ (d : ℕ) {S : Submodule K (Fin n → K)}, finrank K S = d → Nondeg σ S →
      ∃ b : Fin d → (Fin n → K), (∀ j, b j ∈ S) ∧
        ∀ j k, herm σ (b j) (b k) = if j = k then 1 else 0 := by
  intro d
  induction d with
  | zero => exact fun _ _ => ⟨Fin.elim0, fun j => j.elim0, fun j => j.elim0⟩
  | succ d ih =>
    intro S hS hnd
    have hne : S ≠ ⊥ := by
      rintro rfl
      simp at hS
    obtain ⟨v, hvS, hv⟩ := exists_aniso_of_nondeg hσ hnd hne
    obtain ⟨c, hc⟩ := exists_smul_norm_one hσ hv
    have hsS : c • v ∈ S := S.smul_mem c hvS
    have hs1 : herm σ (c • v) (c • v) ≠ 0 := by
      rw [hc]
      exact one_ne_zero
    have hdim := finrank_eq_inf_perp_add_one hσ hsS hs1
    obtain ⟨b', hb'S, hb'⟩ := ih (S := S ⊓ perp σ (K ∙ c • v)) (by omega)
      (Nondeg.inf_perp_span_singleton hσ hsS hs1 hnd)
    have hperp : ∀ j, herm σ (b' j) (c • v) = 0 := fun j =>
      mem_perp_span_singleton.mp (hb'S j).2
    have hperp' : ∀ j, herm σ (c • v) (b' j) = 0 := fun j =>
      herm_eq_zero_comm σ hσ.invol (hperp j)
    refine ⟨Fin.cons (c • v) b', fun j => ?_, fun j k => ?_⟩
    · refine Fin.cases ?_ (fun j => ?_) j
      · simpa using hsS
      · simpa using (hb'S j).1
    · refine Fin.cases ?_ (fun j => ?_) j <;> refine Fin.cases ?_ (fun k => ?_) k
      · rw [Fin.cons_zero, ite_eq_left rfl]
        exact hc
      · rw [Fin.cons_zero, Fin.cons_succ, ite_eq_right (Fin.succ_ne_zero k).symm]
        exact hperp' k
      · rw [Fin.cons_succ, Fin.cons_zero, ite_eq_right (Fin.succ_ne_zero j)]
        exact hperp j
      · rw [Fin.cons_succ, Fin.cons_succ, hb' j k]
        simp

theorem exists_herm_orthonormal_adapted (hσ : IsUnitaryInvolution σ) {S : Type*} [DecidableEq S]
    (E : S → Submodule K (Fin n → K)) (hnd : ∀ s, Nondeg σ (E s))
    (horth : ∀ s t, s ≠ t → Orth σ (E s) (E t)) (ε : Fin n → S)
    (hε : ∀ s, Nat.card {j // ε j = s} = finrank K (E s)) :
    ∃ v : Fin n → (Fin n → K), (∀ j, v j ∈ E (ε j)) ∧
      ∀ j k, herm σ (v j) (v k) = if j = k then 1 else 0 := by
  choose b hbS hb using fun s => exists_herm_orthonormal_family hσ (finrank K (E s)) rfl (hnd s)
  let e : Fin n ≃ Σ s, Fin (finrank K (E s)) :=
    (Equiv.sigmaFiberEquiv ε).symm.trans
      (Equiv.sigmaCongrRight fun s => Finite.equivFinOfCardEq (hε s))
  let w : (Σ s, Fin (finrank K (E s))) → (Fin n → K) := fun x => b x.1 x.2
  have hw : ∀ x y, herm σ (w x) (w y) = if x = y then 1 else 0 := by
    rintro ⟨s, a⟩ ⟨t, c⟩
    by_cases hst : s = t
    · subst hst
      simp only [w, hb s a c, Sigma.mk.injEq, heq_eq_eq, true_and]
    · have hne : (⟨s, a⟩ : Σ s, Fin (finrank K (E s))) ≠ ⟨t, c⟩ := fun h =>
        hst (congrArg Sigma.fst h)
      rw [ite_eq_right hne]
      exact horth s t hst _ (hbS s a) _ (hbS t c)
  refine ⟨fun j => w (e j), fun j => hbS (e j).1 (e j).2, fun j k => ?_⟩
  rw [hw]
  exact if_congr e.injective.eq_iff rfl rfl

theorem exists_su_adapted (hσ : IsUnitaryInvolution σ) {S : Type*} [DecidableEq S] (hn : 0 < n)
    (E : S → Submodule K (Fin n → K)) (hnd : ∀ s, Nondeg σ (E s))
    (horth : ∀ s t, s ≠ t → Orth σ (E s) (E t)) (ε : Fin n → S)
    (hε : ∀ s, Nat.card {j // ε j = s} = finrank K (E s)) :
    ∃ g : SUid σ n, ∀ j, g • (Pi.single j 1 : Fin n → K) ∈ E (ε j) := by
  obtain ⟨v, hvE, hv⟩ := exists_herm_orthonormal_adapted hσ E hnd horth ε hε
  cases n with
  | zero => exact absurd hn (lt_irrefl 0)
  | succ m =>
    obtain ⟨g, hg⟩ := exists_mem_SUid_smul_single (σ := σ) hv
    refine ⟨g, fun j => ?_⟩
    obtain ⟨a, -, ha⟩ := hg j
    rw [ha]
    exact (E (ε j)).smul_mem a (hvE j)

theorem exists_su_frame (hσ : IsUnitaryInvolution σ) (h2 : (2 : K) ≠ 0) (hn : 0 < n)
    {i₁ i₂ : SUid σ n} (h₁ : suMat i₁ * suMat i₁ = 1) (h₂ : suMat i₂ * suMat i₂ = 1)
    (hc : suMat i₁ * suMat i₂ = suMat i₂ * suMat i₁) (ε : Fin n → Bool × Bool)
    (hε : ∀ s, Nat.card {j // ε j = s} = finrank K (jointEig (suMat i₁) (suMat i₂) s)) :
    ∃ g : SUid σ n,
      suMat i₁ * suMat g = suMat g * Matrix.diagonal (fun j => signOf K (ε j).1) ∧
      suMat i₂ * suMat g = suMat g * Matrix.diagonal (fun j => signOf K (ε j).2) := by
  obtain ⟨g, hg⟩ := exists_su_adapted hσ hn (jointEig (suMat i₁) (suMat i₂))
    (nondeg_jointEig h2 h₁ h₂ hc) (fun _ _ => orth_jointEig h2 i₁ i₂) ε hε
  refine ⟨g, ?_, ?_⟩
  · ext a j
    rw [Matrix.mul_diagonal]
    have := congr_fun (mem_jointEig.mp (hg j)).1 a
    rw [suMat_smul, Matrix.mulVec_single_one] at this
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm] using this
  · ext a j
    rw [Matrix.mul_diagonal]
    have := congr_fun (mem_jointEig.mp (hg j)).2 a
    rw [suMat_smul, Matrix.mulVec_single_one] at this
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm] using this

end CFSG.ClassicalInvolution.Models
