module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.F4.LAData

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.IrredF4Aux

open CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectF4

theorem sep {L M : Type*} [Field L] [AddCommGroup M] [Module L M] (N : Submodule L M)
    (A : Finset L) (d : ℕ) (hA : d < A.card) (w : ℕ → M)
    (h : ∀ a ∈ A, ∑ k ∈ Finset.range (d + 1), a ^ k • w k ∈ N) : ∀ k ≤ d, w k ∈ N := by
  classical
  intro k hk
  have key : ∀ φ : Module.Dual L (M ⧸ N), φ (N.mkQ (w k)) = 0 := by
    intro φ
    have hpoly : ∑ j ∈ Finset.range (d + 1),
        Polynomial.C (φ (N.mkQ (w j))) * Polynomial.X ^ j = 0 := by
      refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ A (fun a ha => ?_) ?_
      · have h1 : N.mkQ (∑ j ∈ Finset.range (d + 1), a ^ j • w j) = 0 := by
          rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
          exact h a ha
        have h2 := congrArg φ h1
        simp only [map_sum, map_smul, smul_eq_mul, map_zero] at h2
        rw [Polynomial.eval_finsetSum]
        refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_) h2
        rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
          mul_comm]
      · refine lt_of_le_of_lt (Polynomial.natDegree_sum_le_of_forall_le _ _ fun j hj => ?_) hA
        exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans
          (Nat.lt_add_one_iff.1 (Finset.mem_range.1 hj))
    have hk' : k < d + 1 := Nat.lt_add_one_iff.2 hk
    have := congrArg (fun p => Polynomial.coeff p k) hpoly
    simpa [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, hk'] using this
  have := (Module.forall_dual_apply_eq_zero_iff L (N.mkQ (w k))).1 key
  rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this

theorem sep_inj {L M ι : Type*} [Field L] [AddCommGroup M] [Module L M] [Fintype ι]
    (N : Submodule L M) (A : Finset L) (d : ℕ) (hA : d < A.card) (ex : ι → ℕ)
    (hex : Function.Injective ex) (hd : ∀ i, ex i ≤ d) (z : ι → M)
    (h : ∀ a ∈ A, ∑ i, a ^ ex i • z i ∈ N) : ∀ i, z i ∈ N := by
  classical
  intro i
  have hw := sep N A d hA (fun k => ∑ j, if ex j = k then z j else 0) (fun a ha => ?_) (ex i) (hd i)
  · have hzi : (∑ j, if ex j = ex i then z j else 0) = z i := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hj
        simp [hex.eq_iff, hj]
      · simp
    simpa [hzi] using hw
  · have hsum : ∑ k ∈ Finset.range (d + 1), a ^ k • (∑ j, if ex j = k then z j else 0) =
        ∑ j, a ^ ex j • z j := by
      simp only [Finset.smul_sum, smul_ite, smul_zero]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_ite_eq]
      simp [Nat.lt_add_one_iff.2 (hd j)]
    rw [hsum]
    exact h a ha

def actFunA {L : Type} [Field L] (a1 : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ) → ℤ)
    (γ : Fin Tag.F4.rank → ℤ) :
    ((Fin Tag.F4.rank → ℤ) → L) →ₗ[L] ((Fin Tag.F4.rank → ℤ) → L) where
  toFun v := fun ν => (a1 γ (ν - γ) : L) * v (ν - γ)
  map_add' v v' := by funext ν; simp [mul_add]
  map_smul' s v := by funext ν; simp [mul_left_comm]

def actFunB {L : Type} [Field L] (a2 : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ) → ℤ)
    (γ : Fin Tag.F4.rank → ℤ) :
    ((Fin Tag.F4.rank → ℤ) → L) →ₗ[L] ((Fin Tag.F4.rank → ℤ) → L) where
  toFun v := fun ν => (a2 γ (ν - 2 • γ) : L) * v (ν - 2 • γ)
  map_add' v v' := by funext ν; simp [mul_add]
  map_smul' s v := by funext ν; simp [mul_left_comm]

def actFunX {L : Type} [Field L] (a1 a2 : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ) → ℤ)
    (γ : Fin Tag.F4.rank → ℤ) :
    Fin 3 → ((Fin Tag.F4.rank → ℤ) → L) →ₗ[L] ((Fin Tag.F4.rank → ℤ) → L) :=
  ![LinearMap.id, actFunA a1 γ, actFunB a2 γ]

theorem actFun_eq {L : Type} [Field L]
    (a1 a2 : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ) → ℤ) (γ : Fin Tag.F4.rank → ℤ) (t : L)
    (v : (Fin Tag.F4.rank → ℤ) → L) :
    actFun a1 a2 γ t v = v + t • actFunA a1 γ v + t ^ 2 • actFunB a2 γ v := by
  funext ν
  simp only [actFun, actFunA, actFunB, LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  ring

theorem actFun_eq_sum {L : Type} [Field L]
    (a1 a2 : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ) → ℤ) (γ : Fin Tag.F4.rank → ℤ) (t : L)
    (v : (Fin Tag.F4.rank → ℤ) → L) :
    actFun a1 a2 γ t v = ∑ i : Fin 3, t ^ (i : ℕ) • actFunX a1 a2 γ i v := by
  rw [actFun_eq, Fin.sum_univ_three]
  simp [actFunX]

theorem comp_expand {L M : Type*} [Field L] [AddCommGroup M] [Module L M]
    (X Y : Fin 3 → M →ₗ[L] M) (F G : L → M → M)
    (hF : ∀ t v, F t v = ∑ i : Fin 3, t ^ (i : ℕ) • X i v)
    (hG : ∀ t v, G t v = ∑ j : Fin 3, t ^ (j : ℕ) • Y j v) (q : ℕ) (e a : L) (v : M) :
    F a (G (e * a ^ q) v) =
      ∑ p : Fin 3 × Fin 3, a ^ ((p.1 : ℕ) + q * (p.2 : ℕ)) • (e ^ (p.2 : ℕ) • X p.1 (Y p.2 v)) := by
  rw [hG, hF, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [map_sum, map_smul, Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  ring

theorem algebraize_single {L : Type} [Field L]
    {a1 a2 : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ) → ℤ}
    (N : Submodule L ((Fin Tag.F4.rank → ℤ) → L)) (γ : Fin Tag.F4.rank → ℤ) (T : Finset L)
    (hT : 3 ≤ T.card) (h : ∀ t ∈ T, ∀ v ∈ N, actFun a1 a2 γ t v ∈ N) :
    ∀ t : L, ∀ v ∈ N, actFun a1 a2 γ t v ∈ N := by
  intro t v hv
  have hz : ∀ i : Fin 3, actFunX a1 a2 γ i v ∈ N := by
    refine sep_inj N T 2 (by omega) (fun i : Fin 3 => (i : ℕ)) Fin.val_injective
      (fun i => Nat.lt_add_one_iff.1 i.isLt) (fun i => actFunX a1 a2 γ i v) fun a ha => ?_
    rw [← actFun_eq_sum]
    exact h a ha v hv
  have hA : actFunA a1 γ v ∈ N := hz 1
  have hB : actFunB a2 γ v ∈ N := hz 2
  rw [actFun_eq]
  exact N.add_mem (N.add_mem hv (N.smul_mem _ hA)) (N.smul_mem _ hB)

theorem algebraize_pair {L : Type} [Field L]
    {a1 a2 : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ) → ℤ}
    (N : Submodule L ((Fin Tag.F4.rank → ℤ) → L)) (δ₁ δ₂ : Fin Tag.F4.rank → ℤ) (q : ℕ)
    (hq : 3 ≤ q) (e : L) (he : e ≠ 0) (A : Finset L) (hA : 2 * q + 2 < A.card)
    (h : ∀ a ∈ A, ∀ v ∈ N, actFun a1 a2 δ₁ a (actFun a1 a2 δ₂ (e * a ^ q) v) ∈ N) :
    (∀ t : L, ∀ v ∈ N, actFun a1 a2 δ₁ t v ∈ N) ∧ (∀ t : L, ∀ v ∈ N, actFun a1 a2 δ₂ t v ∈ N) := by
  have hinj : Function.Injective (fun p : Fin 3 × Fin 3 => (p.1 : ℕ) + q * (p.2 : ℕ)) := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ hij
    simp only at hij
    have hi := i.isLt
    have hi' := i'.isLt
    have hjj : (j : ℕ) = j' := by
      rcases Nat.lt_trichotomy (j : ℕ) j' with hlt | heq | hgt
      · have := Nat.mul_le_mul_left q (Nat.succ_le_of_lt hlt)
        rw [Nat.mul_succ] at this
        omega
      · exact heq
      · have := Nat.mul_le_mul_left q (Nat.succ_le_of_lt hgt)
        rw [Nat.mul_succ] at this
        omega
    have hii : (i : ℕ) = i' := by
      rw [hjj] at hij
      omega
    rw [Prod.mk.injEq]
    exact ⟨Fin.ext hii, Fin.ext hjj⟩
  have hbd : ∀ p : Fin 3 × Fin 3, (p.1 : ℕ) + q * (p.2 : ℕ) ≤ 2 * q + 2 := by
    intro p
    have h1 : (p.1 : ℕ) ≤ 2 := Nat.lt_add_one_iff.1 p.1.isLt
    have h2 : (p.2 : ℕ) ≤ 2 := Nat.lt_add_one_iff.1 p.2.isLt
    have := Nat.mul_le_mul_left q h2
    omega
  have key : ∀ v ∈ N, ∀ p : Fin 3 × Fin 3,
      e ^ (p.2 : ℕ) • actFunX a1 a2 δ₁ p.1 (actFunX a1 a2 δ₂ p.2 v) ∈ N := by
    intro v hv
    refine sep_inj N A (2 * q + 2) hA (fun p : Fin 3 × Fin 3 => (p.1 : ℕ) + q * (p.2 : ℕ))
      hinj hbd _ fun a ha => ?_
    rw [← comp_expand (actFunX a1 a2 δ₁) (actFunX a1 a2 δ₂) (actFun a1 a2 δ₁) (actFun a1 a2 δ₂)
      (actFun_eq_sum a1 a2 δ₁) (actFun_eq_sum a1 a2 δ₂) q e a v]
    exact h a ha v hv
  have hA₁ : ∀ v ∈ N, actFunA a1 δ₁ v ∈ N := fun v hv => by
    simpa [actFunX] using key v hv (1, 0)
  have hB₁ : ∀ v ∈ N, actFunB a2 δ₁ v ∈ N := fun v hv => by
    simpa [actFunX] using key v hv (2, 0)
  have hA₂ : ∀ v ∈ N, actFunA a1 δ₂ v ∈ N := fun v hv => by
    have := key v hv (0, 1)
    simp [actFunX] at this
    exact (Submodule.smul_mem_iff N he).1 this
  have hB₂ : ∀ v ∈ N, actFunB a2 δ₂ v ∈ N := fun v hv => by
    have := key v hv (0, 2)
    simp [actFunX] at this
    exact (Submodule.smul_mem_iff N (pow_ne_zero 2 he)).1 this
  refine ⟨fun t v hv => ?_, fun t v hv => ?_⟩
  · rw [actFun_eq]
    exact N.add_mem (N.add_mem hv (N.smul_mem _ (hA₁ v hv))) (N.smul_mem _ (hB₁ v hv))
  · rw [actFun_eq]
    exact N.add_mem (N.add_mem hv (N.smul_mem _ (hA₂ v hv))) (N.smul_mem _ (hB₂ v hv))

theorem mem_of_mem_span_map {K L X : Type} [Field K] [Field L] [Algebra K L]
    (W : Submodule K (X → K)) {u : X → K}
    (h : (fun x => algebraMap K L (u x)) ∈
      Submodule.span L ((fun w : X → K => fun x => algebraMap K L (w x)) '' (W : Set (X → K)))) :
    u ∈ W := by
  obtain ⟨φ, hφ⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap K L)
    (LinearMap.ker_eq_bot.2 (algebraMap K L).injective)
  have hφ1 : ∀ k : K, φ (algebraMap K L k) = k := fun k => by
    simpa using LinearMap.congr_fun hφ k
  let S : Submodule L (X → L) :=
    { carrier := {c | ∀ ψ : L →ₗ[K] K, (fun x => ψ (c x)) ∈ W}
      zero_mem' := fun ψ => by
        have e : (fun x => ψ ((0 : X → L) x)) = 0 := by
          funext x; simp
        show (fun x => ψ ((0 : X → L) x)) ∈ W
        rw [e]
        exact W.zero_mem
      add_mem' := fun {c c'} hc hc' ψ => by
        have e : (fun x => ψ ((c + c') x)) = (fun x => ψ (c x)) + (fun x => ψ (c' x)) := by
          funext x; simp
        show (fun x => ψ ((c + c') x)) ∈ W
        rw [e]
        exact W.add_mem (hc ψ) (hc' ψ)
      smul_mem' := fun s c hc ψ => by
        have := hc (ψ ∘ₗ LinearMap.mulLeft K s)
        simpa using this }
  have hS : Submodule.span L
      ((fun w : X → K => fun x => algebraMap K L (w x)) '' (W : Set (X → K))) ≤ S := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨w, hw, rfl⟩ ψ
    have e : (fun x => ψ (algebraMap K L (w x))) = (ψ 1) • w := by
      funext x
      simp [Algebra.algebraMap_eq_smul_one, mul_comm]
    show (fun x => ψ (algebraMap K L (w x))) ∈ W
    rw [e]
    exact W.smul_mem _ hw
  have := hS h φ
  simpa [hφ1] using this

theorem exists_two_indep {L : Type} [Field L] (q : ℕ) (hq : 2 ≤ q) (e : L) (he : e ≠ 0)
    (A : Finset L) (hA : q < A.card) :
    ∃ a₁ ∈ A, ∃ a₂ ∈ A, a₁ * (e * a₂ ^ q) - a₂ * (e * a₁ ^ q) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨a₁, ha₁, ha₁0⟩ := Finset.exists_mem_ne (show 1 < A.card by omega) (0 : L)
  have hq1 : a₁ ^ q = a₁ * a₁ ^ (q - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hp : (Polynomial.X ^ q - Polynomial.C (a₁ ^ (q - 1)) * Polynomial.X : Polynomial L) = 0 := by
    refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ A (fun a₂ ha₂ => ?_) ?_
    · have h0 := hcon a₁ ha₁ a₂ ha₂
      simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_mul,
        Polynomial.eval_C]
      rw [hq1] at h0
      have h1 : (a₁ * e) * (a₂ ^ q - a₁ ^ (q - 1) * a₂) = 0 := by linear_combination h0
      exact (mul_eq_zero.1 h1).resolve_left (mul_ne_zero ha₁0 he)
    · refine lt_of_le_of_lt ((Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)) hA
      · simp
      · have h1 : (Polynomial.C (a₁ ^ (q - 1)) * Polynomial.X : Polynomial L).natDegree ≤ 1 := by
          simpa using Polynomial.natDegree_C_mul_X_pow_le (a₁ ^ (q - 1)) 1
        omega
  have h1 := congrArg (fun p => Polynomial.coeff p q) hp
  simp only [Polynomial.coeff_sub, Polynomial.coeff_X_pow_self, Polynomial.coeff_C_mul_X,
    Polynomial.coeff_zero] at h1
  rw [if_neg (by omega)] at h1
  simp at h1

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.IrredF4Aux
