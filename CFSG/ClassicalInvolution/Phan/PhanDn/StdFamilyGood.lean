module

public import CFSG.ClassicalInvolution.Phan.PhanDn.StdFamilyTorus
public import CFSG.ClassicalInvolution.Phan.PhanDn.StdFamilyDisj
public import CFSG.LocalAnalysis.StandardType.PhanETorusInf
public import CFSG.LocalAnalysis.StandardType.PhanEMap
public import CFSG.GroupTheory.CommutingProductFixedSubgroup

public section

namespace CFSG.ClassicalInvolution.PhanDn

open CFSG.ClassicalInvolution.Phan
open CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.ClassicalInvolution.Phan.PhanE
open CFSG.ClassicalGroups.Unitary
open CFSG.LieType.Universal.Unitary
open CFSG.LieType.Steinberg
open CFSG.LieType.BorelTits
open QuadraticMap
open Matrix
open CFSG.Timmesfeld

variable {F K : Type} [Field F] [Field K] [Finite K] [Algebra F K] {f : ℕ} [CharP K 2]
variable (E : QuadExt F K (unitaryInvolution K 2 f))

theorem diagHom_smul {n : ℕ} (t : Fin n → normOne (unitaryInvolution K 2 f)) (c : K)
    (v : Fin n → K) :
    diagHom F (unitaryInvolution K 2 f) n t (c • v) =
      c • diagHom F (unitaryInvolution K 2 f) n t v := by
  funext i
  rw [diagHom_apply, Pi.smul_apply, Pi.smul_apply, diagHom_apply, smul_eq_mul, smul_eq_mul]
  ring

theorem diagHom_single {n : ℕ} (t : Fin n → normOne (unitaryInvolution K 2 f)) (c : Fin n) :
    diagHom F (unitaryInvolution K 2 f) n t (Pi.single c (1 : K)) =
      (((t c : normOne (unitaryInvolution K 2 f)) : Kˣ) : K) • Pi.single c (1 : K) := by
  funext i
  rw [diagHom_apply, Pi.smul_apply, Pi.single_apply]
  by_cases h : i = c <;> simp [h]

private theorem eq_diagHom_of_forall_single {m : ℕ} {g : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)}
    {t : Fin (m + 1) → normOne (unitaryInvolution K 2 f)}
    (hlin : ∀ (c : K) (v : Fin (m + 1) → K), g (c • v) = c • g v)
    (h : ∀ c, g (Pi.single c (1 : K)) =
      (((t c : normOne (unitaryInvolution K 2 f)) : Kˣ) : K) • Pi.single c (1 : K)) :
    g = diagHom F (unitaryInvolution K 2 f) (m + 1) t := by
  have hinv : (diagHom F (unitaryInvolution K 2 f) (m + 1) t)⁻¹ =
      diagHom F (unitaryInvolution K 2 f) (m + 1) t⁻¹ :=
    (MonoidHom.map_inv (diagHom F (unitaryInvolution K 2 f) (m + 1)) t).symm
  have h1 : (diagHom F (unitaryInvolution K 2 f) (m + 1) t)⁻¹ * g = 1 := by
    refine eq_one_of_forall_single (fun c v => ?_) (fun c => ?_)
    · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hlin, hinv, diagHom_smul (F := F)]
    · rw [LinearEquiv.mul_apply, h c, ← diagHom_single (F := F) t c, ← LinearEquiv.mul_apply,
        inv_mul_cancel, LinearEquiv.coe_one, id_eq]
  have h2 : diagHom F (unitaryInvolution K 2 f) (m + 1) t *
      ((diagHom F (unitaryInvolution K 2 f) (m + 1) t)⁻¹ * g) = g := by
    rw [← mul_assoc, mul_inv_cancel, one_mul]
  rw [h1, mul_one] at h2
  exact h2.symm

private theorem eq_one_of_diagHom_single {n : ℕ} {g : (Fin n → K) ≃ₗ[F] (Fin n → K)}
    {t : Fin n → normOne (unitaryInvolution K 2 f)}
    (h : g = diagHom F (unitaryInvolution K 2 f) n t) {c : Fin n}
    (hc : g (Pi.single c (1 : K)) = Pi.single c (1 : K)) : t c = 1 := by
  rw [h, diagHom_single] at hc
  have hcc := congrFun hc c
  simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at hcc
  exact Subtype.ext (Units.ext hcc)

private theorem diagHom_single_apply {n : ℕ} {g : (Fin n → K) ≃ₗ[F] (Fin n → K)}
    {t : Fin n → normOne (unitaryInvolution K 2 f)}
    (h : g = diagHom F (unitaryInvolution K 2 f) n t) (c : Fin n) :
    g (Pi.single c (1 : K)) =
      (((t c : normOne (unitaryInvolution K 2 f)) : Kˣ) : K) • Pi.single c (1 : K) := by
  rw [h, diagHom_single]

theorem stdTau_self_inv (m : ℕ) : (stdTau (K := K) (f := f) E m)⁻¹ = stdTau E m :=
  inv_eq_of_mul_eq_one_right (tauAt_mul_self E (Fin.last m))

theorem stdTau_mul_self (m : ℕ) : stdTau (K := K) (f := f) E m * stdTau E m = 1 :=
  tauAt_mul_self E (Fin.last m)

theorem stdConj_stdConj (m : ℕ) (x : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) :
    stdConj E m (stdConj E m x) = x := by
  change MulAut.conj (stdTau E m) (MulAut.conj (stdTau E m) x) = x
  rw [MulAut.conj_apply, MulAut.conj_apply, stdTau_self_inv]
  calc stdTau E m * (stdTau E m * x * stdTau E m) * stdTau E m
      = (stdTau E m * stdTau E m) * x * (stdTau E m * stdTau E m) := by
        simp only [mul_assoc]
    _ = 1 * x * 1 := by rw [stdTau_mul_self]
    _ = x := by simp

private theorem update_inv_last_inv {m : ℕ} (t : Fin (m + 1) → normOne (unitaryInvolution K 2 f)) :
    Function.update
        (Function.update t (Fin.last m) ((t (Fin.last m))⁻¹)) (Fin.last m)
        (((Function.update t (Fin.last m) ((t (Fin.last m))⁻¹)) (Fin.last m))⁻¹) = t := by
  funext i
  by_cases hi : i = Fin.last m
  · subst hi
    simp
  · rw [Function.update_apply, if_neg hi, Function.update_apply, if_neg hi]

theorem stdConj_diagHom (m : ℕ) (t : Fin (m + 1) → normOne (unitaryInvolution K 2 f)) :
    (stdConj E m).toMonoidHom (diagHom F (unitaryInvolution K 2 f) (m + 1) t) =
      diagHom F (unitaryInvolution K 2 f) (m + 1)
        (Function.update t (Fin.last m) ((t (Fin.last m))⁻¹)) := by
  have hσ : unitaryInvolution K 2 f
        (((t (Fin.last m) : normOne (unitaryInvolution K 2 f)) : Kˣ) : K) =
      ((((t (Fin.last m))⁻¹ : normOne (unitaryInvolution K 2 f)) : Kˣ) : K) := by
    have hu := (mem_normOne (unitaryInvolution K 2 f)).1 (t (Fin.last m)).2
    have h2 := eq_inv_of_mul_eq_one_left hu
    simpa [Subgroup.coe_inv, Units.val_inv_eq_inv_val] using h2
  apply LinearEquiv.ext
  intro v
  change (MulAut.conj (stdTau E m) (diagHom F (unitaryInvolution K 2 f) (m + 1) t)) v =
    (diagHom F (unitaryInvolution K 2 f) (m + 1)
      (Function.update t (Fin.last m) ((t (Fin.last m))⁻¹))) v
  rw [MulAut.conj_apply, LinearEquiv.mul_apply, LinearEquiv.mul_apply, stdTau_self_inv]
  funext i
  rw [stdTau, tauAt_apply E, diagHom_apply, tauAt_apply E]
  by_cases hi : i = Fin.last m
  · subst hi
    simp only [Function.update_self, diagHom_apply, map_mul, hσ,
      E.isUnitary.invol, ↓reduceIte]
  · simp only [if_neg hi, Function.update_apply, diagHom_apply]

theorem diagHom_mul_suEndN_blockEmb_mul_inv
    (hK : Nat.card K = (2 ^ f) ^ 2)
    {n k i : ℕ} (h : i + k ≤ n)
    (d : Fin n → normOne (unitaryInvolution K 2 f)) (A : Su K 2 f k) :
    diagHom F (unitaryInvolution K 2 f) n d *
      suEndN (unitaryInvolution K 2 f) n (blockEmb K 2 f n k i h A) *
      (diagHom F (unitaryInvolution K 2 f) n d)⁻¹ =
    suEndN (unitaryInvolution K 2 f) n
      (blockEmb K 2 f n k i h
        (conjDiag (K := K) (p := 2) (f := f) hK
          (fun x : Fin k => d (blockIdx i h x)) A)) := by
  set D : Matrix (Fin n) (Fin n) K := Matrix.diagonal fun a => ((d a : Kˣ) : K) with hD
  set Dinv : Matrix (Fin n) (Fin n) K :=
    Matrix.diagonal fun a => (((d a)⁻¹ : Kˣ) : K) with hDinv
  set M : Matrix (Fin n) (Fin n) K :=
    blockMat n i (((A : GL (Fin k) K) : Matrix (Fin k) (Fin k) K)) with hM
  set M' : Matrix (Fin n) (Fin n) K :=
    blockMat n i (((conjDiag (K := K) (p := 2) (f := f) hK
      (fun x : Fin k => d (blockIdx i h x)) A : GL (Fin k) K) :
      Matrix (Fin k) (Fin k) K)) with hM'
  have hdiag : ∀ v : Fin n → K, diagHom F (unitaryInvolution K 2 f) n d v = D *ᵥ v := by
    intro v
    funext a
    rw [diagHom_apply, Matrix.mulVec_diagonal]
  have hdiag_inv : ∀ v : Fin n → K,
      diagHom F (unitaryInvolution K 2 f) n d⁻¹ v = Dinv *ᵥ v := by
    intro v
    funext a
    rw [diagHom_apply, Matrix.mulVec_diagonal]
    simp [Pi.inv_apply]
  have hmat : D * M * Dinv = M' := by
    rw [hD, hDinv, hM, hM']
    exact diagonal_mul_blockMat_mul_diagonal h
      (fun a => ((d a : Kˣ) : K)) (fun a => (((d a)⁻¹ : Kˣ) : K))
      (fun a => by simp) (((A : GL (Fin k) K) : Matrix (Fin k) (Fin k) K))
  apply LinearEquiv.ext
  intro v
  let t : (Fin n → K) ≃ₗ[F] (Fin n → K) := diagHom F (unitaryInvolution K 2 f) n d
  let s : (Fin n → K) ≃ₗ[F] (Fin n → K) :=
    suEndN (unitaryInvolution K 2 f) n (blockEmb K 2 f n k i h A)
  let s' : (Fin n → K) ≃ₗ[F] (Fin n → K) :=
    suEndN (unitaryInvolution K 2 f) n
      (blockEmb K 2 f n k i h
        (conjDiag (K := K) (p := 2) (f := f) hK
          (fun x : Fin k => d (blockIdx i h x)) A))
  change (t * s * t⁻¹) v = s' v
  have ht : t = diagHom F (unitaryInvolution K 2 f) n d := rfl
  have hs : s = suEndN (unitaryInvolution K 2 f) n (blockEmb K 2 f n k i h A) := rfl
  have hs' : s' = suEndN (unitaryInvolution K 2 f) n
      (blockEmb K 2 f n k i h
        (conjDiag (K := K) (p := 2) (f := f) hK
          (fun x : Fin k => d (blockIdx i h x)) A)) := rfl
  have hL : (t * s * t⁻¹) v = (D * M * Dinv) *ᵥ v := by
    rw [ht, hs]
    rw [show (diagHom F (unitaryInvolution K 2 f) n d)⁻¹ =
      diagHom F (unitaryInvolution K 2 f) n d⁻¹ from (map_inv _ _).symm]
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    simp only [hdiag, hdiag_inv, suEndN_apply, CFSG.ClassicalGroups.Unitary.smul_def,
      coe_coe_blockEmb]
    rw [hM, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have hR : s' v = M' *ᵥ v := by
    rw [hs', suEndN_apply, CFSG.ClassicalGroups.Unitary.smul_def, coe_coe_blockEmb]
  rw [hL, hR, hmat]

private theorem stdConj_diagHom_update (m : ℕ)
    (t : Fin (m + 1) → normOne (unitaryInvolution K 2 f)) :
    (stdConj E m).toMonoidHom
        (diagHom F (unitaryInvolution K 2 f) (m + 1)
          (Function.update t (Fin.last m) ((t (Fin.last m))⁻¹))) =
      diagHom F (unitaryInvolution K 2 f) (m + 1) t := by
  have h := stdConj_diagHom (E := E) m
    (Function.update t (Fin.last m) ((t (Fin.last m))⁻¹))
  rw [update_inv_last_inv] at h
  exact h

private theorem chainIota_entries {m : ℕ} (k : Fin m) (a : Su K 2 f 2)
    {t : Fin (m + 1) → normOne (unitaryInvolution K 2 f)}
    (h : stdChainIota (F := F) (f := f) m k a =
      diagHom F (unitaryInvolution K 2 f) (m + 1) t) :
    ((((a : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) 0 0 =
        (((t (Fin.castSucc k) : normOne (unitaryInvolution K 2 f)) : Kˣ) : K)) ∧
      ((((a : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) 1 0 = 0) ∧
      ((((a : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) 0 1 = 0) ∧
      ((((a : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) 1 1 =
        (((t (k.succ) : normOne (unitaryInvolution K 2 f)) : Kˣ) : K)) := by
  have hc0 : (Fin.castSucc k : Fin (m + 1)) = (⟨k.val, by omega⟩ : Fin (m + 1)) :=
    Fin.ext rfl
  have hc1 : (k.succ : Fin (m + 1)) = (⟨k.val + 1, by omega⟩ : Fin (m + 1)) :=
    Fin.ext rfl
  have hne : (⟨k.val, by omega⟩ : Fin (m + 1)) ≠ ⟨k.val + 1, by omega⟩ := by
    intro hh
    have := congrArg Fin.val hh
    simp at this
  have hne' : (⟨k.val + 1, by omega⟩ : Fin (m + 1)) ≠ ⟨k.val, by omega⟩ := hne.symm
  have hkey : ∀ c : Fin (m + 1),
      stdChainIota (F := F) (f := f) m k a (Pi.single c (1 : K)) =
        diagHom F (unitaryInvolution K 2 f) (m + 1) t (Pi.single c (1 : K)) :=
    fun c => by rw [h]
  constructor
  · have hv := congrFun (hkey (Fin.castSucc k)) (Fin.castSucc k)
    rw [stdChainIota_apply, hc0, blockEmb2_smul_apply_left, diagHom_single] at hv
    simp only [Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_of_ne hne', smul_eq_mul,
      mul_one, mul_zero, add_zero] at hv
    simpa [hc0] using hv
  constructor
  · have hv := congrFun (hkey (Fin.castSucc k)) (k.succ)
    rw [stdChainIota_apply, hc0, hc1, blockEmb2_smul_apply_right, diagHom_single] at hv
    simp only [Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_of_ne hne', smul_eq_mul,
      mul_one, mul_zero, add_zero] at hv
    exact hv
  constructor
  · have hv := congrFun (hkey (k.succ)) (Fin.castSucc k)
    rw [stdChainIota_apply, hc1, hc0, blockEmb2_smul_apply_left, diagHom_single] at hv
    simp only [Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_of_ne hne, smul_eq_mul,
      mul_one, mul_zero, zero_add] at hv
    exact hv
  · have hv := congrFun (hkey (k.succ)) (k.succ)
    rw [stdChainIota_apply, hc1, blockEmb2_smul_apply_right, diagHom_single] at hv
    simp only [Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_of_ne hne, smul_eq_mul,
      mul_one, mul_zero, zero_add] at hv
    simpa [hc1] using hv

private theorem exists_chainIota_torusTwo_of_diag (E : QuadExt F K (unitaryInvolution K 2 f))
    {m : ℕ} (hm : 3 ≤ m) (k : Fin m) (a : Su K 2 f 2)
    {t : Fin (m + 1) → normOne (unitaryInvolution K 2 f)}
    (h : stdChainIota (F := F) (f := f) m k a =
      diagHom F (unitaryInvolution K 2 f) (m + 1) t) :
    ∃ u : normOne (unitaryInvolution K 2 f),
      stdChainIota (F := F) (f := f) m k (torusTwo (unitaryInvolution K 2 f) u) =
        diagHom F (unitaryInvolution K 2 f) (m + 1) t := by
  obtain ⟨hA00, hA10, hA01, hA11⟩ := chainIota_entries (F := F) (f := f) k a h
  have hprodK : (((t (Fin.castSucc k) : normOne (unitaryInvolution K 2 f)) : Kˣ) : K) *
      (((t (k.succ) : normOne (unitaryInvolution K 2 f)) : Kˣ) : K) = 1 := by
    have hdet : (((a : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)).det = 1 := a.2.1
    rw [Matrix.det_fin_two] at hdet
    rw [hA00, hA01, hA10, hA11, mul_zero, sub_zero] at hdet
    exact hdet
  have hprod : t (Fin.castSucc k) * t (k.succ) = 1 := by
    refine Subtype.ext (Units.ext ?_)
    simpa [Subgroup.coe_mul, Units.val_mul] using hprodK
  have hlast : t (k.succ) = (t (Fin.castSucc k))⁻¹ := eq_inv_of_mul_eq_one_right hprod
  have hoff : ∀ c : Fin (m + 1), c ≠ Fin.castSucc k → c ≠ k.succ → t c = 1 := by
    intro c h1 h2
    have hc1 : c.val ≠ k.val := fun hh => h1 (Fin.ext (by simpa using hh))
    have hc2 : c.val ≠ k.val + 1 := fun hh => h2 (Fin.ext (by simpa using hh))
    have hs : stdChainIota (F := F) (f := f) m k a (Pi.single c (1 : K)) =
        Pi.single c (1 : K) := stdChainIota_single_of_not_mem k a hc1 hc2
    rw [h] at hs
    exact eq_one_of_diagHom_single rfl hs
  have ht : t = Pi.mulSingle (Fin.castSucc k) (t (Fin.castSucc k)) *
      Pi.mulSingle (k.succ) (t (Fin.castSucc k))⁻¹ := by
    funext c
    rw [Pi.mul_apply, Pi.mulSingle_apply, Pi.mulSingle_apply]
    by_cases h1 : c = Fin.castSucc k
    · subst h1
      simp [Fin.castSucc_lt_succ.ne]
    · by_cases h2 : c = k.succ
      · subst h2
        rw [if_neg h1, if_pos rfl, one_mul, hlast]
      · rw [if_neg h1, if_neg h2, mul_one, hoff c h1 h2]
  refine ⟨t (Fin.castSucc k), ?_⟩
  have hnt : stdChainIota (F := F) (f := f) m k
      (torusTwo (unitaryInvolution K 2 f) (t (Fin.castSucc k))) =
      diagHom F (unitaryInvolution K 2 f) (m + 1)
        (Pi.mulSingle (Fin.castSucc k) (t (Fin.castSucc k)) *
          Pi.mulSingle (k.succ) (t (Fin.castSucc k))⁻¹) := by
    rw [← stdFamilyV_ι_castSucc]
    exact stdFamilyV_nodeTor_castSucc E m hm k (t (Fin.castSucc k))
  rw [hnt, ← ht]

private theorem exists_forkIota_torusTwo_of_diag {m : ℕ} (hm : 3 ≤ m) (a : Su K 2 f 2)
    {t : Fin (m + 1) → normOne (unitaryInvolution K 2 f)}
    (h : stdForkIota E m hm a = diagHom F (unitaryInvolution K 2 f) (m + 1) t) :
    ∃ u : normOne (unitaryInvolution K 2 f),
      stdForkIota E m hm (torusTwo (unitaryInvolution K 2 f) u) =
        diagHom F (unitaryInvolution K 2 f) (m + 1) t := by
  have hchain : stdChainIota (F := F) (f := f) m ⟨m - 1, by omega⟩ a =
      diagHom F (unitaryInvolution K 2 f) (m + 1)
        (Function.update t (Fin.last m) ((t (Fin.last m))⁻¹)) := by
    have h2 : (stdConj E m).toMonoidHom
          ((stdConj E m).toMonoidHom (stdChainIota (F := F) (f := f) m
            ⟨m - 1, by omega⟩ a)) =
        (stdConj E m).toMonoidHom (diagHom F (unitaryInvolution K 2 f) (m + 1) t) :=
      congrArg (stdConj E m).toMonoidHom h
    change stdConj E m (stdConj E m (stdChainIota (F := F) (f := f) m
        ⟨m - 1, by omega⟩ a)) =
      stdConj E m (diagHom F (unitaryInvolution K 2 f) (m + 1) t) at h2
    rw [stdConj_stdConj] at h2
    change stdChainIota (F := F) (f := f) m ⟨m - 1, by omega⟩ a =
      (stdConj E m).toMonoidHom (diagHom F (unitaryInvolution K 2 f) (m + 1) t) at h2
    rw [stdConj_diagHom] at h2
    exact h2
  obtain ⟨u, hu⟩ := exists_chainIota_torusTwo_of_diag E hm
    (⟨m - 1, by omega⟩ : Fin m) a hchain
  refine ⟨u, ?_⟩
  have h2 : (stdConj E m).toMonoidHom
        (stdChainIota (F := F) (f := f) m ⟨m - 1, by omega⟩
          (torusTwo (unitaryInvolution K 2 f) u)) =
      (stdConj E m).toMonoidHom
        (diagHom F (unitaryInvolution K 2 f) (m + 1)
          (Function.update t (Fin.last m) ((t (Fin.last m))⁻¹))) := congrArg _ hu
  rw [stdConj_diagHom_update] at h2
  exact h2

private theorem chainTheta_entries {m : ℕ} (k : Fin m) (hk : k.val + 1 < m) (B : Su K 2 f 3)
    {t : Fin (m + 1) → normOne (unitaryInvolution K 2 f)}
    (h : stdChainTheta (F := F) (f := f) m k hk B =
      diagHom F (unitaryInvolution K 2 f) (m + 1) t) (y x : Fin 3) :
    (((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) y x =
      if y = x then
        (((t (blockIdx k.val (by omega) x) : normOne (unitaryInvolution K 2 f)) : Kˣ) : K)
      else 0 := by
  have hblk : k.val + 3 ≤ m + 1 := by omega
  have hkey : stdChainTheta (F := F) (f := f) m k hk B
        (Pi.single (blockIdx k.val hblk x) (1 : K)) =
      diagHom F (unitaryInvolution K 2 f) (m + 1) t
        (Pi.single (blockIdx k.val hblk x) (1 : K)) := by rw [h]
  have hv := congrFun hkey (blockIdx k.val hblk y)
  rw [stdChainTheta, MonoidHom.comp_apply, suEndN_apply,
    CFSG.ClassicalGroups.Unitary.smul_def, coe_coe_blockEmb3,
    blockMat_mulVec_blockIdx] at hv
  have hcol : (fun z : Fin 3 => (Pi.single (blockIdx k.val hblk x) (1 : K) :
        Fin (m + 1) → K) (blockIdx k.val hblk z)) = Pi.single x (1 : K) := by
    funext z
    rw [Pi.single_apply, Pi.single_apply]
    by_cases hzx : z = x
    · subst hzx
      simp
    · rw [if_neg (by
        intro hh
        exact hzx (blockIdx_injective hblk hh)), if_neg hzx]
  rw [hcol, Matrix.mulVec_single_one] at hv
  rw [diagHom_single, Pi.smul_apply, Pi.single_apply] at hv
  by_cases hyx : y = x
  · subst hyx
    rw [if_pos rfl, smul_eq_mul, mul_one] at hv
    rw [if_pos rfl]
    simpa using hv
  · rw [if_neg (by
      intro hh
      exact hyx (blockIdx_injective hblk hh)), smul_zero] at hv
    rw [if_neg hyx]
    simpa using hv

private theorem chainTheta_prod {m : ℕ} (k : Fin m) (hk : k.val + 1 < m) (B : Su K 2 f 3)
    {t : Fin (m + 1) → normOne (unitaryInvolution K 2 f)}
    (h : stdChainTheta (F := F) (f := f) m k hk B =
      diagHom F (unitaryInvolution K 2 f) (m + 1) t) :
    t (Fin.castSucc k) * t (k.succ) * t ((⟨k.val + 1, hk⟩ : Fin m).succ) = 1 := by
  have hblk : k.val + 3 ≤ m + 1 := by omega
  have hent := fun y x => chainTheta_entries (F := F) (f := f) k hk B h y x
  have hMdiag : ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      Matrix.diagonal (fun x : Fin 3 =>
        (((t (blockIdx k.val hblk x) : normOne (unitaryInvolution K 2 f)) : Kˣ) : K)) := by
    ext y x
    rw [hent y x, Matrix.diagonal_apply]
    by_cases hyx : y = x <;> simp [hyx]
  have hdet : (((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)).det = 1 := B.2.1
  rw [hMdiag, Matrix.det_diagonal, Fin.prod_univ_three] at hdet
  have h0 : blockIdx k.val hblk (0 : Fin 3) = Fin.castSucc k := Fin.ext (by simp [blockIdx])
  have h1 : blockIdx k.val hblk (1 : Fin 3) = k.succ := Fin.ext (by simp [blockIdx])
  have h2 : blockIdx k.val hblk (2 : Fin 3) =
      ((⟨k.val + 1, hk⟩ : Fin m).succ : Fin (m + 1)) := Fin.ext (by simp [blockIdx])
  rw [h0, h1, h2] at hdet
  refine Subtype.ext (Units.ext ?_)
  simpa [Subgroup.coe_mul, Units.val_mul] using hdet

private theorem exists_chainTheta_nodeTor_mul (E : QuadExt F K (unitaryInvolution K 2 f))
    {m : ℕ} (hm : 3 ≤ m) (k : Fin m) (hk : k.val + 1 < m) (B : Su K 2 f 3)
    {t : Fin (m + 1) → normOne (unitaryInvolution K 2 f)}
    (h : stdChainTheta (F := F) (f := f) m k hk B =
      diagHom F (unitaryInvolution K 2 f) (m + 1) t) :
    ∃ u v : normOne (unitaryInvolution K 2 f),
      (stdFamilyV E m hm).nodeTor (Fin.castSucc k) u *
        (stdFamilyV E m hm).nodeTor (Fin.castSucc (⟨k.val + 1, hk⟩ : Fin m)) v =
        diagHom F (unitaryInvolution K 2 f) (m + 1) t := by
  have hoff : ∀ c : Fin (m + 1), ¬ (k.val ≤ c.val ∧ c.val < k.val + 3) → t c = 1 := by
    intro c hc
    have hs := stdChainTheta_single_of_not_mem (F := F) (f := f) k hk B hc
    rw [h] at hs
    exact eq_one_of_diagHom_single rfl hs
  have hkey1 : (Fin.castSucc (⟨k.val + 1, hk⟩ : Fin m) : Fin (m + 1)) = k.succ :=
    Fin.ext rfl
  have hc2 : ((⟨k.val + 1, hk⟩ : Fin m).succ : Fin (m + 1)) =
      (⟨k.val + 2, by omega⟩ : Fin (m + 1)) := Fin.ext rfl
  have hprod := chainTheta_prod (F := F) (f := f) k hk B h
  rw [hc2] at hprod
  have hlast : t (⟨k.val + 2, by omega⟩ : Fin (m + 1)) =
      (t (Fin.castSucc k) * t (k.succ))⁻¹ := eq_inv_of_mul_eq_one_right hprod
  have e01 : (Fin.castSucc k : Fin (m + 1)) ≠ k.succ := Fin.castSucc_lt_succ.ne
  have e02 : (Fin.castSucc k : Fin (m + 1)) ≠ (⟨k.val + 2, by omega⟩ : Fin (m + 1)) := by
    intro hh
    have := congrArg Fin.val hh
    simp only [Fin.val_castSucc] at this
    omega
  have e12 : (k.succ : Fin (m + 1)) ≠ (⟨k.val + 2, by omega⟩ : Fin (m + 1)) := by
    intro hh
    have := congrArg Fin.val hh
    simp only [Fin.val_succ] at this
    omega
  have ht_eq : t = (Pi.mulSingle (Fin.castSucc k) (t (Fin.castSucc k)) *
        Pi.mulSingle k.succ (t (Fin.castSucc k))⁻¹) *
      (Pi.mulSingle k.succ (t (Fin.castSucc k) * t k.succ) *
        Pi.mulSingle (⟨k.val + 2, by omega⟩ : Fin (m + 1))
          (t (Fin.castSucc k) * t k.succ)⁻¹) := by
    funext c
    rw [Pi.mul_apply, Pi.mul_apply, Pi.mul_apply, Pi.mulSingle_apply, Pi.mulSingle_apply,
      Pi.mulSingle_apply, Pi.mulSingle_apply]
    by_cases e0 : c = Fin.castSucc k
    · subst e0
      rw [if_pos rfl, if_neg e01, if_neg e01, if_neg e02]
      simp
    · by_cases e1 : c = k.succ
      · subst e1
        rw [if_neg (Ne.symm e01), if_pos rfl, if_pos rfl, if_neg e12]
        simp [inv_mul_cancel_left]
      · by_cases e2 : c = (⟨k.val + 2, by omega⟩ : Fin (m + 1))
        · subst e2
          rw [if_neg (Ne.symm e02), if_neg (Ne.symm e12), if_neg (Ne.symm e12), if_pos rfl]
          simp [hlast]
        · have hc : ¬ (k.val ≤ c.val ∧ c.val < k.val + 3) := by
            rintro ⟨h1, h2⟩
            have hcases : c.val = k.val ∨ c.val = k.val + 1 ∨ c.val = k.val + 2 := by omega
            rcases hcases with h | h | h
            · exact e0 (Fin.ext (by simpa using h))
            · exact e1 (Fin.ext (by simpa using h))
            · exact e2 (Fin.ext (by simpa using h))
          rw [if_neg e0, if_neg e1, if_neg e1, if_neg e2]
          simpa using hoff c hc
  refine ⟨t (Fin.castSucc k), t (Fin.castSucc k) * t (k.succ), ?_⟩
  rw [stdFamilyV_nodeTor_castSucc, stdFamilyV_nodeTor_castSucc, hkey1, hc2,
    ← MonoidHom.map_mul, ← ht_eq]

private theorem exists_forkTheta_nodeTor_mul (E : QuadExt F K (unitaryInvolution K 2 f))
    {m : ℕ} (hm : 3 ≤ m) (B : Su K 2 f 3)
    {t : Fin (m + 1) → normOne (unitaryInvolution K 2 f)}
    (h : stdForkTheta E m hm B = diagHom F (unitaryInvolution K 2 f) (m + 1) t) :
    ∃ u v : normOne (unitaryInvolution K 2 f),
      (stdFamilyV E m hm).nodeTor (Fin.castSucc (⟨m - 2, by omega⟩ : Fin m)) u *
        (stdFamilyV E m hm).nodeTor (Fin.last m) v =
        diagHom F (unitaryInvolution K 2 f) (m + 1) t := by
  have hchain : stdChainTheta (F := F) (f := f) m ⟨m - 2, by omega⟩
        (by show m - 2 + 1 < m; omega) B =
      diagHom F (unitaryInvolution K 2 f) (m + 1)
        (Function.update t (Fin.last m) ((t (Fin.last m))⁻¹)) := by
    have h2 : (stdConj E m).toMonoidHom
          ((stdConj E m).toMonoidHom (stdChainTheta (F := F) (f := f) m
            ⟨m - 2, by omega⟩ (by omega : m - 2 + 1 < m) B)) =
        (stdConj E m).toMonoidHom (diagHom F (unitaryInvolution K 2 f) (m + 1) t) :=
      congrArg (stdConj E m).toMonoidHom h
    change stdConj E m (stdConj E m (stdChainTheta (F := F) (f := f) m
        ⟨m - 2, by omega⟩ (by omega : m - 2 + 1 < m) B)) =
      stdConj E m (diagHom F (unitaryInvolution K 2 f) (m + 1) t) at h2
    rw [stdConj_stdConj] at h2
    change stdChainTheta (F := F) (f := f) m ⟨m - 2, by omega⟩
        (by omega : m - 2 + 1 < m) B =
      (stdConj E m).toMonoidHom (diagHom F (unitaryInvolution K 2 f) (m + 1) t) at h2
    rw [stdConj_diagHom] at h2
    exact h2
  obtain ⟨u, v, huv⟩ := exists_chainTheta_nodeTor_mul E hm ⟨m - 2, by omega⟩
    (by omega : m - 2 + 1 < m) B hchain
  refine ⟨u, v, ?_⟩
  have hfix1 : (stdConj E m).toMonoidHom
        ((stdFamilyV E m hm).nodeTor (Fin.castSucc (⟨m - 2, by omega⟩ : Fin m)) u) =
      (stdFamilyV E m hm).nodeTor (Fin.castSucc (⟨m - 2, by omega⟩ : Fin m)) u := by
    rw [PhanFamilyE.nodeTor, MonoidHom.comp_apply, stdFamilyV_ι_castSucc]
    exact stdConj_chainIota E m ⟨m - 2, by omega⟩ (by show m - 2 + 1 < m; omega)
      (torusTwo (unitaryInvolution K 2 f) u)
  have hfix2 : (stdConj E m).toMonoidHom
        ((stdFamilyV E m hm).nodeTor (Fin.castSucc (⟨m - 1, by omega⟩ : Fin m)) v) =
      (stdFamilyV E m hm).nodeTor (Fin.last m) v := by
    rw [PhanFamilyE.nodeTor, MonoidHom.comp_apply, stdFamilyV_ι_castSucc,
      PhanFamilyE.nodeTor, MonoidHom.comp_apply, stdFamilyV_ι_last]
    rw [stdForkIota]
    rfl
  have hidx : (⟨(⟨m - 2, by omega⟩ : Fin m).val + 1,
      by show m - 2 + 1 < m; omega⟩ : Fin m) =
      (⟨m - 1, by omega⟩ : Fin m) := by
    apply Fin.ext
    show (⟨m - 2, by omega⟩ : Fin m).val + 1 = m - 1
    have h : (⟨m - 2, by omega⟩ : Fin m).val = m - 2 := rfl
    omega
  have hc := congrArg (stdConj E m).toMonoidHom huv
  rw [map_mul, hidx, hfix1, hfix2, stdConj_diagHom_update] at hc
  exact hc

private theorem ggCoxeterMatrixD_simplyLaced {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    CFSG.StandardType.ggCoxeterMatrixD n i j = 2 ∨
      CFSG.StandardType.ggCoxeterMatrixD n i j = 3 := by
  rw [CFSG.StandardType.ggCoxeterMatrixD_apply, if_neg hij]
  split_ifs <;> simp

private theorem sq_eq_sq_normOne (hK : Nat.card K = (2 ^ f) ^ 2)
    {x y : normOne (unitaryInvolution K 2 f)}
    (h : x * x = y * y) : x = y := by
  have h1 : (x * y⁻¹) * (x * y⁻¹) = 1 := by
    calc (x * y⁻¹) * (x * y⁻¹) = (x * x) * (y⁻¹ * y⁻¹) := by rw [mul_mul_mul_comm]
      _ = (x * x) * (y * y)⁻¹ := by rw [← mul_inv]
      _ = 1 := by rw [h, mul_inv_cancel]
  have h2 : x * y⁻¹ = 1 := eq_one_of_mul_self_eq_one_normOne hK h1
  exact mul_inv_eq_one.mp h2

private theorem exists_mul_self_normOne (hK : Nat.card K = (2 ^ f) ^ 2)
    (w : normOne (unitaryInvolution K 2 f)) :
    ∃ z : normOne (unitaryInvolution K 2 f), z * z = w := by
  have hinj : Function.Injective (fun z : normOne (unitaryInvolution K 2 f) => z * z) :=
    fun x y h => sq_eq_sq_normOne hK h
  exact Finite.surjective_of_injective hinj w

private theorem exists_mul_inv_mul_normOne (hK : Nat.card K = (2 ^ f) ^ 2)
    (s r : normOne (unitaryInvolution K 2 f)) :
    ∃ u v : normOne (unitaryInvolution K 2 f), u * v = s ∧ u⁻¹ * v = r := by
  obtain ⟨v, hv⟩ := exists_mul_self_normOne hK (s * r)
  obtain ⟨u, hu⟩ := exists_mul_self_normOne hK (s * r⁻¹)
  have h1 : (u * v) * (u * v) = s * s := by
    calc (u * v) * (u * v) = (u * u) * (v * v) := by rw [mul_mul_mul_comm]
      _ = (s * r⁻¹) * (s * r) := by rw [hu, hv]
      _ = s * s := by
          rw [mul_mul_mul_comm, inv_mul_cancel, mul_one]
  have h2 : (u⁻¹ * v) * (u⁻¹ * v) = r * r := by
    calc (u⁻¹ * v) * (u⁻¹ * v) = (u⁻¹ * u⁻¹) * (v * v) := by rw [mul_mul_mul_comm]
      _ = ((s * r⁻¹)⁻¹) * (s * r) := by rw [← mul_inv, hu, hv]
      _ = r * r := by
          rw [mul_inv, inv_inv, mul_mul_mul_comm, inv_mul_cancel, one_mul]
  exact ⟨u, v, sq_eq_sq_normOne hK h1, sq_eq_sq_normOne hK h2⟩

private theorem single_inf_torus_le (m : ℕ) (hm : 3 ≤ m) (hK : Nat.card K = (2 ^ f) ^ 2)
    (i : Fin (m + 1)) :
    ((stdFamilyV E m hm).ι i).range ⊓ (stdFamilyV E m hm).torus ≤
      ((stdFamilyV E m hm).nodeTor i).range := by
  rintro g ⟨⟨a, rfl⟩, hgT⟩
  rw [torus_stdFamilyV E m hm hK] at hgT
  obtain ⟨t, ht⟩ := hgT
  rcases Fin.eq_castSucc_or_eq_last (n := m) i with ⟨k, rfl⟩ | rfl
  · have h' : stdChainIota (F := F) (f := f) m k a =
        diagHom F (unitaryInvolution K 2 f) (m + 1) t := by
      rw [← stdFamilyV_ι_castSucc]
      exact ht.symm
    obtain ⟨u, hu⟩ := exists_chainIota_torusTwo_of_diag E hm k a h'
    refine ⟨u, ?_⟩
    rw [PhanFamilyE.nodeTor, MonoidHom.comp_apply, stdFamilyV_ι_castSucc, hu]
    exact h'.symm
  · have h' : stdForkIota E m hm a =
        diagHom F (unitaryInvolution K 2 f) (m + 1) t := by
      rw [← stdFamilyV_ι_last]
      exact ht.symm
    obtain ⟨u, hu⟩ := exists_forkIota_torusTwo_of_diag (E := E) hm a h'
    refine ⟨u, ?_⟩
    rw [PhanFamilyE.nodeTor, MonoidHom.comp_apply, stdFamilyV_ι_last, hu]
    exact h'.symm

private theorem eq_diagHom_of_mul_of_fix {m : ℕ} {x g h : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)}
    {t : Fin (m + 1) → normOne (unitaryInvolution K 2 f)}
    (hx : x = diagHom F (unitaryInvolution K 2 f) (m + 1) t) (hxgh : x = g * h)
    (hlin : ∀ (c : K) (v : Fin (m + 1) → K), g (c • v) = c • g v)
    {S : Fin (m + 1) → Prop} [DecidablePred S]
    (hS : ∀ c, S c → h (Pi.single c (1 : K)) = Pi.single c (1 : K))
    (hSc : ∀ c, ¬ S c → g (Pi.single c (1 : K)) = Pi.single c (1 : K)) :
    g = diagHom F (unitaryInvolution K 2 f) (m + 1) (fun c => if S c then t c else 1) := by
  refine eq_diagHom_of_forall_single (fun c v => hlin c v) (fun c => ?_)
  by_cases hc : S c
  · rw [if_pos hc]
    have hstep : g (Pi.single c (1 : K)) =
        (diagHom F (unitaryInvolution K 2 f) (m + 1) t) (Pi.single c (1 : K)) := by
      calc g (Pi.single c (1 : K)) = g (h (Pi.single c (1 : K))) := by rw [hS c hc]
        _ = (g * h) (Pi.single c (1 : K)) := rfl
        _ = x (Pi.single c (1 : K)) := by rw [hxgh]
        _ = (diagHom F (unitaryInvolution K 2 f) (m + 1) t) (Pi.single c (1 : K)) := by rw [hx]
    rw [hstep, diagHom_single]
  · rw [if_neg hc]
    simpa using hSc c hc

private theorem chain_chain_diag_exists {m : ℕ} {k l : Fin m}
    (hk : k.val + 1 < l.val ∨ l.val + 1 < k.val) {a b : Su K 2 f 2}
    {t : Fin (m + 1) → normOne (unitaryInvolution K 2 f)}
    (hgx : diagHom F (unitaryInvolution K 2 f) (m + 1) t =
      stdChainIota (F := F) (f := f) m k a * stdChainIota (F := F) (f := f) m l b) :
    (∃ t1 : Fin (m + 1) → normOne (unitaryInvolution K 2 f),
        stdChainIota (F := F) (f := f) m k a =
          diagHom F (unitaryInvolution K 2 f) (m + 1) t1) ∧
      ∃ t2 : Fin (m + 1) → normOne (unitaryInvolution K 2 f),
        stdChainIota (F := F) (f := f) m l b =
          diagHom F (unitaryInvolution K 2 f) (m + 1) t2 := by
  have hcomm : stdChainIota (F := F) (f := f) m k a * stdChainIota (F := F) (f := f) m l b =
      stdChainIota (F := F) (f := f) m l b * stdChainIota (F := F) (f := f) m k a := by
    rcases hk with h | h
    · exact chainIota_mul_comm m k l h a b
    · exact (chainIota_mul_comm m l k h b a).symm
  have hkval : k.val ≠ l.val := by
    rcases hk with h | h <;> omega
  have hfix1 : ∀ c : Fin (m + 1), ¬ (c.val = k.val ∨ c.val = k.val + 1) →
      stdChainIota (F := F) (f := f) m k a (Pi.single c (1 : K)) = Pi.single c (1 : K) :=
    fun c hc => stdChainIota_single_of_not_mem k a (by omega) (by omega)
  have hfix2 : ∀ c : Fin (m + 1), ¬ (c.val = l.val ∨ c.val = l.val + 1) →
      stdChainIota (F := F) (f := f) m l b (Pi.single c (1 : K)) = Pi.single c (1 : K) :=
    fun c hc => stdChainIota_single_of_not_mem l b (by omega) (by omega)
  have hfix2' : ∀ c : Fin (m + 1), c.val = k.val ∨ c.val = k.val + 1 →
      stdChainIota (F := F) (f := f) m l b (Pi.single c (1 : K)) = Pi.single c (1 : K) :=
    fun c hc => stdChainIota_single_of_not_mem l b
      (by rcases hc with h | h <;> omega) (by rcases hc with h | h <;> omega)
  have hfix1' : ∀ c : Fin (m + 1), c.val = l.val ∨ c.val = l.val + 1 →
      stdChainIota (F := F) (f := f) m k a (Pi.single c (1 : K)) = Pi.single c (1 : K) :=
    fun c hc => stdChainIota_single_of_not_mem k a
      (by rcases hc with h | h <;> omega) (by rcases hc with h | h <;> omega)
  constructor
  · refine ⟨fun c => if c.val = k.val ∨ c.val = k.val + 1 then t c else 1, ?_⟩
    exact eq_diagHom_of_mul_of_fix (F := F) (K := K)
      (S := fun c => c.val = k.val ∨ c.val = k.val + 1) rfl hgx
      (fun c v => stdChainIota_smul k a c v) hfix2' hfix1
  · refine ⟨fun c => if c.val = l.val ∨ c.val = l.val + 1 then t c else 1, ?_⟩
    exact eq_diagHom_of_mul_of_fix (F := F) (K := K)
      (S := fun c => c.val = l.val ∨ c.val = l.val + 1) rfl (hgx.trans hcomm)
      (fun c v => stdChainIota_smul l b c v) hfix1' hfix2

private theorem pair_chain_chain_inf_torus_le (m : ℕ) (hm : 3 ≤ m)
    (hK : Nat.card K = (2 ^ f) ^ 2) {k l : Fin m}
    (hM : CFSG.StandardType.ggCoxeterMatrixD (m + 1) (Fin.castSucc k) (Fin.castSucc l) = 2) :
    (((stdFamilyV E m hm).ι (Fin.castSucc k)).range ⊔
        ((stdFamilyV E m hm).ι (Fin.castSucc l)).range) ⊓ (stdFamilyV E m hm).torus ≤
      ((stdFamilyV E m hm).nodeTor (Fin.castSucc k)).range ⊔
        ((stdFamilyV E m hm).nodeTor (Fin.castSucc l)).range := by
  have hn := (ggCoxeterMatrixD_eq_two_iff (by omega : 4 ≤ m + 1) (Fin.castSucc k)
    (Fin.castSucc l)).1 hM
  obtain ⟨hkl, hne, hne'⟩ := hn
  have hklv : k.val ≠ l.val := fun h => hkl (Fin.ext h)
  have hk1 : k.val + 1 ≠ l.val := by
    intro h
    exact hne (by
      rw [edgeD_iff_of_four_le (by omega)]
      exact Or.inl ⟨by simpa using h, by simp only [Fin.val_castSucc]; omega⟩)
  have hl1 : l.val + 1 ≠ k.val := by
    intro h
    exact hne' (by
      rw [edgeD_iff_of_four_le (by omega)]
      exact Or.inl ⟨by simpa using h, by simp only [Fin.val_castSucc]; omega⟩)
  have hlt : k.val + 1 < l.val ∨ l.val + 1 < k.val := by omega
  have hcomm : ∀ a ∈ ((stdFamilyV E m hm).ι (Fin.castSucc k)).range,
      ∀ b ∈ ((stdFamilyV E m hm).ι (Fin.castSucc l)).range, a * b = b * a := by
    rintro a ⟨a', rfl⟩ b ⟨b', rfl⟩
    rw [stdFamilyV_ι_castSucc, stdFamilyV_ι_castSucc]
    rcases hlt with h | h
    · exact chainIota_mul_comm m k l h a' b'
    · exact (chainIota_mul_comm m l k h b' a').symm
  rintro g ⟨hgsup, hgT⟩
  rw [torus_stdFamilyV E m hm hK] at hgT
  obtain ⟨t, ht⟩ := hgT
  obtain ⟨g1, hg1, g2, hg2, hgx⟩ :=
    CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hcomm hgsup
  obtain ⟨a, rfl⟩ := hg1
  obtain ⟨b, rfl⟩ := hg2
  rw [stdFamilyV_ι_castSucc, stdFamilyV_ι_castSucc] at hgx
  have hgx'' : diagHom F (unitaryInvolution K 2 f) (m + 1) t =
      stdChainIota (F := F) (f := f) m k a * stdChainIota (F := F) (f := f) m l b := by
    rw [hgx, ht]
  obtain ⟨⟨t1, ht1⟩, ⟨t2, ht2⟩⟩ := chain_chain_diag_exists (F := F) (f := f) hlt hgx''
  have hmem1 : (stdFamilyV E m hm).ι (Fin.castSucc k) a ∈
      ((stdFamilyV E m hm).nodeTor (Fin.castSucc k)).range := by
    refine single_inf_torus_le (E := E) m hm hK (Fin.castSucc k) ⟨?_, ?_⟩
    · rw [stdFamilyV_ι_castSucc]
      exact ⟨a, rfl⟩
    · rw [torus_stdFamilyV E m hm hK, stdFamilyV_ι_castSucc]
      exact ⟨t1, ht1.symm⟩
  have hmem2 : (stdFamilyV E m hm).ι (Fin.castSucc l) b ∈
      ((stdFamilyV E m hm).nodeTor (Fin.castSucc l)).range := by
    refine single_inf_torus_le (E := E) m hm hK (Fin.castSucc l) ⟨?_, ?_⟩
    · rw [stdFamilyV_ι_castSucc]
      exact ⟨b, rfl⟩
    · rw [torus_stdFamilyV E m hm hK, stdFamilyV_ι_castSucc]
      exact ⟨t2, ht2.symm⟩
  rw [← hgx]
  rw [stdFamilyV_ι_castSucc] at hmem1
  rw [stdFamilyV_ι_castSucc] at hmem2
  exact Subgroup.mul_mem_sup hmem1 hmem2

private theorem pair_chain_fork_inf_torus_le (m : ℕ) (hm : 3 ≤ m)
    (hK : Nat.card K = (2 ^ f) ^ 2) {k : Fin m} (hk : k.val ≤ m - 3) :
    (((stdFamilyV E m hm).ι (Fin.castSucc k)).range ⊔
        ((stdFamilyV E m hm).ι (Fin.last m)).range) ⊓ (stdFamilyV E m hm).torus ≤
      ((stdFamilyV E m hm).nodeTor (Fin.castSucc k)).range ⊔
        ((stdFamilyV E m hm).nodeTor (Fin.last m)).range := by
  have hcomm : ∀ a ∈ ((stdFamilyV E m hm).ι (Fin.castSucc k)).range,
      ∀ b ∈ ((stdFamilyV E m hm).ι (Fin.last m)).range, a * b = b * a := by
    rintro a ⟨a', rfl⟩ b ⟨b', rfl⟩
    rw [stdFamilyV_ι_castSucc, stdFamilyV_ι_last]
    exact chainIota_comm_fork E m hm k (by show k.val + 1 < m - 1; omega) a' b'
  rintro g ⟨hgsup, hgT⟩
  rw [torus_stdFamilyV E m hm hK] at hgT
  obtain ⟨t, ht⟩ := hgT
  obtain ⟨g1, hg1, g2, hg2, hgx⟩ :=
    CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hcomm hgsup
  obtain ⟨a, rfl⟩ := hg1
  obtain ⟨b, rfl⟩ := hg2
  rw [stdFamilyV_ι_castSucc, stdFamilyV_ι_last] at hgx
  have hgx'' : diagHom F (unitaryInvolution K 2 f) (m + 1) t =
      stdChainIota (F := F) (f := f) m k a * stdForkIota E m hm b := by
    rw [hgx, ht]
  have hc1 : (stdConj E m).toMonoidHom (stdChainIota (F := F) (f := f) m k a) =
      stdChainIota (F := F) (f := f) m k a :=
    stdConj_chainIota E m k (by show k.val + 1 < m; omega) a
  have hc2 : (stdConj E m).toMonoidHom (stdForkIota E m hm b) =
      stdChainIota (F := F) (f := f) m ⟨m - 1, by omega⟩ b := by
    rw [stdForkIota]
    exact stdConj_stdConj (E := E) m _
  have hx' : diagHom F (unitaryInvolution K 2 f) (m + 1)
        (Function.update t (Fin.last m) ((t (Fin.last m))⁻¹)) =
      stdChainIota (F := F) (f := f) m k a *
        stdChainIota (F := F) (f := f) m ⟨m - 1, by omega⟩ b := by
    have hh := congrArg (stdConj E m).toMonoidHom hgx''
    rw [map_mul, stdConj_diagHom, hc1, hc2] at hh
    exact hh
  obtain ⟨⟨t1, ht1⟩, ⟨t2, ht2⟩⟩ := chain_chain_diag_exists (F := F) (f := f)
    (l := ⟨m - 1, by omega⟩) (Or.inl (by show k.val + 1 < m - 1; omega)) hx'
  have hg2diag : ∃ t3 : Fin (m + 1) → normOne (unitaryInvolution K 2 f),
      stdForkIota E m hm b = diagHom F (unitaryInvolution K 2 f) (m + 1) t3 := by
    refine ⟨Function.update t2 (Fin.last m) ((t2 (Fin.last m))⁻¹), ?_⟩
    have h1 : stdForkIota E m hm b =
        (stdConj E m).toMonoidHom ((stdConj E m).toMonoidHom (stdForkIota E m hm b)) :=
      (stdConj_stdConj (E := E) m _).symm
    rw [h1, hc2, ht2]
    exact stdConj_diagHom (E := E) m t2
  obtain ⟨t3, ht3⟩ := hg2diag
  have hmem1 : (stdFamilyV E m hm).ι (Fin.castSucc k) a ∈
      ((stdFamilyV E m hm).nodeTor (Fin.castSucc k)).range := by
    refine single_inf_torus_le (E := E) m hm hK (Fin.castSucc k) ⟨?_, ?_⟩
    · rw [stdFamilyV_ι_castSucc]
      exact ⟨a, rfl⟩
    · rw [torus_stdFamilyV E m hm hK, stdFamilyV_ι_castSucc]
      exact ⟨t1, ht1.symm⟩
  have hmem2 : (stdFamilyV E m hm).ι (Fin.last m) b ∈
      ((stdFamilyV E m hm).nodeTor (Fin.last m)).range := by
    refine single_inf_torus_le (E := E) m hm hK (Fin.last m) ⟨?_, ?_⟩
    · rw [stdFamilyV_ι_last]
      exact ⟨b, rfl⟩
    · rw [torus_stdFamilyV E m hm hK, stdFamilyV_ι_last]
      exact ⟨t3, ht3.symm⟩
  rw [← hgx]
  rw [stdFamilyV_ι_castSucc] at hmem1
  rw [stdFamilyV_ι_last] at hmem2
  exact Subgroup.mul_mem_sup hmem1 hmem2



private theorem pair_fork_fork_inf_torus_le (m : ℕ) (hm : 3 ≤ m)
    (hK : Nat.card K = (2 ^ f) ^ 2) :
    (((stdFamilyV E m hm).ι (Fin.castSucc (⟨m - 1, by omega⟩ : Fin m))).range ⊔
        ((stdFamilyV E m hm).ι (Fin.last m)).range) ⊓ (stdFamilyV E m hm).torus ≤
      ((stdFamilyV E m hm).nodeTor (Fin.castSucc (⟨m - 1, by omega⟩ : Fin m))).range ⊔
        ((stdFamilyV E m hm).nodeTor (Fin.last m)).range := by
  have hcomm : ∀ a ∈ ((stdFamilyV E m hm).ι
        (Fin.castSucc (⟨m - 1, by omega⟩ : Fin m))).range,
      ∀ b ∈ ((stdFamilyV E m hm).ι (Fin.last m)).range, a * b = b * a := by
    rintro a ⟨a', rfl⟩ b ⟨b', rfl⟩
    rw [stdFamilyV_ι_castSucc, stdFamilyV_ι_last]
    exact (suEndN_blockEmb2_last_comm E m hm a' b').eq
  rintro g ⟨hgsup, hgT⟩
  rw [torus_stdFamilyV E m hm hK] at hgT
  obtain ⟨t, ht⟩ := hgT
  obtain ⟨g1, hg1, g2, hg2, hgx⟩ :=
    CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hcomm hgsup
  obtain ⟨a, rfl⟩ := hg1
  obtain ⟨b, rfl⟩ := hg2
  rw [stdFamilyV_ι_castSucc, stdFamilyV_ι_last] at hgx
  have hgx'' : diagHom F (unitaryInvolution K 2 f) (m + 1) t =
      stdChainIota (F := F) (f := f) m ⟨m - 1, by omega⟩ a * stdForkIota E m hm b := by
    rw [hgx, ht]
  have hkval : (⟨m - 1, by omega⟩ : Fin m).val = m - 1 := rfl
  have hne : (⟨m - 1, by omega⟩ : Fin (m + 1)) ≠ Fin.last m := by
    intro hh
    have := congrArg Fin.val hh
    simp only [Fin.val_last] at this
    omega
  have hoff : ∀ c : Fin (m + 1), c.val ≠ m - 1 → c.val ≠ m → t c = 1 := by
    intro c h1 h2
    have hfix : (stdChainIota (F := F) (f := f) m ⟨m - 1, by omega⟩ a *
        stdForkIota E m hm b) (Pi.single c (1 : K)) = Pi.single c (1 : K) := by
      rw [LinearEquiv.mul_apply, stdForkIota_single_of_not_mem E hm b h1 h2]
      exact stdChainIota_single_of_not_mem (⟨m - 1, by omega⟩ : Fin m) a
        (by rw [hkval]; exact h1)
        (by rw [hkval]; omega)
    rw [← hgx''] at hfix
    exact eq_one_of_diagHom_single rfl hfix
  obtain ⟨u, v, huv1, huv2⟩ :=
    exists_mul_inv_mul_normOne hK (t ⟨m - 1, by omega⟩) (t (Fin.last m))
  have htup : (Pi.mulSingle (Fin.castSucc (⟨m - 1, by omega⟩ : Fin m)) u *
        Pi.mulSingle ((⟨m - 1, by omega⟩ : Fin m).succ) u⁻¹) *
        (Pi.mulSingle (⟨m - 1, by omega⟩ : Fin (m + 1)) v *
          Pi.mulSingle (Fin.last m) v) = t := by
    have e0 : (Fin.castSucc (⟨m - 1, by omega⟩ : Fin m) : Fin (m + 1)) =
        (⟨m - 1, by omega⟩ : Fin (m + 1)) := Fin.ext rfl
    have e1 : ((⟨m - 1, by omega⟩ : Fin m).succ : Fin (m + 1)) = Fin.last m := by
      apply Fin.ext
      rw [Fin.val_succ, hkval, Fin.val_last]
      omega
    rw [e0, e1]
    funext c
    rw [Pi.mul_apply, Pi.mul_apply, Pi.mul_apply, Pi.mulSingle_apply, Pi.mulSingle_apply,
      Pi.mulSingle_apply, Pi.mulSingle_apply]
    by_cases h0 : c = (⟨m - 1, by omega⟩ : Fin (m + 1))
    · subst h0
      rw [if_pos rfl, if_neg hne, if_pos rfl, if_neg hne]
      simpa using huv1
    · by_cases h1 : c = Fin.last m
      · subst h1
        rw [if_neg (Ne.symm hne), if_pos rfl, if_neg (Ne.symm hne), if_pos rfl]
        simpa using huv2
      · rw [if_neg h0, if_neg h1, if_neg h0, if_neg h1]
        have h1' : c.val ≠ m - 1 := fun h => h0 (Fin.ext (by simpa using h))
        have h2' : c.val ≠ m := fun h => h1 (Fin.ext (by simpa using h))
        simpa using (hoff c h1' h2').symm
  have hnt1 := stdFamilyV_nodeTor_castSucc E m hm (⟨m - 1, by omega⟩ : Fin m) u
  have hnt2 := stdFamilyV_nodeTor_last E m hm v
  have hprod : (stdFamilyV E m hm).nodeTor (Fin.castSucc (⟨m - 1, by omega⟩ : Fin m)) u *
      (stdFamilyV E m hm).nodeTor (Fin.last m) v =
      diagHom F (unitaryInvolution K 2 f) (m + 1) t := by
    rw [hnt1, hnt2, ← MonoidHom.map_mul, ← htup]
  rw [← ht, ← hprod]
  exact Subgroup.mul_mem_sup ⟨u, rfl⟩ ⟨v, rfl⟩


private theorem pair_adjacent_inf_torus_le (m : ℕ) (hm : 3 ≤ m)
    (hK : Nat.card K = (2 ^ f) ^ 2) {i j : Fin (m + 1)} (hlt : i < j)
    (hM : CFSG.StandardType.ggCoxeterMatrixD (m + 1) i j = 3) :
    (((stdFamilyV E m hm).ι i).range ⊔ ((stdFamilyV E m hm).ι j).range) ⊓
        (stdFamilyV E m hm).torus ≤
      ((stdFamilyV E m hm).nodeTor i).range ⊔ ((stdFamilyV E m hm).nodeTor j).range := by
  have hE : edgeD (m + 1) i j := by
    rcases (ggCoxeterMatrixD_eq_three_iff (by omega : 4 ≤ m + 1) i j).1 hM with h | h
    · exact h
    · exact absurd (edgeD_lt_of (by omega) h) (not_lt.mpr (le_of_lt hlt))
  have hle : ((stdFamilyV E m hm).ι i).range ⊔ ((stdFamilyV E m hm).ι j).range ≤
      ((stdFamilyV E m hm).θ i j).range := by
    refine sup_le ?_ ?_
    · rw [← (stdFamilyV E m hm).left i j hlt hM, MonoidHom.range_comp]
      exact Subgroup.map_le_range _ _
    · rw [← (stdFamilyV E m hm).right i j hlt hM, MonoidHom.range_comp]
      exact Subgroup.map_le_range _ _
  rintro g ⟨hgsup, hgT⟩
  have hgθ : g ∈ ((stdFamilyV E m hm).θ i j).range := hle hgsup
  rw [torus_stdFamilyV E m hm hK] at hgT
  obtain ⟨t, ht⟩ := hgT
  obtain ⟨B, hB⟩ := hgθ
  rcases Fin.eq_castSucc_or_eq_last (n := m) j with ⟨j', rfl⟩ | rfl
  · rw [edgeD_iff_of_four_le (by omega : 4 ≤ m + 1)] at hE
    rcases hE with ⟨h1, h2⟩ | ⟨h1, h2⟩
    ·
      have hilt : i.val < m := by omega
      have hi : i = Fin.castSucc (⟨i.val, hilt⟩ : Fin m) := Fin.ext rfl
      have hj : j' = (⟨i.val + 1, by omega⟩ : Fin m) := Fin.ext (by simpa using h1.symm)
      rw [hi, hj] at hB ⊢
      have hθ : (stdFamilyV E m hm).θ (Fin.castSucc (⟨i.val, hilt⟩ : Fin m))
          (Fin.castSucc (⟨i.val + 1, by omega⟩ : Fin m)) =
          stdChainTheta (F := F) (f := f) m ⟨i.val, hilt⟩ (by show i.val + 1 < m; omega) := by
        rw [stdFamilyV_θ, stdTheta_castSucc]
        exact stdThetaAt_eq_chainTheta (F := F) (f := f) (m := m)
          (i := Fin.castSucc (⟨i.val, hilt⟩ : Fin m)) (j' := ⟨i.val + 1, by omega⟩)
          (by simp) hilt
      have hchain : stdChainTheta (F := F) (f := f) m ⟨i.val, hilt⟩
          (by show i.val + 1 < m; omega) B =
          diagHom F (unitaryInvolution K 2 f) (m + 1) t := by
        rw [← hθ, hB]
        exact ht.symm
      obtain ⟨u, v, huv⟩ := exists_chainTheta_nodeTor_mul E hm ⟨i.val, hilt⟩
        (by show i.val + 1 < m; omega) B hchain
      rw [← ht, ← huv]
      exact Subgroup.mul_mem_sup ⟨u, rfl⟩ ⟨v, rfl⟩
    ·
      simp only [Fin.val_castSucc] at h2
      omega
  · rw [edgeD_iff_of_four_le (by omega : 4 ≤ m + 1)] at hE
    rcases hE with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp only [Fin.val_last] at h2
      omega
    ·
      have hi : i = (⟨m - 2, by omega⟩ : Fin (m + 1)) := Fin.ext (by simpa using h1)
      rw [hi] at hB ⊢
      have hθ : (stdFamilyV E m hm).θ (⟨m - 2, by omega⟩ : Fin (m + 1)) (Fin.last m) =
          stdForkTheta E m hm := by
        rw [stdFamilyV_θ, stdTheta_last]
      have hfork : stdForkTheta E m hm B =
          diagHom F (unitaryInvolution K 2 f) (m + 1) t := by
        rw [← hθ, hB]
        exact ht.symm
      obtain ⟨u, v, huv⟩ := exists_forkTheta_nodeTor_mul E hm B hfork
      rw [← ht, ← huv]
      exact Subgroup.mul_mem_sup ⟨u, rfl⟩ ⟨v, rfl⟩

private theorem pair_chain_fork_of_two (m : ℕ) (hm : 3 ≤ m)
    (hK : Nat.card K = (2 ^ f) ^ 2) {k : Fin m}
    (hM : CFSG.StandardType.ggCoxeterMatrixD (m + 1) (Fin.castSucc k) (Fin.last m) = 2) :
    (((stdFamilyV E m hm).ι (Fin.castSucc k)).range ⊔
        ((stdFamilyV E m hm).ι (Fin.last m)).range) ⊓ (stdFamilyV E m hm).torus ≤
      ((stdFamilyV E m hm).nodeTor (Fin.castSucc k)).range ⊔
        ((stdFamilyV E m hm).nodeTor (Fin.last m)).range := by
  have hn := (ggCoxeterMatrixD_eq_two_iff (by omega : 4 ≤ m + 1) (Fin.castSucc k)
    (Fin.last m)).1 hM
  have hkm : k.val ≠ m - 2 := by
    intro h
    exact hn.2.1 (by
      rw [edgeD_iff_of_four_le (by omega)]
      exact Or.inr ⟨by simpa using h, by simp only [Fin.val_last]; omega⟩)
  by_cases hk : k.val = m - 1
  · have hkeq : k = ⟨m - 1, by omega⟩ := Fin.ext hk
    rw [hkeq]
    exact pair_fork_fork_inf_torus_le E m hm hK
  · exact pair_chain_fork_inf_torus_le E m hm hK (by have := k.isLt; omega)

private theorem pair_disjoint_inf_torus_le (m : ℕ) (hm : 3 ≤ m)
    (hK : Nat.card K = (2 ^ f) ^ 2) {i j : Fin (m + 1)} (hij : i ≠ j)
    (hM : CFSG.StandardType.ggCoxeterMatrixD (m + 1) i j = 2) :
    (((stdFamilyV E m hm).ι i).range ⊔ ((stdFamilyV E m hm).ι j).range) ⊓
        (stdFamilyV E m hm).torus ≤
      ((stdFamilyV E m hm).nodeTor i).range ⊔ ((stdFamilyV E m hm).nodeTor j).range := by
  rcases Fin.eq_castSucc_or_eq_last (n := m) i with ⟨k, rfl⟩ | rfl
  · rcases Fin.eq_castSucc_or_eq_last (n := m) j with ⟨l, rfl⟩ | rfl
    · exact pair_chain_chain_inf_torus_le E m hm hK hM
    · exact pair_chain_fork_of_two E m hm hK hM
  · rcases Fin.eq_castSucc_or_eq_last (n := m) j with ⟨l, rfl⟩ | rfl
    · have hM' : CFSG.StandardType.ggCoxeterMatrixD (m + 1) (Fin.castSucc l) (Fin.last m) = 2 := by
        rw [CoxeterMatrix.symmetric]
        exact hM
      calc (((stdFamilyV E m hm).ι (Fin.last m)).range ⊔
            ((stdFamilyV E m hm).ι (Fin.castSucc l)).range) ⊓ (stdFamilyV E m hm).torus
          = (((stdFamilyV E m hm).ι (Fin.castSucc l)).range ⊔
              ((stdFamilyV E m hm).ι (Fin.last m)).range) ⊓ (stdFamilyV E m hm).torus := by
            rw [sup_comm]
        _ ≤ ((stdFamilyV E m hm).nodeTor (Fin.castSucc l)).range ⊔
              ((stdFamilyV E m hm).nodeTor (Fin.last m)).range :=
            pair_chain_fork_of_two E m hm hK hM'
        _ = ((stdFamilyV E m hm).nodeTor (Fin.last m)).range ⊔
              ((stdFamilyV E m hm).nodeTor (Fin.castSucc l)).range := by rw [sup_comm]
    · exact absurd rfl hij

private theorem pair_inf_torus_le (m : ℕ) (hm : 3 ≤ m)
    (hK : Nat.card K = (2 ^ f) ^ 2) {i j : Fin (m + 1)} (hij : i ≠ j)
    (hM : CFSG.StandardType.ggCoxeterMatrixD (m + 1) i j = 2 ∨
      CFSG.StandardType.ggCoxeterMatrixD (m + 1) i j = 3) :
    (((stdFamilyV E m hm).ι i).range ⊔ ((stdFamilyV E m hm).ι j).range) ⊓
        (stdFamilyV E m hm).torus ≤
      ((stdFamilyV E m hm).nodeTor i).range ⊔ ((stdFamilyV E m hm).nodeTor j).range := by
  rcases hM with h2 | h3
  · exact pair_disjoint_inf_torus_le E m hm hK hij h2
  · rcases lt_or_gt_of_ne hij with hlt | hlt
    · exact pair_adjacent_inf_torus_le E m hm hK hlt h3
    · have hM' : CFSG.StandardType.ggCoxeterMatrixD (m + 1) j i = 3 := by
        rw [CoxeterMatrix.symmetric]
        exact h3
      calc (((stdFamilyV E m hm).ι i).range ⊔ ((stdFamilyV E m hm).ι j).range) ⊓
            (stdFamilyV E m hm).torus
          = (((stdFamilyV E m hm).ι j).range ⊔ ((stdFamilyV E m hm).ι i).range) ⊓
              (stdFamilyV E m hm).torus := by rw [sup_comm]
        _ ≤ ((stdFamilyV E m hm).nodeTor j).range ⊔ ((stdFamilyV E m hm).nodeTor i).range :=
            pair_adjacent_inf_torus_le E m hm hK hlt hM'
        _ = ((stdFamilyV E m hm).nodeTor i).range ⊔ ((stdFamilyV E m hm).nodeTor j).range := by
            rw [sup_comm]

theorem stdFamilyV_torus_inf (m : ℕ) (hm : 3 ≤ m)
    (hK : Nat.card K = (2 ^ f) ^ 2) (J : Set (Fin (m + 1))) (hJ : J.encard ≤ 2) :
    (⨆ j ∈ J, ((stdFamilyV E m hm).ι j).range) ⊓ (stdFamilyV E m hm).torus =
      ⨆ j ∈ J, ((stdFamilyV E m hm).nodeTor j).range := by
  refine PhanFamilyE.torus_inf_of_le (S := stdFamilyV E m hm) ?_ ?_ J hJ
  · intro i
    exact single_inf_torus_le E m hm hK i
  · intro i j hij
    exact pair_inf_torus_le E m hm hK hij (ggCoxeterMatrixD_simplyLaced i j hij)

theorem stdFamilyV_good (m : ℕ) (hm : 3 ≤ m)
    (hK : Nat.card K = (2 ^ f) ^ 2) : (stdFamilyV E m hm).Good where
  simplyLaced := fun i j hij => ggCoxeterMatrixD_simplyLaced i j hij
  inj := fun i => stdFamilyV_inj E hm i
  disj := fun i j hij => stdFamilyV_disj E hm i j hij
  θ_inj := fun i j hij hM => stdFamilyV_θ_inj E hm i j hij hM
  indep := stdFamilyV_indep E m hm hK
  torus_inf := stdFamilyV_torus_inf E m hm hK

theorem stdFamilyΩ_map_subtype (m : ℕ) (hm : 3 ≤ m)
    (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) :
    (stdFamilyΩ E m hm hK hq).map
        (Subgroup.subtype ⁅TauCeti.QuadraticMap.orthogonalGroup (Qn E (m + 1)),
          TauCeti.QuadraticMap.orthogonalGroup (Qn E (m + 1))⁆) = stdFamilyV E m hm := by
  refine PhanFamilyE.eq_of_ι_eq_of_θ_eq (fun i => ?_) (fun i j => ?_)
  · exact coe_stdFamilyΩ_ι E m hm hK hq i
  · exact coe_stdFamilyΩ_θ E m hm hK hq i j

theorem stdFamilyΩ_good (m : ℕ) (hm : 3 ≤ m)
    (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) :
    (stdFamilyΩ E m hm hK hq).Good := by
  have hmap := stdFamilyΩ_map_subtype E m hm hK hq
  have hV : (stdFamilyV E m hm).Good := stdFamilyV_good E m hm hK
  rw [← hmap] at hV
  exact PhanFamilyE.Good.of_map (fun a b h => Subtype.ext h) hV

end CFSG.ClassicalInvolution.PhanDn
