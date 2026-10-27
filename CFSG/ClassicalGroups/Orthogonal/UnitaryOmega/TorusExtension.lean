module

public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.Blocks
import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.AutSemilinear
import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.BlockCast
public import CFSG.RankThree.PartOne.KC.OrthogonalNaturalCommonDefs

public section

namespace CFSG.ClassicalGroups.Orthogonal.UnitaryOmega

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.LieType.BorelTits
  CFSG.RankThree.PartOne.KCOrthogonal

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Finite K] [CharP K 2] {f : ℕ}
  (E : QuadExt F K (unitaryInvolution K 2 f))

private theorem torusExt_normHypForm_succ {m : ℕ} (w : (F × F) × (Fin (m + 1) → K)) :
    normHypForm E (m + 1) w = normHypForm E m (w.1, Fin.init w.2) +
      CFSG.ClassicalInvolution.PhanDn.normQuad E (w.2 (Fin.last m)) := by
  have h2 : normHypForm E (m + 1) w =
      CFSG.Timmesfeld.ClassicalOrders.hypPlane F w.1 +
        ∑ i : Fin (m + 1), CFSG.ClassicalInvolution.PhanDn.normQuad E (w.2 i) :=
    normHypForm_apply_coord E (m + 1) w
  have h1 : normHypForm E m (w.1, Fin.init w.2) =
      CFSG.Timmesfeld.ClassicalOrders.hypPlane F w.1 +
        ∑ i : Fin m, CFSG.ClassicalInvolution.PhanDn.normQuad E (w.2 (Fin.castSucc i)) :=
    normHypForm_apply_coord E m (w.1, Fin.init w.2)
  rw [h2, h1, Fin.sum_univ_castSucc]
  abel

private def torusExt_snoc {m : ℕ} (x : Fin m → K) (y : K) : Fin (m + 1) → K :=
  Fin.snoc (α := fun _ => K) x y

omit [Field K] [Finite K] [CharP K 2] in
private theorem torusExt_snoc_last {m : ℕ} (x : Fin m → K) (y : K) :
    torusExt_snoc x y (Fin.last m) = y := by
  show Fin.snoc (α := fun _ => K) x y (Fin.last m) = y
  simp only [Fin.snoc_last]

omit [Field K] [Finite K] [CharP K 2] in
private theorem torusExt_snoc_castSucc {m : ℕ} (x : Fin m → K) (y : K) (i : Fin m) :
    torusExt_snoc x y (Fin.castSucc i) = x i := by
  show Fin.snoc (α := fun _ => K) x y (Fin.castSucc i) = x i
  simp only [Fin.snoc_castSucc]

omit [Field K] [Finite K] [CharP K 2] in
private theorem torusExt_snoc_init {m : ℕ} (x : Fin m → K) (y : K) :
    Fin.init (torusExt_snoc x y) = x :=
  funext fun i => torusExt_snoc_castSucc x y i

omit [Field K] [Finite K] [CharP K 2] in
private theorem torusExt_snoc_init_last {m : ℕ} (v : Fin (m + 1) → K) :
    torusExt_snoc (Fin.init v) (v (Fin.last m)) = v := by
  show Fin.snoc (α := fun _ => K) (Fin.init v) (v (Fin.last m)) = v
  simp only [Fin.snoc_init_self]

private def torusExt_snocPair {m : ℕ} (x : (F × F) × (Fin m → K)) (z : K) :
    (F × F) × (Fin (m + 1) → K) :=
  (x.1, torusExt_snoc x.2 z)

omit [Field F] [Field K] [Algebra F K] [Finite K] [CharP K 2] in
private theorem torusExt_snocPair_apply {m : ℕ} (x : (F × F) × (Fin m → K)) (z : K) :
    torusExt_snocPair x z = (x.1, torusExt_snoc x.2 z) := rfl

omit [Field F] [Field K] [Algebra F K] [Finite K] [CharP K 2] in
private theorem torusExt_castRestr_succ {m : ℕ} (w : (F × F) × (Fin (m + 1) → K)) :
    castRestr (Nat.le_succ m) w = (w.1, Fin.init w.2) := rfl

private def torusExt_castLinSucc {m : ℕ}
    (g : ((F × F) × (Fin m → K)) →ₗ[F] ((F × F) × (Fin m → K)))
    (w : (F × F) × (Fin (m + 1) → K)) : (F × F) × (Fin (m + 1) → K) :=
  ((g (w.1, Fin.init w.2)).1, torusExt_snoc (g (w.1, Fin.init w.2)).2 (w.2 (Fin.last m)))

omit [Finite K] [CharP K 2] in
private theorem torusExt_castLinSucc_fst {m : ℕ}
    (g : ((F × F) × (Fin m → K)) →ₗ[F] ((F × F) × (Fin m → K)))
    (w : (F × F) × (Fin (m + 1) → K)) :
    (torusExt_castLinSucc g w).1 = (g (w.1, Fin.init w.2)).1 := rfl

omit [Finite K] [CharP K 2] in
private theorem torusExt_castLinSucc_snd {m : ℕ}
    (g : ((F × F) × (Fin m → K)) →ₗ[F] ((F × F) × (Fin m → K)))
    (w : (F × F) × (Fin (m + 1) → K)) :
    (torusExt_castLinSucc g w).2 =
      torusExt_snoc (g (w.1, Fin.init w.2)).2 (w.2 (Fin.last m)) := rfl

omit [Finite K] [CharP K 2] in
private theorem torusExt_castLinSucc_eq_snocPair {m : ℕ}
    (g : ((F × F) × (Fin m → K)) →ₗ[F] ((F × F) × (Fin m → K)))
    (w : (F × F) × (Fin (m + 1) → K)) :
    torusExt_castLinSucc g w =
      torusExt_snocPair (g (w.1, Fin.init w.2)) (w.2 (Fin.last m)) := rfl

private theorem torusExt_castLin_succ {m : ℕ}
    (g : ((F × F) × (Fin m → K)) →ₗ[F] ((F × F) × (Fin m → K)))
    (w : (F × F) × (Fin (m + 1) → K)) :
    castLin (Nat.le_succ m) g w = torusExt_castLinSucc g w := by
  refine Prod.ext ?_ ?_
  · rw [castLin_fst, torusExt_castLinSucc_fst, torusExt_castRestr_succ]
  · rw [torusExt_castLinSucc_snd]
    refine funext fun j => ?_
    refine Fin.lastCases ?_ ?_ j
    · rw [castLin_snd_of_not_lt (h := Nat.le_succ m) (g := g) (v := w) (by simp),
        torusExt_snoc_last]
    · intro i
      rw [castLin_snd_of_lt (h := Nat.le_succ m) (g := g) (v := w) (by exact i.2),
        torusExt_castRestr_succ, torusExt_snoc_castSucc]
      rfl

private noncomputable def torusExt_hat {m : ℕ}
    (S : ((F × F) × (Fin m → K)) ≃+ ((F × F) × (Fin m → K))) (t : K ≃+ K) :
    ((F × F) × (Fin (m + 1) → K)) ≃+ ((F × F) × (Fin (m + 1) → K)) where
  toFun w := ((S (w.1, Fin.init w.2)).1,
    torusExt_snoc (S (w.1, Fin.init w.2)).2 (t (w.2 (Fin.last m))))
  invFun w := ((S.symm (w.1, Fin.init w.2)).1,
    torusExt_snoc (S.symm (w.1, Fin.init w.2)).2 (t.symm (w.2 (Fin.last m))))
  left_inv w := by
    have h1 : t.symm (t (w.2 (Fin.last m))) = w.2 (Fin.last m) :=
      AddEquiv.symm_apply_apply t _
    have h2 : S.symm (S (w.1, Fin.init w.2)) = (w.1, Fin.init w.2) :=
      AddEquiv.symm_apply_apply S _
    have h3 : torusExt_snoc (Fin.init w.2) (w.2 (Fin.last m)) = w.2 :=
      torusExt_snoc_init_last w.2
    refine Prod.ext ?_ ?_
    · simp only [torusExt_snoc_init, Prod.mk.eta, h2]
    · simp only [torusExt_snoc_init, Prod.mk.eta, h2, torusExt_snoc_last, h1, h3]
  right_inv w := by
    have h1 : t (t.symm (w.2 (Fin.last m))) = w.2 (Fin.last m) :=
      AddEquiv.apply_symm_apply t _
    have h2 : S (S.symm (w.1, Fin.init w.2)) = (w.1, Fin.init w.2) :=
      AddEquiv.apply_symm_apply S _
    have h3 : torusExt_snoc (Fin.init w.2) (w.2 (Fin.last m)) = w.2 :=
      torusExt_snoc_init_last w.2
    refine Prod.ext ?_ ?_
    · simp only [torusExt_snoc_init, Prod.mk.eta, h2]
    · simp only [torusExt_snoc_init, Prod.mk.eta, h2, torusExt_snoc_last, h1, h3]
  map_add' v w := by
    have hv : ((v + w).1, Fin.init (v + w).2) =
        (v.1, Fin.init v.2) + (w.1, Fin.init w.2) := rfl
    have hlast : (v + w).2 (Fin.last m) = v.2 (Fin.last m) + w.2 (Fin.last m) := rfl
    change ((S ((v + w).1, Fin.init (v + w).2)).1,
        torusExt_snoc (S ((v + w).1, Fin.init (v + w).2)).2 (t ((v + w).2 (Fin.last m)))) =
      ((S (v.1, Fin.init v.2)).1, torusExt_snoc (S (v.1, Fin.init v.2)).2
        (t (v.2 (Fin.last m)))) +
      ((S (w.1, Fin.init w.2)).1, torusExt_snoc (S (w.1, Fin.init w.2)).2
        (t (w.2 (Fin.last m))))
    rw [hv, hlast]
    simp only [map_add]
    refine Prod.ext ?_ (funext fun j => ?_)
    · simp only [Prod.fst_add]
    · simp only [Prod.snd_add, Pi.add_apply]
      refine Fin.lastCases ?_ ?_ j
      · simp only [torusExt_snoc_last]
      · intro i
        simp only [torusExt_snoc_castSucc, Pi.add_apply]

omit [Algebra F K] [Finite K] [CharP K 2] in
private theorem torusExt_hat_apply {m : ℕ}
    (S : ((F × F) × (Fin m → K)) ≃+ ((F × F) × (Fin m → K))) (t : K ≃+ K)
    (w : (F × F) × (Fin (m + 1) → K)) :
    torusExt_hat S t w = ((S (w.1, Fin.init w.2)).1,
      torusExt_snoc (S (w.1, Fin.init w.2)).2 (t (w.2 (Fin.last m)))) := rfl

omit [Algebra F K] [Finite K] [CharP K 2] in
private theorem torusExt_hat_fst {m : ℕ}
    (S : ((F × F) × (Fin m → K)) ≃+ ((F × F) × (Fin m → K))) (t : K ≃+ K)
    (w : (F × F) × (Fin (m + 1) → K)) :
    (torusExt_hat S t w).1 = (S (w.1, Fin.init w.2)).1 := rfl

omit [Algebra F K] [Finite K] [CharP K 2] in
private theorem torusExt_hat_snd {m : ℕ}
    (S : ((F × F) × (Fin m → K)) ≃+ ((F × F) × (Fin m → K))) (t : K ≃+ K)
    (w : (F × F) × (Fin (m + 1) → K)) :
    (torusExt_hat S t w).2 =
      torusExt_snoc (S (w.1, Fin.init w.2)).2 (t (w.2 (Fin.last m))) :=
  rfl

omit [Algebra F K] [Finite K] [CharP K 2] in
private theorem torusExt_hat_snd_castSucc {m : ℕ}
    (S : ((F × F) × (Fin m → K)) ≃+ ((F × F) × (Fin m → K))) (t : K ≃+ K)
    (w : (F × F) × (Fin (m + 1) → K)) (i : Fin m) :
    (torusExt_hat S t w).2 (Fin.castSucc i) = (S (w.1, Fin.init w.2)).2 i := by
  rw [torusExt_hat_snd, torusExt_snoc_castSucc]

omit [Algebra F K] [Finite K] [CharP K 2] in
private theorem torusExt_hat_snd_last {m : ℕ}
    (S : ((F × F) × (Fin m → K)) ≃+ ((F × F) × (Fin m → K))) (t : K ≃+ K)
    (w : (F × F) × (Fin (m + 1) → K)) :
    (torusExt_hat S t w).2 (Fin.last m) = t (w.2 (Fin.last m)) := by
  rw [torusExt_hat_snd, torusExt_snoc_last]

omit [Algebra F K] [Finite K] [CharP K 2] in
private theorem torusExt_hat_restrict {m : ℕ}
    (S : ((F × F) × (Fin m → K)) ≃+ ((F × F) × (Fin m → K))) (t : K ≃+ K)
    (w : (F × F) × (Fin (m + 1) → K)) :
    ((torusExt_hat S t w).1, Fin.init (torusExt_hat S t w).2) = S (w.1, Fin.init w.2) := by
  refine Prod.ext ?_ ?_
  · rw [torusExt_hat_fst]
  · rw [torusExt_hat_snd, torusExt_snoc_init]

omit [Algebra F K] [Finite K] [CharP K 2] in
private theorem torusExt_hat_symm_fst {m : ℕ}
    (S : ((F × F) × (Fin m → K)) ≃+ ((F × F) × (Fin m → K))) (t : K ≃+ K)
    (w : (F × F) × (Fin (m + 1) → K)) :
    ((torusExt_hat S t).symm w).1 = (S.symm (w.1, Fin.init w.2)).1 := rfl

omit [Algebra F K] [Finite K] [CharP K 2] in
private theorem torusExt_hat_symm_snd {m : ℕ}
    (S : ((F × F) × (Fin m → K)) ≃+ ((F × F) × (Fin m → K))) (t : K ≃+ K)
    (w : (F × F) × (Fin (m + 1) → K)) :
    ((torusExt_hat S t).symm w).2 =
      torusExt_snoc (S.symm (w.1, Fin.init w.2)).2 (t.symm (w.2 (Fin.last m))) := rfl

omit [Algebra F K] [Finite K] [CharP K 2] in
private theorem torusExt_hat_symm_restrict {m : ℕ}
    (S : ((F × F) × (Fin m → K)) ≃+ ((F × F) × (Fin m → K))) (t : K ≃+ K)
    (w : (F × F) × (Fin (m + 1) → K)) :
    (((torusExt_hat S t).symm w).1, Fin.init ((torusExt_hat S t).symm w).2) =
      S.symm (w.1, Fin.init w.2) := by
  refine Prod.ext ?_ ?_
  · rw [torusExt_hat_symm_fst]
  · rw [torusExt_hat_symm_snd, torusExt_snoc_init]

omit [Algebra F K] [Finite K] [CharP K 2] in
private theorem torusExt_hat_symm_last {m : ℕ}
    (S : ((F × F) × (Fin m → K)) ≃+ ((F × F) × (Fin m → K))) (t : K ≃+ K)
    (w : (F × F) × (Fin (m + 1) → K)) :
    ((torusExt_hat S t).symm w).2 (Fin.last m) = t.symm (w.2 (Fin.last m)) := by
  rw [torusExt_hat_symm_snd, torusExt_snoc_last]

private theorem torusExt_hat_quad {m : ℕ}
    (S : ((F × F) × (Fin m → K)) ≃+ ((F × F) × (Fin m → K))) (t : K ≃+ K)
    (σ : F ≃+* F) (μ : F)
    (hSQ : ∀ v, normHypForm E m (S v) = μ * σ (normHypForm E m v))
    (htQ : ∀ x : K, CFSG.ClassicalInvolution.PhanDn.normQuad E (t x) =
      μ * σ (CFSG.ClassicalInvolution.PhanDn.normQuad E x))
    (w : (F × F) × (Fin (m + 1) → K)) :
    normHypForm E (m + 1) (torusExt_hat S t w) =
      μ * σ (normHypForm E (m + 1) w) := by
  rw [torusExt_normHypForm_succ E (torusExt_hat S t w),
    torusExt_normHypForm_succ E w, torusExt_hat_restrict, torusExt_hat_snd_last]
  simp only [hSQ, htQ, map_add, mul_add]

omit [Finite K] [CharP K 2] in
private theorem torusExt_hat_smul {m : ℕ}
    (S : ((F × F) × (Fin m → K)) ≃+ ((F × F) × (Fin m → K))) (t : K ≃+ K) (σ : F ≃+* F)
    (hS : ∀ (c : F) (v : (F × F) × (Fin m → K)), S (c • v) = σ c • S v)
    (hts : ∀ (c : F) (x : K), t (c • x) = σ c • t x)
    (c : F) (w : (F × F) × (Fin (m + 1) → K)) :
    torusExt_hat S t (c • w) = σ c • torusExt_hat S t w := by
  have hcw : ((c • w).1, Fin.init (c • w).2) = c • (w.1, Fin.init w.2) := rfl
  have hlast : (c • w).2 (Fin.last m) = c • w.2 (Fin.last m) := rfl
  rw [torusExt_hat_apply, hcw, hlast]
  simp only [hS, hts]
  refine Prod.ext ?_ (funext fun j => ?_)
  · simp only [torusExt_hat_fst, Prod.smul_fst]
  · simp only [torusExt_hat_snd, Prod.smul_snd, Pi.smul_apply]
    refine Fin.lastCases ?_ ?_ j
    · simp only [torusExt_snoc_last]
    · intro i
      simp only [torusExt_snoc_castSucc, Pi.smul_apply]

omit [Field F] [Algebra F K] [Finite K] [CharP K 2] in
private theorem torusExt_torVec_last {m p : ℕ} {χ : Multiplicative (ZMod p) →* Kˣ}
    (u : Fin (m + 1) → Multiplicative (ZMod p)) (w : (F × F) × (Fin (m + 1) → K)) :
    ((w.1, fun i => (χ (u i) : K) * w.2 i) : (F × F) × (Fin (m + 1) → K)).2 (Fin.last m) =
      (χ (u (Fin.last m)) : K) * w.2 (Fin.last m) := rfl

omit [Field F] [Algebra F K] [Finite K] [CharP K 2] in
private theorem torusExt_torVec_init {m p : ℕ} {χ : Multiplicative (ZMod p) →* Kˣ}
    (u : Fin (m + 1) → Multiplicative (ZMod p)) (w : (F × F) × (Fin (m + 1) → K)) :
    (((w.1, fun i => (χ (u i) : K) * w.2 i) : (F × F) × (Fin (m + 1) → K)).1,
      Fin.init ((w.1, fun i => (χ (u i) : K) * w.2 i) :
        (F × F) × (Fin (m + 1) → K)).2) =
      (w.1, fun i : Fin m => (χ ((Fin.init u) i) : K) * (Fin.init w.2) i) := rfl

omit [Algebra F K] [Finite K] [CharP K 2] in
private theorem torusExt_hat_tor {m p : ℕ} {χ : Multiplicative (ZMod p) →* Kˣ}
    (S : ((F × F) × (Fin m → K)) ≃+ ((F × F) × (Fin m → K))) (t : K ≃+ K)
    (hStor : ∀ (a : Fin m → Multiplicative (ZMod p)) (v : (F × F) × (Fin m → K)),
      S (v.1, fun i => (χ (a i) : K) * v.2 i) =
        ((S v).1, fun i => (χ (a i) : K) * (S v).2 i))
    (htχ : ∀ (a : Multiplicative (ZMod p)) (x : K),
      t ((χ a : K) * x) = (χ a : K) * t x)
    (u : Fin (m + 1) → Multiplicative (ZMod p)) (w : (F × F) × (Fin (m + 1) → K)) :
    torusExt_hat S t ((w.1, fun i => (χ (u i) : K) * w.2 i)) =
      (((torusExt_hat S t w).1, fun i => (χ (u i) : K) * (torusExt_hat S t w).2 i)) := by
  rw [torusExt_hat_apply, torusExt_torVec_init, torusExt_torVec_last]
  rw [show S (w.1, fun i : Fin m => (χ ((Fin.init u) i) : K) * (Fin.init w.2) i) =
      ((S (w.1, Fin.init w.2)).1,
        fun i => (χ ((Fin.init u) i) : K) * (S (w.1, Fin.init w.2)).2 i) from
    hStor (Fin.init u) (w.1, Fin.init w.2)]
  refine Prod.ext ?_ (funext fun j => ?_)
  · simp only [torusExt_hat_fst]
  · simp only [torusExt_hat_snd]
    refine Fin.lastCases ?_ ?_ j
    · rw [torusExt_snoc_last, torusExt_snoc_last]
      exact htχ (u (Fin.last m)) (w.2 (Fin.last m))
    · intro i
      have hiu : (Fin.init u) i = u (Fin.castSucc i) := rfl
      rw [torusExt_snoc_castSucc, torusExt_snoc_castSucc, hiu]

omit [Algebra F K] [Finite K] [CharP K 2] in
private theorem torusExt_hat_coord {m : ℕ}
    (S : ((F × F) × (Fin m → K)) ≃+ ((F × F) × (Fin m → K))) (t : K ≃+ K)
    (hScoord : ∀ (i : Fin m) (v : (F × F) × (Fin m → K)), (S v).2 i = 0 ↔ v.2 i = 0)
    (j : Fin (m + 1)) (w : (F × F) × (Fin (m + 1) → K)) :
    (torusExt_hat S t w).2 j = 0 ↔ w.2 j = 0 := by
  refine Fin.lastCases ?_ ?_ j
  · rw [torusExt_hat_snd_last]
    constructor
    · intro h
      exact t.injective (by rw [h, map_zero])
    · intro h
      rw [h, map_zero]
  · intro i
    rw [torusExt_hat_snd_castSucc, hScoord i (w.1, Fin.init w.2)]
    rfl

private theorem torusExt_hat_castLin {m : ℕ}
    (S : ((F × F) × (Fin m → K)) ≃+ ((F × F) × (Fin m → K))) (t : K ≃+ K)
    (g : ((F × F) × (Fin m → K)) →ₗ[F] ((F × F) × (Fin m → K)))
    (w : (F × F) × (Fin (m + 1) → K)) :
    torusExt_hat S t (castLin (Nat.le_succ m) g w) =
      ((S (g (w.1, Fin.init w.2))).1,
        torusExt_snoc (S (g (w.1, Fin.init w.2))).2 (t (w.2 (Fin.last m)))) := by
  rw [torusExt_hat_apply, torusExt_castLin_succ]
  simp only [torusExt_castLinSucc_fst, torusExt_castLinSucc_snd, torusExt_snoc_init,
    torusExt_snoc_last, Prod.mk.eta]

private theorem torusExt_of_parts {m p : ℕ} (hm : 2 ≤ m) (hpq : p ∣ 2 ^ f + 1)
    {χ : Multiplicative (ZMod p) →* Kˣ} (α : MulAut (normOmega E m)) (σ : F ≃+* F)
    (S : ((F × F) × (Fin m → K)) ≃+ ((F × F) × (Fin m → K))) (μ : F)
    (hS : ∀ (c : F) (v : (F × F) × (Fin m → K)), S (c • v) = σ c • S v) (hμ : μ ≠ 0)
    (hSQ : ∀ v, normHypForm E m (S v) = μ * σ (normHypForm E m v))
    (hSα : ∀ (y : normOmega E m) (v : (F × F) × (Fin m → K)),
      ((α y : normOmega E m) : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K)))
          (S v) =
        S ((y : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) v))
    (hStor : ∀ (a : Fin m → Multiplicative (ZMod p)) (v : (F × F) × (Fin m → K)),
      S (v.1, fun i => (χ (a i) : K) * v.2 i) = ((S v).1, fun i => (χ (a i) : K) * (S v).2 i))
    (hScoord : ∀ (i : Fin m) (v : (F × F) × (Fin m → K)), (S v).2 i = 0 ↔ v.2 i = 0)
    (t : K ≃+ K) (hts : ∀ (c : F) (x : K), t (c • x) = σ c • t x)
    (htQ : ∀ x : K, CFSG.ClassicalInvolution.PhanDn.normQuad E (t x) =
      μ * σ (CFSG.ClassicalInvolution.PhanDn.normQuad E x))
    (htχ : ∀ (a : Multiplicative (ZMod p)) (x : K), t ((χ a : K) * x) = (χ a : K) * t x) :
    ∃ β : MulAut (normOmega E (m + 1)),
      (∀ y : normOmega E m,
        β (normOmegaCast E (Nat.le_succ m) y) = normOmegaCast E (Nat.le_succ m) (α y)) ∧
      (∀ u : Fin (m + 1) → Multiplicative (ZMod p),
        β (normPlaneTorus E (by omega) hpq χ u) = normPlaneTorus E (by omega) hpq χ u) ∧
      ∀ T : Finset (Fin (m + 1)),
        (normBlock E (m + 1) T).map β.toMonoidHom = normBlock E (m + 1) T := by
  classical
  have hmpos : 2 ≤ m := hm
  have hFinF : Finite F := Finite.of_injective (algebraMap F K) (algebraMap F K).injective
  have hFinK : Module.Finite F K := finiteDimensional_of_quadExt E
  have hFinPair : Module.Finite F (F × F) :=
    @Module.Finite.prod F F F _ _ _ _ _ (Module.Finite.self F) (Module.Finite.self F)
  have hFinPi : Module.Finite F (Fin (m + 1) → K) :=
    @Module.Finite.pi F _ (Fin (m + 1)) (fun _ => K) _ _ _ (fun _ => hFinK)
  have hFinV : Module.Finite F ((F × F) × (Fin (m + 1) → K)) :=
    @Module.Finite.prod F (F × F) (Fin (m + 1) → K) _ _ _ _ _ hFinPair hFinPi
  let S' : ((F × F) × (Fin (m + 1) → K)) ≃+ ((F × F) × (Fin (m + 1) → K)) :=
    torusExt_hat S t
  have hS' : ∀ (c : F) (w : (F × F) × (Fin (m + 1) → K)), S' (c • w) = σ c • S' w :=
    fun c w => torusExt_hat_smul S t σ hS hts c w
  have hS'Q : ∀ w : (F × F) × (Fin (m + 1) → K),
      normHypForm E (m + 1) (S' w) = μ * σ (normHypForm E (m + 1) w) :=
    fun w => torusExt_hat_quad E S t σ μ hSQ htQ w
  have hS'tor : ∀ (u : Fin (m + 1) → Multiplicative (ZMod p))
      (w : (F × F) × (Fin (m + 1) → K)),
      S' (w.1, fun i => (χ (u i) : K) * w.2 i) =
        ((S' w).1, fun i => (χ (u i) : K) * (S' w).2 i) :=
    fun u w => torusExt_hat_tor S t hStor htχ u w
  have hS'coord : ∀ (j : Fin (m + 1)) (w : (F × F) × (Fin (m + 1) → K)),
      (S' w).2 j = 0 ↔ w.2 j = 0 :=
    fun j w => torusExt_hat_coord S t hScoord j w
  have hsurj : Function.Surjective
      (semilinOrth (Q := normHypForm E (m + 1)) S' σ hS' μ hS'Q) :=
    @semilinOrth_surjective F _ ((F × F) × (Fin (m + 1) → K)) _ _ (normHypForm E (m + 1))
      S' σ hS' μ hS'Q hFinF hFinV
  let β : MulAut (normOmega E (m + 1)) :=
    MulEquiv.ofBijective (semilinOrth (Q := normHypForm E (m + 1)) S' σ hS' μ hS'Q)
      ⟨semilinOrth_injective S' σ hS' μ hS'Q, hsurj⟩
  have hβ : ∀ g : normOmega E (m + 1),
      ((β g : normOmega E (m + 1)) :
        ((F × F) × (Fin (m + 1) → K)) ≃ₗ[F] ((F × F) × (Fin (m + 1) → K))) =
        semilinConj S' σ hS'
          (g : ((F × F) × (Fin (m + 1) → K)) ≃ₗ[F] ((F × F) × (Fin (m + 1) → K))) :=
    fun g => semilinOrth_apply S' σ hS' μ hS'Q g
  refine ⟨β, ?_, ?_, ?_⟩
  · intro y
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    set u : (F × F) × (Fin m → K) := S.symm (v.1, Fin.init v.2) with hu
    set Y : (F × F) × (Fin m → K) :=
      ((y : normOmega E m) : ((F × F) × (Fin m → K)) ≃ₗ[F]
        ((F × F) × (Fin m → K))).toLinearMap u with hY
    have hsymm : ((S'.symm v).1, Fin.init (S'.symm v).2) = u := by
      rw [hu]
      exact torusExt_hat_symm_restrict S t v
    have hlast : (S'.symm v).2 (Fin.last m) = t.symm (v.2 (Fin.last m)) :=
      torusExt_hat_symm_last S t v
    have hSu : S u = (v.1, Fin.init v.2) := by
      rw [hu]
      exact S.apply_symm_apply _
    have hαu : ((α y : normOmega E m) : ((F × F) × (Fin m → K)) ≃ₗ[F]
        ((F × F) × (Fin m → K))).toLinearMap (S u) = S Y := by
      rw [hY]
      exact hSα y u
    have hL : ((β (normOmegaCast E (Nat.le_succ m) y) : normOmega E (m + 1)) :
        ((F × F) × (Fin (m + 1) → K)) ≃ₗ[F]
          ((F × F) × (Fin (m + 1) → K))) v =
        torusExt_snocPair (S Y) (v.2 (Fin.last m)) := by
      rw [hβ, semilinConj_apply, normOmegaCast_apply, castEquiv_apply, torusExt_hat_castLin,
        ← torusExt_snocPair_apply, hsymm, hlast, AddEquiv.apply_symm_apply, ← hY]
    have hR : ((normOmegaCast E (Nat.le_succ m) (α y) : normOmega E (m + 1)) :
        ((F × F) × (Fin (m + 1) → K)) ≃ₗ[F]
          ((F × F) × (Fin (m + 1) → K))) v =
        torusExt_snocPair (S Y) (v.2 (Fin.last m)) := by
      rw [normOmegaCast_apply, castEquiv_apply, torusExt_castLin_succ,
        torusExt_castLinSucc_eq_snocPair, ← hSu, hαu]
    rw [hL, hR]
  · intro u
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    rw [hβ (normPlaneTorus E (by omega) hpq χ u), semilinConj_apply]
    rw [show ((normPlaneTorus E (by omega) hpq χ u : normOmega E (m + 1)) :
        ((F × F) × (Fin (m + 1) → K)) ≃ₗ[F]
          ((F × F) × (Fin (m + 1) → K))) (S'.symm v) =
        ((S'.symm v).1, fun i => (χ (u i) : K) * (S'.symm v).2 i) from
      normPlaneTorus_apply E (by omega) hpq χ u (S'.symm v)]
    rw [hS'tor, AddEquiv.apply_symm_apply]
    rw [show ((normPlaneTorus E (by omega) hpq χ u : normOmega E (m + 1)) :
        ((F × F) × (Fin (m + 1) → K)) ≃ₗ[F]
          ((F × F) × (Fin (m + 1) → K))) v =
        (v.1, fun i => (χ (u i) : K) * v.2 i) from
      normPlaneTorus_apply E (by omega) hpq χ u v]
  · intro T
    let R : Submodule F ((F × F) × (Fin (m + 1) → K)) :=
      coordSupport (LinearEquiv.refl F ((F × F) × (Fin (m + 1) → K))) T
    have hmemCS : ∀ v : (F × F) × (Fin (m + 1) → K),
        v ∈ (R : Set ((F × F) × (Fin (m + 1) → K))) ↔ ∀ j, j ∉ T → v.2 j = 0 :=
      fun v => mem_coordSupport_refl_iff E T v
    have hR : S' '' (R : Set ((F × F) × (Fin (m + 1) → K))) =
        (R : Set ((F × F) × (Fin (m + 1) → K))) := by
      ext w
      constructor
      · rintro ⟨z, hz, rfl⟩
        rw [hmemCS] at hz ⊢
        intro j hj
        exact (hS'coord j z).mpr (hz j hj)
      · intro hw
        rw [hmemCS] at hw
        refine ⟨S'.symm w, ?_, S'.apply_symm_apply w⟩
        rw [hmemCS]
        intro j hj
        exact (hS'coord j (S'.symm w)).mp (by rw [AddEquiv.apply_symm_apply]; exact hw j hj)
    change ((supportedDerived (normHypForm E (m + 1)) R).subgroupOf
      (normOmega E (m + 1))).map β.toMonoidHom =
        (supportedDerived (normHypForm E (m + 1)) R).subgroupOf (normOmega E (m + 1))
    have hmapH : (supportedDerived (normHypForm E (m + 1)) R).map (semilinConj S' σ hS') =
        supportedDerived (normHypForm E (m + 1)) R :=
      map_supportedDerived_semilinConj_of_image_eq S' σ hS' μ hμ hS'Q hR
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      refine Subgroup.mem_subgroupOf.mpr ?_
      show ((β x : normOmega E (m + 1)) : ((F × F) × (Fin (m + 1) → K)) ≃ₗ[F]
        ((F × F) × (Fin (m + 1) → K))) ∈ supportedDerived (normHypForm E (m + 1)) R
      have hx' : (x : ((F × F) × (Fin (m + 1) → K)) ≃ₗ[F]
          ((F × F) × (Fin (m + 1) → K))) ∈
          supportedDerived (normHypForm E (m + 1)) R := Subgroup.mem_subgroupOf.mp hx
      rw [hβ x]
      have hx'' : semilinConj S' σ hS' (x : ((F × F) × (Fin (m + 1) → K)) ≃ₗ[F]
          ((F × F) × (Fin (m + 1) → K))) ∈
          (supportedDerived (normHypForm E (m + 1)) R).map (semilinConj S' σ hS') :=
        Subgroup.mem_map.mpr ⟨_, hx', rfl⟩
      rwa [hmapH] at hx''
    · intro y hy
      have hy' : (y : ((F × F) × (Fin (m + 1) → K)) ≃ₗ[F]
          ((F × F) × (Fin (m + 1) → K))) ∈
          supportedDerived (normHypForm E (m + 1)) R := Subgroup.mem_subgroupOf.mp hy
      refine Subgroup.mem_map.mpr ⟨β.symm y, Subgroup.mem_subgroupOf.mpr ?_,
        MulEquiv.apply_symm_apply β y⟩
      have h1 : ((β (β.symm y) : normOmega E (m + 1)) :
          ((F × F) × (Fin (m + 1) → K)) ≃ₗ[F] ((F × F) × (Fin (m + 1) → K))) ∈
          supportedDerived (normHypForm E (m + 1)) R := by
        rw [MulEquiv.apply_symm_apply]
        exact hy'
      rw [hβ (β.symm y)] at h1
      have h2 : semilinConj S' σ hS' ((β.symm y : normOmega E (m + 1)) :
          ((F × F) × (Fin (m + 1) → K)) ≃ₗ[F]
            ((F × F) × (Fin (m + 1) → K))) ∈
          (supportedDerived (normHypForm E (m + 1)) R).map (semilinConj S' σ hS') := by
        rw [hmapH]
        exact h1
      obtain ⟨g, hg, hge⟩ := Subgroup.mem_map.mp h2
      have hgz : g = ((β.symm y : normOmega E (m + 1)) :
          ((F × F) × (Fin (m + 1) → K)) ≃ₗ[F]
            ((F × F) × (Fin (m + 1) → K))) := semilinConj_injective S' σ hS' hge
      rwa [hgz] at hg


theorem exists_extension_of_fixes_normPlaneTorus {m p : ℕ} [Fact p.Prime] (hm : 3 ≤ m)
    (hpq : p ∣ 2 ^ f + 1) {χ : Multiplicative (ZMod p) →* Kˣ} (hχ : Function.Injective χ)
    (α : MulAut (normOmega E m))
    (hα : ∀ u : Fin m → Multiplicative (ZMod p),
      α (normPlaneTorus E (by omega) hpq χ u) = normPlaneTorus E (by omega) hpq χ u) :
    ∃ β : MulAut (normOmega E (m + 1)),
      (∀ y : normOmega E m,
        β (normOmegaCast E (Nat.le_succ m) y) = normOmegaCast E (Nat.le_succ m) (α y)) ∧
      (∀ u : Fin (m + 1) → Multiplicative (ZMod p),
        β (normPlaneTorus E (by omega) hpq χ u) = normPlaneTorus E (by omega) hpq χ u) ∧
      ∀ S : Finset (Fin (m + 1)),
        (normBlock E (m + 1) S).map β.toMonoidHom = normBlock E (m + 1) S := by
  classical
  have hm2 : 2 ≤ m := by omega
  obtain ⟨σ, S, μ, hS, hμ, hSQ, hSα⟩ := exists_semilinear_conj_of_mulAut E hm α
  have hD_apply : ∀ (a : Fin m → Multiplicative (ZMod p))
      (v : (F × F) × (Fin m → K)),
      ((normPlaneTorus E hm2 hpq χ a : normOmega E m) :
        ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) v =
        (v.1, fun j => (χ (a j) : K) * v.2 j) :=
    fun a v => normPlaneTorus_apply E hm2 hpq χ a v
  have hS_torus : ∀ (a : Fin m → Multiplicative (ZMod p))
      (v : (F × F) × (Fin m → K)),
      S ((v.1, fun i => (χ (a i) : K) * v.2 i)) =
        ((S v).1, fun i => (χ (a i) : K) * (S v).2 i) := by
    intro a v
    have h := hSα (normPlaneTorus E hm2 hpq χ a) v
    rw [hα a, hD_apply a v, hD_apply a (S v)] at h
    exact h.symm
  have hS_torus_map : ∀ (a : Fin m → Multiplicative (ZMod p))
      (v : (F × F) × (Fin m → K)),
      S (((normPlaneTorus E hm2 hpq χ a : normOmega E m) :
        ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) v) =
        ((normPlaneTorus E hm2 hpq χ a : normOmega E m) :
          ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) (S v) := by
    intro a v
    rw [hD_apply a v, hD_apply a (S v)]
    exact hS_torus a v
  let g : Multiplicative (ZMod p) := Multiplicative.ofAdd 1
  have hg1 : g ≠ 1 := by
    intro h1
    have h2 : (1 : ZMod p) = 0 := congrArg Multiplicative.toAdd h1
    exact one_ne_zero h2
  have hχg : (χ g : K) ≠ 1 := by
    intro h1
    refine hg1 (hχ ?_)
    rw [map_one]
    exact Units.ext h1
  have hχg0 : (χ g : K) - 1 ≠ 0 := sub_ne_zero.mpr hχg
  have hfix_iff : ∀ (i : Fin m) (v : (F × F) × (Fin m → K)),
      ((normPlaneTorus E hm2 hpq χ (Pi.mulSingle i g) : normOmega E m) :
        ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) v = v ↔
        v.2 i = 0 := by
    intro i v
    let ai : Fin m → Multiplicative (ZMod p) := Pi.mulSingle i g
    have hai : ai i = g :=
      Pi.mulSingle_eq_same (M := fun _ => Multiplicative (ZMod p)) i g
    have haine : ∀ j, j ≠ i → ai j = 1 := fun j hj =>
      Pi.mulSingle_eq_of_ne (M := fun _ => Multiplicative (ZMod p)) hj g
    rw [hD_apply ai v]
    show ((v.1, fun j => (χ (ai j) : K) * v.2 j) = v ↔ v.2 i = 0)
    constructor
    · intro h
      have h2 : (χ g : K) * v.2 i = v.2 i := by
        simpa [hai] using congrFun (congrArg Prod.snd h) i
      have h3 : ((χ g : K) - 1) * v.2 i = 0 := by
        rw [sub_mul, one_mul, h2, sub_self]
      exact (mul_eq_zero.mp h3).resolve_left hχg0
    · intro h
      refine Prod.ext_iff.mpr ⟨rfl, ?_⟩
      show (fun j => (χ (ai j) : K) * v.2 j) = v.2
      funext j
      by_cases hj : j = i
      · subst hj
        rw [hai, h, mul_zero]
      · rw [haine j hj, map_one, Units.val_one, one_mul]
  have hS_coord_zero : ∀ (i : Fin m) (v : (F × F) × (Fin m → K)),
      (S v).2 i = 0 ↔ v.2 i = 0 := by
    intro i v
    constructor
    · intro h
      have h2 : S (((normPlaneTorus E hm2 hpq χ (Pi.mulSingle i g) : normOmega E m) :
          ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) v) = S v := by
        rw [hS_torus_map (Pi.mulSingle i g) v]
        exact (hfix_iff i (S v)).mpr h
      exact (hfix_iff i v).mp (S.injective h2)
    · intro h
      have h2 : ((normPlaneTorus E hm2 hpq χ (Pi.mulSingle i g) : normOmega E m) :
          ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) (S v) = S v := by
        rw [← hS_torus_map (Pi.mulSingle i g) v, (hfix_iff i v).mpr h]
      exact (hfix_iff i (S v)).mp h2
  let i0 : Fin m := ⟨0, by omega⟩
  let e : K → (F × F) × (Fin m → K) := fun x => ((0, 0), Pi.single i0 x)
  have he_same : ∀ x : K, (e x).2 i0 = x :=
    fun x => Pi.single_eq_same (M := fun _ => K) i0 x
  have he_ne : ∀ (x : K) (j : Fin m), j ≠ i0 → (e x).2 j = 0 :=
    fun x j hj => Pi.single_eq_of_ne (M := fun _ => K) hj x
  have he_zero : e 0 = 0 := by
    refine Prod.ext_iff.mpr ⟨?_, ?_⟩
    · simp [e]
    · funext j
      show (e 0).2 j = (0 : Fin m → K) j
      by_cases hj : j = i0
      · subst hj
        rw [he_same]
        rfl
      · rw [he_ne _ j hj]
        rfl
  have he_add : ∀ x y : K, e (x + y) = e x + e y := by
    intro x y
    refine Prod.ext_iff.mpr ⟨?_, ?_⟩
    · simp [e]
    · funext j
      show (e (x + y)).2 j = (e x).2 j + (e y).2 j
      by_cases hj : j = i0
      · subst hj
        rw [he_same, he_same, he_same]
      · rw [he_ne _ j hj, he_ne _ j hj, he_ne _ j hj]
        rw [add_zero]
  have he_smul : ∀ (c : F) (x : K), e (c • x) = c • e x := by
    intro c x
    refine Prod.ext_iff.mpr ⟨?_, ?_⟩
    · simp [e]
    · funext j
      show (e (c • x)).2 j = c • (e x).2 j
      by_cases hj : j = i0
      · subst hj
        rw [he_same, he_same]
      · rw [he_ne _ j hj, he_ne _ j hj, smul_zero]
  let t : K → K := fun x => (S (e x)).2 i0
  have hD_sub : ∀ (a : Fin m → Multiplicative (ZMod p))
      (v : (F × F) × (Fin m → K)),
      ((normPlaneTorus E hm2 hpq χ a : normOmega E m) :
        ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) v - v =
        ((0, 0), fun j => ((χ (a j) : K) - 1) * v.2 j) := by
    intro a v
    obtain ⟨r, z⟩ := v
    rw [hD_apply a (r, z)]
    refine Prod.ext_iff.mpr ⟨?_, ?_⟩
    · show (r - r) = ((0, 0) : F × F)
      rw [sub_self]
      rfl
    · show (fun j => (χ (a j) : K) * z j - z j) =
        fun j => ((χ (a j) : K) - 1) * z j
      funext j
      rw [sub_mul, one_mul]
  have hS_e : ∀ x : K, S (e x) = e (t x) := by
    intro x
    let a0 : Fin m → Multiplicative (ZMod p) := Pi.mulSingle i0 g
    have ha0 : a0 i0 = g :=
      Pi.mulSingle_eq_same (M := fun _ => Multiplicative (ZMod p)) i0 g
    have ha0ne : ∀ j, j ≠ i0 → a0 j = 1 := fun j hj =>
      Pi.mulSingle_eq_of_ne (M := fun _ => Multiplicative (ZMod p)) hj g
    let w : (F × F) × (Fin m → K) := e (((χ g : K) - 1)⁻¹ * x)
    have hDw : ((normPlaneTorus E hm2 hpq χ a0 : normOmega E m) :
        ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) w - w = e x := by
      rw [hD_sub a0 w]
      refine Prod.ext_iff.mpr ⟨rfl, ?_⟩
      show (fun j => ((χ (a0 j) : K) - 1) * w.2 j) = (e x).2
      funext j
      by_cases hj : j = i0
      · subst hj
        rw [ha0, he_same, he_same]
        exact mul_inv_cancel_left₀ hχg0 x
      · rw [ha0ne j hj, map_one, Units.val_one, he_ne _ j hj, he_ne _ j hj]
        simp
    have hstep : S (e x) =
        ((normPlaneTorus E hm2 hpq χ a0 : normOmega E m) :
          ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) (S w) - S w := by
      have h1 : S (((normPlaneTorus E hm2 hpq χ a0 : normOmega E m) :
          ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) w - w) =
          S (((normPlaneTorus E hm2 hpq χ a0 : normOmega E m) :
            ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) w) - S w :=
        S.map_sub _ _
      rw [hDw] at h1
      rw [h1, hS_torus_map a0 w]
    have hfst : (S (e x)).1 = 0 := by
      have h1 : (((normPlaneTorus E hm2 hpq χ a0 : normOmega E m) :
          ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) (S w)).1 = (S w).1 := by
        rw [hD_apply a0 (S w)]
      rw [hstep, Prod.fst_sub, h1, sub_self]
    have hsnd : ∀ j, j ≠ i0 → (S (e x)).2 j = 0 := by
      intro j hj
      rw [hstep, Prod.snd_sub, hD_apply a0 (S w)]
      show (χ (a0 j) : K) * (S w).2 j - (S w).2 j = 0
      rw [ha0ne j hj, map_one, Units.val_one, one_mul, sub_self]
    refine Prod.ext_iff.mpr ⟨?_, ?_⟩
    · rw [hfst]
      rfl
    · funext j
      show (S (e x)).2 j = (e (t x)).2 j
      by_cases hj : j = i0
      · subst hj
        rw [he_same]
      · rw [he_ne _ j hj]
        exact hsnd j hj
  have ht_zero : t 0 = 0 := by
    show (S (e 0)).2 i0 = 0
    rw [he_zero, S.map_zero]
    rfl
  have ht_add : ∀ x y : K, t (x + y) = t x + t y := by
    intro x y
    calc t (x + y) = (S (e (x + y))).2 i0 := rfl
      _ = (S (e x + e y)).2 i0 := by rw [he_add x y]
      _ = (S (e x) + S (e y)).2 i0 := by rw [S.map_add]
      _ = t x + t y := rfl
  have ht_inj : Function.Injective t := by
    intro x y hxy
    have h1 : S (e x) = S (e y) := by rw [hS_e x, hS_e y, hxy]
    have h2 : e x = e y := S.injective h1
    have h3 := congrFun (congrArg Prod.snd h2) i0
    rw [he_same, he_same] at h3
    exact h3
  have ht_surj : Function.Surjective t := Finite.surjective_of_injective ht_inj
  let tHom : K →+ K :=
    { toFun := t, map_zero' := ht_zero, map_add' := ht_add }
  let tEq : K ≃+ K := AddEquiv.ofBijective tHom ⟨ht_inj, ht_surj⟩
  have ht_smul : ∀ (c : F) (x : K), t (c • x) = σ c • t x := by
    intro c x
    calc t (c • x) = (S (e (c • x))).2 i0 := rfl
      _ = (S (c • e x)).2 i0 := by rw [he_smul c x]
      _ = (σ c • S (e x)).2 i0 := by rw [hS c (e x)]
      _ = σ c • t x := rfl
  have ht_Q : ∀ x : K, CFSG.ClassicalInvolution.PhanDn.normQuad E (t x) =
      μ * σ (CFSG.ClassicalInvolution.PhanDn.normQuad E x) := by
    intro x
    have hsum_t : (∑ j : Fin m,
        CFSG.ClassicalInvolution.PhanDn.normQuad E ((e (t x)).2 j)) =
        CFSG.ClassicalInvolution.PhanDn.normQuad E (t x) := by
      have hzero : ∀ j ∈ (Finset.univ : Finset (Fin m)), j ≠ i0 →
          CFSG.ClassicalInvolution.PhanDn.normQuad E ((e (t x)).2 j) = 0 := by
        intro j _ hj
        rw [he_ne _ j hj]
        exact QuadraticMap.map_zero _
      have hnot : i0 ∉ (Finset.univ : Finset (Fin m)) →
          CFSG.ClassicalInvolution.PhanDn.normQuad E ((e (t x)).2 i0) = 0 :=
        fun h => absurd (Finset.mem_univ i0) h
      rw [Finset.sum_eq_single i0 hzero hnot]
      rw [he_same]
    have hsum_x : (∑ j : Fin m,
        CFSG.ClassicalInvolution.PhanDn.normQuad E ((e x).2 j)) =
        CFSG.ClassicalInvolution.PhanDn.normQuad E x := by
      have hzero : ∀ j ∈ (Finset.univ : Finset (Fin m)), j ≠ i0 →
          CFSG.ClassicalInvolution.PhanDn.normQuad E ((e x).2 j) = 0 := by
        intro j _ hj
        rw [he_ne _ j hj]
        exact QuadraticMap.map_zero _
      have hnot : i0 ∉ (Finset.univ : Finset (Fin m)) →
          CFSG.ClassicalInvolution.PhanDn.normQuad E ((e x).2 i0) = 0 :=
        fun h => absurd (Finset.mem_univ i0) h
      rw [Finset.sum_eq_single i0 hzero hnot]
      rw [he_same]
    have htx : normHypForm E m (e (t x)) =
        CFSG.ClassicalInvolution.PhanDn.normQuad E (t x) := by
      rw [normHypForm_apply_coord E m, hsum_t]
      rw [show CFSG.Timmesfeld.ClassicalOrders.hypPlane F (e (t x)).1 = 0 by
        rw [show (e (t x)).1 = ((0, 0) : F × F) from rfl,
          CFSG.Timmesfeld.ClassicalOrders.hypPlane_apply, zero_mul]]
      rw [zero_add]
    have hx : normHypForm E m (e x) =
        CFSG.ClassicalInvolution.PhanDn.normQuad E x := by
      rw [normHypForm_apply_coord E m, hsum_x]
      rw [show CFSG.Timmesfeld.ClassicalOrders.hypPlane F (e x).1 = 0 by
        rw [show (e x).1 = ((0, 0) : F × F) from rfl,
          CFSG.Timmesfeld.ClassicalOrders.hypPlane_apply, zero_mul]]
      rw [zero_add]
    have h := hSQ (e x)
    rw [hS_e x, htx, hx] at h
    exact h
  have ht_mul : ∀ (a : Multiplicative (ZMod p)) (x : K),
      t ((χ a : K) * x) = (χ a : K) * t x := by
    intro a x
    let a0 : Fin m → Multiplicative (ZMod p) := Pi.mulSingle i0 a
    have ha0 : a0 i0 = a :=
      Pi.mulSingle_eq_same (M := fun _ => Multiplicative (ZMod p)) i0 a
    have ha0ne : ∀ j, j ≠ i0 → a0 j = 1 := fun j hj =>
      Pi.mulSingle_eq_of_ne (M := fun _ => Multiplicative (ZMod p)) hj a
    have hDe : ∀ y : K,
        ((normPlaneTorus E hm2 hpq χ a0 : normOmega E m) :
          ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) (e y) =
          e ((χ a : K) * y) := by
      intro y
      rw [hD_apply a0 (e y)]
      refine Prod.ext_iff.mpr ⟨rfl, ?_⟩
      show (fun j => (χ (a0 j) : K) * (e y).2 j) = (e ((χ a : K) * y)).2
      funext j
      by_cases hj : j = i0
      · subst hj
        rw [ha0, he_same, he_same]
      · rw [ha0ne j hj, map_one, Units.val_one, one_mul, he_ne _ j hj, he_ne _ j hj]
    have h := hS_torus_map a0 (e x)
    rw [hDe x, hS_e x, hDe (t x)] at h
    exact congrFun (congrArg Prod.snd h) i0
  have ht_smul' : ∀ (c : F) (x : K), tEq (c • x) = σ c • tEq x := ht_smul
  have ht_Q' : ∀ x : K, CFSG.ClassicalInvolution.PhanDn.normQuad E (tEq x) =
      μ * σ (CFSG.ClassicalInvolution.PhanDn.normQuad E x) := ht_Q
  have ht_mul' : ∀ (a : Multiplicative (ZMod p)) (x : K),
      tEq ((χ a : K) * x) = (χ a : K) * tEq x := ht_mul
  exact torusExt_of_parts E hm2 hpq α σ S μ hS hμ hSQ hSα hS_torus hS_coord_zero tEq
    ht_smul' ht_Q' ht_mul'

end CFSG.ClassicalGroups.Orthogonal.UnitaryOmega

end
