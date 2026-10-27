module

public import CFSG.LieType.SeitzGeneration.UnitaryCenters

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ONExt

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary Centers

variable {K : Type*} [Field K] {σ : K ≃+* K} {n m : ℕ}

variable (σ) in
@[expose] def IsON (x : Fin m → Fin n → K) : Prop :=
  ∀ i j, herm σ (x i) (x j) = if i = j then 1 else 0

@[expose] def colMat (x : Fin m → Fin n → K) : Matrix (Fin n) (Fin m) K :=
  Matrix.of fun k j => x j k

variable (σ) in
@[expose] def coordMat (x : Fin m → Fin n → K) : Matrix (Fin m) (Fin n) K :=
  Matrix.of fun i k => σ (x i k)

theorem colMat_mulVec (x : Fin m → Fin n → K) (c : Fin m → K) :
    colMat x *ᵥ c = orthoEmb x c := by
  funext k
  simp only [colMat, mulVec, dotProduct, of_apply, orthoEmb_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem coordMat_mulVec (x : Fin m → Fin n → K) (v : Fin n → K) :
    coordMat σ x *ᵥ v = fun i => herm σ (x i) v := by
  funext i
  simp [coordMat, mulVec, dotProduct, herm_def]

theorem coordMat_mul_colMat {x : Fin m → Fin n → K} (hx : IsON σ x) :
    coordMat σ x * colMat x = 1 := by
  ext i j
  have h := hx i j
  rw [herm_def] at h
  simp only [coordMat, colMat, mul_apply, of_apply, one_apply]
  exact h

theorem coord_orthoEmb {x : Fin m → Fin n → K} (hx : IsON σ x) (c : Fin m → K) :
    (fun i => herm σ (x i) (orthoEmb x c)) = c := by
  rw [← coordMat_mulVec, ← colMat_mulVec, mulVec_mulVec, coordMat_mul_colMat hx, one_mulVec]

theorem orthoEmb_injective {x : Fin m → Fin n → K} (hx : IsON σ x) :
    Function.Injective (orthoEmb x) := by
  intro c d h
  rw [← coord_orthoEmb hx c, ← coord_orthoEmb hx d, h]

theorem orthoEmb_single (x : Fin m → Fin n → K) (i : Fin m) :
    orthoEmb x (Pi.single i 1) = x i := by
  rw [orthoEmb_apply, Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_eq_of_ne hj])
    (by simp)]
  simp

theorem herm_orthoEmb_of_orth (x : Fin m → Fin n → K) {u : Fin n → K}
    (hu : ∀ i, herm σ (x i) u = 0) (c : Fin m → K) : herm σ (orthoEmb x c) u = 0 := by
  rw [herm_orthoEmb_left]
  simp [hu]

theorem exists_decomp {x : Fin m → Fin n → K} (hx : IsON σ x) (v : Fin n → K) :
    ∃ (c : Fin m → K) (u : Fin n → K), (∀ i, herm σ (x i) u = 0) ∧ v = orthoEmb x c + u := by
  refine ⟨fun i => herm σ (x i) v, v - orthoEmb x (fun i => herm σ (x i) v), fun i => ?_,
    by abel⟩
  have h := congrFun (coord_orthoEmb hx (fun i => herm σ (x i) v)) i
  rw [herm_sub_right, h, sub_self]

variable (σ) in
@[expose] def extMat (x : Fin m → Fin n → K) (g : Matrix (Fin m) (Fin m) K) :
    Matrix (Fin n) (Fin n) K :=
  1 + colMat x * (g - 1) * coordMat σ x

theorem extMat_mulVec_orthoEmb {x : Fin m → Fin n → K} (hx : IsON σ x)
    (g : Matrix (Fin m) (Fin m) K) (c : Fin m → K) :
    extMat σ x g *ᵥ orthoEmb x c = orthoEmb x (g *ᵥ c) := by
  have h1 : (colMat x * (g - 1) * coordMat σ x) *ᵥ (colMat x *ᵥ c) =
      colMat x *ᵥ ((g - 1) *ᵥ c) := by
    rw [mulVec_mulVec, Matrix.mul_assoc, coordMat_mul_colMat hx, Matrix.mul_one, ← mulVec_mulVec]
  rw [← colMat_mulVec, ← colMat_mulVec, extMat, add_mulVec, one_mulVec, h1, sub_mulVec,
    one_mulVec, mulVec_sub]
  abel

theorem extMat_mulVec_of_orth (x : Fin m → Fin n → K) (g : Matrix (Fin m) (Fin m) K)
    {u : Fin n → K} (hu : ∀ i, herm σ (x i) u = 0) : extMat σ x g *ᵥ u = u := by
  have h0 : coordMat σ x *ᵥ u = 0 := by
    rw [coordMat_mulVec]
    funext i
    exact hu i
  rw [extMat, add_mulVec, one_mulVec, ← mulVec_mulVec, h0, mulVec_zero, add_zero]

theorem extMat_mulVec {x : Fin m → Fin n → K} (hx : IsON σ x) (g : Matrix (Fin m) (Fin m) K)
    (c : Fin m → K) {u : Fin n → K} (hu : ∀ i, herm σ (x i) u = 0) :
    extMat σ x g *ᵥ (orthoEmb x c + u) = orthoEmb x (g *ᵥ c) + u := by
  rw [mulVec_add, extMat_mulVec_orthoEmb hx, extMat_mulVec_of_orth x g hu]

theorem det_extMat {x : Fin m → Fin n → K} (hx : IsON σ x) (g : Matrix (Fin m) (Fin m) K) :
    (extMat σ x g).det = g.det := by
  rw [extMat, Matrix.mul_assoc, det_one_add_mul_comm, Matrix.mul_assoc, coordMat_mul_colMat hx,
    Matrix.mul_one, add_sub_cancel]

theorem herm_extMat (hσ : ∀ c, σ (σ c) = c) {x : Fin m → Fin n → K} (hx : IsON σ x)
    {g : Matrix (Fin m) (Fin m) K} (hg : ∀ c d, herm σ (g *ᵥ c) (g *ᵥ d) = herm σ c d)
    (v w : Fin n → K) :
    herm σ (extMat σ x g *ᵥ v) (extMat σ x g *ᵥ w) = herm σ v w := by
  obtain ⟨c, u, hu, rfl⟩ := exists_decomp hx v
  obtain ⟨d, u', hu', rfl⟩ := exists_decomp hx w
  rw [extMat_mulVec hx g c hu, extMat_mulVec hx g d hu']
  have h1 : ∀ e : Fin m → K, herm σ (orthoEmb x e) u' = 0 := herm_orthoEmb_of_orth x hu'
  have h2 : ∀ e : Fin m → K, herm σ u (orthoEmb x e) = 0 := fun e =>
    herm_eq_zero_comm σ hσ (herm_orthoEmb_of_orth x hu e)
  simp only [herm_add_left, herm_add_right, h1, h2, herm_orthoEmb hx, hg]

@[expose] def ext (hσ : ∀ c, σ (σ c) = c) {x : Fin m → Fin n → K} (hx : IsON σ x) :
    SUid σ m →* SUid σ n where
  toFun g := mkSU σ (extMat σ x ((g : GL (Fin m) K) : Matrix (Fin m) (Fin m) K))
    (by rw [det_extMat hx]; exact ((mem_SUid_iff σ).1 g.2).1)
    (herm_extMat hσ hx ((mem_SUid_iff σ).1 g.2).2)
  map_one' := by
    refine ext_smul σ fun v => ?_
    rw [mkSU_smul]
    simp [extMat]
  map_mul' g g' := by
    refine ext_smul σ fun v => ?_
    rw [mul_smul, mkSU_smul, mkSU_smul, mkSU_smul]
    obtain ⟨c, u, hu, rfl⟩ := exists_decomp hx v
    rw [extMat_mulVec hx _ c hu, extMat_mulVec hx _ c hu, extMat_mulVec hx _ _ hu, mulVec_mulVec]
    rfl

variable (hσ : ∀ c, σ (σ c) = c) {x : Fin m → Fin n → K} (hx : IsON σ x)

theorem ext_smul_eq (g : SUid σ m) (v : Fin n → K) :
    ext hσ hx g • v = extMat σ x ((g : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ v := rfl

theorem ext_smul_orthoEmb (g : SUid σ m) (c : Fin m → K) :
    ext hσ hx g • orthoEmb x c = orthoEmb x (g • c) := by
  rw [ext_smul_eq, extMat_mulVec_orthoEmb hx, smul_def]

theorem ext_smul_of_orth (g : SUid σ m) {u : Fin n → K} (hu : ∀ i, herm σ (x i) u = 0) :
    ext hσ hx g • u = u := by
  rw [ext_smul_eq, extMat_mulVec_of_orth x _ hu]

theorem ext_tv_smul {a : Fin m → K} (ha : herm σ a a = 0) {c : K} (hc : c + σ c = 0)
    (v : Fin n → K) :
    ext hσ hx (tv hσ ha hc) • v = v + (c * herm σ (orthoEmb x a) v) • orthoEmb x a := by
  obtain ⟨d, u, hu, rfl⟩ := exists_decomp hx v
  rw [smul_add, ext_smul_orthoEmb hσ hx, ext_smul_of_orth hσ hx _ hu, tv_smul, map_add, map_smul,
    herm_add_right, herm_orthoEmb hx, herm_orthoEmb_of_orth x hu, add_zero]
  abel

theorem isCenter_orthoEmb {H : Subgroup (SUid σ n)} (hH : ∀ g, ext hσ hx g ∈ H)
    {a : Fin m → K} (ha : herm σ a a = 0) : IsCenter H (orthoEmb x a) :=
  ⟨by rw [herm_orthoEmb hx]; exact ha, fun _ hc =>
    ⟨ext hσ hx (tv hσ ha hc), hH _, ext_tv_smul hσ hx ha hc⟩⟩

theorem allCenters_of_forall_ext_mem {H : Subgroup (SUid σ n)} (hH : ∀ g, ext hσ hx g ∈ H) :
    AllCenters H (Submodule.span K (Set.range x)) := by
  intro v hv hvi
  obtain ⟨c, rfl⟩ := (mem_span_range_iff x v).1 hv
  rw [herm_orthoEmb hx] at hvi
  exact isCenter_orthoEmb hσ hx hH hvi

variable (σ) in
@[expose] def resMat (x : Fin m → Fin n → K) (s : Matrix (Fin n) (Fin n) K) :
    Matrix (Fin m) (Fin m) K :=
  coordMat σ x * s * colMat x

omit hσ in
include hx in
theorem resMat_mulVec_eq {s : SUid σ n} {c d : Fin m → K} (hd : s • orthoEmb x c = orthoEmb x d) :
    resMat σ x ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ c = d := by
  rw [resMat, ← mulVec_mulVec, ← mulVec_mulVec, colMat_mulVec, ← smul_def, hd, coordMat_mulVec,
    coord_orthoEmb hx]

omit hσ in
include hx in
theorem orthoEmb_resMat_mulVec {s : SUid σ n} (hs : ∀ c, ∃ d, s • orthoEmb x c = orthoEmb x d)
    (c : Fin m → K) :
    orthoEmb x (resMat σ x ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ c) =
      s • orthoEmb x c := by
  obtain ⟨d, hd⟩ := hs c
  rw [resMat_mulVec_eq hx hd, hd]

omit hσ in
include hx in
theorem resMat_mul {s t : SUid σ n} (hs : ∀ c, ∃ d, s • orthoEmb x c = orthoEmb x d)
    (ht : ∀ c, ∃ d, t • orthoEmb x c = orthoEmb x d) :
    resMat σ x (((s * t : SUid σ n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      resMat σ x ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        resMat σ x ((t : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  refine Matrix.ext_of_mulVec_single fun i => ?_
  rw [← mulVec_mulVec]
  apply orthoEmb_injective hx
  have hst : ∀ c, ∃ d, (s * t) • orthoEmb x c = orthoEmb x d := fun c => by
    obtain ⟨d, hd⟩ := ht c
    obtain ⟨d', hd'⟩ := hs d
    exact ⟨d', by rw [mul_smul, hd, hd']⟩
  rw [orthoEmb_resMat_mulVec hx hst, orthoEmb_resMat_mulVec hx hs, orthoEmb_resMat_mulVec hx ht,
    mul_smul]

omit hσ in
include hx in
theorem resMat_one :
    resMat σ x (((1 : SUid σ n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
  rw [show (((1 : SUid σ n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 from rfl, resMat,
    Matrix.mul_one, coordMat_mul_colMat hx]

omit hσ in
include hx in
theorem resMat_pow {s : SUid σ n} (hs : ∀ c, ∃ d, s • orthoEmb x c = orthoEmb x d) (k : ℕ) :
    resMat σ x (((s ^ k : SUid σ n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      resMat σ x ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ k := by
  have hsk : ∀ k : ℕ, ∀ c, ∃ d, (s ^ k) • orthoEmb x c = orthoEmb x d := by
    intro k
    induction k with
    | zero => exact fun c => ⟨c, by rw [pow_zero, one_smul]⟩
    | succ k ih =>
      intro c
      obtain ⟨d, hd⟩ := hs c
      obtain ⟨d', hd'⟩ := ih d
      exact ⟨d', by rw [pow_succ, mul_smul, hd, hd']⟩
  induction k with
  | zero => rw [pow_zero, pow_zero, resMat_one hx]
  | succ k ih => rw [pow_succ, resMat_mul hx (hsk k) hs, ih, pow_succ]

omit hσ in
include hx in
theorem herm_resMat {s : SUid σ n} (hs : ∀ c, ∃ d, s • orthoEmb x c = orthoEmb x d)
    (c d : Fin m → K) :
    herm σ (resMat σ x ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ c)
      (resMat σ x ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ d) = herm σ c d := by
  rw [← herm_orthoEmb hx, orthoEmb_resMat_mulVec hx hs, orthoEmb_resMat_mulVec hx hs,
    herm_smul_smul, herm_orthoEmb hx]

variable {S : Subgroup (SUid σ n)} (hS : ∀ s ∈ S, ∀ c, ∃ d, s • orthoEmb x c = orthoEmb x d)
  (hdet : ∀ s ∈ S, (resMat σ x ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).det = 1)

@[expose] def res : S →* SUid σ m where
  toFun s := mkSU σ (resMat σ x (((s : SUid σ n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (hdet s s.2) (herm_resMat hx (hS s s.2))
  map_one' := by
    refine ext_smul σ fun c => ?_
    rw [mkSU_smul, one_smul]
    exact (congrArg (· *ᵥ c) (resMat_one hx)).trans (one_mulVec c)
  map_mul' s t := by
    refine ext_smul σ fun c => ?_
    rw [mul_smul, mkSU_smul, mkSU_smul, mkSU_smul, mulVec_mulVec]
    exact congrArg (· *ᵥ c) (resMat_mul hx (hS s s.2) (hS t t.2))

omit hσ in
theorem res_smul_eq (s : S) (c : Fin m → K) :
    res hx hS hdet s • c =
      resMat σ x (((s : SUid σ n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ c := rfl

omit hσ in
theorem orthoEmb_res_smul (s : S) (c : Fin m → K) :
    orthoEmb x (res hx hS hdet s • c) = (s : SUid σ n) • orthoEmb x c := by
  rw [res_smul_eq, orthoEmb_resMat_mulVec hx (hS s s.2)]

omit hσ in
theorem res_eq_one (s : S) (hfix : ∀ c, (s : SUid σ n) • orthoEmb x c = orthoEmb x c) :
    res hx hS hdet s = 1 := by
  refine ext_smul σ fun c => ?_
  apply orthoEmb_injective hx
  rw [orthoEmb_res_smul, hfix, one_smul]

include hS in
theorem orth_smul_of_orth {s : SUid σ n} (hsS : s ∈ S) {u : Fin n → K}
    (hu : ∀ i, herm σ (x i) u = 0) (i : Fin m) : herm σ (x i) (s • u) = 0 := by
  obtain ⟨d, hd⟩ := hS s⁻¹ (S.inv_mem hsS) (Pi.single i 1)
  rw [orthoEmb_single] at hd
  have h := herm_smul_smul σ s⁻¹ (x i) (s • u)
  rw [inv_smul_smul, hd] at h
  rw [← h]
  exact herm_orthoEmb_of_orth x hu d

theorem commute_ext (s : S) {g : SUid σ m} (h : res hx hS hdet s * g = g * res hx hS hdet s) :
    (s : SUid σ n) * ext hσ hx g = ext hσ hx g * s := by
  refine ext_smul σ fun v => ?_
  obtain ⟨c, u, hu, rfl⟩ := exists_decomp hx v
  have e1 : ext hσ hx g • (orthoEmb x c + u) = orthoEmb x (g • c) + u := by
    rw [smul_add, ext_smul_orthoEmb hσ hx, ext_smul_of_orth hσ hx _ hu]
  have e2 : (s : SUid σ n) • (orthoEmb x c + u) = orthoEmb x (res hx hS hdet s • c) +
      (s : SUid σ n) • u := by
    rw [smul_add, orthoEmb_res_smul]
  rw [mul_smul, mul_smul, e1, e2, smul_add, smul_add, ← orthoEmb_res_smul hx hS hdet,
    ext_smul_orthoEmb hσ hx, ext_smul_of_orth hσ hx _ (orth_smul_of_orth hS s.2 hu), ← mul_smul,
    ← mul_smul, h]

end CFSG.LieType.SeitzGeneration.ONExt
