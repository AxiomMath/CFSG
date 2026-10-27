module

public import CFSG.RankThree.PartOne.KC.UnitaryRigidityFrame

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.PSUTwo

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.KCUnitaryFrame

variable {ℓ f n m : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K)

@[expose] def frameMat (u : Fin m → Fin n → K) : Matrix (Fin n) (Fin m) K :=
  Matrix.of fun k i => u i k

@[expose] noncomputable def frameAdj (u : Fin m → Fin n → K) : Matrix (Fin m) (Fin n) K :=
  ((frameMat u).map h.bar)ᵀ

theorem frameAdj_apply (u : Fin m → Fin n → K) (i : Fin m) (k : Fin n) :
    frameAdj h u i k = h.bar (u i k) := rfl

variable {h}

theorem frameAdj_mul_frameMat {u : Fin m → Fin n → K} (hu : IsOrthonormalFamily h u) :
    frameAdj h u * frameMat u = 1 := by
  ext i j
  have := hu i j
  rw [idForm_eq_dotProduct] at this
  simp only [Matrix.mul_apply, frameAdj_apply, frameMat, Matrix.of_apply, Matrix.one_apply]
  simpa [dotProduct] using this

variable (h) in
@[expose] noncomputable def frameEmb (u : Fin m → Fin n → K) (Y : Matrix (Fin m) (Fin m) K) :
    Matrix (Fin n) (Fin n) K :=
  1 + frameMat u * (Y - 1) * frameAdj h u

theorem frameEmb_one (u : Fin m → Fin n → K) : frameEmb h u (1 : Matrix (Fin m) (Fin m) K) = 1 := by
  simp [frameEmb]

theorem frame_sandwich_mul {u : Fin m → Fin n → K} (hu : IsOrthonormalFamily h u)
    (X X' : Matrix (Fin m) (Fin m) K) :
    frameMat u * X * frameAdj h u * (frameMat u * X' * frameAdj h u) =
      frameMat u * (X * X') * frameAdj h u := by
  have hBA := frameAdj_mul_frameMat hu
  calc frameMat u * X * frameAdj h u * (frameMat u * X' * frameAdj h u)
      = frameMat u * X * (frameAdj h u * frameMat u) * X' * frameAdj h u := by
        simp only [Matrix.mul_assoc]
    _ = frameMat u * (X * X') * frameAdj h u := by
        rw [hBA, Matrix.mul_one]
        simp only [Matrix.mul_assoc]

theorem frameEmb_mul {u : Fin m → Fin n → K} (hu : IsOrthonormalFamily h u)
    (Y Y' : Matrix (Fin m) (Fin m) K) :
    frameEmb h u (Y * Y') = frameEmb h u Y * frameEmb h u Y' := by
  unfold frameEmb
  have key := frame_sandwich_mul hu (Y - 1) (Y' - 1)
  have e : Y * Y' - 1 = (Y - 1) + (Y' - 1) + (Y - 1) * (Y' - 1) := by noncomm_ring
  rw [e]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul]
  rw [key]
  abel

variable (h) in
@[expose] noncomputable def frameHom {u : Fin m → Fin n → K} (hu : IsOrthonormalFamily h u) :
    Matrix (Fin m) (Fin m) K →* Matrix (Fin n) (Fin n) K where
  toFun := frameEmb h u
  map_one' := frameEmb_one u
  map_mul' := frameEmb_mul hu

variable (h) in
@[expose] noncomputable def frameGL {u : Fin m → Fin n → K} (hu : IsOrthonormalFamily h u) :
    GL (Fin m) K →* GL (Fin n) K :=
  Units.map (frameHom h hu)

theorem coe_frameGL {u : Fin m → Fin n → K} (hu : IsOrthonormalFamily h u) (Y : GL (Fin m) K) :
    ((frameGL h hu Y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      frameEmb h u (Y : Matrix (Fin m) (Fin m) K) := rfl

section Adjoint

variable (h) in
@[expose] noncomputable def adj {a b : Type} [Fintype a] [Fintype b] (Y : Matrix a b K) :
    Matrix b a K := (Y.map h.bar)ᵀ

theorem adj_mul {a b c : Type} [Fintype a] [Fintype b] [Fintype c]
    (P : Matrix a b K) (Q : Matrix b c K) : adj h (P * Q) = adj h Q * adj h P := by
  unfold adj
  rw [Matrix.map_mul, Matrix.transpose_mul]

theorem adj_one {a : Type} [Fintype a] [DecidableEq a] : adj h (1 : Matrix a a K) = 1 := by
  unfold adj
  rw [Matrix.map_one _ (map_zero h.bar) (map_one h.bar), Matrix.transpose_one]

theorem adj_add {a b : Type} [Fintype a] [Fintype b] (P Q : Matrix a b K) :
    adj h (P + Q) = adj h P + adj h Q := by
  unfold adj
  rw [Matrix.map_add _ (map_add h.bar), Matrix.transpose_add]

theorem adj_sub {a b : Type} [Fintype a] [Fintype b] (P Q : Matrix a b K) :
    adj h (P - Q) = adj h P - adj h Q := by
  unfold adj
  rw [Matrix.map_sub _ (map_sub h.bar), Matrix.transpose_sub]

theorem adj_adj {a b : Type} [Fintype a] [Fintype b] (P : Matrix a b K) :
    adj h (adj h P) = P := by
  ext i j
  simp [adj, h.bar_bar]

theorem adj_frameMat (u : Fin m → Fin n → K) : adj h (frameMat u) = frameAdj h u := rfl

theorem adj_frameAdj (u : Fin m → Fin n → K) : adj h (frameAdj h u) = frameMat u := by
  rw [← adj_frameMat, adj_adj]

theorem frameEmb_adj (u : Fin m → Fin n → K) (Y : Matrix (Fin m) (Fin m) K) :
    adj h (frameEmb h u Y) = frameEmb h u (adj h Y) := by
  unfold frameEmb
  rw [adj_add, adj_one, adj_mul, adj_mul, adj_sub, adj_one, adj_frameMat, adj_frameAdj]
  simp only [Matrix.mul_assoc]

end Adjoint

section Embedding

theorem frameAdj_mul_frameEmb {u : Fin m → Fin n → K} (hu : IsOrthonormalFamily h u)
    (Y : Matrix (Fin m) (Fin m) K) : frameAdj h u * frameEmb h u Y = Y * frameAdj h u := by
  have hBA := frameAdj_mul_frameMat hu
  unfold frameEmb
  rw [Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hBA, Matrix.one_mul,
    Matrix.sub_mul, Matrix.one_mul]
  abel

theorem frameEmb_injective {u : Fin m → Fin n → K} (hu : IsOrthonormalFamily h u) :
    Function.Injective (frameEmb h u) := by
  intro Y Y' hYY
  have hBA := frameAdj_mul_frameMat hu
  have e : ∀ Z, frameAdj h u * frameEmb h u Z * frameMat u = Z := by
    intro Z
    rw [frameAdj_mul_frameEmb hu, Matrix.mul_assoc, hBA, Matrix.mul_one]
  rw [← e Y, ← e Y', hYY]

theorem frameEmb_mulVec_of_adj_eq_zero {u : Fin m → Fin n → K} (Y : Matrix (Fin m) (Fin m) K)
    {v : Fin n → K} (hv : frameAdj h u *ᵥ v = 0) : frameEmb h u Y *ᵥ v = v := by
  unfold frameEmb
  have h1 : (frameMat u * (Y - 1) * frameAdj h u) *ᵥ v =
      frameMat u *ᵥ ((Y - 1) *ᵥ (frameAdj h u *ᵥ v)) := by
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [Matrix.add_mulVec, Matrix.one_mulVec, h1, hv]
  simp

theorem det_frameEmb {u : Fin m → Fin n → K} (hu : IsOrthonormalFamily h u)
    (Y : Matrix (Fin m) (Fin m) K) : (frameEmb h u Y).det = Y.det := by
  unfold frameEmb
  rw [Matrix.det_one_add_mul_comm, ← Matrix.mul_assoc, frameAdj_mul_frameMat hu, Matrix.one_mul,
    add_sub_cancel]

theorem mem_primeFormUnitary_iff_adj {g : GL (Fin m) K} :
    g ∈ primeFormUnitary h (idGram K m) ↔
      adj h (g : Matrix (Fin m) (Fin m) K) * (g : Matrix (Fin m) (Fin m) K) = 1 := by
  rw [mem_primeFormUnitary]
  simp [idGram, adj]

theorem frameGL_mem {u : Fin m → Fin n → K} (hu : IsOrthonormalFamily h u) {Y : GL (Fin m) K}
    (hY : Y ∈ primeFormUnitary h (idGram K m)) :
    frameGL h hu Y ∈ primeFormUnitary h (idGram K n) := by
  rw [mem_primeFormUnitary_iff_adj] at hY ⊢
  rw [coe_frameGL, frameEmb_adj, ← frameEmb_mul hu, hY, frameEmb_one]

theorem frameGL_mem_gramSU {u : Fin m → Fin n → K} (hu : IsOrthonormalFamily h u) {Y : GL (Fin m) K}
    (hY : Y ∈ gramSU h (idGram K m)) : frameGL h hu Y ∈ gramSU h (idGram K n) := by
  rw [mem_gramSU_iff_unitary] at hY ⊢
  refine ⟨frameGL_mem hu hY.1, ?_⟩
  rw [coe_frameGL, det_frameEmb hu]
  exact hY.2

variable (h) in
@[expose] noncomputable def frameSU {u : Fin m → Fin n → K} (hu : IsOrthonormalFamily h u) :
    gramSU h (idGram K m) →* gramSU h (idGram K n) :=
  MonoidHom.codRestrict ((frameGL h hu).comp (gramSU h (idGram K m)).subtype)
    (gramSU h (idGram K n)) fun Y => frameGL_mem_gramSU hu Y.2

theorem coe_frameSU {u : Fin m → Fin n → K} (hu : IsOrthonormalFamily h u)
    (Y : gramSU h (idGram K m)) :
    (((frameSU h hu Y : gramSU h (idGram K n)) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      frameEmb h u ((Y : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) := rfl

theorem frameSU_injective {u : Fin m → Fin n → K} (hu : IsOrthonormalFamily h u) :
    Function.Injective (frameSU h hu) := by
  intro Y Y' hYY
  have := congrArg (fun Z : gramSU h (idGram K n) => ((Z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    hYY
  simp only [coe_frameSU] at this
  exact Subtype.ext (Units.ext (frameEmb_injective hu this))

end Embedding

section Glue

theorem span_eq_of_orthonormal {W : Submodule K (Fin n → K)} {u : Fin m → Fin n → K}
    (hu : IsOrthonormalFamily h u) (huW : ∀ i, u i ∈ W) (hm : Module.finrank K W = m) :
    Submodule.span K (Set.range u) = W := by
  have hle : Submodule.span K (Set.range u) ≤ W :=
    Submodule.span_le.2 (Set.range_subset_iff.2 huW)
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  rw [finrank_span_eq_card hu.linearIndependent, Fintype.card_fin, hm]

theorem smul_one_mulVec {ι : Type} [Fintype ι] [DecidableEq ι] (c : K) (v : ι → K) :
    (c • (1 : Matrix ι ι K)) *ᵥ v = c • v := by
  simp [Matrix.smul_mulVec]

theorem adj_smul {a b : Type} [Fintype a] [Fintype b] (c : K) (P : Matrix a b K) :
    adj h (c • P) = h.bar c • adj h P := by
  ext i j
  simp [adj]

theorem frame_expand {u : Fin m → Fin n → K} (hu : IsOrthonormalFamily h u) {w : Fin n → K}
    (hw : w ∈ Submodule.span K (Set.range u)) :
    frameMat u *ᵥ (frameAdj h u *ᵥ w) = w := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨i, rfl⟩ := hw
    have h1 : frameAdj h u *ᵥ u i = Pi.single i 1 := by
      have := congrArg (fun M : Matrix (Fin m) (Fin m) K => M.mulVec (Pi.single i 1))
        (frameAdj_mul_frameMat hu)
      simp only [← Matrix.mulVec_mulVec, Matrix.one_mulVec] at this
      have e : frameMat u *ᵥ (Pi.single i 1 : Fin m → K) = u i := by
        ext k; simp [frameMat, Matrix.mulVec_single_one]
      rw [e] at this
      exact this
    rw [h1]
    ext k
    simp [frameMat, Matrix.mulVec_single_one]
  | zero => simp
  | add x y _ _ hx hy => rw [Matrix.mulVec_add, Matrix.mulVec_add, hx, hy]
  | smul c x _ hx => rw [Matrix.mulVec_smul, Matrix.mulVec_smul, hx]

theorem mul_frameMat_apply {a : Type} [Fintype a] (u : Fin m → Fin n → K)
    (A : Matrix a (Fin n) K) (k : a) (i : Fin m) : (A * frameMat u) k i = (A *ᵥ u i) k := rfl

theorem frameMat_mul_apply (u : Fin m → Fin n → K) (W : Matrix (Fin m) (Fin m) K) (k : Fin n)
    (i : Fin m) : (frameMat u * W) k i = (frameMat u *ᵥ fun j => W j i) k := rfl

theorem exists_frame_rep {u : Fin m → Fin n → K} (hu : IsOrthonormalFamily h u) {ν : K}
    {xm A : Matrix (Fin n) (Fin n) K} (hxu : ∀ i, xm *ᵥ u i = ν • u i)
    (hspan : ∀ w, xm *ᵥ w = ν • w → w ∈ Submodule.span K (Set.range u))
    (hA : xm * A = A * xm) :
    A * frameMat u = frameMat u * (frameAdj h u * A * frameMat u) := by
  ext k i
  have hcol : A *ᵥ u i = frameMat u *ᵥ (frameAdj h u *ᵥ (A *ᵥ u i)) := by
    refine (frame_expand hu (hspan _ ?_)).symm
    rw [Matrix.mulVec_mulVec, hA, ← Matrix.mulVec_mulVec, hxu i, Matrix.mulVec_smul]
  rw [mul_frameMat_apply, frameMat_mul_apply]
  have e : (fun j => (frameAdj h u * A * frameMat u) j i) = frameAdj h u *ᵥ (A *ᵥ u i) := by
    funext j
    rw [mul_frameMat_apply, Matrix.mulVec_mulVec]
  rw [e]
  exact congrFun hcol k

theorem frameAdj_mul_eigen {u : Fin m → Fin n → K} {ν : K} (hν : h.bar ν * ν = 1)
    {xm : Matrix (Fin n) (Fin n) K} (hxu : xm * frameMat u = ν • frameMat u)
    (hx : adj h xm * xm = 1) : frameAdj h u * xm = ν • frameAdj h u := by
  have h1 : frameAdj h u * adj h xm = h.bar ν • frameAdj h u := by
    have := congrArg (adj h) hxu
    rwa [adj_mul, adj_smul, adj_frameMat] at this
  have h2 : h.bar ν • (frameAdj h u * xm) = frameAdj h u := by
    have := congrArg (fun P => P * xm) h1
    simp only [Matrix.mul_assoc, hx, Matrix.mul_one] at this
    rw [← Matrix.smul_mul]
    exact this.symm
  calc frameAdj h u * xm = (ν * h.bar ν) • (frameAdj h u * xm) := by
        rw [mul_comm, hν, one_smul]
    _ = ν • (h.bar ν • (frameAdj h u * xm)) := by rw [smul_smul]
    _ = ν • frameAdj h u := by rw [h2]

theorem frameEmb_comm {u : Fin m → Fin n → K} {ν : K} {xm : Matrix (Fin n) (Fin n) K}
    (hxA : xm * frameMat u = ν • frameMat u) (hBx : frameAdj h u * xm = ν • frameAdj h u)
    (Y : Matrix (Fin m) (Fin m) K) : xm * frameEmb h u Y = frameEmb h u Y * xm := by
  unfold frameEmb
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul]
  congr 1
  calc xm * (frameMat u * (Y - 1) * frameAdj h u)
      = (xm * frameMat u) * (Y - 1) * frameAdj h u := by simp only [Matrix.mul_assoc]
    _ = ν • (frameMat u * (Y - 1) * frameAdj h u) := by
        rw [hxA, Matrix.smul_mul, Matrix.smul_mul]
    _ = frameMat u * (Y - 1) * (frameAdj h u * xm) := by
        rw [hBx, Matrix.mul_smul]
    _ = frameMat u * (Y - 1) * frameAdj h u * xm := by simp only [Matrix.mul_assoc]

theorem exists_frameConj {u : Fin m → Fin n → K} (hu : IsOrthonormalFamily h u) {ν : K}
    (x M : primeFormUnitary h (idGram K n))
    (hxu : ∀ i, ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ u i = ν • u i)
    (hspan : ∀ w, ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w = ν • w →
      w ∈ Submodule.span K (Set.range u))
    (hMx : M * x = x * M) :
    ∃ N : primeFormUnitary h (idGram K m),
      ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * frameMat u =
        frameMat u * ((N : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) ∧
      ∀ Y : GL (Fin m) K, (M : GL (Fin n) K) * frameGL h hu Y * (M : GL (Fin n) K)⁻¹ =
        frameGL h hu ((N : GL (Fin m) K) * Y * (N : GL (Fin m) K)⁻¹) := by
  set xg : GL (Fin n) K := (x : GL (Fin n) K) with hxg
  set Mg : GL (Fin n) K := (M : GL (Fin n) K) with hMg
  have hMxg : Mg * xg = xg * Mg := congrArg Subtype.val hMx
  have hcomm : Commute Mg xg := hMxg
  have hxMi : ((xg : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((Mg⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((Mg⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((xg : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    have : Commute Mg⁻¹ xg := hcomm.inv_left
    have h2 : Mg⁻¹ * xg = xg * Mg⁻¹ := this
    exact (congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) h2).symm
  have hxM : ((xg : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (Mg : Matrix (Fin n) (Fin n) K) =
      (Mg : Matrix (Fin n) (Fin n) K) * ((xg : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    (congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) hMxg).symm
  set Mm : Matrix (Fin n) (Fin n) K := (Mg : Matrix (Fin n) (Fin n) K) with hMm
  set Mi : Matrix (Fin n) (Fin n) K := ((Mg⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
    with hMi
  have hMMi : Mm * Mi = 1 := Units.mul_inv Mg
  have hMiM : Mi * Mm = 1 := Units.inv_mul Mg
  have hMu : adj h Mm * Mm = 1 := mem_primeFormUnitary_iff_adj.1 M.2
  have hadjM : adj h Mm = Mi := by
    calc adj h Mm = adj h Mm * (Mm * Mi) := by rw [hMMi, Matrix.mul_one]
      _ = (adj h Mm * Mm) * Mi := by rw [Matrix.mul_assoc]
      _ = Mi := by rw [hMu, Matrix.one_mul]
  have hadjMi : adj h Mi = Mm := by rw [← hadjM, adj_adj]
  have hBA := frameAdj_mul_frameMat hu
  set Mν : Matrix (Fin m) (Fin m) K := frameAdj h u * Mm * frameMat u with hMν
  set Mν' : Matrix (Fin m) (Fin m) K := frameAdj h u * Mi * frameMat u with hMν'
  have hA : Mm * frameMat u = frameMat u * Mν := exists_frame_rep hu hxu hspan hxM
  have hA' : Mi * frameMat u = frameMat u * Mν' := exists_frame_rep hu hxu hspan hxMi
  have hNN' : Mν * Mν' = 1 := by
    calc Mν * Mν' = frameAdj h u * Mm * (frameMat u * Mν') := by
          rw [hMν]; simp only [Matrix.mul_assoc]
      _ = frameAdj h u * Mm * (Mi * frameMat u) := by rw [← hA']
      _ = frameAdj h u * (Mm * Mi) * frameMat u := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hMMi, Matrix.mul_one, hBA]
  have hN'N : Mν' * Mν = 1 := by
    calc Mν' * Mν = frameAdj h u * Mi * (frameMat u * Mν) := by
          rw [hMν']; simp only [Matrix.mul_assoc]
      _ = frameAdj h u * Mi * (Mm * frameMat u) := by rw [← hA]
      _ = frameAdj h u * (Mi * Mm) * frameMat u := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hMiM, Matrix.mul_one, hBA]
  have hadjMν : adj h Mν = Mν' := by
    rw [hMν, adj_mul, adj_mul, adj_frameMat, adj_frameAdj, hadjM]
    simp only [hMν', Matrix.mul_assoc]
  have hadjMν' : adj h Mν' = Mν := by rw [← hadjMν, adj_adj]
  let Ng : GL (Fin m) K := ⟨Mν, Mν', hNN', hN'N⟩
  have hNmem : Ng ∈ primeFormUnitary h (idGram K m) := by
    rw [mem_primeFormUnitary_iff_adj]
    show adj h Mν * Mν = 1
    rw [hadjMν]
    exact hN'N
  have hb : frameAdj h u * Mm = Mν * frameAdj h u := by
    have := congrArg (adj h) hA'
    rw [adj_mul, adj_mul, adj_frameMat, hadjMi, hadjMν'] at this
    exact this
  have hconj : ∀ Y : Matrix (Fin m) (Fin m) K,
      Mm * frameEmb h u Y = frameEmb h u (Mν * Y * Mν') * Mm := by
    intro Y
    unfold frameEmb
    have e1 : (1 + frameMat u * (Mν * Y * Mν' - 1) * frameAdj h u) * Mm =
        Mm + frameMat u * ((Mν * Y * Mν' - 1) * Mν) * frameAdj h u := by
      rw [Matrix.add_mul, Matrix.one_mul]
      congr 1
      calc frameMat u * (Mν * Y * Mν' - 1) * frameAdj h u * Mm
          = frameMat u * (Mν * Y * Mν' - 1) * (frameAdj h u * Mm) := by
            simp only [Matrix.mul_assoc]
        _ = frameMat u * ((Mν * Y * Mν' - 1) * Mν) * frameAdj h u := by
            rw [hb]; simp only [Matrix.mul_assoc]
    have e2 : (Mν * Y * Mν' - 1) * Mν = Mν * Y - Mν := by
      rw [Matrix.sub_mul, Matrix.mul_assoc, Matrix.mul_assoc, hN'N, Matrix.mul_one, Matrix.one_mul]
    rw [e1, e2, Matrix.mul_add, Matrix.mul_one]
    congr 1
    calc Mm * (frameMat u * (Y - 1) * frameAdj h u)
        = (Mm * frameMat u) * (Y - 1) * frameAdj h u := by simp only [Matrix.mul_assoc]
      _ = frameMat u * (Mν * (Y - 1)) * frameAdj h u := by
          rw [hA]; simp only [Matrix.mul_assoc]
      _ = frameMat u * (Mν * Y - Mν) * frameAdj h u := by rw [Matrix.mul_sub, Matrix.mul_one]
  refine ⟨⟨Ng, hNmem⟩, hA, fun Y => ?_⟩
  rw [mul_inv_eq_iff_eq_mul]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_frameGL, coe_frameGL, hconj]
  congr 2

section Completion

theorem exists_gramSU_with_columns
    {ℓ f r s : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData ℓ f K) (hs : 0 < s)
    (U : Matrix (Fin (r + s)) (Fin r) K)
    (hU : (U.map h.bar)ᵀ * U = 1) :
    ∃ T : gramSU h (idGram K (r + s)),
      (((T : GL (Fin (r + s)) K) :
          Matrix (Fin (r + s)) (Fin (r + s)) K).submatrix
        id (Fin.castAdd s)) = U := by
  classical
  let u : Fin r → Fin (r + s) → K := fun i k => U k i
  have hu : IsOrthonormalFamily h u := by
    intro i j
    have h := congrArg (fun M : Matrix (Fin r) (Fin r) K => M i j) hU
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.one_apply] at h
    rw [idForm_eq_dotProduct]
    simpa [u, dotProduct] using h
  have hnorm : ∀ d : K, h.bar d = d → d ≠ 0 → ∃ c : K, h.bar c * c = d := by
    intro d hd _
    obtain ⟨c, hc⟩ := h.normHom_surjective ⟨d, hd⟩
    exact ⟨c, by rw [mul_comm]; exact congrArg Subtype.val hc⟩
  obtain ⟨c₀, hc₀⟩ := h.exists_bar_ne
  have hExt : ∀ k : ℕ, k ≤ s → ∃ b : Fin (r + k) → Fin (r + s) → K,
      IsOrthonormalFamily h b ∧ ∀ i : Fin r, b (Fin.castAdd k i) = u i := by
    intro k hk
    induction k with
    | zero =>
        refine ⟨u, hu, ?_⟩
        intro i
        congr 1
    | succ k ih =>
        obtain ⟨b, hb, hpref⟩ := ih (by omega)
        have hlt : r + k < Module.finrank K (Fin (r + s) → K) := by
          have : r + k < r + s := by omega
          simpa only [Module.finrank_fin_fun] using this
        obtain ⟨v, hv, hbv⟩ := exists_norm_one_perp_of_lt (M := Fin (r + s) → K)
          (B := idForm h (r + s)) (idForm_isSymm h (r + s))
          (idForm_separatingLeft h (r + s)) hc₀ hnorm (r := r + k) hlt b hb
        let b' : Fin (r + (k + 1)) → Fin (r + s) → K := Fin.snoc b v
        refine ⟨b', ?_, ?_⟩
        · intro i j
          dsimp only [b']
          rcases Fin.eq_castSucc_or_eq_last i with ⟨i₀, rfl⟩ | rfl
          · rcases Fin.eq_castSucc_or_eq_last j with ⟨j₀, rfl⟩ | rfl
            · rw [Fin.snoc_castSucc, Fin.snoc_castSucc, hb]
              simp only [Fin.castSucc_inj]
            · rw [Fin.snoc_castSucc, Fin.snoc_last]
              rw [hbv i₀]
              simp
          · rcases Fin.eq_castSucc_or_eq_last j with ⟨j₀, rfl⟩ | rfl
            · rw [Fin.snoc_last, Fin.snoc_castSucc]
              have h0 : idForm h (r + s) v (b j₀) = 0 :=
                ((idForm_isSymm h (r + s)).eq_iff).2 (hbv j₀)
              rw [h0]
              have hne : (Fin.last (r + k) : Fin (r + k + 1)) ≠ j₀.castSucc :=
                Ne.symm (Fin.castSucc_ne_last j₀)
              simp [hne]
            · rw [Fin.snoc_last, hv]
              simp
        · intro i
          have hc : Fin.castAdd (k + 1) i = Fin.castSucc (Fin.castAdd k i) := Fin.ext rfl
          have hsnoc : b' (Fin.castAdd (k + 1) i) = b (Fin.castAdd k i) := by
            dsimp only [b']
            rw [hc, Fin.snoc_castSucc]
          rw [hsnoc, hpref i]
  obtain ⟨b, hb, hpref⟩ := hExt s le_rfl
  let Qmat : Matrix (Fin (r + s)) (Fin (r + s)) K := frameMat b
  let Qadj : Matrix (Fin (r + s)) (Fin (r + s)) K := frameAdj h b
  have hQadjQmat : Qadj * Qmat = 1 := frameAdj_mul_frameMat hb
  have hQmatQadj : Qmat * Qadj = 1 :=
    (Matrix.mul_eq_one_comm_of_equiv (A := Qadj) (B := Qmat) (Equiv.refl _)).mp hQadjQmat
  let Q : GL (Fin (r + s)) K := ⟨Qmat, Qadj, hQmatQadj, hQadjQmat⟩
  let δ : Kˣ := Matrix.GeneralLinearGroup.det Q
  have hδ : h.bar (δ : K) * (δ : K) = 1 := by
    have hdet := congrArg (fun M : Matrix (Fin (r + s)) (Fin (r + s)) K => M.det) hQadjQmat
    rw [Matrix.det_mul, Matrix.det_one] at hdet
    have hQadjdet : Qadj.det = h.bar (δ : K) := by
      change (((Qmat.map h.bar)ᵀ).det) = h.bar (δ : K)
      rw [Matrix.det_transpose]
      change Matrix.det ((h.bar : K →+* K).mapMatrix Qmat) = h.bar (δ : K)
      rw [← RingHom.map_det]
      congr 1
    have hQmatdet : Qmat.det = (δ : K) := by
      simp [Qmat, δ, Q]
    rwa [hQadjdet, hQmatdet] at hdet
  let j₀ : Fin (r + s) := ⟨r, by omega⟩
  let t : Fin (r + s) → Kˣ := Pi.mulSingle j₀ (δ⁻¹)
  let D : GL (Fin (r + s)) K := TauCeti.diagGL t
  have htdiag : ∀ i : Fin (r + s), h.bar (t i : K) * (t i : K) = 1 := by
    intro i
    by_cases hi : i = j₀
    · subst hi
      simp only [t, Pi.mulSingle_eq_same, Units.val_inv_eq_inv_val, map_inv₀]
      rw [← mul_inv, hδ, inv_one]
    · have hti : t i = 1 := by
        exact Pi.mulSingle_eq_of_ne (M := fun _ : Fin (r + s) => Kˣ) hi (δ⁻¹)
      rw [hti]
      simp
  have hDadj : adj h (D : Matrix (Fin (r + s)) (Fin (r + s)) K) *
      (D : Matrix (Fin (r + s)) (Fin (r + s)) K) = 1 := by
    rw [TauCeti.diagGL_coe, adj, Matrix.diagonal_map (map_zero h.bar),
      Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact htdiag i
  let Tgl : GL (Fin (r + s)) K := Q * D
  have hTprime : Tgl ∈ primeFormUnitary h (idGram K (r + s)) := by
    rw [mem_primeFormUnitary_iff_adj]
    change adj h ((Q : Matrix (Fin (r + s)) (Fin (r + s)) K) *
      (D : Matrix (Fin (r + s)) (Fin (r + s)) K)) *
      ((Q : Matrix (Fin (r + s)) (Fin (r + s)) K) *
        (D : Matrix (Fin (r + s)) (Fin (r + s)) K)) = 1
    calc adj h ((Q : Matrix (Fin (r + s)) (Fin (r + s)) K) *
          (D : Matrix (Fin (r + s)) (Fin (r + s)) K)) *
          ((Q : Matrix (Fin (r + s)) (Fin (r + s)) K) *
            (D : Matrix (Fin (r + s)) (Fin (r + s)) K))
        = (adj h (D : Matrix (Fin (r + s)) (Fin (r + s)) K) *
            adj h (Q : Matrix (Fin (r + s)) (Fin (r + s)) K)) *
            ((Q : Matrix (Fin (r + s)) (Fin (r + s)) K) *
              (D : Matrix (Fin (r + s)) (Fin (r + s)) K)) := by rw [adj_mul]
      _ = adj h (D : Matrix (Fin (r + s)) (Fin (r + s)) K) *
            (adj h (Q : Matrix (Fin (r + s)) (Fin (r + s)) K) *
              (Q : Matrix (Fin (r + s)) (Fin (r + s)) K)) *
            (D : Matrix (Fin (r + s)) (Fin (r + s)) K) := by
          simp only [Matrix.mul_assoc]
      _ = adj h (D : Matrix (Fin (r + s)) (Fin (r + s)) K) *
            (Qadj * Qmat) * (D : Matrix (Fin (r + s)) (Fin (r + s)) K) := by rfl
      _ = adj h (D : Matrix (Fin (r + s)) (Fin (r + s)) K) *
            (D : Matrix (Fin (r + s)) (Fin (r + s)) K) := by rw [hQadjQmat, Matrix.mul_one]
      _ = 1 := hDadj
  have hdetT : Matrix.GeneralLinearGroup.det Tgl = 1 := by
    change Matrix.GeneralLinearGroup.det (Q * D) = 1
    rw [map_mul, TauCeti.det_diagGL, Fintype.prod_pi_mulSingle']
    exact mul_inv_cancel δ
  have hTmem : Tgl ∈ gramSU h (idGram K (r + s)) := by
    rw [mem_gramSU_iff_unitary]
    refine ⟨hTprime, ?_⟩
    have := congrArg Units.val hdetT
    simpa [Matrix.GeneralLinearGroup.val_det_apply] using this
  refine ⟨⟨Tgl, hTmem⟩, ?_⟩
  ext k i
  rw [Matrix.submatrix_apply]
  change (Qmat * (D : Matrix (Fin (r + s)) (Fin (r + s)) K)) k (Fin.castAdd s i) = U k i
  rw [Matrix.mul_apply]
  have hne : Fin.castAdd s i ≠ j₀ := by
    intro h
    have := congrArg Fin.val h
    simp [j₀] at this
    omega
  have hDdiag : ∀ j, (D : Matrix (Fin (r + s)) (Fin (r + s)) K) j (Fin.castAdd s i) =
      if j = Fin.castAdd s i then 1 else 0 := by
    intro j
    rw [TauCeti.diagGL_coe, Matrix.diagonal_apply]
    by_cases hj : j = Fin.castAdd s i
    · subst hj
      have ht : t (Fin.castAdd s i) = 1 :=
        Pi.mulSingle_eq_of_ne (M := fun _ : Fin (r + s) => Kˣ) hne (δ⁻¹)
      simp [ht]
    · simp [hj]
  rw [Finset.sum_eq_single (Fin.castAdd s i)]
  · rw [hDdiag (Fin.castAdd s i), if_pos rfl, mul_one]
    exact congrArg (fun w => w k) (hpref i)
  · intro j _ hjc
    rw [hDdiag j, if_neg hjc, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ (Fin.castAdd s i)) h

end Completion

end Glue

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.PSUTwo
