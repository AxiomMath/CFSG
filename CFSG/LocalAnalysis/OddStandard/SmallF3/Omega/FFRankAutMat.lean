module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFRankAutDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2Sim

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Matrix

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private def ffOutFFRankAutMat_Good (d : Fin 6 → ZMod 3)
    (M : Matrix (Fin 6) (Fin 6) (ZMod 3)) : Prop :=
  ∃ c : ZMod 3, (c = 1 ∨ c = -1) ∧ Mᵀ * Matrix.diagonal d * M = c • Matrix.diagonal d

private lemma ffOutFFRankAutMat_sum_sq (d : Fin 6 → ZMod 3) (y : Fin 6 → ZMod 3) :
    (∑ i, d i * (y i) ^ 2) = y ⬝ᵥ (Matrix.diagonal d *ᵥ y) := by
  simp only [dotProduct, Matrix.mulVec_diagonal]
  exact Finset.sum_congr rfl fun i _ => by ring

private lemma ffOutFFRankAutMat_dot_transpose (M : Matrix (Fin 6) (Fin 6) (ZMod 3))
    (y z : Fin 6 → ZMod 3) : (M *ᵥ y) ⬝ᵥ z = y ⬝ᵥ (Mᵀ *ᵥ z) := by
  rw [dotProduct_comm]
  exact (Matrix.dotProduct_transpose_mulVec M y z).symm

private lemma ffOutFFRankAutMat_dot_mul_D (d : Fin 6 → ZMod 3)
    (M : Matrix (Fin 6) (Fin 6) (ZMod 3)) (y : Fin 6 → ZMod 3) :
    (M *ᵥ y) ⬝ᵥ (Matrix.diagonal d *ᵥ (M *ᵥ y)) =
      y ⬝ᵥ ((Mᵀ * Matrix.diagonal d * M) *ᵥ y) := by
  rw [ffOutFFRankAutMat_dot_transpose M y (Matrix.diagonal d *ᵥ (M *ᵥ y))]
  simp only [Matrix.mulVec_mulVec, mul_assoc]

private lemma ffOutFFRankAutMat_isSimilitude
    (b : Module.Basis (Fin 6) (ZMod 3) V)
    {d : Fin 6 → ZMod 3} (hb : ∀ x, Q x = ∑ i, d i * (b.repr x i) ^ 2)
    {M : Matrix (Fin 6) (Fin 6) (ZMod 3)} (hdet : IsUnit M.det) {c : (ZMod 3)ˣ}
    (hEq : Mᵀ * Matrix.diagonal d * M = (c : ZMod 3) • Matrix.diagonal d) :
    IsSimilitude Q (Matrix.toLinearEquiv b M hdet) c := by
  intro v
  change Q (Matrix.toLin b b M v) = (c : ZMod 3) * Q v
  rw [hb (Matrix.toLin b b M v), hb v, Matrix.repr_toLin]
  rw [ffOutFFRankAutMat_sum_sq d (M *ᵥ b.repr v),
    ffOutFFRankAutMat_dot_mul_D d M (b.repr v), hEq, Matrix.smul_mulVec,
    dotProduct_smul, smul_eq_mul, ← ffOutFFRankAutMat_sum_sq d (b.repr v)]

private lemma ffOutFFRankAutMat_det_ne_zero
    (M : Matrix (Fin 6) (Fin 6) (ZMod 3)) {d : Fin 6 → ZMod 3} (hd : ∀ i, d i ≠ 0)
    {c : ZMod 3} (hc : c = 1 ∨ c = -1)
    (hM : Mᵀ * Matrix.diagonal d * M = c • Matrix.diagonal d) : M.det ≠ 0 := by
  have hprod : (∏ i, d i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hd i
  intro hzero
  have hdet := congrArg Matrix.det hM
  simp only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_smul, Matrix.det_diagonal,
    Fintype.card_fin] at hdet
  rw [hzero] at hdet
  simp only [zero_mul, mul_zero] at hdet
  have hc6 : c ^ 6 ≠ 0 := by rcases hc with hc | hc <;> rw [hc] <;> decide
  exact (mul_ne_zero hc6 hprod) hdet.symm

private lemma ffOutFFRankAutMat_unit_of_eq (c : ZMod 3) (hc : c = 1 ∨ c = -1) :
    ∃ u : (ZMod 3)ˣ, (u : ZMod 3) = c := by
  rcases hc with hc | hc
  · exact ⟨1, by rw [hc]; decide⟩
  · exact ⟨-1, by rw [hc]; decide⟩

private noncomputable def ffOutFFRankAutMat_g
    (b : Module.Basis (Fin 6) (ZMod 3) V)
    {d : Fin 6 → ZMod 3} (hb : ∀ x, Q x = ∑ i, d i * (b.repr x i) ^ 2)
    (hd : ∀ i, d i ≠ 0) (M : Matrix (Fin 6) (Fin 6) (ZMod 3))
    (hM : ffOutFFRankAutMat_Good d M) : simGroup Q :=
  let hdet : IsUnit M.det := isUnit_iff_ne_zero.mpr
    (ffOutFFRankAutMat_det_ne_zero M hd hM.choose_spec.1 hM.choose_spec.2)
  ⟨Matrix.toLinearEquiv b M hdet, by
    obtain ⟨c, hc, hEq⟩ := hM
    obtain ⟨u, hu⟩ := ffOutFFRankAutMat_unit_of_eq c hc
    refine ⟨u, ?_⟩
    rw [← hu] at hEq
    exact ffOutFFRankAutMat_isSimilitude b hb hdet hEq⟩

private noncomputable def ffOutFFRankAutMat_cls
    (b : Module.Basis (Fin 6) (ZMod 3) V)
    {d : Fin 6 → ZMod 3} (hb : ∀ x, Q x = ∑ i, d i * (b.repr x i) ^ 2)
    (hd : ∀ i, d i ≠ 0) (M : Matrix (Fin 6) (Fin 6) (ZMod 3))
    (hM : ffOutFFRankAutMat_Good d M) : ProjSim Q :=
  QuotientGroup.mk (ffOutFFRankAutMat_g b hb hd M hM)

private lemma ffOutFFRankAutMat_good_one (d : Fin 6 → ZMod 3) :
    ffOutFFRankAutMat_Good d 1 := by
  refine ⟨1, Or.inl rfl, ?_⟩
  simp

private lemma ffOutFFRankAutMat_good_mul {d : Fin 6 → ZMod 3}
    {M N : Matrix (Fin 6) (Fin 6) (ZMod 3)}
    (hM : ffOutFFRankAutMat_Good d M) (hN : ffOutFFRankAutMat_Good d N) :
    ffOutFFRankAutMat_Good d (M * N) := by
  obtain ⟨c, hc, hMc⟩ := hM
  obtain ⟨e, he, hNe⟩ := hN
  refine ⟨c * e, ?_, ?_⟩
  · rcases hc with hc | hc <;> rcases he with he | he <;> rw [hc, he] <;> decide
  · calc (M * N)ᵀ * Matrix.diagonal d * (M * N)
        = Nᵀ * (Mᵀ * Matrix.diagonal d * M) * N := by
          rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
      _ = Nᵀ * (c • Matrix.diagonal d) * N := by rw [hMc]
      _ = c • (Nᵀ * Matrix.diagonal d * N) := by rw [Matrix.mul_smul, Matrix.smul_mul]
      _ = c • (e • Matrix.diagonal d) := by rw [hNe]
      _ = (c * e) • Matrix.diagonal d := by rw [← smul_smul]

private lemma ffOutFFRankAutMat_good_neg {d : Fin 6 → ZMod 3}
    {M : Matrix (Fin 6) (Fin 6) (ZMod 3)} (hM : ffOutFFRankAutMat_Good d M) :
    ffOutFFRankAutMat_Good d (-M) := by
  obtain ⟨c, hc, hMc⟩ := hM
  refine ⟨c, hc, ?_⟩
  show (-M)ᵀ * Matrix.diagonal d * (-M) = c • Matrix.diagonal d
  rw [Matrix.transpose_neg, neg_mul, neg_mul_neg, hMc]

private lemma ffOutFFRankAutMat_g_one (b : Module.Basis (Fin 6) (ZMod 3) V)
    {d : Fin 6 → ZMod 3} (hb : ∀ x, Q x = ∑ i, d i * (b.repr x i) ^ 2)
    (hd : ∀ i, d i ≠ 0) (h : ffOutFFRankAutMat_Good d 1) :
    ffOutFFRankAutMat_g b hb hd 1 h = 1 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  change Matrix.toLin b b (1 : Matrix (Fin 6) (Fin 6) (ZMod 3)) v =
    (1 : V ≃ₗ[ZMod 3] V) v
  rw [Matrix.toLin_one]
  rfl

private lemma ffOutFFRankAutMat_g_mul (b : Module.Basis (Fin 6) (ZMod 3) V)
    {d : Fin 6 → ZMod 3} (hb : ∀ x, Q x = ∑ i, d i * (b.repr x i) ^ 2)
    (hd : ∀ i, d i ≠ 0) {M N : Matrix (Fin 6) (Fin 6) (ZMod 3)}
    (hM : ffOutFFRankAutMat_Good d M) (hN : ffOutFFRankAutMat_Good d N) :
    ffOutFFRankAutMat_g b hb hd (M * N) (ffOutFFRankAutMat_good_mul hM hN) =
      ffOutFFRankAutMat_g b hb hd M hM * ffOutFFRankAutMat_g b hb hd N hN := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  change Matrix.toLin b b (M * N) v = Matrix.toLin b b M (Matrix.toLin b b N v)
  exact Matrix.toLin_mul_apply (v₁ := b) (v₂ := b) (v₃ := b) (A := M) (B := N) v

private lemma ffOutFFRankAutMat_g_neg (b : Module.Basis (Fin 6) (ZMod 3) V)
    {d : Fin 6 → ZMod 3} (hb : ∀ x, Q x = ∑ i, d i * (b.repr x i) ^ 2)
    (hd : ∀ i, d i ≠ 0) {M : Matrix (Fin 6) (Fin 6) (ZMod 3)}
    (hM : ffOutFFRankAutMat_Good d M) :
    ffOutFFRankAutMat_g b hb hd (-M) (ffOutFFRankAutMat_good_neg hM) =
      ffOutFFRankAutMat_g b hb hd M hM * orthToSim Q (piOrth Q) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  change Matrix.toLin b b (-M) v =
    Matrix.toLin b b M ((piOrth Q : V ≃ₗ[ZMod 3] V) v)
  rw [coe_piOrth_apply]
  let L : Matrix (Fin 6) (Fin 6) (ZMod 3) →ₗ[ZMod 3] V →ₗ[ZMod 3] V := Matrix.toLin b b
  change (L (-M)) v = (L M) (-v)
  calc (L (-M)) v = (-L M) v :=
        congrArg (fun f : V →ₗ[ZMod 3] V => f v) (LinearMap.map_neg L M)
    _ = -(L M v) := rfl
    _ = (L M) (-v) := (LinearMap.map_neg (L M) v).symm

private lemma ffOutFFRankAutMat_cls_proof_irrel (b : Module.Basis (Fin 6) (ZMod 3) V)
    {d : Fin 6 → ZMod 3} (hb : ∀ x, Q x = ∑ i, d i * (b.repr x i) ^ 2)
    (hd : ∀ i, d i ≠ 0) {M : Matrix (Fin 6) (Fin 6) (ZMod 3)}
    (h h' : ffOutFFRankAutMat_Good d M) :
    ffOutFFRankAutMat_cls b hb hd M h = ffOutFFRankAutMat_cls b hb hd M h' := by
  unfold ffOutFFRankAutMat_cls
  apply congrArg QuotientGroup.mk
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  change Matrix.toLin b b M v = Matrix.toLin b b M v
  rfl

private lemma ffOutFFRankAutMat_cls_one (b : Module.Basis (Fin 6) (ZMod 3) V)
    {d : Fin 6 → ZMod 3} (hb : ∀ x, Q x = ∑ i, d i * (b.repr x i) ^ 2)
    (hd : ∀ i, d i ≠ 0) (h : ffOutFFRankAutMat_Good d 1) :
    ffOutFFRankAutMat_cls b hb hd 1 h = 1 := by
  unfold ffOutFFRankAutMat_cls
  rw [ffOutFFRankAutMat_g_one]
  rfl

private lemma ffOutFFRankAutMat_cls_mul (b : Module.Basis (Fin 6) (ZMod 3) V)
    {d : Fin 6 → ZMod 3} (hb : ∀ x, Q x = ∑ i, d i * (b.repr x i) ^ 2)
    (hd : ∀ i, d i ≠ 0) {M N : Matrix (Fin 6) (Fin 6) (ZMod 3)}
    (hM : ffOutFFRankAutMat_Good d M) (hN : ffOutFFRankAutMat_Good d N) :
    ffOutFFRankAutMat_cls b hb hd (M * N) (ffOutFFRankAutMat_good_mul hM hN) =
      ffOutFFRankAutMat_cls b hb hd M hM * ffOutFFRankAutMat_cls b hb hd N hN := by
  unfold ffOutFFRankAutMat_cls
  rw [ffOutFFRankAutMat_g_mul, QuotientGroup.mk_mul]

private lemma ffOutFFRankAutMat_cls_neg (b : Module.Basis (Fin 6) (ZMod 3) V)
    {d : Fin 6 → ZMod 3} (hb : ∀ x, Q x = ∑ i, d i * (b.repr x i) ^ 2)
    (hd : ∀ i, d i ≠ 0) {M : Matrix (Fin 6) (Fin 6) (ZMod 3)}
    (hM : ffOutFFRankAutMat_Good d M) :
    ffOutFFRankAutMat_cls b hb hd (-M) (ffOutFFRankAutMat_good_neg hM) =
      ffOutFFRankAutMat_cls b hb hd M hM := by
  unfold ffOutFFRankAutMat_cls
  rw [ffOutFFRankAutMat_g_neg, QuotientGroup.mk_mul]
  have hpi : (QuotientGroup.mk (orthToSim Q (piOrth Q)) : ProjSim Q) = 1 :=
    (QuotientGroup.eq_one_iff (orthToSim Q (piOrth Q))).mpr
      (mem_piSim_iff.mpr (Or.inr rfl))
  rw [hpi, mul_one]

private lemma ffOutFFRankAutMat_cls_congr (b : Module.Basis (Fin 6) (ZMod 3) V)
    {d : Fin 6 → ZMod 3} (hb : ∀ x, Q x = ∑ i, d i * (b.repr x i) ^ 2)
    (hd : ∀ i, d i ≠ 0) {M N : Matrix (Fin 6) (Fin 6) (ZMod 3)} (h : M = N)
    (hM : ffOutFFRankAutMat_Good d M) (hN : ffOutFFRankAutMat_Good d N) :
    ffOutFFRankAutMat_cls b hb hd M hM = ffOutFFRankAutMat_cls b hb hd N hN := by
  subst h
  exact ffOutFFRankAutMat_cls_proof_irrel b hb hd hM hN

private lemma ffOutFFRankAutMat_cls_neg' (b : Module.Basis (Fin 6) (ZMod 3) V)
    {d : Fin 6 → ZMod 3} (hb : ∀ x, Q x = ∑ i, d i * (b.repr x i) ^ 2)
    (hd : ∀ i, d i ≠ 0) {M : Matrix (Fin 6) (Fin 6) (ZMod 3)}
    (hM : ffOutFFRankAutMat_Good d M) (h : ffOutFFRankAutMat_Good d (-M)) :
    ffOutFFRankAutMat_cls b hb hd (-M) h = ffOutFFRankAutMat_cls b hb hd M hM := by
  rw [ffOutFFRankAutMat_cls_proof_irrel b hb hd h (ffOutFFRankAutMat_good_neg hM)]
  exact ffOutFFRankAutMat_cls_neg b hb hd hM

private lemma ffOutFFRankAutMat_cls_mul' (b : Module.Basis (Fin 6) (ZMod 3) V)
    {d : Fin 6 → ZMod 3} (hb : ∀ x, Q x = ∑ i, d i * (b.repr x i) ^ 2)
    (hd : ∀ i, d i ≠ 0) {M N : Matrix (Fin 6) (Fin 6) (ZMod 3)}
    (hM : ffOutFFRankAutMat_Good d M) (hN : ffOutFFRankAutMat_Good d N)
    (h : ffOutFFRankAutMat_Good d (M * N)) :
    ffOutFFRankAutMat_cls b hb hd (M * N) h =
      ffOutFFRankAutMat_cls b hb hd M hM * ffOutFFRankAutMat_cls b hb hd N hN := by
  rw [ffOutFFRankAutMat_cls_proof_irrel b hb hd h (ffOutFFRankAutMat_good_mul hM hN)]
  exact ffOutFFRankAutMat_cls_mul b hb hd hM hN

private lemma ffOutFFRankAutMat_cls_inj (b : Module.Basis (Fin 6) (ZMod 3) V)
    {d : Fin 6 → ZMod 3} (hb : ∀ x, Q x = ∑ i, d i * (b.repr x i) ^ 2)
    (hd : ∀ i, d i ≠ 0) {M N : Matrix (Fin 6) (Fin 6) (ZMod 3)}
    (hM : ffOutFFRankAutMat_Good d M) (hN : ffOutFFRankAutMat_Good d N)
    (h : ffOutFFRankAutMat_cls b hb hd M hM = ffOutFFRankAutMat_cls b hb hd N hN) :
    M = N ∨ M = -N := by
  have hmem : (ffOutFFRankAutMat_g b hb hd M hM)⁻¹ *
      ffOutFFRankAutMat_g b hb hd N hN ∈ piSim Q := QuotientGroup.eq.mp h
  rcases mem_piSim_iff.mp hmem with h1 | h1
  · left
    have hg : ffOutFFRankAutMat_g b hb hd M hM =
        ffOutFFRankAutMat_g b hb hd N hN := by
      have h2 := congrArg (fun x : simGroup Q =>
        ffOutFFRankAutMat_g b hb hd M hM * x) h1
      rw [mul_one, ← mul_assoc, mul_inv_cancel, one_mul] at h2
      exact h2.symm
    apply (Matrix.toLin b b).injective
    exact congrArg (fun f : V ≃ₗ[ZMod 3] V => f.toLinearMap)
      (congrArg (fun x : simGroup Q => (x : V ≃ₗ[ZMod 3] V)) hg)
  · right
    have hg : ffOutFFRankAutMat_g b hb hd N hN =
        ffOutFFRankAutMat_g b hb hd M hM * orthToSim Q (piOrth Q) := by
      have h2 := congrArg (fun x : simGroup Q =>
        ffOutFFRankAutMat_g b hb hd M hM * x) h1
      rw [← mul_assoc, mul_inv_cancel, one_mul] at h2
      exact h2
    have hg2 : ffOutFFRankAutMat_g b hb hd N hN =
        ffOutFFRankAutMat_g b hb hd (-M) (ffOutFFRankAutMat_good_neg hM) := by
      rw [hg, ← ffOutFFRankAutMat_g_neg b hb hd hM]
    have hNM : N = -M := by
      apply (Matrix.toLin b b).injective
      exact congrArg (fun f : V ≃ₗ[ZMod 3] V => f.toLinearMap)
        (congrArg (fun x : simGroup Q => (x : V ≃ₗ[ZMod 3] V)) hg2)
    rw [hNM]
    exact (neg_neg M).symm

theorem ffRA_exists_table (b : Module.Basis (Fin 6) (ZMod 3) V) {d : Fin 6 → ZMod 3}
    (hb : ∀ x, Q x = ∑ i, d i * (b.repr x i) ^ 2) (hd : ∀ i, d i ≠ 0)
    {n : ℕ} {flag : Bool} {bound : ℕ} (hs : FFRASide n d flag bound) :
    ∃ (e : Fin n → ProjSim Q) (one : Fin n) (mul : Fin n → Fin n → Fin n)
      (𝓛 : Set (Finset (Fin n))),
      Function.Injective e ∧ e one = 1 ∧ (∀ i j, e (mul i j) = e i * e j) ∧
      {one} ∈ 𝓛 ∧ (∀ H ∈ 𝓛, H.card ≤ bound) ∧
      ∀ H ∈ 𝓛, ∀ x : Fin n, x ∉ H → (if flag then mul x x = one else mul x x ∈ H) →
        (∀ h ∈ H, mul x h = mul h x) → H ∪ H.image (mul x) ∈ 𝓛 := by
  obtain ⟨T, mul, one, 𝓛, hTone, hsim, hmul, hdistinct, hL0, hL1, hL2⟩ := hs
  have hsim' : ∀ i : Fin n, ffOutFFRankAutMat_Good d (T i) := fun i => hsim i
  refine ⟨fun i => ffOutFFRankAutMat_cls b hb hd (T i) (hsim' i), one, mul, 𝓛,
    ?_, ?_, ?_, hL0, hL1, hL2⟩
  · intro i j hij
    exact hdistinct i j
      (ffOutFFRankAutMat_cls_inj b hb hd (M := T i) (N := T j) (hsim' i) (hsim' j) hij)
  · dsimp only
    rw [ffOutFFRankAutMat_cls_congr b hb hd hTone (hsim' one)
      (ffOutFFRankAutMat_good_one d)]
    exact ffOutFFRankAutMat_cls_one b hb hd (ffOutFFRankAutMat_good_one d)
  · intro i j
    dsimp only
    rcases hmul i j with h | h
    · rw [ffOutFFRankAutMat_cls_congr b hb hd h (hsim' (mul i j))
        (ffOutFFRankAutMat_good_mul (hsim' i) (hsim' j))]
      exact ffOutFFRankAutMat_cls_mul' b hb hd (hsim' i) (hsim' j)
        (ffOutFFRankAutMat_good_mul (hsim' i) (hsim' j))
    · rw [ffOutFFRankAutMat_cls_congr b hb hd (M := T (mul i j)) (N := -(T i * T j)) h
        (hsim' (mul i j))
        (ffOutFFRankAutMat_good_neg (ffOutFFRankAutMat_good_mul (hsim' i) (hsim' j)))]
      rw [ffOutFFRankAutMat_cls_neg' b hb hd (M := T i * T j)
        (ffOutFFRankAutMat_good_mul (hsim' i) (hsim' j))
        (ffOutFFRankAutMat_good_neg (ffOutFFRankAutMat_good_mul (hsim' i) (hsim' j)))]
      exact ffOutFFRankAutMat_cls_mul' b hb hd (M := T i) (N := T j) (hsim' i) (hsim' j)
        (ffOutFFRankAutMat_good_mul (hsim' i) (hsim' j))

end CFSG.OddStandard.SmallF3.Omega
