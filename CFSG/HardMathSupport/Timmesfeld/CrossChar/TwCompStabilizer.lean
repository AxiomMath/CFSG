module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompAlcove
public import CFSG.HardMathSupport.Timmesfeld.Steinberg.PrimeChar

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar.KacData

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped Matrix

variable {τ : Tag} (K : KacData τ)

theorem height_θ : height K.θ = K.h - 1 := by
  unfold height KacData.h
  ring

theorem height_bounds (hK : K.Facts) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    height γ ≤ K.h - 1 ∧ -(K.h - 1) ≤ height γ := by
  have hle : ∀ δ, IsRoot τ δ → (∀ j, 0 ≤ δ j) → height δ ≤ K.h - 1 := fun δ hδ h0 => by
    rw [← K.height_θ]
    exact Finset.sum_le_sum fun j _ => hK.le_θ δ hδ h0 j
  have hh : 0 ≤ K.h - 1 := by
    rw [← K.height_θ]
    exact Finset.sum_nonneg fun j _ => K.θ_nonneg j
  rcases hγ.nonneg_or_nonpos with h | h
  · have h0 : 0 ≤ height γ := Finset.sum_nonneg fun j _ => h j
    exact ⟨hle γ hγ h, by linarith⟩
  · have h' := hle (-γ) (IsRoot.neg hγ) fun j => by
      simp only [Pi.neg_apply]
      linarith [h j]
    rw [height_neg] at h'
    have h0 : height γ ≤ 0 := Finset.sum_nonpos fun j _ => h j
    exact ⟨by linarith, by linarith⟩

theorem dot_bounds (hK : K.Facts) {p : ℕ} {μ : Fin τ.rank → ℤ} (hμ : K.IsNormal p μ)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    ((∀ j, 0 ≤ γ j) → 0 ≤ γ ⬝ᵥ μ ∧ γ ⬝ᵥ μ ≤ p) ∧
      ((∀ j, γ j ≤ 0) → -(p : ℤ) ≤ γ ⬝ᵥ μ ∧ γ ⬝ᵥ μ ≤ 0) := by
  have pos : ∀ δ, IsRoot τ δ → (∀ j, 0 ≤ δ j) → 0 ≤ δ ⬝ᵥ μ ∧ δ ⬝ᵥ μ ≤ p := by
    intro δ hδ h0
    have hle := hK.le_θ δ hδ h0
    refine ⟨Finset.sum_nonneg fun j _ => mul_nonneg (h0 j) (hμ.1 j), ?_⟩
    exact (Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hle j) (hμ.1 j)).trans hμ.2
  refine ⟨pos γ hγ, fun h => ?_⟩
  have := pos (-γ) (IsRoot.neg hγ) fun j => by
    simp only [Pi.neg_apply]
    linarith [h j]
  rw [neg_dotProduct] at this
  constructor <;> linarith [this.1, this.2]

theorem wall_simple (hK : K.Facts) {p : ℕ} {μ : Fin τ.rank → ℤ} (hμ : K.IsNormal p μ)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) {m n : ℤ} (hdot : γ ⬝ᵥ μ = m + p * n) (hm : 0 ≤ m)
    (hx : height γ - K.h * n < 0) : m = 0 := by
  have hh := K.h_pos
  have hb := K.height_bounds hK hγ
  have hd := K.dot_bounds hK hμ hγ
  have hp : (0 : ℤ) ≤ p := Int.natCast_nonneg p
  rcases hγ.nonneg_or_nonpos with h | h
  · have h1 : 0 < height γ := (IsRoot.height_pos_iff hγ).2 h
    have hn : 1 ≤ n := by
      by_contra hn
      push Not at hn
      nlinarith
    have := (hd.1 h).2
    nlinarith
  · have hn : 0 ≤ n := by
      by_contra hn
      push Not at hn
      nlinarith
    have := (hd.2 h).2
    nlinarith

theorem wall_affine (hK : K.Facts) {p : ℕ} {μ : Fin τ.rank → ℤ} (hμ : K.IsNormal p μ)
    {δ : Fin τ.rank → ℤ} (hδ : IsRoot τ δ) {m n : ℤ} (hdot : δ ⬝ᵥ μ = m + p * n) (hm : m ≤ p)
    (hx : K.h < height δ - K.h * n) : m = p := by
  have hh := K.h_pos
  have hb := K.height_bounds hK hδ
  have hd := K.dot_bounds hK hμ hδ
  have hp : (0 : ℤ) ≤ p := Int.natCast_nonneg p
  rcases hδ.nonneg_or_nonpos with h | h
  · have hn : n ≤ -1 := by
      by_contra hn
      push Not at hn
      nlinarith
    have := (hd.1 h).1
    nlinarith
  · have h1 : height δ < 0 := (IsRoot.height_neg_iff hδ).2 h
    have hn : n ≤ -2 := by
      by_contra hn
      push Not at hn
      nlinarith
    have := (hd.2 h).1
    nlinarith

theorem height_sub_ne_zero (hK : K.Facts) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (n : ℤ) :
    height γ - K.h * n ≠ 0 := by
  intro h0
  have hh := K.h_pos
  have hb := K.height_bounds hK hγ
  have hne := hγ.height_ne_zero
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · nlinarith
  · exact hne (by linarith)
  · nlinarith

omit K in
theorem smul_eq_sum_single (w : WeylGroup τ) (v : Fin τ.rank → ℤ) :
    w • v = ∑ k, v k • (w • (Pi.single k 1 : Fin τ.rank → ℤ)) := by
  have hv : v = ∑ k, v k • (Pi.single k 1 : Fin τ.rank → ℤ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  rw [Finset.smul_sum]
  simp only [smul_comm w]

omit K in
theorem height_smul_eq (w : WeylGroup τ) (v : Fin τ.rank → ℤ) :
    height (w • v) = v ⬝ᵥ fun k => height (w • (Pi.single k 1 : Fin τ.rank → ℤ)) := by
  rw [smul_eq_sum_single]
  simp only [height, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, dotProduct, Finset.mul_sum]
  exact Finset.sum_comm

omit K in
theorem smul_dot_eq {p : ℕ} {μ ν : Fin τ.rank → ℤ} {w : WeylGroup τ}
    (hν : ∀ k, (w • (Pi.single k 1 : Fin τ.rank → ℤ)) ⬝ᵥ μ = μ k + p * ν k)
    (v : Fin τ.rank → ℤ) : (w • v) ⬝ᵥ μ = v ⬝ᵥ μ + p * (v ⬝ᵥ ν) := by
  rw [smul_eq_sum_single, sum_dotProduct]
  simp only [smul_dotProduct, smul_eq_mul, hν]
  simp only [dotProduct, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by ring

@[expose] def muChar (p : ℕ) (μ : Fin τ.rank → ℤ) :
    Multiplicative (Fin τ.rank → ℤ) →* Steinberg.Zp p :=
  Steinberg.pChar fun j => ((μ j : ℤ) : ZMod p)

omit K in
theorem pPairing_cast (p : ℕ) (μ v : Fin τ.rank → ℤ) :
    Steinberg.pPairing (fun j => ((μ j : ℤ) : ZMod p)) v = ((v ⬝ᵥ μ : ℤ) : ZMod p) := by
  simp only [Steinberg.pPairing, dotProduct, Int.cast_sum, Int.cast_mul]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

omit K in
theorem dvd_of_mem_charStabilizer {p : ℕ} {μ : Fin τ.rank → ℤ} {w : WeylGroup τ}
    (hw : w ∈ charStabilizer (muChar p μ)) (v : Fin τ.rank → ℤ) :
    (p : ℤ) ∣ (w • v) ⬝ᵥ μ - v ⬝ᵥ μ := by
  have h := hw v
  rw [muChar, Steinberg.pChar_apply, Steinberg.pChar_apply, Steinberg.Zp.ofAdd_eq_ofAdd_iff,
    pPairing_cast, pPairing_cast] at h
  exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 h.symm

omit K in
theorem mem_kernelRoots_muChar {p : ℕ} [NeZero p] {μ α : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (h : (p : ℤ) ∣ α ⬝ᵥ μ) : α ∈ kernelRoots (muChar p μ) := by
  refine Steinberg.mem_kernelRoots_pChar.2 ⟨hα, ?_⟩
  rw [pPairing_cast]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 h

@[expose] noncomputable def xv (w : WeylGroup τ) (ν : Fin τ.rank → ℤ) : Fin τ.rank → ℤ :=
  fun j => height (w • (Pi.single j 1 : Fin τ.rank → ℤ)) - K.h * ν j

theorem xv_mul {p : ℕ} {μ ν : Fin τ.rank → ℤ} {w : WeylGroup τ}
    (hν : ∀ k, (w • (Pi.single k 1 : Fin τ.rank → ℤ)) ⬝ᵥ μ = μ k + p * ν k)
    (u : WeylGroup τ) (d : Fin τ.rank → ℤ)
    (hd : ∀ j, (u • (Pi.single j 1 : Fin τ.rank → ℤ)) ⬝ᵥ μ = μ j + p * d j) :
    (∀ j, ((w * u) • (Pi.single j 1 : Fin τ.rank → ℤ)) ⬝ᵥ μ =
        μ j + p * ((u • (Pi.single j 1 : Fin τ.rank → ℤ)) ⬝ᵥ ν + d j)) ∧
      K.xv (w * u) (fun j => (u • (Pi.single j 1 : Fin τ.rank → ℤ)) ⬝ᵥ ν + d j) =
        fun j => (u • (Pi.single j 1 : Fin τ.rank → ℤ)) ⬝ᵥ K.xv w ν - K.h * d j := by
  refine ⟨fun j => ?_, funext fun j => ?_⟩
  · rw [mul_smul, smul_dot_eq hν, hd]
    ring
  · have e : K.xv w ν = (fun k => height (w • (Pi.single k 1 : Fin τ.rank → ℤ))) - K.h • ν := by
      funext k
      simp [xv]
    simp only [xv, mul_smul]
    rw [height_smul_eq, e, dotProduct_sub, dotProduct_smul, smul_eq_mul]
    ring

omit K in
theorem simple_smul_single (i j : Fin τ.rank) :
    simple τ i • (Pi.single j 1 : Fin τ.rank → ℤ) =
      Pi.single j 1 - τ.cartan i j • (Pi.single i 1 : Fin τ.rank → ℤ) := by
  have hs : ∑ k, τ.cartan i k * (Pi.single j 1 : Fin τ.rank → ℤ) k = τ.cartan i j := by
    simp [Pi.single_apply]
  rw [simple_smul, reflect, hs]

omit K in
theorem dualReflect_dualReflect (i : Fin τ.rank) (μ : Fin τ.rank → ℤ) :
    dualReflect i (dualReflect i μ) = μ := by
  funext j
  simp only [dualReflect]
  rw [τ.cartan_self i]
  ring

omit K in
theorem simple_smul_dot (i : Fin τ.rank) (β μ : Fin τ.rank → ℤ) :
    (simple τ i • β) ⬝ᵥ μ = β ⬝ᵥ dualReflect i μ := by
  have h := reflect_dot_dualReflect i β (dualReflect i μ)
  rw [dualReflect_dualReflect] at h
  rw [simple_smul, h]

theorem G_mulVec_cartan_row (hsl : ∀ i, τ.symmetrizer i i = 1) (i k : Fin τ.rank) :
    (K.G *ᵥ fun j => τ.cartan i j) k = K.N * (Pi.single i 1 : Fin τ.rank → ℤ) k := by
  have h := K.symmetrizer_mul_cartan_dot i (Pi.single k 1)
  rw [hsl i, one_mul, K.dot_G_comm, single_dotProduct, one_mul] at h
  rw [h]
  simp [Pi.single_apply, eq_comm]

theorem N_dvd_G_delta (hsl : ∀ i, τ.symmetrizer i i = 1) (w : WeylGroup τ) :
    ∀ (lam : Fin τ.rank → ℤ) (k : Fin τ.rank), (K.N : ℤ) ∣
      (K.G *ᵥ fun j => (w • (Pi.single j 1 : Fin τ.rank → ℤ)) ⬝ᵥ lam - lam j) k := by
  obtain ⟨l, rfl⟩ := (coxeterSystem τ).wordProd_surjective w
  induction l with
  | nil =>
    intro lam k
    have e : (fun j => ((coxeterSystem τ).wordProd [] • (Pi.single j 1 : Fin τ.rank → ℤ)) ⬝ᵥ
        lam - lam j) = 0 := by
      funext j
      simp [single_dotProduct]
    rw [e, Matrix.mulVec_zero]
    exact dvd_zero _
  | cons i l ih =>
    intro lam k
    have e : (fun j => ((coxeterSystem τ).wordProd (i :: l) • (Pi.single j 1 : Fin τ.rank → ℤ)) ⬝ᵥ
        lam - lam j) = (fun j => ((coxeterSystem τ).wordProd l • (Pi.single j 1 : Fin τ.rank → ℤ))
          ⬝ᵥ dualReflect i lam - dualReflect i lam j) - lam i • (fun j => τ.cartan i j) := by
      funext j
      rw [CoxeterSystem.wordProd_cons, mul_smul, simple_smul_dot]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, dualReflect]
      ring
    rw [e, Matrix.mulVec_sub, Matrix.mulVec_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      K.G_mulVec_cartan_row hsl]
    exact dvd_sub (ih _ k) (dvd_mul_of_dvd_right (dvd_mul_right _ _) _)

omit K in
theorem simple_mem_kernelWeylGroup {p : ℕ} [NeZero p] {μ : Fin τ.rank → ℤ} {i : Fin τ.rank}
    (hi : μ i = 0) : simple τ i ∈ kernelWeylGroup (muChar p μ) := by
  refine Subgroup.subset_closure ⟨1, i, ?_, by group⟩
  rw [one_smul]
  refine mem_kernelRoots_muChar (isRoot_single τ i) ?_
  rw [single_dotProduct, one_mul, hi]
  exact dvd_zero _

theorem mem_kernelWeylGroup_of_isNormal (hK : K.Facts) {p : ℕ} (hp : 0 < p)
    {μ : Fin τ.rank → ℤ} (hμ : K.IsNormal p μ) (hsl : ∀ i, τ.symmetrizer i i = 1)
    (hΩ : ∀ j, K.θ j = 1 → ∃ k, ¬ (K.N : ℤ) ∣ p * K.G k j) {w : WeylGroup τ}
    (hw : w ∈ charStabilizer (muChar p μ)) : w ∈ kernelWeylGroup (muChar p μ) := by
  have : NeZero p := ⟨hp.ne'⟩
  have hh := K.h_pos
  have hN := K.N_pos
  have hκ := K.κ_pos
  have hpz : (0 : ℤ) < p := by exact_mod_cast hp
  have hhc : ((K.h.toNat : ℕ) : ℤ) = K.h := Int.toNat_of_nonneg hh.le
  have hsumθ : ∑ i, K.θ i = K.h - 1 := K.height_θ
  suffices H : ∀ n : ℕ, ∀ (w : WeylGroup τ) (ν : Fin τ.rank → ℤ),
      w ∈ charStabilizer (muChar p μ) →
      (∀ k, (w • (Pi.single k 1 : Fin τ.rank → ℤ)) ⬝ᵥ μ = μ k + p * ν k) →
      (K.Q K.h.toNat (K.xv w ν)).toNat < n → w ∈ kernelWeylGroup (muChar p μ) by
    have hdv := dvd_of_mem_charStabilizer hw
    choose ν hν using fun k => hdv (Pi.single k 1 : Fin τ.rank → ℤ)
    refine H _ w ν hw (fun k => ?_) (Nat.lt_succ_self _)
    have := hν k
    rw [single_dotProduct, one_mul] at this
    linarith
  intro n
  induction n with
  | zero => exact fun _ _ _ _ h => absurd h (Nat.not_lt_zero _)
  | succ n ih =>
  intro w ν hw hν hn
  have hQ0 := K.Q_nonneg K.h.toNat (K.xv w ν)
  have hroot : ∀ v, IsRoot τ v → IsRoot τ (w • v) := fun v hv => IsRoot.smul hv w
  have hθx : K.θ ⬝ᵥ K.xv w ν = height (w • K.θ) - K.h * (K.θ ⬝ᵥ ν) := by
    rw [height_smul_eq]
    simp only [xv, dotProduct, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by ring
  by_cases hneg : ∃ i, K.xv w ν i < 0
  ·
    obtain ⟨i, hi⟩ := hneg
    have hμi : μ i = 0 := K.wall_simple hK hμ (hroot _ (isRoot_single τ i)) (hν i) (hμ.1 i) hi
    have hs := simple_mem_kernelWeylGroup (p := p) hμi
    obtain ⟨hν2, hx2⟩ := K.xv_mul hν (simple τ i) 0 fun j => by
      rw [simple_smul_single, sub_dotProduct, smul_dotProduct, single_dotProduct,
        single_dotProduct, hμi]
      simp
    have hx2' : K.xv (w * simple τ i)
        (fun j => (simple τ i • (Pi.single j 1 : Fin τ.rank → ℤ)) ⬝ᵥ ν + (0 : Fin τ.rank → ℤ) j) =
        dualReflect i (K.xv w ν) := by
      rw [hx2]
      funext j
      rw [simple_smul_single, sub_dotProduct, smul_dotProduct, single_dotProduct,
        single_dotProduct]
      simp [dualReflect]
    have hQ := K.symmetrizer_mul_Q_reflect K.h.toNat i (K.xv w ν)
    rw [← hx2', hhc] at hQ
    have hd := symmetrizer_pos τ i
    have hpos : 0 < 2 * K.h * K.N * K.h * -(K.xv w ν i) :=
      mul_pos (mul_pos (mul_pos (mul_pos two_pos hh) hN) hh) (by linarith)
    have hQ0' := K.Q_nonneg K.h.toNat (K.xv (w * simple τ i)
        (fun j => (simple τ i • (Pi.single j 1 : Fin τ.rank → ℤ)) ⬝ᵥ ν + (0 : Fin τ.rank → ℤ) j))
    have hlt : K.Q K.h.toNat (K.xv (w * simple τ i)
        (fun j => (simple τ i • (Pi.single j 1 : Fin τ.rank → ℤ)) ⬝ᵥ ν + (0 : Fin τ.rank → ℤ) j)) <
        K.Q K.h.toNat (K.xv w ν) := by
      nlinarith
    have hmem := ih (w * simple τ i) _ (mul_mem hw (kernelWeylGroup_le hs)) hν2 (by omega)
    have := mul_mem hmem (inv_mem hs)
    rwa [mul_inv_cancel_right] at this
  push Not at hneg
  by_cases haff : K.h < K.θ ⬝ᵥ K.xv w ν
  ·
    have hθdot := smul_dot_eq hν K.θ
    have hθμ : K.θ ⬝ᵥ μ = p :=
      K.wall_affine hK hμ (hroot _ K.isRoot_θ) hθdot hμ.2 (by rwa [hθx] at haff)
    have hs : rootReflection K.θ ∈ kernelWeylGroup (muChar p μ) :=
      rootReflection_mem_kernelWeylGroup (mem_kernelRoots_muChar K.isRoot_θ (by rw [hθμ]))
    have hsθ : ∀ j, rootReflection K.θ • (Pi.single j 1 : Fin τ.rank → ℤ) =
        Pi.single j 1 - K.c j • K.θ := fun j => by
      rw [rootReflection_smul K.isRoot_θ, K.corootPair_θ, dotProduct_single, mul_one]
    obtain ⟨hν2, hx2⟩ := K.xv_mul hν (rootReflection K.θ) (-K.c) fun j => by
      rw [hsθ, sub_dotProduct, smul_dotProduct, single_dotProduct, hθμ, smul_eq_mul]
      simp only [one_mul, Pi.neg_apply]
      ring
    have hx2' : K.xv (w * rootReflection K.θ)
        (fun j => (rootReflection K.θ • (Pi.single j 1 : Fin τ.rank → ℤ)) ⬝ᵥ ν + (-K.c) j) =
        K.affineReflect K.h.toNat (K.xv w ν) := by
      rw [hx2]
      funext j
      rw [hsθ, sub_dotProduct, smul_dotProduct, single_dotProduct, affineReflect, hhc]
      simp only [one_mul, Pi.neg_apply, smul_eq_mul, Pi.sub_apply, Pi.smul_apply]
      ring
    have hQ := K.κ_mul_Q_affine K.h.toNat (K.xv w ν)
    rw [← hx2', hhc] at hQ
    have hpos : 0 < 2 * K.h * K.N * K.h * (K.θ ⬝ᵥ K.xv w ν - K.h) :=
      mul_pos (mul_pos (mul_pos (mul_pos two_pos hh) hN) hh) (by linarith)
    have hQ0' := K.Q_nonneg K.h.toNat (K.xv (w * rootReflection K.θ)
        (fun j => (rootReflection K.θ • (Pi.single j 1 : Fin τ.rank → ℤ)) ⬝ᵥ ν + (-K.c) j))
    have hlt : K.Q K.h.toNat (K.xv (w * rootReflection K.θ)
        (fun j => (rootReflection K.θ • (Pi.single j 1 : Fin τ.rank → ℤ)) ⬝ᵥ ν + (-K.c) j)) <
        K.Q K.h.toNat (K.xv w ν) := by
      nlinarith
    have hmem := ih (w * rootReflection K.θ) _ (mul_mem hw (kernelWeylGroup_le hs)) hν2
      (by omega)
    have := mul_mem hmem (inv_mem hs)
    rwa [mul_inv_cancel_right] at this
  push Not at haff
  have hx0 : ∀ i, 1 ≤ K.xv w ν i := fun i => by
    have h1 : K.xv w ν i ≠ 0 := K.height_sub_ne_zero hK (hroot _ (isRoot_single τ i)) (ν i)
    have h3 : 0 < K.xv w ν i := lt_of_le_of_ne (hneg i) (Ne.symm h1)
    omega
  have hterm : ∀ i ∈ Finset.univ, 0 ≤ K.θ i * (K.xv w ν i - 1) := fun i _ =>
    mul_nonneg (K.θ_nonneg i) (by linarith [hx0 i])
  have hθlt : K.θ ⬝ᵥ K.xv w ν ≠ K.h := by
    have h1 := K.height_sub_ne_zero hK (hroot _ K.isRoot_θ) (K.θ ⬝ᵥ ν + 1)
    rw [hθx]
    intro e
    exact h1 (by linear_combination e)
  have hsum0 : ∑ i, K.θ i * (K.xv w ν i - 1) = 0 := by
    have e : ∑ i, K.θ i * (K.xv w ν i - 1) = K.θ ⬝ᵥ K.xv w ν - ∑ i, K.θ i := by
      simp only [dotProduct, mul_sub, mul_one, Finset.sum_sub_distrib]
    have h1 := Finset.sum_nonneg hterm
    have h2 : K.θ ⬝ᵥ K.xv w ν < K.h := lt_of_le_of_ne haff hθlt
    rw [e, hsumθ] at h1 ⊢
    omega
  have hx1 : ∀ i, K.xv w ν i = 1 := fun i => by
    have := (Finset.sum_eq_zero_iff_of_nonneg hterm).1 hsum0 i (Finset.mem_univ i)
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h (hK.θ_pos i).ne'
    · linarith
  have hHt : ∀ i, height (w • (Pi.single i 1 : Fin τ.rank → ℤ)) = 1 + K.h * ν i := fun i => by
    have := hx1 i
    simp only [xv] at this
    linarith
  have hνb : ∀ i, -1 ≤ ν i ∧ ν i ≤ 0 := fun i => by
    have hb := K.height_bounds hK (hroot _ (isRoot_single τ i))
    rw [hHt] at hb
    constructor
    · by_contra hc
      push Not at hc
      nlinarith
    · by_contra hc
      push Not at hc
      nlinarith
  by_cases hall : ∀ i, ν i = 0
  · have hw1 : w = 1 := eq_one_of_forall_height_pos fun i => by
      rw [hHt, hall]
      norm_num
    rw [hw1]
    exact one_mem _
  exfalso
  push Not at hall
  obtain ⟨j, hj⟩ := hall
  have hνj : ν j = -1 := by
    have := hνb j
    omega
  have hHθ : height (w • K.θ) = (K.h - 1) + K.h * (K.θ ⬝ᵥ ν) := by
    rw [height_smul_eq]
    simp only [hHt, dotProduct, mul_add, mul_one, Finset.sum_add_distrib, Finset.mul_sum]
    rw [hsumθ]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by ring
  have hb := K.height_bounds hK (hroot _ K.isRoot_θ)
  have hθν : -1 ≤ K.θ ⬝ᵥ ν := by
    by_contra hc
    push Not at hc
    nlinarith
  have hsplit : K.θ ⬝ᵥ ν = K.θ j * ν j + ∑ i ∈ Finset.univ.erase j, K.θ i * ν i := by
    rw [dotProduct, ← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
  have hrest : ∀ i ∈ Finset.univ.erase j, K.θ i * ν i ≤ 0 := fun i _ =>
    mul_nonpos_of_nonneg_of_nonpos (K.θ_nonneg i) (hνb i).2
  have hsr := Finset.sum_nonpos hrest
  have hθj : K.θ j = 1 := by
    have := hK.θ_pos j
    rw [hνj] at hsplit
    nlinarith
  have hsr0 : ∑ i ∈ Finset.univ.erase j, K.θ i * ν i = 0 := by
    rw [hνj, hθj] at hsplit
    linarith
  have hν0 : ∀ i, i ≠ j → ν i = 0 := fun i hi => by
    have := (Finset.sum_eq_zero_iff_of_nonpos hrest).1 hsr0 i
      (Finset.mem_erase.2 ⟨hi, Finset.mem_univ i⟩)
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h (hK.θ_pos i).ne'
    · exact h
  obtain ⟨k, hk⟩ := hΩ j hθj
  apply hk
  have hd := K.N_dvd_G_delta hsl w μ k
  have e : (fun l => (w • (Pi.single l 1 : Fin τ.rank → ℤ)) ⬝ᵥ μ - μ l) =
      (-(p : ℤ)) • (Pi.single j 1 : Fin τ.rank → ℤ) := by
    funext l
    rw [hν l]
    by_cases hl : l = j
    · subst hl
      simp [hνj]
    · simp [hν0 l hl, hl]
  have e2 : (K.G *ᵥ ((-(p : ℤ)) • (Pi.single j 1 : Fin τ.rank → ℤ))) k = -(p * K.G k j) := by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    ring
  rw [e, e2, dvd_neg] at hd
  exact hd

theorem charStabilizer_eq_kernelWeylGroup (hK : K.Facts) {p : ℕ} (hp : 0 < p)
    (hsl : ∀ i, τ.symmetrizer i i = 1)
    (hΩ : ∀ j, K.θ j = 1 → ∃ k, ¬ (K.N : ℤ) ∣ p * K.G k j)
    (χ : Multiplicative (Fin τ.rank → ℤ) →* Steinberg.Zp p) :
    charStabilizer χ = kernelWeylGroup χ := by
  have : NeZero p := ⟨hp.ne'⟩
  set lam : Fin τ.rank → ℤ :=
    fun j => ((Steinberg.Zp.toAdd (χ (Multiplicative.ofAdd (Pi.single j 1)))).val : ℤ) with hlam
  obtain ⟨w₀, μ, hw₀, hμ⟩ := K.exists_normal p hp lam
  have hconj : IsCharConj (muChar p μ) χ w₀⁻¹ := by
    intro v
    have hb : (fun j => Steinberg.Zp.toAdd (χ (Multiplicative.ofAdd (Pi.single j 1)))) =
        fun j => ((lam j : ℤ) : ZMod p) := by
      funext j
      simp [hlam]
    rw [inv_inv, Steinberg.eq_pChar χ, muChar, Steinberg.pChar_apply, Steinberg.pChar_apply,
      Steinberg.Zp.ofAdd_eq_ofAdd_iff, hb, pPairing_cast, pPairing_cast]
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).2 (hw₀ v)
  rw [charStabilizer_eq_map hconj, kernelWeylGroup_eq_map hconj]
  congr 1
  exact le_antisymm (fun w hw => K.mem_kernelWeylGroup_of_isNormal hK hp hμ hsl hΩ hw)
    kernelWeylGroup_le

omit K in
theorem pChar_injective {p : ℕ} {b c : Fin τ.rank → ZMod p}
    (h : ∀ v, Steinberg.pChar b (Multiplicative.ofAdd v) = Steinberg.pChar c (Multiplicative.ofAdd v)) :
    b = c := by
  funext j
  have hj := h (Pi.single j 1)
  rw [Steinberg.pChar_apply, Steinberg.pChar_apply, Steinberg.Zp.ofAdd_eq_ofAdd_iff] at hj
  have e := Steinberg.pPairing_zsmul_single b 1 j
  have e' := Steinberg.pPairing_zsmul_single c 1 j
  rw [one_smul, Int.cast_one, mul_one] at e e'
  rw [← e, ← e', hj]

theorem exists_pAct_isNormal {p : ℕ} (hp : 0 < p) (b : Fin τ.rank → ZMod p) :
    ∃ μ : Fin τ.rank → ℤ, K.IsNormal p μ ∧ ∃ σ : List (Fin τ.rank),
      Steinberg.pAct σ (fun j => ((μ j : ℤ) : ZMod p)) = b := by
  have : NeZero p := ⟨hp.ne'⟩
  obtain ⟨w₀, μ, hw₀, hμ⟩ := K.exists_normal p hp fun j => ((b j).val : ℤ)
  obtain ⟨σ, hσ⟩ := (coxeterSystem τ).wordProd_surjective w₀⁻¹
  refine ⟨μ, hμ, σ, pChar_injective fun v => ?_⟩
  rw [Steinberg.pChar_pAct, hσ, inv_inv, Steinberg.pChar_apply, Steinberg.pChar_apply,
    Steinberg.Zp.ofAdd_eq_ofAdd_iff, pPairing_cast]
  have hb : b = fun j => (((b j).val : ℤ) : ZMod p) := by
    funext j
    simp
  conv_rhs => rw [hb, pPairing_cast]
  exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).2 (by
    have := hw₀ v
    rwa [← dvd_neg, neg_sub] at this)

end CFSG.HardMathSupport.Timmesfeld.CrossChar.KacData

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


theorem hΩ_E8 (p : ℕ) : ∀ j, kacE8.θ j = 1 → ∃ k, ¬ (kacE8.N : ℤ) ∣ p * kacE8.G k j := by
  have key : ∀ j : Fin 8, (![2, 3, 4, 6, 5, 4, 3, 2] : Fin 8 → ℤ) j ≠ 1 := by decide
  exact fun j hj => absurd hj (key j)

theorem hΩ_E7 (p : ℕ) (hp : ¬ (2 : ℤ) ∣ p) :
    ∀ j, kacE7.θ j = 1 → ∃ k, ¬ (kacE7.N : ℤ) ∣ p * kacE7.G k j := by
  have key : ∀ j : Fin 7, (![2, 2, 3, 4, 3, 2, 1] : Fin 7 → ℤ) j = 1 →
      (![4, 7, 8, 12, 9, 6, 3] : Fin 7 → ℤ) j = 3 := by decide
  refine fun j hj => ⟨(1 : Fin 7), fun h => hp ?_⟩
  have h3 : kacE7.G (1 : Fin 7) j = 3 := key j hj
  have hN : kacE7.N = 2 := rfl
  rw [h3, hN] at h
  exact (Int.Prime.dvd_mul' (by norm_num) h).resolve_right (by norm_num)

theorem hΩ_E6 (p : ℕ) (hp : ¬ (3 : ℤ) ∣ p) :
    ∀ j, kacE6.θ j = 1 → ∃ k, ¬ (kacE6.N : ℤ) ∣ p * kacE6.G k j := by
  have key : ∀ j : Fin 6, (![1, 2, 2, 3, 2, 1] : Fin 6 → ℤ) j = 1 →
      ¬ (3 : ℤ) ∣ (![4, 3, 5, 6, 4, 2] : Fin 6 → ℤ) j := by decide
  refine fun j hj => ⟨(0 : Fin 6), fun h => ?_⟩
  have hN : kacE6.N = 3 := rfl
  rw [hN] at h
  rcases (Int.Prime.dvd_mul' (by norm_num) h) with h1 | h1
  · exact hp h1
  · exact key j hj h1

theorem charStabilizer_eq_kernelWeylGroup_E8_five_affine
    (χ : Multiplicative (Fin Tag.E8.rank → ℤ) →* Steinberg.Zp 5) :
    charStabilizer χ = kernelWeylGroup χ :=
  kacE8.charStabilizer_eq_kernelWeylGroup facts_E8 (by norm_num) (by decide) (hΩ_E8 5) χ

theorem charStabilizer_eq_kernelWeylGroup_E8_seven_affine
    (χ : Multiplicative (Fin Tag.E8.rank → ℤ) →* Steinberg.Zp 7) :
    charStabilizer χ = kernelWeylGroup χ :=
  kacE8.charStabilizer_eq_kernelWeylGroup facts_E8 (by norm_num) (by decide) (hΩ_E8 7) χ

theorem charStabilizer_eq_kernelWeylGroup_E7_five_affine
    (χ : Multiplicative (Fin Tag.E7.rank → ℤ) →* Steinberg.Zp 5) :
    charStabilizer χ = kernelWeylGroup χ :=
  kacE7.charStabilizer_eq_kernelWeylGroup facts_E7 (by norm_num) (by decide)
    (hΩ_E7 5 (by decide)) χ

theorem charStabilizer_eq_kernelWeylGroup_E7_seven_affine
    (χ : Multiplicative (Fin Tag.E7.rank → ℤ) →* Steinberg.Zp 7) :
    charStabilizer χ = kernelWeylGroup χ :=
  kacE7.charStabilizer_eq_kernelWeylGroup facts_E7 (by norm_num) (by decide)
    (hΩ_E7 7 (by decide)) χ

theorem charStabilizer_eq_kernelWeylGroup_E6_five_affine
    (χ : Multiplicative (Fin Tag.E6.rank → ℤ) →* Steinberg.Zp 5) :
    charStabilizer χ = kernelWeylGroup χ :=
  kacE6.charStabilizer_eq_kernelWeylGroup facts_E6 (by norm_num) (by decide)
    (hΩ_E6 5 (by decide)) χ
end CFSG.HardMathSupport.Timmesfeld.CrossChar
