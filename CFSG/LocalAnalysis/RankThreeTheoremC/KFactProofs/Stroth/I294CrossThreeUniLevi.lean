module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossThreeUniPairs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

namespace CrossUni

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.Open
open CFSG.LocalAnalysis.RankFourTheoremC.TorusU

section Levi

variable {K : Type} [Field K] {σ : K ≃+* K} {n k : ℕ} {S : (Fin n → K) →ₗ[K] (Fin n → K)}
  {u w : Fin k → Fin n → K}

variable (σ u w) in
@[expose] def levi (d e : Fin k → K) : (Fin n → K) →ₗ[K] (Fin n → K) :=
  LinearMap.id + ∑ i, (d i - 1) • (hermL σ (w i)).smulRight (u i) +
    ∑ i, (e i - 1) • (hermL σ (u i)).smulRight (w i)

theorem levi_apply (d e : Fin k → K) (x : Fin n → K) :
    levi σ u w d e x = x + ∑ i, ((d i - 1) * herm σ (w i) x) • u i +
      ∑ i, ((e i - 1) * herm σ (u i) x) • w i := by
  simp [levi, mul_smul]

theorem HypPairs.wu (h : HypPairs σ S u w) (hσinv : ∀ c, σ (σ c) = c) (i j : Fin k) :
    herm σ (w i) (u j) = if i = j then 1 else 0 := by
  rw [herm_conj σ hσinv (u j) (w i), h.uw j i]
  by_cases hij : i = j
  · simp [hij]
  · simp [hij, Ne.symm hij]

theorem herm_w_levi (h : HypPairs σ S u w) (hσinv : ∀ c, σ (σ c) = c) (d e : Fin k → K)
    (j : Fin k) (x : Fin n → K) :
    herm σ (w j) (levi σ u w d e x) = d j * herm σ (w j) x := by
  rw [levi_apply, herm_add_right, herm_add_right, herm_sum_right, herm_sum_right]
  simp only [herm_smul_right, h.wu hσinv, h.ww]
  simp
  ring

theorem herm_u_levi (h : HypPairs σ S u w) (d e : Fin k → K)
    (j : Fin k) (x : Fin n → K) :
    herm σ (u j) (levi σ u w d e x) = e j * herm σ (u j) x := by
  rw [levi_apply, herm_add_right, herm_add_right, herm_sum_right, herm_sum_right]
  simp only [herm_smul_right, h.uw, h.uu]
  simp
  ring

theorem HypPairs.u_ne_zero (h : HypPairs σ S u w) (i : Fin k) : u i ≠ 0 := fun h0 => by
  have := h.uw i i
  rw [h0, herm_zero_left] at this
  simp at this

theorem HypPairs.w_ne_zero (h : HypPairs σ S u w) (i : Fin k) : w i ≠ 0 := fun h0 => by
  have := h.uw i i
  rw [h0, herm_zero_right] at this
  simp at this

theorem levi_one (x : Fin n → K) : levi σ u w (1 : Fin k → K) (1 : Fin k → K) x = x := by
  simp [levi_apply]

theorem levi_comp (h : HypPairs σ S u w) (hσinv : ∀ c, σ (σ c) = c) (d e d' e' : Fin k → K)
    (x : Fin n → K) :
    levi σ u w d e (levi σ u w d' e' x) = levi σ u w (d * d') (e * e') x := by
  rw [levi_apply (x := levi σ u w d' e' x)]
  simp only [herm_w_levi h hσinv, herm_u_levi h]
  conv_lhs => rw [levi_apply (d := d') (e := e')]
  rw [levi_apply (d := d * d') (e := e * e')]
  have hs1 : ∑ i, ((d' i - 1) * herm σ (w i) x) • u i +
      ∑ i, ((d i - 1) * (d' i * herm σ (w i) x)) • u i =
      ∑ i, (((d * d') i - 1) * herm σ (w i) x) • u i := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← add_smul, Pi.mul_apply]
    congr 1
    ring
  have hs2 : ∑ i, ((e' i - 1) * herm σ (u i) x) • w i +
      ∑ i, ((e i - 1) * (e' i * herm σ (u i) x)) • w i =
      ∑ i, (((e * e') i - 1) * herm σ (u i) x) • w i := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← add_smul, Pi.mul_apply]
    congr 1
    ring
  rw [← hs1, ← hs2]
  abel

theorem levi_adjoint (hσinv : ∀ c, σ (σ c) = c) (d e : Fin k → K) (x y : Fin n → K) :
    herm σ (levi σ u w d e x) y =
      herm σ x (levi σ u w (fun i => σ (e i)) (fun i => σ (d i)) y) := by
  rw [levi_apply, levi_apply, herm_add_left, herm_add_left, herm_sum_left, herm_sum_left,
    herm_add_right, herm_add_right, herm_sum_right, herm_sum_right]
  simp only [herm_smul_left, herm_smul_right, map_mul, map_sub, map_one]
  have h1 : ∀ i, σ (herm σ (w i) x) = herm σ x (w i) := fun i =>
    (herm_conj σ hσinv (w i) x).symm
  have h2 : ∀ i, σ (herm σ (u i) x) = herm σ x (u i) := fun i =>
    (herm_conj σ hσinv (u i) x).symm
  simp only [h1, h2]
  have e1 : ∑ i, (σ (d i) - 1) * herm σ x (w i) * herm σ (u i) y =
      ∑ i, (σ (d i) - 1) * herm σ (u i) y * herm σ x (w i) :=
    Finset.sum_congr rfl fun i _ => by ring
  have e2 : ∑ i, (σ (e i) - 1) * herm σ x (u i) * herm σ (w i) y =
      ∑ i, (σ (e i) - 1) * herm σ (w i) y * herm σ x (u i) :=
    Finset.sum_congr rfl fun i _ => by ring
  rw [e1, e2]
  ring

theorem levi_isometry (h : HypPairs σ S u w) (hσinv : ∀ c, σ (σ c) = c) {d e : Fin k → K}
    (hde : ∀ i, σ (e i) * d i = 1) (x y : Fin n → K) :
    herm σ (levi σ u w d e x) (levi σ u w d e y) = herm σ x y := by
  rw [levi_adjoint hσinv, levi_comp h hσinv]
  have h1 : (fun i => σ (e i)) * d = 1 := funext hde
  have h2 : (fun i => σ (d i)) * e = 1 := funext fun i => by
    have := congrArg σ (hde i)
    rw [map_mul, hσinv, map_one] at this
    rw [Pi.mul_apply, mul_comm]
    exact this
  rw [h1, h2, levi_one]

theorem levi_u (h : HypPairs σ S u w) (hσinv : ∀ c, σ (σ c) = c) (d e : Fin k → K) (i : Fin k) :
    levi σ u w d e (u i) = d i • u i := by
  rw [levi_apply]
  simp only [h.wu hσinv, h.uu, mul_zero, zero_smul, Finset.sum_const_zero, add_zero]
  simp [Finset.sum_ite_eq', sub_smul]

theorem levi_w (h : HypPairs σ S u w) (d e : Fin k → K) (i : Fin k) :
    levi σ u w d e (w i) = e i • w i := by
  rw [levi_apply]
  simp only [h.uw, h.ww, mul_zero, zero_smul, Finset.sum_const_zero, add_zero]
  simp [Finset.sum_ite_eq', sub_smul]

theorem eigen_cube (hSp : S ^ 3 = 1) {y : Fin n → K} {a : K} (hy : S y = a • y) (hy0 : y ≠ 0) :
    a ^ 3 = 1 := by
  have h3 : S (S (S y)) = a ^ 3 • y := by
    simp only [hy, map_smul, smul_smul]
    congr 1
    ring
  have h1 : S (S (S y)) = y := by
    have := congrArg (fun T : (Fin n → K) →ₗ[K] (Fin n → K) => T y) hSp
    simpa [pow_succ, Module.End.mul_apply] using this
  rw [h1] at h3
  have h4 : (a ^ 3 - 1) • y = 0 := by rw [sub_smul, ← h3, one_smul, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp h4).resolve_right hy0)

theorem levi_comm (h : HypPairs σ S u w) (hσinv : ∀ c, σ (σ c) = c) (hSp : S ^ 3 = 1)
    (hS : ∀ x y, herm σ (S x) (S y) = herm σ x y) (d e : Fin k → K) (x : Fin n → K) :
    levi σ u w d e (S x) = S (levi σ u w d e x) := by
  choose a ha using h.eu
  choose b hb using h.ew
  have ha3 : ∀ i, a i ^ 3 = 1 := fun i => eigen_cube hSp (ha i) (h.u_ne_zero i)
  have hb3 : ∀ i, b i ^ 3 = 1 := fun i => eigen_cube hSp (hb i) (h.w_ne_zero i)
  have hab : ∀ i, σ (a i) * b i = 1 := fun i => by
    have h1 := hS (u i) (w i)
    rw [ha i, hb i, herm_smul_left, herm_smul_right, h.uw i i, if_pos rfl] at h1
    simpa using h1
  have hab' : ∀ i, a i * σ (b i) = 1 := fun i => by
    have := congrArg σ (hab i)
    rwa [map_mul, hσinv, map_one] at this
  have hS3 : ∀ y, S (S (S y)) = y := fun y => by
    have := congrArg (fun T : (Fin n → K) →ₗ[K] (Fin n → K) => T y) hSp
    simpa [pow_succ, Module.End.mul_apply] using this
  have hS2 : ∀ y z, herm σ y (S z) = herm σ (S (S y)) z := fun y z => by
    have := hS (S (S y)) (S (S (S z)))
    rw [hS3 z, hS3 y] at this
    exact this
  have hsw : ∀ i z, herm σ (w i) (S z) = a i * herm σ (w i) z := fun i z => by
    rw [hS2, hb i, map_smul, hb i, smul_smul, herm_smul_left]
    have : σ (b i * b i) = a i := by
      rw [map_mul]
      calc σ (b i) * σ (b i) = σ (b i) * σ (b i) * a i ^ 3 := by rw [ha3 i, mul_one]
        _ = (a i * σ (b i)) * (a i * σ (b i)) * a i := by ring
        _ = a i := by rw [hab' i]; ring
    rw [this]
  have hsu : ∀ i z, herm σ (u i) (S z) = b i * herm σ (u i) z := fun i z => by
    rw [hS2, ha i, map_smul, ha i, smul_smul, herm_smul_left]
    have : σ (a i * a i) = b i := by
      rw [map_mul]
      calc σ (a i) * σ (a i) = σ (a i) * σ (a i) * b i ^ 3 := by rw [hb3 i, mul_one]
        _ = (σ (a i) * b i) * (σ (a i) * b i) * b i := by ring
        _ = b i := by rw [hab i]; ring
    rw [this]
  rw [levi_apply, levi_apply, map_add, map_add, map_sum, map_sum]
  simp only [hsw, hsu, map_smul, ha, hb, smul_smul]
  have e1 : ∀ i, (d i - 1) * (a i * herm σ (w i) x) = (d i - 1) * herm σ (w i) x * a i :=
    fun i => by ring
  have e2 : ∀ i, (e i - 1) * (b i * herm σ (u i) x) = (e i - 1) * herm σ (u i) x * b i :=
    fun i => by ring
  simp only [e1, e2]

end Levi

section Torus

variable {K : Type} [Field K] {σ : K ≃+* K} {n k p : ℕ} {ζ : K} [NeZero p]
  {S : (Fin n → K) →ₗ[K] (Fin n → K)} {u w : Fin k → Fin n → K}

variable (σ u w) in
@[expose] noncomputable def leviMat (d e : Fin k → K) : Matrix (Fin n) (Fin n) K :=
  LinearMap.toMatrix' (levi σ u w d e)

theorem leviMat_mulVec (d e : Fin k → K) (x : Fin n → K) :
    leviMat σ u w d e *ᵥ x = levi σ u w d e x := by
  rw [← Matrix.toLin'_apply, leviMat, Matrix.toLin'_toMatrix']

theorem charHom_ne_zero (hζ : IsPrimitiveRoot ζ p) (a : Multiplicative (ZMod p)) :
    charHom hζ a ≠ 0 :=
  pow_ne_zero _ (hζ.ne_zero (NeZero.ne p))

@[expose] noncomputable def leviHom (h : HypPairs σ S u w) (hσinv : ∀ c, σ (σ c) = c)
    (hζ : IsPrimitiveRoot ζ p) :
    (Fin k → Multiplicative (ZMod p)) →* Matrix (Fin n) (Fin n) K where
  toFun a := leviMat σ u w (fun i => charHom hζ (a i)) (fun i => (σ (charHom hζ (a i)))⁻¹)
  map_one' := by
    refine Matrix.ext_of_mulVec_single fun i => ?_
    rw [leviMat_mulVec, Matrix.one_mulVec]
    simp [levi_apply]
  map_mul' a b := by
    refine Matrix.ext_of_mulVec_single fun i => ?_
    rw [← Matrix.mulVec_mulVec, leviMat_mulVec, leviMat_mulVec, leviMat_mulVec,
      levi_comp h hσinv]
    have hd : (fun i => charHom hζ ((a * b) i)) =
        (fun i => charHom hζ (a i)) * fun i => charHom hζ (b i) := by
      funext j
      simp
    have he : (fun i => (σ (charHom hζ ((a * b) i)))⁻¹) =
        (fun i => (σ (charHom hζ (a i)))⁻¹) * fun i => (σ (charHom hζ (b i)))⁻¹ := by
      funext j
      simp only [Pi.mul_apply, map_mul]
      ring
    rw [hd, he]

theorem leviHom_mulVec (h : HypPairs σ S u w) (hσinv : ∀ c, σ (σ c) = c)
    (hζ : IsPrimitiveRoot ζ p) (a : Fin k → Multiplicative (ZMod p)) (x : Fin n → K) :
    leviHom h hσinv hζ a *ᵥ x =
      levi σ u w (fun i => charHom hζ (a i)) (fun i => (σ (charHom hζ (a i)))⁻¹) x :=
  leviMat_mulVec _ _ x

theorem scalar_mulVec_eq (c : K) (v : Fin n → K) : Matrix.scalar (Fin n) c *ᵥ v = c • v := by
  ext i
  simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]

theorem det_conjTr_eq (σ : K ≃+* K) (M : Matrix (Fin n) (Fin n) K) :
    (conjTr σ M).det = σ M.det := by
  rw [conjTr, Matrix.det_transpose]
  exact (RingHom.map_det (σ : K →+* K) M).symm

theorem exists_torusHom_pairs (hσinv : ∀ c, σ (σ c) = c) (hζ : IsPrimitiveRoot ζ p)
    (hnorm : ∀ c : K, c ^ p = 1 → σ c * c = 1 → c = 1) (s : GL (Fin n) K)
    (hsiso : conjTr σ (s : Matrix (Fin n) (Fin n) K) * (s : Matrix (Fin n) (Fin n) K) = 1)
    (hs : s ^ 3 = 1)
    (h : HypPairs σ (Matrix.toLin' (s : Matrix (Fin n) (Fin n) K)) u w) :
    ∃ F : (Fin k → Multiplicative (ZMod p)) →* SUid σ n,
      Function.Injective F ∧
      (∀ x, s * ((F x : SUid σ n) : GL (Fin n) K) = ((F x : SUid σ n) : GL (Fin n) K) * s) ∧
      ∀ x, ((F x : SUid σ n) : GL (Fin n) K) ∈ StatedScalars (Fin n) K → F x = 1 := by
  set sM : Matrix (Fin n) (Fin n) K := ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hsM
  have hspow : sM ^ 3 = 1 := by
    have := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) hs
    simpa [hsM] using this
  have hSp : (Matrix.toLin' sM) ^ 3 = 1 := by
    rw [← Matrix.toLin'_pow, hspow, Matrix.toLin'_one]
    rfl
  have hS : ∀ x y, herm σ (Matrix.toLin' sM x) (Matrix.toLin' sM y) = herm σ x y := by
    intro x y
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, herm_mulVec, hsiso, Matrix.one_mulVec]
  set Ψ := leviHom h hσinv hζ with hΨ
  have hc0 : ∀ a : Fin k → Multiplicative (ZMod p), ∀ i, charHom hζ (a i) ≠ 0 := fun a i =>
    charHom_ne_zero hζ (a i)
  have hiso : ∀ a x y, herm σ (Ψ a *ᵥ x) (Ψ a *ᵥ y) = herm σ x y := by
    intro a x y
    rw [hΨ, leviHom_mulVec, leviHom_mulVec]
    refine levi_isometry h hσinv (fun i => ?_) x y
    show σ ((σ (charHom hζ (a i)))⁻¹) * charHom hζ (a i) = 1
    rw [map_inv₀, hσinv]
    exact inv_mul_cancel₀ (hc0 a i)
  have hunit : ∀ a, conjTr σ (Ψ a) * Ψ a = 1 := fun a => conjTr_mul_self_of_isometry σ (hiso a)
  have hpow : ∀ a, (Ψ a) ^ p = 1 := fun a => by
    rw [← map_pow]
    have : a ^ p = 1 := funext fun i => pow_prime_eq_one_zmod (a i)
    rw [this, map_one]
  have hdet : ∀ a, (Ψ a).det = 1 := fun a => by
    have h1 : ((Ψ a).det) ^ p = 1 := by rw [← Matrix.det_pow, hpow, Matrix.det_one]
    have h2 : σ ((Ψ a).det) * (Ψ a).det = 1 := by
      have := congrArg Matrix.det (hunit a)
      rwa [Matrix.det_mul, Matrix.det_one, det_conjTr_eq] at this
    exact hnorm _ h1 h2
  let F : (Fin k → Multiplicative (ZMod p)) →* SUid σ n :=
    (Ψ.toHomUnits).codRestrict (SUid σ n) (fun a => ⟨hdet a, hunit a⟩)
  have hFval : ∀ a, (((F a : SUid σ n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = Ψ a :=
    fun a => rfl
  have hcomm : ∀ a, sM * Ψ a = Ψ a * sM := fun a => by
    refine Matrix.ext_of_mulVec_single fun i => ?_
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hΨ, leviHom_mulVec, leviHom_mulVec]
    have := levi_comm h hσinv hSp hS (fun i => charHom hζ (a i))
      (fun i => (σ (charHom hζ (a i)))⁻¹) (Pi.single i 1)
    simpa [Matrix.toLin'_apply] using this.symm
  have hscal : ∀ a, ((F a : SUid σ n) : GL (Fin n) K) ∈ StatedScalars (Fin n) K → a = 1 := by
    intro a ha
    obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp ha
    have h1 : Ψ a = Matrix.scalar (Fin n) (c : K) := by
      have := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) hc
      rw [← hFval a]
      simpa using this.symm
    have hu : ∀ i, charHom hζ (a i) = c := fun i => by
      have h2 : levi σ u w (fun i => charHom hζ (a i)) (fun i => (σ (charHom hζ (a i)))⁻¹)
          (u i) = (c : K) • u i := by
        rw [← leviHom_mulVec h hσinv hζ, ← hΨ, h1, scalar_mulVec_eq]
      rw [levi_u h hσinv] at h2
      have h3 : (charHom hζ (a i) - c) • u i = 0 := by rw [sub_smul, h2, sub_self]
      exact sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right (h.u_ne_zero i))
    have he : ∀ i, (σ (charHom hζ (a i)))⁻¹ = c := fun i => by
      have h2 : levi σ u w (fun i => charHom hζ (a i)) (fun i => (σ (charHom hζ (a i)))⁻¹)
          (w i) = (c : K) • w i := by
        rw [← leviHom_mulVec h hσinv hζ, ← hΨ, h1, scalar_mulVec_eq]
      rw [levi_w h] at h2
      have h3 : ((σ (charHom hζ (a i)))⁻¹ - c) • w i = 0 := by rw [sub_smul, h2, sub_self]
      exact sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right (h.w_ne_zero i))
    funext i
    have hcp : (charHom hζ (a i)) ^ p = 1 := by
      rw [← map_pow, pow_prime_eq_one_zmod, map_one]
    have hn : σ (charHom hζ (a i)) * charHom hζ (a i) = 1 := by
      have hd : (σ (charHom hζ (a i)))⁻¹ = charHom hζ (a i) := (he i).trans (hu i).symm
      calc σ (charHom hζ (a i)) * charHom hζ (a i)
          = σ (charHom hζ (a i)) * (σ (charHom hζ (a i)))⁻¹ := by rw [hd]
        _ = 1 := mul_inv_cancel₀ ((map_ne_zero σ).2 (hc0 a i))
    exact eq_one_of_charHom_eq_one hζ (hnorm _ hcp hn)
  refine ⟨F, (injective_iff_map_eq_one F).mpr fun a ha => hscal a ?_, fun a => ?_,
    fun a ha => by rw [hscal a ha, map_one]⟩
  · rw [ha]
    exact (StatedScalars (Fin n) K).one_mem
  · apply Units.ext
    simp only [Units.val_mul]
    exact hcomm a

end Torus

end CrossUni

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
