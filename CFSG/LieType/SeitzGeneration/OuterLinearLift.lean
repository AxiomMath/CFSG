module

public import CFSG.LieType.SeitzGeneration.OuterLinearDescent
public import CFSG.RankThree.PartOne.KC.LinearNoninnerPlaneInner
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.PartOne.KCLinComm CFSG.RankThree.PartOne.KCLinPlane

section Groups

theorem exists_pow_of_pow_eq {G : Type*} [CommGroup G] {p n : ℕ} (hcop : Nat.Coprime n p)
    {c δ : G} (h : c ^ n = δ ^ p) : ∃ v : G, v ^ p = c := by
  obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, a * n + b * p = 1 := Nat.isCoprime_iff_coprime.mpr hcop
  have comm_pow : ∀ (x : G) (a : ℤ) (m : ℕ), (x ^ a) ^ m = (x ^ m) ^ a := fun x a m => by
    rw [← zpow_natCast, ← zpow_natCast x m, ← _root_.zpow_mul, ← _root_.zpow_mul, mul_comm]
  refine ⟨δ ^ a * c ^ b, ?_⟩
  have : (n : ℤ) * a + (p : ℤ) * b = 1 := by linarith
  rw [mul_pow, comm_pow δ a p, ← h, comm_pow c b p, ← zpow_natCast c n, ← zpow_natCast c p,
    ← _root_.zpow_mul, ← _root_.zpow_mul, ← _root_.zpow_add, this, zpow_one]

theorem exists_pow_of_coprime_card {G : Type*} [CommGroup G] {p : ℕ}
    (hcop : Nat.Coprime (Nat.card G) p) (c : G) : ∃ v : G, v ^ p = c :=
  ⟨(powCoprime hcop).symm c, by rw [← powCoprime_apply hcop, Equiv.apply_symm_apply]⟩

end Groups

section Lift

variable {n : ℕ} {K : Type} [Field K]

theorem conjAut_toGL (X : SpecialLinearGroup (Fin n) K) :
    conjAut n K (SpecialLinearGroup.toGL X) = MulAut.conj (proj n K X) := by
  ext y
  obtain ⟨Y, rfl⟩ := proj_surjective n K y
  rw [conjAut_proj, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply SpecialLinearGroup.toGL_injective
  rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation, map_mul,
    map_mul, map_inv]

theorem exists_rational_lift [Finite K] {ℓ e p : ℕ} (hp : p.Prime) (hℓ : ℓ.Prime) (he : 1 ≤ e)
    (hK : Nat.card K = ℓ ^ e) (σ : K ≃+* K) (hσ : orderOf σ = p) (hn : 1 ≤ n)
    {g : projectiveSL n K} (hg : fieldAut n K σ g = g) :
    ∃ Ĝ : GL (Fin n) K, conjAut n K Ĝ = MulAut.conj g ∧
      (Ĝ : Matrix (Fin n) (Fin n) K).map σ = Ĝ := by
  obtain ⟨X, rfl⟩ := proj_surjective n K g
  rw [fieldAut_proj] at hg
  have h1 := mem_scalars.mp (proj_eq_proj_iff.mp hg.symm)
  obtain ⟨c, -, hc⟩ := h1
  have hXσ : (X : Matrix (Fin n) (Fin n) K).map σ = (c : K) • (X : Matrix (Fin n) (Fin n) K) := by
    have h2 : SpecialLinearGroup.map σ.toRingHom X =
        X * (X⁻¹ * SpecialLinearGroup.map σ.toRingHom X) := by group
    have h3 := congrArg (fun Z : SpecialLinearGroup (Fin n) K => (Z : Matrix (Fin n) (Fin n) K)) h2
    beta_reduce at h3
    rw [Matrix.SpecialLinearGroup.coe_mul, hc] at h3
    ext i j
    have h4 := congrFun (congrFun h3 i) j
    simp only [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
      Matrix.mul_apply, Matrix.scalar_apply, Matrix.diagonal_apply] at h4
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
    simpa [mul_comm] using h4
  have hX0 : (X : Matrix (Fin n) (Fin n) K) ≠ 0 := by
    intro h0
    have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
    have h1 := X.2
    rw [h0, Matrix.det_zero] at h1
    exact zero_ne_one h1
  obtain ⟨c', hc'0, hc'⟩ := exists_rational_smul hp hℓ he hK σ hσ hX0 hXσ
  refine ⟨GeneralLinearGroup.scalar (Fin n) (Units.mk0 c' hc'0) * SpecialLinearGroup.toGL X, ?_, ?_⟩
  · rw [map_mul, conjAut_scalar, one_mul, conjAut_toGL]
  · have hcoe : ((GeneralLinearGroup.scalar (Fin n) (Units.mk0 c' hc'0) *
        SpecialLinearGroup.toGL X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        c' • (X : Matrix (Fin n) (Fin n) K) := by
      rw [Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.smul_eq_diagonal_mul]
      rfl
    rw [hcoe]
    exact hc'

theorem exists_normalized_lift [Finite K] {k : Subfield K} {p : ℕ} (hp : p.Prime) (σ : K ≃+* K)
    (hk : ∀ x, x ∈ k ↔ σ x = x) (hn : 3 ≤ n) (hpow : ¬ p ∣ n ∨ ¬ p ∣ Nat.card k - 1)
    {g : projectiveSL n K} (hgp : g ^ p = 1) {Ĝ₀ : GL (Fin n) K}
    (hĜ₀ : conjAut n K Ĝ₀ = MulAut.conj g) (hσ₀ : (Ĝ₀ : Matrix (Fin n) (Fin n) K).map σ = Ĝ₀) :
    ∃ Ĝ : GL (Fin n) K, conjAut n K Ĝ = MulAut.conj g ∧
      (Ĝ : Matrix (Fin n) (Fin n) K).map σ = Ĝ ∧ (Ĝ : Matrix (Fin n) (Fin n) K) ^ p = 1 := by
  have h1 : conjAut n K (Ĝ₀ ^ p) = 1 := by rw [map_pow, hĜ₀, ← map_pow, hgp, map_one]
  obtain ⟨c, hc⟩ := (conjAut_eq_one_iff hn _).mp h1
  have hpowσ : ((Ĝ₀ : Matrix (Fin n) (Fin n) K) ^ p).map σ =
      (Ĝ₀ : Matrix (Fin n) (Fin n) K) ^ p := by
    have := Matrix.map_pow (Ĝ₀ : Matrix (Fin n) (Fin n) K) (σ : K →+* K) p
    rw [show (⇑(σ : K →+* K) : K → K) = ⇑σ from rfl, hσ₀] at this
    exact this
  have hcσ : σ (c : K) = c := by
    have hcm : (GeneralLinearGroup.scalar (Fin n) c : GL (Fin n) K) =
        Ĝ₀ ^ p := hc
    have h2 : (scalar (Fin n) (c : K)).map σ = scalar (Fin n) (c : K) := by
      have := congrArg (fun A : GL (Fin n) K => (A : Matrix (Fin n) (Fin n) K)) hcm
      simp only [GeneralLinearGroup.coe_scalar, Units.val_pow_eq_pow_val] at this
      rw [this]
      exact hpowσ
    have h3 := congrFun (congrFun h2 ⟨0, by omega⟩) ⟨0, by omega⟩
    simpa [Matrix.map_apply, Matrix.scalar_apply, Matrix.diagonal_apply] using h3
  set δ : Kˣ := GeneralLinearGroup.det Ĝ₀ with hδ
  have hδp : δ ^ p = c ^ n := by
    have h2 := congrArg GeneralLinearGroup.det hc
    rw [det_scalar_gl_units, map_pow] at h2
    exact h2.symm
  have hδσ : σ (δ : K) = δ := by
    have h2 : σ (Ĝ₀ : Matrix (Fin n) (Fin n) K).det = (Ĝ₀ : Matrix (Fin n) (Fin n) K).det := by
      have h3 := RingHom.map_det (σ : K →+* K) (Ĝ₀ : Matrix (Fin n) (Fin n) K)
      have h4 : (σ : K →+* K).mapMatrix (Ĝ₀ : Matrix (Fin n) (Fin n) K) = Ĝ₀ := hσ₀
      rw [h4] at h3
      exact h3
    simpa [hδ, GeneralLinearGroup.val_det_apply] using h2
  obtain ⟨v, hvσ, hvp⟩ : ∃ v : Kˣ, σ (v : K) = v ∧ v ^ p = c := by
    have hck : (c : K) ∈ k := (hk _).mpr hcσ
    have hδk : (δ : K) ∈ k := (hk _).mpr hδσ
    let f : k →* K := k.subtype.toMonoidHom
    let c' : kˣ := Units.mk0 ⟨c, hck⟩ (fun h => c.ne_zero (congrArg Subtype.val h))
    let δ' : kˣ := Units.mk0 ⟨δ, hδk⟩ (fun h => δ.ne_zero (congrArg Subtype.val h))
    have hc'f : Units.map f c' = c := Units.ext rfl
    have hδ'f : Units.map f δ' = δ := Units.ext rfl
    obtain ⟨v', hv'⟩ : ∃ v' : kˣ, v' ^ p = c' := by
      rcases hpow with h | h
      · refine exists_pow_of_pow_eq (δ := δ') ((Nat.Prime.coprime_iff_not_dvd hp).mpr h).symm ?_
        apply Units.map_injective (f := f) k.subtype.injective
        rw [map_pow, map_pow, hc'f, hδ'f, hδp]
      · refine exists_pow_of_coprime_card ?_ c'
        rw [Nat.card_units]
        exact ((Nat.Prime.coprime_iff_not_dvd hp).mpr h).symm
    refine ⟨Units.map f v', (hk _).mp (v'.val).2, ?_⟩
    rw [← map_pow, hv', hc'f]
  have hcomm : Commute (GeneralLinearGroup.scalar (Fin n) v⁻¹) Ĝ₀ := by
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_mul, GeneralLinearGroup.coe_scalar]
    exact (Matrix.scalar_commute _ (fun r' => Commute.all _ _) _).eq
  refine ⟨GeneralLinearGroup.scalar (Fin n) v⁻¹ * Ĝ₀, ?_, ?_, ?_⟩
  · rw [map_mul, conjAut_scalar, one_mul, hĜ₀]
  · have hcoe : ((GeneralLinearGroup.scalar (Fin n) v⁻¹ * Ĝ₀ : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) = ((v⁻¹ : Kˣ) : K) • (Ĝ₀ : Matrix (Fin n) (Fin n) K) := by
      rw [Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.smul_eq_diagonal_mul]
      rfl
    rw [hcoe]
    ext i j
    have hij : σ ((Ĝ₀ : Matrix (Fin n) (Fin n) K) i j) = (Ĝ₀ : Matrix (Fin n) (Fin n) K) i j := by
      have := congrFun (congrFun hσ₀ i) j
      simpa [Matrix.map_apply] using this
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, hij]
    rw [Units.val_inv_eq_inv_val, map_inv₀, hvσ]
  · rw [← Units.val_pow_eq_pow_val, hcomm.mul_pow, ← map_pow, ← hc, ← map_mul, inv_pow, hvp,
      inv_mul_cancel, map_one, Units.val_one]

end Lift

end CFSG.LieType.SeitzGeneration
