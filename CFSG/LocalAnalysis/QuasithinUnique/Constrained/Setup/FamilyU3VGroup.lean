module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyU3Skew
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyU3Outer

public section

namespace CFSG.QuasithinUnique.Setup.Family

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag

section VAlg

variable {K : Type} [Field K] (σ : K ≃+* K)

theorem map_mul_ringEquiv (M N : Matrix (Fin 3) (Fin 3) K) :
    (M * N).map σ = M.map σ * N.map σ :=
  (σ.toRingHom.mapMatrix).map_mul M N

theorem vMat_map (N : Matrix (Fin 3) (Fin 3) K) (a : K × K) :
    (vMat N a).map σ = 1 + σ a.1 • N.map σ + (σ a.2 + σ a.1 ^ 2 / 2) • (N.map σ * N.map σ) := by
  have h2 : σ (2 : K) = 2 := map_ofNat σ 2
  unfold vMat
  rw [map_add_ringEquiv, map_add_ringEquiv, map_one_ringEquiv, map_smul_ringEquiv,
    map_smul_ringEquiv, map_mul_ringEquiv]
  simp only [map_add, map_div₀, map_pow, h2]

theorem vMat_map_transpose {N : Matrix (Fin 3) (Fin 3) K} (hN : (N.map σ)ᵀ = -N) {a : K × K}
    (ha1 : σ a.1 = a.1) (ha2 : σ a.2 = -a.2) : ((vMat N a).map σ)ᵀ = vMat N (-a) := by
  rw [vMat_map, ha1, ha2]
  unfold vMat
  simp only [Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_smul,
    Matrix.transpose_mul, hN]
  simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg, Prod.fst_neg, Prod.snd_neg, smul_neg,
    neg_sq]
  rw [neg_smul]

theorem vMat_conj {A N : Matrix (Fin 3) (Fin 3) K} (hAN : A * N.map σ = -(N * A)) {a : K × K}
    (ha1 : σ a.1 = a.1) (ha2 : σ a.2 = -a.2) : A * (vMat N a).map σ = vMat N (-a) * A := by
  have hNN : A * (N.map σ * N.map σ) = N * N * A := by
    calc A * (N.map σ * N.map σ) = (A * N.map σ) * N.map σ := by rw [Matrix.mul_assoc]
      _ = -(N * A) * N.map σ := by rw [hAN]
      _ = -(N * (A * N.map σ)) := by rw [Matrix.neg_mul, Matrix.mul_assoc]
      _ = -(N * -(N * A)) := by rw [hAN]
      _ = N * N * A := by rw [Matrix.mul_neg, neg_neg, Matrix.mul_assoc]
  rw [vMat_map, ha1, ha2]
  unfold vMat
  simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, hAN, hNN, Matrix.add_mul,
    Matrix.smul_mul, Matrix.one_mul, Prod.fst_neg, Prod.snd_neg, neg_sq, smul_neg]
  rw [neg_smul]

theorem vMat_eq_scalar {N : Matrix (Fin 3) (Fin 3) K} (hN3 : N * N * N = 0)
    (hN2 : N * N ≠ 0) {a : K × K} {r : K} (h : vMat N a = r • 1) : a = 0 := by
  have hN1 : N * (N * N) = 0 := by rw [← Matrix.mul_assoc]; exact hN3
  set x := a.1 with hx
  set c := a.2 + a.1 ^ 2 / 2 with hc
  have hT : (r - 1) • (1 : Matrix (Fin 3) (Fin 3) K) = x • N + c • (N * N) := by
    unfold vMat at h
    calc (r - 1) • (1 : Matrix (Fin 3) (Fin 3) K) = r • 1 - 1 := by rw [sub_smul, one_smul]
      _ = x • N + c • (N * N) := by rw [← h]; abel
  have hr1 : r = 1 := by
    have h1 : ((r - 1) • (1 : Matrix (Fin 3) (Fin 3) K)) * (N * N) = 0 := by
      rw [hT]
      simp only [Matrix.add_mul, Matrix.smul_mul]
      rw [show N * (N * N) = 0 from hN1, show N * N * (N * N) = 0 by
        rw [Matrix.mul_assoc, hN1, Matrix.mul_zero]]
      simp
    rw [Matrix.smul_mul, Matrix.one_mul] at h1
    rcases smul_eq_zero.1 h1 with h' | h'
    · exact sub_eq_zero.1 h'
    · exact absurd h' hN2
  have hT0 : x • N + c • (N * N) = 0 := by
    rw [← hT, hr1, sub_self, zero_smul]
  have hx0 : x = 0 := by
    have h1 : (x • N + c • (N * N)) * N = 0 := by rw [hT0, Matrix.zero_mul]
    rw [Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, hN3, smul_zero, add_zero] at h1
    rcases smul_eq_zero.1 h1 with h' | h'
    · exact h'
    · exact absurd h' hN2
  have hc0 : c = 0 := by
    rw [hx0, zero_smul, zero_add] at hT0
    rcases smul_eq_zero.1 hT0 with h' | h'
    · exact h'
    · exact absurd h' hN2
  refine Prod.ext hx0 ?_
  have : a.2 = c - a.1 ^ 2 / 2 := by rw [hc]; ring
  rw [this, hc0, ← hx, hx0]
  simp

end VAlg

section VGroup

variable {p : ℕ} [Fact p.Prime] {K F : Type} [Field K] [Field F] [Fintype F] [DecidableEq F]
  [CharP F p] (h : UnitaryFieldData p 1 K) (ι : F →+* K)

theorem exists_unitary_inverted_vgroup (hFcard : Fintype.card F = p) (hp5 : 5 ≤ p)
    (hι : ∀ x, h.bar (ι x) = ι x) (hfix : ∀ m : K, h.bar m = m → ∃ x : F, ι x = m) (A : UI h)
    (hAs : ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)ᵀ =
      ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
    (hAA : ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map h.bar = 1) :
    ∃ v : F × F → ↥(SUI h), v 0 = 1 ∧ (∀ a b, v (a + b) = v a * v b) ∧
      (∀ a, tauU h A (barEquiv h) (v a) = (v a)⁻¹) ∧
      (∀ (a : F × F) (r : Kˣ), ((v a : ↥(SUI h)) : GL (Fin 3) K) =
        GeneralLinearGroup.scalar (Fin 3) r → a = 0) := by
  classical
  have : Finite K := h.finite
  have : Fintype K := Fintype.ofFinite K
  have hp : p.Prime := Fact.out
  have h2 : (2 : K) ≠ 0 := by
    have : CharP K p := h.charP
    exact Ring.two_ne_zero (by rw [ringChar.eq K p]; omega)
  obtain ⟨c, hc⟩ := h.exists_bar_ne
  set ω : K := c - h.bar c with hωdef
  have hω : barEquiv h ω = -ω := by
    rw [hωdef, map_sub, barEquiv_apply, barEquiv_apply, h.bar_bar]
    ring
  have hω0 : ω ≠ 0 := fun h0 => hc (sub_eq_zero.1 h0).symm
  have hσ : ∀ x, barEquiv h (barEquiv h x) = x := h.bar_bar
  have hι' : ∀ x, barEquiv h (ι x) = ι x := hι
  have hfix' : ∀ m : K, barEquiv h m = m → ∃ x : F, ι x = m := hfix
  obtain ⟨N, hN3, hN2, hNs, hAN⟩ := exists_skew_nilpotent (p := p) ι (barEquiv h) hFcard hp5 hσ
    hι' hfix' hω hω0 h2 hAs hAA
  let w : F × F → K × K := fun z => (ι z.1, ω * ι z.2)
  have hw_add : ∀ z z', w (z + z') = w z + w z' := by
    intro z z'
    refine Prod.ext ?_ ?_
    · simp [w]
    · simp [w, mul_add]
  have hw_zero : w 0 = 0 := by simp [w]
  have hdet : ∀ a : K × K, IsUnit (vMat N a).det := fun a => by
    rw [det_vMat h2 hN3 a]
    exact isUnit_one
  let V : K × K → GL (Fin 3) K := fun a => Matrix.GeneralLinearGroup.mk'' (vMat N a) (hdet a)
  have hV : ∀ a, ((V a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = vMat N a := fun a => rfl
  have hVadd : ∀ a b, V (a + b) = V a * V b := fun a b =>
    Units.ext (by rw [Units.val_mul, hV, hV, hV, vMat_add h2 hN3])
  have hV0 : V 0 = 1 := Units.ext (by rw [hV, vMat_zero]; rfl)
  have hVw1 : ∀ z, barEquiv h (w z).1 = (w z).1 := fun z => hι' z.1
  have hVw2 : ∀ z, barEquiv h (w z).2 = -(w z).2 := fun z => by
    simp only [w, map_mul, hω, hι']
    ring
  have hmem : ∀ z, V (w z) ∈ SUI h := by
    intro z
    rw [SUI, mem_gramSU_iff_unitary]
    refine ⟨?_, ?_⟩
    · rw [mem_primeFormUnitary, hV]
      have h1 := vMat_map_transpose (barEquiv h) hNs (hVw1 z) (hVw2 z)
      simp only [Units.val_one, Matrix.mul_one]
      show ((vMat N (w z)).map (barEquiv h))ᵀ * vMat N (w z) = 1
      rw [h1, ← vMat_add h2 hN3, neg_add_cancel, vMat_zero]
    · rw [hV, det_vMat h2 hN3]
  have hconj : ∀ z, (A : GL (Fin 3) K) * glAut (barEquiv h) (V (w z)) * (A : GL (Fin 3) K)⁻¹ =
      V (-(w z)) := by
    intro z
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, coe_glAut, hV, hV]
    have := vMat_conj (barEquiv h) hAN (hVw1 z) (hVw2 z)
    rw [this, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  refine ⟨fun z => ⟨V (w z), hmem z⟩, ?_, ?_, ?_, ?_⟩
  · apply Subtype.ext
    show V (w 0) = 1
    rw [hw_zero, hV0]
  · intro a b
    apply Subtype.ext
    show V (w (a + b)) = V (w a) * V (w b)
    rw [hw_add, hVadd]
  · intro a
    apply Subtype.ext
    have hinv : (V (w a))⁻¹ = V (-(w a)) := by
      apply inv_eq_of_mul_eq_one_right
      rw [← hVadd, add_neg_cancel, hV0]
    show (A : GL (Fin 3) K) * glAut (barEquiv h) (V (w a)) * (A : GL (Fin 3) K)⁻¹ =
      (V (w a))⁻¹
    rw [hinv, hconj]
  · intro a r hr
    have h1 : vMat N (w a) = (r : K) • (1 : Matrix (Fin 3) (Fin 3) K) := by
      have := congrArg (fun M : GL (Fin 3) K => (M : Matrix (Fin 3) (Fin 3) K)) hr
      simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at this
      exact this.trans (smul_one_eq_diagonal _).symm
    have h0 := vMat_eq_scalar hN3 hN2 h1
    have e1 : ι a.1 = 0 := congrArg Prod.fst h0
    have e2 : ω * ι a.2 = 0 := congrArg Prod.snd h0
    have ha1 : a.1 = 0 := ι.injective (by rw [e1, map_zero])
    have ha2 : a.2 = 0 :=
      ι.injective (by rw [map_zero]; exact (mul_eq_zero.1 e2).resolve_left hω0)
    exact Prod.ext ha1 ha2

end VGroup

end CFSG.QuasithinUnique.Setup.Family
