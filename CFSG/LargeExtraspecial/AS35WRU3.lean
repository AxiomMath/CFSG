module

public import CFSG.ClassicalGroups.UnitaryFlag.HyperbolicData

public section

namespace CFSG.LargeExtraspecial

open Subgroup Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

namespace AS35W

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

@[expose] noncomputable def rk1U3 (u w : HypIndex 1 1 → K) :
    Matrix (HypIndex 1 1) (HypIndex 1 1) K :=
  LinearMap.toMatrix' ((hypForm h 1 1 w).smulRight u)

theorem rk1U3_mulVec (u w x : HypIndex 1 1 → K) :
    rk1U3 h u w *ᵥ x = hypForm h 1 1 w x • u := by
  rw [rk1U3, LinearMap.toMatrix'_mulVec, LinearMap.smulRight_apply]

theorem card_dvd_card_centralizer_U3_of_family {A : hypSU h 1 1} {G : Type} [AddCommGroup G]
    [Finite G] (hpG : ∀ a : G, p • a = 0)
    (N : G →+ Matrix (HypIndex 1 1) (HypIndex 1 1) K)
    (hNN : ∀ a b x, N a *ᵥ (N b *ᵥ x) = 0)
    (hskew : ∀ a x y, hypForm h 1 1 (N a *ᵥ x) y + hypForm h 1 1 x (N a *ᵥ y) = 0)
    (hcomm : ∀ a x, N a *ᵥ (((A : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K)
      *ᵥ x) = ((A : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) *ᵥ
        (N a *ᵥ x))
    (hinj : ∀ a, (∀ x, N a *ᵥ x = 0) → a = 0) :
    Nat.card G ∣ Nat.card (centralizer ({hypProj h 1 1 A} : Set (hypPSU h 1 1))) := by
  classical
  have hp : p.Prime := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := h.charP
  set Am : Matrix (HypIndex 1 1) (HypIndex 1 1) K :=
    ((A : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) with hAm
  have hext : ∀ M₁ M₂ : Matrix (HypIndex 1 1) (HypIndex 1 1) K, (∀ x, M₁ *ᵥ x = M₂ *ᵥ x) →
      M₁ = M₂ := fun M₁ M₂ hM =>
    Matrix.toLin'.injective (LinearMap.ext fun x => by
      rw [Matrix.toLin'_apply, Matrix.toLin'_apply, hM])
  have hNN' : ∀ a b, N a * N b = 0 := fun a b =>
    hext _ _ fun x => by rw [← Matrix.mulVec_mulVec, hNN, Matrix.zero_mulVec]
  set M : G → Matrix (HypIndex 1 1) (HypIndex 1 1) K := fun a => 1 + N a with hM
  have hMmul : ∀ a b, M a * M b = M (a + b) := by
    intro a b
    simp only [hM, add_mul, mul_add, one_mul, mul_one, hNN', map_add, add_zero]
    abel
  have hM0 : M 0 = 1 := by simp [hM]
  have hMpow : ∀ (n : ℕ) a, M a ^ n = M (n • a) := by
    intro n a
    induction n with
    | zero => rw [pow_zero, zero_nsmul, hM0]
    | succ n ih => rw [pow_succ, ih, hMmul, succ_nsmul]
  have hdet : ∀ a, (M a).det = 1 := by
    intro a
    have h1 : (M a).det ^ p = 1 := by
      rw [← det_pow, hMpow, hpG, hM0, det_one]
    have h2 : ((M a).det - 1) ^ p = 0 := by
      rw [sub_pow_char, h1, one_pow, sub_self]
    exact sub_eq_zero.1 ((pow_eq_zero_iff hp.ne_zero).1 h2)
  have hMv : ∀ a v, M a *ᵥ v = v + N a *ᵥ v := fun a v => by
    rw [hM, add_mulVec, one_mulVec]
  have hiso : ∀ a x y, hypForm h 1 1 (M a *ᵥ x) (M a *ᵥ y) = hypForm h 1 1 x y := by
    intro a x y
    have h1 := hskew a x y
    have h2 : hypForm h 1 1 (N a *ᵥ x) (N a *ᵥ y) = 0 := by
      have := hskew a x (N a *ᵥ y)
      rwa [hNN, map_zero, add_zero] at this
    simp only [hMv, map_add, LinearMap.add_apply]
    linear_combination h1 + h2
  let Φ : Multiplicative G →* hypSU h 1 1 :=
    { toFun := fun a => ⟨⟨M (Multiplicative.toAdd a), M (-Multiplicative.toAdd a),
          by rw [hMmul, add_neg_cancel, hM0], by rw [hMmul, neg_add_cancel, hM0]⟩,
        mem_gramSU_iff_isometry.2 ⟨hiso _, hdet _⟩⟩
      map_one' := Subtype.ext (Units.ext hM0)
      map_mul' := fun a b => Subtype.ext (Units.ext (hMmul _ _).symm) }
  set ψ := (hypProj h 1 1).comp Φ
  have hψ : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have hmem : Φ a ∈ hypScalars h 1 1 := by
      rw [← ker_hypProj]
      exact ha
    obtain ⟨c, -, -, hc⟩ := mem_normOneScalars.1 hmem
    have hMc : M (Multiplicative.toAdd a) = (c : K) • 1 := by
      have := congrArg (fun g : GL (HypIndex 1 1) K => Units.val g) hc
      simp only [GeneralLinearGroup.coe_scalar, scalar_apply] at this
      rw [smul_one_eq_diagonal]
      exact this
    have hNa : N (Multiplicative.toAdd a) = ((c : K) - 1) • 1 := by
      rw [sub_smul, one_smul, ← hMc, hM, add_sub_cancel_left]
    have hsq := hNN' (Multiplicative.toAdd a) (Multiplicative.toAdd a)
    rw [hNa, smul_mul_smul_comm, Matrix.one_mul] at hsq
    have hc1 : ((c : K) - 1) * ((c : K) - 1) = 0 := by
      have := congrFun (congrFun hsq (Sum.inl 0)) (Sum.inl 0)
      simpa using this
    have hc1' : (c : K) - 1 = 0 := mul_self_eq_zero.1 hc1
    exact hinj (Multiplicative.toAdd a) fun x => by
      rw [hNa, hc1', zero_smul, Matrix.zero_mulVec]
  have hle : ψ.range ≤ centralizer ({hypProj h 1 1 A} : Set (hypPSU h 1 1)) := by
    rintro _ ⟨a, rfl⟩
    rw [mem_centralizer_singleton_iff]
    change hypProj h 1 1 (Φ a) * hypProj h 1 1 A = hypProj h 1 1 A * hypProj h 1 1 (Φ a)
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    apply Units.ext
    change M (Multiplicative.toAdd a) * Am = Am * M (Multiplicative.toAdd a)
    refine hext _ _ fun x => ?_
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hMv, hMv, Matrix.mulVec_add, hcomm]
  have hcard : Nat.card ψ.range = Nat.card G := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv]
    rfl
  rw [← hcard]
  exact Subgroup.card_dvd_of_le hle

abbrev iE : HypIndex 1 1 := Sum.inl 0

abbrev iW : HypIndex 1 1 := Sum.inr (Sum.inl 0)

abbrev iF : HypIndex 1 1 := Sum.inr (Sum.inr 0)

variable (K) in
@[expose] def dU3Diag : HypIndex 1 1 → K :=
  Sum.elim (fun _ => -1) (Sum.elim (fun _ => 1) (fun _ => -1))

variable (K) in
@[expose] noncomputable def dU3Mat : Matrix (HypIndex 1 1) (HypIndex 1 1) K :=
  Matrix.diagonal (dU3Diag K)

theorem dU3Mat_mul_self : dU3Mat K * dU3Mat K = 1 := by
  rw [dU3Mat, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext a
  rcases a with i | i | i <;> simp [dU3Diag]

theorem det_dU3Mat : (dU3Mat K).det = 1 := by
  rw [dU3Mat, det_diagonal]
  simp [Fintype.prod_sum_type, dU3Diag]

theorem dU3Diag_partner (a : HypIndex 1 1) :
    h.bar (dU3Diag K a) * dU3Diag K (hypPartner a) = 1 := by
  rcases a with i | i | i <;> simp [dU3Diag]

theorem dU3_iso (x y : HypIndex 1 1 → K) :
    hypForm h 1 1 (dU3Mat K *ᵥ x) (dU3Mat K *ᵥ y) = hypForm h 1 1 x y := by
  rw [hypForm_apply, hypForm_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [dU3Mat, mulVec_diagonal, mulVec_diagonal, map_mul]
  have := dU3Diag_partner h a
  linear_combination (h.bar (x a) * y (hypPartner a)) * this

@[expose] noncomputable def dU3 : hypSU h 1 1 :=
  ⟨⟨dU3Mat K, dU3Mat K, dU3Mat_mul_self, dU3Mat_mul_self⟩,
    mem_gramSU_iff_isometry.2 ⟨dU3_iso h, det_dU3Mat⟩⟩

@[expose] noncomputable def psu3Inv : hypPSU h 1 1 := hypProj h 1 1 (dU3 h)

theorem orderOf_psu3Inv (hp2 : p ≠ 2) : orderOf (psu3Inv h) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K p := h.charP
  apply orderOf_eq_prime
  · rw [psu3Inv, ← map_pow]
    have h1 : dU3 h ^ 2 = 1 := Subtype.ext (Units.ext (by
      rw [sq]
      exact dU3Mat_mul_self))
    rw [h1, map_one]
  · intro h1
    have hmem : dU3 h ∈ hypScalars h 1 1 := by
      rw [← ker_hypProj]
      exact h1
    obtain ⟨c, -, -, hc⟩ := mem_normOneScalars.1 hmem
    have hE := congrArg (fun g : GL (HypIndex 1 1) K =>
      (g : Matrix (HypIndex 1 1) (HypIndex 1 1) K) iE iE) hc
    have hW := congrArg (fun g : GL (HypIndex 1 1) K =>
      (g : Matrix (HypIndex 1 1) (HypIndex 1 1) K) iW iW) hc
    simp [dU3, dU3Mat, dU3Diag] at hE hW
    have h2 : ((2 : ℕ) : K) = 0 := by
      rw [Nat.cast_ofNat]
      linear_combination hW - hE
    have hp2' := (CharP.cast_eq_zero_iff K p 2).1 h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_two).1 hp2')

variable (K) in
@[expose] def vE : HypIndex 1 1 → K := Pi.single iE 1

theorem hypForm_vE_left (x : HypIndex 1 1 → K) : hypForm h 1 1 (vE K) x = x iF := by
  rw [hypForm_apply, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp [vE]

theorem hypForm_vE_right (x : HypIndex 1 1 → K) : hypForm h 1 1 x (vE K) = h.bar (x iF) := by
  rw [hypForm_apply, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp [vE]

theorem dU3Mat_mulVec_vE : dU3Mat K *ᵥ vE K = -vE K := by
  funext a
  rw [dU3Mat, mulVec_diagonal]
  rcases a with i | i | i <;> simp [vE, dU3Diag]

theorem dU3Mat_mulVec_iF (x : HypIndex 1 1 → K) : (dU3Mat K *ᵥ x) iF = -x iF := by
  rw [dU3Mat, mulVec_diagonal]
  simp [dU3Diag]

@[expose] noncomputable def rootU3 : h.traceZero →+ Matrix (HypIndex 1 1) (HypIndex 1 1) K where
  toFun μ := (μ : K) • rk1U3 h (vE K) (vE K)
  map_zero' := by simp
  map_add' a b := by simp [add_smul]

theorem rootU3_mulVec (μ : h.traceZero) (x : HypIndex 1 1 → K) :
    rootU3 h μ *ᵥ x = ((μ : K) * x iF) • vE K := by
  simp only [rootU3, AddMonoidHom.coe_mk, ZeroHom.coe_mk, smul_mulVec, rk1U3_mulVec,
    hypForm_vE_left, smul_smul]

theorem dvd_card_centralizer_psu3Inv [Finite K] :
    p ^ f ∣ Nat.card (centralizer ({psu3Inv h} : Set (hypPSU h 1 1))) := by
  have : CharP K p := h.charP
  have htr : ∀ μ : h.traceZero, (μ : K) + h.bar μ = 0 := fun μ => (h.mem_traceZero).1 μ.2
  have hvF : vE K iF = 0 := by simp [vE]
  have hG := card_dvd_card_centralizer_U3_of_family h (A := dU3 h) (G := h.traceZero)
    (fun μ => Subtype.ext (by simp [nsmul_eq_mul, CharP.cast_eq_zero])) (rootU3 h)
    (fun a b x => by rw [rootU3_mulVec, rootU3_mulVec, Pi.smul_apply, hvF]; simp)
    (fun μ x y => by
      rw [rootU3_mulVec, rootU3_mulVec, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
        hypForm_vE_left, LinearMap.map_smul, hypForm_vE_right, smul_eq_mul, smul_eq_mul,
        map_mul]
      linear_combination (h.bar (x iF) * y iF) * htr μ)
    (fun μ x => by
      change rootU3 h μ *ᵥ (dU3Mat K *ᵥ x) = dU3Mat K *ᵥ (rootU3 h μ *ᵥ x)
      rw [rootU3_mulVec, rootU3_mulVec, dU3Mat_mulVec_iF, Matrix.mulVec_smul,
        dU3Mat_mulVec_vE, smul_neg, ← neg_smul, mul_neg])
    (fun μ hμ => by
      have h1 := congrFun (hμ (Pi.single iF 1)) iE
      rw [rootU3_mulVec] at h1
      simpa [vE] using h1)
  rwa [h.card_traceZero] at hG

end AS35W

end CFSG.LargeExtraspecial
