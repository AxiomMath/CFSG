module

public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.TOdd.SL2Pair
public import CFSG.ClassicalInvolution.ModelFacts.G2D4SL2Lin
public import CFSG.RankThree.PartTwo.Sec11.Item1118Res3ProofSL2

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.TOdd

open CFSG.ClassicalInvolution.G2D4Models CFSG.RankThree.PartOne.CTP
open scoped MatrixGroups

section Center

variable {X : Type} [Field X]

theorem threeB_sl2_central {Y : SL(2, X)} (hY : ∀ A : SL(2, X), Y * A = A * Y) :
    Y = 1 ∨ Y = -1 := by
  have hu := congrArg (fun A : SL(2, X) => (A : Matrix (Fin 2) (Fin 2) X)) (hY (u2 1))
  have hl := congrArg (fun A : SL(2, X) => (A : Matrix (Fin 2) (Fin 2) X)) (hY (l2 1))
  simp only [Matrix.SpecialLinearGroup.coe_mul] at hu hl
  obtain ⟨s, hs⟩ := scalar_of_commute_u2_l2 _ hu hl
  have hdet : s * s = 1 := by
    have h := Y.2
    rw [hs] at h
    rw [Matrix.det_smul, Matrix.det_one, Fintype.card_fin] at h
    linear_combination h
  rcases mul_self_eq_one_iff.mp hdet with h | h
  · left
    exact Subtype.ext (by rw [hs, h, one_smul]; rfl)
  · right
    exact Subtype.ext (by
      rw [hs, h, neg_smul, one_smul, Matrix.SpecialLinearGroup.coe_neg]
      rfl)

end Center

section GL2

variable {X : Type} [Field X]

theorem threeB_scalar_of_glConjSL_eq_self {D : GL (Fin 2) X}
    (h : ∀ A : SL(2, X), glConjSL D A = A) :
    ∃ c : X, (D : Matrix (Fin 2) (Fin 2) X) = c • 1 := by
  have key : ∀ A : SL(2, X),
      (D : Matrix (Fin 2) (Fin 2) X) * (A : Matrix (Fin 2) (Fin 2) X) =
        (A : Matrix (Fin 2) (Fin 2) X) * D := fun A =>
    mul_comm_of_conj_eq_self (by
      have := congrArg (fun B : SL(2, X) => (B : Matrix (Fin 2) (Fin 2) X)) (h A)
      simpa only [glConjSL_coe] using this)
  have hu := key (u2 1)
  have hl := key (l2 1)
  exact scalar_of_commute_u2_l2 _ hu hl

theorem threeB_glConjSL_eq_of_smul {D : GL (Fin 2) X} {μ : X} {M : SL(2, X)}
    (hDM : (D : Matrix (Fin 2) (Fin 2) X) = μ • (M : Matrix (Fin 2) (Fin 2) X))
    (A : SL(2, X)) : glConjSL D A = M * A * M⁻¹ := by
  apply Subtype.ext
  rw [glConjSL_coe]
  have hMi : ((M⁻¹ : SL(2, X)) : Matrix (Fin 2) (Fin 2) X) *
      (M : Matrix (Fin 2) (Fin 2) X) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel]
    rfl
  have h1 : (D : Matrix (Fin 2) (Fin 2) X) * (A : Matrix (Fin 2) (Fin 2) X) =
      ((M * A * M⁻¹ : SL(2, X)) : Matrix (Fin 2) (Fin 2) X) * D := by
    have e2 : ((M : Matrix (Fin 2) (Fin 2) X) * (A : Matrix (Fin 2) (Fin 2) X) *
        ((M⁻¹ : SL(2, X)) : Matrix (Fin 2) (Fin 2) X)) * (M : Matrix (Fin 2) (Fin 2) X) =
        (M : Matrix (Fin 2) (Fin 2) X) * (A : Matrix (Fin 2) (Fin 2) X) := by
      rw [Matrix.mul_assoc, hMi, Matrix.mul_one]
    rw [hDM, Matrix.smul_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mul_smul, e2]
  calc (D : Matrix (Fin 2) (Fin 2) X) * (A : Matrix (Fin 2) (Fin 2) X) *
        ((D⁻¹ : GL (Fin 2) X) : Matrix (Fin 2) (Fin 2) X)
      = (((M * A * M⁻¹ : SL(2, X)) : Matrix (Fin 2) (Fin 2) X) * D) *
          ((D⁻¹ : GL (Fin 2) X) : Matrix (Fin 2) (Fin 2) X) := by rw [h1]
    _ = ((M * A * M⁻¹ : SL(2, X)) : Matrix (Fin 2) (Fin 2) X) := by
        rw [Matrix.mul_assoc, gl_mul_inv, Matrix.mul_one]

theorem threeB_exists_sl2_smul {D : GL (Fin 2) X} {c : X}
    (hc : ((D ^ 3 : GL (Fin 2) X) : Matrix (Fin 2) (Fin 2) X) = c • 1) :
    ∃ (M : SL(2, X)) (μ : X), μ ≠ 0 ∧
      (D : Matrix (Fin 2) (Fin 2) X) = μ • (M : Matrix (Fin 2) (Fin 2) X) := by
  set d : X := (D : Matrix (Fin 2) (Fin 2) X).det with hd
  have hd0 : d ≠ 0 := by
    have := congrArg Matrix.det (gl_mul_inv D)
    rw [Matrix.det_mul, Matrix.det_one] at this
    exact left_ne_zero_of_mul_eq_one this
  have hdc : d ^ 3 = c ^ 2 := by
    have h1 := congrArg Matrix.det hc
    rw [Units.val_pow_eq_pow_val, Matrix.det_pow, Matrix.det_smul, Matrix.det_one,
      Fintype.card_fin] at h1
    rw [hd]
    linear_combination h1
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0] at hdc
    exact pow_ne_zero 3 hd0 (by simpa using hdc)
  set μ : X := c / d with hμ
  have hμ0 : μ ≠ 0 := div_ne_zero hc0 hd0
  have hμ2 : μ ^ 2 = d := by
    rw [hμ, div_pow, ← hdc]
    field_simp
  have hdetM : (μ⁻¹ • (D : Matrix (Fin 2) (Fin 2) X)).det = 1 := by
    rw [Matrix.det_smul, Fintype.card_fin, ← hd, inv_pow, hμ2, inv_mul_cancel₀ hd0]
  refine ⟨⟨μ⁻¹ • (D : Matrix (Fin 2) (Fin 2) X), hdetM⟩, μ, hμ0, ?_⟩
  show (D : Matrix (Fin 2) (Fin 2) X) = μ • (μ⁻¹ • (D : Matrix (Fin 2) (Fin 2) X))
  rw [smul_smul, mul_inv_cancel₀ hμ0, one_smul]

end GL2

section Act

variable {G : Type*} [Group G] {X : Type} [Field X]

theorem threeB_neg_one_mul_comm (A : SL(2, X)) : (-1 : SL(2, X)) * A = A * (-1 : SL(2, X)) :=
  Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one, Matrix.neg_mul,
      Matrix.mul_neg, Matrix.one_mul, Matrix.mul_one])

theorem threeB_neg_one_mul_self : (-1 : SL(2, X)) * (-1 : SL(2, X)) = 1 :=
  Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_neg,
      Matrix.SpecialLinearGroup.coe_one, Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_one, neg_neg])

theorem threeB_conj_pow {ι : SL(2, X) →* G} {x : G} {N : GL (Fin 2) X}
    (hN : ∀ A, x * ι A * x⁻¹ = ι (glConjSL N A)) (n : ℕ) (A : SL(2, X)) :
    x ^ n * ι A * (x ^ n)⁻¹ = ι (glConjSL (N ^ n) A) := by
  induction n generalizing A with
  | zero => simp [glConjSL_one]
  | succ n ih =>
    rw [pow_succ', mul_inv_rev, pow_succ', glConjSL_mul]
    calc x * x ^ n * ι A * ((x ^ n)⁻¹ * x⁻¹)
        = x * (x ^ n * ι A * (x ^ n)⁻¹) * x⁻¹ := by group
      _ = ι (glConjSL N (glConjSL (N ^ n) A)) := by rw [ih, hN]

theorem threeB_decomp (ι : SL(2, X) →* G) (hι : Function.Injective ι)
    {b : G} {Nb : GL (Fin 2) X} (hNb : ∀ A, b * ι A * b⁻¹ = ι (glConjSL Nb A))
    (hb3 : b ^ 3 = 1) :
    ∃ (M : SL(2, X)) (t : G), (∀ A, t * ι A = ι A * t) ∧ t ^ 3 = 1 ∧ b = ι M * t ∧
      M ^ 3 = 1 := by
  have hcube : ∀ A, glConjSL (Nb ^ 3) A = A := fun A => by
    apply hι
    rw [← threeB_conj_pow hNb 3 A, hb3]
    group
  obtain ⟨c, hc⟩ := threeB_scalar_of_glConjSL_eq_self hcube
  obtain ⟨M₀, μ, -, hM₀⟩ := threeB_exists_sl2_smul hc
  have hconj : ∀ A, glConjSL Nb A = M₀ * A * M₀⁻¹ := threeB_glConjSL_eq_of_smul hM₀
  have hbM : ∀ A, b * ι A * b⁻¹ = ι M₀ * ι A * (ι M₀)⁻¹ := fun A => by
    rw [hNb, hconj, map_mul, map_mul, map_inv]
  set t₀ : G := (ι M₀)⁻¹ * b with ht₀
  have ht₀c : ∀ A, t₀ * ι A = ι A * t₀ := fun A => by
    have h1 : b * ι A = ι M₀ * ι A * (ι M₀)⁻¹ * b := by
      calc b * ι A = (b * ι A * b⁻¹) * b := by group
        _ = _ := by rw [hbM A]
    calc t₀ * ι A = (ι M₀)⁻¹ * (b * ι A) := by rw [ht₀]; group
      _ = (ι M₀)⁻¹ * (ι M₀ * ι A * (ι M₀)⁻¹ * b) := by rw [h1]
      _ = ι A * t₀ := by rw [ht₀]; group
  have hbt : b = ι M₀ * t₀ := by rw [ht₀]; group
  have hcomm : Commute (ι M₀) t₀ := (ht₀c M₀).symm
  have hpow : (ι M₀) ^ 3 * t₀ ^ 3 = 1 := by
    rw [← hcomm.mul_pow, ← hbt, hb3]
  have hcentral : ∀ A : SL(2, X), M₀ ^ 3 * A = A * M₀ ^ 3 := fun A => by
    apply hι
    have h1 : Commute (t₀ ^ 3) (ι A) := Commute.pow_left (show Commute t₀ (ι A) from ht₀c A) 3
    have h2 : ι M₀ ^ 3 = (t₀ ^ 3)⁻¹ := eq_inv_of_mul_eq_one_left hpow
    rw [map_mul, map_mul, map_pow, h2]
    exact (Commute.inv_left h1).eq
  rcases threeB_sl2_central hcentral with h | h
  · refine ⟨M₀, t₀, ht₀c, ?_, hbt, h⟩
    have h3 : ι M₀ ^ 3 = 1 := by rw [← map_pow, h, map_one]
    rw [h3, one_mul] at hpow
    exact hpow
  · have hww : ι (-1 : SL(2, X)) * ι (-1 : SL(2, X)) = 1 := by
      rw [← map_mul, threeB_neg_one_mul_self, map_one]
    have hwt : Commute t₀ (ι (-1 : SL(2, X))) := ht₀c (-1)
    have hwM : Commute (ι M₀) (ι (-1 : SL(2, X))) := by
      show ι M₀ * ι (-1) = ι (-1) * ι M₀
      rw [← map_mul, ← map_mul, ← threeB_neg_one_mul_comm]
    have hM3' : ι M₀ ^ 3 = ι (-1 : SL(2, X)) := by rw [← map_pow, h]
    have hw3 : ι (-1 : SL(2, X)) ^ 3 = ι (-1 : SL(2, X)) := by
      rw [pow_succ, pow_two, hww, one_mul]
    have ht03 : t₀ ^ 3 = ι (-1 : SL(2, X)) := by
      rw [hM3'] at hpow
      calc t₀ ^ 3 = ι (-1 : SL(2, X)) * (ι (-1 : SL(2, X)) * t₀ ^ 3) := by
            rw [← mul_assoc, hww, one_mul]
        _ = ι (-1 : SL(2, X)) := by rw [hpow, mul_one]
    refine ⟨M₀ * (-1), t₀ * ι (-1 : SL(2, X)), ?_, ?_, ?_, ?_⟩
    · intro A
      calc t₀ * ι (-1 : SL(2, X)) * ι A = t₀ * (ι (-1 : SL(2, X)) * ι A) := by rw [mul_assoc]
        _ = t₀ * (ι A * ι (-1 : SL(2, X))) := by
            rw [← map_mul, ← map_mul, threeB_neg_one_mul_comm]
        _ = ι A * (t₀ * ι (-1 : SL(2, X))) := by rw [← mul_assoc, ht₀c A, mul_assoc]
    · rw [hwt.mul_pow, ht03, hw3, hww]
    · rw [map_mul]
      calc b = ι M₀ * t₀ := hbt
        _ = ι M₀ * ι (-1 : SL(2, X)) * (t₀ * ι (-1 : SL(2, X))) := by
            calc ι M₀ * t₀ = ι M₀ * (t₀ * (ι (-1 : SL(2, X)) * ι (-1 : SL(2, X)))) := by
                  rw [hww, mul_one]
              _ = ι M₀ * (t₀ * ι (-1 : SL(2, X)) * ι (-1 : SL(2, X))) := by rw [mul_assoc t₀]
              _ = ι M₀ * (ι (-1 : SL(2, X)) * t₀ * ι (-1 : SL(2, X))) := by rw [hwt.eq]
              _ = _ := by group
    · apply hι
      rw [map_pow, map_one, map_mul, hwM.mul_pow, hM3', hw3, hww]

theorem threeB_central_of_decomp (ι : SL(2, X) →* G) (hι : Function.Injective ι) (C : Subgroup G)
    (hact : ∀ x ∈ C, ∃ N : GL (Fin 2) X, ∀ A, x * ι A * x⁻¹ = ι (glConjSL N A))
    (hcomm : ∀ x ∈ C, ∀ y ∈ C, x * y * x⁻¹ * y⁻¹ ∈ ι.range)
    {t : G} (htC : t ∈ C) (htc : ∀ A, t * ι A = ι A * t) (ht3 : t ^ 3 = 1) :
    ∀ x ∈ C, x * t * x⁻¹ = t := by
  intro x hx
  obtain ⟨N', hN'⟩ := hact x⁻¹ (C.inv_mem hx)
  have hxtc : ∀ A, x * t * x⁻¹ * ι A = ι A * (x * t * x⁻¹) := fun A => by
    have h1 : x⁻¹ * ι A * x = ι (glConjSL N' A) := by simpa using hN' A
    calc x * t * x⁻¹ * ι A = x * t * (x⁻¹ * ι A * x) * x⁻¹ := by group
      _ = x * (t * ι (glConjSL N' A)) * x⁻¹ := by rw [h1]; group
      _ = x * (ι (glConjSL N' A) * t) * x⁻¹ := by rw [htc]
      _ = x * (x⁻¹ * ι A * x) * t * x⁻¹ := by rw [h1]; group
      _ = ι A * (x * t * x⁻¹) := by group
  obtain ⟨u, hu⟩ : ∃ u : G, u = x * t * x⁻¹ * t⁻¹ := ⟨_, rfl⟩
  obtain ⟨U, hU⟩ := hcomm x hx t htC
  have huc : ∀ A, u * ι A = ι A * u := fun A => by
    have h1 : Commute (x * t * x⁻¹) (ι A) := hxtc A
    have h2 : Commute t⁻¹ (ι A) := Commute.inv_left (htc A)
    rw [hu]
    exact (h1.mul_left h2).eq
  have hU' : ι U = u := by rw [hu]; exact hU
  have hUc : ∀ A : SL(2, X), U * A = A * U := fun A => by
    apply hι
    rw [map_mul, map_mul, hU']
    exact huc A
  have huu : u * u = 1 := by
    rcases threeB_sl2_central hUc with h | h
    · rw [← hU', h, ← map_mul, mul_one, map_one]
    · rw [← hU', h, ← map_mul, threeB_neg_one_mul_self, map_one]
  have hcu : Commute u t := by
    rw [← hU']
    exact (htc U).symm
  have hu3 : u ^ 3 = 1 := by
    have h1 : (u * t) ^ 3 = x * t ^ 3 * x⁻¹ := by
      rw [show u * t = x * t * x⁻¹ by rw [hu]; group, conj_pow]
    rw [ht3, mul_one, mul_inv_cancel, hcu.mul_pow, ht3, mul_one] at h1
    exact h1
  have hu1 : u = 1 := by
    calc u = u * (u * u) := by rw [huu, mul_one]
      _ = u ^ 3 := by rw [pow_succ, pow_two, mul_assoc]
      _ = 1 := hu3
  calc x * t * x⁻¹ = u * t := by rw [hu]; group
    _ = t := by rw [hu1, one_mul]

theorem threeB_conj_exists [Finite X] (h3 : (3 : X) ≠ 0)
    (ι : SL(2, X) →* G) (hι : Function.Injective ι) (C : Subgroup G)
    (hSC : ∀ A, ι A ∈ C)
    (hact : ∀ x ∈ C, ∃ N : GL (Fin 2) X, ∀ A, x * ι A * x⁻¹ = ι (glConjSL N A))
    (hcomm : ∀ x ∈ C, ∀ y ∈ C, x * y * x⁻¹ * y⁻¹ ∈ ι.range)
    {b : G} (hbC : b ∈ C) (hb3 : b ^ 3 = 1) :
    ∀ x ∈ C, ∃ A : SL(2, X), ι A * b * (ι A)⁻¹ = x * b * x⁻¹ := by
  obtain ⟨Nb, hNb⟩ := hact b hbC
  obtain ⟨M, t, htc, ht3, hbt, hM3⟩ := threeB_decomp ι hι hNb hb3
  have htC : t ∈ C := by
    have : t = (ι M)⁻¹ * b := by rw [hbt]; group
    rw [this]
    exact C.mul_mem (C.inv_mem (hSC M)) hbC
  have hcen := threeB_central_of_decomp ι hι C hact hcomm htC htc ht3
  intro x hx
  by_cases hM1 : M = 1
  · refine ⟨1, ?_⟩
    have hb : b = t := by rw [hbt, hM1, map_one, one_mul]
    rw [map_one, one_mul, inv_one, mul_one, hb, hcen x hx]
  · obtain ⟨Nx, hNx⟩ := hact x hx
    have hM'3 : (glConjSL Nx M) ^ 3 = 1 := by rw [← map_pow, hM3, map_one]
    have hM'1 : glConjSL Nx M ≠ 1 := fun h => hM1 (by
      have h' := congrArg (glConjSL Nx⁻¹) h
      rwa [← glConjSL_mul, inv_mul_cancel, glConjSL_one, map_one] at h')
    obtain ⟨R, hR⟩ := CFSG.RankThree.PartTwo.Sec11.Item1118Res3Proof.exists_conj_of_pow_three h3
      hM3 hM1 hM'3 hM'1
    refine ⟨R, ?_⟩
    have ha : ι R * ι M * (ι R)⁻¹ = x * ι M * x⁻¹ := by
      rw [hNx, ← hR, map_mul, map_mul, map_inv]
    have hb' : ι R * t * (ι R)⁻¹ = t := by
      rw [← htc R]
      group
    calc ι R * b * (ι R)⁻¹ = ι R * (ι M * t) * (ι R)⁻¹ := by rw [← hbt]
      _ = (ι R * ι M * (ι R)⁻¹) * (ι R * t * (ι R)⁻¹) := by group
      _ = (x * ι M * x⁻¹) * (x * t * x⁻¹) := by rw [ha, hb', hcen x hx]
      _ = x * (ι M * t) * x⁻¹ := by group
      _ = x * b * x⁻¹ := by rw [← hbt]

end Act

end CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.TOdd
