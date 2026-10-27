module

import CFSG.LieType.SeitzGeneration.OuterLinearDescent
public import CFSG.GroupTheory.SteinbergBKSemilinearFixedBasis
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ZUniAut

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267Z.Uni

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Open
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)

variable {ℓ f : ℕ} {K : Type} [Field K] [Finite K]

theorem exists_norm_one_hilbert90 (h : UnitaryFieldData ℓ f K) {σ : K ≃+* K} (hσ : orderOf σ = 3)
    {f₀ : ℕ} (hf₀ : 1 ≤ f₀) (hK0 : Nat.card (semilinearFixedSubfield σ) = (ℓ ^ f₀) ^ 2)
    (hbar : ∀ x : K, σ x = x → h.bar x = x ^ (ℓ ^ f₀)) {x : K} (hxn : h.bar x * x = 1)
    (hN : x * σ x * σ (σ x) = 1) : ∃ y : K, h.bar y * y = 1 ∧ x * σ y = y := by
  obtain ⟨c, hc0, hc⟩ := CFSG.LieType.SeitzGeneration.exists_hilbert90 (p := 3) Nat.prime_three
    h.prime (by have := h.one_le; omega) h.card σ hσ x (by
      rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_one]
      exact hN)
  have hbarσ : ∀ z : K, σ (h.bar z) = h.bar (σ z) := fun z => by
    rw [UnitaryFieldData.bar_apply, UnitaryFieldData.bar_apply, map_pow]
  have hσn : σ (h.bar c * c) = h.bar c * c := by
    rw [map_mul, hbarσ]
    calc h.bar (σ c) * σ c = (h.bar x * x) * (h.bar (σ c) * σ c) := by rw [hxn, one_mul]
      _ = h.bar (x * σ c) * (x * σ c) := by rw [map_mul]; ring
      _ = h.bar c * c := by rw [hc]
  have hn0 : h.bar c * c ≠ 0 := mul_ne_zero ((h.bar_eq_zero_iff).not.2 hc0) hc0
  have hbn : h.bar (h.bar c * c) = h.bar c * c := by
    rw [map_mul, UnitaryFieldData.bar_bar, mul_comm]
  have h₀ : UnitaryFieldData ℓ f₀ (semilinearFixedSubfield σ) :=
    ⟨h.prime, hf₀, by rw [hK0, ← pow_mul, mul_comm]⟩
  have hn₀ : (h.bar c * c)⁻¹ ∈ semilinearFixedSubfield σ :=
    (show σ (h.bar c * c)⁻¹ = (h.bar c * c)⁻¹ by rw [map_inv₀, hσn])
  have hfix : h₀.bar ⟨(h.bar c * c)⁻¹, hn₀⟩ = ⟨(h.bar c * c)⁻¹, hn₀⟩ := by
    apply Subtype.ext
    rw [UnitaryFieldData.bar_apply, SubmonoidClass.coe_pow]
    change ((h.bar c * c)⁻¹) ^ (ℓ ^ f₀) = (h.bar c * c)⁻¹
    rw [← hbar _ (RingHom.mem_eqLocusField.mp hn₀), map_inv₀, hbn]
  obtain ⟨e, he⟩ := h₀.normHom_surjective ⟨⟨(h.bar c * c)⁻¹, hn₀⟩, (h₀.mem_fixedField).2 hfix⟩
  have heσ : σ (e : K) = e := RingHom.mem_eqLocusField.mp e.2
  have he1 : (e : K) * ((h₀.bar e : semilinearFixedSubfield σ) : K) = (h.bar c * c)⁻¹ := by
    have := congrArg (fun z : h₀.fixedField => ((z : semilinearFixedSubfield σ) : K)) he
    simpa [UnitaryFieldData.norm] using this
  have he' : h.bar (e : K) * (e : K) = (h.bar c * c)⁻¹ := by
    rw [← he1, UnitaryFieldData.bar_apply h₀ e, SubmonoidClass.coe_pow, ← hbar _ heσ, mul_comm]
  refine ⟨c * e, ?_, ?_⟩
  · rw [map_mul, mul_mul_mul_comm, he', mul_inv_cancel₀ hn0]
  · rw [map_mul, heσ, ← mul_assoc, hc]

theorem exists_fixed_mul_isDiag (h : UnitaryFieldData ℓ f K) {σ : K ≃+* K} (hσ : orderOf σ = 3)
    {f₀ : ℕ} (hf₀ : 1 ≤ f₀) (hK0 : Nat.card (semilinearFixedSubfield σ) = (ℓ ^ f₀) ^ 2)
    (hbar : ∀ x : K, σ x = x → h.bar x = x ^ (ℓ ^ f₀)) {P : GL (Fin 3) K} (hPU : P ∈ UG h)
    (hx : ((P⁻¹ * glAut σ P : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).IsDiag) :
    ∃ Y : GL (Fin 3) K, Y ∈ UG h ∧ ((Y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).IsDiag ∧
      glAut σ (P * Y) = P * Y := by
  set X := P⁻¹ * glAut σ P with hX
  have hXU : X ∈ UG h :=
    mul_mem (inv_mem hPU) (glAut_mem_primeFormUnitary h (isPrimeFormGram_one (n := 3)) σ hPU)
  set d : Fin 3 → K := fun i => ((X : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i i with hd
  have hXd : ((X : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal d := hx.diagonal_diag.symm
  have hdn : ∀ i, h.bar (d i) * d i = 1 := by
    intro i
    have e := mem_primeFormUnitary.1 hXU
    rw [hXd, Units.val_one, Matrix.mul_one, diagonal_map (map_zero _), diagonal_transpose,
      diagonal_mul_diagonal] at e
    have e' := congrFun (congrFun e i) i
    rwa [diagonal_apply_eq, one_apply_eq] at e'
  have hσ3 : σ ^ 3 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  have e3 : glAut σ (glAut σ (glAut σ P)) = P := by
    have : glAut σ (glAut σ (glAut σ P)) = glAut (σ ^ 3) P := by
      rw [pow_three, map_mul, map_mul]
      rfl
    rw [this, hσ3, map_one]
    rfl
  have hNX : X * glAut σ X * glAut σ (glAut σ X) = 1 := by
    simp only [hX, map_mul, map_inv]
    rw [e3]
    group
  have hdN : ∀ i, d i * σ (d i) * σ (σ (d i)) = 1 := by
    intro i
    have e := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) i i) hNX
    simp only [Units.val_mul, coe_glAut, hXd, diagonal_map (map_zero σ), diagonal_mul_diagonal,
      Units.val_one, diagonal_apply_eq, one_apply_eq] at e
    exact e
  choose y hy using fun i => exists_norm_one_hilbert90 h hσ hf₀ hK0 hbar (hdn i) (hdN i)
  have hy0 : ∀ i, y i ≠ 0 := fun i => ne_zero_of_norm (hy i).1
  have hdet : (diagonal y).det ≠ 0 := by
    rw [det_diagonal]
    exact Finset.prod_ne_zero_iff.2 fun i _ => hy0 i
  set Y := Matrix.GeneralLinearGroup.mkOfDetNeZero (diagonal y) hdet with hY
  have hYm : ((Y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal y := rfl
  have hYU : Y ∈ UG h := by
    rw [mem_primeFormUnitary, hYm, Units.val_one, Matrix.mul_one, diagonal_map (map_zero _),
      diagonal_transpose, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    exact (hy i).1
  refine ⟨Y, hYU, by rw [hYm]; exact isDiag_diagonal y, ?_⟩
  have hσP : glAut σ P = P * X := by rw [hX, mul_inv_cancel_left]
  have hXY : X * glAut σ Y = Y := by
    apply Units.ext
    rw [Units.val_mul, coe_glAut, hXd, hYm, diagonal_map (map_zero σ), diagonal_mul_diagonal]
    congr 1
    funext i
    exact (hy i).2
  rw [map_mul, hσP, mul_assoc, hXY]

theorem coe_pow_of_isDiag {h : UnitaryFieldData ℓ f K} {s : SG h}
    (hs : ((s : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).IsDiag) (n : ℕ) :
    ((s ^ n : SG h) : GL (Fin 3) K) =
      (diagonal fun i => ((s : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i i ^ n :
        Matrix (Fin 3) (Fin 3) K) := by
  rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val]
  conv_lhs => rw [← hs.diagonal_diag]
  rw [diagonal_pow]
  rfl

theorem mem_of_isDiag_of_le_card {h : UnitaryFieldData ℓ f K} {AM : Subgroup (SG h)}
    (hdiag : ∀ s ∈ AM, ((s : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).IsDiag)
    (h9 : ∀ s ∈ AM, s ^ 9 = 1) (h3 : ∀ s ∈ AM, s ^ 3 ∈ normOneScalars h (SG h) 3)
    (hcard : 27 ≤ Nat.card AM) {t : SG h}
    (htd : ((t : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).IsDiag) (ht9 : t ^ 9 = 1)
    (ht3 : t ^ 3 ∈ normOneScalars h (SG h) 3) : t ∈ AM := by
  classical
  set Ω : Set (SG h) := {s | ((s : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).IsDiag ∧ s ^ 9 = 1 ∧
    s ^ 3 ∈ normOneScalars h (SG h) 3} with hΩ
  have hsub : (AM : Set (SG h)) ⊆ Ω := fun s hs => ⟨hdiag s hs, h9 s hs, h3 s hs⟩
  have hR : ∀ n : ℕ, 0 < n → ({x : K | x ^ n = 1}).ncard ≤ n := by
    intro n hn
    have e : {x : K | x ^ n = 1} = ((Polynomial.nthRoots n (1 : K)).toFinset : Set K) := by
      ext x
      simp [Polynomial.mem_nthRoots hn]
    rw [e, Set.ncard_coe_finset]
    exact (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots n 1)
  have hent : ∀ s ∈ Ω, ((s : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0 ^ 9 = 1 ∧
      ((s : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0 ^ 3 =
        ((s : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 1 ^ 3 ∧
      ((s : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0 *
        ((s : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 1 *
          ((s : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 2 = 1 := by
    rintro s ⟨hsd, hs9, hs3⟩
    refine ⟨?_, ?_, ?_⟩
    · have e := congrArg (fun g : SG h => ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0) hs9
      simp only [coe_pow_of_isDiag hsd, diagonal_apply_eq, Subgroup.coe_one, Units.val_one,
        one_apply_eq] at e
      exact e
    · obtain ⟨c, -, -, hc⟩ := mem_normOneScalars.1 hs3
      have e0 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 0) hc
      have e1 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 1 1) hc
      simp only [coe_pow_of_isDiag hsd, diagonal_apply_eq, Matrix.GeneralLinearGroup.coe_scalar,
        scalar_apply] at e0 e1
      exact e0.trans e1.symm
    · have hdet : ((s : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := (mem_gramSU.1 s.2).2
      rw [← hsd.diagonal_diag, det_diagonal, Fin.prod_univ_three] at hdet
      exact hdet
  have hne0 : ∀ s ∈ Ω, ((s : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0 ≠ 0 := by
    intro s hs h0
    have := (hent s hs).2.2
    rw [h0, zero_mul, zero_mul] at this
    exact zero_ne_one this
  set ψ : SG h → K × K := fun s => (((s : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0,
    ((s : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 1 *
      (((s : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0)⁻¹) with hψ
  have hmaps : ∀ s ∈ Ω, ψ s ∈ {x : K | x ^ 9 = 1} ×ˢ {x : K | x ^ 3 = 1} := by
    intro s hs
    obtain ⟨e9, e3, -⟩ := hent s hs
    refine ⟨e9, ?_⟩
    change (_ * _⁻¹) ^ 3 = 1
    rw [mul_pow, inv_pow, ← e3, mul_inv_cancel₀ (pow_ne_zero 3 (hne0 s hs))]
  have hinj : Set.InjOn ψ Ω := by
    intro s hs s' hs' hss
    have h0 := congrArg Prod.fst hss
    have h1 := congrArg Prod.snd hss
    simp only [hψ] at h0 h1
    rw [h0] at h1
    have h1' := mul_right_cancel₀ (inv_ne_zero (hne0 s' hs')) h1
    have h2 : ((s : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 2 =
        ((s' : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 2 := by
      have d := (hent s hs).2.2
      have d' := (hent s' hs').2.2
      rw [h0, h1'] at d
      exact mul_left_cancel₀ (mul_ne_zero (hne0 s' hs') (by
        intro h0'
        rw [h0', mul_zero, zero_mul] at d'
        exact zero_ne_one d')) (d.trans d'.symm)
    apply Subtype.ext
    apply Units.ext
    rw [← hs.1.diagonal_diag, ← hs'.1.diagonal_diag]
    congr 1
    funext i
    fin_cases i
    · exact h0
    · exact h1'
    · exact h2
  have hΩcard : Ω.ncard ≤ 27 :=
    calc Ω.ncard ≤ ({x : K | x ^ 9 = 1} ×ˢ {x : K | x ^ 3 = 1}).ncard :=
          Set.ncard_le_ncard_of_injOn ψ hmaps hinj
      _ = ({x : K | x ^ 9 = 1}).ncard * ({x : K | x ^ 3 = 1}).ncard := Set.ncard_prod
      _ ≤ 9 * 3 := Nat.mul_le_mul (hR 9 (by norm_num)) (hR 3 (by norm_num))
  have hEq : (AM : Set (SG h)) = Ω := Set.eq_of_subset_of_ncard_le hsub
    (hΩcard.trans (hcard.trans_eq (Nat.card_coe_set_eq _)))
  have htΩ : t ∈ Ω := ⟨htd, ht9, ht3⟩
  rw [← hEq] at htΩ
  exact htΩ

end CFSG.LocalAnalysis.GLTheoremA.S267Z.Uni

end
