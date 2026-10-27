module

public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockUniPosGU
public import CFSG.LocalAnalysis.SectionRank.QTK.EvenLinear

public section

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.AGLEmbedding.LeviBlock CFSG.Open

namespace CFSG.AGLEmbedding.LeviBlock

theorem guEmbed_injective {f : ℕ} {K : Type} [Field K] {t s ε : ℕ}
    (h : UnitaryFieldData 2 f K) (hε : ε ≤ 1) (ht : 1 ≤ t) :
    Function.Injective (guEmbed (s := s) (ε := ε) h hε ht) := by
  intro B B' hBB'
  have h : guMat (ε := ε) h ht B = guMat h ht B' := by
    have := congrArg (fun z : hypSU h (t + s) ε =>
      ((z : GL (HypIndex (t + s) ε) K) : Matrix (HypIndex (t + s) ε) (HypIndex (t + s) ε) K)) hBB'
    rwa [coe_guEmbed, coe_guEmbed] at this
  ext x y
  have e := congrFun (congrFun h (resIdx t x)) (resIdx t y)
  simp only [guMat, diagonal_mul, guDiag_resIdx, one_mul,
    extendMat_apply_map (resIdx_injective t)] at e
  exact e

end CFSG.AGLEmbedding.LeviBlock

namespace CFSG.ClassicalGroups.UnitaryFlag

variable {n : ℕ} {K : Type} [Field K]

private theorem exists_add_bar_eq_one (h : UnitaryFieldData 2 n K) : ∃ c : K, c + h.bar c = 1 := by
  haveI : CharP K 2 := h.charP
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have h2z : ∀ z : K, z + z = 0 := fun z => by
    have hzz : (2 : K) * z = 0 := by rw [h2, zero_mul]
    rwa [two_mul] at hzz
  obtain ⟨x, hx⟩ := h.exists_bar_ne
  have hy0 : x + h.bar x ≠ 0 := by
    intro h0
    apply hx
    have h1 : h.bar x = -x := by linear_combination h0
    have h2x : -x = x := (eq_neg_of_add_eq_zero_right (h2z x)).symm
    rw [h1, h2x]
  refine ⟨x / (x + h.bar x), ?_⟩
  have hybar : h.bar (x + h.bar x) = x + h.bar x := by
    rw [map_add, h.bar_bar, add_comm]
  rw [map_div₀, hybar, ← add_div, div_self hy0]

theorem exists_pthRoots_subgroup (h : UnitaryFieldData 2 n K) {p : ℕ} (hp : p.Prime)
    (hpd : p ∣ 2 ^ n + 1) :
    ∃ μ : Subgroup Kˣ, Nat.card ↥μ = p ∧ (∀ a : ↥μ, a ^ p = 1) ∧
      ∀ a : ↥μ, h.bar ((a : Kˣ) : K) * ((a : Kˣ) : K) = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite K := h.finite
  haveI : Finite Kˣ := Finite.of_injective (fun z : Kˣ => (z : K)) Units.val_injective
  have hdvd : p ∣ Nat.card Kˣ := by
    have hcard : Nat.card Kˣ = 2 ^ (2 * n) - 1 := by
      rw [Nat.card_units, h.card]
    have hfac : 2 ^ (2 * n) - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by
      have hsq : 2 ^ (2 * n) = (2 ^ n) ^ 2 := by
        rw [← pow_mul]
        congr 1
        omega
      rw [hsq]
      simpa using (Nat.sq_sub_sq (2 ^ n) 1)
    rw [hcard, hfac]
    exact dvd_mul_of_dvd_left hpd _
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) p hdvd
  have hcard : Nat.card ↥(Subgroup.zpowers g) = p := by rw [Nat.card_zpowers, hg]
  refine ⟨Subgroup.zpowers g, hcard, ?_, ?_⟩
  · intro a
    have h1 : a ^ Nat.card ↥(Subgroup.zpowers g) = 1 := pow_card_eq_one'
    rwa [hcard] at h1

  · intro a
    have h1 : ((a : Kˣ)) ^ p = 1 := by
      have h2 : a ^ Nat.card ↥(Subgroup.zpowers g) = 1 := pow_card_eq_one'
      rw [hcard] at h2
      simpa using congrArg (fun z : ↥(Subgroup.zpowers g) => (z : Kˣ)) h2
    have h2 : ((a : Kˣ) : K) ^ p = 1 := by
      simpa using congrArg (fun z : Kˣ => (z : K)) h1
    have h3 : ((a : Kˣ) : K) ^ (2 ^ n + 1) = 1 := by
      obtain ⟨t, ht⟩ := hpd
      rw [ht, pow_mul, h2, one_pow]
    rw [h.bar_apply, ← pow_succ, h3]

private def cbMat (c cb : K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K :=
  Matrix.of fun i j =>
    match i, j with
    | .inl _, .inl _ => 0
    | .inl _, .inr (.inl _) => 1
    | .inl _, .inr (.inr _) => 1
    | .inr (.inl _), .inl _ => 1
    | .inr (.inl _), .inr (.inl _) => 0
    | .inr (.inl _), .inr (.inr _) => 0
    | .inr (.inr _), .inl _ => 0
    | .inr (.inr _), .inr (.inl _) => c
    | .inr (.inr _), .inr (.inr _) => cb

private def cbInvMat (c cb : K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K :=
  Matrix.of fun i j =>
    match i, j with
    | .inl _, .inl _ => 0
    | .inl _, .inr (.inl _) => 1
    | .inl _, .inr (.inr _) => 0
    | .inr (.inl _), .inl _ => cb
    | .inr (.inl _), .inr (.inl _) => 0
    | .inr (.inl _), .inr (.inr _) => 1
    | .inr (.inr _), .inl _ => c
    | .inr (.inr _), .inr (.inl _) => 0
    | .inr (.inr _), .inr (.inr _) => 1

private theorem cbMat_mul_cbInvMat (c cb : K) (hc : c + cb = 1) (h2 : (2 : K) = 0) :
    cbMat c cb * cbInvMat c cb = 1 := by
  ext a b
  rcases a with i | k | i <;> rcases b with j | l | j <;>
    (try fin_cases i) <;> (try fin_cases j) <;> (try fin_cases k) <;> (try fin_cases l) <;>
    simp [Matrix.mul_apply, Matrix.one_apply, Fintype.sum_sum_type, Fin.sum_univ_one,
      cbMat, cbInvMat, Matrix.of_apply]
  all_goals first
    | linear_combination hc
    | linear_combination h2
    | linear_combination (c * cb) * h2
    | linear_combination (cb * c) * h2
    | linear_combination (c * c) * h2
    | linear_combination (cb * cb) * h2
    | linear_combination c * h2
    | linear_combination cb * h2
    | ring

private theorem cbInvMat_mul_cbMat (c cb : K) (hc : c + cb = 1) (h2 : (2 : K) = 0) :
    cbInvMat c cb * cbMat c cb = 1 := by
  ext a b
  rcases a with i | k | i <;> rcases b with j | l | j <;>
    (try fin_cases i) <;> (try fin_cases j) <;> (try fin_cases k) <;> (try fin_cases l) <;>
    simp [Matrix.mul_apply, Matrix.one_apply, Fintype.sum_sum_type, Fin.sum_univ_one,
      cbMat, cbInvMat, Matrix.of_apply]
  all_goals first
    | linear_combination hc
    | linear_combination h2
    | linear_combination (c * cb) * h2
    | linear_combination (cb * c) * h2
    | linear_combination (c * c) * h2
    | linear_combination (cb * cb) * h2
    | linear_combination c * h2
    | linear_combination cb * h2
    | ring

private theorem cbMat_gram (h : UnitaryFieldData 2 n K) {c cb : K} (hcb : h.bar c = cb)
    (hc : c + cb = 1) (h2 : (2 : K) = 0) :
    ((cbMat c cb).map h.bar)ᵀ * hypGram 1 1 K * cbMat c cb = 1 := by
  have hbcb : h.bar cb = c := by rw [← hcb, h.bar_bar]
  ext a b
  rcases a with i | k | i <;> rcases b with j | l | j <;>
    (try fin_cases i) <;> (try fin_cases j) <;> (try fin_cases k) <;> (try fin_cases l) <;>
    simp [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.one_apply,
      Fintype.sum_sum_type, Fin.sum_univ_one, cbMat, hypGram_apply, hypPartner, hcb, hbcb,
      Matrix.of_apply]
  all_goals first
    | linear_combination hc
    | linear_combination h2
    | linear_combination (c * cb) * h2
    | linear_combination (cb * c) * h2
    | linear_combination (c * c) * h2
    | linear_combination (cb * cb) * h2
    | linear_combination c * h2
    | linear_combination cb * h2
    | ring

private theorem cbInvMat_gram (h : UnitaryFieldData 2 n K) {c cb : K} (hcb : h.bar c = cb)
    (hc : c + cb = 1) (h2 : (2 : K) = 0) :
    ((cbInvMat c cb).map h.bar)ᵀ * cbInvMat c cb = hypGram 1 1 K := by
  have hbcb : h.bar cb = c := by rw [← hcb, h.bar_bar]
  ext a b
  rcases a with i | k | i <;> rcases b with j | l | j <;>
    (try fin_cases i) <;> (try fin_cases j) <;> (try fin_cases k) <;> (try fin_cases l) <;>
    simp [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
      Fintype.sum_sum_type, Fin.sum_univ_one, cbInvMat, hypGram_apply, hypPartner, hcb, hbcb,
      Matrix.of_apply]
  all_goals first
    | linear_combination hc
    | linear_combination h2
    | linear_combination (c * cb) * h2
    | linear_combination (cb * c) * h2
    | linear_combination (c * c) * h2
    | linear_combination (cb * cb) * h2
    | linear_combination c * h2
    | linear_combination cb * h2
    | ring

private noncomputable def diagUnit (d : HypIndex 1 1 → Kˣ) : GL (HypIndex 1 1) K where
  val := Matrix.diagonal fun i => (d i : K)
  inv := Matrix.diagonal fun i => (((d i)⁻¹ : Kˣ) : K)
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    simp
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    simp

private theorem coe_diagUnit (d : HypIndex 1 1 → Kˣ) :
    ((diagUnit d : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) =
      Matrix.diagonal fun i => (d i : K) := rfl

private theorem diagUnit_mul (d d' : HypIndex 1 1 → Kˣ) :
    diagUnit (d * d') = diagUnit d * diagUnit d' := by
  apply Units.ext
  rw [coe_diagUnit, Units.val_mul, coe_diagUnit, coe_diagUnit, Matrix.diagonal_mul_diagonal]
  first | rfl | (congr 1; funext i; exact Units.val_mul (d i) (d' i))

private theorem diagUnit_injective : Function.Injective (diagUnit (K := K)) := by
  intro d d' h
  funext i
  have := congrArg (fun z : GL (HypIndex 1 1) K =>
    ((z : Matrix (HypIndex 1 1) (HypIndex 1 1) K) i i)) h
  exact Units.ext (by simpa [coe_diagUnit] using this)

private def triEntry (p : Kˣ × Kˣ × Kˣ) : HypIndex 1 1 → Kˣ
  | .inl _ => p.1
  | .inr (.inl _) => p.2.1
  | .inr (.inr _) => p.2.2

private theorem triEntry_mul (p q : Kˣ × Kˣ × Kˣ) : triEntry (p * q) = triEntry p * triEntry q := by
  funext i
  rcases i with i | k | i <;> rfl

private noncomputable def diagTriple : (Kˣ × Kˣ × Kˣ) →* GL (HypIndex 1 1) K :=
  MonoidHom.mk' (fun p => diagUnit (triEntry p)) (fun p q => by
    rw [triEntry_mul, diagUnit_mul])

private theorem diagTriple_injective : Function.Injective (diagTriple (K := K)) := by
  intro p q h
  have h' : triEntry p = triEntry q := diagUnit_injective h
  have h1 : p.1 = q.1 := congrFun h' (.inl 0)
  have h2 : p.2.1 = q.2.1 := congrFun h' (.inr (.inl 0))
  have h3 : p.2.2 = q.2.2 := congrFun h' (.inr (.inr 0))
  exact Prod.ext h1 (Prod.ext h2 h3)

private noncomputable def conjDiag (Cg : GL (HypIndex 1 1) K) :
    (Kˣ × Kˣ × Kˣ) →* GL (HypIndex 1 1) K :=
  (MulAut.conj Cg).toMonoidHom.comp diagTriple

private theorem conjDiag_injective (Cg : GL (HypIndex 1 1) K) :
    Function.Injective (conjDiag Cg) := fun p q h =>
  diagTriple_injective ((MulAut.conj Cg).injective h)

private theorem coe_diagTriple (p : Kˣ × Kˣ × Kˣ) :
    ((diagTriple (K := K) p : GL (HypIndex 1 1) K) :
      Matrix (HypIndex 1 1) (HypIndex 1 1) K) =
      Matrix.diagonal (fun i => (triEntry p i : K)) :=
  coe_diagUnit _

private theorem coe_conjDiag (Cg : GL (HypIndex 1 1) K) (p : Kˣ × Kˣ × Kˣ) :
    ((conjDiag Cg p : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) =
      (Cg : Matrix (HypIndex 1 1) (HypIndex 1 1) K) *
        Matrix.diagonal (fun i => (triEntry p i : K)) *
          (((Cg⁻¹ : GL (HypIndex 1 1) K)) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) := by
  change (((MulAut.conj Cg) (diagTriple p) : GL (HypIndex 1 1) K) :
      Matrix (HypIndex 1 1) (HypIndex 1 1) K) = _
  rw [MulAut.conj_apply, Units.val_mul, Units.val_mul, coe_diagTriple]

private theorem conjDiag_mem_hypUnitary (h : UnitaryFieldData 2 n K) {c cb : K} (hcb : h.bar c = cb)
    (hc : c + cb = 1) (h2 : (2 : K) = 0) (Cg : GL (HypIndex 1 1) K)
    (hCg : (Cg : Matrix (HypIndex 1 1) (HypIndex 1 1) K) = cbMat c cb)
    (hCgiv : (((Cg⁻¹ : GL (HypIndex 1 1) K)) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) =
      cbInvMat c cb)
    (p : Kˣ × Kˣ × Kˣ) (hp : ∀ i, h.bar (triEntry p i : K) * (triEntry p i : K) = 1) :
    conjDiag Cg p ∈ hypUnitary h 1 1 := by
  rw [mem_hypUnitary, coe_conjDiag, hCg, hCgiv]
  set D : Matrix (HypIndex 1 1) (HypIndex 1 1) K :=
    Matrix.diagonal (fun i => (triEntry p i : K)) with hD
  have hDbar : (D.map h.bar)ᵀ * D = 1 := by
    rw [hD, Matrix.diagonal_map (map_zero h.bar), Matrix.diagonal_transpose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact hp i
  calc
    ((cbMat c cb * D * cbInvMat c cb).map h.bar)ᵀ * hypGram 1 1 K *
        (cbMat c cb * D * cbInvMat c cb)
        = ((cbInvMat c cb).map h.bar)ᵀ * ((D.map h.bar)ᵀ *
            (((cbMat c cb).map h.bar)ᵀ * hypGram 1 1 K * cbMat c cb) * D * cbInvMat c cb) := by
          simp only [Matrix.map_mul, Matrix.transpose_mul]
          noncomm_ring
    _ = ((cbInvMat c cb).map h.bar)ᵀ * ((D.map h.bar)ᵀ * D * cbInvMat c cb) := by
          rw [cbMat_gram h hcb hc h2]
          noncomm_ring
    _ = ((cbInvMat c cb).map h.bar)ᵀ * cbInvMat c cb := by
          rw [hDbar]
          noncomm_ring
    _ = hypGram 1 1 K := cbInvMat_gram h hcb hc h2

private def tripleSubtype (μ : Subgroup Kˣ) :
    (↥μ × ↥μ × ↥μ) →* (Kˣ × Kˣ × Kˣ) :=
  MonoidHom.mk' (fun p => ((p.1 : Kˣ), (p.2.1 : Kˣ), (p.2.2 : Kˣ))) (fun a b => rfl)

private theorem tripleSubtype_injective (μ : Subgroup Kˣ) :
    Function.Injective (tripleSubtype μ) := by
  intro a b h
  have h1 : ((a.1 : Kˣ)) = ((b.1 : Kˣ)) := congrArg (fun z : Kˣ × Kˣ × Kˣ => z.1) h
  have h2 : ((a.2.1 : Kˣ)) = ((b.2.1 : Kˣ)) := congrArg (fun z : Kˣ × Kˣ × Kˣ => z.2.1) h
  have h3 : ((a.2.2 : Kˣ)) = ((b.2.2 : Kˣ)) := congrArg (fun z : Kˣ × Kˣ × Kˣ => z.2.2) h
  exact Prod.ext (Subtype.ext h1) (Prod.ext (Subtype.ext h2) (Subtype.ext h3))

theorem exists_prime_elemAbelian_le_projIsoStabilizer (h : UnitaryFieldData 2 n K) (hn : n ≠ 2) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ≠ 5 ∧ p ∣ 2 ^ n + 1 ∧
      ∃ E : Subgroup (hypPSU h 2 1),
        E ≤ projIsoStabilizer h 2 1 (hypFlag h 2 1 1) ∧
          IsElemAbelian p E ∧ Nat.card E = p ^ 3 := by
  classical
  have h2v : (2 : K) = 0 := by
    haveI : CharP K 2 := h.charP
    exact CharP.cast_eq_zero K 2
  obtain ⟨p, hp, hp2, hp5, hpd⟩ :=
    CFSG.SectionRank.QTK.exists_prime_ne_five_dvd_two_pow_add_one h.one_le hn
  obtain ⟨c, hc⟩ := exists_add_bar_eq_one h
  obtain ⟨μ, hμcard, hμexp, hμbar⟩ := exists_pthRoots_subgroup h hp hpd
  set C : Matrix (HypIndex 1 1) (HypIndex 1 1) K := cbMat c (h.bar c) with hCdef
  set Cinv : Matrix (HypIndex 1 1) (HypIndex 1 1) K := cbInvMat c (h.bar c) with hCinvdef
  have hCm : C * Cinv = 1 := cbMat_mul_cbInvMat c (h.bar c) hc h2v
  have hCim : Cinv * C = 1 := cbInvMat_mul_cbMat c (h.bar c) hc h2v
  let Cg : GL (HypIndex 1 1) K := ⟨C, Cinv, hCm, hCim⟩
  have hCgval : (Cg : Matrix (HypIndex 1 1) (HypIndex 1 1) K) = cbMat c (h.bar c) := rfl
  have hCgivval : (((Cg⁻¹ : GL (HypIndex 1 1) K)) :
      Matrix (HypIndex 1 1) (HypIndex 1 1) K) = cbInvMat c (h.bar c) := rfl
  set Ψ : (↥μ × ↥μ × ↥μ) →* GL (HypIndex 1 1) K :=
    (conjDiag Cg).comp (tripleSubtype μ) with hΨdef
  have hΨmem : ∀ a : ↥μ × ↥μ × ↥μ, Ψ a ∈ hypUnitary h 1 1 := by
    intro a
    have hbar1 : ∀ i, h.bar (triEntry (tripleSubtype μ a) i : K) *
        (triEntry (tripleSubtype μ a) i : K) = 1 := by
      intro i
      rcases i with i | k | i
      · exact hμbar a.1
      · exact hμbar a.2.1
      · exact hμbar a.2.2
    exact conjDiag_mem_hypUnitary h rfl hc h2v Cg hCgval hCgivval _ hbar1
  have hΨinj : Function.Injective Ψ :=
    (conjDiag_injective Cg).comp (tripleSubtype_injective μ)
  have hexp : ∀ a : ↥μ × ↥μ × ↥μ, a ^ p = 1 := by
    intro a
    exact Prod.ext (hμexp a.1) (Prod.ext (hμexp a.2.1) (hμexp a.2.2))
  have hcomm : ∀ a b : ↥μ × ↥μ × ↥μ, a * b = b * a := by
    intro a b
    exact Prod.ext (mul_comm _ _) (Prod.ext (mul_comm _ _) (mul_comm _ _))
  have hfs : flagStabilizer h 2 1 ({1} : Set ℕ) = isoStabilizer h 2 1 (hypFlag h 2 1 1) := by
    simp [flagStabilizer]
  set Φ : (↥μ × ↥μ × ↥μ) →* hypPSU h 2 1 :=
    (hypProj h 2 1).comp
      ((CFSG.AGLEmbedding.LeviBlock.guEmbed (t := 1) (s := 1) (ε := 1) h (by norm_num)
        (by norm_num)).comp (Ψ.codRestrict (hypUnitary h 1 1) hΨmem)) with hΦdef
  have hΦker : ∀ a : ↥μ × ↥μ × ↥μ, Φ a = 1 → a = 1 := by
    intro a ha
    set B : hypUnitary h 1 1 := Ψ.codRestrict (hypUnitary h 1 1) hΨmem a with hB
    have hBp : B ^ p = 1 := by
      rw [hB, ← map_pow, hexp a, map_one]
    have hscal : (CFSG.AGLEmbedding.LeviBlock.guEmbed (t := 1) (s := 1) (ε := 1) h (by norm_num)
        (by norm_num)) B ∈ hypScalars h 2 1 := by
      rw [← ker_hypProj]
      show hypProj h 2 1 ((CFSG.AGLEmbedding.LeviBlock.guEmbed (t := 1) (s := 1) (ε := 1) h
        (by norm_num) (by norm_num)) B) = 1
      simpa [hΦdef, hB] using ha
    have hcop : Nat.Coprime 5 p := by
      have h1 : Nat.Coprime p 5 := (Nat.Prime.coprime_iff_not_dvd hp).mpr (by
        rintro hdvd
        have hp2 : 2 ≤ p := hp.two_le
        have hle : p ≤ 5 := Nat.le_of_dvd (by norm_num) hdvd
        have h4 : p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 := by omega
        rcases h4 with rfl | rfl | rfl | rfl
        · norm_num at hdvd
        · norm_num at hdvd
        · norm_num at hdvd
        · exact absurd rfl hp5)
      exact h1.symm
    have hx5 : ((CFSG.AGLEmbedding.LeviBlock.guEmbed (t := 1) (s := 1) (ε := 1) h (by norm_num)
        (by norm_num)) B) ^ 5 = 1 := by
      obtain ⟨cc, -, hcc5, hval⟩ := mem_normOneScalars.mp hscal
      apply Subtype.ext
      show ((((CFSG.AGLEmbedding.LeviBlock.guEmbed (t := 1) (s := 1) (ε := 1) h (by norm_num)
        (by norm_num)) B : hypSU h 2 1) : GL (HypIndex 2 1) K)) ^ 5 = 1
      rw [hval, ← map_pow, hcc5, map_one]
    have hxp : ((CFSG.AGLEmbedding.LeviBlock.guEmbed (t := 1) (s := 1) (ε := 1) h (by norm_num)
        (by norm_num)) B) ^ p = 1 := by
      rw [← map_pow, hBp, map_one]
    have h1 : ((CFSG.AGLEmbedding.LeviBlock.guEmbed (t := 1) (s := 1) (ε := 1) h (by norm_num)
        (by norm_num)) B) = 1 := by
      have h2 := (pow_gcd_eq_one (a := (CFSG.AGLEmbedding.LeviBlock.guEmbed (t := 1) (s := 1)
        (ε := 1) h (by norm_num) (by norm_num)) B)).mpr ⟨hx5, hxp⟩
      rwa [Nat.Coprime.gcd_eq_one hcop, pow_one] at h2
    have hB1 : B = 1 :=
      CFSG.AGLEmbedding.LeviBlock.guEmbed_injective h (t := 1) (s := 1) (ε := 1)
        (by norm_num) (by norm_num) (by rw [h1, map_one])
    have h2 : Ψ a = 1 := by
      have h3 : (Ψ.codRestrict (hypUnitary h 1 1) hΨmem a) = 1 := hB1
      exact Subtype.ext_iff.mp h3
    exact hΨinj (by rw [h2, map_one])
  have hΦinj : Function.Injective Φ := by
    intro a b hab
    have h1 : Φ (a * b⁻¹) = 1 := by
      rw [map_mul, map_inv, hab, mul_inv_cancel]
    have := hΦker (a * b⁻¹) h1
    rwa [mul_inv_eq_one] at this
  refine ⟨p, hp, hp2, hp5, hpd, Φ.range, ?_, ?_, ?_⟩
  ·
    rintro _ ⟨a, rfl⟩
    have hI : ∀ c ∈ ({1} : Set ℕ), c ≤ 1 := by
      intro c hc
      rw [Set.mem_singleton_iff] at hc
      omega
    refine Subgroup.mem_map_of_mem _ ?_
    have h := CFSG.AGLEmbedding.LeviBlock.guEmbed_mem_flagStabilizer h (s := 1) (ε := 1)
      (by norm_num) (by norm_num) (I := ({1} : Set ℕ)) hI
      (Ψ.codRestrict (hypUnitary h 1 1) hΨmem a)
    rwa [hfs] at h
  ·
    refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
    · apply Subtype.ext
      show (x : hypPSU h 2 1) * (y : hypPSU h 2 1) = (y : hypPSU h 2 1) * (x : hypPSU h 2 1)
      obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp x.2
      obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp y.2
      rw [← ha, ← hb, ← map_mul, ← map_mul, hcomm]
    · show (x : hypPSU h 2 1) ^ p = 1
      obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp hx
      rw [← ha, ← map_pow, hexp a, map_one]
  ·
    have h1 : Nat.card ↥Φ.range = Nat.card (↥μ × ↥μ × ↥μ) :=
      (Nat.card_congr (MonoidHom.ofInjective hΦinj).toEquiv).symm
    rw [h1, Nat.card_prod, Nat.card_prod, hμcard]
    ring

theorem exists_prime_three_le_pRank_projIsoStabilizer (h : UnitaryFieldData 2 n K) (hn : n ≠ 2) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ≠ 5 ∧ p ∣ 2 ^ n + 1 ∧
      3 ≤ CFSG.Open.pRank p (projIsoStabilizer h 2 1 (hypFlag h 2 1 1)) := by
  obtain ⟨p, hp, hp2, hp5, hpd, E, hE, hEel, hEcard⟩ :=
    exists_prime_elemAbelian_le_projIsoStabilizer h hn
  exact ⟨p, hp, hp2, hp5, hpd, CFSG.SectionRank.le_pRank hp.one_lt hE hEel hEcard⟩

end CFSG.ClassicalGroups.UnitaryFlag
