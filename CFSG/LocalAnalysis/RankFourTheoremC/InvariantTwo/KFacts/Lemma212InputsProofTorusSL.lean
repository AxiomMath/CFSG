module

public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

namespace L212TorusSL

open Matrix

section Eigen

variable {K : Type*} [Field K] {n : ℕ}

private theorem sum_range_succ_of_periodic {M : Type*} [AddCommGroup M] (g : ℕ → M) (p : ℕ)
    (h : g p = g 0) : ∑ j ∈ Finset.range p, g (j + 1) = ∑ j ∈ Finset.range p, g j := by
  have h1 := Finset.sum_range_succ g p
  have h2 := Finset.sum_range_succ' g p
  rw [h] at h1
  exact add_right_cancel (h2.symm.trans h1)

private def eigProj (A : Matrix (Fin n) (Fin n) K) (ω : K) (p i : ℕ) (v : Fin n → K) : Fin n → K :=
  ∑ j ∈ Finset.range p, ω ^ (i * j) • ((A ^ j) *ᵥ v)

private theorem mulVec_eigProj (A : Matrix (Fin n) (Fin n) K) {ω : K} {p : ℕ} (hp : 0 < p)
    (hA : A ^ p = 1) (hω : ω ^ p = 1) (i : ℕ) (v : Fin n → K) :
    A *ᵥ eigProj A ω p i v = (ω ^ i)⁻¹ • eigProj A ω p i v := by
  have hω0 : ω ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne'] at hω
    exact zero_ne_one hω
  have key : ω ^ i • (A *ᵥ eigProj A ω p i v) = eigProj A ω p i v := by
    have h := sum_range_succ_of_periodic (fun j => ω ^ (i * j) • ((A ^ j) *ᵥ v)) p (by
      simp only [mul_zero, pow_zero, one_smul, Matrix.one_mulVec]
      rw [mul_comm, pow_mul, hω, one_pow, one_smul, hA, Matrix.one_mulVec])
    unfold eigProj
    rw [Matrix.mulVec_sum, Finset.smul_sum]
    refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_) h
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← pow_succ', smul_comm, smul_smul, ← pow_add,
      mul_add, mul_one]
  calc A *ᵥ eigProj A ω p i v = (ω ^ i)⁻¹ • (ω ^ i • (A *ᵥ eigProj A ω p i v)) :=
        (inv_smul_smul₀ (pow_ne_zero i hω0) _).symm
    _ = (ω ^ i)⁻¹ • eigProj A ω p i v := by rw [key]

private theorem sum_eigProj (A : Matrix (Fin n) (Fin n) K) {ω : K} {p : ℕ}
    (hω : IsPrimitiveRoot ω p) (hp : 0 < p) (v : Fin n → K) :
    ∑ i ∈ Finset.range p, eigProj A ω p i v = (p : K) • v := by
  unfold eigProj
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro j hj hj0
    have hne : ω ^ j ≠ 1 := hω.pow_ne_one_of_pos_of_lt hj0 (Finset.mem_range.1 hj)
    have hpow : (ω ^ j) ^ p = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow]
    have h1 : (∑ i ∈ Finset.range p, (ω ^ j) ^ i) * (ω ^ j - 1) = (ω ^ j) ^ p - 1 :=
      geom_sum_mul _ _
    rw [hpow, sub_self] at h1
    have hgeom : ∑ i ∈ Finset.range p, ω ^ (i * j) = 0 := by
      simpa only [pow_mul'] using (mul_eq_zero.1 h1).resolve_right (sub_ne_zero.2 hne)
    rw [hgeom, zero_smul]
  · intro h
    exact absurd (Finset.mem_range.2 hp) h

private theorem top_le_span_eigenvectors (A : Matrix (Fin n) (Fin n) K) {ω : K} {p : ℕ}
    (hω : IsPrimitiveRoot ω p) (hp : 0 < p) (hpK : (p : K) ≠ 0) (hA : A ^ p = 1) :
    ⊤ ≤ Submodule.span K {w : Fin n → K | ∃ μ : K, A *ᵥ w = μ • w} := by
  intro v _
  have hv : v = (p : K)⁻¹ • ∑ i ∈ Finset.range p, eigProj A ω p i v := by
    rw [sum_eigProj A hω hp v, inv_smul_smul₀ hpK]
  rw [hv]
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ => Submodule.subset_span ?_)
  exact ⟨_, mulVec_eigProj A hp hA hω.pow_eq_one i v⟩

end Eigen

section Basis

variable {K : Type*} [Field K] {n : ℕ}

private theorem exists_eigenbasis_matrix (A : Matrix (Fin n) (Fin n) K)
    (hspan : ⊤ ≤ Submodule.span K {w : Fin n → K | ∃ μ : K, A *ᵥ w = μ • w}) :
    ∃ (P Q : Matrix (Fin n) (Fin n) K) (u : Fin n → K),
      P * Q = 1 ∧ Q * P = 1 ∧ A * P = P * diagonal u := by
  classical
  let b0 := Module.Basis.ofSpan hspan
  let e := b0.indexEquiv (Pi.basisFun K (Fin n))
  let b := b0.reindex e
  have hb : ∀ j, ∃ μ : K, A *ᵥ b j = μ • b j := by
    intro j
    have h : b0 (e.symm j) ∈ {w : Fin n → K | ∃ μ : K, A *ᵥ w = μ • w} :=
      Module.Basis.ofSpan_subset hspan ⟨e.symm j, rfl⟩
    simpa [b, Module.Basis.reindex_apply] using h
  choose u hu using hb
  refine ⟨(Pi.basisFun K (Fin n)).toMatrix b, b.toMatrix (Pi.basisFun K (Fin n)), u, ?_, ?_, ?_⟩
  · exact Module.Basis.toMatrix_mul_toMatrix_flip _ _
  · exact Module.Basis.toMatrix_mul_toMatrix_flip _ _
  · ext i j
    rw [Matrix.mul_diagonal]
    have h := congrFun (hu j) i
    simpa [Matrix.mul_apply, Module.Basis.toMatrix_apply, Matrix.mulVec, dotProduct,
      mul_comm] using h

end Basis

section Torus

variable {K : Type*} [Field K] {n : ℕ}

private theorem conj_diagonal_mul (P Q : Matrix (Fin n) (Fin n) K) (hQP : Q * P = 1)
    (a b : Fin n → K) :
    (P * diagonal a * Q) * (P * diagonal b * Q) = P * diagonal (fun j => a j * b j) * Q := by
  calc (P * diagonal a * Q) * (P * diagonal b * Q)
      = P * diagonal a * (Q * P) * diagonal b * Q := by simp only [Matrix.mul_assoc]
    _ = P * (diagonal a * diagonal b) * Q := by
        rw [hQP, Matrix.mul_one, ← Matrix.mul_assoc P]
    _ = P * diagonal (fun j => a j * b j) * Q := by rw [diagonal_mul_diagonal]

private def conjSL (P Q : Matrix (Fin n) (Fin n) K) (hQP : Q * P = 1) (a : Fin n → K)
    (ha : ∏ j, a j = 1) : SpecialLinearGroup (Fin n) K :=
  ⟨P * diagonal a * Q, by
    rw [Matrix.det_mul_comm, ← Matrix.mul_assoc, hQP, Matrix.one_mul, Matrix.det_diagonal]
    exact ha⟩

private theorem coe_conjSL (P Q : Matrix (Fin n) (Fin n) K) (hQP : Q * P = 1) (a : Fin n → K)
    (ha : ∏ j, a j = 1) :
    (conjSL P Q hQP a ha : Matrix (Fin n) (Fin n) K) = P * diagonal a * Q :=
  rfl

private def conjDiag {G : Type*} [Group G] (P Q : Matrix (Fin n) (Fin n) K) (hPQ : P * Q = 1)
    (hQP : Q * P = 1) (κ : G →* (Fin n → Kˣ)) (hdet : ∀ g, ∏ j, ((κ g j : Kˣ) : K) = 1) :
    G →* SpecialLinearGroup (Fin n) K where
  toFun g := conjSL P Q hQP (fun j => ((κ g j : Kˣ) : K)) (hdet g)
  map_one' := by
    apply Subtype.ext
    rw [coe_conjSL, SpecialLinearGroup.coe_one]
    simp [hPQ]
  map_mul' g h := by
    apply Subtype.ext
    rw [SpecialLinearGroup.coe_mul, coe_conjSL, coe_conjSL, coe_conjSL,
      conj_diagonal_mul P Q hQP]
    simp [map_mul]

private theorem coe_conjDiag {G : Type*} [Group G] (P Q : Matrix (Fin n) (Fin n) K)
    (hPQ : P * Q = 1) (hQP : Q * P = 1) (κ : G →* (Fin n → Kˣ))
    (hdet : ∀ g, ∏ j, ((κ g j : Kˣ) : K) = 1) (g : G) :
    (conjDiag P Q hPQ hQP κ hdet g : Matrix (Fin n) (Fin n) K) =
      P * diagonal (fun j => ((κ g j : Kˣ) : K)) * Q :=
  rfl

private theorem entries_eq_of_conj_eq_scalar (P Q : Matrix (Fin n) (Fin n) K) (hQP : Q * P = 1)
    (a : Fin n → K) (c : K) (h : P * diagonal a * Q = scalar (Fin n) c) (j : Fin n) :
    a j = c := by
  have h1 : diagonal a = scalar (Fin n) c := by
    calc diagonal a = (Q * P) * diagonal a * (Q * P) := by
          rw [hQP, Matrix.one_mul, Matrix.mul_one]
      _ = Q * (P * diagonal a * Q) * P := by simp only [Matrix.mul_assoc]
      _ = Q * scalar (Fin n) c * P := by rw [h]
      _ = scalar (Fin n) c := by
          rw [← (Matrix.scalar_commute c (fun _ => Commute.all _ _) Q).eq, Matrix.mul_assoc, hQP,
            Matrix.mul_one]
  have h2 := congrFun (congrFun h1 j) j
  simpa [Matrix.diagonal_apply_eq, Matrix.scalar_apply] using h2

private theorem commute_conj_diagonal (P Q : Matrix (Fin n) (Fin n) K) (hPQ : P * Q = 1)
    (hQP : Q * P = 1) (A : Matrix (Fin n) (Fin n) K) (u : Fin n → K)
    (hAP : A * P = P * diagonal u) (a : Fin n → K) :
    (P * diagonal a * Q) * A = A * (P * diagonal a * Q) := by
  have hQA : Q * A = diagonal u * Q := by
    calc Q * A = Q * A * (P * Q) := by rw [hPQ, Matrix.mul_one]
      _ = Q * (A * P) * Q := by simp only [Matrix.mul_assoc]
      _ = Q * (P * diagonal u) * Q := by rw [hAP]
      _ = (Q * P) * diagonal u * Q := by simp only [Matrix.mul_assoc]
      _ = diagonal u * Q := by rw [hQP, Matrix.one_mul]
  calc (P * diagonal a * Q) * A = P * diagonal a * (Q * A) := by simp only [Matrix.mul_assoc]
    _ = P * (diagonal a * diagonal u) * Q := by rw [hQA]; simp only [Matrix.mul_assoc]
    _ = P * (diagonal u * diagonal a) * Q := by
        rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
        simp only [mul_comm]
    _ = (P * diagonal u) * diagonal a * Q := by simp only [Matrix.mul_assoc]
    _ = A * P * diagonal a * Q := by rw [hAP]
    _ = A * (P * diagonal a * Q) := by simp only [Matrix.mul_assoc]

private def torusEntry {G : Type*} [Group G] (a₀ a₁ a₂ : G →* Kˣ) : ℕ → (G →* Kˣ)
  | 0 => a₀
  | 1 => a₁
  | 2 => a₂
  | 3 => (a₀ * a₁ * a₂)⁻¹
  | _ + 4 => 1

private theorem prod_torusEntry {G : Type*} [Group G] (a₀ a₁ a₂ : G →* Kˣ) (hn : 4 ≤ n)
    (x : G) : ∏ j : Fin n, torusEntry a₀ a₁ a₂ j.val x = 1 := by
  rw [Fin.prod_univ_eq_prod_range (fun i => torusEntry a₀ a₁ a₂ i x) n]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Finset.prod_range_add]
  have h2 : ∏ i ∈ Finset.range m, torusEntry a₀ a₁ a₂ (4 + i) x = 1 := by
    refine Finset.prod_eq_one fun i _ => ?_
    rw [Nat.add_comm]
    rfl
  rw [h2, mul_one]
  simp [Finset.prod_range_succ, torusEntry]

private theorem exists_torus {p : ℕ} (hn : 5 ≤ n) (χ : Multiplicative (ZMod p) →* Kˣ) :
    ∃ κ : (Fin 3 → Multiplicative (ZMod p)) →* (Fin n → Kˣ),
      (∀ x, ∏ j, κ x j = 1) ∧ (∀ x (m : Fin 3), κ x ⟨m.val, by omega⟩ = χ (x m)) ∧
        ∀ x, κ x ⟨4, by omega⟩ = 1 := by
  refine ⟨MonoidHom.pi (fun j : Fin n => torusEntry
    (χ.comp (Pi.evalMonoidHom (fun _ => Multiplicative (ZMod p)) 0))
    (χ.comp (Pi.evalMonoidHom (fun _ => Multiplicative (ZMod p)) 1))
    (χ.comp (Pi.evalMonoidHom (fun _ => Multiplicative (ZMod p)) 2)) j.val), ?_, ?_, ?_⟩
  · intro x
    simpa using prod_torusEntry
      (χ.comp (Pi.evalMonoidHom (fun _ => Multiplicative (ZMod p)) 0))
      (χ.comp (Pi.evalMonoidHom (fun _ => Multiplicative (ZMod p)) 1))
      (χ.comp (Pi.evalMonoidHom (fun _ => Multiplicative (ZMod p)) 2)) (by omega) x
  · intro x m
    fin_cases m <;> simp [torusEntry]
  · intro x
    simp [torusEntry]

end Torus

private theorem exists_injective_hom {p : ℕ} [NeZero p] {K : Type*} [Field K] {ζ : Kˣ}
    (h : IsPrimitiveRoot ζ p) :
    ∃ χ : Multiplicative (ZMod p) →* Kˣ, Function.Injective χ :=
  ⟨(Subgroup.zpowers ζ).subtype.comp (AddEquiv.toMultiplicativeLeft h.zmodEquivZPowers).toMonoidHom,
    Subtype.val_injective.comp (AddEquiv.toMultiplicativeLeft h.zmodEquivZPowers).injective⟩

end L212TorusSL

open L212TorusSL Matrix in
theorem l212in_torusHom_sl {p n : ℕ} (hp : p.Prime) (hn : 5 ≤ n) {K : Type} [Field K] [Finite K]
    (hpK : p ∣ Nat.card K - 1) (s : Matrix.SpecialLinearGroup (Fin n) K) (hs : s ^ p = 1) :
    ∃ f : (Fin 3 → Multiplicative (ZMod p)) →* Matrix.SpecialLinearGroup (Fin n) K,
      Function.Injective f ∧ (∀ x, Commute (f x) s) ∧
      ∀ x, f x ∈ CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars n K → f x = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) p (by rwa [Nat.card_units])
  have hprimU : IsPrimitiveRoot ζ p := by
    rw [← hζ]
    exact IsPrimitiveRoot.orderOf ζ
  have hprim : IsPrimitiveRoot (ζ : K) p :=
    hprimU.map_of_injective (f := Units.coeHom K) Units.val_injective
  haveI : NeZero (p : K) := hprim.neZero'
  have hA : (s : Matrix (Fin n) (Fin n) K) ^ p = 1 := by
    rw [← SpecialLinearGroup.coe_pow, hs, SpecialLinearGroup.coe_one]
  obtain ⟨P, Q, u, hPQ, hQP, hAP⟩ := exists_eigenbasis_matrix (s : Matrix (Fin n) (Fin n) K)
    (top_le_span_eigenvectors _ hprim hp.pos (NeZero.ne _) hA)
  obtain ⟨χ, hχ⟩ := exists_injective_hom hprimU
  obtain ⟨κ, hκdet, hκ, hκ4⟩ := exists_torus hn χ
  have hdet : ∀ x, ∏ j, ((κ x j : Kˣ) : K) = 1 := by
    intro x
    rw [← Units.coe_prod, hκdet x, Units.val_one]
  refine ⟨conjDiag P Q hPQ hQP κ hdet, ?_, ?_, ?_⟩
  · rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : ∀ j, ((κ x j : Kˣ) : K) = 1 := by
      intro j
      refine entries_eq_of_conj_eq_scalar P Q hQP (fun j => ((κ x j : Kˣ) : K)) 1 ?_ j
      rw [map_one, ← coe_conjDiag P Q hPQ hQP κ hdet x, hx]
      rfl
    funext m
    apply hχ
    show χ (x m) = χ 1
    rw [map_one, ← hκ x m]
    exact Units.val_eq_one.1 (h1 _)
  · intro x
    show conjDiag P Q hPQ hQP κ hdet x * s = s * conjDiag P Q hPQ hQP κ hdet x
    apply Subtype.ext
    rw [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul,
      coe_conjDiag P Q hPQ hQP κ hdet x]
    exact commute_conj_diagonal P Q hPQ hQP _ u hAP _
  · intro x hx
    obtain ⟨c, -, hc⟩ := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.mem_scalars.1 hx
    have h1 : ∀ j, ((κ x j : Kˣ) : K) = (c : K) := fun j =>
      entries_eq_of_conj_eq_scalar P Q hQP (fun j => ((κ x j : Kˣ) : K)) c
        ((coe_conjDiag P Q hPQ hQP κ hdet x).symm.trans hc) j
    have h4 : (c : K) = 1 := by
      rw [← h1 ⟨4, by omega⟩, hκ4, Units.val_one]
    apply Subtype.ext
    rw [hc, h4, map_one]
    rfl

end CFSG.LocalAnalysis.RankFourTheoremC
