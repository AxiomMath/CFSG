module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGenNode
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeMult

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGen

open Matrix CFSG.LieType.Universal CFSG.LieType.Universal.Unitary CFSG.LieType.CurtisTits
  CFSG.LieType.Steinberg CFSG.LieType.BorelTits CFSG.AGLEmbedding.ParabHub

section Block

variable {F : Type} [Field F] [CharP F 2] {σ : F ≃+* F} (k : Subfield F)

omit [CharP F 2] in
theorem antidiag_three : (antidiag 3 : Matrix (Fin 3) (Fin 3) F) = !![0, 0, 1; 0, 1, 0; 1, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [antidiag]

@[expose] def blk3 (A : Matrix (Fin 2) (Fin 2) k) : Matrix (Fin 3) (Fin 3) F :=
  !![(A 0 0 : F), 0, (A 0 1 : F); 0, 1, 0; (A 1 0 : F), 0, (A 1 1 : F)]

omit [CharP F 2] in
theorem blk3_mul (A B : Matrix (Fin 2) (Fin 2) k) : blk3 k (A * B) = blk3 k A * blk3 k B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blk3, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two]

omit [CharP F 2] in
theorem blk3_one : blk3 k (1 : Matrix (Fin 2) (Fin 2) k) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blk3]

omit [CharP F 2] in
theorem det_blk3 (A : Matrix (Fin 2) (Fin 2) k) : (blk3 k A).det = ((A.det : k) : F) := by
  rw [Matrix.det_fin_three, Matrix.det_fin_two]
  simp [blk3]

theorem blk3_isometry (hk : ∀ c ∈ k, σ c = c) {A : Matrix (Fin 2) (Fin 2) k} (hA : A.det = 1) :
    conjTr σ (blk3 k A) * antidiag 3 * blk3 k A = antidiag 3 := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hdet : ((A 0 0 : F) * A 1 1 - A 0 1 * A 1 0) = 1 := by
    have := congrArg (fun x : k => (x : F)) hA
    simpa [Matrix.det_fin_two] using this
  have hfix : ∀ a : k, σ (a : F) = a := fun a => hk a a.2
  rw [antidiag_three]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [conjTr, blk3, Matrix.mul_apply, Fin.sum_univ_three, hfix] <;>
    first | ring1 | linear_combination hdet + (A 0 1 * A 1 0 : F) * h2 |
      linear_combination (A 0 0 * A 1 0 : F) * h2 | linear_combination (A 0 1 * A 1 1 : F) * h2

@[expose] noncomputable def blk3Elt (hk : ∀ c ∈ k, σ c = c)
    (A : Matrix.SpecialLinearGroup (Fin 2) k) : SU σ 3 :=
  ⟨⟨blk3 k (A : Matrix (Fin 2) (Fin 2) k),
      blk3 k ((A⁻¹ : Matrix.SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k),
      by rw [← blk3_mul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.SpecialLinearGroup.coe_one, blk3_one],
      by rw [← blk3_mul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.SpecialLinearGroup.coe_one, blk3_one]⟩,
    by rw [Units.val_mk, det_blk3, A.2]; rfl,
    blk3_isometry k hk A.2⟩

theorem coe_blk3Elt (hk : ∀ c ∈ k, σ c = c) (A : Matrix.SpecialLinearGroup (Fin 2) k) :
    ((blk3Elt k hk A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      blk3 k (A : Matrix (Fin 2) (Fin 2) k) :=
  rfl

@[expose] noncomputable def blk3Hom (hk : ∀ c ∈ k, σ c = c) :
    Matrix.SpecialLinearGroup (Fin 2) k →* SU σ 3 :=
  MonoidHom.mk' (blk3Elt k hk) fun A B => Subtype.ext (Units.ext (by
    rw [Subgroup.coe_mul, Units.val_mul, coe_blk3Elt, coe_blk3Elt, coe_blk3Elt,
      Matrix.SpecialLinearGroup.coe_mul, blk3_mul]))

theorem blk3Hom_injective (hk : ∀ c ∈ k, σ c = c) : Function.Injective (blk3Hom (σ := σ) k hk) := by
  intro A B h
  have h' := congrArg (fun g : SU σ 3 => ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) h
  simp only [blk3Hom, MonoidHom.mk'_apply, coe_blk3Elt] at h'
  have key : ∀ a b : Fin 3, blk3 k (A : Matrix (Fin 2) (Fin 2) k) a b =
      blk3 k (B : Matrix (Fin 2) (Fin 2) k) a b := fun a b => by rw [h']
  have e00 : (((A : Matrix (Fin 2) (Fin 2) k) 0 0 : k) : F) =
      (((B : Matrix (Fin 2) (Fin 2) k) 0 0 : k) : F) := by simpa [blk3] using key 0 0
  have e01 : (((A : Matrix (Fin 2) (Fin 2) k) 0 1 : k) : F) =
      (((B : Matrix (Fin 2) (Fin 2) k) 0 1 : k) : F) := by simpa [blk3] using key 0 2
  have e10 : (((A : Matrix (Fin 2) (Fin 2) k) 1 0 : k) : F) =
      (((B : Matrix (Fin 2) (Fin 2) k) 1 0 : k) : F) := by simpa [blk3] using key 2 0
  have e11 : (((A : Matrix (Fin 2) (Fin 2) k) 1 1 : k) : F) =
      (((B : Matrix (Fin 2) (Fin 2) k) 1 1 : k) : F) := by simpa [blk3] using key 2 2
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j
  · simpa using e00
  · simpa using e01
  · simpa using e10
  · simpa using e11

end Block


theorem oddNode_of_mulEquiv {K G : Type*} [Group K] [Group G] {R : Subgroup K} {p : ℕ}
    (e : ↥R ≃* G) (h : ∃ w n : G, w ^ p = 1 ∧ w ≠ 1 ∧ n * w * n⁻¹ = w⁻¹) : OddNode R p := by
  obtain ⟨w, n, hw, hw1, hn⟩ := h
  refine ⟨((e.symm w : ↥R) : K), (e.symm w).2, ((e.symm n : ↥R) : K), (e.symm n).2, ?_, ?_, ?_⟩
  · have : (e.symm w) ^ p = 1 := by rw [← map_pow, hw, map_one]
    exact congrArg Subtype.val this
  · intro h1
    apply hw1
    have : e.symm w = 1 := Subtype.ext h1
    simpa using this
  · have := congrArg e.symm hn
    simp only [map_mul, map_inv] at this
    exact congrArg Subtype.val this

theorem dvd_sq_sq_sub_one_of_dvd_add_one {q p : ℕ} (hq : 1 ≤ q) (h : p ∣ q + 1) :
    p ∣ (q ^ 2) ^ 2 - 1 := by
  obtain ⟨-, h1⟩ := CFSG.AGLEmbedding.ParabPrime.sub_one_dvd_and_add_one_dvd q hq
  obtain ⟨h2, -⟩ := CFSG.AGLEmbedding.ParabPrime.sub_one_dvd_and_add_one_dvd (q ^ 2)
    (Nat.one_le_pow _ _ hq)
  exact h.trans (h1.trans h2)

section Nodes

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2)

theorem oddNode_su {n : ℕ} (hn : 3 ≤ n) (i : Fin (n / 2)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpd : p ∣ 2 ^ f + 1) : OddNode (rankOne (rootDatum hF n).rootGroup i) p := by
  have hf1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  by_cases hk : i.val + 1 < n / 2
  · refine oddNode_of_hasSL2Node (hasSL2Node_su_short hF hk) hp hp2 ?_
    rw [hF]
    exact dvd_sq_sq_sub_one_of_dvd_add_one hf1 hpd
  · obtain ⟨ζ, hζ0, hζ⟩ := exists_unitaryInvolution_eq_neg hF
    have hcard : Nat.card (fixedSubfield F 2 f) = 2 ^ f := card_fixedSubfield hF
    have hpd' : p ∣ Nat.card (fixedSubfield F 2 f) ^ 2 - 1 := by
      rw [hcard]
      exact hpd.trans (CFSG.AGLEmbedding.ParabPrime.sub_one_dvd_and_add_one_dvd _ hf1).2
    obtain ⟨w, m, hw, hw1, hm⟩ := exists_order_inverted_sl2 (F := fixedSubfield F 2 f) hp hp2 hpd'
    by_cases he : Even n
    · obtain ⟨e⟩ := nonempty_rankOne_last_even_mulEquiv hF he (by omega) hk
      exact oddNode_of_mulEquiv (e.trans (hypEquiv hζ0 hζ).symm) ⟨w, m, hw, hw1, hm⟩
    · obtain ⟨e⟩ := nonempty_rankOne_last_odd_mulEquiv hF he hn hk
      have hk' : ∀ c ∈ fixedSubfield F 2 f, unitaryInvolution F 2 f c = c := fun c hc =>
        mem_fixedSubfield.1 hc
      refine oddNode_of_mulEquiv e ⟨blk3Hom (fixedSubfield F 2 f) hk' w,
        blk3Hom (fixedSubfield F 2 f) hk' m, by rw [← map_pow, hw, map_one],
        fun h => hw1 (blk3Hom_injective (fixedSubfield F 2 f) hk' (by rw [h, map_one])), ?_⟩
      simpa [map_mul, map_inv] using congrArg (blk3Hom (fixedSubfield F 2 f) hk') hm

end Nodes

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGen
