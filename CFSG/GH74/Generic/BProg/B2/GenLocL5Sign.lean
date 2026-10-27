module

public import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupOddHigherLinear
public import CFSG.GH74.Generic.BProg.B2.WeakSigGen

public section

namespace CFSG.GH74.Generic.BProg.B2.GenLocL5Sign

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OddHigherLinear
  CFSG.LocalAnalysis.ComponentInitial.FourGroupOddBilinear CFSG.GH74.Generic.BProg.B2

variable {K : Type} [Field K]

theorem even_symmDiff_card {ι : Type} [DecidableEq ι] {S T : Finset ι} (hS : Even S.card)
    (hT : Even T.card) : Even (symmDiff S T).card := by
  have h1 := Finset.card_union_add_card_inter S T
  have h2 : (symmDiff S T) = (S ∪ T) \ (S ∩ T) := by
    ext x; simp [Finset.mem_symmDiff]; tauto
  rw [h2, Finset.card_sdiff_of_subset (Finset.inter_subset_union)]
  obtain ⟨a, ha⟩ := hS
  obtain ⟨b, hb⟩ := hT
  refine ⟨a + b - (S ∩ T).card, ?_⟩
  have h3 : (S ∩ T).card ≤ (S ∪ T).card := Finset.card_le_card Finset.inter_subset_union
  omega

theorem signSL_mul {n : ℕ} (S T : Finset (Fin n)) (hS : Even S.card) (hT : Even T.card) :
    (signSL S hS * signSL T hT : SpecialLinearGroup (Fin n) K) =
      signSL (symmDiff S T) (even_symmDiff_card hS hT) :=
  Subtype.ext (CLSFourGroupScalarSquare.signDiag_mul_signDiag S T)

theorem signSL_empty {n : ℕ} : (signSL (∅ : Finset (Fin n)) (by simp) : SpecialLinearGroup (Fin n) K) = 1 :=
  Subtype.ext (by
    change signDiag (∅ : Finset (Fin n)) = (1 : Matrix (Fin n) (Fin n) K)
    simp [signDiag, diagonal_one])

@[expose] def signGroup (n : ℕ) (K : Type) [Field K] : Subgroup (LinearFlag.projectiveSL n K) where
  carrier := {x | ∃ (S : Finset (Fin n)) (hS : Even S.card), x = LinearFlag.proj n K (signSL S hS)}
  mul_mem' := by
    rintro _ _ ⟨S, hS, rfl⟩ ⟨T, hT, rfl⟩
    exact ⟨symmDiff S T, even_symmDiff_card hS hT, by rw [← map_mul, signSL_mul]⟩
  one_mem' := ⟨∅, by simp, by rw [signSL_empty, map_one]⟩
  inv_mem' := by
    rintro _ ⟨S, hS, rfl⟩
    exact ⟨S, hS, by rw [← map_inv, inv_eq_of_mul_eq_one_right (signSL_mul_self S hS)]⟩

theorem signGroup_comm {n : ℕ} : ∀ x ∈ signGroup n K, ∀ y ∈ signGroup n K, x * y = y * x := by
  rintro _ ⟨S, hS, rfl⟩ _ ⟨T, hT, rfl⟩
  rw [← map_mul, ← map_mul]
  exact congrArg (LinearFlag.proj n K) (Subtype.ext (signDiag_comm _ _))

theorem signGroup_sq {n : ℕ} : ∀ x ∈ signGroup n K, x * x = 1 := by
  rintro _ ⟨S, hS, rfl⟩
  rw [← map_mul, signSL_mul_self, map_one]

theorem isEA_signGroup (n : ℕ) : CFSG.IsElementaryAbelian 2 ↥(signGroup n K) :=
  WeakSigGen.isElementaryAbelian_of_forall signGroup_comm signGroup_sq

theorem signGroup_inj {n : ℕ} (hn : Odd n) (h2 : (2 : K) ≠ 0) {S T : Finset (Fin n)}
    (hS : Even S.card) (hT : Even T.card)
    (h : LinearFlag.proj n K (signSL S hS) = LinearFlag.proj n K (signSL T hT)) : S = T := by
  classical
  by_contra hne
  have hU : symmDiff S T ≠ ∅ := fun h0 => hne (symmDiff_eq_bot.1 h0)
  have hUe := even_symmDiff_card hS hT
  have hu1 : LinearFlag.proj n K (signSL (symmDiff S T) hUe) = 1 := by
    rw [← signSL_mul S T hS hT, map_mul, h, ← map_mul, signSL_mul_self, map_one]
  obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.2 hU
  have hj : ∃ j, j ∉ symmDiff S T := by
    by_contra hall
    push Not at hall
    have : symmDiff S T = Finset.univ := Finset.eq_univ_iff_forall.2 hall
    rw [this, Finset.card_univ, Fintype.card_fin] at hUe
    exact (Nat.not_even_iff_odd.2 hn) hUe
  obtain ⟨j, hj⟩ := hj
  exact proj_signSL_ne_one h2 hUe hi hj hu1

theorem card_signGroup {n : ℕ} (hn : n = 5) (h2 : (2 : K) ≠ 0) : Nat.card ↥(signGroup n K) = 16 := by
  subst hn
  let φ : {S : Finset (Fin 5) // Even S.card} → ↥(signGroup 5 K) := fun S =>
    ⟨LinearFlag.proj 5 K (signSL S.1 S.2), S.1, S.2, rfl⟩
  have hφ : Function.Bijective φ := by
    refine ⟨fun S T h => Subtype.ext
      (signGroup_inj (by decide) h2 S.2 T.2 (congrArg Subtype.val h)), ?_⟩
    rintro ⟨_, S, hS, rfl⟩
    exact ⟨⟨S, hS⟩, rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective φ hφ), Nat.card_eq_fintype_card]
  decide

theorem exists_orthogonal_congr (hK : ringChar K ≠ 2) {n : ℕ} (R : Matrix (Fin n) (Fin n) K)
    (hR : Rᵀ = R) :
    ∃ B : GL (Fin n) K, ∀ i j, i ≠ j → ((B : Matrix (Fin n) (Fin n) K)ᵀ * R * B) i j = 0 := by
  classical
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have : Invertible (2 : K) := invertibleOfNonzero h2
  set Bf := Matrix.toBilin' R with hBdef
  have hB : ∀ x y, Bf x y = x ⬝ᵥ (R *ᵥ y) := fun x y => Matrix.toBilin'_apply' _ x y
  have hsymm : LinearMap.IsSymm Bf := ⟨fun x y => by
    simp only [RingHom.id_apply, hB]
    rw [dotProduct_comm, ← vecMul_transpose, hR, dotProduct_mulVec]⟩
  obtain ⟨c0, hc0⟩ := LinearMap.BilinForm.exists_orthogonal_basis hsymm
  have hfin : Module.finrank K (Fin n → K) = n := Module.finrank_fin_fun K
  set c : Module.Basis (Fin n) K (Fin n → K) := c0.reindex (finCongr hfin) with hcdef
  have hcij : ∀ i j, i ≠ j → c i ⬝ᵥ (R *ᵥ c j) = 0 := by
    intro i j hij
    have h1 : (finCongr hfin).symm i ≠ (finCongr hfin).symm j := fun h =>
      hij ((finCongr hfin).symm.injective h)
    have h3 := hc0 h1
    change Bf (c0 ((finCongr hfin).symm i)) (c0 ((finCongr hfin).symm j)) = 0 at h3
    rw [hB] at h3
    simpa [hcdef, Module.Basis.reindex_apply] using h3
  set e := Pi.basisFun K (Fin n)
  set P : Matrix (Fin n) (Fin n) K := e.toMatrix c
  set Q : Matrix (Fin n) (Fin n) K := c.toMatrix e
  have hPQ : P * Q = 1 := Module.Basis.toMatrix_mul_toMatrix_flip e c
  have hQP : Q * P = 1 := Module.Basis.toMatrix_mul_toMatrix_flip c e
  refine ⟨⟨P, Q, hPQ, hQP⟩, fun i j hij => ?_⟩
  change (Pᵀ * R * P) i j = 0
  rw [Matrix.mul_apply, ← hcij i j hij, dotProduct]
  simp only [Matrix.mul_apply, transpose_apply, P, Module.Basis.toMatrix_apply, e,
      Pi.basisFun_repr, mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring


theorem exists_E16_isometry {m : ℕ} (hm : m = 5) (hK : ringChar K ≠ 2) (R : GL (Fin m) K)
    (hR : (R : Matrix (Fin m) (Fin m) K)ᵀ = R) :
    ∃ V : Subgroup (LinearFlag.projectiveSL m K),
      V ≤ (isometrySL (R : Matrix (Fin m) (Fin m) K)).map (LinearFlag.proj m K) ∧
        CFSG.IsElementaryAbelian 2 V ∧ Nat.card V = 16 := by
  subst hm
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  obtain ⟨B, hB⟩ := exists_orthogonal_congr hK (R : Matrix (Fin 5) (Fin 5) K) hR
  have hea : CFSG.IsElementaryAbelian 2 ↥(signGroup 5 K) := isEA_signGroup 5
  refine ⟨(signGroup 5 K).map (LinearFlag.conjAut 5 K B).toMonoidHom, ?_,
    CFSG.IsElementaryAbelian.map _, ?_⟩
  · rintro _ ⟨_, ⟨S, hS, rfl⟩, rfl⟩
    refine ⟨CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 5 K B
      (signSL S hS), ?_,
      (LinearFlag.conjAut_proj B _).symm⟩
    rw [SetLike.mem_coe, mem_isometrySL, LinearFlag.coe_slConjugation]
    set Bm : Matrix (Fin 5) (Fin 5) K := (B : Matrix (Fin 5) (Fin 5) K)
    set Bi : Matrix (Fin 5) (Fin 5) K := ((B⁻¹ : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)
    set M : Matrix (Fin 5) (Fin 5) K := Bmᵀ * (R : Matrix (Fin 5) (Fin 5) K) * Bm with hMdef
    have hBB : Bm * Bi = 1 := by
      simp only [Bm, Bi]; rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hM : ∀ i j, M i j ≠ 0 → (i ∈ S ↔ j ∈ S) := fun i j h => by
      have : i = j := by_contra fun hij => h (hB i j hij)
      rw [this]
    have hS' : ((signSL S hS : SpecialLinearGroup (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
        signDiag S := rfl
    rw [hS']
    calc (Bm * signDiag S * Bi)ᵀ * (R : Matrix (Fin 5) (Fin 5) K) * (Bm * signDiag S * Bi)
        = Biᵀ * ((signDiag S)ᵀ * M * signDiag S) * Bi := by
          simp only [hMdef, transpose_mul, Matrix.mul_assoc]
      _ = Biᵀ * M * Bi := by rw [signDiag_conj hM]
      _ = (Bm * Bi)ᵀ * (R : Matrix (Fin 5) (Fin 5) K) * (Bm * Bi) := by
          simp only [hMdef, transpose_mul, Matrix.mul_assoc]
      _ = R := by rw [hBB, transpose_one, Matrix.one_mul, Matrix.mul_one]
  · rw [Subgroup.card_map_of_injective (MulEquiv.injective _), card_signGroup rfl h2]

end CFSG.GH74.Generic.BProg.B2.GenLocL5Sign
