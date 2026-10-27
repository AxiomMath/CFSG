module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockSylowThreeAutWitCommon

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open CFSG.Open Matrix

open scoped commutatorElement

def plusWitS : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2) :=
  fromBlocks !![1, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0]
    !![0, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0]
    !![0, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0]
    !![1, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0]

def plusWitT : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2) :=
  fromBlocks !![0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0; 0, 1, 0, 1] 0
    !![1, 0, 0, 0; 0, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 0]
    !![0, 0, 1, 0; 0, 1, 0, 1; 1, 0, 0, 0; 0, 0, 0, 1]

theorem plusWitS_mul_self : plusWitS * plusWitS = 1 := by decide +kernel

theorem plusWitT_mul_self : plusWitT * plusWitT = 1 := by decide +kernel

theorem plusWitS_isometry (v : Fin 4 ⊕ Fin 4 → ZMod 2) :
    StatedQuadPlus 4 (ZMod 2) (plusWitS *ᵥ v) = StatedQuadPlus 4 (ZMod 2) v := by
  revert v
  decide +kernel

theorem plusWitT_isometry (v : Fin 4 ⊕ Fin 4 → ZMod 2) :
    StatedQuadPlus 4 (ZMod 2) (plusWitT *ᵥ v) = StatedQuadPlus 4 (ZMod 2) v := by
  revert v
  decide +kernel

theorem plusWit_comm_pow_nine : (plusWitS * plusWitT * plusWitS * plusWitT) ^ 9 = 1 := by
  decide +kernel

theorem plusWit_comm_pow_three : (plusWitS * plusWitT * plusWitS * plusWitT) ^ 3 ≠ 1 := by
  decide +kernel

def plusWitSUnit : GL (Fin 4 ⊕ Fin 4) (ZMod 2) :=
  ⟨plusWitS, plusWitS, plusWitS_mul_self, plusWitS_mul_self⟩

def plusWitTUnit : GL (Fin 4 ⊕ Fin 4) (ZMod 2) :=
  ⟨plusWitT, plusWitT, plusWitT_mul_self, plusWitT_mul_self⟩

theorem orderOf_plusWit_commutator : orderOf ⁅plusWitSUnit, plusWitTUnit⁆ = 9 := by
  have hval : ((⁅plusWitSUnit, plusWitTUnit⁆ : GL (Fin 4 ⊕ Fin 4) (ZMod 2)) :
      Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2)) =
      plusWitS * plusWitT * plusWitS * plusWitT := rfl
  have h := orderOf_eq_prime_pow (p := 3) (n := 1) (x := ⁅plusWitSUnit, plusWitTUnit⁆)
    (fun h3 => plusWit_comm_pow_three (by
      rw [pow_one] at h3
      rw [← hval, ← Units.val_pow_eq_pow_val, h3, Units.val_one]))
    (Units.ext (by rw [Units.val_pow_eq_pow_val, hval]; exact plusWit_comm_pow_nine))
  rw [h]
  norm_num

theorem statedQuadPlus_comp_ringHom {R S : Type} [Field R] [Field S] (f : R →+* S) (n : ℕ)
    (w : Fin n ⊕ Fin n → R) : StatedQuadPlus n S (f ∘ w) = f (StatedQuadPlus n R w) := by
  simp [StatedQuadPlus, map_sum, map_mul]

theorem statedQuadPlus_map_mulVec {R S : Type} [Field R] [Field S] {f : R →+* S}
    (hf : Function.Surjective f) {n : ℕ} {A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R}
    (hA : ∀ v, StatedQuadPlus n R (A *ᵥ v) = StatedQuadPlus n R v) (v : Fin n ⊕ Fin n → S) :
    StatedQuadPlus n S (A.map f *ᵥ v) = StatedQuadPlus n S v := by
  obtain ⟨w, rfl⟩ : ∃ w, f ∘ w = v := hf.comp_left v
  have h : A.map f *ᵥ (f ∘ w) = f ∘ (A *ᵥ w) :=
    funext fun i => (RingHom.map_mulVec f A w i).symm
  rw [h, statedQuadPlus_comp_ringHom, statedQuadPlus_comp_ringHom, hA]

def plusSplitEquiv (a b : ℕ) : Fin (a + b) ⊕ Fin (a + b) ≃ (Fin a ⊕ Fin a) ⊕ (Fin b ⊕ Fin b) :=
  (Equiv.sumCongr finSumFinEquiv.symm finSumFinEquiv.symm).trans (Equiv.sumSumSumComm _ _ _ _)

theorem statedQuadPlus_comp_plusSplitEquiv {K : Type} [Field K] (a b : ℕ)
    (w : (Fin a ⊕ Fin a) ⊕ (Fin b ⊕ Fin b) → K) :
    StatedQuadPlus (a + b) K (w ∘ plusSplitEquiv a b) =
      StatedQuadPlus a K (w ∘ Sum.inl) + StatedQuadPlus b K (w ∘ Sum.inr) := by
  simp [StatedQuadPlus, Fin.sum_univ_add, plusSplitEquiv]

def plusBlockExt (a b : ℕ) (K : Type) [Field K] :
    Matrix (Fin a ⊕ Fin a) (Fin a ⊕ Fin a) K →*
      Matrix (Fin (a + b) ⊕ Fin (a + b)) (Fin (a + b) ⊕ Fin (a + b)) K where
  toFun A := (fromBlocks A 0 0 1).submatrix (plusSplitEquiv a b) (plusSplitEquiv a b)
  map_one' := by simp only [fromBlocks_one, submatrix_one_equiv]
  map_mul' A B := by
    simp only [submatrix_mul_equiv, fromBlocks_multiply]
    simp

theorem plusBlockExt_injective (a b : ℕ) (K : Type) [Field K] :
    Function.Injective (plusBlockExt a b K) := by
  intro A B h
  ext i j
  have := congrFun (congrFun h ((plusSplitEquiv a b).symm (Sum.inl i)))
    ((plusSplitEquiv a b).symm (Sum.inl j))
  simpa [plusBlockExt] using this

theorem plusBlockExt_isometry {K : Type} [Field K] {a b : ℕ}
    {A : Matrix (Fin a ⊕ Fin a) (Fin a ⊕ Fin a) K}
    (hA : ∀ v, StatedQuadPlus a K (A *ᵥ v) = StatedQuadPlus a K v)
    (v : Fin (a + b) ⊕ Fin (a + b) → K) :
    StatedQuadPlus (a + b) K (plusBlockExt a b K A *ᵥ v) = StatedQuadPlus (a + b) K v := by
  obtain ⟨w, rfl⟩ : ∃ w, w ∘ plusSplitEquiv a b = v :=
    ⟨v ∘ (plusSplitEquiv a b).symm, by ext; simp⟩
  have h : plusBlockExt a b K A *ᵥ (w ∘ plusSplitEquiv a b) =
      Sum.elim (A *ᵥ (w ∘ Sum.inl)) (w ∘ Sum.inr) ∘ plusSplitEquiv a b := by
    simp [plusBlockExt, submatrix_mulVec_equiv, fromBlocks_mulVec, Function.comp_assoc]
  rw [h, statedQuadPlus_comp_plusSplitEquiv, statedQuadPlus_comp_plusSplitEquiv,
    Sum.elim_comp_inl, Sum.elim_comp_inr, hA]

theorem exists_mem_statedOmega_plus_orderOf_eq_nine {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) (m : ℕ) :
    ∃ g : StatedOmega (StatedQuadPlus (4 + m) K), orderOf g = 9 := by
  have : Fintype K := Fintype.ofFinite K
  have hK' : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card, hK]
  have : CharP K 2 := charP_of_card_eq_prime hK'
  have hf := ZMod.castHom_bijective K hK'
  let Φ : GL (Fin 4 ⊕ Fin 4) (ZMod 2) →* GL (Fin (4 + m) ⊕ Fin (4 + m)) K :=
    (Units.map (plusBlockExt 4 m K)).comp (GeneralLinearGroup.map (ZMod.castHom (dvd_refl 2) K))
  have hΦ : Function.Injective Φ :=
    (Units.map_injective (plusBlockExt_injective 4 m K)).comp
      (Units.map_injective (Matrix.map_injective hf.1))
  have hiso : ∀ x : GL (Fin 4 ⊕ Fin 4) (ZMod 2),
      (∀ v, StatedQuadPlus 4 (ZMod 2) (x.val *ᵥ v) = StatedQuadPlus 4 (ZMod 2) v) →
      Φ x ∈ Subgroup.closure {A : GL (Fin (4 + m) ⊕ Fin (4 + m)) K |
        ∀ v, StatedQuadPlus (4 + m) K (A.val *ᵥ v) = StatedQuadPlus (4 + m) K v} :=
    fun x hx => Subgroup.subset_closure fun v =>
      plusBlockExt_isometry (statedQuadPlus_map_mulVec hf.2 hx) v
  have hmem : Φ ⁅plusWitSUnit, plusWitTUnit⁆ ∈ StatedOmega (StatedQuadPlus (4 + m) K) := by
    rw [map_commutatorElement]
    exact Subgroup.commutator_mem_commutator (hiso _ plusWitS_isometry)
      (hiso _ plusWitT_isometry)
  exact ⟨⟨_, hmem⟩, by
    rw [Subgroup.orderOf_mk, orderOf_injective Φ hΦ, orderOf_plusWit_commutator]⟩

theorem exists_orderOf_eq_nine_pomegaPlus_two {X : Type} [Group X] {n : ℕ}
    (h : CFSG.Open.StatedClassicalModel X .POmegaPlus n 2 1) : ∃ x : X, orderOf x = 9 := by
  obtain ⟨⟨-, -, hn⟩, K, _, _, hcard, ⟨e⟩⟩ := h
  have hK : Nat.card K = 2 := by rw [hcard, pow_one]
  obtain ⟨m, rfl⟩ : ∃ m, n = 4 + m := ⟨n - 4, by omega⟩
  obtain ⟨g, hg⟩ := exists_mem_statedOmega_plus_orderOf_eq_nine hK m
  exact exists_orderOf_eq_of_equiv_statedProj hK e g hg

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
