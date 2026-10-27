module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockSylowThreeAutWitCommon

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open CFSG.Open
open scoped commutatorElement

namespace WitOrthMinus

open Matrix CFSG.MatrixModel

local notation "ι₆" => Fin 2 ⊕ Fin 2 ⊕ Fin 2

section Six

def sixIdx : ι₆ → Fin 6
  | .inl i => ⟨i, by omega⟩
  | .inr (.inl i) => ⟨i + 2, by omega⟩
  | .inr (.inr i) => ⟨i + 4, by omega⟩

def sSix : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![0, 1, 0, 0, 0, 0;
     1, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0;
     0, 0, 1, 0, 0, 0;
     0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 1, 0]

def tSix : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![1, 0, 1, 0, 1, 0;
     0, 0, 0, 1, 0, 0;
     0, 0, 1, 0, 0, 0;
     0, 1, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 0;
     0, 0, 1, 0, 0, 1]

def sMat : Matrix ι₆ ι₆ (ZMod 2) := sSix.submatrix sixIdx sixIdx

def tMat : Matrix ι₆ ι₆ (ZMod 2) := tSix.submatrix sixIdx sixIdx

theorem sMat_mul_self : sMat * sMat = 1 := by decide +kernel

theorem tMat_mul_self : tMat * tMat = 1 := by decide +kernel

theorem minusQuadCore_sMat_mulVec : ∀ w : ι₆ → ZMod 2,
    minusQuadCore 2 (ZMod 2) 1 1 (sMat *ᵥ w) = minusQuadCore 2 (ZMod 2) 1 1 w := by
  decide +kernel

theorem minusQuadCore_tMat_mulVec : ∀ w : ι₆ → ZMod 2,
    minusQuadCore 2 (ZMod 2) 1 1 (tMat *ᵥ w) = minusQuadCore 2 (ZMod 2) 1 1 w := by
  decide +kernel

theorem commMat_pow_nine : (sMat * tMat * sMat * tMat) ^ 9 = 1 := by decide +kernel

theorem commMat_pow_three : (sMat * tMat * sMat * tMat) ^ 3 ≠ 1 := by decide +kernel

def sGL : GL ι₆ (ZMod 2) := ⟨sMat, sMat, sMat_mul_self, sMat_mul_self⟩

def tGL : GL ι₆ (ZMod 2) := ⟨tMat, tMat, tMat_mul_self, tMat_mul_self⟩

theorem orderOf_commutator_sGL_tGL : orderOf ⁅sGL, tGL⁆ = 9 := by
  have hval : ((⁅sGL, tGL⁆ : GL ι₆ (ZMod 2)) : Matrix ι₆ ι₆ (ZMod 2)) =
      sMat * tMat * sMat * tMat := by
    rw [commutatorElement_def]
    rfl
  have h3 : ¬⁅sGL, tGL⁆ ^ 3 ^ 1 = 1 := by
    intro h
    apply commMat_pow_three
    have := congrArg Units.val h
    rwa [pow_one, Units.val_pow_eq_pow_val, hval, Units.val_one] at this
  have h9 : ⁅sGL, tGL⁆ ^ 3 ^ (1 + 1) = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hval, Units.val_one]
    exact commMat_pow_nine
  simpa using orderOf_eq_prime_pow h3 h9

end Six

section Block

variable {K : Type} [Field K] {α β ι : Type} [Fintype α] [DecidableEq α] [Fintype β]
  [DecidableEq β] [Fintype ι] [DecidableEq ι]

def blockExt (e : ι ≃ α ⊕ β) : Matrix α α K →* Matrix ι ι K where
  toFun A := (fromBlocks A 0 0 1).submatrix e e
  map_one' := by rw [fromBlocks_one, submatrix_one_equiv]
  map_mul' A B := by
    rw [submatrix_mul_equiv, fromBlocks_multiply]
    simp

theorem blockExt_units_injective (e : ι ≃ α ⊕ β) :
    Function.Injective (Units.map (blockExt (K := K) e)) := by
  refine Units.map_injective fun A B h => ?_
  have h1 := congrArg (fun M : Matrix ι ι K => M.submatrix e.symm e.symm) h
  simp only [blockExt, MonoidHom.coe_mk, OneHom.coe_mk, submatrix_submatrix,
    Equiv.self_comp_symm, submatrix_id_id] at h1
  exact (fromBlocks_inj.1 h1).1

theorem blockExt_isometry (e : ι ≃ α ⊕ β) {Q : (ι → K) → K} {Q₁ : (α → K) → K}
    {Q₂ : (β → K) → K}
    (hQ : ∀ v, Q v = Q₁ (fun a => v (e.symm (.inl a))) + Q₂ (fun b => v (e.symm (.inr b))))
    {A : Matrix α α K} (hA : ∀ w, Q₁ (A *ᵥ w) = Q₁ w) (v : ι → K) :
    Q (blockExt e A *ᵥ v) = Q v := by
  have h1 : (fun a => (blockExt e A *ᵥ v) (e.symm (.inl a))) =
      A *ᵥ (fun a => v (e.symm (.inl a))) := by
    ext a
    simp [blockExt, submatrix_mulVec_equiv, fromBlocks_mulVec, Function.comp_def]
  have h2 : (fun b => (blockExt e A *ᵥ v) (e.symm (.inr b))) = fun b => v (e.symm (.inr b)) := by
    ext b
    simp [blockExt, submatrix_mulVec_equiv, fromBlocks_mulVec, Function.comp_def]
  rw [hQ, hQ v, h1, h2, hA]

end Block

section Split

variable {K : Type} [Field K]

@[expose] def finSplit (m : ℕ) (hm : 2 ≤ m) : Fin m ≃ Fin 2 ⊕ Fin (m - 2) :=
  (finCongr (by omega)).trans finSumFinEquiv.symm

@[expose] def regroup (A B C : Type) : (A ⊕ B) ⊕ (A ⊕ B) ⊕ C ≃ (A ⊕ A ⊕ C) ⊕ (B ⊕ B) where
  toFun
    | .inl (.inl a) => .inl (.inl a)
    | .inl (.inr b) => .inr (.inl b)
    | .inr (.inl (.inl a)) => .inl (.inr (.inl a))
    | .inr (.inl (.inr b)) => .inr (.inr b)
    | .inr (.inr c) => .inl (.inr (.inr c))
  invFun
    | .inl (.inl a) => .inl (.inl a)
    | .inl (.inr (.inl a)) => .inr (.inl (.inl a))
    | .inl (.inr (.inr c)) => .inr (.inr c)
    | .inr (.inl b) => .inl (.inr b)
    | .inr (.inr b) => .inr (.inl (.inr b))
  left_inv := by rintro ((a | b) | (a | b) | c) <;> rfl
  right_inv := by rintro ((a | a | c) | (b | b)) <;> rfl

@[expose] def coordSplit (m : ℕ) (hm : 2 ≤ m) :
    Fin m ⊕ Fin m ⊕ Fin 2 ≃ (Fin 2 ⊕ Fin 2 ⊕ Fin 2) ⊕ (Fin (m - 2) ⊕ Fin (m - 2)) :=
  (Equiv.sumCongr (finSplit m hm) (Equiv.sumCongr (finSplit m hm) (Equiv.refl (Fin 2)))).trans
    (regroup _ _ _)

theorem coordSplit_symm_inl_inl (m : ℕ) (hm : 2 ≤ m) (a : Fin 2) :
    (coordSplit m hm).symm (.inl (.inl a)) = .inl ((finSplit m hm).symm (.inl a)) :=
  rfl

theorem coordSplit_symm_inl_inr_inl (m : ℕ) (hm : 2 ≤ m) (a : Fin 2) :
    (coordSplit m hm).symm (.inl (.inr (.inl a))) = .inr (.inl ((finSplit m hm).symm (.inl a))) :=
  rfl

theorem coordSplit_symm_inl_inr_inr (m : ℕ) (hm : 2 ≤ m) (a : Fin 2) :
    (coordSplit m hm).symm (.inl (.inr (.inr a))) = .inr (.inr a) :=
  rfl

theorem coordSplit_symm_inr_inl (m : ℕ) (hm : 2 ≤ m) (j : Fin (m - 2)) :
    (coordSplit m hm).symm (.inr (.inl j)) = .inl ((finSplit m hm).symm (.inr j)) :=
  rfl

theorem coordSplit_symm_inr_inr (m : ℕ) (hm : 2 ≤ m) (j : Fin (m - 2)) :
    (coordSplit m hm).symm (.inr (.inr j)) = .inr (.inl ((finSplit m hm).symm (.inr j))) :=
  rfl

theorem minusQuadCore_eq_add (m : ℕ) (hm : 2 ≤ m) (b c : K) (v : Fin m ⊕ Fin m ⊕ Fin 2 → K) :
    minusQuadCore m K b c v =
      minusQuadCore 2 K b c (fun a => v ((coordSplit m hm).symm (.inl a))) +
        plusQuadCore (m - 2) K (fun j => v ((coordSplit m hm).symm (.inr j))) := by
  simp only [minusQuadCore, plusQuadCore, coordSplit_symm_inl_inl, coordSplit_symm_inl_inr_inl,
    coordSplit_symm_inl_inr_inr, coordSplit_symm_inr_inl, coordSplit_symm_inr_inr]
  rw [← Equiv.sum_comp (finSplit m hm).symm (fun i => v (.inl i) * v (.inr (.inl i))),
    Fintype.sum_sum_type]
  ring

end Split

section Field

variable {K : Type} [Field K]

theorem minusQuadCore_comp (φ : ZMod 2 →+* K) (w : ι₆ → ZMod 2) :
    minusQuadCore 2 K 1 1 (fun i => φ (w i)) = φ (minusQuadCore 2 (ZMod 2) 1 1 w) := by
  simp only [minusQuadCore, map_add, map_mul, map_pow, map_sum, map_one]

theorem minusQuadCore_map_mulVec (φ : ZMod 2 →+* K) (hφ : Function.Surjective φ)
    (A : Matrix ι₆ ι₆ (ZMod 2))
    (hA : ∀ w, minusQuadCore 2 (ZMod 2) 1 1 (A *ᵥ w) = minusQuadCore 2 (ZMod 2) 1 1 w)
    (v : ι₆ → K) : minusQuadCore 2 K 1 1 (A.map φ *ᵥ v) = minusQuadCore 2 K 1 1 v := by
  obtain ⟨w, rfl⟩ : ∃ w : ι₆ → ZMod 2, (fun i => φ (w i)) = v :=
    ⟨fun i => Function.surjInv hφ (v i), funext fun i => Function.surjInv_eq hφ (v i)⟩
  have h : A.map φ *ᵥ (fun i => φ (w i)) = fun i => φ ((A *ᵥ w) i) :=
    funext fun i => (RingHom.map_mulVec φ A w i).symm
  rw [h, minusQuadCore_comp, minusQuadCore_comp, hA]

end Field

section Main

variable {K : Type} [Field K] [Finite K]

theorem exists_mem_omega_orderOf_eq_nine (hK : Nat.card K = 2) {m : ℕ} (hm : 2 ≤ m) :
    ∃ g ∈ ⁅isometryCore (minusQuadCore m K 1 1), isometryCore (minusQuadCore m K 1 1)⁆,
      orderOf g = 9 := by
  have : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card, hK]
  have : CharP K 2 := charP_of_card_eq_prime hcard
  let φ : ZMod 2 →+* K := ZMod.castHom (dvd_refl 2) K
  have hφ : Function.Bijective φ := ZMod.castHom_bijective K hcard
  let Φ : GL ι₆ (ZMod 2) →* GL (Fin m ⊕ Fin m ⊕ Fin 2) K :=
    (Units.map (blockExt (coordSplit m hm))).comp (Matrix.GeneralLinearGroup.map φ)
  have hΦ : Function.Injective Φ :=
    (blockExt_units_injective _).comp
      (Units.map_injective fun _ _ h => Matrix.map_injective hφ.1 h)
  have hiso : ∀ A : GL ι₆ (ZMod 2), (∀ w, minusQuadCore 2 (ZMod 2) 1 1
      ((A : Matrix ι₆ ι₆ (ZMod 2)) *ᵥ w) = minusQuadCore 2 (ZMod 2) 1 1 w) →
      Φ A ∈ isometryCore (minusQuadCore m K 1 1) := fun A hA =>
    Subgroup.subset_closure fun v =>
      blockExt_isometry (coordSplit m hm) (minusQuadCore_eq_add m hm 1 1)
        (minusQuadCore_map_mulVec φ hφ.2 _ hA) v
  refine ⟨Φ ⁅sGL, tGL⁆, ?_, ?_⟩
  · rw [map_commutatorElement]
    exact Subgroup.commutator_mem_commutator (hiso _ minusQuadCore_sMat_mulVec)
      (hiso _ minusQuadCore_tMat_mulVec)
  · rw [orderOf_injective Φ hΦ, orderOf_commutator_sGL_tGL]

end Main

end WitOrthMinus

theorem exists_orderOf_eq_nine_pomegaMinus_two {X : Type} [Group X] {n : ℕ}
    (h : CFSG.Open.StatedClassicalModel X .POmegaMinus n 2 1) : ∃ x : X, orderOf x = 9 := by
  obtain ⟨⟨-, -, hn⟩, K, hKfield, hKfin, hcard, b, c, hirr, ⟨e⟩⟩ := h
  have hn' : 4 ≤ n := hn
  have hK : Nat.card K = 2 := by simpa using hcard
  have : Fintype K := Fintype.ofFinite K
  have hcardF : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card, hK]
  have : CharP K 2 := charP_of_card_eq_prime hcardF
  have h01 : ∀ x : K, x = 0 ∨ x = 1 := by
    intro x
    obtain ⟨y, rfl⟩ := (ZMod.castHom_bijective K hcardF).2 x
    have hy : ∀ y : ZMod 2, y = 0 ∨ y = 1 := by decide
    rcases hy y with rfl | rfl <;> simp
  have hc : c = 1 := (h01 c).resolve_left fun hc => hirr 0 (by simp [hc])
  have hb : b = 1 := (h01 b).resolve_left fun hb => hirr 1 (by
    rw [hb, hc]
    simpa using CharTwo.add_self_eq_zero (1 : K))
  subst hb hc
  obtain ⟨g, hg, hord⟩ := WitOrthMinus.exists_mem_omega_orderOf_eq_nine (K := K) hK
    (m := n - 1) (by omega)
  have hg' : g ∈ StatedOmega (StatedQuadMinus n K 1 1) := hg
  exact exists_orderOf_eq_of_equiv_statedProj hK e ⟨g, hg'⟩ (by rw [Subgroup.orderOf_mk, hord])

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
