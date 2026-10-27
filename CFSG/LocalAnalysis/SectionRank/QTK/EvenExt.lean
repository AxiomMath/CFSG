module

public import CFSG.LocalAnalysis.SectionRank.QTK.EvenPlus8
public import CFSG.RankThree.PartOne.S11c.BlockExt
public import CFSG.RankThree.PartOne.KF.ClsOmega

public section

namespace CFSG.SectionRank.QTK

open Matrix CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.HNRed
open CFSG.Assembly.RankThreeEven (localRank)
open scoped commutatorElement

variable (K : Type) [Field K]

theorem isometry_of_mem_statedOmega {ι : Type} [Fintype ι] [DecidableEq ι] {Q : (ι → K) → K}
    {A : GL ι K} (hA : A ∈ StatedOmega Q) (v : ι → K) : Q ((A : Matrix ι ι K) *ᵥ v) = Q v := by
  let O : Subgroup (GL ι K) :=
    { carrier := {A | ∀ v, Q ((A : Matrix ι ι K) *ᵥ v) = Q v}
      mul_mem' := fun {a b} ha hb v => by
        change Q (((a * b : GL ι K) : Matrix ι ι K) *ᵥ v) = Q v
        rw [Units.val_mul, ← Matrix.mulVec_mulVec]
        exact (ha _).trans (hb v)
      one_mem' := fun v => by
        change Q (((1 : GL ι K) : Matrix ι ι K) *ᵥ v) = Q v
        rw [Units.val_one, Matrix.one_mulVec]
      inv_mem' := fun {a} ha v => by
        have h := ha ((a⁻¹ : GL ι K) *ᵥ v)
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
          Matrix.one_mulVec] at h
        exact h.symm }
  have hC : Subgroup.closure {A : GL ι K | ∀ v, Q ((A : Matrix ι ι K) *ᵥ v) = Q v} ≤ O :=
    (Subgroup.closure_le O).2 fun _ h => h
  have hOO : ⁅O, O⁆ ≤ O := Subgroup.commutator_le.2 fun a ha b hb => by
    rw [commutatorElement_def]
    exact O.mul_mem (O.mul_mem (O.mul_mem ha hb) (O.inv_mem ha)) (O.inv_mem hb)
  exact hOO (Subgroup.commutator_mono hC hC hA) v

variable {K} [CharP K 2]

theorem statedScalars_subgroupOf_statedOmega_eq_bot {ι : Type} [Fintype ι] [DecidableEq ι]
    (Q : QuadraticForm K (ι → K)) {Q₀ : (ι → K) → K} (hQ : ⇑Q = Q₀) {v₀ : ι → K}
    (hv₀ : Q v₀ ≠ 0) : (StatedScalars ι K).subgroupOf (StatedOmega Q₀) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 hx
  have hiso := isometry_of_mem_statedOmega K x.2 v₀
  have hmul : ((x : GL ι K) : Matrix ι ι K) *ᵥ v₀ = (c : K) • v₀ := by
    ext i
    rw [← hc, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.mulVec_diagonal,
      Pi.smul_apply, smul_eq_mul]
  rw [hmul, ← hQ, QuadraticMap.map_smul, smul_eq_mul] at hiso
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have h1 : ((c : K) * c - 1) * Q v₀ = 0 := by linear_combination hiso
  have h3 : ((c : K) - 1) ^ 2 = 0 := by
    linear_combination (mul_eq_zero.1 h1).resolve_right hv₀ + (1 - (c : K)) * h2
  have hc1 : c = 1 := Units.ext (sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h3))
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [Subgroup.coe_one, ← hc, hc1, map_one]

omit [CharP K 2] in
theorem blockExt_isometry {κ ι : Type} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    (e : κ ↪ ι) {Q : (ι → K) → K} {Q' : (κ → K) → K} {R : (ι → K) → K}
    (hQ : ∀ v, Q v = Q' (v ∘ e) + R v)
    (hR : ∀ v w : ι → K, (∀ a, (∀ s, e s ≠ a) → v a = w a) → R v = R w)
    {M : Matrix κ κ K} (hM : ∀ u, Q' (M *ᵥ u) = Q' u) (v : ι → K) :
    Q (blockExt e M *ᵥ v) = Q v := by
  have hT : (incl K e)ᵀ *ᵥ v = v ∘ e := funext fun s => inclT_mulVec e v s
  have h1 : (blockExt e M *ᵥ v) ∘ e = M *ᵥ (v ∘ e) := by
    funext s
    rw [Function.comp_apply, blockExt_mulVec, Pi.add_apply, incl_mulVec_emb, hT,
      Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, Function.comp_apply]
    abel
  have h2 : ∀ a, (∀ s, e s ≠ a) → (blockExt e M *ᵥ v) a = v a := fun a ha => by
    rw [blockExt_mulVec, Pi.add_apply, incl_mulVec_of_ne e _ a ha, add_zero]
  rw [hQ, hQ, h1, hM, hR _ _ h2]

@[expose] def plusEmb (m : ℕ) : Fin 4 ⊕ Fin 4 ↪ Fin (4 + m) ⊕ Fin (4 + m) :=
  Function.Embedding.sumMap (Fin.castAddEmb m) (Fin.castAddEmb m)

@[expose] def plusRest (m : ℕ) (v : Fin (4 + m) ⊕ Fin (4 + m) → K) : K :=
  ∑ j : Fin m, v (.inl (Fin.natAdd 4 j)) * v (.inr (Fin.natAdd 4 j))

omit [CharP K 2] in
theorem statedQuadPlus_split (m : ℕ) (v : Fin (4 + m) ⊕ Fin (4 + m) → K) :
    StatedQuadPlus (4 + m) K v = StatedQuadPlus 4 K (v ∘ plusEmb m) + plusRest m v := by
  rw [StatedQuadPlus, Fin.sum_univ_add]
  rfl

theorem plusEmb_ne (m : ℕ) (s : Fin 4 ⊕ Fin 4) (j : Fin m) :
    plusEmb m s ≠ .inl (Fin.natAdd 4 j) ∧ plusEmb m s ≠ .inr (Fin.natAdd 4 j) := by
  rcases s with i | i <;> simp [plusEmb, Fin.ext_iff] <;> omega

omit [CharP K 2] in
theorem plusRest_congr (m : ℕ) (v w : Fin (4 + m) ⊕ Fin (4 + m) → K)
    (h : ∀ a, (∀ s, plusEmb m s ≠ a) → v a = w a) : plusRest m v = plusRest m w :=
  Finset.sum_congr rfl fun j _ => by
    rw [h _ fun s => (plusEmb_ne m s j).1, h _ fun s => (plusEmb_ne m s j).2]

@[expose] def minusEmb (m : ℕ) : Fin 4 ⊕ Fin 4 ↪ Fin (4 + m) ⊕ Fin (4 + m) ⊕ Fin 2 :=
  (plusEmb m).trans (Function.Embedding.sumMap (Function.Embedding.refl _)
    Function.Embedding.inl)

@[expose] def minusRest (m : ℕ) (b c : K) (v : Fin (4 + m) ⊕ Fin (4 + m) ⊕ Fin 2 → K) : K :=
  ∑ j : Fin m, v (.inl (Fin.natAdd 4 j)) * v (.inr (.inl (Fin.natAdd 4 j))) +
    (v (.inr (.inr 0)) ^ 2 + b * v (.inr (.inr 0)) * v (.inr (.inr 1)) +
      c * v (.inr (.inr 1)) ^ 2)

omit [CharP K 2] in
theorem statedQuadMinus_split (m : ℕ) (b c : K) (v : Fin (4 + m) ⊕ Fin (4 + m) ⊕ Fin 2 → K) :
    StatedQuadMinus (4 + m + 1) K b c v =
      StatedQuadPlus 4 K (v ∘ minusEmb m) + minusRest m b c v := by
  change (∑ i : Fin (4 + m), v (.inl i) * v (.inr (.inl i))) + v (.inr (.inr 0)) ^ 2 +
    b * v (.inr (.inr 0)) * v (.inr (.inr 1)) + c * v (.inr (.inr 1)) ^ 2 = _
  rw [Fin.sum_univ_add, minusRest]
  change _ = (∑ i : Fin 4, v (.inl (Fin.castAdd m i)) * v (.inr (.inl (Fin.castAdd m i)))) + _
  ring

theorem minusEmb_ne (m : ℕ) (s : Fin 4 ⊕ Fin 4) :
    (∀ j : Fin m, minusEmb m s ≠ .inl (Fin.natAdd 4 j) ∧
      minusEmb m s ≠ .inr (.inl (Fin.natAdd 4 j))) ∧ ∀ k : Fin 2, minusEmb m s ≠ .inr (.inr k) := by
  rcases s with i | i <;> simp [minusEmb, plusEmb, Fin.ext_iff] <;> omega

omit [CharP K 2] in
theorem minusRest_congr (m : ℕ) (b c : K) (v w : Fin (4 + m) ⊕ Fin (4 + m) ⊕ Fin 2 → K)
    (h : ∀ a, (∀ s, minusEmb m s ≠ a) → v a = w a) : minusRest m b c v = minusRest m b c w := by
  have hu : ∀ k : Fin 2, v (.inr (.inr k)) = w (.inr (.inr k)) := fun k =>
    h _ fun s => (minusEmb_ne m s).2 k
  rw [minusRest, minusRest, hu 0, hu 1]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by
    rw [h _ fun s => ((minusEmb_ne m s).1 j).1, h _ fun s => ((minusEmb_ne m s).1 j).2]

variable (K) [Finite K]

theorem three_le_localRank_statedOmegaPlus (m : ℕ) :
    3 ≤ localRank 3 ↥(StatedOmega (StatedQuadPlus (4 + m) K)) :=
  three_le_localRank_statedOmega_of_plusHom K (blockGL (plusEmb m)) (blockGL_injective _)
    fun _ hg v => blockExt_isometry (plusEmb m) (statedQuadPlus_split m) (plusRest_congr m) hg v

theorem three_le_localRank_statedOmegaMinus (m : ℕ) (b c : K) :
    3 ≤ localRank 3 ↥(StatedOmega (StatedQuadMinus (4 + m + 1) K b c)) :=
  three_le_localRank_statedOmega_of_plusHom K (blockGL (minusEmb m)) (blockGL_injective _)
    fun _ hg v => blockExt_isometry (minusEmb m) (statedQuadMinus_split m b c)
      (minusRest_congr m b c) hg v

theorem three_le_localRank_statedProj_statedOmegaPlus {n : ℕ} (hn : 4 ≤ n) :
    3 ≤ localRank 3 (StatedProj (StatedOmega (StatedQuadPlus n K))) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 4 + m := ⟨n - 4, by omega⟩
  rw [← CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv
    (CFSG.RankThree.PartOne.KFU.equivProjOfScalarsBot _
      (CFSG.RankThree.PartOne.KFU.statedScalars_subgroupOf_statedOmega_quadPlus_eq_bot (K := K)
        (n := 4 + m) (by omega))) Nat.prime_three]
  exact three_le_localRank_statedOmegaPlus K m

theorem three_le_localRank_statedProj_statedOmegaMinus {n : ℕ} (hn : 5 ≤ n) (b c : K) :
    3 ≤ localRank 3 (StatedProj (StatedOmega (StatedQuadMinus n K b c))) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 4 + m + 1 := ⟨n - 5, by omega⟩
  have hv : CFSG.LieType.Universal.Spin.quadMinus (4 + m + 1) K b c
      (Pi.single (.inr (.inr 0)) 1) ≠ 0 := by
    rw [CFSG.LieType.Universal.Spin.coe_quadMinus]
    simp [StatedQuadMinus]
  rw [← CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv
    (CFSG.RankThree.PartOne.KFU.equivProjOfScalarsBot _
      (statedScalars_subgroupOf_statedOmega_eq_bot _
        (CFSG.LieType.Universal.Spin.coe_quadMinus (4 + m + 1) K b c) hv)) Nat.prime_three]
  exact three_le_localRank_statedOmegaMinus K m b c

end CFSG.SectionRank.QTK
