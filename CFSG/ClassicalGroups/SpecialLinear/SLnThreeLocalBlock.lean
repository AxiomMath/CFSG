module

public import CFSG.ClassicalGroups.SpecialLinear.SLnThreeLocalDefs
public import CFSG.Open.LocalVocabulary
import CFSG.GroupTheory.PGroup.RankTwoCommute

public section

namespace CFSG.ClassicalGroups.SLnThreeLocal

open Matrix CFSG.Open

variable {K : Type} [Field K] {n : ℕ}

@[expose] def blockEmb (hn : n = 6 ∨ n = 7) (j : Fin 3) :
    Matrix.SpecialLinearGroup (Fin 2) K →* StatedSL n K :=
  (((blkGL hn).comp (MonoidHom.mulSingle (fun _ : Fin 3 => GL (Fin 2) K) j)).comp
      Matrix.SpecialLinearGroup.toGL).codRestrict (StatedSL n K) fun T => by
    apply blkGL_mem_statedSL
    refine Finset.prod_eq_one fun i _ => ?_
    by_cases hij : i = j
    · subst hij
      simp
    · simp [Pi.mulSingle_eq_of_ne hij]

theorem coe_blockEmb (hn : n = 6 ∨ n = 7) (j : Fin 3) (T : Matrix.SpecialLinearGroup (Fin 2) K) :
    ((blockEmb hn j T : StatedSL n K) : GL (Fin n) K) =
      blkGL hn (Pi.mulSingle j (Matrix.SpecialLinearGroup.toGL T)) := rfl

theorem blockEmb_injective (hn : n = 6 ∨ n = 7) (j : Fin 3) :
    Function.Injective (blockEmb (K := K) hn j) := by
  intro T T' h
  have h1 := congrArg (fun g : StatedSL n K => (g : GL (Fin n) K)) h
  simp only [coe_blockEmb] at h1
  exact Matrix.SpecialLinearGroup.toGL_injective (Pi.mulSingle_injective j (blkGL_injective hn h1))

theorem orderOf_blockEmb (hn : n = 6 ∨ n = 7) (j : Fin 3)
    (T : Matrix.SpecialLinearGroup (Fin 2) K) : orderOf (blockEmb hn j T) = orderOf T := by
  have h := orderOf_injective (blockEmb (K := K) hn j) (blockEmb_injective hn j) T
  rw [h]

theorem commute_blockEmb_c₀ (hn : n = 6 ∨ n = 7) (j : Fin 3)
    (T : Matrix.SpecialLinearGroup (Fin 2) K) (v : Multiplicative (Fin 3 → ZMod 3))
    (h : Commute (Matrix.SpecialLinearGroup.toGL T) (blockPowGL K (Multiplicative.toAdd v j))) :
    Commute (blockEmb hn j T) (c₀ K hn v) := by
  apply Subtype.ext
  show blkGL hn _ * blkGL hn _ = blkGL hn _ * blkGL hn _
  simp only [← map_mul]
  congr 1
  funext i
  by_cases hij : i = j
  · subst hij
    simpa using h.eq
  · simp [Pi.mulSingle_eq_of_ne hij]

theorem commute_blockEmb_blockEmb (hn : n = 6 ∨ n = 7) {j j' : Fin 3} (hjj : j ≠ j')
    (T T' : Matrix.SpecialLinearGroup (Fin 2) K) :
    Commute (blockEmb hn j T) (blockEmb hn j' T') := by
  apply Subtype.ext
  show blkGL hn _ * blkGL hn _ = blkGL hn _ * blkGL hn _
  simp only [← map_mul]
  congr 1
  exact (Pi.mulSingle_commute hjj _ _).eq

@[expose] def vecStab (n : ℕ) (K : Type) [Field K] (w : Fin n → K) :
    Subgroup (StatedSL n K) where
  carrier := {g | ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w = w}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Subgroup.coe_mul, Units.val_mul, ← Matrix.mulVec_mulVec] at *
    rw [hb, ha]
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    have h1 : (((a : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
        (((a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w) = w := by
      rw [Matrix.mulVec_mulVec]
      simp
    rw [ha] at h1
    simpa using h1

theorem notMem_zpowers_of_mulVec {x y : StatedSL n K} {w : Fin n → K}
    (hx : ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w = w)
    (hy : ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w ≠ w) :
    y ∉ Subgroup.zpowers x := fun hmem =>
  hy ((Subgroup.zpowers_le.mpr (show x ∈ vecStab n K w from hx)) hmem)

@[expose] def vecOfBlk (hn : n = 6 ∨ n = 7) (x : Blk → K) : Fin n → K :=
  fun a => Sum.elim x 0 (blkEquiv hn a)

theorem blkVec_vecOfBlk (hn : n = 6 ∨ n = 7) (x : Blk → K) : blkVec hn (vecOfBlk hn x) = x := by
  funext b
  simp [blkVec, vecOfBlk]

theorem embMat_mulVec_vecOfBlk (hn : n = 6 ∨ n = 7) (X : Matrix Blk Blk K) (x : Blk → K) :
    embMat hn X *ᵥ vecOfBlk hn x = vecOfBlk hn x ↔ X *ᵥ x = x := by
  rw [embMat_mulVec_eq_self_iff, blkVec_vecOfBlk]

theorem blkGL_mulVec_vecOfBlk_iff (hn : n = 6 ∨ n = 7) (M : Fin 3 → GL (Fin 2) K)
    (x : Blk → K) :
    ((blkGL hn M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ vecOfBlk hn x =
        vecOfBlk hn x ↔
      ∀ i, ((M i : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ (fun q => x (q, i)) =
        fun q => x (q, i) := by
  rw [coe_blkGL, embMat_mulVec_vecOfBlk, blockDiagonal_mulVec_eq_self_iff]

theorem blockEmb_mulVec_vecOfBlk_of_ne (hn : n = 6 ∨ n = 7) {j i : Fin 3} (hij : i ≠ j)
    (T : Matrix.SpecialLinearGroup (Fin 2) K) (p : Fin 2) :
    ((blockEmb hn j T : StatedSL n K) : GL (Fin n) K).val *ᵥ
      vecOfBlk hn (Pi.single (p, i) 1) = vecOfBlk hn (Pi.single (p, i) 1) := by
  rw [coe_blockEmb, blkGL_mulVec_vecOfBlk_iff]
  intro k
  by_cases hk : k = j
  · subst hk
    have : (fun q => (Pi.single (p, i) (1 : K) : Blk → K) (q, k)) = 0 := by
      funext q
      simp [Pi.single_apply, hij.symm]
    simp [this]
  · simp [Pi.mulSingle_eq_of_ne hk]

theorem blockEmb_mulVec_vecOfBlk_ne_of (hn : n = 6 ∨ n = 7) (j : Fin 3)
    (T : Matrix.SpecialLinearGroup (Fin 2) K) (q : Fin 2)
    (hq : (T : Matrix (Fin 2) (Fin 2) K) *ᵥ Pi.single q 1 ≠ Pi.single q 1) :
    ((blockEmb hn j T : StatedSL n K) : GL (Fin n) K).val *ᵥ
      vecOfBlk hn (Pi.single (q, j) 1) ≠ vecOfBlk hn (Pi.single (q, j) 1) := by
  rw [coe_blockEmb, Ne, blkGL_mulVec_vecOfBlk_iff]
  intro h
  apply hq
  have h1 := h j
  have h2 : (fun q' => (Pi.single (q, j) (1 : K) : Blk → K) (q', j)) = Pi.single q 1 := by
    funext q'
    simp [Pi.single_apply]
  rw [h2] at h1
  simpa using h1

theorem one_le_pRank_of_orderOf {G : Type*} [Group G] [Finite G] {r : ℕ} [Fact r.Prime]
    {H : Subgroup G} {x : G} (hx : x ∈ H) (hxo : orderOf x = r) : 1 ≤ pRank r H := by
  have hcard : Nat.card (Subgroup.zpowers x) = r := by rw [Nat.card_zpowers, hxo]
  exact CFSG.SectionRank.le_pRank (Fact.out : r.Prime).one_lt (Subgroup.zpowers_le.mpr hx)
    (CFSG.GroupTheory.isElemAbelian_of_card_prime hcard) (by simpa using hcard)

theorem two_le_pRank_of_mulVec [Finite K] {r : ℕ} [Fact r.Prime] {H : Subgroup (StatedSL n K)}
    {x y : StatedSL n K} (hx : x ∈ H) (hy : y ∈ H) (hxo : orderOf x = r) (hyo : orderOf y = r)
    (hxy : Commute x y) {w : Fin n → K}
    (hxw : ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w = w)
    (hyw : ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w ≠ w) : 2 ≤ pRank r H :=
  CFSG.GroupTheory.two_le_pRank_of_commute hx hy hxo hyo hxy (notMem_zpowers_of_mulVec hxw hyw)

end CFSG.ClassicalGroups.SLnThreeLocal
