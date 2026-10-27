module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I2016U6Flag
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieU6Big
public import CFSG.LieType.BorelTits.HeldFlagL
import all CFSG.Fischer.F4
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1431YU5Core
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.RankThree.PartTwo.Sec4.Census.Witness46

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.I2016U6

open Matrix CFSG.Open CFSG.Fischer CFSG.LieType.BorelTits CFSG.AGLEmbedding
  CFSG.LocalAnalysis.GLTheoremA.LevelLieU6 CFSG.LocalAnalysis.GLTheoremA.CatB.U52Layer
open scoped commutatorElement

private theorem proj_poly :
    ∀ x e : F4, x ≠ 0 → e ≠ 0 → e * x ^ 2 + e ^ 2 * x + 1 = if x = e then 1 else 0 := by
  decide

theorem F4_card_four : Nat.card F4 = 4 := by
  rw [Nat.card_eq_fintype_card, F4.card]

theorem coord_eq_zero_of_single {d : Fin 6 → F4} {D : GL (Fin 6) F4}
    (hD : (D : Matrix (Fin 6) (Fin 6) F4) = Matrix.diagonal d) (hd0 : ∀ i, d i ≠ 0)
    {W : Submodule F4 (Fin 6 → F4)} (hWiso : IsTotallyIsotropicSU 2 W)
    (hWD : ∀ w ∈ W, (D : Matrix (Fin 6) (Fin 6) F4) *ᵥ w ∈ W)
    {i : Fin 6} (hsing : ∀ j, d j = d i → j = i) {w : Fin 6 → F4} (hw : w ∈ W) : w i = 0 := by
  set e := d i with he
  have hu : e • ((D : Matrix (Fin 6) (Fin 6) F4) *ᵥ ((D : Matrix (Fin 6) (Fin 6) F4) *ᵥ w)) +
      e ^ 2 • ((D : Matrix (Fin 6) (Fin 6) F4) *ᵥ w) + w ∈ W :=
    add_mem (add_mem (W.smul_mem e (hWD _ (hWD _ hw))) (W.smul_mem _ (hWD _ hw))) hw
  have hcoord : ∀ j, (e • ((D : Matrix (Fin 6) (Fin 6) F4) *ᵥ ((D : Matrix (Fin 6) (Fin 6) F4) *ᵥ w)) +
      e ^ 2 • ((D : Matrix (Fin 6) (Fin 6) F4) *ᵥ w) + w) j = if j = i then w i else 0 := by
    intro j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hD, Matrix.mulVec_diagonal]
    have h1 : e * (d j * (d j * w j)) + e ^ 2 * (d j * w j) + w j =
        (e * d j ^ 2 + e ^ 2 * d j + 1) * w j := by ring
    rw [h1, proj_poly (d j) e (hd0 j) (hd0 i)]
    by_cases hj : j = i
    · have hdj : d j = e := by rw [hj]
      rw [if_pos hdj, if_pos hj, one_mul, hj]
    · have : d j ≠ e := fun h => hj (hsing j h)
      rw [if_neg this, if_neg hj, zero_mul]
  have hiso := hWiso _ hu _ hu
  simp only [hcoord] at hiso
  have hs : ∑ k : Fin 6, ((if k = i then w i else 0) ^ 2 * (if k = i then w i else 0)) =
      w i ^ 2 * w i := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro k _ hk
      simp [hk]
    · simp
  rw [hs] at hiso
  rcases mul_eq_zero.1 hiso with h | h
  · exact pow_eq_zero_iff (by norm_num) |>.1 h
  · exact h

section Ext

variable (d : Fin 6 → F4) (c : F4)

private noncomputable def extV : (Fin (Fintype.card (Blk d c)) → F4) →ₗ[F4] (Fin 6 → F4) where
  toFun w i := if h : d i = c then w (Fintype.equivFin (Blk d c) ⟨i, h⟩) else 0
  map_add' w w' := by
    ext i
    by_cases h : d i = c <;> simp [h]
  map_smul' a w := by
    ext i
    by_cases h : d i = c <;> simp [h]

private theorem extV_pos (w : Fin (Fintype.card (Blk d c)) → F4) {i : Fin 6} (h : d i = c) :
    extV d c w i = w (Fintype.equivFin (Blk d c) ⟨i, h⟩) := by
  simp [extV, h]

private theorem extV_neg (w : Fin (Fintype.card (Blk d c)) → F4) {i : Fin 6} (h : d i ≠ c) :
    extV d c w i = 0 := by
  simp [extV, h]

private theorem sum_extV (v w : Fin (Fintype.card (Blk d c)) → F4) :
    ∑ i : Fin 6, extV d c v i ^ 2 * extV d c w i = ∑ k, v k ^ 2 * w k := by
  rw [sum_blk d c (fun i => extV d c v i ^ 2 * extV d c w i)
    (fun i hi => by rw [extV_neg d c w hi, mul_zero])]
  have : ∀ k : Blk d c, extV d c v k.1 ^ 2 * extV d c w k.1 =
      v (Fintype.equivFin (Blk d c) k) ^ 2 * w (Fintype.equivFin (Blk d c) k) := by
    intro k
    rw [extV_pos d c v k.2, extV_pos d c w k.2]
  simp only [this]
  exact Equiv.sum_comp (Fintype.equivFin (Blk d c)) (fun j => v j ^ 2 * w j)

private theorem mulVec_embSU (A : ↥(StatedSU (Fintype.card (Blk d c)) (2 ^ 1) F4))
    (w : Fin (Fintype.card (Blk d c)) → F4) :
    mM6 (embSU d c A) *ᵥ extV d c w =
      extV d c (((A : GL (Fin (Fintype.card (Blk d c))) F4) :
        Matrix (Fin (Fintype.card (Blk d c))) (Fin (Fintype.card (Blk d c))) F4) *ᵥ w) := by
  ext i
  rw [mM6_embSU]
  by_cases hi : d i = c
  · rw [extV_pos d c _ hi]
    rw [Matrix.mulVec, dotProduct]
    rw [sum_blk d c (fun j => extMat d c (Matrix.reindex (Fintype.equivFin (Blk d c)).symm
        (Fintype.equivFin (Blk d c)).symm
        (((A : GL (Fin (Fintype.card (Blk d c))) F4) :
          Matrix (Fin (Fintype.card (Blk d c))) (Fin (Fintype.card (Blk d c))) F4))) i j *
        extV d c w j) (fun j hj => by rw [extV_neg d c w hj, mul_zero])]
    rw [Matrix.mulVec, dotProduct]
    rw [← Equiv.sum_comp (Fintype.equivFin (Blk d c))
      (fun l => ((A : GL (Fin (Fintype.card (Blk d c))) F4) :
        Matrix (Fin (Fintype.card (Blk d c))) (Fin (Fintype.card (Blk d c))) F4)
          (Fintype.equivFin (Blk d c) ⟨i, hi⟩) l * w l)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [extMat_apply, dif_pos ⟨hi, j.2⟩, extV_pos d c w j.2]
    simp [Matrix.reindex_apply]
  · rw [extV_neg d c _ hi, Matrix.mulVec, dotProduct]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [extMat_apply]
    by_cases hj : d j = c
    · have hne : i ≠ j := fun h => hi (h ▸ hj)
      rw [dif_neg (fun h => hi h.1), Matrix.one_apply_ne hne, zero_mul]
    · rw [extV_neg d c w hj, mul_zero]

theorem core_blk (n : ℕ) (hn : n = 4 ∨ n = 5) (W : Submodule F4 (Fin n → F4)) (hW0 : W ≠ ⊥)
    (hWiso : IsTotallyIsotropicSU 2 W) (X : Subgroup ↥(StatedSU n (2 ^ 1) F4))
    (hXW : ∀ y ∈ X, ∀ w ∈ W, ((y : GL (Fin n) F4) : Matrix (Fin n) (Fin n) F4) *ᵥ w ∈ W)
    {S : Type} [Group S] [IsSimpleGroup S] (hS : Nat.card S = 360) (ψ : ↥X →* S)
    (hψ : Function.Surjective ψ) : False := by
  rcases hn with rfl | rfl
  · apply not_dvd_card_of_stabilizes_isotropic F4_card_four X W hW0 hWiso hXW
    have h1 := Subgroup.card_dvd_of_surjective hψ
    rwa [hS] at h1
  · haveI : Finite S := Nat.finite_of_card_ne_zero (by rw [hS]; norm_num)
    exact CatB.I1431YU5.core_stated F4_card_four W hW0 hWiso X hXW S hS ⟨ψ, hψ⟩

end Ext

theorem no_T_small {D : GL (Fin 6) F4} {d : Fin 6 → F4}
    (hD : (D : Matrix (Fin 6) (Fin 6) F4) = Matrix.diagonal d) (hDiso : D ∈ isoU)
    (hd0 : ∀ i, d i ≠ 0) (c : F4)
    (hc4 : 4 ≤ Fintype.card (Blk d c)) (hc5 : Fintype.card (Blk d c) ≤ 5)
    (hsing : ∀ i, d i ≠ c → Fintype.card (Blk d (d i)) ≤ 1)
    (L : Subgroup M6) (hLC : L ≤ CenD D) (hLperf : ⁅L, L⁆ = L)
    {S : Type} [Group S] [IsSimpleGroup S] (hS : Nat.card S = 360)
    (φ : ↥L →* S) (hφ : Function.Surjective φ)
    (T : Subgroup M6) (hT0 : T ≠ ⊥) (hT2 : IsPGroup 2 ↥T)
    (hLT : L ≤ Subgroup.normalizer (T : Set M6))
    (hDT : ∀ t ∈ T, ∃ t' ∈ T, (t' : GL (Fin 6) F4) = D * (t : GL (Fin 6) F4) * D⁻¹)
    (hDT' : ∀ t ∈ T, ∃ t' ∈ T, (t' : GL (Fin 6) F4) = D⁻¹ * (t : GL (Fin 6) F4) * D) : False := by
  obtain ⟨W, hW0, hWiso, hWinv⟩ := flag_exists T hT0 hT2
  have hWL : ∀ x ∈ L, ∀ w ∈ W, mM6 x *ᵥ w ∈ W := by
    intro x hx w hw
    have hxN := hLT hx
    refine hWinv (x : GL (Fin 6) F4) (statedSU_le_isoU x.2) ?_ ?_ w hw
    · intro t ht
      exact ⟨x * t * x⁻¹, (Subgroup.mem_normalizer_iff.1 hxN t).1 ht, rfl⟩
    · intro t ht
      have h1 := (Subgroup.mem_normalizer_iff.1 (inv_mem hxN) t).1 ht
      rw [inv_inv] at h1
      exact ⟨x⁻¹ * t * x, h1, rfl⟩
  have hWD : ∀ w ∈ W, (D : Matrix (Fin 6) (Fin 6) F4) *ᵥ w ∈ W := fun w hw =>
    hWinv D hDiso hDT hDT' w hw
  have hW1 : ∀ w ∈ W, ∀ i, d i ≠ c → w i = 0 := by
    intro w hw i hi
    refine coord_eq_zero_of_single hD hd0 hWiso hWD ?_ hw
    intro j hj
    have := Fintype.card_le_one_iff.1 (hsing i hi) ⟨j, hj⟩ ⟨i, rfl⟩
    exact congrArg Subtype.val this
  let W' : Submodule F4 (Fin (Fintype.card (Blk d c)) → F4) := W.comap (extV d c)
  have hW'0 : W' ≠ ⊥ := by
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
    intro hbot
    apply hw0
    have hext : w = extV d c (fun k => w ((Fintype.equivFin (Blk d c)).symm k).1) := by
      funext i
      by_cases hi : d i = c
      · rw [extV_pos d c _ hi]
        simp
      · rw [extV_neg d c _ hi]
        exact hW1 w hw i hi
    have hmem : (fun k => w ((Fintype.equivFin (Blk d c)).symm k).1) ∈ W' := by
      show extV d c _ ∈ W
      rw [← hext]
      exact hw
    rw [hbot, Submodule.mem_bot] at hmem
    rw [hext, hmem, map_zero]
  have hW'iso : IsTotallyIsotropicSU 2 W' := by
    intro v hv w hw
    have := hWiso _ hv _ hw
    rwa [sum_extV d c v w] at this
  have hsmall : ∀ c' : F4, c' ≠ c → Fintype.card (Blk d c') ≤ 3 := by
    intro c' hc'
    by_cases h : ∃ i, d i = c'
    · obtain ⟨i, rfl⟩ := h
      exact (hsing i hc').trans (by norm_num)
    · have : Fintype.card (Blk d c') = 0 :=
        Fintype.card_eq_zero_iff.2 ⟨fun ⟨i, hi⟩ => h ⟨i, hi⟩⟩
      omega
  have hLE := le_range_embSU d c hD hsmall hLC hLperf
  let X : Subgroup ↥(StatedSU (Fintype.card (Blk d c)) (2 ^ 1) F4) := L.comap (embSU d c)
  have hXW : ∀ y ∈ X, ∀ w ∈ W', ((y : GL (Fin (Fintype.card (Blk d c))) F4) :
      Matrix (Fin (Fintype.card (Blk d c))) (Fin (Fintype.card (Blk d c))) F4) *ᵥ w ∈ W' := by
    intro y hy w hw
    show extV d c _ ∈ W
    rw [← mulVec_embSU d c y w]
    exact hWL _ hy _ hw
  let θ : ↥X →* ↥L := ((embSU d c).comp X.subtype).codRestrict L (fun A => A.2)
  have hθ : Function.Surjective θ := by
    intro l
    obtain ⟨A, hA⟩ := hLE l.2
    exact ⟨⟨A, by show embSU d c A ∈ L; rw [hA]; exact l.2⟩, Subtype.ext hA⟩
  exact core_blk (Fintype.card (Blk d c)) (by omega) W' hW'0 hW'iso X hXW hS (φ.comp θ)
    (hφ.comp hθ)

end CFSG.LocalAnalysis.GLTheoremA.CatB.I2016U6

end
