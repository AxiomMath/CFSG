module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi22FiveAbstract
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi22FiveWords
public import Certificates.Certificate9550

public section

namespace CFSG.AGLEmbedding.KFactProofs.Fi22Five

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer
  CFSG.Sporadic.FischerOddCore

theorem orb_check : orbCheck = true :=
  Certificates.certificate9550

def wordProdN {G : Type*} [Group G] (n₁ n₂ : G) (w : List Nat) : G :=
  w.foldr (fun k A => (if k = 1 then n₁ else n₂) * A) 1

theorem wordProdN_map {G H : Type*} [Group G] [Group H] (f : G →* H) (n₁ n₂ : G)
    (w : List Nat) : f (wordProdN n₁ n₂ w) = wordProdN (f n₁) (f n₂) w := by
  induction w with
  | nil => simp [wordProdN]
  | cons k w ih =>
    simp only [wordProdN, List.foldr_cons] at ih ⊢
    rw [map_mul, ih]
    split_ifs <;> rfl

theorem wordProdN_mem {G : Type*} [Group G] {S : Subgroup G} {n₁ n₂ : G} (h₁ : n₁ ∈ S)
    (h₂ : n₂ ∈ S) (w : List Nat) : wordProdN n₁ n₂ w ∈ S := by
  induction w with
  | nil => exact S.one_mem
  | cons k w ih =>
    simp only [wordProdN, List.foldr_cons] at ih ⊢
    refine S.mul_mem ?_ ih
    split_ifs
    exacts [h₁, h₂]

theorem rep_nProd {N₁ N₂ : Equiv.Perm (Fin 3510)} (h₁ : Rep 3510 n1A N₁) (h₂ : Rep 3510 n2A N₂)
    (w : List Nat) : Rep 3510 (nProd w) (wordProdN N₁ N₂ w) := by
  induction w with
  | nil =>
    simp only [nProd, wordProdN, List.foldr_nil]
    exact rep_idA
  | cons k w ih =>
    simp only [nProd, wordProdN, List.foldr_cons] at ih ⊢
    refine rep_compA ?_ ih
    split_ifs
    exacts [h₁, h₂]

theorem orbit_part :
    ∃ X Y : fi22P, Rep 3510 xA X.1 ∧ Rep 3510 yA Y.1 ∧ PlaneData X Y ∧ NormData X Y := by
  have h := orb_check
  unfold orbCheck at h
  simp only [Bool.and_eq_true, and_assoc] at h
  obtain ⟨hlx, hly, hl1, hl2, hx5, hy5, hcomm, hne, c1x, c1y, c2x, c2y, hconj⟩ := h
  obtain ⟨X, hXP, hX⟩ := exists_rep_evalW hlx
  obtain ⟨Y, hYP, hY⟩ := exists_rep_evalW hly
  obtain ⟨N1, hN1P, hN1⟩ := exists_rep_evalW hl1
  obtain ⟨N2, hN2P, hN2⟩ := exists_rep_evalW hl2
  have hX' : Rep 3510 xA X := hX
  have hY' : Rep 3510 yA Y := hY
  have hN1' : Rep 3510 n1A N1 := hN1
  have hN2' : Rep 3510 n2A N2 := hN2
  have hX5 : X ^ 5 = 1 := (eqA_iff (rep_pw hX' 5) rep_idA).1 hx5
  have hY5 : Y ^ 5 = 1 := (eqA_iff (rep_pw hY' 5) rep_idA).1 hy5
  have hXY : X * Y = Y * X := (eqA_iff (rep_compA hX' hY') (rep_compA hY' hX')).1 hcomm
  have hne' : ∀ i < 5, ∀ j < 5, ¬ (i = 0 ∧ j = 0) → X ^ i * Y ^ j ≠ 1 := by
    intro i hi j hj hij h1
    have h2 := allLt_spec (allLt_spec hne hi) hj
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h2
    rcases h2 with h2 | h2
    · exact hij h2
    · have := (eqA_iff (rep_planeA hX' hY' i j) rep_idA).2 h1
      rw [this] at h2
      exact Bool.noConfusion h2
  have hN1X : N1 * X = X ^ 2 * Y ^ 3 * N1 :=
    (eqA_iff (rep_compA hN1' hX') (rep_compA (rep_planeA hX' hY' 2 3) hN1')).1 c1x
  have hN1Y : N1 * Y = X ^ 1 * Y ^ 2 * N1 :=
    (eqA_iff (rep_compA hN1' hY') (rep_compA (rep_planeA hX' hY' 1 2) hN1')).1 c1y
  have hN2X : N2 * X = X ^ 4 * Y ^ 1 * N2 :=
    (eqA_iff (rep_compA hN2' hX') (rep_compA (rep_planeA hX' hY' 4 1) hN2')).1 c2x
  have hN2Y : N2 * Y = X ^ 1 * Y ^ 1 * N2 :=
    (eqA_iff (rep_compA hN2' hY') (rep_compA (rep_planeA hX' hY' 1 1) hN2')).1 c2y
  set x : fi22P := ⟨X, hXP⟩ with hx_def
  set y : fi22P := ⟨Y, hYP⟩ with hy_def
  set n1 : fi22P := ⟨N1, hN1P⟩ with hn1_def
  set n2 : fi22P := ⟨N2, hN2P⟩ with hn2_def
  have hD : PlaneData x y := by
    refine ⟨Subtype.ext hX5, Subtype.ext hY5, Subtype.ext hXY, fun v hv h => ?_⟩
    refine hne' (v 0).val (ZMod.val_lt _) (v 1).val (ZMod.val_lt _) ?_ (congrArg Subtype.val h)
    rintro ⟨h0, h1⟩
    exact hv (funext fun i => by
      fin_cases i
      · exact (ZMod.val_eq_zero _).1 h0
      · exact (ZMod.val_eq_zero _).1 h1)
  refine ⟨x, y, hX', hY', hD, ?_⟩
  have hxm : ∀ i j : ℕ, x ^ i * y ^ j ∈ Subgroup.closure ({x, y} : Set fi22P) := fun i j =>
    Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
      (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
  have hconj_of : ∀ (n a b : fi22P), n * a = b * n → n * a * n⁻¹ = b := fun n a b h => by
    rw [h]
    group
  have hn1x : n1 * x * n1⁻¹ = x ^ 2 * y ^ 3 := hconj_of _ _ _ (Subtype.ext hN1X)
  have hn1y : n1 * y * n1⁻¹ = x ^ 1 * y ^ 2 := hconj_of _ _ _ (Subtype.ext hN1Y)
  have hn2x : n2 * x * n2⁻¹ = x ^ 4 * y ^ 1 := hconj_of _ _ _ (Subtype.ext hN2X)
  have hn2y : n2 * y * n2⁻¹ = x ^ 1 * y ^ 1 := hconj_of _ _ _ (Subtype.ext hN2Y)
  have hn1 := mem_normalizer_closure_pair (x := x) (y := y) (n := n1)
    (by rw [hn1x]; exact hxm 2 3) (by rw [hn1y]; exact hxm 1 2)
  have hn2 := mem_normalizer_closure_pair (x := x) (y := y) (n := n2)
    (by rw [hn2x]; exact hxm 4 1) (by rw [hn2y]; exact hxm 1 1)
  unfold NormData
  intro v hv
  have hspec := allLt_spec (allLt_spec hconj (ZMod.val_lt (v 0))) (ZMod.val_lt (v 1))
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, List.any_eq_true] at hspec
  rcases hspec with ⟨h0, h1⟩ | ⟨t, ht, ⟨hti, htj⟩, htok⟩
  · exact absurd (funext fun i => by
      fin_cases i
      · exact (ZMod.val_eq_zero _).1 h0
      · exact (ZMod.val_eq_zero _).1 h1) hv
  · refine ⟨wordProdN n1 n2 t.2.2, wordProdN_mem hn1 hn2 _, ?_⟩
    have hM := rep_nProd hN1' hN2' t.2.2
    have hrel : wordProdN N1 N2 t.2.2 * X =
        (X ^ (v 0).val * Y ^ (v 1).val) * wordProdN N1 N2 t.2.2 := by
      have := (eqA_iff (rep_compA hM hX') (rep_compA (rep_planeA hX' hY' t.1 t.2.1) hM)).1 htok
      rwa [hti, htj] at this
    have hcoe : (wordProdN n1 n2 t.2.2).1 = wordProdN N1 N2 t.2.2 :=
      wordProdN_map fi22P.subtype n1 n2 t.2.2
    apply Subtype.ext
    show (wordProdN n1 n2 t.2.2).1 * X * ((wordProdN n1 n2 t.2.2).1)⁻¹ =
      X ^ (v 0).val * Y ^ (v 1).val
    rw [hcoe, mul_inv_eq_iff_eq_mul]
    exact hrel

end CFSG.AGLEmbedding.KFactProofs.Fi22Five
