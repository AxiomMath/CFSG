module

public import CFSG.LieType.Chevalley.IntrinsicSimplePairs
import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.BruhatUnique
import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.PairStabilizerNativePart1

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.F4AdjointCert
public import CFSG.LieType.Ree.Duality

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Ree
open CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.F4Adjoint

section

private theorem f4_repsCheck_local : CFSG.LieType.Chevalley.RootOps.repsCheck Tag.F4 CFSG.LieType.Chevalley.RootOps.f4Reps = true := by
  decide +kernel

private theorem f4_coverCheck_local :
    CFSG.LieType.Chevalley.RootOps.coverCheck Tag.F4 CFSG.LieType.Chevalley.RootOps.f4Reps CFSG.LieType.Chevalley.RootOps.f4Cover = true := by
  decide +kernel

private lemma no_root_supported_pair_check :
    ∀ i j : Fin Tag.F4.rank, i ≠ j →
      ¬(i.val + 1 = j.val ∨ j.val + 1 = i.val) →
      ∀ γ ∈ rootFinset Tag.F4,
        ¬(γ i ≠ 0 ∧ γ j ≠ 0 ∧ ∀ k, k ≠ i → k ≠ j → γ k = 0) := by
  decide +kernel

private lemma no_root_supported_pair {i j : Fin Tag.F4.rank} (hij : i ≠ j)
    (hna : ¬(i.val + 1 = j.val ∨ j.val + 1 = i.val)) :
    ¬ ∃ γ : Fin Tag.F4.rank → ℤ, IsRoot Tag.F4 γ ∧ γ i ≠ 0 ∧ γ j ≠ 0 ∧
      ∀ k, k ≠ i → k ≠ j → γ k = 0 := by
  rintro ⟨γ, hγ, hi, hj, hzero⟩
  rw [← mem_rootFinset] at hγ
  exact no_root_supported_pair_check i j hij hna γ hγ ⟨hi, hj, hzero⟩

private lemma no_pos_combo_root {i j : Fin Tag.F4.rank} (hij : i ≠ j)
    (hna : ¬(i.val + 1 = j.val ∨ j.val + 1 = i.val)) (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    ¬ IsRoot Tag.F4 (a • (simpleRoot Tag.F4 i).1 + b • (simpleRoot Tag.F4 j).1) := by
  intro hroot
  apply no_root_supported_pair hij hna
  refine ⟨_, hroot, ?_, ?_, ?_⟩
  · have hcoef : (a • (simpleRoot Tag.F4 i).1 + b • (simpleRoot Tag.F4 j).1) i = (a : ℤ) := by
      simp [simpleRoot, Pi.single_eq_same, Pi.single_eq_of_ne hij]
    rw [hcoef]
    exact_mod_cast (Nat.one_le_iff_ne_zero.mp ha)
  · have hcoef : (a • (simpleRoot Tag.F4 i).1 + b • (simpleRoot Tag.F4 j).1) j = (b : ℤ) := by
      simp [simpleRoot, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hij)]
    rw [hcoef]
    exact_mod_cast (Nat.one_le_iff_ne_zero.mp hb)
  · intro k hki hkj
    rw [show (simpleRoot Tag.F4 i).1 = (Pi.single i 1 : Fin Tag.F4.rank → ℤ) from rfl,
      show (simpleRoot Tag.F4 j).1 = (Pi.single j 1 : Fin Tag.F4.rank → ℤ) from rfl]
    simp [Pi.single_eq_of_ne hki, Pi.single_eq_of_ne hkj]

private theorem f4_simple_ringComm {K : Type} [CommRing K]
    {i j : Fin Tag.F4.rank} (hij : i ≠ j)
    :
    (rootOperatorFamily Tag.F4).RingCommContained K (simpleRoot Tag.F4 i) (simpleRoot Tag.F4 j) := by
  have hβ : 0 < height (simpleRoot Tag.F4 j).1 := by
    simp [height, simpleRoot]
  have hne : simpleRoot Tag.F4 j ≠ simpleRoot Tag.F4 i := by
    intro h
    have h' := congrFun (congrArg Subtype.val h) i
    simp [simpleRoot, Ne.symm hij] at h'
  exact CFSG.LieType.Chevalley.RootOps.ringCommContained_of_checks (R := K) (τ := Tag.F4)
    (CFSG.LieType.Chevalley.RootOps.dataChecks_F4).valid (CFSG.LieType.Chevalley.RootOps.dataChecks_F4).tab
    f4_repsCheck_local f4_coverCheck_local i (simpleRoot Tag.F4 j) hβ hne

public theorem f4_nonadjacent_xUnit_commute {K : Type} [Field K] [CharP K 2]
    {i j : Fin Tag.F4.rank} (hij : i ≠ j)
    (hna : ¬(i.val + 1 = j.val ∨ j.val + 1 = i.val)) (c d : K) :
    Commute (xUnit Tag.F4 K i c) (xUnit Tag.F4 K j d) := by
  let F := rootOperatorFamily Tag.F4
  have hRC := f4_simple_ringComm (K := K) hij
  have hno : ∀ γ : Root Tag.F4,
      ¬ ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧
        γ.1 = a • (simpleRoot Tag.F4 i).1 + b • (simpleRoot Tag.F4 j).1 := by
    rintro γ ⟨a, b, ha, hb, hγ⟩
    exact no_pos_combo_root hij hna a b ha hb (hγ ▸ γ.2)
  have hbot : (⨆ (γ : Root Tag.F4) (_ : ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧
      γ.1 = a • (simpleRoot Tag.F4 i).1 + b • (simpleRoot Tag.F4 j).1),
      F.ringRootSubgroup K γ) = ⊥ := by
    refine iSup_eq_bot.mpr fun γ => ?_
    refine iSup_eq_bot.mpr fun h => ?_
    exact (hno γ h).elim
  have hmem := (RootOperatorFamily.ringCommContained_iff (F := F) (R := K)
    (α := simpleRoot Tag.F4 i) (β := simpleRoot Tag.F4 j)).1 hRC c d
  have hcomm1 : F.eltUnit K (simpleRoot Tag.F4 i) c * F.eltUnit K (simpleRoot Tag.F4 j) d *
      (F.eltUnit K (simpleRoot Tag.F4 i) c)⁻¹ * (F.eltUnit K (simpleRoot Tag.F4 j) d)⁻¹ = 1 := by
    rw [hbot] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hcomm : Commute (F.eltUnit K (simpleRoot Tag.F4 i) c)
      (F.eltUnit K (simpleRoot Tag.F4 j) d) := by
    rw [← commutatorElement_eq_one_iff_commute, commutatorElement_def]
    exact hcomm1
  simpa only [RootOperatorFamily.eltUnit_simple] using hcomm

public theorem f4_nonadjacent_simplePos_commute
    {K : Type} [Field K] [CharP K 2]
    {i j : Fin Tag.F4.rank} (hij : i ≠ j)
    (hna : ¬(i.val + 1 = j.val ∨ j.val + 1 = i.val)) :
    ∀ x ∈ simplePosSubgroup Tag.F4 K i,
      ∀ y ∈ simplePosSubgroup Tag.F4 K j, Commute x y := by
  intro x hx y hy
  obtain ⟨c, hc⟩ := (mem_simplePosSubgroup (τ := Tag.F4) (K := K)).1 hx
  obtain ⟨d, hd⟩ := (mem_simplePosSubgroup (τ := Tag.F4) (K := K)).1 hy
  have hx' : x = (⟨xUnit Tag.F4 K i c, xUnit_mem_adjointGroup i c⟩ :
      adjointGroup Tag.F4 K) := Subtype.ext hc
  have hy' : y = (⟨xUnit Tag.F4 K j d, xUnit_mem_adjointGroup j d⟩ :
      adjointGroup Tag.F4 K) := Subtype.ext hd
  rw [hx', hy']
  have hcUnit := f4_nonadjacent_xUnit_commute hij hna c d
  refine Subtype.ext ?_
  exact hcUnit.eq

end
private def fin0 : Fin Tag.F4.rank := ⟨0, by decide⟩
private def fin1 : Fin Tag.F4.rank := ⟨1, by decide⟩
private def fin2 : Fin Tag.F4.rank := ⟨2, by decide⟩
private def fin3 : Fin Tag.F4.rank := ⟨3, by decide⟩

section Tables

variable {K : Type} [Field K] [CharP K 2]

private lemma xOp_one_mul_ne_of_bit
    (i j : Fin Tag.F4.rank) (b q : ℕ) (hb : b < 52) (hq : q < 52)
    (hbit : (idxMask (applyX (i : ℕ) (applyX (j : ℕ) [b]))).testBit q ≠
      (idxMask (applyX (j : ℕ) (applyX (i : ℕ) [b]))).testBit q) :
    xOp Tag.F4 K i 1 * xOp Tag.F4 K j 1 ≠
      xOp Tag.F4 K j 1 * xOp Tag.F4 K i 1 := by
  intro heq
  have hL0 : ∀ l ∈ [b], l < 52 := by simpa using hb
  have hLji : ∀ l ∈ applyX (j : ℕ) [b], l < 52 := applyX_lt j hL0
  have hLij : ∀ l ∈ applyX (i : ℕ) [b], l < 52 := applyX_lt i hL0
  have hv := congrArg
    (fun f : Module.End K (RootModule Tag.F4 K) => f (lvec K [b])) heq
  simp only [Module.End.mul_apply] at hv
  rw [xOp_one_lvec j hL0, xOp_one_lvec i hLji,
    xOp_one_lvec i hL0, xOp_one_lvec j hLij] at hv
  have hcoord := congrArg
    (fun v : RootModule Tag.F4 K => v (lab ⟨q, hq⟩)) hv
  rw [← toVec_idxMask, ← toVec_idxMask, toVec_apply_lab, toVec_apply_lab] at hcoord
  by_cases h1 : (idxMask (applyX (i : ℕ) (applyX (j : ℕ) [b]))).testBit q <;>
    by_cases h2 : (idxMask (applyX (j : ℕ) (applyX (i : ℕ) [b]))).testBit q <;>
    simp [h1, h2] at hcoord hbit

private lemma bit_01 :
    (idxMask (applyX (0 : ℕ) (applyX (1 : ℕ) [0]))).testBit 9 ≠
      (idxMask (applyX (1 : ℕ) (applyX (0 : ℕ) [0]))).testBit 9 := by
  decide +kernel

private lemma bit_12 :
    (idxMask (applyX (1 : ℕ) (applyX (2 : ℕ) [0]))).testBit 12 ≠
      (idxMask (applyX (2 : ℕ) (applyX (1 : ℕ) [0]))).testBit 12 := by
  decide +kernel

private lemma bit_23 :
    (idxMask (applyX (2 : ℕ) (applyX (3 : ℕ) [1]))).testBit 14 ≠
      (idxMask (applyX (3 : ℕ) (applyX (2 : ℕ) [1]))).testBit 14 := by
  decide +kernel

private lemma xOp_ncomm_01 :
    xOp Tag.F4 K ⟨0, by decide⟩ 1 * xOp Tag.F4 K ⟨1, by decide⟩ 1 ≠
      xOp Tag.F4 K ⟨1, by decide⟩ 1 * xOp Tag.F4 K ⟨0, by decide⟩ 1 :=
  xOp_one_mul_ne_of_bit (K := K) ⟨0, by decide⟩ ⟨1, by decide⟩ 0 9
    (by norm_num) (by norm_num) bit_01

private lemma xOp_ncomm_12 :
    xOp Tag.F4 K ⟨1, by decide⟩ 1 * xOp Tag.F4 K ⟨2, by decide⟩ 1 ≠
      xOp Tag.F4 K ⟨2, by decide⟩ 1 * xOp Tag.F4 K ⟨1, by decide⟩ 1 :=
  xOp_one_mul_ne_of_bit (K := K) ⟨1, by decide⟩ ⟨2, by decide⟩ 0 12
    (by norm_num) (by norm_num) bit_12

private lemma xOp_ncomm_23 :
    xOp Tag.F4 K ⟨2, by decide⟩ 1 * xOp Tag.F4 K ⟨3, by decide⟩ 1 ≠
      xOp Tag.F4 K ⟨3, by decide⟩ 1 * xOp Tag.F4 K ⟨2, by decide⟩ 1 :=
  xOp_one_mul_ne_of_bit (K := K) ⟨2, by decide⟩ ⟨3, by decide⟩ 1 14
    (by norm_num) (by norm_num) bit_23

omit [CharP K 2] in
private lemma xUnit_ncomm_of_xOp {i j : Fin Tag.F4.rank}
    (h : xOp Tag.F4 K i 1 * xOp Tag.F4 K j 1 ≠
      xOp Tag.F4 K j 1 * xOp Tag.F4 K i 1) :
    ¬ Commute (xUnit Tag.F4 K i 1) (xUnit Tag.F4 K j 1) := by
  intro hc
  apply h
  have hv := congrArg Units.val hc.eq
  simpa [Units.val_mul, coe_xUnit] using hv

private lemma xUnit_ncomm_01 :
    ¬ Commute (xUnit Tag.F4 K ⟨0, by decide⟩ 1) (xUnit Tag.F4 K ⟨1, by decide⟩ 1) :=
  xUnit_ncomm_of_xOp (K := K) (i := ⟨0, by decide⟩) (j := ⟨1, by decide⟩) xOp_ncomm_01

private lemma xUnit_ncomm_12 :
    ¬ Commute (xUnit Tag.F4 K ⟨1, by decide⟩ 1) (xUnit Tag.F4 K ⟨2, by decide⟩ 1) :=
  xUnit_ncomm_of_xOp (K := K) (i := ⟨1, by decide⟩) (j := ⟨2, by decide⟩) xOp_ncomm_12

private lemma xUnit_ncomm_23 :
    ¬ Commute (xUnit Tag.F4 K ⟨2, by decide⟩ 1) (xUnit Tag.F4 K ⟨3, by decide⟩ 1) :=
  xUnit_ncomm_of_xOp (K := K) (i := ⟨2, by decide⟩) (j := ⟨3, by decide⟩) xOp_ncomm_23

end Tables

section CommuteIf

variable {K : Type} [Field K] [CharP K 2]

omit [CharP K 2] in
private lemma xUnit_mem_simplePos (i : Fin Tag.F4.rank) (c : K) :
    (⟨xUnit Tag.F4 K i c, xUnit_mem_adjointGroup i c⟩ : adjointGroup Tag.F4 K) ∈
      simplePosSubgroup Tag.F4 K i :=
  (mem_simplePosSubgroup (τ := Tag.F4) (K := K)).2 ⟨c, rfl⟩

private lemma commute_simplePos_of_nonadjacent
    {i j : Fin Tag.F4.rank} (hij : i ≠ j)
    (hna : ¬(i.val + 1 = j.val ∨ j.val + 1 = i.val)) :
    ∀ x ∈ simplePosSubgroup Tag.F4 K i,
      ∀ y ∈ simplePosSubgroup Tag.F4 K j, Commute x y :=
  f4_nonadjacent_simplePos_commute
    (K := K) hij hna

private lemma adjacent_not_commute
    {i j : Fin Tag.F4.rank}
    (hadj : i.val + 1 = j.val ∨ j.val + 1 = i.val) :
    ¬ (∀ x ∈ simplePosSubgroup Tag.F4 K i,
      ∀ y ∈ simplePosSubgroup Tag.F4 K j, Commute x y) := by
  have hcases : ∀ l l' : Fin Tag.F4.rank, l.val + 1 = l'.val →
      (l = fin0 ∧ l' = fin1) ∨ (l = fin1 ∧ l' = fin2) ∨ (l = fin2 ∧ l' = fin3) := by
    decide +kernel
  have hnc : ∀ l l' : Fin Tag.F4.rank, l.val + 1 = l'.val →
      ¬ Commute (xUnit Tag.F4 K l 1) (xUnit Tag.F4 K l' 1) := by
    intro l l' hll'
    rcases hcases l l' hll' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    exacts [xUnit_ncomm_01 (K := K), xUnit_ncomm_12 (K := K), xUnit_ncomm_23 (K := K)]
  intro h
  have hc : Commute (xUnit Tag.F4 K i 1) (xUnit Tag.F4 K j 1) := by
    have hsub := h ⟨xUnit Tag.F4 K i 1, xUnit_mem_adjointGroup i 1⟩
      (xUnit_mem_simplePos i 1) ⟨xUnit Tag.F4 K j 1, xUnit_mem_adjointGroup j 1⟩
      (xUnit_mem_simplePos j 1)
    have hv := congrArg Subtype.val hsub.eq
    change (xUnit Tag.F4 K i 1 * xUnit Tag.F4 K j 1 : ModGL Tag.F4 K) =
      xUnit Tag.F4 K j 1 * xUnit Tag.F4 K i 1 at hv
    exact hv
  rcases hadj with hadj | hadj
  · exact hnc i j hadj hc
  · exact hnc j i hadj hc.symm

end CommuteIf

section Public


public theorem f4_even_simplePos_commute_iff
    {K : Type} [Field K] [CharP K 2] {i j : Fin Tag.F4.rank} (hij : i ≠ j) :
    (∀ x ∈ simplePosSubgroup Tag.F4 K i,
      ∀ y ∈ simplePosSubgroup Tag.F4 K j, Commute x y) ↔
      ¬(i.val + 1 = j.val ∨ j.val + 1 = i.val) := by
  constructor
  · intro h hadj
    exact adjacent_not_commute hadj h
  · intro hna
    exact commute_simplePos_of_nonadjacent hij hna


public theorem f4_even_simple_pair_perm
    {K : Type} [Field K] [CharP K 2]
    {β : MulAut (adjointGroup Tag.F4 K)}
    {π : Equiv.Perm (Fin Tag.F4.rank)}
    (hπ : ∀ i, (simplePosSubgroup Tag.F4 K i).map β.toMonoidHom =
      simplePosSubgroup Tag.F4 K (π i)) :
    π = 1 ∨ π = ReeTag.F4.perm := by
  have hadj : ∀ i j : Fin Tag.F4.rank, i ≠ j →
      ((i.val + 1 = j.val ∨ j.val + 1 = i.val) ↔
        ((π i).val + 1 = (π j).val ∨ (π j).val + 1 = (π i).val)) := by
    intro i j hij
    have htr :
        (∀ x ∈ simplePosSubgroup Tag.F4 K i, ∀ y ∈ simplePosSubgroup Tag.F4 K j, Commute x y) ↔
          (∀ x ∈ simplePosSubgroup Tag.F4 K (π i),
            ∀ y ∈ simplePosSubgroup Tag.F4 K (π j), Commute x y) := by
      constructor
      · intro h x hx y hy
        rw [← hπ i] at hx
        rw [← hπ j] at hy
        obtain ⟨x0, hx0, rfl⟩ := hx
        obtain ⟨y0, hy0, rfl⟩ := hy
        exact (h x0 hx0 y0 hy0).map β.toMonoidHom
      · intro h x hx y hy
        have h1 := h (β x) (hπ i ▸ ⟨x, hx, rfl⟩) (β y) (hπ j ▸ ⟨y, hy, rfl⟩)
        have h2 := h1.map β.symm.toMonoidHom
        simpa using h2
    rw [f4_even_simplePos_commute_iff hij,
      f4_even_simplePos_commute_iff (π.injective.ne hij)] at htr
    exact not_iff_not.1 htr
  have key : ∀ π : Equiv.Perm (Fin Tag.F4.rank),
      (∀ i j : Fin Tag.F4.rank, i ≠ j →
        ((i.val + 1 = j.val ∨ j.val + 1 = i.val) ↔
          ((π i).val + 1 = (π j).val ∨ (π j).val + 1 = (π i).val))) →
      π = 1 ∨ π = Equiv.swap fin0 fin3 * Equiv.swap fin1 fin2 := by
    decide
  have hperm : ReeTag.F4.perm = Equiv.swap fin0 fin3 * Equiv.swap fin1 fin2 := rfl
  rcases key π hadj with h | h
  · exact Or.inl h
  · exact Or.inr (h.trans hperm.symm)


section OriginalPair

variable {K : Type} [Field K]

namespace F4SimplePairExtraction

open CFSG.StandardType.F4ExplicitPos.BruhatUnique
open CFSG.StandardType.F4ExplicitPos.PairStabilizerNative
open CFSG.StandardType.F4ExplicitPos.BruhatNo117
open scoped Pointwise commutatorElement

private theorem f4_commute_xUnit_yUnit_of_ne' {i j : Fin Tag.F4.rank} (hij : i ≠ j) (c d : K) :
    Commute (xUnit Tag.F4 K i c) (yUnit Tag.F4 K j d) := by
  have hne : (Pi.single i 1 : Fin Tag.F4.rank → ℤ) - Pi.single j 1 ≠ 0 := by
    intro h
    have := congrFun h i
    simp [hij] at this
  have hroot : ¬ IsRoot Tag.F4 (Pi.single i 1 - Pi.single j 1) := by
    intro h
    rcases IsRoot.nonneg_or_nonpos h with h | h
    · have := h j
      simp [hij] at this
    · have := h i
      simp [hij] at this
  have h := f4_commute_pinnedX_of_not_isRoot (K := K) (isRoot_single Tag.F4 i)
    (isRoot_neg_single Tag.F4 j) (by simpa [sub_eq_add_neg] using hne)
    (by simpa [sub_eq_add_neg] using hroot) c d
  simpa only [pinnedX_single, pinnedX_neg_single] using h

private theorem f4_mem_borelGroup_of_conj_posUnipotent_le {g : ModGL Tag.F4 K}
    (hg : g ∈ adjointGroup Tag.F4 K)
    (h : ∀ b ∈ borelGroup Tag.F4 K, ∀ b' ∈ borelGroup Tag.F4 K, ∀ w : WeylGroup Tag.F4,
      b * canonicalRep (coxeterSystem Tag.F4) K w * b' = g →
      ∀ u ∈ posUnipotent Tag.F4 K, canonicalRep (coxeterSystem Tag.F4) K w * u *
        (canonicalRep (coxeterSystem Tag.F4) K w)⁻¹ ∈ borelGroup Tag.F4 K) :
    g ∈ borelGroup Tag.F4 K := by
  have hg' : g ∈ ⋃ w, bruhatCell Tag.F4 K w := by
    rw [← f4_adjointGroup_eq_iUnion_bruhatCell]
    exact hg
  obtain ⟨w, hw⟩ := Set.mem_iUnion.1 hg'
  obtain ⟨b, hb, b', hb', rfl⟩ := mem_bruhatCell.1 hw
  have hw1 := eq_one_of_canonicalRep_conj_posUnipotent_le (h b hb b' hb' w rfl)
  subst hw1
  rw [canonicalRep_one, mul_one]
  exact mul_mem hb hb'

private theorem f4_borel_self_normalizers :
    adjointGroup Tag.F4 K ⊓
        Subgroup.normalizer (posUnipotent Tag.F4 K : Set (ModGL Tag.F4 K)) =
      borelGroup Tag.F4 K ∧
    adjointGroup Tag.F4 K ⊓
        Subgroup.normalizer (borelGroup Tag.F4 K : Set (ModGL Tag.F4 K)) =
      borelGroup Tag.F4 K := by
  have hBC : borelGroup Tag.F4 K ≤ adjointGroup Tag.F4 K :=
    ((triangular_borel_structure.{0, 0} Tag.F4 K).2.2.2.2.2.2.2.2.2.2.2 K).1
  have hUB : posUnipotent Tag.F4 K ≤ borelGroup Tag.F4 K := le_sup_right
  have hBN : borelGroup Tag.F4 K ≤
      Subgroup.normalizer (posUnipotent Tag.F4 K : Set (ModGL Tag.F4 K)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUB).1
      (triangular_borel_structure.{0, 0} Tag.F4 K).2.2.2.2.2.2.2.2.1
  refine ⟨le_antisymm (fun g hg => ?_) (le_inf hBC hBN),
    le_antisymm (fun g hg => ?_) (le_inf hBC Subgroup.le_normalizer)⟩
  · obtain ⟨hgC, hgN⟩ := Subgroup.mem_inf.1 hg
    refine f4_mem_borelGroup_of_conj_posUnipotent_le hgC fun b hb b' hb' w hgw u hu => hUB ?_
    have hn : canonicalRep (coxeterSystem Tag.F4) K w = b⁻¹ * g * b'⁻¹ := by
      rw [← hgw]
      group
    have hnN : canonicalRep (coxeterSystem Tag.F4) K w ∈
        Subgroup.normalizer (posUnipotent Tag.F4 K : Set (ModGL Tag.F4 K)) := by
      rw [hn]
      exact mul_mem (mul_mem (inv_mem (hBN hb)) hgN) (inv_mem (hBN hb'))
    exact (Subgroup.mem_normalizer_iff.1 hnN u).1 hu
  · obtain ⟨hgC, hgN⟩ := Subgroup.mem_inf.1 hg
    refine f4_mem_borelGroup_of_conj_posUnipotent_le hgC fun b hb b' hb' w hgw u hu => ?_
    have hn : canonicalRep (coxeterSystem Tag.F4) K w = b⁻¹ * g * b'⁻¹ := by
      rw [← hgw]
      group
    have hnN : canonicalRep (coxeterSystem Tag.F4) K w ∈
        Subgroup.normalizer (borelGroup Tag.F4 K : Set (ModGL Tag.F4 K)) := by
      rw [hn]
      exact mul_mem (mul_mem (inv_mem (Subgroup.le_normalizer hb)) hgN)
        (inv_mem (Subgroup.le_normalizer hb'))
    exact (Subgroup.mem_normalizer_iff.1 hnN u).1 (hUB hu)

private theorem f4_oppositeBorel_normalizer :
    adjointGroup Tag.F4 K ⊓
        Subgroup.normalizer (negUnipotent Tag.F4 K : Set (ModGL Tag.F4 K)) =
      oppositeBorel Tag.F4 K := by
  obtain ⟨w₀, hmax, -, himage, -⟩ := weyl_longest_element Tag.F4
  obtain ⟨hS, -, -⟩ := canonical_weyl_root_transport Tag.F4 K
  set n₀ := canonicalRep (coxeterSystem Tag.F4) K w₀
  have hn₀ : n₀ ∈ adjointGroup Tag.F4 K := canonicalRep_mem_adjointGroup _ K w₀
  have hU : (posUnipotent Tag.F4 K).map (MulAut.conj n₀).toMonoidHom =
      negUnipotent Tag.F4 K := by
    rw [posUnipotent, hS w₀ _ fun α hα => hα.1, himage]
    rfl
  have hB : (borelGroup Tag.F4 K).map (MulAut.conj n₀).toMonoidHom =
      oppositeBorel Tag.F4 K :=
    (opposite_Borel_intersection Tag.F4 K w₀ hmax).2.1
  have hC : (adjointGroup Tag.F4 K).map (MulAut.conj n₀).toMonoidHom =
      adjointGroup Tag.F4 K := by
    ext x
    rw [Subgroup.mem_map_equiv]
    constructor
    · intro hx
      have := mul_mem (mul_mem hn₀ hx) (inv_mem hn₀)
      simpa [mul_assoc] using this
    · intro hx
      exact mul_mem (mul_mem (inv_mem hn₀) hx) hn₀
  rw [← hU, ← hB, ← (f4_borel_self_normalizers).1, Subgroup.map_inf_eq _ _ _
    (MulAut.conj n₀).injective, hC, ← Subgroup.map_equiv_normalizer_eq]

private theorem f4_weylElt_mul_mem_parabolicCells {J : Set (Fin Tag.F4.rank)} {j : Fin Tag.F4.rank}
    (hj : j ∈ J) {x : ModGL Tag.F4 K} (hx : x ∈ parabolicCells Tag.F4 K J) :
    weylElt Tag.F4 K j 1 * x ∈ parabolicCells Tag.F4 K J := by
  obtain ⟨w, hw, hx⟩ := mem_parabolicCells.1 hx
  have hsw : simple Tag.F4 j * w ∈ parabolicWeylGroup Tag.F4 J :=
    mul_mem (Subgroup.subset_closure ⟨j, hj, rfl⟩) hw
  have hn : weylElt Tag.F4 K j 1 ∈ bruhatCell Tag.F4 K (simple Tag.F4 j) := by
    rw [← canonicalRep_simple (coxeterSystem Tag.F4) K j]
    exact canonicalRep_mem_bruhatCell _
  have hmem : weylElt Tag.F4 K j 1 * x ∈ bruhatCell Tag.F4 K (simple Tag.F4 j) *
      bruhatCell Tag.F4 K w := Set.mul_mem_mul hn hx
  rcases f4_bruhatCell_simple_mul_subset j w hmem with hmem | hmem
  · exact mem_parabolicCells.2 ⟨simple Tag.F4 j * w, hsw, hmem⟩
  · exact mem_parabolicCells.2 ⟨w, hw, hmem⟩

private theorem f4_parabolicSubgroup_subset_parabolicCells (J : Set (Fin Tag.F4.rank)) :
    (parabolicSubgroup Tag.F4 K J : Set (ModGL Tag.F4 K)) ⊆ parabolicCells Tag.F4 K J := by
  let M : Subgroup (ModGL Tag.F4 K) :=
    { carrier := {g | (∀ x ∈ parabolicCells Tag.F4 K J, g * x ∈ parabolicCells Tag.F4 K J) ∧
        ∀ x ∈ parabolicCells Tag.F4 K J, g⁻¹ * x ∈ parabolicCells Tag.F4 K J}
      one_mem' := ⟨fun x hx => by rwa [one_mul], fun x hx => by rwa [inv_one, one_mul]⟩
      mul_mem' := fun {a b} ha hb => ⟨fun x hx => by
          rw [mul_assoc]
          exact ha.1 _ (hb.1 x hx), fun x hx => by
          rw [mul_inv_rev, mul_assoc]
          exact hb.2 _ (ha.2 x hx)⟩
      inv_mem' := fun {a} ha => ⟨ha.2, fun x hx => by rw [inv_inv]; exact ha.1 x hx⟩ }
  have hBM : borelGroup Tag.F4 K ≤ M := fun b hb =>
    ⟨fun x hx => borel_mul_mem_parabolicCells hb hx,
      fun x hx => borel_mul_mem_parabolicCells (inv_mem hb) hx⟩
  have hnM : ∀ j ∈ J, weylElt Tag.F4 K j 1 ∈ M := fun j hj => by
    refine ⟨fun x hx => f4_weylElt_mul_mem_parabolicCells hj hx, fun x hx => ?_⟩
    have hsq := weylElt_one_sq (τ := Tag.F4) (R := K) j
    have e : (weylElt Tag.F4 K j 1)⁻¹ =
        weylElt Tag.F4 K j 1 * (torusElt Tag.F4 K j (-1))⁻¹ := by
      rw [← hsq, sq, mul_inv_rev, mul_inv_cancel_left]
    have hd : (torusElt Tag.F4 K j (-1))⁻¹ ∈ borelGroup Tag.F4 K :=
      inv_mem (Subgroup.mem_sup_left (torusElt_mem_torusGroup j (-1)))
    rw [e, mul_assoc]
    exact f4_weylElt_mul_mem_parabolicCells hj (borel_mul_mem_parabolicCells hd hx)
  have hle : parabolicSubgroup Tag.F4 K J ≤ M :=
    sup_le hBM ((Subgroup.closure_le _).2 fun _ ⟨j, hj, he⟩ => he ▸ hnM j hj)
  intro g hg
  have h1 : (1 : ModGL Tag.F4 K) ∈ parabolicCells Tag.F4 K J :=
    mem_parabolicCells.2 ⟨1, one_mem _, one_mem_bruhatCell_one⟩
  simpa using (hle hg).1 1 h1

private theorem f4_parabolicSubgroup_eq_parabolicCells (J : Set (Fin Tag.F4.rank)) :
    (parabolicSubgroup Tag.F4 K J : Set (ModGL Tag.F4 K)) = parabolicCells Tag.F4 K J := by
  refine Set.Subset.antisymm (f4_parabolicSubgroup_subset_parabolicCells J) fun x hx => ?_
  obtain ⟨w, hw, hx⟩ := mem_parabolicCells.1 hx
  exact bruhatCell_subset_parabolicSubgroup hw hx

private theorem f4_weylElt_mem_parabolicSubgroup_iff {J : Set (Fin Tag.F4.rank)}
    {i : Fin Tag.F4.rank} :
    weylElt Tag.F4 K i 1 ∈ parabolicSubgroup Tag.F4 K J ↔ i ∈ J := by
  refine ⟨fun h => ?_, weylElt_mem_parabolicSubgroup⟩
  have h' : weylElt Tag.F4 K i 1 ∈ parabolicCells Tag.F4 K J := by
    rw [← f4_parabolicSubgroup_eq_parabolicCells]
    exact h
  obtain ⟨w, hw, hx⟩ := mem_parabolicCells.1 h'
  have hn : weylElt Tag.F4 K i 1 ∈ bruhatCell Tag.F4 K (simple Tag.F4 i) := by
    rw [← canonicalRep_simple (coxeterSystem Tag.F4) K i]
    exact canonicalRep_mem_bruhatCell _
  by_cases hwi : w = simple Tag.F4 i
  · rw [hwi] at hw
    exact simple_mem_parabolicWeylGroup_iff.1 hw
  · exact absurd hn (Set.disjoint_left.1 (f4_disjoint_bruhatCell hwi) hx)

private theorem f4_standard_parabolic_cells_basic :
    (∀ J : Set (Fin Tag.F4.rank), (parabolicSubgroup Tag.F4 K J : Set (ModGL Tag.F4 K)) =
      ⋃ w ∈ parabolicWeylGroup Tag.F4 J, bruhatCell Tag.F4 K w) ∧
    (∀ w w' : WeylGroup Tag.F4, w ≠ w' →
      Disjoint (bruhatCell Tag.F4 K w) (bruhatCell Tag.F4 K w')) ∧
    (∀ (J : Set (Fin Tag.F4.rank)) (i : Fin Tag.F4.rank),
      weylElt Tag.F4 K i 1 ∈ parabolicSubgroup Tag.F4 K J ↔ i ∈ J) ∧
    (∀ J J' : Set (Fin Tag.F4.rank),
      parabolicSubgroup Tag.F4 K J ≤ parabolicSubgroup Tag.F4 K J' ↔ J ⊆ J') ∧
    parabolicSubgroup Tag.F4 K ∅ = borelGroup Tag.F4 K ∧
    parabolicSubgroup Tag.F4 K Set.univ = adjointGroup Tag.F4 K := by
  refine ⟨fun J => f4_parabolicSubgroup_eq_parabolicCells J,
    fun w w' h => f4_disjoint_bruhatCell h,
    fun J i => f4_weylElt_mem_parabolicSubgroup_iff,
    fun J J' => ⟨fun h j hj => ?_, fun h => ?_⟩, ?_, ?_⟩
  · exact f4_weylElt_mem_parabolicSubgroup_iff.1
      (h (weylElt_mem_parabolicSubgroup hj))
  · exact sup_le_sup_left (Subgroup.closure_mono (Set.image_mono h)) _
  · simp [parabolicSubgroup]
  · rw [(borel_weyl_generation Tag.F4 K).1, parabolicSubgroup, Set.image_univ]

private theorem f4_parabolicSubgroup_le_parabolicSubgroup_iff {J J' : Set (Fin Tag.F4.rank)} :
    parabolicSubgroup Tag.F4 K J ≤ parabolicSubgroup Tag.F4 K J' ↔ J ⊆ J' :=
  (f4_standard_parabolic_cells_basic (K := K)).2.2.2.1 J J'

private theorem f4_parabolicSubgroup_injective :
    Function.Injective (parabolicSubgroup Tag.F4 K) :=
  fun _ _ h => Set.Subset.antisymm
    (f4_parabolicSubgroup_le_parabolicSubgroup_iff.1 h.le)
    (f4_parabolicSubgroup_le_parabolicSubgroup_iff.1 h.ge)

private theorem f4_parabolicSubgroup_empty :
    parabolicSubgroup Tag.F4 K ∅ = borelGroup Tag.F4 K :=
  (f4_standard_parabolic_cells_basic (K := K)).2.2.2.2.1

private theorem f4_borelGroup_lt_parabolicSubgroup {J : Set (Fin Tag.F4.rank)} (hJ : J.Nonempty) :
    borelGroup Tag.F4 K < parabolicSubgroup Tag.F4 K J := by
  refine lt_of_le_of_ne (borelGroup_le_parabolicSubgroup J) fun h => ?_
  rw [← f4_parabolicSubgroup_empty] at h
  exact hJ.ne_empty (f4_parabolicSubgroup_injective h).symm

private theorem f4_nonempty_of_borelGroup_lt {J : Set (Fin Tag.F4.rank)}
    (h : borelGroup Tag.F4 K < parabolicSubgroup Tag.F4 K J) : J.Nonempty := by
  rw [Set.nonempty_iff_ne_empty]
  rintro rfl
  rw [f4_parabolicSubgroup_empty] at h
  exact lt_irrefl _ h

private theorem f4_eq_parabolicSubgroup_of_borelGroup_le {A : Subgroup (ModGL Tag.F4 K)}
    (hB : borelGroup Tag.F4 K ≤ A) (hA : A ≤ adjointGroup Tag.F4 K) :
    A = parabolicSubgroup Tag.F4 K {i | weylElt Tag.F4 K i 1 ∈ A} := by
  refine le_antisymm (fun g hg => ?_) (sup_le hB ((Subgroup.closure_le _).2 ?_))
  · have hg' : g ∈ ⋃ w, bruhatCell Tag.F4 K w := by
      rw [← f4_adjointGroup_eq_iUnion_bruhatCell]
      exact hA hg
    obtain ⟨w, hw⟩ := Set.mem_iUnion.1 hg'
    obtain ⟨b, hb, b', hb', rfl⟩ := mem_bruhatCell.1 hw
    have hn : canonicalRep (coxeterSystem Tag.F4) K w ∈ A := by
      have := mul_mem (mul_mem (inv_mem (hB hb)) hg) (inv_mem (hB hb'))
      simpa [mul_assoc] using this
    obtain ⟨ω, hω, rfl⟩ := (coxeterSystem Tag.F4).exists_isReduced w
    have hconj : (borelGroup Tag.F4 K).map (MulAut.conj
        (canonicalRep (coxeterSystem Tag.F4) K
          ((coxeterSystem Tag.F4).wordProd ω))).toMonoidHom ≤ A := by
      rintro _ ⟨x, hx, rfl⟩
      exact mul_mem (mul_mem hn (hB hx)) (inv_mem hn)
    have hletters := reduced_word_borel_extraction Tag.F4 K A hB ω hω hconj
    have hwJ := wordProd_mem_parabolicWeylGroup
      (J := {i | weylElt Tag.F4 K i 1 ∈ A}) hletters
    exact bruhatCell_subset_parabolicSubgroup hwJ hw
  · rintro _ ⟨i, hi, rfl⟩
    exact hi

private theorem f4_borel_overgroup_classification :
    (∀ A : Subgroup (ModGL Tag.F4 K), borelGroup Tag.F4 K ≤ A →
      A ≤ adjointGroup Tag.F4 K →
      A = parabolicSubgroup Tag.F4 K {i | weylElt Tag.F4 K i 1 ∈ A}) ∧
    ∀ A : Subgroup (ModGL Tag.F4 K), borelGroup Tag.F4 K ≤ A →
      A ≤ adjointGroup Tag.F4 K →
      ∃! J : Set (Fin Tag.F4.rank), A = parabolicSubgroup Tag.F4 K J := by
  refine ⟨fun A hB hA => f4_eq_parabolicSubgroup_of_borelGroup_le hB hA,
    fun A hB hA => ⟨_, f4_eq_parabolicSubgroup_of_borelGroup_le hB hA, fun J hJ => ?_⟩⟩
  ext i
  rw [Set.mem_ofPred_eq, hJ, f4_weylElt_mem_parabolicSubgroup_iff]

private theorem f4_borelGroup_covBy_iff {A : Subgroup (ModGL Tag.F4 K)}
    (hA : A ≤ adjointGroup Tag.F4 K) :
    borelGroup Tag.F4 K ⋖ A ↔ ∃ i, A = parabolicSubgroup Tag.F4 K {i} := by
  have hclass := (f4_borel_overgroup_classification (K := K)).2
  constructor
  · rintro ⟨hlt, hmin⟩
    obtain ⟨J, hJ, -⟩ := hclass A hlt.le hA
    obtain ⟨i, hi⟩ := f4_nonempty_of_borelGroup_lt (hJ ▸ hlt)
    refine ⟨i, ?_⟩
    have hle : parabolicSubgroup Tag.F4 K {i} ≤ A := hJ ▸
      f4_parabolicSubgroup_le_parabolicSubgroup_iff.2 (Set.singleton_subset_iff.2 hi)
    by_contra hne
    exact hmin (f4_borelGroup_lt_parabolicSubgroup (Set.singleton_nonempty i))
      (lt_of_le_of_ne hle fun h => hne h.symm)
  · rintro ⟨i, rfl⟩
    refine ⟨f4_borelGroup_lt_parabolicSubgroup (Set.singleton_nonempty i),
      fun A' hBA' hA'P => ?_⟩
    obtain ⟨J', hJ', -⟩ := hclass A' hBA'.le (hA'P.le.trans hA)
    have hsub : J' ⊆ {i} :=
      f4_parabolicSubgroup_le_parabolicSubgroup_iff.1 (hJ' ▸ hA'P.le)
    obtain ⟨j, hj⟩ := f4_nonempty_of_borelGroup_lt (hJ' ▸ hBA')
    have hJ'i : J' = {i} := Set.Subset.antisymm hsub (Set.singleton_subset_iff.2 (by
      have := hsub hj
      rw [Set.mem_singleton_iff] at this
      exact this ▸ hj))
    rw [hJ', hJ'i] at hA'P
    exact lt_irrefl _ hA'P

private theorem f4_parabolicSubgroup_singleton_inf_negUnipotent (i : Fin Tag.F4.rank) :
    parabolicSubgroup Tag.F4 K {i} ⊓ negUnipotent Tag.F4 K =
      rootSubgroup Tag.F4 K (-Pi.single i 1) := by
  refine le_antisymm (fun v hv => ?_) fun v hv => ?_
  · obtain ⟨hvP, hvV⟩ := Subgroup.mem_inf.1 hv
    rw [← SetLike.mem_coe, coe_rootSubgroup_neg_single]
    have hvP' : v ∈ (parabolicSubgroup Tag.F4 K {i} : Set (ModGL Tag.F4 K)) := hvP
    rw [(f4_standard_parabolic_cells_basic (K := K)).1] at hvP'
    obtain ⟨w, hw, hvw⟩ := Set.mem_iUnion₂.1 hvP'
    rcases mem_parabolicWeylGroup_singleton hw with rfl | rfl
    · obtain ⟨b, hb, b', hb', hbb⟩ := mem_bruhatCell.1 hvw
      rw [canonicalRep_one, mul_one] at hbb
      have hvB : v ∈ borelGroup Tag.F4 K := hbb ▸ mul_mem hb hb'
      have : v ∈ borelGroup Tag.F4 K ⊓ negUnipotent Tag.F4 K := Subgroup.mem_inf.2 ⟨hvB, hvV⟩
      rw [borelGroup_inf_negUnipotent, Subgroup.mem_bot] at this
      exact ⟨0, by rw [yUnit_zero, this]⟩
    · obtain ⟨⟨b, u⟩, ⟨hb, hu⟩, rfl⟩ :=
        (f4_bijOn_bruhatCell (K := K) (simple Tag.F4 i)).surjOn hvw
      rw [inversionSet_simple, rootSpan_singleton, coe_rootSubgroup_single] at hu
      obtain ⟨c, rfl⟩ := hu
      simp only [canonicalRep_simple] at hvV ⊢
      by_cases hc : c = 0
      · rw [hc, xUnit_zero, mul_one] at hvV
        exact absurd hvV (mul_weylElt_not_mem_negUnipotent i hb)
      · obtain ⟨b', hb', hb'eq⟩ := (simple_rank_one_bruhat_identity Tag.F4 K).2 K i c hc
        rw [mul_assoc, hb'eq, ← mul_assoc] at hvV ⊢
        have hbb : b * b' ∈ borelGroup Tag.F4 K ⊓ negUnipotent Tag.F4 K := by
          refine Subgroup.mem_inf.2 ⟨mul_mem hb hb', ?_⟩
          have := mul_mem hvV (inv_mem (yUnit_mem_negUnipotent (K := K) i c⁻¹))
          rwa [mul_inv_cancel_right] at this
        rw [borelGroup_inf_negUnipotent, Subgroup.mem_bot] at hbb
        exact ⟨c⁻¹, by rw [hbb, one_mul]⟩
  · rw [← SetLike.mem_coe, coe_rootSubgroup_neg_single] at hv
    obtain ⟨c, rfl⟩ := hv
    exact Subgroup.mem_inf.2 ⟨yUnit_mem_parabolicSubgroup i c, yUnit_mem_negUnipotent i c⟩

private theorem f4_parabolicSubgroup_singleton_eq (i : Fin Tag.F4.rank) :
    parabolicSubgroup Tag.F4 K {i} = borelGroup Tag.F4 K ⊔
      rootSubgroup Tag.F4 K (-Pi.single i 1) := by
  refine le_antisymm (sup_le le_sup_left ((Subgroup.closure_le _).2 ?_))
    (sup_le (borelGroup_le_parabolicSubgroup _) ?_)
  · rintro _ ⟨j, hj, rfl⟩
    rw [Set.mem_singleton_iff] at hj
    subst hj
    change weylElt Tag.F4 K j 1 ∈ _
    rw [weylElt_eq_yUnit_mul]
    have hy : yUnit Tag.F4 K j (-1) ∈ borelGroup Tag.F4 K ⊔
        rootSubgroup Tag.F4 K (-Pi.single j 1) :=
      Subgroup.mem_sup_right (by
        rw [← SetLike.mem_coe, coe_rootSubgroup_neg_single]
        exact ⟨_, rfl⟩)
    exact mul_mem (mul_mem hy (Subgroup.mem_sup_left (xUnit_mem_borelGroup j 1))) hy
  · rw [← f4_parabolicSubgroup_singleton_inf_negUnipotent]
    exact inf_le_left

private theorem f4_exceptional_ordinary_minimal_Borel_intersections :
    (∀ A : Subgroup (ModGL Tag.F4 K), A ≤ adjointGroup Tag.F4 K →
      (borelGroup Tag.F4 K ⋖ A ↔ ∃ i, A = parabolicSubgroup Tag.F4 K {i})) ∧
    Function.Injective (fun i : Fin Tag.F4.rank => parabolicSubgroup Tag.F4 K {i}) ∧
    (∀ i, ((parabolicSubgroup Tag.F4 K {i} ⊓ negUnipotent Tag.F4 K : Subgroup (ModGL Tag.F4 K)) :
      Set (ModGL Tag.F4 K)) = Set.range (yUnit Tag.F4 K i)) ∧
    (∀ A : Subgroup (ModGL Tag.F4 K), A ≤ adjointGroup Tag.F4 K →
      (oppositeBorel Tag.F4 K ⋖ A ↔ ∃ i, A = oppositeMinimalParabolic Tag.F4 K i)) ∧
    Function.Injective (oppositeMinimalParabolic Tag.F4 K) ∧
    ∀ i, ((oppositeMinimalParabolic Tag.F4 K i ⊓ posUnipotent Tag.F4 K :
      Subgroup (ModGL Tag.F4 K)) : Set (ModGL Tag.F4 K)) = Set.range (xUnit Tag.F4 K i) := by
  have hPinj : Function.Injective (fun i : Fin Tag.F4.rank => parabolicSubgroup Tag.F4 K {i}) :=
    fun i j h => Set.singleton_injective (f4_parabolicSubgroup_injective h)
  obtain ⟨n₀, δ, hn₀, hδδ, hB, hV, hY⟩ := exists_opposite_data Tag.F4 K
  set φ : ModGL Tag.F4 K →* ModGL Tag.F4 K := (MulAut.conj n₀).toMonoidHom with hφ
  have hφinj : Function.Injective φ := (MulAut.conj n₀).injective
  have hφsurj : Function.Surjective φ := (MulAut.conj n₀).surjective
  have hP : ∀ i, (parabolicSubgroup Tag.F4 K {i}).map φ =
      oppositeMinimalParabolic Tag.F4 K (δ i) := fun i => by
    rw [f4_parabolicSubgroup_singleton_eq, Subgroup.map_sup, hB, hY,
      oppositeMinimalParabolic, rootSubgroup_single_eq_closure]
  have hQ : ∀ j, oppositeMinimalParabolic Tag.F4 K j =
      (parabolicSubgroup Tag.F4 K {δ j}).map φ :=
    fun j => by rw [hP, hδδ]
  refine ⟨fun A hA => f4_borelGroup_covBy_iff hA, hPinj, fun i => ?_, fun A hA => ?_,
    fun j k h => ?_, fun j => ?_⟩
  · rw [f4_parabolicSubgroup_singleton_inf_negUnipotent, coe_rootSubgroup_neg_single]
  · have hAc : (A.comap φ).map φ = A :=
      Subgroup.map_comap_eq_self_of_surjective hφsurj A
    have hAcC : A.comap φ ≤ adjointGroup Tag.F4 K := fun x hx => by
      have h1 : n₀ * x * n₀⁻¹ ∈ adjointGroup Tag.F4 K := hA hx
      have h2 := mul_mem (mul_mem (inv_mem hn₀) h1) hn₀
      simpa [mul_assoc] using h2
    rw [← hB, ← hAc, covBy_map_conj_iff, f4_borelGroup_covBy_iff hAcC]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨δ i, by rw [hi, hP]⟩
    · rintro ⟨j, hj⟩
      refine ⟨δ j, Subgroup.map_injective hφinj ?_⟩
      rw [hj, hQ]
  · rw [hQ, hQ] at h
    have := hPinj (Subgroup.map_injective hφinj h)
    rw [← hδδ j, ← hδδ k]
    exact congrArg δ this
  · rw [hQ, ← hV, ← Subgroup.map_inf_eq _ _ φ hφinj,
      f4_parabolicSubgroup_singleton_inf_negUnipotent, hY, hδδ, coe_rootSubgroup_single]


end F4SimplePairExtraction

open F4SimplePairExtraction

public theorem f4_exists_perm_map_simple {β : MulAut (adjointGroup Tag.F4 K)}
    (hβ : β ∈ unipotentPairAut Tag.F4 K) :
    ∃ π : Equiv.Perm (Fin Tag.F4.rank), ∀ i,
      (simplePosSubgroup Tag.F4 K i).map β.toMonoidHom = simplePosSubgroup Tag.F4 K (π i) ∧
      (simpleNegSubgroup Tag.F4 K i).map β.toMonoidHom = simpleNegSubgroup Tag.F4 K (π i) := by
  obtain ⟨hcov, hPinj, hPV, hcov', -, hQU⟩ :=
    f4_exceptional_ordinary_minimal_Borel_intersections (K := K)
  obtain ⟨π, hπ⟩ := exists_perm_map_eq (G := ModGL Tag.F4 K) (C := adjointGroup Tag.F4 K)
    (U := posUnipotent Tag.F4 K) (V := negUnipotent Tag.F4 K) (B := borelGroup Tag.F4 K)
    (B' := oppositeBorel Tag.F4 K) (P := fun i => parabolicSubgroup Tag.F4 K {i})
    (Q := oppositeMinimalParabolic Tag.F4 K) (X := fun i => rootSubgroup Tag.F4 K (Pi.single i 1))
    (Y := fun i => rootSubgroup Tag.F4 K (-Pi.single i 1)) borelGroup_le_adjointGroup'
    oppositeBorel_le_adjointGroup (fun i => parabolicSubgroup_le_adjointGroup Tag.F4 K {i})
    oppositeMinimalParabolic_le_adjointGroup posUnipotent_le_adjointGroup
    negUnipotent_le_adjointGroup (fun i => rootSubgroup_le_adjointGroup _)
    (fun i => rootSubgroup_le_adjointGroup _) hcov hcov' hPinj
    (f4_borel_self_normalizers (K := K)).1
    (f4_oppositeBorel_normalizer (K := K))
    (fun i => SetLike.coe_injective ((hPV i).trans (coe_rootSubgroup_neg_single i).symm))
    (fun i => SetLike.coe_injective ((hQU i).trans (coe_rootSubgroup_single i).symm))
    (fun a b hab x hx y hy => by
      rw [← SetLike.mem_coe, coe_rootSubgroup_single] at hx
      rw [← SetLike.mem_coe, coe_rootSubgroup_neg_single] at hy
      obtain ⟨c, rfl⟩ := hx
      obtain ⟨d, rfl⟩ := hy
      exact f4_commute_xUnit_yUnit_of_ne' hab c d)
    (fun a => ⟨_, mem_rootSubgroup.2 ⟨1, by rw [pinnedX_single]⟩, _,
      mem_rootSubgroup.2 ⟨1, by rw [pinnedX_neg_single]⟩, not_commute_xUnit_yUnit a⟩) hβ.1 hβ.2
  refine ⟨π, fun i => ?_⟩
  have := hπ i
  simp only [subgroupOf_rootSubgroup_single, subgroupOf_rootSubgroup_neg_single] at this
  exact this


open CFSG.StandardType.F4ExplicitPos.BruhatUnique
open CFSG.StandardType.F4ExplicitPos.BruhatNo117
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Pointwise

private theorem f4_card_negUnipotent {w₀ : WeylGroup Tag.F4}
    (hw₀ : ∀ w, (coxeterSystem Tag.F4).length w ≤ (coxeterSystem Tag.F4).length w₀) :
    Nat.card (negUnipotent Tag.F4 K) =
      Nat.card K ^ {α : Fin Tag.F4.rank → ℤ | IsRoot Tag.F4 α ∧ 0 < height α}.ncard := by
  rw [← map_conj_canonicalRep_longest (K := K) hw₀,
    Subgroup.card_map_of_injective (MulAut.conj _).injective,
    f4_card_posUnipotent]

private theorem f4_isPGroup_and_not_dvd_index [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p]
    {X : Subgroup (ModGL Tag.F4 K)} (hXC : X ≤ adjointGroup Tag.F4 K)
    (hX : Nat.card X =
      Nat.card K ^ {α : Fin Tag.F4.rank → ℤ | IsRoot Tag.F4 α ∧ 0 < height α}.ncard) :
    IsPGroup p (X.subgroupOf (adjointGroup Tag.F4 K)) ∧
      ¬ p ∣ (X.subgroupOf (adjointGroup Tag.F4 K)).index := by
  have : Fintype K := Fintype.ofFinite K
  have := finite_modGL (τ := Tag.F4) (K := K)
  obtain ⟨n, -, hcard⟩ := FiniteField.card K p
  have hqcard : Nat.card K = p ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  set N := {α : Fin Tag.F4.rank → ℤ | IsRoot Tag.F4 α ∧ 0 < height α}.ncard
  have hXs : Nat.card (X.subgroupOf (adjointGroup Tag.F4 K)) = Nat.card K ^ N := by
    rw [card_subgroupOf_of_le hXC, hX]
  refine ⟨IsPGroup.of_card (n := (n : ℕ) * N) (by rw [hXs, hqcard, ← pow_mul]),
    fun hdvd => ?_⟩
  have hmul := Subgroup.card_mul_index (X.subgroupOf (adjointGroup Tag.F4 K))
  rw [hXs, f4_card_adjointGroup, mul_comm (Nat.card (torusGroup Tag.F4 K)),
    mul_assoc] at hmul
  have hpos : 0 < Nat.card K ^ N := pow_pos Nat.card_pos N
  have hidx := Nat.eq_of_mul_eq_mul_left hpos hmul
  rw [hidx] at hdvd
  rcases (Nat.Prime.dvd_mul Fact.out).1 hdvd with h | h
  · exact not_dvd_card_torusGroup p h
  · exact not_dvd_sum_length p h

public theorem f4_exists_conj_mul_unipotentPair [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (w₀ : WeylGroup Tag.F4)
    (hw₀ : ∀ w, (coxeterSystem Tag.F4).length w ≤ (coxeterSystem Tag.F4).length w₀)
    (α : MulAut (adjointGroup Tag.F4 K)) :
    ∃ (c : adjointGroup Tag.F4 K) (β : MulAut (adjointGroup Tag.F4 K)),
      β ∈ unipotentPairAut Tag.F4 K ∧ α = MulAut.conj c * β := by
  have hBC : borelGroup Tag.F4 K ≤ adjointGroup Tag.F4 K :=
    ((triangular_borel_structure.{0, 0} Tag.F4 K).2.2.2.2.2.2.2.2.2.2.2 K).1
  have hUC : posUnipotent Tag.F4 K ≤ adjointGroup Tag.F4 K := le_trans le_sup_right hBC
  have hn₀ := canonicalRep_mem_adjointGroup (coxeterSystem Tag.F4) K w₀
  have hVC : negUnipotent Tag.F4 K ≤ adjointGroup Tag.F4 K := by
    rw [← map_conj_canonicalRep_longest (K := K) hw₀]
    rintro _ ⟨u, hu, rfl⟩
    exact mul_mem (mul_mem hn₀ (hUC hu)) (inv_mem hn₀)
  obtain ⟨hUp, hUi⟩ := f4_isPGroup_and_not_dvd_index (K := K) p hUC
    (f4_card_posUnipotent (K := K))
  obtain ⟨hVp, hVi⟩ := f4_isPGroup_and_not_dvd_index (K := K) p hVC
    (f4_card_negUnipotent (K := K) hw₀)
  have hPU := IsPGroup.toSylow_coe hUp hUi
  have hPV := IsPGroup.toSylow_coe hVp hVi
  set PU : Sylow p (adjointGroup Tag.F4 K) := hUp.toSylow hUi
  set PV : Sylow p (adjointGroup Tag.F4 K) := hVp.toSylow hVi
  set UC := (posUnipotent Tag.F4 K).subgroupOf (adjointGroup Tag.F4 K) with hUCdef
  set VC := (negUnipotent Tag.F4 K).subgroupOf (adjointGroup Tag.F4 K) with hVCdef
  have hUV : UC ⊓ VC = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    have h : (x : ModGL Tag.F4 K) ∈ posUnipotent Tag.F4 K ⊓ negUnipotent Tag.F4 K :=
      Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hx).1, (Subgroup.mem_inf.1 hx).2⟩
    rw [posUnipotent_inf_negUnipotent, Subgroup.mem_bot] at h
    exact Subgroup.mem_bot.2 (Subtype.ext h)
  have hkey : ∀ S : Sylow p (adjointGroup Tag.F4 K), UC ⊓ S = ⊥ →
      ∃ u ∈ UC, (S : Subgroup (adjointGroup Tag.F4 K)) =
        VC.map (MulAut.conj u).toMonoidHom := by
    intro S hS
    obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (adjointGroup Tag.F4 K) PU S
    have hSc : (S : Subgroup (adjointGroup Tag.F4 K)) =
        UC.map (MulAut.conj c).toMonoidHom := by
      rw [← hc, coe_smul_sylow_eq_map, hPU]
    rw [hSc, map_conj_subgroupOf hUC] at hS ⊢
    have hamb : posUnipotent Tag.F4 K ⊓
        (posUnipotent Tag.F4 K).map (MulAut.conj (c : ModGL Tag.F4 K)).toMonoidHom = ⊥ := by
      refine eq_bot_iff.2 fun x hx => ?_
      have hxC : x ∈ adjointGroup Tag.F4 K := hUC (Subgroup.mem_inf.1 hx).1
      have h : (⟨x, hxC⟩ : adjointGroup Tag.F4 K) ∈ UC ⊓ ((posUnipotent Tag.F4 K).map
          (MulAut.conj (c : ModGL Tag.F4 K)).toMonoidHom).subgroupOf (adjointGroup Tag.F4 K) :=
        Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hx).1, (Subgroup.mem_inf.1 hx).2⟩
      rw [hS, Subgroup.mem_bot] at h
      exact Subgroup.mem_bot.2 (congrArg Subtype.val h)
    have hcell : (c : ModGL Tag.F4 K) ∈ ⋃ w, bruhatCell Tag.F4 K w := by
      rw [← f4_adjointGroup_eq_iUnion_bruhatCell]
      exact c.2
    obtain ⟨w, hcw⟩ := Set.mem_iUnion.1 hcell
    obtain rfl := (posUnipotent_inf_map_conj_eq_bot_iff (K := K) hw₀ hcw).1 hamb
    obtain ⟨b, hb, b', hb', hbb⟩ := mem_bruhatCell.1 hcw
    have hb'' : b ∈ (posUnipotent Tag.F4 K : Set (ModGL Tag.F4 K)) *
        (torusGroup Tag.F4 K : Set _) := by
      rw [← (triangular_borel_structure.{0, 0} Tag.F4 K).2.2.2.2.2.1]
      exact hb
    obtain ⟨u, hu, h, hh, rfl⟩ := hb''
    have hmapc : (posUnipotent Tag.F4 K).map (MulAut.conj (c : ModGL Tag.F4 K)).toMonoidHom =
        (negUnipotent Tag.F4 K).map (MulAut.conj u).toMonoidHom := by
      rw [← hbb, map_conj_mul, map_conj_mul, map_conj_posUnipotent_of_mem_borelGroup hb',
        map_conj_canonicalRep_longest hw₀, map_conj_mul,
        CFSG.LieType.Chevalley.map_conj_eq_of_mem_normalizer (torusGroup_le_normalizer_negUnipotent hh)]
    refine ⟨⟨u, hUC hu⟩, hu, ?_⟩
    rw [hmapc, map_conj_subgroupOf hVC]
  have hkey' : ∀ S : Sylow p (adjointGroup Tag.F4 K),
      (∃ u ∈ UC, (S : Subgroup (adjointGroup Tag.F4 K)) =
        VC.map (MulAut.conj u).toMonoidHom) → UC ⊓ S = ⊥ := by
    rintro S ⟨u, hu, hS⟩
    rw [hS, ← map_conj_self hu, ← Subgroup.map_inf_eq _ _ _ (MulAut.conj u).injective, hUV,
      Subgroup.map_bot]
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (adjointGroup Tag.F4 K) PU (α • PU)
  have hαU : UC.map α.toMonoidHom = UC.map (MulAut.conj c).toMonoidHom := by
    rw [← hPU, ← coe_mulAut_smul_sylow, ← coe_smul_sylow_eq_map, hc]
  set α₁ := (MulAut.conj c)⁻¹ * α with hα₁
  have hα₁U : UC.map α₁.toMonoidHom = UC := by
    rw [map_mulAut_mul, hαU, ← map_mulAut_mul, inv_mul_cancel, map_mulAut_one]
  have hS : UC ⊓ ((α₁ • PV : Sylow p (adjointGroup Tag.F4 K)) :
      Subgroup (adjointGroup Tag.F4 K)) = ⊥ := by
    rw [coe_mulAut_smul_sylow, hPV, ← hα₁U, ← Subgroup.map_inf_eq _ _ _ α₁.injective, hUV,
      Subgroup.map_bot]
  obtain ⟨u, hu, hu'⟩ := hkey _ hS
  rw [coe_mulAut_smul_sylow, hPV] at hu'
  refine ⟨c * u, (MulAut.conj u)⁻¹ * α₁, ⟨?_, ?_⟩, ?_⟩
  · rw [map_mulAut_mul, hα₁U, ← map_inv, map_conj_self (inv_mem hu)]
  · rw [map_mulAut_mul, hu', ← map_mulAut_mul, inv_mul_cancel, map_mulAut_one]
  · rw [hα₁, map_mul]
    group


end OriginalPair

end Public


end CFSG.LieType.Chevalley
