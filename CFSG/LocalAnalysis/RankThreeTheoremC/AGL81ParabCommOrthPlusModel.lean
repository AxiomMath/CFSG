module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommOrthPlusRes
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommOrthPlusFlag
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommLinModelMat
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthPlusData

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.OrthPlus

open Matrix QuadraticMap CFSG.AGLEmbedding.LeviBlock CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit CFSG.LieType.Universal.Spin
  CFSG.ClassicalGroups.Orthogonal
open scoped Pointwise commutatorElement
open CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm

variable {r : ℕ} {K : Type} [Field K]

theorem map_one_add_single {m : ℕ} (σ : K ≃+* K) (i j : Fin m) (t : K) :
    (1 + Matrix.single i j t : Matrix (Fin m) (Fin m) K).map σ =
      1 + Matrix.single i j (σ t) := by
  ext k l
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  split_ifs <;> simp

theorem map_rpMat {m : ℕ} (σ : K ≃+* K) (a b : Fin m ⊕ Fin m) :
    (rpMat K a b).map σ = rpMat K a b := by
  ext u v
  simp only [rpMat, Matrix.map_apply, Matrix.sub_apply, Matrix.single_apply]
  split_ifs <;> simp

variable [Finite K] [CharP K 2]

section Rel

variable (σ : K ≃+* K) {D : Finset ℕ} (hD : ∀ d ∈ D, d ≤ r) {h x g : GLV r K}
  (hh : h ∈ plusFlagStabO K r D) (hx : x ∈ plusFlagStabO K r D)
  (hgeq : g = h * fieldConj r K σ x * h⁻¹ * x⁻¹) (hg : g ∈ plusFlagStabO K r D)

include hgeq in
theorem plusEBlockHomO_rel {b : ℕ} (hb : b ∈ D)
    (h1 : plusEBlockHomO hD hb ⟨g, hg⟩ = 1) :
    ((plusEBlockHomO hD hb ⟨h, hh⟩ : GL (Fin (b - predCut D b)) K) :
        Matrix (Fin (b - predCut D b)) (Fin (b - predCut D b)) K) *
      ((plusEBlockHomO hD hb ⟨x, hx⟩ : GL (Fin (b - predCut D b)) K) :
        Matrix (Fin (b - predCut D b)) (Fin (b - predCut D b)) K).map σ =
    ((plusEBlockHomO hD hb ⟨x, hx⟩ : GL (Fin (b - predCut D b)) K) :
        Matrix (Fin (b - predCut D b)) (Fin (b - predCut D b)) K) *
      ((plusEBlockHomO hD hb ⟨h, hh⟩ : GL (Fin (b - predCut D b)) K) :
        Matrix (Fin (b - predCut D b)) (Fin (b - predCut D b)) K) := by
  have hxσ := fieldConj_mem_plusFlagStabO σ hD hx
  have hu : (⟨g, hg⟩ : ↥(plusFlagStabO K r D)) =
      ⟨h, hh⟩ * ⟨fieldConj r K σ x, hxσ⟩ * ⟨h, hh⟩⁻¹ * ⟨x, hx⟩⁻¹ := Subtype.ext hgeq
  rw [hu, map_mul, map_mul, map_mul, map_inv, map_inv] at h1
  have h2 : plusEBlockHomO hD hb ⟨h, hh⟩ * plusEBlockHomO hD hb ⟨fieldConj r K σ x, hxσ⟩ =
      plusEBlockHomO hD hb ⟨x, hx⟩ * plusEBlockHomO hD hb ⟨h, hh⟩ := by
    rw [mul_inv_eq_one] at h1
    exact mul_inv_eq_iff_eq_mul.1 h1
  have h3 := congrArg (fun u : GL (Fin (b - predCut D b)) K =>
    (u : Matrix (Fin (b - predCut D b)) (Fin (b - predCut D b)) K)) h2
  simp only [Units.val_mul] at h3
  rw [plusEBlockHomO_fieldConj σ hD hb x hx] at h3
  exact h3

include hgeq in
theorem plusResBlockHomO_rel {t m : ℕ} (ht : t = 0 ∨ t ∈ D) (htm : t + m = r)
    (h1 : plusResBlockHomO hD ht htm ⟨g, hg⟩ = 1) :
    ((plusResBlockHomO hD ht htm ⟨h, hh⟩ : GL (Fin m ⊕ Fin m) K) :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *
      ((plusResBlockHomO hD ht htm ⟨x, hx⟩ : GL (Fin m ⊕ Fin m) K) :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K).map σ =
    ((plusResBlockHomO hD ht htm ⟨x, hx⟩ : GL (Fin m ⊕ Fin m) K) :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *
      ((plusResBlockHomO hD ht htm ⟨h, hh⟩ : GL (Fin m ⊕ Fin m) K) :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) := by
  have hxσ := fieldConj_mem_plusFlagStabO σ hD hx
  have hu : (⟨g, hg⟩ : ↥(plusFlagStabO K r D)) =
      ⟨h, hh⟩ * ⟨fieldConj r K σ x, hxσ⟩ * ⟨h, hh⟩⁻¹ * ⟨x, hx⟩⁻¹ := Subtype.ext hgeq
  rw [hu, map_mul, map_mul, map_mul, map_inv, map_inv] at h1
  have h2 : plusResBlockHomO hD ht htm ⟨h, hh⟩ *
      plusResBlockHomO hD ht htm ⟨fieldConj r K σ x, hxσ⟩ =
      plusResBlockHomO hD ht htm ⟨x, hx⟩ * plusResBlockHomO hD ht htm ⟨h, hh⟩ := by
    rw [mul_inv_eq_one] at h1
    exact mul_inv_eq_iff_eq_mul.1 h1
  have h3 := congrArg (fun u : GL (Fin m ⊕ Fin m) K =>
    (u : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)) h2
  simp only [Units.val_mul] at h3
  rw [plusResBlockHomO_fieldConj σ hD ht htm x hx] at h3
  exact h3

end Rel

theorem plusResIdx_swap {t m : ℕ} (htm : t + m = r) (a : Fin m ⊕ Fin m) :
    plusResIdx htm a.swap = (plusResIdx htm a).swap := by
  rcases a with s | s <;> rfl

theorem coordIdx_plusResIdx {t m : ℕ} (htm : t + m = r) (a : Fin m ⊕ Fin m) :
    (coordIdx (plusResIdx htm a)).val = t + (coordIdx a).val := by
  rcases a with s | s <;> rfl

theorem plusResExt_rpElt {t m : ℕ} (htm : t + m = r) {a b : Fin m ⊕ Fin m}
    (hab : coordIdx a ≠ coordIdx b) (s : K) :
    plusResExt K htm (rpElt a b s) = rpElt (plusResIdx htm a) (plusResIdx htm b) s := by
  have hab' : coordIdx (plusResIdx htm a) ≠ coordIdx (plusResIdx htm b) := by
    intro h
    apply hab
    apply Fin.ext
    have := congrArg Fin.val h
    rw [coordIdx_plusResIdx, coordIdx_plusResIdx] at this
    omega
  apply autMat_injective
  rw [autMat_plusResExt, autMat_rpElt hab, autMat_rpElt hab']
  ext u v
  by_cases hboth : u ∈ Set.range (plusResIdx htm) ∧ v ∈ Set.range (plusResIdx htm)
  · obtain ⟨⟨u', rfl⟩, ⟨v', rfl⟩⟩ := hboth
    rw [extendMat_apply_map]
    simp only [Matrix.add_apply, Matrix.smul_apply, rpMat, Matrix.sub_apply, Matrix.single_apply,
      Matrix.one_apply, ← plusResIdx_swap, (plusResIdx_injective htm).eq_iff]
  · have hnot : u ∉ Set.range (plusResIdx htm) ∨ v ∉ Set.range (plusResIdx htm) := by
      by_contra hc
      exact hboth ⟨not_not.1 (fun h => hc (Or.inl h)), not_not.1 (fun h => hc (Or.inr h))⟩
    rw [extendMat_apply_of_not_mem _ _ hnot]
    have h1 : Matrix.single (plusResIdx htm a) (plusResIdx htm b) (1 : K) u v = 0 := by
      rw [Matrix.single_apply, if_neg]
      rintro ⟨h1, h2⟩
      rcases hnot with hu | hv
      · exact hu ⟨a, h1⟩
      · exact hv ⟨b, h2⟩
    have h2 : Matrix.single (plusResIdx htm b).swap (plusResIdx htm a).swap (1 : K) u v = 0 := by
      rw [Matrix.single_apply, if_neg]
      rintro ⟨h1, h2⟩
      rcases hnot with hu | hv
      · exact hu ⟨b.swap, by rw [plusResIdx_swap, h1]⟩
      · exact hv ⟨a.swap, by rw [plusResIdx_swap, h2]⟩
    simp only [Matrix.add_apply, Matrix.smul_apply, rpMat, Matrix.sub_apply, h1, h2, sub_zero,
      smul_zero, add_zero]

theorem plusResExt_rpElt_mem {D : Finset ℕ} {t m : ℕ} (htm : t + m = r)
    (hDt : ∀ d ∈ D, d ≤ t) {a b : Fin m ⊕ Fin m} (hab : coordIdx a ≠ coordIdx b) (s : K) :
    plusResExt K htm (rpElt a b s) ∈ plusFlagStab K r D :=
  plusResExt_mem_plusFlagStab_of_mem htm hDt (by
    rw [plusResExt_rpElt htm hab s]
    exact eichler_mem_elementaryGroup _ _ _)

theorem coe_plusResBlockHom_plusResExt {D : Finset ℕ} (hD : ∀ d ∈ D, d ≤ r) {t m : ℕ}
    (ht : t = 0 ∨ t ∈ D) (htm : t + m = r) (h : GLV m K)
    (hq : plusResExt K htm h ∈ plusFlagStab K r D) :
    ((plusResBlockHom hD ht htm ⟨plusResExt K htm h, hq⟩ : GL (Fin m ⊕ Fin m) K) :
      Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) = autMat h := by
  rw [coe_plusResBlockHom]
  change (autMat (plusResExt K htm h)).submatrix _ _ = _
  rw [autMat_plusResExt, submatrix_extendMat]

theorem map_one_add_smul_rpMat {m : ℕ} (σ : K ≃+* K) (a b : Fin m ⊕ Fin m) (s : K) :
    (1 + s • rpMat K a b : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K).map σ =
      1 + σ s • rpMat K a b := by
  have hN := fun u v => congrFun (congrFun (map_rpMat σ a b) u) v
  ext u v
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add,
    map_mul, Matrix.one_apply, apply_ite σ, map_one, map_zero]
  have := hN u v
  rw [Matrix.map_apply] at this
  rw [this]

section Blocks

variable (hr : 3 ≤ r) {D : Finset ℕ} (hD : ∀ d ∈ D, d ≤ r) {t m : ℕ}
  (ht : t = 0 ∨ t ∈ D) (htm : t + m = r)

include hr in
theorem gl_block {α : MulAut ↥(orthElementaryGroup (quadPlus r K))}
    (hNF : NormFix hD ht htm α) {h : GLV r K} {σ : K ≃+* K}
    (hα : ∀ x : ↥(orthElementaryGroup (quadPlus r K)),
      ((α x : ↥(orthElementaryGroup (quadPlus r K))) : GLV r K) = h * fieldConj r K σ x * h⁻¹)
    (hh : h ∈ plusFlagStabO K r D) {b : ℕ} (hb : b ∈ D) (hk : 2 ≤ b - predCut D b) :
    (∀ s : K, σ s = s) ∧ ∃ c : K,
      ((plusEBlockHomO hD hb ⟨h, hh⟩ : GL (Fin (b - predCut D b)) K) :
        Matrix (Fin (b - predCut D b)) (Fin (b - predCut D b)) K) = c • 1 := by
  set B := plusEBlockHomO hD hb ⟨h, hh⟩ with hB
  have hrel : ∀ i j : Fin (b - predCut D b), i ≠ j → ∀ s : K, ∃ c : K,
      (B : Matrix (Fin (b - predCut D b)) (Fin (b - predCut D b)) K) *
        (1 + Matrix.single i j (σ s)) = c • ((1 + Matrix.single i j s) *
          (B : Matrix (Fin (b - predCut D b)) (Fin (b - predCut D b)) K)) := by
    intro i j hij s
    refine ⟨1, ?_⟩
    rw [one_smul]
    set A := Matrix.SpecialLinearGroup.transvection hij s with hA
    have hq : plusFlagLevi K (hD b hb) (Matrix.SpecialLinearGroup.toGL A) ∈
        plusFlagStab K r D := plusFlagLevi_mem_plusFlagStab hr hD hb _
    obtain ⟨hg, hb1, -⟩ := hNF.block ⟨_, hq⟩ b hb A hk rfl
    have hgeq : autQ α ⟨_, hq⟩ * (plusFlagLevi K (hD b hb) (Matrix.SpecialLinearGroup.toGL A))⁻¹ =
        h * fieldConj r K σ (plusFlagLevi K (hD b hb) (Matrix.SpecialLinearGroup.toGL A)) * h⁻¹ *
          (plusFlagLevi K (hD b hb) (Matrix.SpecialLinearGroup.toGL A))⁻¹ := by
      rw [show autQ α ⟨_, hq⟩ = h * fieldConj r K σ
        (plusFlagLevi K (hD b hb) (Matrix.SpecialLinearGroup.toGL A)) * h⁻¹ from hα _]
    have h0 := plusEBlockHomO_rel σ hD hh (plusFlagStab_le_plusFlagStabO D hq) hgeq
      (plusFlagStab_le_plusFlagStabO D hg) hb (hb1 b hb)
    have hblk : plusEBlockHomO hD hb ⟨_, plusFlagStab_le_plusFlagStabO D hq⟩ =
        Matrix.SpecialLinearGroup.toGL A := plusEBlockHom_plusFlagLevi_self hr hD hb _
    rw [hblk] at h0
    have hAm : ((Matrix.SpecialLinearGroup.toGL A : GL (Fin (b - predCut D b)) K) :
        Matrix (Fin (b - predCut D b)) (Fin (b - predCut D b)) K) = 1 + Matrix.single i j s := by
      change ((A : Matrix.SpecialLinearGroup (Fin (b - predCut D b)) K) :
        Matrix (Fin (b - predCut D b)) (Fin (b - predCut D b)) K) = _
      rw [hA, Matrix.SpecialLinearGroup.transvection_coe]
    rw [hAm, map_one_add_single] at h0
    exact h0
  have hBB' : ((B⁻¹ : GL (Fin (b - predCut D b)) K) :
      Matrix (Fin (b - predCut D b)) (Fin (b - predCut D b)) K) *
      (B : Matrix (Fin (b - predCut D b)) (Fin (b - predCut D b)) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  obtain ⟨hσ, c, -, hc⟩ := Lin.eq_scalar_of_transvection_rel hk (σ : K →+* K) hBB' hrel
  exact ⟨fun s => hσ s, c, hc⟩

include hr in
theorem res_block (hDt : ∀ d ∈ D, d ≤ t) (hm : 2 ≤ m)
    {α : MulAut ↥(orthElementaryGroup (quadPlus r K))}
    (hNF : NormFix hD ht htm α) {h : GLV r K} {σ : K ≃+* K}
    (hα : ∀ x : ↥(orthElementaryGroup (quadPlus r K)),
      ((α x : ↥(orthElementaryGroup (quadPlus r K))) : GLV r K) = h * fieldConj r K σ x * h⁻¹)
    (hh : h ∈ plusFlagStabO K r D) :
    (∀ s : K, σ s = s) ∧ ∃ c : K,
      ((plusResBlockHomO hD ht htm ⟨h, hh⟩ : GL (Fin m ⊕ Fin m) K) :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) = c • 1 := by
  set R := plusResBlockHomO hD ht htm ⟨h, hh⟩ with hR
  have hrel : ∀ a b : Fin m ⊕ Fin m, coordIdx a ≠ coordIdx b → ∀ s : K,
      (R : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) * (1 + σ s • rpMat K a b) =
        (1 + s • rpMat K a b) * (R : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) := by
    intro a b hab s
    have hq : plusResExt K htm (rpElt a b s) ∈ plusFlagStab K r D :=
      plusResExt_rpElt_mem htm hDt hab s
    obtain ⟨hg, -, hres⟩ := hNF.res hm ⟨_, hq⟩ a b s hab rfl
    have hgeq : autQ α ⟨_, hq⟩ * (plusResExt K htm (rpElt a b s))⁻¹ =
        h * fieldConj r K σ (plusResExt K htm (rpElt a b s)) * h⁻¹ *
          (plusResExt K htm (rpElt a b s))⁻¹ := by
      rw [show autQ α ⟨_, hq⟩ = h * fieldConj r K σ (plusResExt K htm (rpElt a b s)) * h⁻¹ from
        hα _]
    have h0 := plusResBlockHomO_rel σ hD hh (plusFlagStab_le_plusFlagStabO D hq) hgeq
      (plusFlagStab_le_plusFlagStabO D hg) ht htm hres
    have hblk : ((plusResBlockHomO hD ht htm ⟨_, plusFlagStab_le_plusFlagStabO D hq⟩ :
        GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) =
        1 + s • rpMat K a b := by
      rw [← autMat_rpElt hab]
      exact coe_plusResBlockHom_plusResExt hD ht htm _ hq
    rw [hblk, map_one_add_smul_rpMat] at h0
    exact h0
  have hHG : ((R⁻¹ : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *
      (R : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  obtain ⟨hσ, c, hc⟩ := eq_of_rel_rpMat hm (σ : K →+* K) _ _ hHG hrel
  exact ⟨fun s => hσ s, c, hc⟩

end Blocks

theorem gl_mul_comm_of_lt_two {k : ℕ} (hk : k < 2) (g h : GL (Fin k) K) : g * h = h * g := by
  rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
  · exact Subsingleton.elim _ _
  · apply Units.ext
    ext i j
    have hi : i = 0 := Subsingleton.elim _ _
    have hj : j = 0 := Subsingleton.elim _ _
    subst hi hj
    simp [Matrix.mul_apply, mul_comm]

theorem gl_subsingleton_zero : Subsingleton (GL (Fin 0 ⊕ Fin 0) K) :=
  ⟨fun g h => Units.ext (Matrix.ext fun i => by rcases i with i | i <;> exact i.elim0)⟩

theorem mem_center_of_eq_smul_one {ι : Type} [Fintype ι] [DecidableEq ι] {z : GL ι K} {c : K}
    (hz : (z : Matrix ι ι K) = c • 1) : z ∈ Subgroup.center (GL ι K) := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hz, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    Matrix.one_mul]

theorem sup_id_eq {D : Finset ℕ} {t : ℕ} (ht : t = 0 ∨ t ∈ D) (hDt : ∀ d ∈ D, d ≤ t) :
    D.sup id = t := by
  refine le_antisymm (Finset.sup_le hDt) ?_
  rcases ht with rfl | ht
  · exact Nat.zero_le _
  · exact Finset.le_sup (f := id) ht

theorem eq_zero_or_two_le {D : Finset ℕ} (hr : 3 ≤ r) (hD1 : r - 1 ∈ D → r ∈ D) {t m : ℕ}
    (ht : t = 0 ∨ t ∈ D) (hDt : ∀ d ∈ D, d ≤ t) (htm : t + m = r) : m = 0 ∨ 2 ≤ m := by
  by_contra hcon
  have hm1 : m = 1 := by omega
  have htr : t = r - 1 := by omega
  rcases ht with h0 | hmem
  · omega
  · have := hDt r (hD1 (htr ▸ hmem))
    omega

theorem exists_data (hr : 3 ≤ r) {D : Finset ℕ} (hD : ∀ d ∈ D, 1 ≤ d ∧ d ≤ r) {t m : ℕ}
    (ht : t = 0 ∨ t ∈ D) (hDt : ∀ d ∈ D, d ≤ t) (htm : t + m = r) (hm : m = 0 ∨ 2 ≤ m)
    (hblk : (∃ b ∈ D, 2 ≤ b - predCut D b) ∨ 2 ≤ m)
    {α : MulAut ↥(orthElementaryGroup (quadPlus r K))} (hs : IsSemilinear α)
    (hodd : Odd (orderOf α)) (hNF : NormFix (fun d hd => (hD d hd).2) ht htm α) :
    ∃ (h : GLV r K) (hh : h ∈ plusFlagStabO K r D),
      (∀ x : ↥(orthElementaryGroup (quadPlus r K)),
        ((α x : ↥(orthElementaryGroup (quadPlus r K))) : GLV r K) = h * x * h⁻¹) ∧
      (∀ (b : ℕ) (hb : b ∈ D),
        plusEBlockHomO (fun d hd => (hD d hd).2) hb ⟨h, hh⟩ ∈
          Subgroup.center (GL (Fin (b - predCut D b)) K)) ∧
      plusResBlockHomO (fun d hd => (hD d hd).2) ht htm ⟨h, hh⟩ ∈
        Subgroup.center (GL (Fin m ⊕ Fin m) K) := by
  obtain ⟨h, σ, hO, hα⟩ := hs
  have hD' : ∀ d ∈ D, d ≤ r := fun d hd => (hD d hd).2
  have hh : h ∈ plusFlagStabO K r D := mem_plusFlagStabO.2 ⟨hO, fun d hd =>
    smul_flag_eq hr hD hO hα hNF.stab hodd hd⟩
  have hσ : ∀ s : K, σ s = s := by
    rcases hblk with ⟨b, hb, hk⟩ | hm2
    · exact (gl_block hr hD' ht htm hNF hα hh hb hk).1
    · exact (res_block hr hD' ht htm hDt hm2 hNF hα hh).1
  have hσ1 : σ = 1 := RingEquiv.ext hσ
  refine ⟨h, hh, fun x => ?_, fun b hb => ?_, ?_⟩
  · rw [hα, hσ1, fieldConj_one]
  · by_cases hk : 2 ≤ b - predCut D b
    · obtain ⟨c, hc⟩ := (gl_block hr hD' ht htm hNF hα hh hb hk).2
      exact mem_center_of_eq_smul_one hc
    · exact Subgroup.mem_center_iff.2 fun g => gl_mul_comm_of_lt_two (by omega) _ _
  · rcases hm with hm0 | hm2
    · subst hm0
      haveI := gl_subsingleton_zero (K := K)
      exact Subgroup.mem_center_iff.2 fun g => Subsingleton.elim _ _
    · obtain ⟨c, hc⟩ := (res_block hr hD' ht htm hDt hm2 hNF hα hh).2
      exact mem_center_of_eq_smul_one hc

theorem mem_normalizer_orthElementaryGroup {h : GLV r K}
    (hO : h ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus r K)) :
    h ∈ Subgroup.normalizer (orthElementaryGroup (quadPlus r K) : Set (GLV r K)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => conj_mem_orthElementaryGroup hO hx, fun hx => ?_⟩
  have := conj_mem_orthElementaryGroup (inv_mem hO) hx
  simpa [mul_assoc] using this

theorem orthModelComm (hr : 3 ≤ r) {D : Finset ℕ} (hD : ∀ d ∈ D, 1 ≤ d ∧ d ≤ r)
    (hD1 : r - 1 ∈ D → r ∈ D) {t m : ℕ} (ht : t = 0 ∨ t ∈ D) (hDt : ∀ d ∈ D, d ≤ t)
    (htm : t + m = r) (hblk : (∃ b ∈ D, 2 ≤ b - predCut D b) ∨ 2 ≤ m)
    {α₁ α₂ : MulAut ↥(orthElementaryGroup (quadPlus r K))} (hs₁ : IsSemilinear α₁)
    (hs₂ : IsSemilinear α₂) (ho₁ : Odd (orderOf α₁)) (ho₂ : Odd (orderOf α₂))
    (hoc : Odd (orderOf ⁅α₁, α₂⁆)) (hN₁ : NormFix (fun d hd => (hD d hd).2) ht htm α₁)
    (hN₂ : NormFix (fun d hd => (hD d hd).2) ht htm α₂) : ⁅α₁, α₂⁆ = 1 := by
  have hD' : ∀ d ∈ D, d ≤ r := fun d hd => (hD d hd).2
  have hm : m = 0 ∨ 2 ≤ m := eq_zero_or_two_le hr hD1 ht hDt htm
  obtain ⟨h₁, hh₁, hα₁, hb₁, hr₁⟩ := exists_data hr hD ht hDt htm hm hblk hs₁ ho₁ hN₁
  obtain ⟨h₂, hh₂, hα₂, hb₂, hr₂⟩ := exists_data hr hD ht hDt htm hm hblk hs₂ ho₂ hN₂
  have hO₁ := (mem_plusFlagStabO.1 hh₁).1
  have hO₂ := (mem_plusFlagStabO.1 hh₂).1
  set c : GLV r K := ⁅h₁, h₂⁆ with hc
  have hcO : c ∈ plusFlagStabO K r D := by
    rw [hc, commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hh₁ hh₂) (inv_mem hh₁)) (inv_mem hh₂)
  have hcE : c ∈ orthElementaryGroup (quadPlus r K) := by
    rw [← OrthogonalSplit.commutator_orthogonalGroup_quadPlus hr]
    exact Subgroup.commutator_mem_commutator hO₁ hO₂
  have hcQ : c ∈ plusFlagStab K r D := mem_plusFlagStab_iff.2 ⟨hcO, hcE⟩
  have hcsub : (⟨c, hcO⟩ : ↥(plusFlagStabO K r D)) =
      ⁅(⟨h₁, hh₁⟩ : ↥(plusFlagStabO K r D)), ⟨h₂, hh₂⟩⁆ := rfl
  have hblocks : ∀ (b : ℕ) (hb : b ∈ D), plusEBlockHom hD' hb ⟨c, hcQ⟩ = 1 := by
    intro b hb
    change plusEBlockHomO hD' hb ⟨c, hcO⟩ = 1
    rw [hcsub, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 ((Subgroup.mem_center_iff.1 (hb₂ b hb) _))
  have hres : plusResBlockHom hD' ht htm ⟨c, hcQ⟩ = 1 := by
    change plusResBlockHomO hD' ht htm ⟨c, hcO⟩ = 1
    rw [hcsub, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 ((Subgroup.mem_center_iff.1 hr₂ _))
  have hsup : D.sup id = t := sup_id_eq ht hDt
  have hP : IsPGroup 2 (Subgroup.zpowers (⟨c, hcQ⟩ : ↥(plusFlagStab K r D))) := by
    refine isPGroup_of_plusBlocks hD' (fun d hd => (hD d hd).1) fun g hg => ?_
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    refine ⟨fun b hb => ?_, fun x hx => ?_⟩
    · rw [map_zpow, hblocks b hb, _root_.one_zpow]
    · rw [hsup] at hx ⊢
      refine sub_mem_of_plusResBlockHom_eq_one hD' ht htm ?_ hx
      rw [map_zpow, hres, _root_.one_zpow]
  obtain ⟨k, hk⟩ := hP (⟨⟨c, hcQ⟩, Subgroup.mem_zpowers _⟩ :
    ↥(Subgroup.zpowers (⟨c, hcQ⟩ : ↥(plusFlagStab K r D))))
  have hck : c ^ 2 ^ k = 1 := by
    have := congrArg (fun y : ↥(Subgroup.zpowers (⟨c, hcQ⟩ : ↥(plusFlagStab K r D))) =>
      ((y : ↥(plusFlagStab K r D)) : GLV r K)) hk
    simpa using this
  set ν := (orthElementaryGroup (quadPlus r K)).normalizerMonoidHom with hν
  have hn₁ := mem_normalizer_orthElementaryGroup hO₁
  have hn₂ := mem_normalizer_orthElementaryGroup hO₂
  let a₁ : ↥(Subgroup.normalizer (orthElementaryGroup (quadPlus r K) : Set (GLV r K))) :=
    ⟨h₁, hn₁⟩
  let a₂ : ↥(Subgroup.normalizer (orthElementaryGroup (quadPlus r K) : Set (GLV r K))) :=
    ⟨h₂, hn₂⟩
  have hαν₁ : α₁ = ν a₁ :=
    MulEquiv.ext fun x => Subtype.ext (by
      rw [hα₁, hν, Subgroup.normalizerMonoidHom_apply_apply_coe])
  have hαν₂ : α₂ = ν a₂ :=
    MulEquiv.ext fun x => Subtype.ext (by
      rw [hα₂, hν, Subgroup.normalizerMonoidHom_apply_apply_coe])
  have hcomm : ⁅α₁, α₂⁆ = ν ⁅a₁, a₂⁆ := by
    rw [map_commutatorElement, ← hαν₁, ← hαν₂]
  have hgk : ⁅a₁, a₂⁆ ^ 2 ^ k = 1 := Subtype.ext hck
  have hdvd : orderOf ⁅α₁, α₂⁆ ∣ 2 ^ k := by
    rw [hcomm]
    exact (orderOf_map_dvd ν _).trans (orderOf_dvd_of_pow_eq_one hgk)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hj0 : j = 0 := by
    by_contra hne
    rw [hj] at hoc
    exact (Nat.not_even_iff_odd.mpr hoc) (Nat.even_pow.mpr ⟨even_two, hne⟩)
  rw [hj0, pow_zero] at hj
  exact orderOf_eq_one_iff.mp hj

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.OrthPlus
