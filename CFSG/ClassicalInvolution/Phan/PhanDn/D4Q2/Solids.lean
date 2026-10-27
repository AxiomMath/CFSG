module

public import CFSG.ClassicalInvolution.Phan.PhanDn.D4Q2.Points

public section

namespace CFSG.ClassicalInvolution.PhanDn.D4Q2

open QuadraticMap CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Unitary Module

variable {K : Type} [Field K] [CharP K 2] {σ : K ≃+* K} {ω : K}

@[expose] noncomputable def solSub (ω : K) (F : Array (Array ℕ)) (j : ℕ) :
    Submodule K (Fin 4 ⊕ Fin 4 → K) :=
  Submodule.span K (Set.range fun k : Fin 4 => vecC ω (ptCodes ())[(F[j]!)[k.1]!]!)

variable {F : Array (Array ℕ)}

structure Checks (F : Array (Array ℕ)) : Prop where
  size : sizeCheck (mkTabs (ptCodes ()) F) = true
  frame : frameCheck (mkTabs (ptCodes ()) F) = true
  distinct : distinctCheck (mkTabs (ptCodes ()) F) = true
  clique : cliqueCheck (mkTabs (ptCodes ()) F) = true
  apart : apartCheck (mkTabs (ptCodes ()) F) = true

private theorem d4s_getElem!_eq_getElem {α : Type} [Inhabited α] (a : Array α) {i : Nat}
    (h : i < a.size) : a[i]! = a[i]'h := by
  rw [Array.getElem!_eq_getD, Array.getElem_eq_getD]

private theorem d4s_size (hT : Checks F) : F.size = 4480 := by
  have hpts : (mkTabs (ptCodes ()) F).pts = ptCodes () := rfl
  have hframes : (mkTabs (ptCodes ()) F).frames = F := rfl
  have h := hT.size
  rw [sizeCheck, hpts, hframes, Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at h
  exact h.2

private theorem d4s_pts_size (hT : Checks F) : (ptCodes ()).size = 2240 := by
  have hpts : (mkTabs (ptCodes ()) F).pts = ptCodes () := rfl
  have hframes : (mkTabs (ptCodes ()) F).frames = F := rfl
  have h := hT.size
  rw [sizeCheck, hpts, hframes, Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at h
  exact h.1

private theorem d4s_frame_spec (hT : Checks F) {j : ℕ} (hj : j < 4480) :
    (F[j]!).size = 4 ∧ (∀ k, k < 4 → (F[j]!)[k]! < 2240) ∧
      (∀ k l : Fin 4, k < l →
        ptAdjC ((ptCodes ())[(F[j]!)[k.1]!]!) ((ptCodes ())[(F[j]!)[l.1]!]!) = true) := by
  have hpts : (mkTabs (ptCodes ()) F).pts = ptCodes () := rfl
  have hframes : (mkTabs (ptCodes ()) F).frames = F := rfl
  have h := hT.frame
  rw [frameCheck, hframes, hpts, Array.all_eq_true] at h
  have hj' : j < F.size := by rw [d4s_size hT]; exact hj
  have h1 := h j hj'
  have h1' : ((F[j]!).size == 4 && (F[j]!).all (fun x => decide (x < 2240)) &&
      ptAdjC (ptCodes ())[(F[j]!)[0]!]! (ptCodes ())[(F[j]!)[1]!]! &&
      ptAdjC (ptCodes ())[(F[j]!)[0]!]! (ptCodes ())[(F[j]!)[2]!]! &&
      ptAdjC (ptCodes ())[(F[j]!)[0]!]! (ptCodes ())[(F[j]!)[3]!]! &&
      ptAdjC (ptCodes ())[(F[j]!)[1]!]! (ptCodes ())[(F[j]!)[2]!]! &&
      ptAdjC (ptCodes ())[(F[j]!)[1]!]! (ptCodes ())[(F[j]!)[3]!]! &&
      ptAdjC (ptCodes ())[(F[j]!)[2]!]! (ptCodes ())[(F[j]!)[3]!]!) = true := by
    rw [d4s_getElem!_eq_getElem F hj']
    exact h1
  simp only [Bool.and_eq_true, beq_iff_eq] at h1'
  obtain ⟨⟨⟨⟨⟨⟨⟨hsz, hlt⟩, h01⟩, h02⟩, h03⟩, h12⟩, h13⟩, h23⟩ := h1'
  have hall : ∀ k, k < 4 → (F[j]!)[k]! < 2240 := by
    intro k hk
    have hk' : k < (F[j]!).size := by rw [hsz]; exact hk
    have h2 : decide ((F[j]!)[k]'hk' < 2240) = true :=
      (Array.all_eq_true (p := fun x => decide (x < 2240)) (as := F[j]!)).mp hlt k hk'
    have h3 : (F[j]!)[k]'hk' < 2240 := of_decide_eq_true h2
    rw [d4s_getElem!_eq_getElem (F[j]!) hk']
    exact h3
  refine ⟨hsz, hall, ?_⟩
  intro k l hkl
  fin_cases k <;> fin_cases l <;> simp_all

private def d4s_b (F : Array (Array ℕ)) (j : ℕ) (k : Fin 4) : ℕ :=
  (ptCodes ())[(F[j]!)[k.1]!]!

private def d4s_x {K : Type} [Field K] (ω : K) (F : Array (Array ℕ)) (j : ℕ) (k : Fin 4) :
    Fin 4 ⊕ Fin 4 → K :=
  vecC ω (d4s_b F j k)

omit [CharP K 2] in
private theorem d4s_solSub_eq_span (ω : K) (F : Array (Array ℕ)) (j : ℕ) :
    solSub ω F j = Submodule.span K (Set.range (d4s_x ω F j)) := rfl

private theorem d4s_b_mem_ptCodes (hT : Checks F) {j : ℕ} (hj : j < 4480) (k : Fin 4) :
    d4s_b F j k ∈ ptCodes () := by
  have hk : (F[j]!)[k.1]! < (ptCodes ()).size := by
    rw [d4s_pts_size hT]
    exact (d4s_frame_spec hT hj).2.1 k.1 k.2
  simp only [d4s_b, d4s_getElem!_eq_getElem (ptCodes ()) hk]
  exact Array.getElem_mem hk

private theorem d4s_b_data (hT : Checks F) {j : ℕ} (hj : j < 4480) (k : Fin 4) :
    d4s_b F j k < 65536 ∧ normC (d4s_b F j k) = true ∧ quadC (d4s_b F j k) = 0 ∧
      hermC (d4s_b F j k) (d4s_b F j k) ≠ 0 :=
  mem_ptCodes.mp (d4s_b_mem_ptCodes hT hj k)

private theorem d4s_x_quad (hω : ω * ω = ω + 1) (hT : Checks F) {j : ℕ} (hj : j < 4480)
    (k : Fin 4) : quadPlus 4 K (d4s_x ω F j k) = 0 := by
  obtain ⟨-, -, hq, -⟩ := d4s_b_data hT hj k
  rw [d4s_x, quadPlus_vecC hω]
  rw [hq]
  rfl

private theorem d4s_x_diag [Finite K] (hσ : IsUnitaryInvolution σ) (hK : Nat.card K = 4)
    (hω : ω * ω = ω + 1) (hσω : σ ω = ω + 1) (hT : Checks F) {j : ℕ} (hj : j < 4480)
    (k : Fin 4) : flipHerm σ (d4s_x ω F j k) (d4s_x ω F j k) = 1 := by
  obtain ⟨-, -, -, hh⟩ := d4s_b_data hT hj k
  have hne : flipHerm σ (d4s_x ω F j k) (d4s_x ω F j k) ≠ 0 := by
    rw [d4s_x, flipHerm_vecC hω hσω]
    intro hzero
    exact hh ((enc_eq_zero_iff hω (hermC_lt _ _)).mp hzero)
  exact qTwo_fixed_eq_one hσ hK (flipHerm_self_mem_fixed hσ.invol _) hne

private theorem d4s_x_ne_zero [Finite K] (hσ : IsUnitaryInvolution σ) (hK : Nat.card K = 4)
    (hω : ω * ω = ω + 1) (hσω : σ ω = ω + 1) (hT : Checks F) {j : ℕ} (hj : j < 4480)
    (k : Fin 4) : d4s_x ω F j k ≠ 0 := by
  intro h
  have h1 := d4s_x_diag hσ hK hω hσω hT hj k
  rw [h, flipHerm_zero_left] at h1
  exact one_ne_zero h1.symm

private theorem d4s_hermC_eq_zero (hT : Checks F) {j : ℕ} (hj : j < 4480) {k l : Fin 4}
    (hkl : k < l) : hermC (d4s_b F j k) (d4s_b F j l) = 0 := by
  have h := (d4s_frame_spec hT hj).2.2 k l hkl
  simp only [ptAdjC, Bool.and_eq_true, beq_iff_eq] at h
  exact h.2

private theorem d4s_polarC_eq_zero (hT : Checks F) {j : ℕ} (hj : j < 4480) {k l : Fin 4}
    (hkl : k < l) : polarC (d4s_b F j k) (d4s_b F j l) = 0 := by
  have h := (d4s_frame_spec hT hj).2.2 k l hkl
  simp only [ptAdjC, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.2

private theorem d4s_x_flipHerm_eq_zero (hσ : IsUnitaryInvolution σ) (hω : ω * ω = ω + 1)
    (hσω : σ ω = ω + 1) (hT : Checks F) {j : ℕ} (hj : j < 4480) {k l : Fin 4} (hkl : k ≠ l) :
    flipHerm σ (d4s_x ω F j k) (d4s_x ω F j l) = 0 := by
  rcases lt_or_gt_of_ne hkl with h | h
  · rw [d4s_x, d4s_x, flipHerm_vecC hω hσω, d4s_hermC_eq_zero hT hj h]
    rfl
  · have h1 : flipHerm σ (d4s_x ω F j l) (d4s_x ω F j k) = 0 := by
      rw [d4s_x, d4s_x, flipHerm_vecC hω hσω, d4s_hermC_eq_zero hT hj h]
      rfl
    exact (flipHerm_eq_zero_iff hσ.invol).mp h1

private theorem d4s_x_polar_eq_zero (hω : ω * ω = ω + 1) (hT : Checks F) {j : ℕ}
    (hj : j < 4480) {k l : Fin 4} (hkl : k ≠ l) :
    polar (quadPlus 4 K) (d4s_x ω F j k) (d4s_x ω F j l) = 0 := by
  rcases lt_or_gt_of_ne hkl with h | h
  · rw [d4s_x, d4s_x, polar_vecC hω, d4s_polarC_eq_zero hT hj h]
    rfl
  · have h1 : polar (quadPlus 4 K) (d4s_x ω F j l) (d4s_x ω F j k) = 0 := by
      rw [d4s_x, d4s_x, polar_vecC hω, d4s_polarC_eq_zero hT hj h]
      rfl
    rwa [QuadraticMap.polar_comm (quadPlus 4 K)] at h1

omit [CharP K 2] in
private theorem d4s_span_le_flipOrth {x y : Fin 4 ⊕ Fin 4 → K} (h : flipHerm σ y x = 0) :
    K ∙ x ≤ flipOrth σ (K ∙ y) := by
  intro v hv
  rw [mem_flipOrth_span_singleton]
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
  rw [flipHerm_smul_right, h, mul_zero]

omit [CharP K 2] in
private theorem d4s_span_le_qPerp {x y : Fin 4 ⊕ Fin 4 → K}
    (h : polar (quadPlus 4 K) y x = 0) : K ∙ x ≤ qPerp 4 K (K ∙ y) := by
  intro v hv
  rw [mem_qPerp]
  intro w hw
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
  obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hw
  rw [QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right, h]
  simp

omit [CharP K 2] in
private theorem d4s_span_fin4 (x : Fin 4 → (Fin 4 ⊕ Fin 4 → K)) :
    Submodule.span K (Set.range x) = K ∙ x 0 ⊔ K ∙ x 1 ⊔ K ∙ x 2 ⊔ K ∙ x 3 := by
  refine le_antisymm ?_ ?_
  · rw [Submodule.span_le]
    rintro v ⟨k, rfl⟩
    fin_cases k
    · exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_left
        (Submodule.mem_span_singleton_self _)))
    · exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_right
        (Submodule.mem_span_singleton_self _)))
    · exact Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
    · exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  · refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
    · exact (Submodule.span_singleton_le_iff_mem _ _).mpr (Submodule.subset_span ⟨0, rfl⟩)
    · exact (Submodule.span_singleton_le_iff_mem _ _).mpr (Submodule.subset_span ⟨1, rfl⟩)
    · exact (Submodule.span_singleton_le_iff_mem _ _).mpr (Submodule.subset_span ⟨2, rfl⟩)
    · exact (Submodule.span_singleton_le_iff_mem _ _).mpr (Submodule.subset_span ⟨3, rfl⟩)

private theorem d4s_linearIndependent [Finite K] (hσ : IsUnitaryInvolution σ) (hK : Nat.card K = 4)
    (hω : ω * ω = ω + 1) (hσω : σ ω = ω + 1) (hT : Checks F) {j : ℕ} (hj : j < 4480) :
    LinearIndependent K (d4s_x ω F j) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg k
  have h := congrArg (flipHermSesq (n := 4) σ (d4s_x ω F j k)) hg
  simp only [map_zero] at h
  rw [map_sum] at h
  simp only [map_smul, flipHermSesq_apply, smul_eq_mul] at h
  rw [Finset.sum_eq_single k] at h
  · rw [d4s_x_diag hσ hK hω hσω hT hj k, mul_one] at h
    exact h
  · intro l _ hlk
    rw [(flipHerm_eq_zero_iff hσ.invol).mp
      (d4s_x_flipHerm_eq_zero hσ hω hσω hT hj hlk.symm), mul_zero]
  · intro hk
    exact absurd (Finset.mem_univ k) hk


section More

variable {K : Type} [Field K] [CharP K 2] {σ : K ≃+* K} {ω : K}
variable {F : Array (Array ℕ)}

private theorem d4s_le_qPerp (hω : ω * ω = ω + 1) (hT : Checks F) {j : ℕ} (hj : j < 4480)
    {k l : Fin 4} (hkl : k ≠ l) : K ∙ d4s_x ω F j k ≤ qPerp 4 K (K ∙ d4s_x ω F j l) := by
  refine d4s_span_le_qPerp ?_
  rw [QuadraticMap.polar_comm (quadPlus 4 K)]
  exact d4s_x_polar_eq_zero hω hT hj hkl

private theorem d4s_le_flipOrth (hσ : IsUnitaryInvolution σ) (hω : ω * ω = ω + 1)
    (hσω : σ ω = ω + 1) (hT : Checks F) {j : ℕ} (hj : j < 4480) {k l : Fin 4}
    (hkl : k ≠ l) : K ∙ d4s_x ω F j k ≤ flipOrth σ (K ∙ d4s_x ω F j l) := by
  refine d4s_span_le_flipOrth ?_
  exact (flipHerm_eq_zero_iff hσ.invol).mp (d4s_x_flipHerm_eq_zero hσ hω hσω hT hj hkl)

private theorem d4s_isFlipflopSub_solSub [Finite K] (hσ : IsUnitaryInvolution σ)
    (hK : Nat.card K = 4) (hω : ω * ω = ω + 1) (hσω : σ ω = ω + 1) (hT : Checks F)
    {j : ℕ} (hj : j < 4480) : IsFlipflopSub σ (solSub ω F j) := by
  have hsingle : ∀ k : Fin 4, IsFlipflopSub σ (K ∙ d4s_x ω F j k) := by
    intro k
    rw [isFlipflopSub_span_singleton_iff (d4s_x_ne_zero hσ hK hω hσω hT hj k)]
    exact ⟨d4s_x_quad hω hT hj k, by rw [d4s_x_diag hσ hK hω hσω hT hj k]; exact one_ne_zero⟩
  have h01 : IsFlipflopSub σ (K ∙ d4s_x ω F j 0 ⊔ K ∙ d4s_x ω F j 1) :=
    (IsFlipflopSub.sup_of_orth hσ.invol (hsingle 0) (hsingle 1)
      (d4s_le_qPerp hω hT hj (k := 0) (l := 1) (by decide))
      (d4s_le_flipOrth hσ hω hσω hT hj (k := 0) (l := 1) (by decide))).1
  have h23 : IsFlipflopSub σ (K ∙ d4s_x ω F j 2 ⊔ K ∙ d4s_x ω F j 3) :=
    (IsFlipflopSub.sup_of_orth hσ.invol (hsingle 2) (hsingle 3)
      (d4s_le_qPerp hω hT hj (k := 2) (l := 3) (by decide))
      (d4s_le_flipOrth hσ hω hσω hT hj (k := 2) (l := 3) (by decide))).1
  have hq : (K ∙ d4s_x ω F j 0 ⊔ K ∙ d4s_x ω F j 1) ≤
      qPerp 4 K (K ∙ d4s_x ω F j 2 ⊔ K ∙ d4s_x ω F j 3) := by
    rw [qPerp_sup]
    refine sup_le (le_inf ?_ ?_) (le_inf ?_ ?_)
    · exact d4s_le_qPerp hω hT hj (k := 0) (l := 2) (by decide)
    · exact d4s_le_qPerp hω hT hj (k := 0) (l := 3) (by decide)
    · exact d4s_le_qPerp hω hT hj (k := 1) (l := 2) (by decide)
    · exact d4s_le_qPerp hω hT hj (k := 1) (l := 3) (by decide)
  have hf : (K ∙ d4s_x ω F j 0 ⊔ K ∙ d4s_x ω F j 1) ≤
      flipOrth σ (K ∙ d4s_x ω F j 2 ⊔ K ∙ d4s_x ω F j 3) := by
    rw [flipOrth_sup]
    refine sup_le (le_inf ?_ ?_) (le_inf ?_ ?_)
    · exact d4s_le_flipOrth hσ hω hσω hT hj (k := 0) (l := 2) (by decide)
    · exact d4s_le_flipOrth hσ hω hσω hT hj (k := 0) (l := 3) (by decide)
    · exact d4s_le_flipOrth hσ hω hσω hT hj (k := 1) (l := 2) (by decide)
    · exact d4s_le_flipOrth hσ hω hσω hT hj (k := 1) (l := 3) (by decide)
  have hAB : IsFlipflopSub σ ((K ∙ d4s_x ω F j 0 ⊔ K ∙ d4s_x ω F j 1) ⊔
      (K ∙ d4s_x ω F j 2 ⊔ K ∙ d4s_x ω F j 3)) :=
    (IsFlipflopSub.sup_of_orth hσ.invol h01 h23 hq hf).1
  have hspan : solSub ω F j =
      (K ∙ d4s_x ω F j 0 ⊔ K ∙ d4s_x ω F j 1) ⊔
        (K ∙ d4s_x ω F j 2 ⊔ K ∙ d4s_x ω F j 3) := by
    rw [d4s_solSub_eq_span, d4s_span_fin4, sup_assoc]
  rw [hspan]
  exact hAB

private theorem d4s_finrank_solSub [Finite K] (hσ : IsUnitaryInvolution σ)
    (hK : Nat.card K = 4) (hω : ω * ω = ω + 1) (hσω : σ ω = ω + 1) (hT : Checks F)
    {j : ℕ} (hj : j < 4480) : finrank K (solSub ω F j) = 4 := by
  rw [d4s_solSub_eq_span, finrank_span_eq_card
    (d4s_linearIndependent hσ hK hω hσω hT hj)]
  simp

end More

section Proj

variable {K : Type} [Field K] [CharP K 2] {σ : K ≃+* K} {ω : K}
variable {F : Array (Array ℕ)}

private def d4s_proj (F : Array (Array ℕ)) (j v : ℕ) : ℕ :=
  smulC (hermC v (d4s_b F j 0)) (d4s_b F j 0) ^^^
    smulC (hermC v (d4s_b F j 1)) (d4s_b F j 1) ^^^
    smulC (hermC v (d4s_b F j 2)) (d4s_b F j 2) ^^^
    smulC (hermC v (d4s_b F j 3)) (d4s_b F j 3)

private theorem d4s_memC_eq (F : Array (Array ℕ)) (j v : ℕ) :
    memC (ptCodes ()) F[j]! v = (v == d4s_proj F j v) := rfl

private theorem d4s_proj_lt (F : Array (Array ℕ)) (j v : ℕ) : d4s_proj F j v < 65536 := by
  simp only [d4s_proj]
  refine xor_lt (xor_lt (xor_lt (smulC_lt (hermC_lt _ _) _) (smulC_lt (hermC_lt _ _) _))
    (smulC_lt (hermC_lt _ _) _)) (smulC_lt (hermC_lt _ _) _)

private theorem d4s_vecC_proj (hω : ω * ω = ω + 1) (hσω : σ ω = ω + 1)
    (F : Array (Array ℕ)) (j v : ℕ) :
    vecC ω (d4s_proj F j v) =
      ∑ k : Fin 4, flipHerm σ (vecC ω v) (d4s_x ω F j k) • d4s_x ω F j k := by
  rw [Fin.sum_univ_four]
  simp only [d4s_proj, d4s_x, vecC_xor, vecC_smulC hω (hermC_lt v (d4s_b F j 0)),
    vecC_smulC hω (hermC_lt v (d4s_b F j 1)), vecC_smulC hω (hermC_lt v (d4s_b F j 2)),
    vecC_smulC hω (hermC_lt v (d4s_b F j 3)), flipHerm_vecC hω hσω]

end Proj

section Proj2

variable {K : Type} [Field K] [CharP K 2] {σ : K ≃+* K} {ω : K}
variable {F : Array (Array ℕ)}

private theorem d4s_eq_proj_of_mem [Finite K] (hσ : IsUnitaryInvolution σ)
    (hK : Nat.card K = 4) (hω : ω * ω = ω + 1) (hσω : σ ω = ω + 1) (hT : Checks F)
    {j : ℕ} (hj : j < 4480) {u : Fin 4 ⊕ Fin 4 → K} (hu : u ∈ solSub ω F j) :
    u = ∑ k : Fin 4, flipHerm σ u (d4s_x ω F j k) • d4s_x ω F j k := by
  rw [d4s_solSub_eq_span] at hu
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, rfl⟩ := hx
    rw [Finset.sum_eq_single l]
    · rw [d4s_x_diag hσ hK hω hσω hT hj l, one_smul]
    · intro k _ hkl
      rw [(flipHerm_eq_zero_iff hσ.invol).mp
        (d4s_x_flipHerm_eq_zero hσ hω hσω hT hj hkl), zero_smul]
    · intro hl
      exact absurd (Finset.mem_univ l) hl
  | zero => simp
  | add x y hx hy ihx ihy =>
    conv_lhs => rw [ihx, ihy]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [flipHerm_add_left, add_smul]
  | smul a x hx ih =>
    conv_lhs => rw [ih]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [flipHerm_smul_left, mul_smul]

private theorem d4s_mem_solSub_of_memC (hω : ω * ω = ω + 1) (hσω : σ ω = ω + 1)
    (F : Array (Array ℕ)) {j v : ℕ} (h : memC (ptCodes ()) F[j]! v = true) :
    vecC ω v ∈ solSub ω F j := by
  have hv : v = d4s_proj F j v := by
    rw [d4s_memC_eq] at h
    exact beq_iff_eq.mp h
  rw [hv, d4s_vecC_proj hω hσω]
  exact Submodule.sum_mem _ fun k _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

private theorem d4s_memC_of_mem_solSub [Finite K] (hσ : IsUnitaryInvolution σ)
    (hK : Nat.card K = 4) (hω : ω * ω = ω + 1) (hσω : σ ω = ω + 1) (hT : Checks F)
    {j : ℕ} (hj : j < 4480) {v : ℕ} (hv : v < 65536) (h : vecC ω v ∈ solSub ω F j) :
    memC (ptCodes ()) F[j]! v = true := by
  have hp := d4s_eq_proj_of_mem hσ hK hω hσω hT hj h
  have heq : v = d4s_proj F j v :=
    vecC_injOn hω hv (d4s_proj_lt F j v) (hp.trans (d4s_vecC_proj hω hσω F j v).symm)
  rw [d4s_memC_eq, beq_iff_eq]
  exact heq

private theorem d4s_memC_iff [Finite K] (hω : ω * ω = ω + 1) (hσω : σ ω = ω + 1)
    (hσ : IsUnitaryInvolution σ) (hK : Nat.card K = 4) (hT : Checks F) {j : ℕ} (hj : j < 4480)
    {v : ℕ} (hv : v < 65536) :
    memC (ptCodes ()) F[j]! v = true ↔ vecC ω v ∈ solSub ω F j :=
  ⟨d4s_mem_solSub_of_memC hω hσω F, d4s_memC_of_mem_solSub hσ hK hω hσω hT hj hv⟩

end Proj2

section Inj

variable {K : Type} [Field K] [CharP K 2] {σ : K ≃+* K} {ω : K}
variable {F : Array (Array ℕ)}

private theorem d4s_getElem!_map {α β : Type} [Inhabited α] [Inhabited β] {f : α → β}
    {a : Array α} {i : Nat} (h : i < a.size) : (a.map f)[i]! = f a[i]! := by
  rw [d4s_getElem!_eq_getElem (a.map f) (by simpa using h), Array.getElem_map,
    ← d4s_getElem!_eq_getElem a h]

private theorem d4s_getElem!_range {n i : Nat} (h : i < n) : (Array.range n)[i]! = i := by
  rw [d4s_getElem!_eq_getElem (Array.range n) (by simpa using h), Array.getElem_range]

private theorem d4s_filter_congr_mem {α : Type} {p q : α → Bool} {xs : Array α}
    (h : ∀ a, a ∈ xs → p a = q a) : xs.filter p = xs.filter q := by
  apply Array.toList_inj.mp
  rw [Array.toList_filter, Array.toList_filter]
  exact List.filter_congr fun x hx => h x (Array.mem_def.mpr hx)

private theorem d4s_filter_map {n : Nat} (g : Nat → Bool) :
    (Array.range (Array.map g (Array.range n)).size).filter
        (fun i => (Array.map g (Array.range n))[i]!) = (Array.range n).filter g := by
  apply Array.toList_inj.mp
  rw [Array.toList_filter, Array.toList_filter, Array.toList_range, Array.toList_range,
    Array.size_map, Array.size_range]
  refine List.filter_congr fun i hi => ?_
  rw [List.mem_range] at hi
  rw [d4s_getElem!_map (a := Array.range n) (by simpa using hi), d4s_getElem!_range hi]

private theorem d4s_solPts_mkTabs (P : Array Nat) (j : Nat) (hj : j < F.size) :
    (mkTabs P F).solPts[j]! = (Array.range P.size).filter (fun i => memC P F[j]! P[i]!) := by
  have hsp : (mkTabs P F).solPts =
      (F.map (fun fr => (Array.range P.size).map fun i => memC P fr P[i]!)).map
        (fun r => (Array.range r.size).filter fun i => r[i]!) := rfl
  rw [hsp, d4s_getElem!_map
      (a := F.map (fun fr => (Array.range P.size).map fun i => memC P fr P[i]!))
      (by simpa using hj),
    d4s_getElem!_map (a := F) hj]
  exact d4s_filter_map (n := P.size) (g := fun i => memC P F[j]! P[i]!)

private theorem d4s_getElem!_mem_ptCodes {i : ℕ} (hi : i < (ptCodes ()).size) :
    (ptCodes ())[i]! ∈ ptCodes () := by
  rw [d4s_getElem!_eq_getElem (ptCodes ()) hi]
  exact Array.getElem_mem hi

private theorem d4s_add_self (w : Fin 4 ⊕ Fin 4 → K) : w + w = 0 := by
  ext x
  exact CharTwo.add_self_eq_zero (w x)

private theorem d4s_inc_mkTabs (P : Array Nat) (j : Nat) (hj : j < F.size) :
    ((mkTabs P F).inc[j]!) = (Array.range P.size).map (fun i => memC P F[j]! P[i]!) := by
  have hinc : (mkTabs P F).inc =
      F.map (fun fr => (Array.range P.size).map fun i => memC P fr P[i]!) := rfl
  rw [hinc, d4s_getElem!_map (a := F) hj]

private theorem d4s_inc_eval {j i : ℕ} (hj : j < F.size) (hi : i < (ptCodes ()).size) :
    ((mkTabs (ptCodes ()) F).inc[j]!)[i]! = memC (ptCodes ()) F[j]! (ptCodes ())[i]! := by
  rw [d4s_inc_mkTabs (ptCodes ()) j hj,
    d4s_getElem!_map (a := Array.range (ptCodes ()).size) (by simpa using hi),
    d4s_getElem!_range hi]

private theorem d4s_mem_solPts_mkTabs {j i : ℕ} (hj : j < F.size) :
    i ∈ (mkTabs (ptCodes ()) F).solPts[j]! ↔
      i < (ptCodes ()).size ∧ memC (ptCodes ()) F[j]! (ptCodes ())[i]! = true := by
  rw [d4s_solPts_mkTabs (ptCodes ()) j hj, Array.mem_filter, Array.mem_range]

private theorem d4s_bool_eq_of_iff {a b : Bool} (h : (a = true) ↔ (b = true)) : a = b := by
  cases a <;> cases b <;> simp_all

private theorem d4s_solPts_eq_of_solSub_eq [Finite K] (hσ : IsUnitaryInvolution σ)
    (hK : Nat.card K = 4) (hω : ω * ω = ω + 1) (hσω : σ ω = ω + 1) (hT : Checks F)
    {j j' : ℕ} (hj : j < 4480) (hj' : j' < 4480) (h : solSub ω F j = solSub ω F j') :
    (mkTabs (ptCodes ()) F).solPts[j]! = (mkTabs (ptCodes ()) F).solPts[j']! := by
  have hjF : j < F.size := by rw [d4s_size hT]; exact hj
  have hjF' : j' < F.size := by rw [d4s_size hT]; exact hj'
  rw [d4s_solPts_mkTabs (ptCodes ()) j hjF, d4s_solPts_mkTabs (ptCodes ()) j' hjF']
  refine d4s_filter_congr_mem fun i hi => ?_
  rw [Array.mem_range] at hi
  have hb : (ptCodes ())[i]! < 65536 := by
    rw [d4s_getElem!_eq_getElem (ptCodes ()) hi]
    exact (mem_ptCodes.mp (Array.getElem_mem hi)).1
  refine d4s_bool_eq_of_iff ?_
  rw [d4s_memC_iff hω hσω hσ hK hT hj hb, d4s_memC_iff hω hσω hσ hK hT hj' hb, h]

private theorem d4s_solSub_injOn [Finite K] (hσ : IsUnitaryInvolution σ) (hK : Nat.card K = 4)
    (hω : ω * ω = ω + 1) (hσω : σ ω = ω + 1) (hT : Checks F) {j j' : ℕ} (hj : j < 4480)
    (hj' : j' < 4480) (h : solSub ω F j = solSub ω F j') : j = j' := by
  by_contra hne
  have heq := d4s_solPts_eq_of_solSub_eq hσ hK hω hσω hT hj hj' h
  have hdist := hT.distinct
  rw [distinctCheck, List.all_eq_true] at hdist
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have h1 := hdist j' (List.mem_range.mpr (by omega))
    rw [List.all_eq_true] at h1
    have h2 := h1 j (List.mem_range.mpr hlt)
    rw [heq] at h2
    simp at h2
  · have h1 := hdist j (List.mem_range.mpr (by omega))
    rw [List.all_eq_true] at h1
    have h2 := h1 j' (List.mem_range.mpr hlt)
    rw [heq] at h2
    simp at h2

end Inj

section Gen

variable {K : Type} [Field K] [CharP K 2] {σ : K ≃+* K} {ω : K}

private theorem d4s_ptCode_diag [Finite K] (hσ : IsUnitaryInvolution σ) (hK : Nat.card K = 4)
    (hω : ω * ω = ω + 1) (hσω : σ ω = ω + 1) {c : ℕ} (hc : c ∈ ptCodes ()) :
    flipHerm σ (vecC ω c) (vecC ω c) = 1 := by
  obtain ⟨-, -, -, hh⟩ := mem_ptCodes.mp hc
  refine qTwo_fixed_eq_one hσ hK (flipHerm_self_mem_fixed hσ.invol _) ?_
  rw [flipHerm_vecC hω hσω]
  intro hzero
  exact hh ((enc_eq_zero_iff hω (hermC_lt _ _)).mp hzero)

private theorem d4s_ptCode_ne_zero [Finite K] (hσ : IsUnitaryInvolution σ)
    (hK : Nat.card K = 4) (hω : ω * ω = ω + 1) (hσω : σ ω = ω + 1) {c : ℕ}
    (hc : c ∈ ptCodes ()) : vecC ω c ≠ 0 := by
  intro h
  have h1 := d4s_ptCode_diag hσ hK hω hσω hc
  rw [h, flipHerm_zero_left] at h1
  exact one_ne_zero h1.symm

private theorem d4s_ptCode_flipHerm_eq_zero (hω : ω * ω = ω + 1) (hσω : σ ω = ω + 1)
    {c c' : ℕ} (hadj : ptAdjC c c' = true) :
    flipHerm σ (vecC ω c) (vecC ω c') = 0 := by
  simp only [ptAdjC, Bool.and_eq_true, beq_iff_eq] at hadj
  rw [flipHerm_vecC hω hσω, hadj.2]
  rfl

omit [CharP K 2] in
private theorem d4s_linearIndependent_of_orth {ι : Type} [Fintype ι]
    (x : ι → (Fin 4 ⊕ Fin 4 → K))
    (hdiag : ∀ i, flipHerm σ (x i) (x i) = 1)
    (horth : ∀ i j, i ≠ j → flipHerm σ (x i) (x j) = 0) : LinearIndependent K x := by
  rw [Fintype.linearIndependent_iff]
  intro g hg k
  have h := congrArg (flipHermSesq (n := 4) σ (x k)) hg
  simp only [map_zero] at h
  rw [map_sum] at h
  simp only [map_smul, flipHermSesq_apply, smul_eq_mul] at h
  rw [Finset.sum_eq_single k] at h
  · rw [hdiag k, mul_one] at h
    exact h
  · intro l _ hlk
    rw [horth l k hlk, mul_zero]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

end Gen

section Five

variable {K : Type} [Field K] [CharP K 2] {σ : K ≃+* K} {ω : K}

private theorem d4s_smul_add_not_mem [Finite K] (hK : Nat.card K = 4) (hω : ω * ω = ω + 1)
    {T : Submodule K (Fin 4 ⊕ Fin 4 → K)} {u v : Fin 4 ⊕ Fin 4 → K}
    (hu : u ∉ T) (hv : v ∉ T) (h1 : u + v ∉ T) (h2 : u + ω • v ∉ T)
    (h3 : u + (ω * ω) • v ∉ T) {a b : K} (hab : a ≠ 0 ∨ b ≠ 0) :
    a • u + b • v ∉ T := by
  intro hw
  have hmain : ∀ c : K, u + c • v ∈ T → False := by
    intro c hc
    by_cases hc0 : c = 0
    · rw [hc0, zero_smul, add_zero] at hc
      exact hu hc
    · obtain ⟨k, hk, hck⟩ := exists_enc hω hK c
      rw [← hck] at hc
      have hk0 : k ≠ 0 := by
        rintro rfl
        exact hc0 (by rw [← hck]; rfl)
      interval_cases k
      · exact hk0 rfl
      · have hc' : u + v ∈ T := by simpa [enc] using hc
        exact h1 hc'
      · have hc' : u + ω • v ∈ T := by simpa [enc] using hc
        exact h2 hc'
      · have hc' : u + (ω * ω) • v ∈ T := by
          rw [show enc ω 3 = ω * ω from by rw [show enc ω 3 = ω + 1 from rfl, ← hω]] at hc
          exact hc
        exact h3 hc'
  by_cases ha : a = 0
  · rw [ha, zero_smul, zero_add] at hw
    have hb : b ≠ 0 := by
      rcases hab with h | h
      · exact absurd ha h
      · exact h
    refine hv ?_
    have h := Submodule.smul_mem _ b⁻¹ hw
    rwa [inv_smul_smul₀ hb] at h
  · refine hmain (a⁻¹ * b) ?_
    have h := Submodule.smul_mem _ a⁻¹ hw
    simp only [smul_add, smul_smul, inv_mul_cancel₀ ha, one_smul] at h
    exact h

end Five

section Clique

variable {K : Type} [Field K] [CharP K 2] {σ : K ≃+* K} {ω : K}
variable {F : Array (Array ℕ)}

private theorem d4s_clique_apply (hT : Checks F) {i1 i2 i3 i4 : ℕ}
    (hi1 : i1 < 2240) (hi2 : i2 < 2240) (hi3 : i3 < 2240) (hi4 : i4 < 2240)
    (h12 : i1 < i2) (h23 : i2 < i3) (h34 : i3 < i4)
    (ha12 : ptAdjC ((ptCodes ())[i1]!) ((ptCodes ())[i2]!) = true)
    (ha13 : ptAdjC ((ptCodes ())[i1]!) ((ptCodes ())[i3]!) = true)
    (ha14 : ptAdjC ((ptCodes ())[i1]!) ((ptCodes ())[i4]!) = true)
    (ha23 : ptAdjC ((ptCodes ())[i2]!) ((ptCodes ())[i3]!) = true)
    (ha24 : ptAdjC ((ptCodes ())[i2]!) ((ptCodes ())[i4]!) = true)
    (ha34 : ptAdjC ((ptCodes ())[i3]!) ((ptCodes ())[i4]!) = true) :
    ∃ j < 4480, ((mkTabs (ptCodes ()) F).inc[j]!)[i1]! = true ∧
      ((mkTabs (ptCodes ()) F).inc[j]!)[i2]! = true ∧
      ((mkTabs (ptCodes ()) F).inc[j]!)[i3]! = true ∧
      ((mkTabs (ptCodes ()) F).inc[j]!)[i4]! = true := by
  have h := hT.clique
  unfold cliqueCheck at h
  dsimp only at h
  have hpts : (mkTabs (ptCodes ()) F).pts = ptCodes () := rfl
  rw [hpts] at h
  rw [List.all_eq_true] at h
  have hAi : ∀ i, i < 2240 →
      (Array.map (fun i => Array.filter
        (fun i' => ptAdjC ((ptCodes ())[i]!) ((ptCodes ())[i']!))
        (Array.range 2240)) (Array.range 2240))[i]! =
      Array.filter (fun i' => ptAdjC ((ptCodes ())[i]!)
        ((ptCodes ())[i']!)) (Array.range 2240) := by
    intro i hi
    rw [d4s_getElem!_map (a := Array.range 2240) (by simpa using hi), d4s_getElem!_range hi]
  have hSi : ∀ i, i < 2240 →
      (Array.map (fun i => Array.filter (fun j => ((mkTabs (ptCodes ()) F).inc[j]!)[i]!)
        (Array.range 4480)) (Array.range 2240))[i]! =
      Array.filter (fun j => ((mkTabs (ptCodes ()) F).inc[j]!)[i]!) (Array.range 4480) := by
    intro i hi
    rw [d4s_getElem!_map (a := Array.range 2240) (by simpa using hi), d4s_getElem!_range hi]
  have h1 := h i1 (List.mem_range.mpr hi1)
  rw [hAi i1 hi1] at h1
  have hi2mem : i2 ∈ Array.filter (fun i' =>
      ptAdjC ((ptCodes ())[i1]!) ((ptCodes ())[i']!))
      (Array.range 2240) := by
    rw [Array.mem_filter, Array.mem_range]
    exact ⟨hi2, ha12⟩
  have h2 := (Array.all_eq_true'.mp h1) i2 hi2mem
  simp only [h12, decide_true, Bool.not_true, Bool.false_or] at h2
  have hi3mem : i3 ∈ Array.filter (fun i3 => decide (i2 < i3) &&
      ptAdjC ((ptCodes ())[i2]!) ((ptCodes ())[i3]!))
      (Array.filter (fun i' => ptAdjC ((ptCodes ())[i1]!)
        ((ptCodes ())[i']!)) (Array.range 2240)) := by
    rw [Array.mem_filter]
    refine ⟨?_, by simp [h23, ha23]⟩
    rw [Array.mem_filter, Array.mem_range]
    exact ⟨hi3, ha13⟩
  have h3 := (Array.all_eq_true'.mp h2) i3 hi3mem
  have hi4mem : i4 ∈ Array.filter (fun i4 => decide (i3 < i4) &&
      ptAdjC ((ptCodes ())[i3]!) ((ptCodes ())[i4]!))
      (Array.filter (fun i3 => decide (i2 < i3) &&
        ptAdjC ((ptCodes ())[i2]!) ((ptCodes ())[i3]!))
        (Array.filter (fun i' => ptAdjC ((ptCodes ())[i1]!)
          ((ptCodes ())[i']!)) (Array.range 2240))) := by
    rw [Array.mem_filter]
    refine ⟨?_, by simp [h34, ha34]⟩
    rw [Array.mem_filter]
    refine ⟨?_, by simp [show i2 < i4 from by omega, ha24]⟩
    rw [Array.mem_filter, Array.mem_range]
    exact ⟨hi4, ha14⟩
  have h4 := (Array.all_eq_true'.mp h3) i4 hi4mem
  rw [hSi i1 hi1] at h4
  obtain ⟨j, hjS, hj⟩ := Array.any_eq_true'.mp h4
  rw [Array.mem_filter, Array.mem_range] at hjS
  obtain ⟨hjlt, hji1⟩ := hjS
  simp only [Bool.and_eq_true] at hj
  exact ⟨j, hjlt, hji1, hj.1.1, hj.1.2, hj.2⟩

end Clique

section Sorted

private theorem d4s_sorted_enum (i : Fin 4 → ℕ) (hinj : Function.Injective i) :
    ∃ (e : Fin 4 → ℕ) (m : Fin 4 → Fin 4), (∀ k, i (m k) = e k) ∧
      (∀ a b : Fin 4, a < b → e a < e b) := by
  classical
  let s : Finset ℕ := Finset.univ.image i
  have hcard : s.card = 4 := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  let eo : Fin 4 ≃o ↥s := Finset.orderIsoOfFin s hcard
  have hm : ∀ k : Fin 4, ∃ m : Fin 4, i m = (eo k : ℕ) := by
    intro k
    obtain ⟨x, -, hx⟩ := Finset.mem_image.mp (eo k).2
    exact ⟨x, hx⟩
  choose m hm using hm
  refine ⟨fun k => (eo k : ℕ), m, hm, ?_⟩
  intro a b hab
  simpa using eo.strictMono hab

end Sorted

section Exists

variable {K : Type} [Field K] [CharP K 2] {σ : K ≃+* K} {ω : K}
variable {F : Array (Array ℕ)}

private theorem d4s_exists_solSub_eq [Finite K] (hσ : IsUnitaryInvolution σ) (hK : Nat.card K = 4)
    (hω : ω * ω = ω + 1) (hσω : σ ω = ω + 1) (hT : Checks F)
    {S : Submodule K (Fin 4 ⊕ Fin 4 → K)} (hS : IsFlipflopSub σ S) (h4 : finrank K S = 4) :
    ∃ j < 4480, S = solSub ω F j := by
  obtain ⟨b, hb⟩ := exists_orthonormal_basis (n := 4) (σ := σ) hσ.invol hσ.exists_ne
    (fun a ha ha0 => by
      obtain ⟨y, hy⟩ := hσ.norm_surj a ha ha0
      exact ⟨y, by rwa [mul_comm]⟩) hS
  let x : Fin 4 → (Fin 4 ⊕ Fin 4 → K) := fun k => (b (Fin.cast h4.symm k) : S)
  have hxmem : ∀ k, x k ∈ S := fun k => (b (Fin.cast h4.symm k)).2
  have hxdiag : ∀ k, flipHerm σ (x k) (x k) = 1 := by
    intro k
    have h := hb (Fin.cast h4.symm k) (Fin.cast h4.symm k)
    simpa [x] using h
  have hxorth : ∀ k l, k ≠ l → flipHerm σ (x k) (x l) = 0 := by
    intro k l hkl
    have hne : Fin.cast h4.symm k ≠ Fin.cast h4.symm l :=
      fun h' => hkl (Fin.cast_injective h4.symm h')
    have h := hb (Fin.cast h4.symm k) (Fin.cast h4.symm l)
    rw [if_neg hne] at h
    simpa [x] using h
  have hxquad : ∀ k, quadPlus 4 K (x k) = 0 := fun k => hS.total (x k) (hxmem k)
  have hxne : ∀ k, x k ≠ 0 := by
    intro k h
    have h1 := hxdiag k
    rw [h, flipHerm_zero_left] at h1
    exact one_ne_zero h1.symm
  have hpolar : ∀ k l, k ≠ l → polar (quadPlus 4 K) (x k) (x l) = 0 := by
    intro k l hkl
    have hsum : quadPlus 4 K (x k + x l) = 0 := hS.total _ (S.add_mem (hxmem k) (hxmem l))
    have h := QuadraticMap.map_add (quadPlus 4 K) (x k) (x l)
    rw [hsum, hxquad k, hxquad l, add_zero, zero_add] at h
    exact h.symm
  have hpt : ∀ k, IsFlipflopPt σ (K ∙ x k) := by
    intro k
    rw [isFlipflopPt_span_singleton_iff (hxne k)]
    exact ⟨hxquad k, by rw [hxdiag k]; exact one_ne_zero⟩
  have hcode : ∀ k, ∃ c ∈ ptCodes (), K ∙ x k = K ∙ vecC ω c :=
    fun k => exists_mem_ptCodes hω hσω hK (hpt k)
  choose c hcP hcV using hcode
  have hidx : ∀ k, ∃ i, ∃ (_ : i < (ptCodes ()).size), (ptCodes ())[i]'‹_› = c k :=
    fun k => Array.mem_iff_getElem.mp (hcP k)
  choose ii hii hii' using hidx
  have hcode_eq : ∀ k, (ptCodes ())[ii k]! = c k := by
    intro k
    rw [d4s_getElem!_eq_getElem (ptCodes ()) (hii k)]
    exact hii' k
  have hadj : ∀ k l : Fin 4, k ≠ l → ptAdjC ((ptCodes ())[ii k]!) ((ptCodes ())[ii l]!) = true := by
    intro k l hkl
    have hqc : K ∙ x k ≤ qPerp 4 K (K ∙ x l) := by
      refine d4s_span_le_qPerp ?_
      rw [QuadraticMap.polar_comm (quadPlus 4 K)]
      exact hpolar k l hkl
    have hfc : K ∙ x k ≤ flipOrth σ (K ∙ x l) := by
      refine d4s_span_le_flipOrth ?_
      rw [flipHerm_eq_zero_iff hσ.invol]
      exact hxorth k l hkl
    have hcoll := flipColl_of_orth hσ.invol (hpt k) (hpt l) hqc hfc
    rw [hcV k, hcV l] at hcoll
    have h := (flipColl_span_vecC_iff hω hσω hσ hK (hcP k) (hcP l)).mp hcoll
    rwa [← hcode_eq k, ← hcode_eq l] at h
  have hinj_ii : Function.Injective ii := by
    intro k l hkl
    by_contra hne
    have h := hadj k l hne
    rw [hkl] at h
    simp [ptAdjC] at h
  obtain ⟨e, m, hm, he_mono⟩ := d4s_sorted_enum ii hinj_ii
  have he01 : e 0 < e 1 := he_mono 0 1 (by decide)
  have he12 : e 1 < e 2 := he_mono 1 2 (by decide)
  have he23 : e 2 < e 3 := he_mono 2 3 (by decide)
  have he_lt : ∀ k, e k < 2240 := by
    intro k
    rw [← hm k, ← d4s_pts_size hT]
    exact hii (m k)
  have he_inj : Function.Injective e := by
    intro a b hab
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact absurd hab (ne_of_lt (he_mono a b h))
    · exact absurd hab.symm (ne_of_lt (he_mono b a h))
  have hm_inj : Function.Injective m := by
    intro a b hab
    have h1 : e a = e b := by rw [← hm a, ← hm b, hab]
    exact he_inj h1
  have hm_surj : Function.Surjective m := Finite.injective_iff_surjective.mp hm_inj
  have hadj_e : ∀ a b : Fin 4, a < b →
      ptAdjC ((ptCodes ())[e a]!) ((ptCodes ())[e b]!) = true := by
    intro a b hab
    have hne : m a ≠ m b := by
      intro h
      have h1 : e a = e b := (hm a).symm.trans (by rw [h]; exact hm b)
      exact absurd h1 (ne_of_lt (he_mono a b hab))
    rw [← hm a, ← hm b]
    exact hadj (m a) (m b) hne
  obtain ⟨j, hjlt, hj0, hj1, hj2, hj3⟩ :=
    d4s_clique_apply hT (he_lt 0) (he_lt 1) (he_lt 2) (he_lt 3) he01 he12 he23
      (hadj_e 0 1 (by decide)) (hadj_e 0 2 (by decide)) (hadj_e 0 3 (by decide))
      (hadj_e 1 2 (by decide)) (hadj_e 1 3 (by decide)) (hadj_e 2 3 (by decide))
  have hjF : j < F.size := by rw [d4s_size hT]; exact hjlt
  have hinc : ∀ k : Fin 4, ((mkTabs (ptCodes ()) F).inc[j]!)[e k]! = true := by
    intro k
    fin_cases k
    · exact hj0
    · exact hj1
    · exact hj2
    · exact hj3
  have hspanS : Submodule.span K (Set.range x) = S := by
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rw [Submodule.span_le]
      rintro v ⟨k, rfl⟩
      exact hxmem k
    · rw [finrank_span_eq_card (d4s_linearIndependent_of_orth x hxdiag hxorth), h4]
      simp
  have hmemC_e : ∀ k : Fin 4, memC (ptCodes ()) F[j]! (ptCodes ())[e k]! = true := by
    intro k
    rw [← d4s_inc_eval hjF (i := e k) (by rw [d4s_pts_size hT]; exact he_lt k)]
    exact hinc k
  have hvec_e : ∀ k : Fin 4, vecC ω ((ptCodes ())[e k]!) ∈ solSub ω F j := by
    intro k
    have hbnd : (ptCodes ())[e k]! < 65536 := by
      have hi : e k < (ptCodes ()).size := by rw [d4s_pts_size hT]; exact he_lt k
      rw [d4s_getElem!_eq_getElem (ptCodes ()) hi]
      exact (mem_ptCodes.mp (Array.getElem_mem hi)).1
    exact (d4s_memC_iff hω hσω hσ hK hT hjlt hbnd).mp (hmemC_e k)
  have hxk : ∀ k, x k ∈ solSub ω F j := by
    intro k
    obtain ⟨r, rfl⟩ := hm_surj k
    have hi : ii (m r) < (ptCodes ()).size := hii (m r)
    have hline : K ∙ x (m r) = K ∙ vecC ω ((ptCodes ())[e r]!) := by
      rw [hcV (m r), ← hm r, ← hcode_eq (m r)]
    have hself : x (m r) ∈ K ∙ vecC ω ((ptCodes ())[e r]!) := by
      rw [← hline]
      exact Submodule.mem_span_singleton_self (x (m r))
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hself
    rw [← ha]
    exact Submodule.smul_mem _ _ (hvec_e r)
  refine ⟨j, hjlt, ?_⟩
  have hle : S ≤ solSub ω F j := by
    rw [← hspanS, Submodule.span_le]
    rintro v ⟨k, rfl⟩
    exact hxk k
  exact Submodule.eq_of_le_of_finrank_eq hle (by
    rw [d4s_finrank_solSub hσ hK hω hσω hT hjlt, h4])

end Exists

section TriTest

variable {K : Type} [Field K] [CharP K 2] {σ : K ≃+* K} {ω : K}
variable {F : Array (Array ℕ)}

private theorem d4s_triTest_spec {j j' : ℕ}
    (h : triTest (mkTabs (ptCodes ()) F) j j' = true) :
    ∃ a b c, a ∈ commonPts (mkTabs (ptCodes ()) F) j j' ∧
      b ∈ commonPts (mkTabs (ptCodes ()) F) j j' ∧
      c ∈ commonPts (mkTabs (ptCodes ()) F) j j' ∧
      ptAdjC ((ptCodes ())[a]!) ((ptCodes ())[b]!) = true ∧
      ptAdjC ((ptCodes ())[a]!) ((ptCodes ())[c]!) = true ∧
      ptAdjC ((ptCodes ())[b]!) ((ptCodes ())[c]!) = true := by
  unfold triTest at h
  obtain ⟨a, ha, h2⟩ := Array.any_eq_true'.mp h
  obtain ⟨b, hb, h3⟩ := Array.any_eq_true'.mp h2
  obtain ⟨c, hc, h4⟩ := Array.any_eq_true'.mp h3
  simp only [Bool.and_eq_true] at h4
  exact ⟨a, b, c, ha, hb, hc, h4.1.1, h4.1.2, h4.2⟩

private theorem d4s_apart_spec (hT : Checks F) {j j' : ℕ} (hj : j < 4480) (hj' : j' < 4480)
    (hne : j ≠ j') (htri : triTest (mkTabs (ptCodes ()) F) j j' = false) :
    ∃ a b, a ∈ (mkTabs (ptCodes ()) F).solPts[j]! ∧ b ∈ (mkTabs (ptCodes ()) F).solPts[j]! ∧
      ((mkTabs (ptCodes ()) F).inc[j']!)[a]! = false ∧
      ((mkTabs (ptCodes ()) F).inc[j']!)[b]! = false ∧
      memC (ptCodes ()) F[j']! ((ptCodes ())[a]! ^^^ (ptCodes ())[b]!) = false ∧
      memC (ptCodes ()) F[j']! ((ptCodes ())[a]! ^^^ smulC 2 (ptCodes ())[b]!) = false ∧
      memC (ptCodes ()) F[j']! ((ptCodes ())[a]! ^^^ smulC 3 (ptCodes ())[b]!) = false := by
  have h := hT.apart
  unfold apartCheck at h
  dsimp only at h
  rw [List.all_eq_true] at h
  have h1 := h j (List.mem_range.mpr hj)
  rw [List.all_eq_true] at h1
  have h2 := h1 j' (List.mem_range.mpr hj')
  have hjj : (j == j') = false := by simp [hne]
  simp only [hjj, htri, Bool.false_or] at h2
  obtain ⟨a, ha, h3⟩ := Array.any_eq_true'.mp h2
  obtain ⟨b, hb, h4⟩ := Array.any_eq_true'.mp h3
  simp only [Bool.not_eq_true', Bool.and_eq_true] at h4
  exact ⟨a, b, ha, hb, h4.1.1.1.1, h4.1.1.1.2, h4.1.1.2, h4.1.2, h4.2⟩

end TriTest

section DimInf

variable {K : Type} [Field K] [CharP K 2] {σ : K ≃+* K} {ω : K}
variable {F : Array (Array ℕ)}

private theorem d4s_inf_solSub_eq_three_iff [Finite K] (hσ : IsUnitaryInvolution σ)
    (hK : Nat.card K = 4) (hω : ω * ω = ω + 1) (hσω : σ ω = ω + 1) (hT : Checks F)
    {j j' : ℕ} (hj : j < 4480) (hj' : j' < 4480) (hne : j ≠ j') :
    finrank K ↥(solSub ω F j ⊓ solSub ω F j') = 3 ↔
      triTest (mkTabs (ptCodes ()) F) j j' = true := by
  have hjF : j < F.size := by rw [d4s_size hT]; exact hj
  have hjF' : j' < F.size := by rw [d4s_size hT]; exact hj'
  constructor
  · intro hdim3
    by_contra htri
    have htri' : triTest (mkTabs (ptCodes ()) F) j j' = false := by
      cases h : triTest (mkTabs (ptCodes ()) F) j j' <;> simp_all
    obtain ⟨a, b, haP, hbP, hina, hinb, hm1, hm2, hm3⟩ := d4s_apart_spec hT hj hj' hne htri'
    obtain ⟨ha_size, ha_memC⟩ := (d4s_mem_solPts_mkTabs (F := F) (hj := hjF)).mp haP
    obtain ⟨hb_size, hb_memC⟩ := (d4s_mem_solPts_mkTabs (F := F) (hj := hjF)).mp hbP
    have ha_lt : (ptCodes ())[a]! < 65536 := by
      rw [d4s_getElem!_eq_getElem (ptCodes ()) ha_size]
      exact (mem_ptCodes.mp (Array.getElem_mem ha_size)).1
    have hb_lt : (ptCodes ())[b]! < 65536 := by
      rw [d4s_getElem!_eq_getElem (ptCodes ()) hb_size]
      exact (mem_ptCodes.mp (Array.getElem_mem hb_size)).1
    have hja : vecC ω ((ptCodes ())[a]!) ∈ solSub ω F j :=
      (d4s_memC_iff hω hσω hσ hK hT hj ha_lt).mp ha_memC
    have hjb : vecC ω ((ptCodes ())[b]!) ∈ solSub ω F j :=
      (d4s_memC_iff hω hσω hσ hK hT hj hb_lt).mp hb_memC
    have hja' : vecC ω ((ptCodes ())[a]!) ∉ solSub ω F j' := by
      intro hmem
      have h1 : memC (ptCodes ()) F[j']! ((ptCodes ())[a]!) = true :=
        (d4s_memC_iff hω hσω hσ hK hT hj' ha_lt).mpr hmem
      rw [← d4s_inc_eval hjF' ha_size] at h1
      rw [h1] at hina
      exact absurd hina (by simp)
    have hjb' : vecC ω ((ptCodes ())[b]!) ∉ solSub ω F j' := by
      intro hmem
      have h1 : memC (ptCodes ()) F[j']! ((ptCodes ())[b]!) = true :=
        (d4s_memC_iff hω hσω hσ hK hT hj' hb_lt).mpr hmem
      rw [← d4s_inc_eval hjF' hb_size] at h1
      rw [h1] at hinb
      exact absurd hinb (by simp)
    have h1_lt : (ptCodes ())[a]! ^^^ (ptCodes ())[b]! < 65536 := xor_lt ha_lt hb_lt
    have h2_lt : (ptCodes ())[a]! ^^^ smulC 2 ((ptCodes ())[b]!) < 65536 :=
      xor_lt ha_lt (smulC_lt (show 2 < 4 by decide) _)
    have h3_lt : (ptCodes ())[a]! ^^^ smulC 3 ((ptCodes ())[b]!) < 65536 :=
      xor_lt ha_lt (smulC_lt (show 3 < 4 by decide) _)
    have hv1 : vecC ω ((ptCodes ())[a]! ^^^ (ptCodes ())[b]!) ∉ solSub ω F j' := by
      intro hmem
      have h1 : memC (ptCodes ()) F[j']! ((ptCodes ())[a]! ^^^ (ptCodes ())[b]!) = true :=
        (d4s_memC_iff hω hσω hσ hK hT hj' h1_lt).mpr hmem
      rw [h1] at hm1
      exact absurd hm1 (by simp)
    have hv2 : vecC ω ((ptCodes ())[a]! ^^^ smulC 2 ((ptCodes ())[b]!)) ∉ solSub ω F j' := by
      intro hmem
      have h1 : memC (ptCodes ()) F[j']! ((ptCodes ())[a]! ^^^ smulC 2 ((ptCodes ())[b]!)) =
          true := (d4s_memC_iff hω hσω hσ hK hT hj' h2_lt).mpr hmem
      rw [h1] at hm2
      exact absurd hm2 (by simp)
    have hv3 : vecC ω ((ptCodes ())[a]! ^^^ smulC 3 ((ptCodes ())[b]!)) ∉ solSub ω F j' := by
      intro hmem
      have h1 : memC (ptCodes ()) F[j']! ((ptCodes ())[a]! ^^^ smulC 3 ((ptCodes ())[b]!)) =
          true := (d4s_memC_iff hω hσω hσ hK hT hj' h3_lt).mpr hmem
      rw [h1] at hm3
      exact absurd hm3 (by simp)
    have hv1' : vecC ω ((ptCodes ())[a]!) + vecC ω ((ptCodes ())[b]!) ∉ solSub ω F j' := by
      rw [← vecC_xor]
      exact hv1
    have hv2' : vecC ω ((ptCodes ())[a]!) + ω • vecC ω ((ptCodes ())[b]!) ∉
        solSub ω F j' := by
      have he : vecC ω ((ptCodes ())[a]!) + ω • vecC ω ((ptCodes ())[b]!) =
          vecC ω ((ptCodes ())[a]! ^^^ smulC 2 ((ptCodes ())[b]!)) := by
        rw [vecC_xor, vecC_smulC hω (show 2 < 4 by decide)]
        rfl
      rw [he]
      exact hv2
    have hv3' : vecC ω ((ptCodes ())[a]!) + (ω * ω) • vecC ω ((ptCodes ())[b]!) ∉
        solSub ω F j' := by
      have he : vecC ω ((ptCodes ())[a]!) + (ω * ω) • vecC ω ((ptCodes ())[b]!) =
          vecC ω ((ptCodes ())[a]! ^^^ smulC 3 ((ptCodes ())[b]!)) := by
        rw [vecC_xor, vecC_smulC hω (show 3 < 4 by decide)]
        rw [show enc ω 3 = ω * ω from by rw [show enc ω 3 = ω + 1 from rfl, ← hω]]
      rw [he]
      exact hv3
    have hfive : ∀ (x y : K), x ≠ 0 ∨ y ≠ 0 →
        x • vecC ω ((ptCodes ())[a]!) + y • vecC ω ((ptCodes ())[b]!) ∉ solSub ω F j' :=
      fun x y hxy => d4s_smul_add_not_mem hK hω hja' hjb' hv1' hv2' hv3' hxy
    have hbot : (K ∙ vecC ω ((ptCodes ())[a]!) ⊔ K ∙ vecC ω ((ptCodes ())[b]!)) ⊓
        solSub ω F j' = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro w hw
      obtain ⟨hw1, hw2⟩ := Submodule.mem_inf.mp hw
      obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hw1
      obtain ⟨A, rfl⟩ := Submodule.mem_span_singleton.mp hx
      obtain ⟨B, rfl⟩ := Submodule.mem_span_singleton.mp hy
      by_cases hA : A = 0
      · by_cases hB : B = 0
        · rw [hA, hB, zero_smul, zero_smul, add_zero]
        · exact absurd hw2 (hfive A B (Or.inr hB))
      · exact absurd hw2 (hfive A B (Or.inl hA))
    have hdisj : Disjoint (K ∙ vecC ω ((ptCodes ())[a]!)) (K ∙ vecC ω ((ptCodes ())[b]!)) := by
      rw [Submodule.disjoint_def]
      intro w hwu hwv
      obtain ⟨A, hA⟩ := Submodule.mem_span_singleton.mp hwu
      obtain ⟨B, hB⟩ := Submodule.mem_span_singleton.mp hwv
      by_cases hA0 : A = 0
      · rw [hA0, zero_smul] at hA
        exact hA.symm
      · by_cases hB0 : B = 0
        · rw [hB0, zero_smul] at hB
          exact hB.symm
        · exfalso
          have hzero : A • vecC ω ((ptCodes ())[a]!) + B • vecC ω ((ptCodes ())[b]!) = 0 := by
            rw [show B • vecC ω ((ptCodes ())[b]!) = A • vecC ω ((ptCodes ())[a]!) from
              hB.trans hA.symm]
            exact d4s_add_self _
          exact (hfive A B (Or.inl hA0)) (hzero ▸ Submodule.zero_mem _)
    have hL2 : finrank K ↥(K ∙ vecC ω ((ptCodes ())[a]!) ⊔
        K ∙ vecC ω ((ptCodes ())[b]!)) = 2 := by
      have hna : vecC ω ((ptCodes ())[a]!) ≠ 0 :=
        d4s_ptCode_ne_zero hσ hK hω hσω (d4s_getElem!_mem_ptCodes ha_size)
      have hnb : vecC ω ((ptCodes ())[b]!) ≠ 0 :=
        d4s_ptCode_ne_zero hσ hK hω hσω (d4s_getElem!_mem_ptCodes hb_size)
      have h := Submodule.finrank_sup_add_finrank_inf_eq (K ∙ vecC ω ((ptCodes ())[a]!))
        (K ∙ vecC ω ((ptCodes ())[b]!))
      rw [hdisj.eq_bot, finrank_bot, finrank_span_singleton hna,
        finrank_span_singleton hnb] at h
      omega
    have hLle : (K ∙ vecC ω ((ptCodes ())[a]!) ⊔ K ∙ vecC ω ((ptCodes ())[b]!)) ≤
        solSub ω F j :=
      sup_le ((Submodule.span_singleton_le_iff_mem _ _).mpr hja)
        ((Submodule.span_singleton_le_iff_mem _ _).mpr hjb)
    have hAL : (solSub ω F j ⊓ solSub ω F j') ⊓
        (K ∙ vecC ω ((ptCodes ())[a]!) ⊔ K ∙ vecC ω ((ptCodes ())[b]!)) = ⊥ := by
      refine le_antisymm ?_ bot_le
      intro w hw
      obtain ⟨⟨hwj, hwj'⟩, hwL⟩ := Submodule.mem_inf.mp hw
      have h1 : w ∈ (K ∙ vecC ω ((ptCodes ())[a]!) ⊔ K ∙ vecC ω ((ptCodes ())[b]!)) ⊓
          solSub ω F j' := Submodule.mem_inf.mpr ⟨hwL, hwj'⟩
      rw [hbot] at h1
      exact h1
    have hdim := Submodule.finrank_sup_add_finrank_inf_eq (solSub ω F j ⊓ solSub ω F j')
      (K ∙ vecC ω ((ptCodes ())[a]!) ⊔ K ∙ vecC ω ((ptCodes ())[b]!))
    rw [hAL, finrank_bot, hL2] at hdim
    have hsup : finrank K ↥((solSub ω F j ⊓ solSub ω F j') ⊔
        (K ∙ vecC ω ((ptCodes ())[a]!) ⊔ K ∙ vecC ω ((ptCodes ())[b]!))) ≤ 4 := by
      have hle := Submodule.finrank_mono (sup_le inf_le_left hLle :
        (solSub ω F j ⊓ solSub ω F j') ⊔
          (K ∙ vecC ω ((ptCodes ())[a]!) ⊔ K ∙ vecC ω ((ptCodes ())[b]!)) ≤ solSub ω F j)
      rwa [d4s_finrank_solSub hσ hK hω hσω hT hj] at hle
    omega
  · intro htri
    obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := d4s_triTest_spec (F := F) htri
    have haP : a ∈ (mkTabs (ptCodes ()) F).solPts[j]! := (Array.mem_filter.mp ha).1
    have hbP : b ∈ (mkTabs (ptCodes ()) F).solPts[j]! := (Array.mem_filter.mp hb).1
    have hcP : c ∈ (mkTabs (ptCodes ()) F).solPts[j]! := (Array.mem_filter.mp hc).1
    have hina : ((mkTabs (ptCodes ()) F).inc[j']!)[a]! = true := (Array.mem_filter.mp ha).2
    have hinb : ((mkTabs (ptCodes ()) F).inc[j']!)[b]! = true := (Array.mem_filter.mp hb).2
    have hinc : ((mkTabs (ptCodes ()) F).inc[j']!)[c]! = true := (Array.mem_filter.mp hc).2
    obtain ⟨ha_size, ha_memC⟩ := (d4s_mem_solPts_mkTabs (F := F) (hj := hjF)).mp haP
    obtain ⟨hb_size, hb_memC⟩ := (d4s_mem_solPts_mkTabs (F := F) (hj := hjF)).mp hbP
    obtain ⟨hc_size, hc_memC⟩ := (d4s_mem_solPts_mkTabs (F := F) (hj := hjF)).mp hcP
    have ha_lt : (ptCodes ())[a]! < 65536 := by
      rw [d4s_getElem!_eq_getElem (ptCodes ()) ha_size]
      exact (mem_ptCodes.mp (Array.getElem_mem ha_size)).1
    have hb_lt : (ptCodes ())[b]! < 65536 := by
      rw [d4s_getElem!_eq_getElem (ptCodes ()) hb_size]
      exact (mem_ptCodes.mp (Array.getElem_mem hb_size)).1
    have hc_lt : (ptCodes ())[c]! < 65536 := by
      rw [d4s_getElem!_eq_getElem (ptCodes ()) hc_size]
      exact (mem_ptCodes.mp (Array.getElem_mem hc_size)).1
    have hmem_a : vecC ω ((ptCodes ())[a]!) ∈ solSub ω F j ⊓ solSub ω F j' := by
      refine Submodule.mem_inf.mpr ⟨(d4s_memC_iff hω hσω hσ hK hT hj ha_lt).mp ha_memC, ?_⟩
      rw [d4s_inc_eval hjF' ha_size] at hina
      exact (d4s_memC_iff hω hσω hσ hK hT hj' ha_lt).mp hina
    have hmem_b : vecC ω ((ptCodes ())[b]!) ∈ solSub ω F j ⊓ solSub ω F j' := by
      refine Submodule.mem_inf.mpr ⟨(d4s_memC_iff hω hσω hσ hK hT hj hb_lt).mp hb_memC, ?_⟩
      rw [d4s_inc_eval hjF' hb_size] at hinb
      exact (d4s_memC_iff hω hσω hσ hK hT hj' hb_lt).mp hinb
    have hmem_c : vecC ω ((ptCodes ())[c]!) ∈ solSub ω F j ⊓ solSub ω F j' := by
      refine Submodule.mem_inf.mpr ⟨(d4s_memC_iff hω hσω hσ hK hT hj hc_lt).mp hc_memC, ?_⟩
      rw [d4s_inc_eval hjF' hc_size] at hinc
      exact (d4s_memC_iff hω hσω hσ hK hT hj' hc_lt).mp hinc
    have hP_a : (ptCodes ())[a]! ∈ ptCodes () := d4s_getElem!_mem_ptCodes ha_size
    have hP_b : (ptCodes ())[b]! ∈ ptCodes () := d4s_getElem!_mem_ptCodes hb_size
    have hP_c : (ptCodes ())[c]! ∈ ptCodes () := d4s_getElem!_mem_ptCodes hc_size
    let z : Fin 3 → (Fin 4 ⊕ Fin 4 → K) :=
      ![vecC ω ((ptCodes ())[a]!), vecC ω ((ptCodes ())[b]!), vecC ω ((ptCodes ())[c]!)]
    have hz0 : z 0 = vecC ω ((ptCodes ())[a]!) := rfl
    have hz1 : z 1 = vecC ω ((ptCodes ())[b]!) := rfl
    have hz2 : z 2 = vecC ω ((ptCodes ())[c]!) := rfl
    have hk3 : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2 := by
      intro k
      fin_cases k <;> simp
    have hzmem : ∀ k, z k ∈ solSub ω F j ⊓ solSub ω F j' := by
      intro k
      rcases hk3 k with rfl | rfl | rfl
      · exact hmem_a
      · exact hmem_b
      · exact hmem_c
    have hzdiag : ∀ k, flipHerm σ (z k) (z k) = 1 := by
      intro k
      rcases hk3 k with rfl | rfl | rfl
      · exact d4s_ptCode_diag hσ hK hω hσω hP_a
      · exact d4s_ptCode_diag hσ hK hω hσω hP_b
      · exact d4s_ptCode_diag hσ hK hω hσω hP_c
    have hzorth : ∀ k l, k ≠ l → flipHerm σ (z k) (z l) = 0 := by
      intro k l hkl
      rcases hk3 k with rfl | rfl | rfl <;> rcases hk3 l with rfl | rfl | rfl
      · exact (hkl rfl).elim
      · exact d4s_ptCode_flipHerm_eq_zero hω hσω hab
      · exact d4s_ptCode_flipHerm_eq_zero hω hσω hac
      · rw [flipHerm_eq_zero_iff hσ.invol]
        exact d4s_ptCode_flipHerm_eq_zero hω hσω hab
      · exact (hkl rfl).elim
      · exact d4s_ptCode_flipHerm_eq_zero hω hσω hbc
      · rw [flipHerm_eq_zero_iff hσ.invol]
        exact d4s_ptCode_flipHerm_eq_zero hω hσω hac
      · rw [flipHerm_eq_zero_iff hσ.invol]
        exact d4s_ptCode_flipHerm_eq_zero hω hσω hbc
      · exact (hkl rfl).elim
    have hWle : Submodule.span K (Set.range z) ≤ solSub ω F j ⊓ solSub ω F j' := by
      rw [Submodule.span_le]
      rintro v ⟨k, rfl⟩
      exact hzmem k
    have hW3 : finrank K ↥(Submodule.span K (Set.range z)) = 3 := by
      rw [finrank_span_eq_card (d4s_linearIndependent_of_orth z hzdiag hzorth)]
      simp
    have hge : 3 ≤ finrank K ↥(solSub ω F j ⊓ solSub ω F j') := by
      rw [← hW3]
      exact Submodule.finrank_mono hWle
    have hne4 : finrank K ↥(solSub ω F j ⊓ solSub ω F j') ≠ 4 := by
      intro h4
      have heq : solSub ω F j ⊓ solSub ω F j' = solSub ω F j :=
        Submodule.eq_of_le_of_finrank_eq inf_le_left
          (by rw [h4, d4s_finrank_solSub hσ hK hω hσω hT hj])
      have hle : solSub ω F j ≤ solSub ω F j' := by
        rw [← heq]
        exact inf_le_right
      have heq2 : solSub ω F j = solSub ω F j' :=
        Submodule.eq_of_le_of_finrank_eq hle
          (by rw [d4s_finrank_solSub hσ hK hω hσω hT hj,
            d4s_finrank_solSub hσ hK hω hσω hT hj'])
      exact hne (d4s_solSub_injOn hσ hK hω hσω hT hj hj' heq2)
    have hle4 : finrank K ↥(solSub ω F j ⊓ solSub ω F j') ≤ 4 := by
      have hle := Submodule.finrank_mono (inf_le_left :
        solSub ω F j ⊓ solSub ω F j' ≤ solSub ω F j)
      rwa [d4s_finrank_solSub hσ hK hω hσω hT hj] at hle
    omega

end DimInf

theorem inc_mkTabs {j i : ℕ} (hj : j < F.size) (hi : i < (ptCodes ()).size) :
    ((mkTabs (ptCodes ()) F).inc[j]!)[i]! = memC (ptCodes ()) F[j]! (ptCodes ())[i]! :=
  d4s_inc_eval hj hi

theorem mem_solPts_mkTabs {j i : ℕ} (hj : j < F.size) :
    i ∈ (mkTabs (ptCodes ()) F).solPts[j]! ↔
      i < (ptCodes ()).size ∧ memC (ptCodes ()) F[j]! (ptCodes ())[i]! = true :=
  d4s_mem_solPts_mkTabs hj

section Omega

variable (hω : ω * ω = ω + 1) (hσω : σ ω = ω + 1)
include hω hσω

theorem isFlipflopSub_solSub [Finite K] (hσ : IsUnitaryInvolution σ) (hK : Nat.card K = 4)
    (hT : Checks F) {j : ℕ} (hj : j < 4480) : IsFlipflopSub σ (solSub ω F j) :=
  d4s_isFlipflopSub_solSub hσ hK hω hσω hT hj

theorem finrank_solSub [Finite K] (hσ : IsUnitaryInvolution σ) (hK : Nat.card K = 4)
    (hT : Checks F) {j : ℕ} (hj : j < 4480) : finrank K (solSub ω F j) = 4 :=
  d4s_finrank_solSub hσ hK hω hσω hT hj

theorem memC_iff [Finite K] (hσ : IsUnitaryInvolution σ) (hK : Nat.card K = 4)
    (hT : Checks F) {j : ℕ} (hj : j < 4480) {v : ℕ} (hv : v < 65536) :
    memC (ptCodes ()) F[j]! v = true ↔ vecC ω v ∈ solSub ω F j :=
  d4s_memC_iff hω hσω hσ hK hT hj hv

theorem solSub_injOn [Finite K] (hσ : IsUnitaryInvolution σ) (hK : Nat.card K = 4)
    (hT : Checks F) {j j' : ℕ} (hj : j < 4480) (hj' : j' < 4480)
    (h : solSub ω F j = solSub ω F j') : j = j' :=
  d4s_solSub_injOn hσ hK hω hσω hT hj hj' h

theorem exists_solSub_eq [Finite K] (hσ : IsUnitaryInvolution σ) (hK : Nat.card K = 4)
    (hT : Checks F) {S : Submodule K (Fin 4 ⊕ Fin 4 → K)} (hS : IsFlipflopSub σ S)
    (h4 : finrank K S = 4) : ∃ j < 4480, S = solSub ω F j :=
  d4s_exists_solSub_eq hσ hK hω hσω hT hS h4

theorem finrank_inf_solSub_eq_three_iff [Finite K] (hσ : IsUnitaryInvolution σ)
    (hK : Nat.card K = 4) (hT : Checks F) {j j' : ℕ} (hj : j < 4480) (hj' : j' < 4480)
    (hne : j ≠ j') : finrank K ↥(solSub ω F j ⊓ solSub ω F j') = 3 ↔
      triTest (mkTabs (ptCodes ()) F) j j' = true :=
  d4s_inf_solSub_eq_three_iff hσ hK hω hσω hT hj hj' hne

end Omega

end CFSG.ClassicalInvolution.PhanDn.D4Q2

