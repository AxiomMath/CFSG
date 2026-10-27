module

public import CFSG.ClassicalInvolution.Q3.Q3AM289S4LFrame
public import CFSG.ClassicalInvolution.Q3.Q3AM289S4LOver

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM.S4L

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.ClassicalInvolution.Balance.StrongBalance.Orth
open scoped MatrixGroups

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

theorem forall_fin_six {P : Fin 6 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) (h4 : P 4)
    (h5 : P 5) : ∀ j, P j := by
  intro j
  fin_cases j <;> assumption

theorem IsON.on4 {n : ℕ} {w : Fin n → V} (h : IsON Q w) {i₀ i₁ i₂ i₃ : Fin n} (h01 : i₀ ≠ i₁)
    (h02 : i₀ ≠ i₂) (h03 : i₀ ≠ i₃) (h12 : i₁ ≠ i₂) (h13 : i₁ ≠ i₃) (h23 : i₂ ≠ i₃) :
    ON4 Q (w i₀) (w i₁) (w i₂) (w i₃) :=
  ⟨h.q _, h.q _, h.q _, h.q _, h.o _ _ h01, h.o _ _ h02, h.o _ _ h03, h.o _ _ h12, h.o _ _ h13,
    h.o _ _ h23⟩

variable {w : Fin 6 → V}

theorem on4_a (hw : IsON Q w) : ON4 Q (w 0) (w 1) (w 2) (w 3) :=
  hw.on4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem on4_b (hw : IsON Q w) : ON4 Q (w 4) (w 5) (w 0) (w 1) :=
  hw.on4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem on4_c (hw : IsON Q w) : ON4 Q (w 2) (w 3) (w 4) (w 5) :=
  hw.on4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

@[expose] noncomputable def frA (hw : IsON Q w) (h3 : (3 : F) = 0) : Frame Q :=
  adFrame (on4_a hw) h3

@[expose] noncomputable def frB (hw : IsON Q w) (h3 : (3 : F) = 0) : Frame Q :=
  adFrame (on4_b hw) h3

@[expose] noncomputable def frC (hw : IsON Q w) (h3 : (3 : F) = 0) : Frame Q :=
  adFrame (on4_c hw) h3

section Props

variable [Finite F] [FiniteDimensional F V] (hw : IsON Q w) (h3 : (3 : F) = 0)

theorem Cmp_le_perp_a {z : V} (hz : z ∈ Cmp w Q) : z ∈ (frA hw h3).perp := by
  rw [frA, mem_perp_adFrame_iff]
  exact ⟨mem_Cmp_iff.mp hz _ (w_mem_Sp (by decide)), mem_Cmp_iff.mp hz _ (w_mem_Sp (by decide)),
    mem_Cmp_iff.mp hz _ (w_mem_Sp (by decide)), mem_Cmp_iff.mp hz _ (w_mem_Sp (by decide))⟩

theorem Cmp_le_perp_b {z : V} (hz : z ∈ Cmp w Q) : z ∈ (frB hw h3).perp := by
  rw [frB, mem_perp_adFrame_iff]
  exact ⟨mem_Cmp_iff.mp hz _ (w_mem_Sp (by decide)), mem_Cmp_iff.mp hz _ (w_mem_Sp (by decide)),
    mem_Cmp_iff.mp hz _ (w_mem_Sp (by decide)), mem_Cmp_iff.mp hz _ (w_mem_Sp (by decide))⟩

theorem Cmp_le_perp_c {z : V} (hz : z ∈ Cmp w Q) : z ∈ (frC hw h3).perp := by
  rw [frC, mem_perp_adFrame_iff]
  exact ⟨mem_Cmp_iff.mp hz _ (w_mem_Sp (by decide)), mem_Cmp_iff.mp hz _ (w_mem_Sp (by decide)),
    mem_Cmp_iff.mp hz _ (w_mem_Sp (by decide)), mem_Cmp_iff.mp hz _ (w_mem_Sp (by decide))⟩

@[expose] def sgnA (F : Type) [Field F] : Fin 6 → F := ![-1, -1, -1, -1, 1, 1]

@[expose] def sgnB (F : Type) [Field F] : Fin 6 → F := ![-1, -1, 1, 1, -1, -1]

@[expose] def sgnC (F : Type) [Field F] : Fin 6 → F := ![1, 1, -1, -1, -1, -1]

theorem La_a_w (j : Fin 6) : (frA hw h3).La (-1) (w j) = sgnA F j • w j := by
  have hp : ∀ i j' : Fin 6, i ≠ j' → polar Q (w i) (w j') = 0 := hw.o
  unfold frA
  revert j
  refine forall_fin_six ?_ ?_ ?_ ?_ ?_ ?_
  · simpa [sgnA] using La_neg_one_x₀ (on4_a hw) h3
  · simpa [sgnA] using La_neg_one_x₁ (on4_a hw) h3
  · simpa [sgnA] using La_neg_one_x₂ (on4_a hw) h3
  · simpa [sgnA] using La_neg_one_x₃ (on4_a hw) h3
  · rw [La_neg_one_of_mem_perp (on4_a hw) h3 ((mem_perp_adFrame_iff _ _).mpr
      ⟨hp 4 0 (by decide), hp 4 1 (by decide), hp 4 2 (by decide), hp 4 3 (by decide)⟩)]
    simp [sgnA]
  · rw [La_neg_one_of_mem_perp (on4_a hw) h3 ((mem_perp_adFrame_iff _ _).mpr
      ⟨hp 5 0 (by decide), hp 5 1 (by decide), hp 5 2 (by decide), hp 5 3 (by decide)⟩)]
    simp [sgnA]

theorem La_b_w (j : Fin 6) : (frB hw h3).La (-1) (w j) = sgnB F j • w j := by
  have hp : ∀ i j' : Fin 6, i ≠ j' → polar Q (w i) (w j') = 0 := hw.o
  unfold frB
  revert j
  refine forall_fin_six ?_ ?_ ?_ ?_ ?_ ?_
  · simpa [sgnB] using La_neg_one_x₂ (on4_b hw) h3
  · simpa [sgnB] using La_neg_one_x₃ (on4_b hw) h3
  · rw [La_neg_one_of_mem_perp (on4_b hw) h3 ((mem_perp_adFrame_iff _ _).mpr
      ⟨hp 2 4 (by decide), hp 2 5 (by decide), hp 2 0 (by decide), hp 2 1 (by decide)⟩)]
    simp [sgnB]
  · rw [La_neg_one_of_mem_perp (on4_b hw) h3 ((mem_perp_adFrame_iff _ _).mpr
      ⟨hp 3 4 (by decide), hp 3 5 (by decide), hp 3 0 (by decide), hp 3 1 (by decide)⟩)]
    simp [sgnB]
  · simpa [sgnB] using La_neg_one_x₀ (on4_b hw) h3
  · simpa [sgnB] using La_neg_one_x₁ (on4_b hw) h3

theorem La_c_w (j : Fin 6) : (frC hw h3).La (-1) (w j) = sgnC F j • w j := by
  have hp : ∀ i j' : Fin 6, i ≠ j' → polar Q (w i) (w j') = 0 := hw.o
  unfold frC
  revert j
  refine forall_fin_six ?_ ?_ ?_ ?_ ?_ ?_
  · rw [La_neg_one_of_mem_perp (on4_c hw) h3 ((mem_perp_adFrame_iff _ _).mpr
      ⟨hp 0 2 (by decide), hp 0 3 (by decide), hp 0 4 (by decide), hp 0 5 (by decide)⟩)]
    simp [sgnC]
  · rw [La_neg_one_of_mem_perp (on4_c hw) h3 ((mem_perp_adFrame_iff _ _).mpr
      ⟨hp 1 2 (by decide), hp 1 3 (by decide), hp 1 4 (by decide), hp 1 5 (by decide)⟩)]
    simp [sgnC]
  · simpa [sgnC] using La_neg_one_x₀ (on4_c hw) h3
  · simpa [sgnC] using La_neg_one_x₁ (on4_c hw) h3
  · simpa [sgnC] using La_neg_one_x₂ (on4_c hw) h3
  · simpa [sgnC] using La_neg_one_x₃ (on4_c hw) h3

theorem La_a_cmp {z : V} (hz : z ∈ Cmp w Q) : (frA hw h3).La (-1) z = z :=
  La_neg_one_of_mem_perp (on4_a hw) h3 (Cmp_le_perp_a hw h3 hz)

theorem La_b_cmp {z : V} (hz : z ∈ Cmp w Q) : (frB hw h3).La (-1) z = z :=
  La_neg_one_of_mem_perp (on4_b hw) h3 (Cmp_le_perp_b hw h3 hz)

theorem La_c_cmp {z : V} (hz : z ∈ Cmp w Q) : (frC hw h3).La (-1) z = z :=
  La_neg_one_of_mem_perp (on4_c hw) h3 (Cmp_le_perp_c hw h3 hz)

theorem ext_of_w_cmp (hw : IsON Q w) (h2 : (2 : F) ≠ 0) {f g : V ≃ₗ[F] V}
    (hf : ∀ j, f (w j) = g (w j)) (hc : ∀ z ∈ Cmp w Q, f z = g z) : f = g := by
  refine LinearEquiv.ext fun v => ?_
  have hv : v ∈ Sp w F Finset.univ ⊔ Cmp w Q := by
    rw [(isCompl_Cmp hw h2).sup_eq_top]; trivial
  obtain ⟨x, hx, z, hz, rfl⟩ := Submodule.mem_sup.mp hv
  obtain ⟨c, -, rfl⟩ := mem_Sp_iff.mp hx
  rw [map_add, map_add, hc z hz, map_sum, map_sum]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by rw [map_smul, map_smul, hf j]

theorem ic_eq (h2 : (2 : F) ≠ 0) :
    (frC hw h3).La (-1) = (frA hw h3).La (-1) * (frB hw h3).La (-1) := by
  refine ext_of_w_cmp hw h2 (fun j => ?_) (fun z hz => ?_)
  · rw [LinearEquiv.mul_apply, La_b_w, map_smul, La_a_w, La_c_w, smul_smul]
    congr 1
    fin_cases j <;> simp [sgnA, sgnB, sgnC]
  · rw [LinearEquiv.mul_apply, La_b_cmp hw h3 hz, La_a_cmp hw h3 hz, La_c_cmp hw h3 hz]

theorem polar_map_sign {g : V ≃ₗ[F] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {s : F}
    (hs : s * s = 1) {u : V} (hu : g u = s • u) (v : V) : polar Q (g v) u = s * polar Q v u := by
  have e : u = s • g u := by rw [hu, smul_smul, hs, one_smul]
  conv_lhs => rw [e]
  rw [polar_smul_right_eq, polar_map_of_mem hg]

theorem ia_comm_u : (frA hw h3).La (-1) * (frB hw h3).La (Jmat F) =
    (frB hw h3).La (Jmat F) * (frA hw h3).La (-1) := by
  have hg : (frA hw h3).La (-1) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    Frame.La_mem_orthogonalGroup _ _
  have hs : ∀ j, sgnA F j * sgnA F j = 1 := fun j => by fin_cases j <;> simp [sgnA]
  unfold frB
  refine La_J_comm (on4_b hw) h3 ((frA hw h3).La (-1)) ?_ ?_ ?_ ?_ ?_
  · simpa [sgnA] using La_a_w hw h3 4
  · simpa [sgnA] using La_a_w hw h3 5
  · simpa [sgnA] using La_a_w hw h3 0
  · simpa [sgnA] using La_a_w hw h3 1
  · intro v hv
    rw [mem_perp_adFrame_iff] at hv ⊢
    obtain ⟨h4, h5, h0, h1⟩ := hv
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [polar_map_sign hg (hs 4) (La_a_w hw h3 4), h4, mul_zero]
    · rw [polar_map_sign hg (hs 5) (La_a_w hw h3 5), h5, mul_zero]
    · rw [polar_map_sign hg (hs 0) (La_a_w hw h3 0), h0, mul_zero]
    · rw [polar_map_sign hg (hs 1) (La_a_w hw h3 1), h1, mul_zero]

theorem ic_not_mem_scalars (h2 : (2 : F) ≠ 0) : (frC hw h3).La (-1) ∉ scalars F V := by
  intro hmem
  obtain ⟨c, hc⟩ := mem_scalars.mp hmem
  have hne : ∀ i, w i ≠ 0 := fun i h => by
    have := hw.q i
    rw [h, QuadraticMap.map_zero] at this
    exact zero_ne_one this
  have e0 := hc (w 0)
  have e2 := hc (w 2)
  rw [La_c_w] at e0 e2
  have c0 : c = 1 := (smul_left_injective F (hne 0) (by simpa [sgnC] using e0)).symm
  have c2 : c = -1 := (smul_left_injective F (hne 2) (by simpa [sgnC] using e2)).symm
  apply h2
  rw [c0] at c2
  linear_combination c2

theorem Sp_a_le_span : Sp w F {0, 1, 2, 3} ≤ (frA hw h3).span := by
  rw [Sp, Submodule.span_le]
  rintro _ ⟨i, hi, rfl⟩
  have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hi
    exact hi
  rcases hi' with rfl | rfl | rfl | rfl
  · exact ⟨_, (x₀_eq_incl (on4_a hw) h3).symm⟩
  · exact ⟨_, (x₁_eq_incl (on4_a hw) h3).symm⟩
  · exact ⟨_, (x₂_eq_incl (on4_a hw) h3).symm⟩
  · exact ⟨_, (x₃_eq_incl (on4_a hw) h3).symm⟩

theorem Sp_c_le_span : Sp w F {2, 3, 4, 5} ≤ (frC hw h3).span := by
  rw [Sp, Submodule.span_le]
  rintro _ ⟨i, hi, rfl⟩
  have hi' : i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hi
    exact hi
  rcases hi' with rfl | rfl | rfl | rfl
  · exact ⟨_, (x₀_eq_incl (on4_c hw) h3).symm⟩
  · exact ⟨_, (x₁_eq_incl (on4_c hw) h3).symm⟩
  · exact ⟨_, (x₂_eq_incl (on4_c hw) h3).symm⟩
  · exact ⟨_, (x₃_eq_incl (on4_c hw) h3).symm⟩

theorem Sp_cmp_le_perp : Sp w F {4, 5} ⊔ Cmp w Q ≤ (frA hw h3).perp := by
  refine sup_le ?_ fun z hz => Cmp_le_perp_a hw h3 hz
  rw [Sp, Submodule.span_le]
  rintro _ ⟨i, hi, rfl⟩
  have hi' : i = 4 ∨ i = 5 := by
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hi
    exact hi
  have hp : ∀ i j' : Fin 6, i ≠ j' → polar Q (w i) (w j') = 0 := hw.o
  rw [SetLike.mem_coe, frA, mem_perp_adFrame_iff]
  rcases hi' with rfl | rfl
  · exact ⟨hp 4 0 (by decide), hp 4 1 (by decide), hp 4 2 (by decide), hp 4 3 (by decide)⟩
  · exact ⟨hp 5 0 (by decide), hp 5 1 (by decide), hp 5 2 (by decide), hp 5 3 (by decide)⟩

theorem elementaryGroup_le_of_frames (hodd : Odd (Nat.card F)) (hQ : (polarBilin Q).Nondegenerate)
    (hdim : 7 ≤ Module.finrank F V) {H : Subgroup (V ≃ₗ[F] V)}
    (hHO : H ≤ TauCeti.QuadraticMap.orthogonalGroup Q) (h₁ : elemOn Q (frA hw h3).span ≤ H)
    (h₂ : elemOn Q (frC hw h3).span ≤ H) (h₃ : elemOn Q (frA hw h3).perp ≤ H) :
    elementaryGroup Q ≤ H :=
  elementaryGroup_le_of_pairs hodd hQ hdim hw hHO
    ((elemOn_mono_S4L (Sp_a_le_span hw h3)).trans h₁)
    ((elemOn_mono_S4L (Sp_c_le_span hw h3)).trans h₂)
    ((elemOn_mono_S4L (Sp_cmp_le_perp hw h3)).trans h₃)

end Props

section Bundle

variable [Finite F] [FiniteDimensional F V]

@[expose] def VFrames (Q : QuadraticForm F V) : Prop :=
  ∃ Fa Fb Fc : Frame Q,
    Fa.La (-1) * Fb.La (Jmat F) = Fb.La (Jmat F) * Fa.La (-1) ∧
    Fc.La (-1) = Fa.La (-1) * Fb.La (-1) ∧ Fc.La (-1) ∉ scalars F V ∧
    ∀ H : Subgroup (V ≃ₗ[F] V), H ≤ TauCeti.QuadraticMap.orthogonalGroup Q →
      elemOn Q Fa.span ≤ H → elemOn Q Fc.span ≤ H → elemOn Q Fa.perp ≤ H →
        elementaryGroup Q ≤ H

theorem vFrames_of_orthonormal {w : Fin 6 → V} (hodd : Odd (Nat.card F)) (h3 : (3 : F) = 0)
    (hQ : (polarBilin Q).Nondegenerate) (hdim : 7 ≤ Module.finrank F V) (hw : IsON Q w) :
    VFrames Q := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_three h3
  exact ⟨frA hw h3, frB hw h3, frC hw h3, ia_comm_u hw h3, ic_eq hw h3 h2,
    ic_not_mem_scalars hw h3 h2, fun H hHO h₁ h₂ h₃ =>
      elementaryGroup_le_of_frames hw h3 hodd hQ hdim hHO h₁ h₂ h₃⟩

end Bundle

end CFSG.ClassicalInvolution.Q3.Q3AM.S4L
