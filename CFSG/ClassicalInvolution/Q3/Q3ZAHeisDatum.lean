module

public import CFSG.ClassicalInvolution.Q3.Q3ZAHeisPres

public section

namespace CFSG.ClassicalInvolution.Q3.Q3ZA

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat)
open scoped MatrixGroups commutatorElement
open Matrix

@[expose] def heisGens : Set Heis :=
  {Heis.center, Heis.vec bE0, Heis.vec bE1, Heis.vec bF0, Heis.vec bF1}

theorem heis_decomp (m : Heis) : m = (⟨m.c, 0⟩ : Heis) * Heis.vec m.v := by
  refine Heis.ext ?_ ?_
  · simp [Heis.mul_def, Heis.vec, form_zero_left]
  · simp [Heis.mul_def, Heis.vec]

theorem heis_closure_center (a : F3) : (⟨a, 0⟩ : Heis) ∈ Subgroup.closure heisGens := by
  rcases eq_zero_or_one_or_neg_one_f3 a with rfl | rfl | rfl
  · rw [show (⟨0, 0⟩ : Heis) = 1 from rfl]
    exact Subgroup.one_mem _
  · exact Subgroup.subset_closure (Or.inl rfl)
  · have h : (⟨-1, 0⟩ : Heis) = Heis.center⁻¹ := by
      refine Heis.ext ?_ ?_ <;> simp [Heis.inv_def, Heis.center]
    rw [h]
    exact Subgroup.inv_mem _ (Subgroup.subset_closure (Or.inl rfl))

theorem heis_closure_vec_smul {b : V4} (hb : Heis.vec b ∈ Subgroup.closure heisGens) (x : F3) :
    Heis.vec (x • b) ∈ Subgroup.closure heisGens := by
  rcases eq_zero_or_one_or_neg_one_f3 x with rfl | rfl | rfl
  · rw [zero_smul, show Heis.vec 0 = 1 from rfl]
    exact Subgroup.one_mem _
  · rwa [one_smul]
  · rw [neg_smul, one_smul, ← vec_inv]
    exact Subgroup.inv_mem _ hb

theorem heis_closure_vec_add {v w : V4} (hv : Heis.vec v ∈ Subgroup.closure heisGens)
    (hw : Heis.vec w ∈ Subgroup.closure heisGens) :
    Heis.vec (v + w) ∈ Subgroup.closure heisGens := by
  have h : Heis.vec (v + w) = (⟨-(2 * form v w), 0⟩ : Heis) * (Heis.vec v * Heis.vec w) := by
    refine Heis.ext ?_ ?_
    · simp [Heis.mul_def, Heis.vec, form_zero_left]
    · simp [Heis.mul_def, Heis.vec]
  rw [h]
  exact Subgroup.mul_mem _ (heis_closure_center _) (Subgroup.mul_mem _ hv hw)

theorem heis_closure_vec (v : V4) : Heis.vec v ∈ Subgroup.closure heisGens := by
  have hb0 : Heis.vec bE0 ∈ Subgroup.closure heisGens :=
    Subgroup.subset_closure (Or.inr (Or.inl rfl))
  have hb1 : Heis.vec bE1 ∈ Subgroup.closure heisGens :=
    Subgroup.subset_closure (Or.inr (Or.inr (Or.inl rfl)))
  have hf0 : Heis.vec bF0 ∈ Subgroup.closure heisGens :=
    Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have hf1 : Heis.vec bF1 ∈ Subgroup.closure heisGens :=
    Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  have hv : v = v (Sum.inl 0) • bE0 + v (Sum.inl 1) • bE1 + v (Sum.inr 0) • bF0 +
      v (Sum.inr 1) • bF1 := by
    funext i
    rcases i with i | i <;> fin_cases i <;> simp
  rw [hv]
  exact heis_closure_vec_add (heis_closure_vec_add (heis_closure_vec_add
    (heis_closure_vec_smul hb0 _) (heis_closure_vec_smul hb1 _)) (heis_closure_vec_smul hf0 _))
    (heis_closure_vec_smul hf1 _)

theorem heis_closure_eq_top : Subgroup.closure heisGens = ⊤ := by
  rw [eq_top_iff]
  intro m _
  rw [heis_decomp m]
  exact Subgroup.mul_mem _ (heis_closure_center _) (heis_closure_vec _)

@[expose] noncomputable def sp4Gens : Set (StatedSp 2 F3) :=
  {sbU, sbL, longBlock F3 2 1 uSL, longBlock F3 2 1 lSL}

theorem map_SL2_mem_of {H : Type} [Group H] (f : SL(2, F3) →* H) (T : Subgroup H)
    (hU : f uSL ∈ T) (hL : f lSL ∈ T) (g : SL(2, F3)) : f g ∈ T := by
  have hc : ∀ c : F3, f (usl c) ∈ T ∧ f (lsl c) ∈ T := by
    intro c
    rcases eq_zero_or_one_or_neg_one_f3 c with rfl | rfl | rfl
    · rw [usl_zero, lsl_zero, map_one]
      exact ⟨T.one_mem, T.one_mem⟩
    · exact ⟨hU, hL⟩
    · refine ⟨?_, ?_⟩
      · rw [← usl_inv, map_inv]
        exact T.inv_mem hU
      · rw [← lsl_inv, map_inv]
        exact T.inv_mem hL
  have hle : Subgroup.closure (Set.range (CFSG.LieType.Steinberg.sl2Upper : F3 → SL(2, F3)) ∪
      Set.range (CFSG.LieType.Steinberg.sl2Lower : F3 → SL(2, F3))) ≤ T.comap f := by
    rw [Subgroup.closure_le]
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · exact (hc c).1
    · exact (hc c).2
  exact hle (CFSG.LieType.Steinberg.Sp.mem_closure_sl2 g)

theorem sp4Gens_closure : Subgroup.closure sp4Gens = ⊤ := by
  have hsb : ∀ g : SL(2, F3), sb g ∈ Subgroup.closure sp4Gens := fun g =>
    map_SL2_mem_of sb _ (Subgroup.subset_closure (Or.inl rfl))
      (Subgroup.subset_closure (Or.inr (Or.inl rfl))) g
  have hlb : ∀ g : SL(2, F3), longBlock F3 2 1 g ∈ Subgroup.closure sp4Gens := fun g =>
    map_SL2_mem_of (longBlock F3 2 1) _
      (Subgroup.subset_closure (Or.inr (Or.inr (Or.inl rfl))))
      (Subgroup.subset_closure (Or.inr (Or.inr (Or.inr rfl)))) g
  rw [eq_top_iff, ← shortBlock_sup_longBlock_eq_top F3]
  refine sup_le ?_ ?_
  · rintro _ ⟨g, rfl⟩
    exact hsb g
  · rintro _ ⟨g, rfl⟩
    exact hlb g

section Gen

variable {G : Type} [Group G] {θ : StatedSp 2 F3 →* G} {φ : Heis →* G}

theorem act_of_gens
    (h : ∀ s ∈ sp4Gens, ∀ x ∈ heisGens, θ s * φ x * (θ s)⁻¹ = φ (heisAct s x)) :
    ∀ (s : StatedSp 2 F3) (x : Heis), θ s * φ x * (θ s)⁻¹ = φ (heisAct s x) := by
  have h1 : ∀ s ∈ sp4Gens, ∀ x, θ s * φ x * (θ s)⁻¹ = φ (heisAct s x) := by
    intro s hs
    have hfg : (MulAut.conj (θ s)).toMonoidHom.comp φ = φ.comp (heisAct s).toMonoidHom :=
      MonoidHom.eq_of_eqOn_dense heis_closure_eq_top fun x hx => h s hs x hx
    intro x
    exact DFunLike.congr_fun hfg x
  let T : Subgroup (StatedSp 2 F3) :=
    { carrier := {s | ∀ x, θ s * φ x * (θ s)⁻¹ = φ (heisAct s x)}
      one_mem' := by
        intro x
        simp
      mul_mem' := by
        intro s t hs ht x
        calc θ (s * t) * φ x * (θ (s * t))⁻¹ = θ s * (θ t * φ x * (θ t)⁻¹) * (θ s)⁻¹ := by
              simp only [map_mul, _root_.mul_inv_rev, mul_assoc]
          _ = θ s * φ (heisAct t x) * (θ s)⁻¹ := by rw [ht x]
          _ = φ (heisAct s (heisAct t x)) := hs _
          _ = φ (heisAct (s * t) x) := by rw [map_mul]; rfl
      inv_mem' := by
        intro s hs x
        have h2 := hs (heisAct s⁻¹ x)
        have h3 : heisAct s (heisAct s⁻¹ x) = x := by
          rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
        rw [h3] at h2
        calc θ s⁻¹ * φ x * (θ s⁻¹)⁻¹ = (θ s)⁻¹ * φ x * θ s := by simp only [map_inv, inv_inv]
          _ = (θ s)⁻¹ * (θ s * φ (heisAct s⁻¹ x) * (θ s)⁻¹) * θ s := by rw [h2]
          _ = φ (heisAct s⁻¹ x) := by group }
  have hle : Subgroup.closure sp4Gens ≤ T := (Subgroup.closure_le T).2 fun s hs => h1 s hs
  intro s x
  have hs' : s ∈ Subgroup.closure sp4Gens := by
    rw [sp4Gens_closure]
    exact Subgroup.mem_top s
  have hmem : s ∈ T := hle hs'
  exact hmem x

end Gen

theorem heisAct_center (s : StatedSp 2 F3) : heisAct s Heis.center = Heis.center := by
  refine Heis.ext rfl ?_
  show (mat 2 F3 s).mulVec 0 = 0
  exact Matrix.mulVec_zero _

theorem heisAct_vec (s : StatedSp 2 F3) (v : V4) :
    heisAct s (Heis.vec v) = Heis.vec (mat 2 F3 s *ᵥ v) := rfl

theorem vec_add_eq (v w : V4) :
    Heis.vec (v + w) = (⟨-(2 * form v w), 0⟩ : Heis) * (Heis.vec v * Heis.vec w) := by
  refine Heis.ext ?_ ?_
  · simp [Heis.mul_def, Heis.vec, form_zero_left]
  · simp [Heis.mul_def, Heis.vec]

theorem form_E1_F1 : form bE1 bF1 = 1 := form_single_inl_inr 1

theorem lb1U_e0 : mat 2 F3 (longBlock F3 2 1 uSL) *ᵥ bE0 = bE0 :=
  lb_mulVec_other 1 uSL (by simp [coords])

theorem lb1U_f0 : mat 2 F3 (longBlock F3 2 1 uSL) *ᵥ bF0 = bF0 :=
  lb_mulVec_other 1 uSL (by simp [coords])

theorem lb1U_e1 : mat 2 F3 (longBlock F3 2 1 uSL) *ᵥ bE1 = bE1 := by
  rw [lb_mulVec_inl 1 uSL]
  simp [uSL]

theorem lb1U_f1 : mat 2 F3 (longBlock F3 2 1 uSL) *ᵥ bF1 = bE1 + bF1 := by
  rw [lb_mulVec_inr 1 uSL]
  simp [uSL]

theorem lb1L_e0 : mat 2 F3 (longBlock F3 2 1 lSL) *ᵥ bE0 = bE0 :=
  lb_mulVec_other 1 lSL (by simp [coords])

theorem lb1L_f0 : mat 2 F3 (longBlock F3 2 1 lSL) *ᵥ bF0 = bF0 :=
  lb_mulVec_other 1 lSL (by simp [coords])

theorem lb1L_e1 : mat 2 F3 (longBlock F3 2 1 lSL) *ᵥ bE1 = bE1 + bF1 := by
  rw [lb_mulVec_inl 1 lSL]
  simp [lSL]

theorem lb1L_f1 : mat 2 F3 (longBlock F3 2 1 lSL) *ᵥ bF1 = bF1 := by
  rw [lb_mulVec_inr 1 lSL]
  simp [lSL]

section Action

variable {G : Type} [Group G]

structure HeisAction (θ : StatedSp 2 F3 →* G) (z e0 e1 f0 f1 : G) : Prop where
  U_z : Commute (θ sbU) z
  U_e0 : θ sbU * e0 * (θ sbU)⁻¹ = e0
  U_e1 : θ sbU * e1 * (θ sbU)⁻¹ = e1 * e0
  U_f0 : θ sbU * f0 * (θ sbU)⁻¹ = f0 * f1⁻¹
  U_f1 : θ sbU * f1 * (θ sbU)⁻¹ = f1
  L_z : Commute (θ sbL) z
  L_e0 : θ sbL * e0 * (θ sbL)⁻¹ = e0 * e1
  L_e1 : θ sbL * e1 * (θ sbL)⁻¹ = e1
  L_f0 : θ sbL * f0 * (θ sbL)⁻¹ = f0
  L_f1 : θ sbL * f1 * (θ sbL)⁻¹ = f1 * f0⁻¹
  V_z : Commute (θ (longBlock F3 2 1 uSL)) z
  V_e0 : θ (longBlock F3 2 1 uSL) * e0 * (θ (longBlock F3 2 1 uSL))⁻¹ = e0
  V_e1 : θ (longBlock F3 2 1 uSL) * e1 * (θ (longBlock F3 2 1 uSL))⁻¹ = e1
  V_f0 : θ (longBlock F3 2 1 uSL) * f0 * (θ (longBlock F3 2 1 uSL))⁻¹ = f0
  V_f1 : θ (longBlock F3 2 1 uSL) * f1 * (θ (longBlock F3 2 1 uSL))⁻¹ = z * (e1 * f1)
  W_z : Commute (θ (longBlock F3 2 1 lSL)) z
  W_e0 : θ (longBlock F3 2 1 lSL) * e0 * (θ (longBlock F3 2 1 lSL))⁻¹ = e0
  W_e1 : θ (longBlock F3 2 1 lSL) * e1 * (θ (longBlock F3 2 1 lSL))⁻¹ = z * (e1 * f1)
  W_f0 : θ (longBlock F3 2 1 lSL) * f0 * (θ (longBlock F3 2 1 lSL))⁻¹ = f0
  W_f1 : θ (longBlock F3 2 1 lSL) * f1 * (θ (longBlock F3 2 1 lSL))⁻¹ = f1

theorem heisDatum_of_rels {θ : StatedSp 2 F3 →* G} {z e0 e1 f0 f1 : G}
    (hr : HeisRels z e0 e1 f0 f1) (ha : HeisAction θ z e0 e1 f0 f1) :
    HeisDatum θ z e0 e1 f0 f1 := by
  obtain ⟨φ, hz, h0, h1, h2, h3⟩ := exists_hom_of_rels hr
  refine ⟨φ, hz, h0, h1, h2, h3, act_of_gens ?_⟩
  have hph0 : ph φ bE0 = e0 := h0
  have hph1 : ph φ bE1 = e1 := h1
  have hph2 : ph φ bF0 = f0 := h2
  have hph3 : ph φ bF1 = f1 := h3
  have hEF : ph φ (bE1 + bF1) = z * (e1 * f1) := by
    have h := congrArg φ (vec_add_eq bE1 bF1)
    have e : (-(2 * 1) : F3) = 1 := by linear_combination (-1 : F3) * three_eq_zero_f3
    rw [map_mul, map_mul, form_E1_F1, e, h1, h3] at h
    exact h.trans (by rw [show (⟨1, 0⟩ : Heis) = Heis.center from rfl, hz])
  have hasAct : ∀ {s : StatedSp 2 F3} {b w : V4} {x y : G}, mat 2 F3 s *ᵥ b = w → ph φ b = x →
      ph φ w = y → θ s * x * (θ s)⁻¹ = y →
        θ s * φ (Heis.vec b) * (θ s)⁻¹ = φ (heisAct s (Heis.vec b)) := by
    intro s b w x y hb hx hy h
    rw [heisAct_vec, hb, show φ (Heis.vec b) = x from hx, show φ (Heis.vec w) = y from hy]
    exact h
  have hcen : ∀ {s : StatedSp 2 F3}, Commute (θ s) z →
      θ s * φ Heis.center * (θ s)⁻¹ = φ (heisAct s Heis.center) := by
    intro s hs
    rw [heisAct_center, hz]
    exact mul_inv_eq_iff_eq_mul.2 hs.eq
  have fE0E1 : form bE0 bE1 = 0 := form_E0_E1
  have fE1E0 : form bE1 bE0 = 0 := form_E1_E0
  have fF0nF1 : form bF0 (-bF1) = 0 := by rw [Heis.form_neg_right', form_F0_F1, neg_zero]
  have fF1nF0 : form bF1 (-bF0) = 0 := by rw [Heis.form_neg_right', form_F1_F0, neg_zero]
  have hUe1 : ph φ (bE1 + bE0) = e1 * e0 := by rw [← ph_mul φ fE1E0, hph1, hph0]
  have hUf0 : ph φ (bF0 + -bF1) = f0 * f1⁻¹ := by
    rw [← ph_mul φ fF0nF1, ph_neg, hph2, hph3]
  have hLe0 : ph φ (bE0 + bE1) = e0 * e1 := by rw [← ph_mul φ fE0E1, hph0, hph1]
  have hLf1 : ph φ (bF1 + -bF0) = f1 * f0⁻¹ := by
    rw [← ph_mul φ fF1nF0, ph_neg, hph3, hph2]
  intro s hs x hx
  simp only [sp4Gens, heisGens, Set.mem_insert_iff, Set.mem_singleton_iff] at hs hx
  rcases hs with rfl | rfl | rfl | rfl <;> rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact hcen ha.U_z
  · exact hasAct (sb_usl_e0 1) hph0 hph0 ha.U_e0
  · exact hasAct ((sb_usl_e1 1).trans (by rw [one_smul])) hph1 hUe1 ha.U_e1
  · exact hasAct ((sb_usl_f0 1).trans (by rw [one_smul, sub_eq_add_neg])) hph2 hUf0 ha.U_f0
  · exact hasAct (sb_usl_f1 1) hph3 hph3 ha.U_f1
  · exact hcen ha.L_z
  · exact hasAct ((sb_lsl_e0 1).trans (by rw [one_smul])) hph0 hLe0 ha.L_e0
  · exact hasAct (sb_lsl_e1 1) hph1 hph1 ha.L_e1
  · exact hasAct (sb_lsl_f0 1) hph2 hph2 ha.L_f0
  · exact hasAct ((sb_lsl_f1 1).trans (by rw [one_smul, sub_eq_add_neg])) hph3 hLf1 ha.L_f1
  · exact hcen ha.V_z
  · exact hasAct lb1U_e0 hph0 hph0 ha.V_e0
  · exact hasAct lb1U_e1 hph1 hph1 ha.V_e1
  · exact hasAct lb1U_f0 hph2 hph2 ha.V_f0
  · exact hasAct lb1U_f1 hph3 hEF ha.V_f1
  · exact hcen ha.W_z
  · exact hasAct lb1L_e0 hph0 hph0 ha.W_e0
  · exact hasAct lb1L_e1 hph1 hEF ha.W_e1
  · exact hasAct lb1L_f0 hph2 hph2 ha.W_f0
  · exact hasAct lb1L_f1 hph3 hph3 ha.W_f1

end Action

end CFSG.ClassicalInvolution.Q3.Q3ZA
