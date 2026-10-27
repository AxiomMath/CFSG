module

public import CFSG.ClassicalGroups.Orthogonal.SixPlane.FrameCone
public import CFSG.ClassicalInvolution.Phan.Geometry.ConeQuad

public section

namespace CFSG.ClassicalGroups.Orthogonal.SixPlane

open Module _root_.QuadraticMap CFSG.QuadraticMap

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


private theorem plane_inf_orthogonal_plane (x : FrameVert) :
    x.plane ⊓ LinearMap.BilinForm.orthogonal (polarBilin (Q 6)) x.plane = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  obtain ⟨hv1, hv2⟩ := hv
  obtain ⟨s, t, hst⟩ := Submodule.mem_span_pair.mp (by simpa using hv1)
  have hv2' : polar (Q 6) x.u v = 0 ∧ polar (Q 6) x.w v = 0 :=
    (FrameVert.mem_orthogonal_plane_iff x v).mp (by simpa using hv2)
  obtain ⟨hu, hw⟩ := hv2'
  rw [← hst] at hu hw
  rw [polar_add_right, polar_smul_right, polar_smul_right, polar_self,
    CharTwo.two_nsmul, smul_zero, zero_add, x.polar_u_w] at hu
  rw [polar_add_right, polar_smul_right, polar_smul_right, polar_comm (Q 6) x.w x.u,
    x.polar_u_w, polar_self, CharTwo.two_nsmul, smul_zero, add_zero] at hw
  simp only [smul_eq_mul, mul_one] at hu hw
  rw [Submodule.mem_bot, ← hst, hu, hw]
  simp

private theorem finrank_plane_eq_two (x : FrameVert) :
    finrank (ZMod 2) x.plane = 2 := by
  have h := hullDim_plane x
  unfold hullDim at h
  rw [plane_inf_orthogonal_plane, finrank_bot, add_zero] at h
  exact h

private theorem finrank_sup_three_planes_le_six (x y z : FrameVert) :
    finrank (ZMod 2) ↥(x.plane ⊔ y.plane ⊔ z.plane) ≤ 6 := by
  have h1 := Submodule.finrank_add_le_finrank_add_finrank (x.plane ⊔ y.plane) z.plane
  have h2 := Submodule.finrank_add_le_finrank_add_finrank x.plane y.plane
  rw [finrank_plane_eq_two z] at h1
  rw [finrank_plane_eq_two x, finrank_plane_eq_two y] at h2
  omega

private theorem finrank_inf_orthogonal_plane_le {U : Submodule (ZMod 2) (V 6)} {x : FrameVert}
    (hx : x.plane ≤ U) (hU : finrank (ZMod 2) U ≤ 6) :
    finrank (ZMod 2) ↥(U ⊓ LinearMap.BilinForm.orthogonal (polarBilin (Q 6)) x.plane) ≤ 4 := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq x.plane
    (U ⊓ LinearMap.BilinForm.orthogonal (polarBilin (Q 6)) x.plane)
  have hinf : x.plane ⊓ (U ⊓ LinearMap.BilinForm.orthogonal (polarBilin (Q 6)) x.plane) = ⊥ := by
    rw [← inf_assoc, inf_eq_left.mpr hx, plane_inf_orthogonal_plane]
  have hle : x.plane ⊔ (U ⊓ LinearMap.BilinForm.orthogonal (polarBilin (Q 6)) x.plane) ≤ U :=
    sup_le hx inf_le_left
  have hmono := Submodule.finrank_mono hle
  rw [hinf, finrank_bot, finrank_plane_eq_two x] at h
  have hU6 : finrank (ZMod 2) U ≤ 6 := hU
  omega

private theorem exists_mem_orthogonal_not_mem {U W : Submodule (ZMod 2) (V 6)} {x : FrameVert}
    (hxU : x.plane ≤ U) (hxW : x.plane ≤ W)
    (hU : finrank (ZMod 2) U ≤ 6) (hW : finrank (ZMod 2) W ≤ 6) :
    ∃ m ∈ LinearMap.BilinForm.orthogonal (polarBilin (Q 6)) W, m ∉ U := by
  by_contra h
  push Not at h
  have hLle : LinearMap.BilinForm.orthogonal (polarBilin (Q 6)) W ≤
      U ⊓ LinearMap.BilinForm.orthogonal (polarBilin (Q 6)) x.plane :=
    le_inf (fun m hm => h m hm) (LinearMap.BilinForm.orthogonal_le hxW)
  have hfin := finrank_inf_orthogonal_plane_le hxU hU
  have hdimW : 6 ≤ finrank (ZMod 2) (LinearMap.BilinForm.orthogonal (polarBilin (Q 6)) W) := by
    rw [LinearMap.BilinForm.finrank_orthogonal (nondegenerate_Q 6), finrank_V 6]
    have hW6 : finrank (ZMod 2) W ≤ 6 := hW
    omega
  have hmono := Submodule.finrank_mono hLle
  omega

private theorem exists_framedPair_quad {a b c d : FrameVert}
    (hab : frameGraph.Adj a b) (hbc : frameGraph.Adj b c) (hcd : frameGraph.Adj c d)
    (hda : frameGraph.Adj d a) :
    ∃ (x₁ x₂ : V 6),
      x₁ ∈ LinearMap.BilinForm.orthogonal (polarBilin (Q 6)) ((b.plane ⊔ d.plane) ⊔ a.plane) ∧
      x₂ ∈ LinearMap.BilinForm.orthogonal (polarBilin (Q 6)) ((b.plane ⊔ d.plane) ⊔ c.plane) ∧
      Q 6 x₁ = 1 ∧ Q 6 x₂ = 1 ∧ polar (Q 6) x₁ x₂ = 1 := by
  have hBA : a.plane ≤ LinearMap.BilinForm.orthogonal (polarBilin (Q 6)) b.plane :=
    FrameVert.orth_iff_plane_le_orthogonal.mp (FrameVert.orth_comm.mp hab.2)
  have hAD : a.plane ≤ LinearMap.BilinForm.orthogonal (polarBilin (Q 6)) d.plane :=
    FrameVert.orth_iff_plane_le_orthogonal.mp hda.2
  have hCB : c.plane ≤ LinearMap.BilinForm.orthogonal (polarBilin (Q 6)) b.plane :=
    FrameVert.orth_iff_plane_le_orthogonal.mp hbc.2
  have hCD : c.plane ≤ LinearMap.BilinForm.orthogonal (polarBilin (Q 6)) d.plane :=
    FrameVert.orth_iff_plane_le_orthogonal.mp (FrameVert.orth_comm.mp hcd.2)
  have hA_BD : a.plane ≤
      LinearMap.BilinForm.orthogonal (polarBilin (Q 6)) (b.plane ⊔ d.plane) := by
    rw [orthogonal_sup]
    exact le_inf hBA hAD
  have hC_BD : c.plane ≤
      LinearMap.BilinForm.orthogonal (polarBilin (Q 6)) (b.plane ⊔ d.plane) := by
    rw [orthogonal_sup]
    exact le_inf hCB hCD
  have hBD : hullDim (Q 6) (b.plane ⊔ d.plane) ≤ 6 := by
    have h := hullDim_sup_plane_le (U := b.plane) d
    have hb := hullDim_plane b
    omega
  have hW1_hd : hullDim (Q 6) ((b.plane ⊔ d.plane) ⊔ a.plane) ≤ 8 := by
    have h := hullDim_sup_plane_le_of_le_orthogonal (U := b.plane ⊔ d.plane) (x := a) hA_BD
    omega
  have hW2_hd : hullDim (Q 6) ((b.plane ⊔ d.plane) ⊔ c.plane) ≤ 8 := by
    have h := hullDim_sup_plane_le_of_le_orthogonal (U := b.plane ⊔ d.plane) (x := c) hC_BD
    omega
  obtain ⟨m, hmL2, hmW1⟩ :=
    exists_mem_orthogonal_not_mem (x := b)
      (U := (b.plane ⊔ d.plane) ⊔ a.plane) (W := (b.plane ⊔ d.plane) ⊔ c.plane)
      (le_sup_left.trans le_sup_left) (le_sup_left.trans le_sup_left)
      (finrank_sup_three_planes_le_six b d a) (finrank_sup_three_planes_le_six b d c)
  have hrefl : (polarBilin (Q 6)).IsRefl := (QuadraticMap.isSymm_polarBilin (Q 6)).isRefl
  have hmW1' : m ∉ LinearMap.BilinForm.orthogonal (polarBilin (Q 6))
      (LinearMap.BilinForm.orthogonal (polarBilin (Q 6)) ((b.plane ⊔ d.plane) ⊔ a.plane)) := by
    rwa [LinearMap.BilinForm.orthogonal_orthogonal (nondegenerate_Q 6) hrefl
      ((b.plane ⊔ d.plane) ⊔ a.plane)]
  rw [LinearMap.BilinForm.mem_orthogonal_iff, not_forall] at hmW1'
  push Not at hmW1'
  obtain ⟨l, hl, hlm⟩ := hmW1'
  have hml1 : polar (Q 6) m l = 1 := by
    rw [polar_comm (Q 6) m l]
    exact Fin.eq_one_of_ne_zero (polar (Q 6) l m) hlm
  have hdimV : finrank (ZMod 2) (V 6) = 12 := by
    rw [finrank_V 6]
  have hW1_dim : hullDim (Q 6) ((b.plane ⊔ d.plane) ⊔ a.plane) + 3 ≤
      finrank (ZMod 2) (V 6) := by
    omega
  obtain ⟨x₁, hx₁L1, hmx₁, hx₁Q⟩ :=
    exists_polar_eq_one_Q_eq_one (nondegenerate_Q 6)
      (U := (b.plane ⊔ d.plane) ⊔ a.plane) hW1_dim (z := m) (l := l) hl hml1
  have hx1m : polar (Q 6) x₁ m = 1 := by
    rw [polar_comm (Q 6) x₁ m]
    exact hmx₁
  have hW2_dim : hullDim (Q 6) ((b.plane ⊔ d.plane) ⊔ c.plane) + 3 ≤
      finrank (ZMod 2) (V 6) := by
    omega
  obtain ⟨x₂, hx₂L2, hx₁x₂, hx₂Q⟩ :=
    exists_polar_eq_one_Q_eq_one (nondegenerate_Q 6)
      (U := (b.plane ⊔ d.plane) ⊔ c.plane) hW2_dim (z := x₁) (l := m) hmL2 hx1m
  exact ⟨x₁, x₂, hx₁L1, hx₂L2, hx₁Q, hx₂Q, hx₁x₂⟩

theorem exists_adj_adj_isGoodPair_isGoodPair {a b c d : FrameVert}
    (hab : frameGraph.Adj a b) (hbc : frameGraph.Adj b c) (hcd : frameGraph.Adj c d)
    (hda : frameGraph.Adj d a) :
    ∃ x, frameGraph.Adj b x ∧ frameGraph.Adj d x ∧ IsGoodPair x a ∧ IsGoodPair x c := by
  classical
  obtain ⟨x₁, x₂, hx₁L1, hx₂L2, hx₁Q, hx₂Q, hx₁x₂⟩ :=
    exists_framedPair_quad hab hbc hcd hda
  have hcard : ({b.typ, d.typ} : Finset (Fin 5)).card < (Finset.univ : Finset (Fin 5)).card := by
    have h2 : ({b.typ, d.typ} : Finset (Fin 5)).card ≤ 2 := Finset.card_le_two
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨t, -, ht⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht
  obtain ⟨htb, htd⟩ := ht
  let x : FrameVert :=
    { typ := t, u := x₁, w := x₂, Q_u := hx₁Q, Q_w := hx₂Q, polar_u_w := hx₁x₂ }
  have hbx : frameGraph.Adj b x := by
    refine ⟨Ne.symm htb, ?_⟩
    obtain ⟨h₁, h₂⟩ := (FrameVert.mem_orthogonal_plane_iff b x₁).mp
      (LinearMap.BilinForm.orthogonal_le (le_sup_left.trans le_sup_left) hx₁L1)
    obtain ⟨h₃, h₄⟩ := (FrameVert.mem_orthogonal_plane_iff b x₂).mp
      (LinearMap.BilinForm.orthogonal_le (le_sup_left.trans le_sup_left) hx₂L2)
    exact ⟨h₁, h₃, h₂, h₄⟩
  have hdx : frameGraph.Adj d x := by
    refine ⟨Ne.symm htd, ?_⟩
    obtain ⟨h₁, h₂⟩ := (FrameVert.mem_orthogonal_plane_iff d x₁).mp
      (LinearMap.BilinForm.orthogonal_le (le_sup_right.trans le_sup_left) hx₁L1)
    obtain ⟨h₃, h₄⟩ := (FrameVert.mem_orthogonal_plane_iff d x₂).mp
      (LinearMap.BilinForm.orthogonal_le (le_sup_right.trans le_sup_left) hx₂L2)
    exact ⟨h₁, h₃, h₂, h₄⟩
  have hxa : IsGoodPair x a := by
    have h := (FrameVert.mem_orthogonal_plane_iff a x₁).mp
      (LinearMap.BilinForm.orthogonal_le le_sup_right hx₁L1)
    refine isGoodPair_of_polar_u_eq_zero (z := x) (y := a) ?_ ?_
    · rw [polar_comm (Q 6) x.u a.u]
      exact h.1
    · rw [polar_comm (Q 6) x.u a.w]
      exact h.2
  have hxc : IsGoodPair x c := by
    have h := (FrameVert.mem_orthogonal_plane_iff c x₂).mp
      (LinearMap.BilinForm.orthogonal_le le_sup_right hx₂L2)
    refine isGoodPair_of_polar_w_eq_zero (z := x) (y := c) ?_ ?_
    · rw [polar_comm (Q 6) x.w c.u]
      exact h.1
    · rw [polar_comm (Q 6) x.w c.w]
      exact h.2
  exact ⟨x, hbx, hdx, hxa, hxc⟩

theorem nullLen_four_frameGraph :
    CFSG.ClassicalInvolution.Phan.NullLen
      (fun x => {c : frameGraph.Walk x x | CFSG.Monster.B.Recog.Homotopic c .nil}) 4 := by
  intro u p hp
  cases p with
  | nil => simp at hp
  | cons hab p1 =>
    rename_i b
    cases p1 with
    | nil => simp at hp
    | cons hbc p2 =>
      rename_i c
      cases p2 with
      | nil => simp at hp
      | cons hcd p3 =>
        rename_i d
        cases p3 with
        | nil => simp at hp
        | cons hda p4 =>
          cases p4 with
          | cons _ _ => simp at hp
          | nil =>
            obtain ⟨x, hbx, hdx, hxa, hxc⟩ :=
              exists_adj_adj_isGoodPair_isGoodPair hab hbc hcd hda
            have hcone_cx := preconnected_induce_neighborSet_inter hxc.symm
            have hcone_xa := preconnected_induce_neighborSet_inter hxa
            have h1 : CFSG.ClassicalInvolution.Phan.CycleHomotopic
                (fun x => {c : frameGraph.Walk x x | CFSG.Monster.B.Recog.Homotopic c .nil})
                (CFSG.ClassicalInvolution.Phan.quadWalk hbc hcd hdx hbx.symm) .nil :=
              CFSG.ClassicalInvolution.Phan.cycleHomotopic_quad_rotate_rev _ hbc hcd hdx hbx.symm
                (CFSG.ClassicalInvolution.Phan.cycleHomotopic_quad_of_preconnected _
                  (CFSG.ClassicalInvolution.Phan.nullLen_three_homotopic frameGraph)
                  hcd hdx hbx.symm hbc hcone_cx)
            have h2 : CFSG.ClassicalInvolution.Phan.CycleHomotopic
                (fun x => {c : frameGraph.Walk x x | CFSG.Monster.B.Recog.Homotopic c .nil})
                (CFSG.ClassicalInvolution.Phan.quadWalk hbx hdx.symm hda hab) .nil :=
              CFSG.ClassicalInvolution.Phan.cycleHomotopic_quad_rotate_rev _ hbx hdx.symm hda hab
                (CFSG.ClassicalInvolution.Phan.cycleHomotopic_quad_of_preconnected _
                  (CFSG.ClassicalInvolution.Phan.nullLen_three_homotopic frameGraph)
                  hdx.symm hda hab hbx hcone_xa)
            have hrot : CFSG.ClassicalInvolution.Phan.CycleHomotopic
                (fun x => {c : frameGraph.Walk x x | CFSG.Monster.B.Recog.Homotopic c .nil})
                (CFSG.ClassicalInvolution.Phan.quadWalk hbc hcd hda hab) .nil :=
              CFSG.ClassicalInvolution.Phan.cycleHomotopic_quad_trans _ hbc hcd hdx hbx.symm hda
                hab h1 h2
            exact CFSG.ClassicalInvolution.Phan.cycleHomotopic_quad_rotate_rev _ hab hbc hcd hda
              hrot

end CFSG.ClassicalGroups.Orthogonal.SixPlane
