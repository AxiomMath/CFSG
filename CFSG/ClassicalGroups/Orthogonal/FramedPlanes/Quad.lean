module

public import CFSG.ClassicalGroups.Orthogonal.FramedPlanes.Cone
public import CFSG.ClassicalInvolution.Phan.Geometry.ConeQuad

public section

namespace CFSG.ClassicalGroups.Orthogonal.FramedPlanes

open Module QuadraticMap

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
  {Q : QuadraticForm F V} {ν : F} {n : ℕ}

private theorem orthogonal_sup_eq_inf (B : LinearMap.BilinForm F V) (U W : Submodule F V) :
    B.orthogonal (U ⊔ W) = B.orthogonal U ⊓ B.orthogonal W := by
  refine le_antisymm ?_ ?_
  · exact le_inf (LinearMap.BilinForm.orthogonal_le le_sup_left)
      (LinearMap.BilinForm.orthogonal_le le_sup_right)
  · intro x hx
    obtain ⟨hxU, hxW⟩ := Submodule.mem_inf.mp hx
    rw [LinearMap.BilinForm.mem_orthogonal_iff] at hxU hxW ⊢
    intro y hy
    obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hy
    have h1 : (B u) x = 0 := hxU u hu
    have h2 : (B w) x = 0 := hxW w hw
    rw [map_add, LinearMap.add_apply, h1, h2, add_zero]

private theorem plane_le_orthogonal_sup_of_orthogonal {X Y : Submodule F V}
    {x : FrameVert Q ν n} (hX : x.plane ≤ LinearMap.BilinForm.orthogonal (polarBilin Q) X)
    (hY : x.plane ≤ LinearMap.BilinForm.orthogonal (polarBilin Q) Y) :
    x.plane ≤ LinearMap.BilinForm.orthogonal (polarBilin Q) (X ⊔ Y) := by
  rw [orthogonal_sup_eq_inf]
  exact le_inf hX hY

private theorem hullDim_sup_plane_le_six [Module.Finite F V] [CharP F 2]
    (x y : FrameVert Q ν n) : hullDim Q (x.plane ⊔ y.plane) ≤ 6 := by
  have h := hullDim_sup_plane_le (Q := Q) (U := x.plane) y
  have hx : hullDim Q x.plane = 2 := FrameVert.hullDim_plane x
  omega

private theorem hullDim_sup_plane_le_eight_of_le_orthogonal [Module.Finite F V] [CharP F 2]
    {U : Submodule F V} {x : FrameVert Q ν n}
    (hx : x.plane ≤ LinearMap.BilinForm.orthogonal (polarBilin Q) U)
    (hU : hullDim Q U ≤ 6) : hullDim Q (U ⊔ x.plane) ≤ 8 := by
  have h := hullDim_sup_plane_le_of_le_orthogonal (Q := Q) hx
  omega

private theorem finrank_sup_plane_le_add_two [Module.Finite F V] [CharP F 2]
    (U : Submodule F V) (x : FrameVert Q ν n) :
    finrank F ↥(U ⊔ x.plane) ≤ finrank F ↥U + 2 := by
  have h := Submodule.finrank_add_le_finrank_add_finrank U x.plane
  have hx : finrank F x.plane = 2 := FrameVert.finrank_plane x
  omega

private theorem inf_orthogonal_sup_le_rad_sup {U X Y : Submodule F V}
    (hY : Y ≤ LinearMap.BilinForm.orthogonal (polarBilin Q) U) :
    LinearMap.BilinForm.orthogonal (polarBilin Q) (U ⊔ X) ⊓ (U ⊔ Y) ≤
      (U ⊓ LinearMap.BilinForm.orthogonal (polarBilin Q) U) ⊔ Y := by
  intro t ht
  obtain ⟨htX, htY⟩ := Submodule.mem_inf.mp ht
  obtain ⟨u, huU, v, hvY, huv⟩ := Submodule.mem_sup.mp htY
  have htU : t ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) U :=
    LinearMap.BilinForm.orthogonal_le le_sup_left htX
  have hvU : v ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) U := hY hvY
  have hu_eq : u = t - v := eq_sub_iff_add_eq.mpr huv
  have huOrth : u ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) U := by
    rw [hu_eq]
    exact Submodule.sub_mem _ htU hvU
  exact Submodule.mem_sup.mpr ⟨u, ⟨huU, huOrth⟩, v, hvY, huv⟩

private theorem finrank_inf_orthogonal_sup_add_two_le [Module.Finite F V]
    {U W₁ W₂ M C : Submodule F V}
    (hM : finrank F ↥M = finrank F V - finrank F ↥W₁)
    (hW₁ : finrank F ↥W₁ ≤ finrank F ↥U + 2)
    (hS : M ⊓ W₂ ≤ (U ⊓ LinearMap.BilinForm.orthogonal (polarBilin Q) U) ⊔ C)
    (hC : finrank F ↥C ≤ 2) (hU : hullDim Q U ≤ 6) (hV : 12 ≤ finrank F V) :
    finrank F ↥(M ⊓ W₂) + 2 ≤ finrank F ↥M := by
  have h1 := Submodule.finrank_mono hS
  have h2 := Submodule.finrank_add_le_finrank_add_finrank
    (U ⊓ LinearMap.BilinForm.orthogonal (polarBilin Q) U) C
  have hUdef : hullDim Q U = finrank F ↥U + finrank F
      ↥(U ⊓ LinearMap.BilinForm.orthogonal (polarBilin Q) U) := rfl
  have hW₁V : finrank F ↥W₁ ≤ finrank F V := Submodule.finrank_le W₁
  omega

private theorem not_le_orthogonal_of_ne_inf [FiniteDimensional F V]
    (hQ : (polarBilin Q).Nondegenerate) (hrefl : (polarBilin Q).IsRefl)
    {W₁ W₂ : Submodule F V}
    (h : LinearMap.BilinForm.orthogonal (polarBilin Q) W₁ ≠
      LinearMap.BilinForm.orthogonal (polarBilin Q) W₁ ⊓ W₂) :
    ¬ LinearMap.BilinForm.orthogonal (polarBilin Q) W₂ ≤ W₁ := by
  intro hN
  have horth : LinearMap.BilinForm.orthogonal (polarBilin Q) W₁ ≤
      LinearMap.BilinForm.orthogonal (polarBilin Q)
        (LinearMap.BilinForm.orthogonal (polarBilin Q) W₂) :=
    LinearMap.BilinForm.orthogonal_le hN
  rw [LinearMap.BilinForm.orthogonal_orthogonal hQ hrefl W₂] at horth
  exact h (inf_eq_left.mpr horth).symm

private theorem exists_mem_orthogonal_polar_eq_one [FiniteDimensional F V]
    (hQ : (polarBilin Q).Nondegenerate) (hrefl : (polarBilin Q).IsRefl)
    {W₁ W₂ : Submodule F V}
    (hN : ¬ LinearMap.BilinForm.orthogonal (polarBilin Q) W₂ ≤ W₁) :
    ∃ m ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) W₂,
      ∃ l ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) W₁, polar Q m l = 1 := by
  obtain ⟨m, hmN, hmW₁⟩ :
      ∃ m ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) W₂, m ∉ W₁ := by
    by_contra h
    push Not at h
    exact hN fun m hm => h m hm
  have hmM : m ∉ LinearMap.BilinForm.orthogonal (polarBilin Q)
      (LinearMap.BilinForm.orthogonal (polarBilin Q) W₁) := by
    rwa [LinearMap.BilinForm.orthogonal_orthogonal hQ hrefl W₁]
  rw [LinearMap.BilinForm.mem_orthogonal_iff, not_forall] at hmM
  push Not at hmM
  obtain ⟨l, hlM, hlm⟩ := hmM
  have hml_ne : polar Q m l ≠ 0 := by
    rw [polar_comm Q m l]
    simpa using hlm
  refine ⟨m, hmN, (polar Q m l)⁻¹ • l, Submodule.smul_mem _ _ hlM, ?_⟩
  rw [polar_smul_right, smul_eq_mul, inv_mul_cancel₀ hml_ne]

private theorem plane_le_orthogonal_of_adj {x y : FrameVert Q ν n}
    (h : (frameGraph Q ν n).Adj x y) :
    y.plane ≤ LinearMap.BilinForm.orthogonal (polarBilin Q) x.plane :=
  FrameVert.orth_iff_plane_le_orthogonal.mp h.2

private theorem mem_orthogonal_of_mem_orthogonal_sup {X Y : Submodule F V} {v : V}
    (h : v ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) (X ⊔ Y)) :
    v ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) X ∧
      v ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) Y := by
  rw [orthogonal_sup_eq_inf] at h
  exact Submodule.mem_inf.mp h

private theorem adj_of_mem_orthogonal_plane {x y : FrameVert Q ν n} (hxy : x.typ ≠ y.typ)
    (hu : y.u ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) x.plane)
    (hw : y.w ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) x.plane) :
    (frameGraph Q ν n).Adj x y := by
  refine ⟨hxy, ?_⟩
  obtain ⟨h₁, h₂⟩ := (FrameVert.mem_orthogonal_plane_iff x y.u).mp hu
  obtain ⟨h₃, h₄⟩ := (FrameVert.mem_orthogonal_plane_iff x y.w).mp hw
  exact ⟨h₁, h₃, h₂, h₄⟩

private theorem isGoodPair_of_mem_orthogonal_plane_u [Module.Finite F V] [CharP F 2]
    {y z : FrameVert Q ν n}
    (h : z.u ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) y.plane) : IsGoodPair z y := by
  obtain ⟨h₁, h₂⟩ := (FrameVert.mem_orthogonal_plane_iff y z.u).mp h
  refine isGoodPair_of_polar_u_eq_zero (z := z) (y := y) ?_ ?_
  · rw [polar_comm Q z.u y.u]
    exact h₁
  · rw [polar_comm Q z.u y.w]
    exact h₂

private theorem isGoodPair_of_mem_orthogonal_plane_w [Module.Finite F V] [CharP F 2]
    {y z : FrameVert Q ν n}
    (h : z.w ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) y.plane) : IsGoodPair z y := by
  obtain ⟨h₁, h₂⟩ := (FrameVert.mem_orthogonal_plane_iff y z.w).mp h
  refine isGoodPair_of_polar_w_eq_zero (z := z) (y := y) ?_ ?_
  · rw [polar_comm Q z.w y.u]
    exact h₁
  · rw [polar_comm Q z.w y.w]
    exact h₂

private theorem hullDim_quad_le_eight [Module.Finite F V] [CharP F 2]
    {a b c d : FrameVert Q ν n}
    (hab : (frameGraph Q ν n).Adj a b) (hbc : (frameGraph Q ν n).Adj b c)
    (hcd : (frameGraph Q ν n).Adj c d) (hda : (frameGraph Q ν n).Adj d a) :
    hullDim Q ((b.plane ⊔ d.plane) ⊔ a.plane) ≤ 8 ∧
      hullDim Q ((b.plane ⊔ d.plane) ⊔ c.plane) ≤ 8 := by
  have hA : a.plane ≤ LinearMap.BilinForm.orthogonal (polarBilin Q) (b.plane ⊔ d.plane) :=
    plane_le_orthogonal_sup_of_orthogonal
      (plane_le_orthogonal_of_adj hab.symm) (plane_le_orthogonal_of_adj hda)
  have hC : c.plane ≤ LinearMap.BilinForm.orthogonal (polarBilin Q) (b.plane ⊔ d.plane) :=
    plane_le_orthogonal_sup_of_orthogonal
      (plane_le_orthogonal_of_adj hbc) (plane_le_orthogonal_of_adj hcd.symm)
  have hU6 : hullDim Q (b.plane ⊔ d.plane) ≤ 6 := hullDim_sup_plane_le_six b d
  exact ⟨hullDim_sup_plane_le_eight_of_le_orthogonal hA hU6,
    hullDim_sup_plane_le_eight_of_le_orthogonal hC hU6⟩

private theorem exists_polar_one_quad [Finite F] [CharP F 2] [FiniteDimensional F V]
    (hQ : (polarBilin Q).Nondegenerate) (hV : 12 ≤ finrank F V)
    {a b c d : FrameVert Q ν n}
    (hab : (frameGraph Q ν n).Adj a b) (hbc : (frameGraph Q ν n).Adj b c)
    (hcd : (frameGraph Q ν n).Adj c d) (hda : (frameGraph Q ν n).Adj d a) :
    ∃ m ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) ((b.plane ⊔ d.plane) ⊔ c.plane),
      ∃ l ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) ((b.plane ⊔ d.plane) ⊔ a.plane),
        polar Q m l = 1 := by
  classical
  let U : Submodule F V := b.plane ⊔ d.plane
  let W₁ : Submodule F V := U ⊔ a.plane
  let W₂ : Submodule F V := U ⊔ c.plane
  let M : Submodule F V := LinearMap.BilinForm.orthogonal (polarBilin Q) W₁
  let N : Submodule F V := LinearMap.BilinForm.orthogonal (polarBilin Q) W₂
  have hU6 : hullDim Q U ≤ 6 := hullDim_sup_plane_le_six b d
  have hC : c.plane ≤ LinearMap.BilinForm.orthogonal (polarBilin Q) U :=
    plane_le_orthogonal_sup_of_orthogonal
      (plane_le_orthogonal_of_adj hbc) (plane_le_orthogonal_of_adj hcd.symm)
  have hS : M ⊓ W₂ ≤ (U ⊓ LinearMap.BilinForm.orthogonal (polarBilin Q) U) ⊔ c.plane :=
    inf_orthogonal_sup_le_rad_sup hC
  have hdim : finrank F ↥(M ⊓ W₂) + 2 ≤ finrank F M :=
    finrank_inf_orthogonal_sup_add_two_le (LinearMap.BilinForm.finrank_orthogonal hQ W₁)
      (finrank_sup_plane_le_add_two U a) hS (le_of_eq (FrameVert.finrank_plane c)) hU6 hV
  have hMS : M ≠ M ⊓ W₂ := by
    intro h
    have hfin : finrank F M = finrank F ↥(M ⊓ W₂) :=
      congrArg (fun t : Submodule F V => finrank F ↥t) h
    omega
  have hrefl : (polarBilin Q).IsRefl := (QuadraticMap.isSymm_polarBilin Q).isRefl
  have hN : ¬ N ≤ W₁ := not_le_orthogonal_of_ne_inf hQ hrefl hMS
  exact exists_mem_orthogonal_polar_eq_one hQ hrefl hN

private theorem exists_framedPair_quad [Finite F] [CharP F 2] [FiniteDimensional F V]
    (hQ : (polarBilin Q).Nondegenerate) (hV : 12 ≤ finrank F V)
    {a b c d : FrameVert Q ν n}
    (hab : (frameGraph Q ν n).Adj a b) (hbc : (frameGraph Q ν n).Adj b c)
    (hcd : (frameGraph Q ν n).Adj c d) (hda : (frameGraph Q ν n).Adj d a) :
    ∃ (x₁ x₂ : V),
      x₁ ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) ((b.plane ⊔ d.plane) ⊔ a.plane) ∧
      x₂ ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) ((b.plane ⊔ d.plane) ⊔ c.plane) ∧
      Q x₁ = 1 ∧ Q x₂ = ν ∧ polar Q x₁ x₂ = 1 := by
  obtain ⟨hW1_8, hW2_8⟩ := hullDim_quad_le_eight (Q := Q) hab hbc hcd hda
  obtain ⟨m, hmN, l, hlM, hml⟩ := exists_polar_one_quad hQ hV hab hbc hcd hda
  have hW1_dim_le : hullDim Q ((b.plane ⊔ d.plane) ⊔ a.plane) + 3 ≤ finrank F V := by
    omega
  obtain ⟨x₁, hx₁M, hmx₁, hx₁Q⟩ :=
    exists_polar_eq_one_Q_eq (Q := Q) hQ (U := (b.plane ⊔ d.plane) ⊔ a.plane) hW1_dim_le
      (z := m) (l := l) hlM hml (1 : F)
  have hW2_dim_le : hullDim Q ((b.plane ⊔ d.plane) ⊔ c.plane) + 3 ≤ finrank F V := by
    omega
  have hx₁m : polar Q x₁ m = 1 := by
    rw [polar_comm Q x₁ m]
    exact hmx₁
  obtain ⟨x₂, hx₂N, hx₁x₂, hx₂Q⟩ :=
    exists_polar_eq_one_Q_eq (Q := Q) hQ (U := (b.plane ⊔ d.plane) ⊔ c.plane) hW2_dim_le
      (z := x₁) (l := m) hmN hx₁m ν
  exact ⟨x₁, x₂, hx₁M, hx₂N, hx₁Q, hx₂Q, hx₁x₂⟩

private theorem exists_adj_adj_good_of_orthogonal_pair [CharP F 2] [Module.Finite F V]
    (hn : 5 ≤ n) {a b c d : FrameVert Q ν n} {x₁ x₂ : V}
    (hx₁L1 : x₁ ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) ((b.plane ⊔ d.plane) ⊔ a.plane))
    (hx₂L2 : x₂ ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) ((b.plane ⊔ d.plane) ⊔ c.plane))
    (hx₁Q : Q x₁ = 1) (hx₂Q : Q x₂ = ν) (hx₁x₂ : polar Q x₁ x₂ = 1) :
    ∃ x, (frameGraph Q ν n).Adj b x ∧ (frameGraph Q ν n).Adj d x ∧ IsGoodPair x a ∧
      IsGoodPair x c := by
  obtain ⟨hx₁_bd, hx₁a⟩ := mem_orthogonal_of_mem_orthogonal_sup hx₁L1
  obtain ⟨hx₁b, hx₁d⟩ := mem_orthogonal_of_mem_orthogonal_sup hx₁_bd
  obtain ⟨hx₂_bd, hx₂c⟩ := mem_orthogonal_of_mem_orthogonal_sup hx₂L2
  obtain ⟨hx₂b, hx₂d⟩ := mem_orthogonal_of_mem_orthogonal_sup hx₂_bd
  have hcard : ({b.typ, d.typ} : Finset (Fin n)).card <
      (Finset.univ : Finset (Fin n)).card := by
    have h2 : ({b.typ, d.typ} : Finset (Fin n)).card ≤ 2 := Finset.card_le_two
    rw [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨t, -, ht⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht
  obtain ⟨htb, htd⟩ := ht
  let x : FrameVert Q ν n :=
    { typ := t, u := x₁, w := x₂, Q_u := hx₁Q, Q_w := hx₂Q, polar_u_w := hx₁x₂ }
  exact ⟨x, adj_of_mem_orthogonal_plane (Ne.symm htb) hx₁b hx₂b,
    adj_of_mem_orthogonal_plane (Ne.symm htd) hx₁d hx₂d,
    isGoodPair_of_mem_orthogonal_plane_u hx₁a, isGoodPair_of_mem_orthogonal_plane_w hx₂c⟩

theorem exists_adj_adj_isGoodPair_isGoodPair [Finite F] [CharP F 2] [FiniteDimensional F V]
    (hQ : (polarBilin Q).Nondegenerate) (hV : 12 ≤ finrank F V) (hn : 5 ≤ n)
    {a b c d : FrameVert Q ν n}
    (hab : (frameGraph Q ν n).Adj a b) (hbc : (frameGraph Q ν n).Adj b c)
    (hcd : (frameGraph Q ν n).Adj c d) (hda : (frameGraph Q ν n).Adj d a) :
    ∃ x, (frameGraph Q ν n).Adj b x ∧ (frameGraph Q ν n).Adj d x ∧ IsGoodPair x a ∧
      IsGoodPair x c := by
  obtain ⟨x₁, x₂, hx₁L1, hx₂L2, hx₁Q, hx₂Q, hx₁x₂⟩ :=
    exists_framedPair_quad (Q := Q) hQ hV hab hbc hcd hda
  exact exists_adj_adj_good_of_orthogonal_pair hn hx₁L1 hx₂L2 hx₁Q hx₂Q hx₁x₂

private theorem cycleHomotopic_quad_frameGraph [Finite F] [CharP F 2] [FiniteDimensional F V]
    (hQ : (polarBilin Q).Nondegenerate) (hV : 12 ≤ finrank F V) (hn : 5 ≤ n)
    {a b c d : FrameVert Q ν n}
    (hab : (frameGraph Q ν n).Adj a b) (hbc : (frameGraph Q ν n).Adj b c)
    (hcd : (frameGraph Q ν n).Adj c d) (hda : (frameGraph Q ν n).Adj d a) :
    CFSG.ClassicalInvolution.Phan.CycleHomotopic
      (fun x => {c : (frameGraph Q ν n).Walk x x | CFSG.Monster.B.Recog.Homotopic c .nil})
      (CFSG.ClassicalInvolution.Phan.quadWalk hab hbc hcd hda) .nil := by
  obtain ⟨x, hbx, hdx, hxa, hxc⟩ :=
    exists_adj_adj_isGoodPair_isGoodPair hQ hV hn hab hbc hcd hda
  have hcone_cx := preconnected_induce_neighborSet_inter hQ hV hn hxc.symm
  have hcone_xa := preconnected_induce_neighborSet_inter hQ hV hn hxa
  have h1 : CFSG.ClassicalInvolution.Phan.CycleHomotopic
      (fun x => {c : (frameGraph Q ν n).Walk x x | CFSG.Monster.B.Recog.Homotopic c .nil})
      (CFSG.ClassicalInvolution.Phan.quadWalk hbc hcd hdx hbx.symm) .nil :=
    CFSG.ClassicalInvolution.Phan.cycleHomotopic_quad_rotate_rev _ hbc hcd hdx hbx.symm
      (CFSG.ClassicalInvolution.Phan.cycleHomotopic_quad_of_preconnected _
        (CFSG.ClassicalInvolution.Phan.nullLen_three_homotopic (frameGraph Q ν n))
        hcd hdx hbx.symm hbc hcone_cx)
  have h2 : CFSG.ClassicalInvolution.Phan.CycleHomotopic
      (fun x => {c : (frameGraph Q ν n).Walk x x | CFSG.Monster.B.Recog.Homotopic c .nil})
      (CFSG.ClassicalInvolution.Phan.quadWalk hbx hdx.symm hda hab) .nil :=
    CFSG.ClassicalInvolution.Phan.cycleHomotopic_quad_rotate_rev _ hbx hdx.symm hda hab
      (CFSG.ClassicalInvolution.Phan.cycleHomotopic_quad_of_preconnected _
        (CFSG.ClassicalInvolution.Phan.nullLen_three_homotopic (frameGraph Q ν n))
        hdx.symm hda hab hbx hcone_xa)
  have hrot : CFSG.ClassicalInvolution.Phan.CycleHomotopic
      (fun x => {c : (frameGraph Q ν n).Walk x x | CFSG.Monster.B.Recog.Homotopic c .nil})
      (CFSG.ClassicalInvolution.Phan.quadWalk hbc hcd hda hab) .nil :=
    CFSG.ClassicalInvolution.Phan.cycleHomotopic_quad_trans _ hbc hcd hdx hbx.symm hda hab
      h1 h2
  exact CFSG.ClassicalInvolution.Phan.cycleHomotopic_quad_rotate_rev _ hab hbc hcd hda hrot

theorem nullLen_four_frameGraph [Finite F] [CharP F 2] [FiniteDimensional F V]
    (hQ : (polarBilin Q).Nondegenerate) (hV : 12 ≤ finrank F V) (hn : 5 ≤ n) :
    CFSG.ClassicalInvolution.Phan.NullLen
      (fun x => {c : (frameGraph Q ν n).Walk x x | CFSG.Monster.B.Recog.Homotopic c .nil}) 4 := by
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
            exact cycleHomotopic_quad_frameGraph hQ hV hn hab hbc hcd hda

end CFSG.ClassicalGroups.Orthogonal.FramedPlanes
