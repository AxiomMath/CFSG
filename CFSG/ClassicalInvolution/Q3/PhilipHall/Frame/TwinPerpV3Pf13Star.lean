module

public import CFSG.ClassicalInvolution.Asc77.AscT7JHyp51u
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscData
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgtLift
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameVertex
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPfCore

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.Q3CH CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
open scoped commutatorElement
open CFSG.ClassicalInvolution.Balance.Bootstrap (trivialOnQuot)

section StarVertices

section ZType

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem hyp51At_of_twin_pair (hΩ : HypOmegaGen Ω) (hsolv : ∀ M ∈ Ω, Group.IsSolvable ↥M)
    {K K' : Subgroup G} {c x y : G} (hK : K ∈ Ω) (hK' : K' ∈ Ω) (hzK : IsUniqueInvolution K c)
    (hzK' : IsUniqueInvolution K' c) (hx : x ∈ K) (hy : y ∈ K') {B : Subgroup G}
    (hB : IsElemAbelian 2 B) (hcB : c ∈ B) (hxyB : x * y ∈ B) (hc1 : c ≠ 1) (hxy1 : x * y ≠ 1)
    (hxyc : x * y ≠ c) : Hyp51At B c := by
  have hKsub := isSubnormal_of_hypOmegaGen hΩ hK hzK
  have hK'sub := isSubnormal_of_hypOmegaGen hΩ hK' hzK'
  have hKz : K ≤ Subgroup.centralizer ({c} : Set G) := le_centralizer_of_unique hzK
  have hK'z : K' ≤ Subgroup.centralizer ({c} : Set G) := le_centralizer_of_unique hzK'
  have hx' : x ∈ Subgroup.centralizer ({c} : Set G) := hKz hx
  have hy' : y ∈ Subgroup.centralizer ({c} : Set G) := hK'z hy
  have huC : x * y ∈ Subgroup.centralizer ({c} : Set G) := Subgroup.mul_mem _ hx' hy'
  have hno : ∀ L : Subgroup (OddQuot c), CFSG.IsComponent L → MovedByAll B c L → False := by
    intro L hL hmov
    have hxm : oddQuotMk c ⟨x * y, huC⟩ ∈ modOdd c B := oddQuotMk_mem_modOdd hxyB huC
    have hnot := Lemma52Proof.oddQuotMk_not_mem_zpowers hB hcB hc1 hxyB hxy1 hxyc huC
    obtain ⟨w, hw, hwne⟩ := hmov _ hxm hnot
    apply hwne
    have hcx : ∀ v ∈ L, v * oddQuotMk c ⟨x, hx'⟩ = oddQuotMk c ⟨x, hx'⟩ * v := by
      intro v hv
      have h1 : ⁅v, oddQuotMk c ⟨x, hx'⟩⁆ ∈ ⁅L, modOdd c K⁆ :=
        Subgroup.commutator_mem_commutator hv (oddQuotMk_mem_modOdd hx hx')
      rw [TwinFrame.commutator_component_modOdd_of_solvable hKsub (hsolv K hK) hL,
        Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1
    have hcy : ∀ v ∈ L, v * oddQuotMk c ⟨y, hy'⟩ = oddQuotMk c ⟨y, hy'⟩ * v := by
      intro v hv
      have h1 : ⁅v, oddQuotMk c ⟨y, hy'⟩⁆ ∈ ⁅L, modOdd c K'⁆ :=
        Subgroup.commutator_mem_commutator hv (oddQuotMk_mem_modOdd hy hy')
      rw [TwinFrame.commutator_component_modOdd_of_solvable hK'sub (hsolv K' hK') hL,
        Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1
    have e1 : oddQuotMk c ⟨x * y, huC⟩ = oddQuotMk c ⟨x, hx'⟩ * oddQuotMk c ⟨y, hy'⟩ := by
      rw [← map_mul]
      rfl
    rw [e1, mul_assoc, ← hcy w hw, ← mul_assoc, ← hcx w hw, mul_assoc]
  exact ⟨fun L₁ L₂ h1 _ m1 _ => (hno L₁ h1 m1).elim, fun L hL hm => (hno L hL hm).elim⟩

end ZType

section Frame

variable {Y : Type} [Group Y] [Finite Y]

structure StarFrame (Ω : Set (Subgroup Y)) (t : Y) (K K' K₃ K₄ : Subgroup Y) (a₁ a₂ a₃ a₄ : Y) :
    Prop where
  hyp : HypOmegaGen Ω
  hK : K ∈ Ω
  hK' : K' ∈ Ω
  hK₃ : K₃ ∈ Ω
  hK₄ : K₄ ∈ Ω
  hzK : IsUniqueInvolution K t
  hzK' : IsUniqueInvolution K' t
  hzK₃ : IsUniqueInvolution K₃ t
  hzK₄ : IsUniqueInvolution K₄ t
  n12 : K' ≠ K
  n13 : K₃ ≠ K
  n23 : K₃ ≠ K'
  n14 : K₄ ≠ K
  n24 : K₄ ≠ K'
  n34 : K₄ ≠ K₃
  h₁ : a₁ ∈ K
  h₂ : a₂ ∈ K'
  h₃ : a₃ ∈ K₃
  h₄ : a₄ ∈ K₄
  o₁ : orderOf a₁ = 4
  o₂ : orderOf a₂ = 4
  o₃ : orderOf a₃ = 4
  o₄ : orderOf a₄ = 4
  c12 : a₁ * a₂ = a₂ * a₁
  c13 : a₁ * a₃ = a₃ * a₁
  c14 : a₁ * a₄ = a₄ * a₁
  c23 : a₂ * a₃ = a₃ * a₂
  c24 : a₂ * a₄ = a₄ * a₂
  c34 : a₃ * a₄ = a₄ * a₃
  t1 : a₁ * a₂ * a₃ * a₄ ≠ 1
  tt : a₁ * a₂ * a₃ * a₄ ≠ t

theorem no_common_order4 {Ω : Set (Subgroup Y)} (hΩ : HypOmegaGen Ω) {K K' : Subgroup Y}
    (hK : K ∈ Ω) (hK' : K' ∈ Ω) (hne : K' ≠ K) {x : Y} (o : orderOf x = 4) (hx : x ∈ K)
    (hx' : x ∈ K') : False := by
  have h2 : IsPGroup 2 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, o]; norm_num)
  have h4 : 4 ≤ Nat.card (Subgroup.zpowers x) := by rw [Nat.card_zpowers, o]
  exact hne (Sec6Gen.eq_of_le_of_le hΩ hK hK' h2 h4 (Subgroup.zpowers_le.mpr hx)
    (Subgroup.zpowers_le.mpr hx')).symm

namespace StarFrame

variable {Ω : Set (Subgroup Y)} {t : Y} {K K' K₃ K₄ : Subgroup Y} {a₁ a₂ a₃ a₄ : Y}

theorem sq₁ (F : StarFrame Ω t K K' K₃ K₄ a₁ a₂ a₃ a₄) : a₁ * a₁ = t :=
  T7A.sq_eq_of_orderOf_four F.hzK F.h₁ F.o₁

theorem sq₂ (F : StarFrame Ω t K K' K₃ K₄ a₁ a₂ a₃ a₄) : a₂ * a₂ = t :=
  T7A.sq_eq_of_orderOf_four F.hzK' F.h₂ F.o₂

theorem sq₃ (F : StarFrame Ω t K K' K₃ K₄ a₁ a₂ a₃ a₄) : a₃ * a₃ = t :=
  T7A.sq_eq_of_orderOf_four F.hzK₃ F.h₃ F.o₃

theorem sq₄ (F : StarFrame Ω t K K' K₃ K₄ a₁ a₂ a₃ a₄) : a₄ * a₄ = t :=
  T7A.sq_eq_of_orderOf_four F.hzK₄ F.h₄ F.o₄

theorem tc₁ (F : StarFrame Ω t K K' K₃ K₄ a₁ a₂ a₃ a₄) : t * a₁ = a₁ * t :=
  F.hzK.commute_of_mem F.h₁

theorem tc₂ (F : StarFrame Ω t K K' K₃ K₄ a₁ a₂ a₃ a₄) : t * a₂ = a₂ * t :=
  F.hzK'.commute_of_mem F.h₂

theorem tc₃ (F : StarFrame Ω t K K' K₃ K₄ a₁ a₂ a₃ a₄) : t * a₃ = a₃ * t :=
  F.hzK₃.commute_of_mem F.h₃

theorem tc₄ (F : StarFrame Ω t K K' K₃ K₄ a₁ a₂ a₃ a₄) : t * a₄ = a₄ * t :=
  F.hzK₄.commute_of_mem F.h₄

theorem tsq (F : StarFrame Ω t K K' K₃ K₄ a₁ a₂ a₃ a₄) : t * t = 1 := F.hzK.sq

theorem p_sq (F : StarFrame Ω t K K' K₃ K₄ a₁ a₂ a₃ a₄) : (a₁ * a₂) * (a₁ * a₂) = 1 := by
  calc (a₁ * a₂) * (a₁ * a₂) = a₁ * (a₂ * a₁) * a₂ := by group
    _ = a₁ * (a₁ * a₂) * a₂ := by rw [← F.c12]
    _ = (a₁ * a₁) * (a₂ * a₂) := by group
    _ = 1 := by rw [F.sq₁, F.sq₂, F.tsq]

theorem q_sq (F : StarFrame Ω t K K' K₃ K₄ a₁ a₂ a₃ a₄) : (a₃ * a₄) * (a₃ * a₄) = 1 := by
  calc (a₃ * a₄) * (a₃ * a₄) = a₃ * (a₄ * a₃) * a₄ := by group
    _ = a₃ * (a₃ * a₄) * a₄ := by rw [← F.c34]
    _ = (a₃ * a₃) * (a₄ * a₄) := by group
    _ = 1 := by rw [F.sq₃, F.sq₄, F.tsq]

theorem p_ne_one (F : StarFrame Ω t K K' K₃ K₄ a₁ a₂ a₃ a₄) : a₁ * a₂ ≠ 1 := by
  intro he
  refine no_common_order4 F.hyp F.hK F.hK' F.n12 F.o₂ ?_ F.h₂
  rw [show a₂ = a₁⁻¹ from eq_inv_of_mul_eq_one_right he]
  exact K.inv_mem F.h₁

theorem p_ne_t (F : StarFrame Ω t K K' K₃ K₄ a₁ a₂ a₃ a₄) : a₁ * a₂ ≠ t := by
  intro he
  refine no_common_order4 F.hyp F.hK F.hK' F.n12 F.o₂ ?_ F.h₂
  have : a₂ = a₁⁻¹ * t := by rw [← he]; group
  rw [this]
  exact K.mul_mem (K.inv_mem F.h₁) F.hzK.mem

theorem q_ne_one (F : StarFrame Ω t K K' K₃ K₄ a₁ a₂ a₃ a₄) : a₃ * a₄ ≠ 1 := by
  intro he
  refine no_common_order4 F.hyp F.hK₃ F.hK₄ F.n34 F.o₄ ?_ F.h₄
  rw [show a₄ = a₃⁻¹ from eq_inv_of_mul_eq_one_right he]
  exact K₃.inv_mem F.h₃

theorem q_ne_t (F : StarFrame Ω t K K' K₃ K₄ a₁ a₂ a₃ a₄) : a₃ * a₄ ≠ t := by
  intro he
  refine no_common_order4 F.hyp F.hK₃ F.hK₄ F.n34 F.o₄ ?_ F.h₄
  have : a₄ = a₃⁻¹ * t := by rw [← he]; group
  rw [this]
  exact K₃.mul_mem (K₃.inv_mem F.h₃) F.hzK₃.mem

theorem comm_gen (F : StarFrame Ω t K K' K₃ K₄ a₁ a₂ a₃ a₄) :
    ∀ a ∈ ({a₁ * a₂, t, a₃ * a₄} : Set Y), ∀ b ∈ ({a₁ * a₂, t, a₃ * a₄} : Set Y), a * b = b * a := by
  have hpt : (a₁ * a₂) * t = t * (a₁ * a₂) := by
    calc (a₁ * a₂) * t = a₁ * (a₂ * t) := by group
      _ = a₁ * (t * a₂) := by rw [F.tc₂]
      _ = (a₁ * t) * a₂ := by group
      _ = (t * a₁) * a₂ := by rw [F.tc₁]
      _ = t * (a₁ * a₂) := by group
  have hqt : (a₃ * a₄) * t = t * (a₃ * a₄) := by
    calc (a₃ * a₄) * t = a₃ * (a₄ * t) := by group
      _ = a₃ * (t * a₄) := by rw [F.tc₄]
      _ = (a₃ * t) * a₄ := by group
      _ = (t * a₃) * a₄ := by rw [F.tc₃]
      _ = t * (a₃ * a₄) := by group
  have hpq : (a₁ * a₂) * (a₃ * a₄) = (a₃ * a₄) * (a₁ * a₂) :=
    (Commute.mul_right (Commute.mul_left (show Commute a₁ a₃ from F.c13) (show Commute a₂ a₃ from F.c23))
      (Commute.mul_left (show Commute a₁ a₄ from F.c14) (show Commute a₂ a₄ from F.c24))).eq
  intro a ha b hb
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
  · rfl
  · exact hpt
  · exact hpq
  · exact hpt.symm
  · rfl
  · exact hqt.symm
  · exact hpq.symm
  · exact hqt
  · rfl

theorem sq_gen (F : StarFrame Ω t K K' K₃ K₄ a₁ a₂ a₃ a₄) :
    ∀ a ∈ ({a₁ * a₂, t, a₃ * a₄} : Set Y), a * a = 1 := by
  intro a ha
  rcases ha with rfl | rfl | rfl
  · exact F.p_sq
  · exact F.tsq
  · exact F.q_sq

theorem isElemAbelian (F : StarFrame Ω t K K' K₃ K₄ a₁ a₂ a₃ a₄) :
    IsElemAbelian 2 (Subgroup.closure ({a₁ * a₂, t, a₃ * a₄} : Set Y)) := by
  have hcomm := T7A.commutes_closure F.comm_gen
  refine ⟨⟨⟨fun a b => Subtype.ext (hcomm _ a.2 _ b.2)⟩⟩, fun x hx => ?_⟩
  rw [pow_two]
  exact T7A.sq_closure F.sq_gen F.comm_gen x hx

theorem natCard (F : StarFrame Ω t K K' K₃ K₄ a₁ a₂ a₃ a₄) :
    Nat.card ↥(Subgroup.closure ({a₁ * a₂, t, a₃ * a₄} : Set Y)) = 8 := by
  have hpt : a₁ * a₂ ≠ t := F.p_ne_t
  have hnot : a₃ * a₄ ∉ Subgroup.closure ({a₁ * a₂, t} : Set Y) := by
    intro hx
    rcases T7B.mem_closure_pair F.p_sq F.tsq F.p_ne_one F.hzK.ne_one
      (F.comm_gen _ (by simp) _ (by simp)) hx with h | h | h | h
    · exact F.q_ne_one h
    · apply F.t1
      calc a₁ * a₂ * a₃ * a₄ = (a₁ * a₂) * (a₃ * a₄) := by group
        _ = (a₁ * a₂) * (a₁ * a₂) := by rw [h]
        _ = 1 := F.p_sq
    · exact F.q_ne_t h
    · apply F.tt
      calc a₁ * a₂ * a₃ * a₄ = (a₁ * a₂) * (a₃ * a₄) := by group
        _ = (a₁ * a₂) * ((a₁ * a₂) * t) := by rw [h]
        _ = ((a₁ * a₂) * (a₁ * a₂)) * t := by group
        _ = t := by rw [F.p_sq, one_mul]
  exact T7B.natCard_closure_three_eq_eight F.p_sq F.tsq F.q_sq F.p_ne_one F.hzK.ne_one hpt F.q_ne_one
    (F.comm_gen _ (by simp) _ (by simp)) (F.comm_gen _ (by simp) _ (by simp))
    (F.comm_gen _ (by simp) _ (by simp)) hnot

theorem mem_cases (F : StarFrame Ω t K K' K₃ K₄ a₁ a₂ a₃ a₄) {c : Y}
    (hc : c ∈ Subgroup.closure ({a₁ * a₂, t, a₃ * a₄} : Set Y)) :
    c = 1 ∨ c = a₁ * a₂ ∨ c = t ∨ c = a₃ * a₄ ∨ c = a₁ * a₂ * t ∨ c = a₁ * a₂ * (a₃ * a₄) ∨
      c = t * (a₃ * a₄) ∨ c = a₁ * a₂ * t * (a₃ * a₄) :=
  T7J.mem_closure_three (F.comm_gen _ (by simp) _ (by simp)) (F.comm_gen _ (by simp) _ (by simp))
    (F.comm_gen _ (by simp) _ (by simp)) F.p_sq F.tsq F.q_sq hc

end StarFrame

end Frame

section Vertices

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K K' K₃ K₄ : Subgroup Y} {a₁ a₂ a₃ a₄ : Y}

namespace StarFrame

variable {Ω : Set (Subgroup Y)}

theorem pq_comm (F : StarFrame Ω t K K' K₃ K₄ a₁ a₂ a₃ a₄) :
    (a₁ * a₂) * (a₃ * a₄) = (a₃ * a₄) * (a₁ * a₂) :=
  F.comm_gen _ (by simp) _ (by simp)

theorem pt_comm (F : StarFrame Ω t K K' K₃ K₄ a₁ a₂ a₃ a₄) :
    (a₁ * a₂) * t = t * (a₁ * a₂) :=
  F.comm_gen _ (by simp) _ (by simp)

theorem swap (F : StarFrame Ω t K K' K₃ K₄ a₁ a₂ a₃ a₄) :
    StarFrame Ω t K₃ K₄ K K' a₃ a₄ a₁ a₂ where
  hyp := F.hyp
  hK := F.hK₃
  hK' := F.hK₄
  hK₃ := F.hK
  hK₄ := F.hK'
  hzK := F.hzK₃
  hzK' := F.hzK₄
  hzK₃ := F.hzK
  hzK₄ := F.hzK'
  n12 := F.n34
  n13 := F.n13.symm
  n23 := F.n14.symm
  n14 := F.n23.symm
  n24 := F.n24.symm
  n34 := F.n12
  h₁ := F.h₃
  h₂ := F.h₄
  h₃ := F.h₁
  h₄ := F.h₂
  o₁ := F.o₃
  o₂ := F.o₄
  o₃ := F.o₁
  o₄ := F.o₂
  c12 := F.c34
  c13 := F.c13.symm
  c14 := F.c23.symm
  c23 := F.c14.symm
  c24 := F.c24.symm
  c34 := F.c12
  t1 := by rw [show a₃ * a₄ * a₁ * a₂ = (a₃ * a₄) * (a₁ * a₂) by group, ← F.pq_comm,
      show (a₁ * a₂) * (a₃ * a₄) = a₁ * a₂ * a₃ * a₄ by group]; exact F.t1
  tt := by rw [show a₃ * a₄ * a₁ * a₂ = (a₃ * a₄) * (a₁ * a₂) by group, ← F.pq_comm,
      show (a₁ * a₂) * (a₃ * a₄) = a₁ * a₂ * a₃ * a₄ by group]; exact F.tt

theorem inv_eq (F : StarFrame Ω t K K' K₃ K₄ a₁ a₂ a₃ a₄) : a₁⁻¹ = t * a₁ := by
  rw [inv_eq_iff_mul_eq_one]
  calc a₁ * (t * a₁) = a₁ * (a₁ * t) := by rw [F.tc₁]
    _ = (a₁ * a₁) * t := by group
    _ = 1 := by rw [F.sq₁, F.tsq]

theorem invFirst (F : StarFrame Ω t K K' K₃ K₄ a₁ a₂ a₃ a₄) :
    StarFrame Ω t K K' K₃ K₄ a₁⁻¹ a₂ a₃ a₄ where
  hyp := F.hyp
  hK := F.hK
  hK' := F.hK'
  hK₃ := F.hK₃
  hK₄ := F.hK₄
  hzK := F.hzK
  hzK' := F.hzK'
  hzK₃ := F.hzK₃
  hzK₄ := F.hzK₄
  n12 := F.n12
  n13 := F.n13
  n23 := F.n23
  n14 := F.n14
  n24 := F.n24
  n34 := F.n34
  h₁ := K.inv_mem F.h₁
  h₂ := F.h₂
  h₃ := F.h₃
  h₄ := F.h₄
  o₁ := by rw [orderOf_inv]; exact F.o₁
  o₂ := F.o₂
  o₃ := F.o₃
  o₄ := F.o₄
  c12 := ((show Commute a₁ a₂ from F.c12).inv_left).eq
  c13 := ((show Commute a₁ a₃ from F.c13).inv_left).eq
  c14 := ((show Commute a₁ a₄ from F.c14).inv_left).eq
  c23 := F.c23
  c24 := F.c24
  c34 := F.c34
  t1 := by
    intro h
    apply F.tt
    have : a₁⁻¹ * a₂ * a₃ * a₄ = t * (a₁ * a₂ * a₃ * a₄) := by
      rw [F.inv_eq]; group
    rw [this] at h
    have h' : a₁ * a₂ * a₃ * a₄ = t⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [h']
    exact inv_eq_of_mul_eq_one_right F.tsq
  tt := by
    intro h
    apply F.t1
    have : a₁⁻¹ * a₂ * a₃ * a₄ = t * (a₁ * a₂ * a₃ * a₄) := by
      rw [F.inv_eq]; group
    rw [this] at h
    have := mul_eq_left.mp h
    exact this

theorem inv_mul (F : StarFrame Ω t K K' K₃ K₄ a₁ a₂ a₃ a₄) : a₁⁻¹ * a₂ = a₁ * a₂ * t := by
  rw [F.inv_eq]
  calc t * a₁ * a₂ = t * (a₁ * a₂) := by group
    _ = (a₁ * a₂) * t := F.pt_comm.symm

end StarFrame

theorem hsolv_conjClass (hP : PerpHypS n Y R S t) :
    ∀ M ∈ CoreAssembly.conjClass (tightCore R), Group.IsSolvable ↥M := by
  have hC := CoreData.of_S hP.core
  rintro _ ⟨g, rfl⟩
  have hR := Q8Datum.isSolvable hC.datum
  have hK : Group.IsSolvable ↥(tightCore R) :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion (tightCore_le R))
      (Subgroup.inclusion_injective _)
  exact isSolvable_conjSub_of hK g

end Vertices

end StarVertices

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
