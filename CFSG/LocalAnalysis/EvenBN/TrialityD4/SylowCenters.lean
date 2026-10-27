module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.Sylow
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import Mathlib.GroupTheory.Nilpotent
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup
open scoped commutatorElement

section Generic

variable {G : Type*} [Group G]

theorem mem_inf_centralizer_iff {H : Subgroup G} {x : G} :
    x ∈ H ⊓ centralizer (H : Set G) ↔ x ∈ H ∧ ∀ y ∈ H, ⁅x, y⁆ = 1 := by
  rw [mem_inf, mem_centralizer_iff]
  refine and_congr_right fun _ => forall₂_congr fun y _ => ?_
  rw [commutatorElement_eq_one_iff_commute, Commute, SemiconjBy, eq_comm]

theorem map_upperCentralSeries_succ {H T T' : Subgroup G} {n : ℕ}
    (hT : (Subgroup.upperCentralSeries H n).map H.subtype = T)
    (hT' : ∀ x, x ∈ T' ↔ x ∈ H ∧ ∀ y ∈ H, ⁅x, y⁆ ∈ T) :
    (Subgroup.upperCentralSeries H (n + 1)).map H.subtype = T' := by
  ext x
  rw [hT', mem_map]
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨z.2, fun y hy => ?_⟩
    rw [← hT]
    exact ⟨⁅z, ⟨y, hy⟩⁆, Subgroup.mem_upperCentralSeries_succ_iff.1 hz _, rfl⟩
  · rintro ⟨hx, h⟩
    refine ⟨⟨x, hx⟩, Subgroup.mem_upperCentralSeries_succ_iff.2 fun y => ?_, rfl⟩
    have hy := h y y.2
    rw [← hT] at hy
    obtain ⟨w, hw, hw'⟩ := hy
    have hw'' : w = ⁅(⟨x, hx⟩ : H), y⁆ := Subtype.ext hw'
    rwa [← hw'']

theorem map_upperCentralSeries_zero (H : Subgroup G) :
    (Subgroup.upperCentralSeries H 0).map H.subtype = ⊥ := by
  rw [Subgroup.upperCentralSeries_zero, Subgroup.map_bot]

theorem mul_mul_self_eq_commutatorElement {g f : G} (hg : g * g = 1) :
    g * f * (g * f) = ⁅g, f⁆ * (f * f) := by
  rw [commutatorElement_def, inv_eq_of_mul_eq_one_right hg]
  group

theorem isElementaryAbelian_two_of_forall {E : Subgroup G}
    (hc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (h2 : ∀ x ∈ E, x * x = 1) :
    IsElementaryAbelian 2 E := CFSG.IsElementaryAbelian.two_of_forall_mul_self hc h2

theorem conj_mul_conj (w₁ w₂ n : G) :
    w₁ * w₂ * n * (w₁ * w₂)⁻¹ = w₁ * (w₂ * n * w₂⁻¹) * w₁⁻¹ := by
  group

theorem conj_conj_of_mul_self {w : G} (hw : w * w = 1) (y : G) :
    w * (w * y * w⁻¹) * w⁻¹ = y := by
  calc w * (w * y * w⁻¹) * w⁻¹ = (w * w) * y * (w * w)⁻¹ := by group
    _ = y := by rw [hw]; group

end Generic

namespace TrialityD4Data

variable {X : Type*} [Group X] {q : ℕ} (d : TrialityD4Data X q)

theorem mem_D_of_commutatorElement_x₂_mem_W {x : X} (hx : x ∈ d.S)
    (h : ⁅x, d.x₂ 1⁆ ∈ d.W) : x ∈ d.D := by
  obtain ⟨a, n, hn, rfl⟩ := d.mem_S_iff.1 hx
  have hn' : ⁅n, d.x₂ 1⁆ ∈ d.W :=
    d.Y_le_W (d.V_le_Y (d.commutator_D_D (commutator_mem_commutator hn (d.x₂_mem_D 1))))
  rw [commutatorElement_mul_mem_iff (d.S_le_normalizer_W (d.U₁_le_S (d.x₁_mem_U₁ a))) hn',
    d.comm₁₂, mul_assoc, mul_mem_cancel_right (mul_mem (d.x₄_mem_W _) (d.x₅_mem_W _))] at h
  have ha : a = 0 := by simpa using d.x₃_mem_W_iff.1 h
  rw [ha, d.x₁_zero, one_mul]
  exact hn

theorem mem_F_of_commutatorElement_x₁_mem_W {x : X} (hx : x ∈ d.D)
    (h : ⁅x, d.x₁ 1⁆ ∈ d.W) : x ∈ d.F := by
  obtain ⟨a, n, hn, rfl⟩ := d.mem_D_iff.1 hx
  have hn' : ⁅n, d.x₁ 1⁆ ∈ d.W := commutatorElement_mem_comm.1
    (d.commutator_S_F (commutator_mem_commutator (d.U₁_le_S (d.x₁_mem_U₁ 1)) hn))
  rw [commutatorElement_mul_mem_iff (d.S_le_normalizer_W (d.U₂_le_S (d.x₂_mem_U₂ a))) hn',
    commutatorElement_mem_comm, d.comm₁₂, mul_assoc,
    mul_mem_cancel_right (mul_mem (d.x₄_mem_W _) (d.x₅_mem_W _))] at h
  have ha : a = 0 := by simpa using d.x₃_mem_W_iff.1 h
  rw [ha, d.x₂_zero, one_mul]
  exact hn

theorem mem_W_of_forall_commutatorElement_x₁_mem_Y {x : X} (hx : x ∈ d.F)
    (h : ∀ b, ⁅x, d.x₁ b⁆ ∈ d.Y) : x ∈ d.W := by
  obtain ⟨a, n, hn, rfl⟩ := d.mem_F_iff.1 hx
  have key : ∀ b, d.σ b * d.σ (d.σ a) + d.σ (d.σ b) * d.σ a = 0 := fun b => by
    have hb := h b
    have hn' : ⁅n, d.x₁ b⁆ ∈ d.Y := commutatorElement_mem_comm.1
      (d.commutator_S_W (commutator_mem_commutator (d.U₁_le_S (d.x₁_mem_U₁ b)) hn))
    rw [commutatorElement_mul_mem_iff (d.S_le_normalizer_Y (d.U₃_le_S (d.x₃_mem_U₃ a))) hn',
      commutatorElement_mem_comm, d.comm₁₃, mul_assoc,
      mul_mem_cancel_right (mul_mem (d.x₅_mem_Y _) (d.x₆_mem_Y _)), d.x₄_mem_Y_iff] at hb
    exact hb
  rw [d.eq_zero_of_forall_twist key, d.x₃_zero, one_mul]
  exact hn

theorem mem_F_of_forall_commutatorElement_x₃_mem_Y {x : X} (hx : x ∈ d.M)
    (h : ∀ b, ⁅x, d.x₃ b⁆ ∈ d.Y) : x ∈ d.F := by
  obtain ⟨a, n, hn, rfl⟩ := d.mem_M_iff.1 hx
  have key : ∀ b, d.σ b * d.σ (d.σ a) + d.σ (d.σ b) * d.σ a = 0 := fun b => by
    have hb := h b
    have hn' : ⁅n, d.x₃ b⁆ ∈ d.Y :=
      d.V_le_Y (d.commutator_F_F (commutator_mem_commutator hn (d.x₃_mem_F b)))
    rw [commutatorElement_mul_mem_iff (d.S_le_normalizer_Y (d.U₁_le_S (d.x₁_mem_U₁ a))) hn',
      d.comm₁₃, mul_assoc, mul_mem_cancel_right (mul_mem (d.x₅_mem_Y _) (d.x₆_mem_Y _)),
      d.x₄_mem_Y_iff] at hb
    rw [← hb]
    ring
  rw [d.eq_zero_of_forall_twist key, d.x₁_zero, one_mul]
  exact hn

theorem mem_Y_of_forall_commutatorElement_x₁_mem_V {x : X} (hx : x ∈ d.W)
    (h : ∀ b, ⁅x, d.x₁ b⁆ ∈ d.V) : x ∈ d.Y := by
  obtain ⟨a, n, hn, rfl⟩ := d.mem_W_iff.1 hx
  have key : ∀ b, d.tr (a * b) = 0 := fun b => by
    have hb := h b
    have h1 : ⁅d.x₁ b, n⁆ ∈ (⊥ : Subgroup X) :=
      d.commutator_M_Y ▸ commutator_mem_commutator (d.x₁_mem_M b) hn
    have hn' : ⁅n, d.x₁ b⁆ ∈ d.V := by
      rw [commutatorElement_mem_comm, mem_bot.1 h1]
      exact one_mem _
    rw [commutatorElement_mul_mem_iff (d.S_le_normalizer_V (d.U₄_le_S (d.x₄_mem_U₄ a))) hn',
      commutatorElement_mem_comm, d.comm₁₄, d.x₅_mem_V_iff] at hb
    rwa [mul_comm] at hb
  rw [d.eq_zero_of_forall_tr_mul key, d.x₄_zero, one_mul]
  exact hn

theorem mem_V_of_commutatorElement_x₂_eq_one {x : X} (hx : x ∈ d.Y)
    (h : ⁅x, d.x₂ 1⁆ = 1) : x ∈ d.V := by
  obtain ⟨a, n, hn, rfl⟩ := d.mem_Y_iff.1 hx
  have hn' : ⁅n, d.x₂ 1⁆ ∈ (⊥ : Subgroup X) := by
    rw [commutatorElement_mem_comm, ← d.commutator_S_V]
    exact commutator_mem_commutator (d.U₂_le_S (d.x₂_mem_U₂ 1)) hn
  rw [← mem_bot, commutatorElement_mul_mem_iff (le_normalizer_bot_subgroup ⊤ (mem_top _)) hn',
    commutatorElement_mem_comm, d.comm₂₅, mem_bot, d.x₆_eq_one_iff] at h
  have ha : a = 0 := by simpa using h
  rw [ha, d.x₅_zero, one_mul]
  exact hn

theorem mem_W_of_forall_commutatorElement_x₄_eq_one {x : X} (hx : x ∈ d.F)
    (h : ∀ b, ⁅x, d.x₄ b⁆ = 1) : x ∈ d.W := by
  obtain ⟨a, n, hn, rfl⟩ := d.mem_F_iff.1 hx
  have key : ∀ b, d.tr (a * b) = 0 := fun b => by
    have hb := h b
    have hn' : ⁅n, d.x₄ b⁆ ∈ (⊥ : Subgroup X) :=
      d.commutator_W_U₄ ▸ commutator_mem_commutator hn (d.x₄_mem_U₄ b)
    rw [← mem_bot, commutatorElement_mul_mem_iff (le_normalizer_bot_subgroup ⊤ (mem_top _)) hn',
      d.comm₃₄, mem_bot, d.x₆_eq_one_iff] at hb
    exact hb
  rw [d.eq_zero_of_forall_tr_mul key, d.x₃_zero, one_mul]
  exact hn

theorem mem_Y_of_forall_commutatorElement_x₃_eq_one {x : X} (hx : x ∈ d.W)
    (h : ∀ b, ⁅x, d.x₃ b⁆ = 1) : x ∈ d.Y := by
  obtain ⟨a, n, hn, rfl⟩ := d.mem_W_iff.1 hx
  have key : ∀ b, d.tr (a * b) = 0 := fun b => by
    have hb := h b
    have hn' : ⁅n, d.x₃ b⁆ ∈ (⊥ : Subgroup X) := commutatorElement_mem_comm.1
      (d.commutator_M_Y ▸ commutator_mem_commutator (d.F_le_M (d.x₃_mem_F b)) hn)
    rw [← mem_bot, commutatorElement_mul_mem_iff (le_normalizer_bot_subgroup ⊤ (mem_top _)) hn',
      commutatorElement_mem_comm, d.comm₃₄, mem_bot, d.x₆_eq_one_iff] at hb
    rwa [mul_comm] at hb
  rw [d.eq_zero_of_forall_tr_mul key, d.x₄_zero, one_mul]
  exact hn

theorem mem_F_of_commutatorElement_x₅_eq_one {x : X} (hx : x ∈ d.D)
    (h : ⁅x, d.x₅ 1⁆ = 1) : x ∈ d.F := by
  obtain ⟨a, n, hn, rfl⟩ := d.mem_D_iff.1 hx
  have hn' : ⁅n, d.x₅ 1⁆ ∈ (⊥ : Subgroup X) :=
    d.commutator_M_Y ▸ commutator_mem_commutator (d.F_le_M hn) (d.x₅_mem_Y 1)
  rw [← mem_bot, commutatorElement_mul_mem_iff (le_normalizer_bot_subgroup ⊤ (mem_top _)) hn',
    d.comm₂₅, mem_bot, d.x₆_eq_one_iff] at h
  have ha : a = 0 := by simpa using h
  rw [ha, d.x₂_zero, one_mul]
  exact hn

theorem mem_F_of_forall_commutatorElement_x₄_mem_V {x : X} (hx : x ∈ d.M)
    (h : ∀ b, ⁅x, d.x₄ b⁆ ∈ d.V) : x ∈ d.F := by
  obtain ⟨a, n, hn, rfl⟩ := d.mem_M_iff.1 hx
  have key : ∀ b, d.tr (a * b) = 0 := fun b => by
    have hb := h b
    have hn' : ⁅n, d.x₄ b⁆ ∈ d.V := d.commutator_F_F (commutator_mem_commutator hn (d.x₄_mem_F b))
    rw [commutatorElement_mul_mem_iff (d.S_le_normalizer_V (d.U₁_le_S (d.x₁_mem_U₁ a))) hn',
      d.comm₁₄, d.x₅_mem_V_iff] at hb
    exact hb
  rw [d.eq_zero_of_forall_tr_mul key, d.x₁_zero, one_mul]
  exact hn

theorem mem_F_iff_forall {x : X} : x ∈ d.F ↔ x ∈ d.S ∧ ∀ y ∈ d.S, ⁅x, y⁆ ∈ d.W := by
  refine ⟨fun hx => ⟨d.F_le_S hx, fun y hy => commutatorElement_mem_comm.1
    (d.commutator_S_F (commutator_mem_commutator hy hx))⟩, fun ⟨hx, h⟩ => ?_⟩
  exact d.mem_F_of_commutatorElement_x₁_mem_W
    (d.mem_D_of_commutatorElement_x₂_mem_W hx (h _ (d.U₂_le_S (d.x₂_mem_U₂ 1))))
    (h _ (d.U₁_le_S (d.x₁_mem_U₁ 1)))

theorem mem_W_iff_forall {x : X} : x ∈ d.W ↔ x ∈ d.S ∧ ∀ y ∈ d.S, ⁅x, y⁆ ∈ d.Y := by
  refine ⟨fun hx => ⟨d.W_le_S hx, fun y hy => commutatorElement_mem_comm.1
    (d.commutator_S_W (commutator_mem_commutator hy hx))⟩, fun ⟨hx, h⟩ => ?_⟩
  exact d.mem_W_of_forall_commutatorElement_x₁_mem_Y
    (d.mem_F_iff_forall.2 ⟨hx, fun y hy => d.Y_le_W (h y hy)⟩)
    (fun b => h _ (d.U₁_le_S (d.x₁_mem_U₁ b)))

theorem mem_Y_iff_forall {x : X} : x ∈ d.Y ↔ x ∈ d.S ∧ ∀ y ∈ d.S, ⁅x, y⁆ ∈ d.V := by
  refine ⟨fun hx => ⟨d.Y_le_S hx, fun y hy => commutatorElement_mem_comm.1
    (d.commutator_S_Y (commutator_mem_commutator hy hx))⟩, fun ⟨hx, h⟩ => ?_⟩
  exact d.mem_Y_of_forall_commutatorElement_x₁_mem_V
    (d.mem_W_iff_forall.2 ⟨hx, fun y hy => d.V_le_Y (h y hy)⟩)
    (fun b => h _ (d.U₁_le_S (d.x₁_mem_U₁ b)))

theorem mem_V_iff_forall {x : X} : x ∈ d.V ↔ x ∈ d.S ∧ ∀ y ∈ d.S, ⁅x, y⁆ ∈ (⊥ : Subgroup X) := by
  refine ⟨fun hx => ⟨d.V_le_S hx, fun y hy => commutatorElement_mem_comm.1
    (d.commutator_S_V ▸ commutator_mem_commutator hy hx)⟩, fun ⟨hx, h⟩ => ?_⟩
  exact d.mem_V_of_commutatorElement_x₂_eq_one
    (d.mem_Y_iff_forall.2 ⟨hx, fun y hy => (mem_bot.1 (h y hy)).symm ▸ one_mem _⟩)
    (mem_bot.1 (h _ (d.U₂_le_S (d.x₂_mem_U₂ 1))))

theorem S_inf_centralizer_S : d.S ⊓ centralizer (d.S : Set X) = d.V := by
  ext x
  rw [mem_inf_centralizer_iff, d.mem_V_iff_forall]
  simp only [mem_bot]

theorem D_inf_centralizer_D : d.D ⊓ centralizer (d.D : Set X) = d.V := by
  ext x
  rw [mem_inf_centralizer_iff]
  constructor
  · rintro ⟨hx, h⟩
    have hF := d.mem_F_of_commutatorElement_x₅_eq_one hx (h _ (d.F_le_D (d.x₅_mem_F 1)))
    have hW := d.mem_W_of_forall_commutatorElement_x₄_eq_one hF
      (fun b => h _ (d.F_le_D (d.x₄_mem_F b)))
    exact d.mem_V_of_commutatorElement_x₂_eq_one
      (d.mem_Y_of_forall_commutatorElement_x₃_eq_one hW (fun b => h _ (d.F_le_D (d.x₃_mem_F b))))
      (h _ (d.x₂_mem_D 1))
  · intro hx
    exact ⟨d.F_le_D (d.W_le_F (d.Y_le_W (d.V_le_Y hx))), fun y hy => mem_bot.1
      (commutatorElement_mem_comm.1 (d.commutator_S_V ▸
        commutator_mem_commutator (d.D_le_S hy) hx))⟩

theorem F_inf_centralizer_F : d.F ⊓ centralizer (d.F : Set X) = d.Y := by
  ext x
  rw [mem_inf_centralizer_iff]
  constructor
  · rintro ⟨hx, h⟩
    exact d.mem_Y_of_forall_commutatorElement_x₃_eq_one
      (d.mem_W_of_forall_commutatorElement_x₄_eq_one hx (fun b => h _ (d.x₄_mem_F b)))
      (fun b => h _ (d.x₃_mem_F b))
  · intro hx
    exact ⟨d.W_le_F (d.Y_le_W hx), fun y hy => mem_bot.1
      (commutatorElement_mem_comm.1 (d.commutator_M_Y ▸
        commutator_mem_commutator (d.F_le_M hy) hx))⟩

theorem mem_Y_iff_forall_M {x : X} :
    x ∈ d.Y ↔ x ∈ d.M ∧ ∀ y ∈ d.M, ⁅x, y⁆ ∈ (⊥ : Subgroup X) := by
  refine ⟨fun hx => ⟨d.F_le_M (d.W_le_F (d.Y_le_W hx)), fun y hy => commutatorElement_mem_comm.1
    (d.commutator_M_Y ▸ commutator_mem_commutator hy hx)⟩, fun ⟨hx, h⟩ => ?_⟩
  have hF := d.mem_F_of_forall_commutatorElement_x₄_mem_V hx
    (fun b => (mem_bot.1 (h _ (d.F_le_M (d.x₄_mem_F b)))).symm ▸ one_mem _)
  exact (d.F_inf_centralizer_F ▸ mem_inf_centralizer_iff.2 ⟨hF, fun y hy =>
    mem_bot.1 (h y (d.F_le_M hy))⟩ : x ∈ d.Y)

theorem M_inf_centralizer_M : d.M ⊓ centralizer (d.M : Set X) = d.Y := by
  ext x
  rw [mem_inf_centralizer_iff, d.mem_Y_iff_forall_M]
  simp only [mem_bot]

theorem mem_W_iff_forall_M {x : X} : x ∈ d.W ↔ x ∈ d.M ∧ ∀ y ∈ d.M, ⁅x, y⁆ ∈ d.Y := by
  refine ⟨fun hx => ⟨d.F_le_M (d.W_le_F hx), fun y hy => commutatorElement_mem_comm.1
    (d.commutator_S_W (commutator_mem_commutator (d.M_le_S hy) hx))⟩, fun ⟨hx, h⟩ => ?_⟩
  exact d.mem_W_of_forall_commutatorElement_x₁_mem_Y
    (d.mem_F_of_forall_commutatorElement_x₃_mem_Y hx (fun b => h _ (d.F_le_M (d.x₃_mem_F b))))
    (fun b => h _ (d.x₁_mem_M b))

theorem V_le_commutator {H K : Subgroup X} (hH : d.x₃ 1 ∈ H) (hK : d.U₄ ≤ K) :
    d.V ≤ ⁅H, K⁆ := by
  rintro _ ⟨c, rfl⟩
  obtain ⟨b, hb⟩ := d.exists_tr_eq c
  have hb' : fixedTrace d.σ_cube b = c := hb
  have h := commutator_mem_commutator hH (hK (d.x₄_mem_U₄ b))
  rwa [d.comm₃₄, one_mul, hb'] at h

theorem commutator_D_eq : ⁅d.D, d.D⁆ = d.V := by
  refine le_antisymm d.commutator_D_D ?_
  rintro _ ⟨c, rfl⟩
  have h := commutator_mem_commutator (d.x₂_mem_D c) (d.F_le_D (d.x₅_mem_F 1))
  rwa [d.comm₂₅, mul_one] at h

theorem commutator_F_eq : ⁅d.F, d.F⁆ = d.V :=
  le_antisymm d.commutator_F_F (d.V_le_commutator (d.x₃_mem_F 1) (d.U₄_le_W.trans d.W_le_F))

theorem U₅_le_commutator_M : d.U₅ ≤ ⁅d.M, d.M⁆ := by
  rintro _ ⟨c, rfl⟩
  obtain ⟨b, hb⟩ := d.exists_tr_eq c
  have hb' : fixedTrace d.σ_cube b = c := hb
  have h := commutator_mem_commutator (d.x₁_mem_M 1) (d.F_le_M (d.x₄_mem_F b))
  rwa [d.comm₁₄, one_mul, hb'] at h

theorem exists_torus_conj_x₄ {c δ : d.Γ} (hc : c ≠ 0) (hδ : δ ≠ 0) :
    ∃ h, d.torus h * d.x₄ δ * (d.torus h)⁻¹ = d.x₄ c := by
  set ν := c * δ⁻¹ with hν
  have hν0 : ν ≠ 0 := mul_ne_zero hc (inv_ne_zero hδ)
  have hσν : d.σ ν ≠ 0 := (map_ne_zero d.σ).2 hν0
  have hσσν : d.σ (d.σ ν) ≠ 0 := (map_ne_zero d.σ).2 hσν
  have hN : d.nm ν ≠ 0 := fun h0 => by
    have := congrArg Subtype.val h0
    rw [coe_fixedNorm, ZeroMemClass.coe_zero] at this
    exact mul_ne_zero (mul_ne_zero hν0 hσν) hσσν this
  refine ⟨(Units.mk0 (d.nm ν) hN, (Units.mk0 ν hν0)⁻¹), ?_⟩
  rw [d.torus_x₄]
  congr 1
  simp only [Units.val_mk0, Units.val_inv_eq_inv_val, map_inv₀, coe_fixedNorm]
  field_simp
  rw [hν]
  field_simp

theorem U₄_le_commutator_M : d.U₄ ≤ ⁅d.M, d.M⁆ := by
  have hY : d.Y ≤ ⁅d.M, d.M⁆ :=
    sup_le d.U₅_le_commutator_M (d.V_le_commutator (d.F_le_M (d.x₃_mem_F 1))
      (d.U₄_le_W.trans (d.W_le_F.trans d.F_le_M)))
  obtain ⟨γ, hγ⟩ := d.exists_σ_ne
  have hδ : d.σ (d.σ γ) + d.σ γ ≠ 0 := fun h0 =>
    hγ (d.σ.injective (CharTwo.add_eq_zero.1 h0))
  have h₀ : d.x₄ (d.σ (d.σ γ) + d.σ γ) ∈ ⁅d.M, d.M⁆ := by
    have h := commutator_mem_commutator (d.x₁_mem_M 1) (d.F_le_M (d.x₃_mem_F γ))
    rw [d.comm₁₃, mul_assoc, mul_mem_cancel_right (hY (mul_mem (d.x₅_mem_Y _)
      (d.x₆_mem_Y _)))] at h
    simpa using h
  rintro _ ⟨c, rfl⟩
  by_cases hc : c = 0
  · rw [hc, d.x₄_zero]
    exact one_mem _
  · obtain ⟨h, hh⟩ := d.exists_torus_conj_x₄ hc hδ
    rw [← hh]
    exact conj_mem_commutator (d.J_le_normalizer_M ⟨h, rfl⟩) h₀

theorem commutator_M_eq : ⁅d.M, d.M⁆ = d.W := by
  refine le_antisymm d.commutator_M_M (sup_le d.U₄_le_commutator_M (sup_le d.U₅_le_commutator_M
    (d.V_le_commutator (d.F_le_M (d.x₃_mem_F 1)) (d.U₄_le_W.trans (d.W_le_F.trans d.F_le_M)))))

theorem commutator_S_eq : ⁅d.S, d.S⁆ = d.F := by
  have hW : d.W ≤ ⁅d.S, d.S⁆ := d.commutator_M_eq ▸ commutator_mono d.M_le_S d.M_le_S
  refine le_antisymm d.commutator_S_S (sup_le ?_ hW)
  rintro _ ⟨c, rfl⟩
  have h := commutator_mem_commutator (d.U₁_le_S (d.x₁_mem_U₁ c)) (d.U₂_le_S (d.x₂_mem_U₂ 1))
  rw [d.comm₁₂, mul_assoc, mul_mem_cancel_right (hW (mul_mem (d.x₄_mem_W _) (d.x₅_mem_W _)))]
    at h
  simpa using h

theorem mul_self_mem_W_of_mem_F {f : X} (hf : f ∈ d.F) : f * f ∈ d.W := by
  obtain ⟨a, w, hw, rfl⟩ := d.mem_F_iff.1 hf
  have e : d.x₃ a * w * (d.x₃ a * w) = d.x₃ a * w * (d.x₃ a)⁻¹ * w := by
    rw [d.x₃_inv]
    group
  rw [e]
  exact mul_mem ((mem_normalizer_iff.1
    (d.S_le_normalizer_W (d.U₃_le_S (d.x₃_mem_U₃ a))) w).1 hw) hw

theorem mem_D_or_mem_M_of_mul_self_mem_W {s : X} (hs : s ∈ d.S) (h : s * s ∈ d.W) :
    s ∈ d.D ∨ s ∈ d.M := by
  obtain ⟨a, n, hn, rfl⟩ := d.mem_S_iff.1 hs
  obtain ⟨b, f, hf, rfl⟩ := d.mem_D_iff.1 hn
  have hp : d.x₁ a * d.x₂ b * (d.x₁ a * d.x₂ b) = ⁅d.x₁ a, d.x₂ b⁆ := by
    rw [commutatorElement_def, d.x₁_inv, d.x₂_inv]
    group
  have hpS : (d.x₁ a * d.x₂ b)⁻¹ ∈ d.S :=
    inv_mem (mul_mem (d.U₁_le_S (d.x₁_mem_U₁ a)) (d.U₂_le_S (d.x₂_mem_U₂ b)))
  have e : d.x₁ a * (d.x₂ b * f) * (d.x₁ a * (d.x₂ b * f)) =
      ⁅d.x₁ a, d.x₂ b⁆ * (⁅(d.x₁ a * d.x₂ b)⁻¹, f⁆ * (f * f)) := by
    rw [← hp, commutatorElement_def]
    group
  rw [e, mul_mem_cancel_right (mul_mem (d.commutator_S_F (commutator_mem_commutator hpS hf))
    (d.mul_self_mem_W_of_mem_F hf)), d.comm₁₂, mul_assoc,
    mul_mem_cancel_right (mul_mem (d.x₄_mem_W _) (d.x₅_mem_W _)), d.x₃_mem_W_iff] at h
  rcases mul_eq_zero.1 h with ha | hb
  · left
    rw [ha, d.x₁_zero, one_mul]
    exact hn
  · right
    rw [show b = 0 from Subtype.ext hb, d.x₂_zero, one_mul]
    exact d.mem_M_iff.2 ⟨a, f, hf, rfl⟩

theorem not_D_le_M : ¬ d.D ≤ d.M := fun h =>
  one_ne_zero (d.x₂_mem_M_iff.1 (h (d.x₂_mem_D 1)))

instance normal_W_subgroupOf_S : (d.W.subgroupOf d.S).Normal :=
  (normal_subgroupOf_iff_le_normalizer d.W_le_S).2 d.S_le_normalizer_W

theorem u_conj_x₂ (a : d.Γ₀) : d.u * d.x₂ a * d.u⁻¹ = d.x₅ a := by
  rw [d.u_inv, d.u_x₂]

theorem u_conj_x₅ (a : d.Γ₀) : d.u * d.x₅ a * d.u⁻¹ = d.x₂ a := by
  rw [← d.u_conj_x₂ a, conj_conj_of_mul_self d.u_mul_self]

theorem u_conj_x₆ (a : d.Γ₀) : d.u * d.x₆ a * d.u⁻¹ = d.x₆ a := by
  rw [d.u_inv, d.u_x₆]

theorem v_conj_x₁ (a : d.Γ) : d.v * d.x₁ a * d.v⁻¹ = d.x₃ a := by
  rw [d.v_inv, d.v_x₁]

theorem v_conj_x₃ (a : d.Γ) : d.v * d.x₃ a * d.v⁻¹ = d.x₁ a := by
  rw [← d.v_conj_x₁ a, conj_conj_of_mul_self d.v_mul_self]

theorem v_conj_x₄ (a : d.Γ) : d.v * d.x₄ a * d.v⁻¹ = d.x₄ a := by
  rw [d.v_inv, d.v_x₄]

theorem v_conj_x₅ (a : d.Γ₀) : d.v * d.x₅ a * d.v⁻¹ = d.x₆ a := by
  rw [d.v_inv, d.v_x₅]

theorem v_conj_x₆ (a : d.Γ₀) : d.v * d.x₆ a * d.v⁻¹ = d.x₅ a := by
  rw [← d.v_conj_x₅ a, conj_conj_of_mul_self d.v_mul_self]

theorem uv_cube : d.u * d.v * d.u * d.v * d.u * d.v = d.v * d.u * d.v * d.u * d.v * d.u := by
  have h6 : (d.u * d.v) ^ 6 = 1 := d.orderOf_u_mul_v ▸ pow_orderOf_eq_one (d.u * d.v)
  have hx : d.u * d.v * d.u * d.v * d.u * d.v * (d.u * d.v * d.u * d.v * d.u * d.v) = 1 := by
    rw [← h6]
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  rw [eq_inv_of_mul_eq_one_left hx]
  simp only [mul_inv_rev, d.u_inv, d.v_inv, mul_assoc]

theorem u_mem_normalizer_V : d.u ∈ normalizer (d.V : Set X) :=
  have := d.finite
  mem_normalizer_fintype fun _ ⟨a, ha⟩ => ⟨a, by rw [← ha, d.u_conj_x₆]⟩

end TrialityD4Data

end CFSG.LocalAnalysis.EvenBN.TrialityD4
