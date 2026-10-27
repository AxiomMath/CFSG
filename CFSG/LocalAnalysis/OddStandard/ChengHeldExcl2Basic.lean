module

public import CFSG.LocalAnalysis.OddStandard.ChengHeldSec2Open
public import CFSG.LocalAnalysis.OddStandard.ChengHeldSec2Img
public import Certificates.Certificate6137
public import Certificates.Certificate6138
public import Certificates.Certificate6139
public import CFSG.LocalAnalysis.OddStandard.ChengHeldModelNormalizer
public import CFSG.LocalAnalysis.OddStandard.ChengHeldSec1Basic
public import CFSG.LocalAnalysis.OddStandard.ChengHeldSetupZStar

public section

namespace CFSG.OddStandard.ChengHeld.Excl2

open Subgroup CFSG.OddStandard.ChengHeldData
open CFSG.OddStandard.ChengHeld.ChartShape (cj_mul cj_inv cj_cj cj_of_commute cm_eq_one_iff)

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}

structure Cfg (d : Datum A) (α : ℕ) where
  h : Hyp G A
  hα : α ≤ 1
  hc : Nat.card ↥(d.X ⊓ A ⊓ centralizer (A : Set G)) = 4
  c : Chart4 d α
  hP : chPresOK = true
  hQ : chPropsOK = true
  hS2 : chSec2OK = true
  hN : normalizer (A : Set G) = (A ⊔ centralizer (A : Set G)) ⊔ d.X
  g : G
  g_norm : ∀ s ∈ d.S, g⁻¹ * s * g ∈ d.S
  g_act : GAct α c.t c.pi c.tau c.mu c.lam c.ze c.xi g
  kin : c.kinds = Set.univ

@[expose] def kidx : Kind → Fin 3
  | .field => 0
  | .graph => 1
  | .unitary => 2

theorem kidx_injective : Function.Injective kidx := by
  intro a b h
  cases a <;> cases b <;> first | rfl | (exfalso; revert h; decide)

open Classical in
theorem exists_cls {d : Datum A} {α : ℕ} (c : Chart4 d α) :
    ∃ cls : G → Fin 4, ∀ y₁ ∈ d.X, ∀ y₂ ∈ d.X, cls y₁ = cls y₂ → y₁⁻¹ * y₂ ∈ d.QS := by
  let cls : G → Fin 4 := fun y =>
    if h : y ∈ d.X ∧ y ∉ d.QS then (kidx (c.cover y h.1 h.2).choose).succ else 0
  refine ⟨cls, fun y₁ hy₁ y₂ hy₂ heq => ?_⟩
  by_cases h1 : y₁ ∈ d.QS <;> by_cases h2 : y₂ ∈ d.QS
  · exact mul_mem (d.QS.inv_mem h1) h2
  · exfalso
    have e2 : cls y₂ = (kidx (c.cover y₂ hy₂ h2).choose).succ := by simp [cls, hy₂, h2]
    have e1 : cls y₁ = 0 := by simp [cls, h1]
    rw [e1, e2] at heq
    exact (Fin.succ_ne_zero _) heq.symm
  · exfalso
    have e1 : cls y₁ = (kidx (c.cover y₁ hy₁ h1).choose).succ := by simp [cls, hy₁, h1]
    have e2 : cls y₂ = 0 := by simp [cls, h2]
    rw [e1, e2] at heq
    exact (Fin.succ_ne_zero _) heq
  · have e1 : cls y₁ = (kidx (c.cover y₁ hy₁ h1).choose).succ := by simp [cls, hy₁, h1]
    have e2 : cls y₂ = (kidx (c.cover y₂ hy₂ h2).choose).succ := by simp [cls, hy₂, h2]
    rw [e1, e2] at heq
    have hk : (c.cover y₁ hy₁ h1).choose = (c.cover y₂ hy₂ h2).choose :=
      kidx_injective (Fin.succ_injective _ heq)
    obtain ⟨y0, hrep, u, hu, hy1⟩ := (c.cover y₁ hy₁ h1).choose_spec
    obtain ⟨y0', hrep', u', hu', hy2⟩ := (c.cover y₂ hy₂ h2).choose_spec
    rw [hk] at hrep
    rw [hrep'] at hrep
    obtain rfl : y0' = y0 := Option.some_injective _ hrep
    obtain ⟨hy0X, -, -⟩ := c.rep_mem _ y0' hrep'
    have : y₁⁻¹ * y₂ = y0'⁻¹ * (u⁻¹ * u') * y0' := by rw [hy1, hy2]; group
    rw [this]
    exact ChartShape.conj_inv_mem_QS d hy0X (mul_mem (d.QS.inv_mem hu) hu')

omit [Finite G] in
theorem isConj_of_cj_eq {a b s : G} (h : cj a s = b) : IsConj a b :=
  isConj_iff.2 ⟨s⁻¹, by rw [← h]; unfold cj; group⟩

namespace Cfg

variable {d : Datum A} {α : ℕ} (K : Cfg d α)

include K

theorem sf : K.c.SFacts := K.c.sFacts K.hα K.h K.hP K.hQ

theorem q_mem_Q : d.q ∈ d.Q := d.q_mem_Q K.h

theorem t_comm {s : G} (hs : s ∈ d.S) : s * K.c.t = K.c.t * s :=
  K.c.t_comm K.hα K.h K.hP K.hQ s hs

theorem q_comm_X {x : G} (hx : x ∈ d.X) : x * d.q = d.q * x :=
  mem_centralizer_singleton_iff.mp ((d.q_mem_X K.h).2 hx)

theorem exists_conj_mem_QS {E : Subgroup G} {g₀ : G} (hE : 4 < Nat.card E)
    (hX : ∀ v ∈ E, g₀ * v * g₀⁻¹ ∈ d.X) : ∃ x ∈ E, x ≠ 1 ∧ g₀ * x * g₀⁻¹ ∈ d.QS := by
  classical
  obtain ⟨cls, hcls⟩ := exists_cls K.c
  have hs : 4 < (Set.toFinite (E : Set G)).toFinset.card := by
    rw [← Set.ncard_eq_toFinset_card (E : Set G) (Set.toFinite _), ← Nat.card_coe_set_eq]
    exact hE
  obtain ⟨a, ha, b, hb, hab, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := (Set.toFinite (E : Set G)).toFinset) (t := (Finset.univ : Finset (Fin 4)))
    (f := fun v => cls (g₀ * v * g₀⁻¹)) (by simpa using hs) (fun _ _ => Finset.mem_univ _)
  rw [Set.Finite.mem_toFinset] at ha hb
  refine ⟨a⁻¹ * b, mul_mem (inv_mem ha) hb, fun h1 => hab ?_, ?_⟩
  · exact (inv_mul_eq_one.mp h1)
  · have := hcls _ (hX a ha) _ (hX b hb) heq
    have e : g₀ * (a⁻¹ * b) * g₀⁻¹ = (g₀ * a * g₀⁻¹)⁻¹ * (g₀ * b * g₀⁻¹) := by group
    rw [e]
    exact this

theorem fuse_aux {z g₀ x : G}
    (hzX : z ∈ d.X) (hzQS : z ∉ d.QS) (hg₀ : g₀⁻¹ * d.q * g₀ = z)
    (hgX : ∀ y ∈ d.X, y * z = z * y → g₀ * y * g₀⁻¹ ∈ d.X) (hxX : x ∈ d.X) (hxQS : x ∈ d.QS)
    (hxz : x * z = z * x) (hx2 : x * x = 1) (hx1 : x ≠ 1) (hx' : g₀ * x * g₀⁻¹ ∈ d.QS) :
    IsConj K.c.pi x ∧ IsConj K.c.pi (z * x) := by
  have hq2 : d.q * d.q = 1 := Sec1.q_mul_self d
  have hq' : g₀ * z * g₀⁻¹ = d.q := by rw [← hg₀]; group
  have hxz' : x ≠ z := fun h => hzQS (h ▸ hxQS)
  have hx'X : g₀ * x * g₀⁻¹ ∈ d.X := hgX x hxX hxz
  have hx'2 : (g₀ * x * g₀⁻¹) * (g₀ * x * g₀⁻¹) = 1 := by
    calc (g₀ * x * g₀⁻¹) * (g₀ * x * g₀⁻¹) = g₀ * (x * x) * g₀⁻¹ := by group
      _ = 1 := by rw [hx2]; group
  have hx'1 : g₀ * x * g₀⁻¹ ≠ 1 := fun h => hx1 (by
    have : g₀ * x * g₀⁻¹ = g₀ * 1 * g₀⁻¹ := by rw [h]; group
    exact mul_left_cancel (mul_right_cancel this))
  have hx'q : g₀ * x * g₀⁻¹ ≠ d.q := fun h => hxz' (by
    have : g₀ * x * g₀⁻¹ = g₀ * z * g₀⁻¹ := by rw [h, hq']
    exact mul_left_cancel (mul_right_cancel this))
  have hc1 : IsConj (g₀ * x * g₀⁻¹) K.c.pi :=
    K.c.involution_QS_conj_pi K.hα K.h K.hP K.hQ K.hc hx' hx'2 hx'1 hx'q
  have hxx' : IsConj x (g₀ * x * g₀⁻¹) := isConj_of_cj_eq (s := g₀⁻¹) (by unfold cj; group)
  refine ⟨(hxx'.trans hc1).symm, ?_⟩
  have hzxX : z * x ∈ d.X := d.X.mul_mem hzX hxX
  have hzxz : (z * x) * z = z * (z * x) := by
    calc z * x * z = z * (x * z) := by group
      _ = z * (z * x) := by rw [hxz]
  have hzx' : g₀ * (z * x) * g₀⁻¹ = d.q * (g₀ * x * g₀⁻¹) := by
    calc g₀ * (z * x) * g₀⁻¹ = (g₀ * z * g₀⁻¹) * (g₀ * x * g₀⁻¹) := by group
      _ = d.q * (g₀ * x * g₀⁻¹) := by rw [hq']
  have hqx'QS : d.q * (g₀ * x * g₀⁻¹) ∈ d.QS := mul_mem (mem_sup_left K.q_mem_Q) hx'
  have hqx'2 : (d.q * (g₀ * x * g₀⁻¹)) * (d.q * (g₀ * x * g₀⁻¹)) = 1 := by
    have hc : (g₀ * x * g₀⁻¹) * d.q = d.q * (g₀ * x * g₀⁻¹) := K.q_comm_X hx'X
    calc (d.q * (g₀ * x * g₀⁻¹)) * (d.q * (g₀ * x * g₀⁻¹))
        = d.q * ((g₀ * x * g₀⁻¹) * d.q) * (g₀ * x * g₀⁻¹) := by group
      _ = d.q * (d.q * (g₀ * x * g₀⁻¹)) * (g₀ * x * g₀⁻¹) := by rw [hc]
      _ = (d.q * d.q) * ((g₀ * x * g₀⁻¹) * (g₀ * x * g₀⁻¹)) := by group
      _ = 1 := by rw [hq2, hx'2, mul_one]
  have hqx'1 : d.q * (g₀ * x * g₀⁻¹) ≠ 1 := fun h => hx'q (by
    rw [eq_inv_of_mul_eq_one_right h, inv_eq_of_mul_eq_one_right hq2])
  have hqx'q : d.q * (g₀ * x * g₀⁻¹) ≠ d.q := fun h =>
    hx'1 (mul_left_cancel (h.trans (mul_one _).symm))
  have hc2 : IsConj (d.q * (g₀ * x * g₀⁻¹)) K.c.pi :=
    K.c.involution_QS_conj_pi K.hα K.h K.hP K.hQ K.hc hqx'QS hqx'2 hqx'1 hqx'q
  have hzx'c : IsConj (z * x) (d.q * (g₀ * x * g₀⁻¹)) :=
    isConj_of_cj_eq (s := g₀⁻¹) (by unfold cj; rw [← hzx']; group)
  exact (hzx'c.trans hc2).symm

theorem act_mul_Q {k : Kind} {y x : G} (hy : y ∈ d.X) (hx : x ∈ d.Q)
    (hact : k.Act α K.c.t K.c.pi K.c.tau K.c.mu K.c.lam K.c.ze K.c.xi y) :
    k.Act α K.c.t K.c.pi K.c.tau K.c.mu K.c.lam K.c.ze K.c.xi (y * x) := by
  have key : ∀ a ∈ d.S, cj a (y * x) = cj a y := by
    intro a ha
    rw [← cj_cj]
    have hb : cj a y ∈ d.S := d.conj_inv_mem_S hy a ha
    exact cj_of_commute (d.comm_Q_S hx hb)
  have mt : K.c.t ∈ d.S := K.c.t_mem.2
  have mpi : K.c.pi ∈ d.S := K.c.mem.1
  have mtau : K.c.tau ∈ d.S := K.c.mem.2.1
  have mmu : K.c.mu ∈ d.S := K.c.mem.2.2.1
  have mlam : K.c.lam ∈ d.S := K.c.mem.2.2.2.1
  have mze : K.c.ze ∈ d.S := K.c.mem.2.2.2.2.1
  have mxi : K.c.xi ∈ d.S := K.c.mem.2.2.2.2.2
  cases k <;> by_cases hα0 : α = 0 <;>
    simp only [Kind.Act, hα0, ↓reduceIte] at hact ⊢ <;>
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hact <;>
    exact ⟨(key _ mt).trans h1, (key _ mpi).trans h2, (key _ mtau).trans h3, (key _ mmu).trans h4,
      (key _ mlam).trans h5, (key _ mze).trans h6, (key _ mxi).trans h7⟩

theorem exists_pure_involution
    (hnc : ¬ IsConj d.q K.c.pi) :
    ∃ k y x, K.c.rep k = some y ∧ x ∈ d.Q ∧ IsConj d.q (y * x) ∧ (y * x) * (y * x) = 1 := by
  obtain ⟨g₀, hg₀X, hg₀ne⟩ := d.exists_conj_ne K.h
  have hqq : d.q * d.q = 1 := Sec1.q_mul_self d
  have hzq : IsConj d.q (g₀⁻¹ * d.q * g₀) := isConj_iff.2 ⟨g₀⁻¹, by simp⟩
  have hz2 : (g₀⁻¹ * d.q * g₀) * (g₀⁻¹ * d.q * g₀) = 1 := by
    calc (g₀⁻¹ * d.q * g₀) * (g₀⁻¹ * d.q * g₀) = g₀⁻¹ * (d.q * d.q) * g₀ := by group
      _ = 1 := by rw [hqq]; group
  have hz1 : g₀⁻¹ * d.q * g₀ ≠ 1 := fun h1 => Sec1.q_ne_one d (by
    have h2 : g₀⁻¹ * d.q * g₀ = g₀⁻¹ * 1 * g₀ := by rw [h1]; group
    exact mul_left_cancel (mul_right_cancel h2))
  by_cases hzQS : g₀⁻¹ * d.q * g₀ ∈ d.QS
  · exact absurd (hzq.trans (K.c.involution_QS_conj_pi K.hα K.h K.hP K.hQ K.hc hzQS hz2 hz1 hg₀ne))
      hnc
  · obtain ⟨k, y0, hrep, u, hu, hzy⟩ := K.c.cover _ hg₀X hzQS
    obtain ⟨s, hs, x, hx, hcj⟩ := K.c.act_of_involution_rep K.hα K.h K.hP K.hQ K.hS2 K.hc hrep hz2
      ⟨u, hu, hzy⟩
    refine ⟨k, y0, x, hrep, hx, hzq.trans (isConj_of_cj_eq hcj), ?_⟩
    rw [← hcj, ← cj_mul, hz2]
    unfold cj
    group

end Cfg

end CFSG.OddStandard.ChengHeld.Excl2
