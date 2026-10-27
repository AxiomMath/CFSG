module

public import CFSG.LocalAnalysis.OddStandard.ChengHeldExcl1Z
public import CFSG.LocalAnalysis.OddStandard.ChengHeldSec2Img

public section

namespace CFSG.OddStandard.ChengHeld

open Subgroup CFSG.OddStandard.ChengHeldData

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {d : Datum A} {α : ℕ}

theorem Chart4.false_of_acts_through_S
    (hα : α ≤ 1) (c : Chart4 d α) (h : Hyp G A)
    (hP : chPresOK = true) (hQ : chPropsOK = true) (hS2 : chSec2OK = true)
    (hc : Nat.card ↥(d.X ⊓ A ⊓ centralizer (A : Set G)) = 4) {g : G}
    (hg : ∀ s ∈ d.S, g⁻¹ * s * g ∈ d.S) (hact : GAct α c.t c.pi c.tau c.mu c.lam c.ze c.xi g)
    (hX : ∀ x ∈ d.X, ∃ s ∈ d.S, ∀ v ∈ c.V, x * v * x⁻¹ = s * v * s⁻¹)
    (hfus : IsConj d.q c.pi) : False := by
  have hS := c.sFacts hα h hP hQ
  have h8 := c.card_X_eq_eight_mul_of_isConj hα h hP hQ hS2 hc hg hact hfus
  set ρ := c.V.normalizerMonoidHom with hρ
  have hXN : d.X ≤ normalizer (c.V : Set G) := fun x hx =>
    mem_normalizer_iff.2 fun v => (c.X_normalizes hα h hP hQ hS2 hc hx).2 v
  have hSN := c.S_le_normalizer_V hα h hP hQ
  let f : ↥d.X →* MulAut ↥c.V := ρ.comp (Subgroup.inclusion hXN)
  let fS : ↥d.S →* MulAut ↥c.V := ρ.comp (Subgroup.inclusion hSN)
  have hker : f.ker = (centralizer (c.V : Set G)).subgroupOf d.X := by
    ext x
    have h1 : x ∈ f.ker ↔ Subgroup.inclusion hXN x ∈ ρ.ker := Iff.rfl
    rw [h1, hρ, Subgroup.normalizerMonoidHom_ker, mem_subgroupOf, mem_subgroupOf]
    rfl
  have hkercard : Nat.card f.ker = Nat.card ↥(d.X ⊓ centralizer (c.V : Set G)) := by
    rw [hker]
    exact Nat.card_congr
      { toFun := fun x => ⟨x.1.1, x.1.2, x.2⟩
        invFun := fun y => ⟨⟨y.1, y.2.1⟩, y.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hmul := Subgroup.card_ker_mul_card_range f
  rw [h8, ← hkercard] at hmul
  have hkpos : 0 < Nat.card f.ker := Nat.card_pos
  have hrange8 : Nat.card f.range = 8 := by
    have : Nat.card f.ker * Nat.card f.range = Nat.card f.ker * 8 := by rw [hmul, mul_comm]
    exact Nat.eq_of_mul_eq_mul_left hkpos this
  have hWker : c.W.subgroupOf d.S ≤ fS.ker := by
    intro s hs
    rw [mem_subgroupOf] at hs
    rw [MonoidHom.mem_ker]
    refine MulEquiv.ext fun v => Subtype.ext ?_
    have h3 : ((fS s v : ↥c.V) : G) = (s : G) * v * (s : G)⁻¹ :=
      Sec2Aux.normalizerMonoidHom_coe (Subgroup.inclusion hSN s) v
    rw [h3, MulAut.one_apply]
    have := mem_centralizer_iff.1 hs.2 v v.2
    calc (s : G) * v * (s : G)⁻¹ = (v * s) * (s : G)⁻¹ := by rw [← this]
      _ = v := by group
  have hWcard : Nat.card (c.W.subgroupOf d.S) = 64 := by
    rw [← hS.card_W]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hkS : 64 ≤ Nat.card fS.ker := hWcard ▸ Subgroup.card_le_of_le hWker
  have hmulS := Subgroup.card_ker_mul_card_range fS
  rw [hS.card_S] at hmulS
  have hrS : Nat.card fS.range ≤ 4 := by
    have : 64 * Nat.card fS.range ≤ Nat.card fS.ker * Nat.card fS.range :=
      Nat.mul_le_mul_right _ hkS
    omega
  have hle : f.range ≤ fS.range := by
    rintro φ ⟨x, rfl⟩
    obtain ⟨s, hs, hxs⟩ := hX x x.2
    refine ⟨⟨s, hs⟩, MulEquiv.ext fun v => Subtype.ext ?_⟩
    have h3 : ((fS ⟨s, hs⟩ v : ↥c.V) : G) = s * v * s⁻¹ :=
      Sec2Aux.normalizerMonoidHom_coe (Subgroup.inclusion hSN ⟨s, hs⟩) v
    have h4 : ((f x v : ↥c.V) : G) = (x : G) * v * (x : G)⁻¹ :=
      Sec2Aux.normalizerMonoidHom_coe (Subgroup.inclusion hXN x) v
    rw [h3, h4]
    exact (hxs v v.2).symm
  have := Subgroup.card_le_of_le hle
  omega

theorem Chart4.excl_QS_core
    (hα : α ≤ 1) (c : Chart4 d α) (h : Hyp G A) (hP : chPresOK = true) (hQ : chPropsOK = true)
    (hS2 : chSec2OK = true) (hc : Nat.card ↥(d.X ⊓ A ⊓ centralizer (A : Set G)) = 4) {g : G}
    (hg : ∀ s ∈ d.S, g⁻¹ * s * g ∈ d.S) (hact : GAct α c.t c.pi c.tau c.mu c.lam c.ze c.xi g)
    (hk : c.kinds = ∅) : False := by
  have hXQS : ∀ x ∈ d.X, x ∈ d.QS := by
    intro x hx
    by_contra hxQS
    obtain ⟨k, y, hrep, -⟩ := c.cover x hx hxQS
    have hmem : k ∈ c.kinds := by simp [Chart4.kinds, hrep]
    rw [hk] at hmem
    exact hmem
  obtain ⟨i, hiX, hi2, hi1, hiq, hqi⟩ := d.exists_conj_involution h
  have hfus : IsConj d.q c.pi :=
    hqi.trans (c.involution_QS_conj_pi hα h hP hQ hc (hXQS i hiX) hi2 hi1 hiq)
  refine c.false_of_acts_through_S hα h hP hQ hS2 hc hg hact (fun x hx => ?_) hfus
  obtain ⟨u, hu, s, hs, rfl⟩ := d.mem_QS_iff.1 (hXQS x hx)
  exact ⟨s, hs, fun v hv => d.conj_QS_on_S hu hs (c.V_le_S h hv)⟩

end CFSG.OddStandard.ChengHeld
