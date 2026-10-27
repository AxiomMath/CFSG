module

public import CFSG.GH74.Uniqueness.SU.SU13TB3Gen
public import CFSG.GH74.Uniqueness.SU.SU13Data
public import CFSG.GroupTheory.OddInversion

public section

namespace CFSG.GH74.Uniqueness.SU.SU13

open Subgroup CFSG.GH74.Uniqueness.SU.SU4 CFSG.GH74.Uniqueness.SU.SU13.TB

variable {G : Type} [Group G] [Finite G] {z : G}

omit [Finite G] in
theorem zpowers_comm_of_mem_centralizer {s x : G} (hx : x ∈ centralizer ({s} : Set G)) {c : G}
    (hc : c ∈ zpowers s) : c * x = x * c := by
  obtain ⟨k, rfl⟩ := hc
  have hxs : Commute x s := (mem_centralizer_singleton_iff.mp hx)
  exact ((hxs.symm).zpow_left k).eq

theorem W_inf_centralizer_le (e : Elts G z) (f : FPart10 z e) :
    oc (centralizer ({e.s₁} : Set G)) ⊓ centralizer ({z} : Set G) ≤ zpowers e.s₁ := by
  intro x hx
  obtain ⟨hxW, hxz⟩ := mem_inf.mp hx
  have hxX : x ∈ centralizer ({e.s₁} : Set G) := oc_le _ hxW
  have hxXH : x ∈ centralizer ({e.s₁} : Set G) ⊓ centralizer ({z} : Set G) := mem_inf.mpr ⟨hxX, hxz⟩
  rw [f.cent] at hxXH
  obtain ⟨p, hp, a, ha, rfl⟩ := SU1.mem_sup_of_commute (A := zpowers e.s₁) (B := f.F)
    (fun p hp a ha => zpowers_comm_of_mem_centralizer
      (mem_centralizer_singleton_iff.mpr (f.F_s₁ a ha)) hp) hxXH
  have hpW : p ∈ oc (centralizer ({e.s₁} : Set G)) := by
    refine le_oc_of_normal_odd ?_ ?_ ?_ hp
    · exact (zpowers_le).mpr (mem_centralizer_singleton_iff.mpr rfl)
    · intro g hg n hn
      have := zpowers_comm_of_mem_centralizer hg hn
      rw [← this]; simpa using hn
    · rw [Nat.card_zpowers, e.s₁_ord]; decide
  have haW : a ∈ oc (centralizer ({e.s₁} : Set G)) := by
    have := (oc (centralizer ({e.s₁} : Set G))).mul_mem (inv_mem hpW) hxW
    simpa using this
  have hN : (oc (centralizer ({e.s₁} : Set G)) ⊓ f.F) = ⊥ := by
    refine f.F_noOdd _ inf_le_right ?_ ?_
    · intro g hg n hn
      obtain ⟨hnW, hnF⟩ := mem_inf.mp hn
      have hgX : g ∈ centralizer ({e.s₁} : Set G) := mem_centralizer_singleton_iff.mpr (f.F_s₁ g hg)
      exact mem_inf.mpr ⟨conj_mem_oc hgX hnW, f.F.mul_mem (f.F.mul_mem hg hnF) (f.F.inv_mem hg)⟩
    · exact Odd.of_dvd_nat (odd_card_oc _) (Subgroup.card_dvd_of_le inf_le_left)
  have ha1 : a = 1 := by
    have : a ∈ oc (centralizer ({e.s₁} : Set G)) ⊓ f.F := mem_inf.mpr ⟨haW, ha⟩
    rw [hN] at this
    exact mem_bot.mp this
  rw [ha1, mul_one]
  exact hp

omit [Finite G] in
theorem z_mem_centralizer (e : Elts G z) (f : FPart10 z e) :
    z ∈ centralizer ({e.s₁} : Set G) := mem_centralizer_singleton_iff.mpr (f.F_s₁ z f.z_mem)

theorem z_inv_mod (hz : orderOf z = 2) (e : Elts G z) (f : FPart10 z e) {w : G}
    (hw : w ∈ oc (centralizer ({e.s₁} : Set G))) :
    ∃ c ∈ zpowers e.s₁, z * w * z⁻¹ = c * c * w⁻¹ := by
  have hzX := z_mem_centralizer e f
  have hzN : z ∈ normalizer ((oc (centralizer ({e.s₁} : Set G)) : Subgroup G) : Set G) :=
    le_normalizer_oc _ hzX
  obtain ⟨hbij, -⟩ := CFSG.OddInversion.odd_involution_product_decomposition
    (odd_card_oc (centralizer ({e.s₁} : Set G))) hz hzN
  obtain ⟨⟨c, j⟩, ⟨hc, hj⟩, hcj⟩ := hbij.surjOn hw
  obtain ⟨hcW, hcz⟩ := mem_inf.mp hc
  have hcP : c ∈ zpowers e.s₁ := W_inf_centralizer_le e f (mem_inf.mpr ⟨hcW, hcz⟩)
  have hjW := hj.1
  have hjz : z * j * z⁻¹ = j⁻¹ := hj.2
  have hczz : c * z = z * c := mem_centralizer_singleton_iff.mp hcz
  have hcomm : c * j = j * c := zpowers_comm_of_mem_centralizer (oc_le _ hjW) hcP
  have hcomm' : c * j⁻¹ = j⁻¹ * c := (Commute.inv_right (show Commute c j from hcomm)).eq
  refine ⟨c, hcP, ?_⟩
  have hcjw : c * j = w := hcj
  rw [← hcjw]
  calc z * (c * j) * z⁻¹ = (z * c * z⁻¹) * (z * j * z⁻¹) := by group
    _ = c * j⁻¹ := by rw [hjz, show z * c * z⁻¹ = c by rw [← hczz]; group]
    _ = c * (j⁻¹ * c) * c⁻¹ := by group
    _ = c * (c * j⁻¹) * c⁻¹ := by rw [hcomm']
    _ = c * c * (c * j)⁻¹ := by rw [mul_inv_rev]; group

theorem comm_mem_P (hz : orderOf z = 2) (e : Elts G z) (f : FPart10 z e) {w w' : G}
    (hw : w ∈ oc (centralizer ({e.s₁} : Set G))) (hw' : w' ∈ oc (centralizer ({e.s₁} : Set G))) :
    w * w' * w⁻¹ * w'⁻¹ ∈ zpowers e.s₁ := by
  set W := oc (centralizer ({e.s₁} : Set G)) with hW
  have key : ∀ {w w' : G}, w ∈ W → w' ∈ W → w⁻¹ * w'⁻¹ * w * w' ∈ zpowers e.s₁ := by
    intro w w' hw hw'
    obtain ⟨c, hc, h1⟩ := z_inv_mod hz e f hw
    obtain ⟨c', hc', h2⟩ := z_inv_mod hz e f hw'
    obtain ⟨c'', hc'', h3⟩ := z_inv_mod hz e f (W.mul_mem hw hw')
    have hwX : w⁻¹ ∈ centralizer ({e.s₁} : Set G) := (centralizer ({e.s₁} : Set G)).inv_mem (oc_le _ hw)
    have hc'w : Commute c' w⁻¹ := zpowers_comm_of_mem_centralizer hwX hc'
    have heq : c * c * (c' * c') * (w⁻¹ * w'⁻¹) = c'' * c'' * (w'⁻¹ * w⁻¹) := by
      have e1 : z * (w * w') * z⁻¹ = (z * w * z⁻¹) * (z * w' * z⁻¹) := by group
      rw [h3, h1, h2] at e1
      calc c * c * (c' * c') * (w⁻¹ * w'⁻¹) = c * c * ((c' * c') * w⁻¹) * w'⁻¹ := by group
        _ = c * c * (w⁻¹ * (c' * c')) * w'⁻¹ := by rw [(hc'w.mul_left hc'w).eq]
        _ = c * c * w⁻¹ * (c' * c' * w'⁻¹) := by group
        _ = c'' * c'' * (w * w')⁻¹ := e1.symm
        _ = c'' * c'' * (w'⁻¹ * w⁻¹) := by rw [mul_inv_rev]
    have hq : w⁻¹ * w'⁻¹ = (c * c * (c' * c'))⁻¹ * (c'' * c'') * (w'⁻¹ * w⁻¹) := by
      rw [mul_assoc, ← heq]; group
    have hqP : (c * c * (c' * c'))⁻¹ * (c'' * c'') ∈ zpowers e.s₁ :=
      (zpowers e.s₁).mul_mem ((zpowers e.s₁).inv_mem
        ((zpowers e.s₁).mul_mem ((zpowers e.s₁).mul_mem hc hc) ((zpowers e.s₁).mul_mem hc' hc')))
        ((zpowers e.s₁).mul_mem hc'' hc'')
    have hfin : w⁻¹ * w'⁻¹ * w * w' = (c * c * (c' * c'))⁻¹ * (c'' * c'') := by
      calc w⁻¹ * w'⁻¹ * w * w' = ((c * c * (c' * c'))⁻¹ * (c'' * c'') * (w'⁻¹ * w⁻¹)) * w * w' := by
            rw [← hq]
        _ = (c * c * (c' * c'))⁻¹ * (c'' * c'') := by group
    rw [hfin]; exact hqP
  have := key (W.inv_mem hw) (W.inv_mem hw')
  simpa using this

omit [Finite G] in
theorem mem_normalizer_centralizer_of_conj_inv {s g : G} (hg : g * s * g⁻¹ = s⁻¹) :
    g ∈ normalizer ((centralizer ({s} : Set G) : Subgroup G) : Set G) := by
  have hs : g⁻¹ * s * g = s⁻¹ := by
    have h1 : s = g⁻¹ * s⁻¹ * g := by
      calc s = g⁻¹ * (g * s * g⁻¹) * g := by group
        _ = g⁻¹ * s⁻¹ * g := by rw [hg]
    calc g⁻¹ * s * g = (g⁻¹ * s⁻¹ * g)⁻¹ := by group
      _ = s⁻¹ := by rw [← h1]
  have hgs : g * s⁻¹ * g⁻¹ = s := by
    calc g * s⁻¹ * g⁻¹ = (g * s * g⁻¹)⁻¹ := by group
      _ = s := by rw [hg, inv_inv]
  have key : ∀ x : G, x ∈ centralizer ({s} : Set G) → g * x * g⁻¹ ∈ centralizer ({s} : Set G) := by
    intro x hx
    rw [mem_centralizer_singleton_iff] at hx ⊢
    have hxs : x * s⁻¹ = s⁻¹ * x := (Commute.inv_right (show Commute x s from hx)).eq
    calc g * x * g⁻¹ * s = g * (x * (g⁻¹ * s * g)) * g⁻¹ := by group
      _ = g * (x * s⁻¹) * g⁻¹ := by rw [hs]
      _ = g * (s⁻¹ * x) * g⁻¹ := by rw [hxs]
      _ = (g * s⁻¹ * g⁻¹) * (g * x * g⁻¹) := by group
      _ = s * (g * x * g⁻¹) := by rw [hgs]
  have key' : ∀ x : G, x ∈ centralizer ({s} : Set G) → g⁻¹ * x * g ∈ centralizer ({s} : Set G) := by
    intro x hx
    rw [mem_centralizer_singleton_iff] at hx ⊢
    have hxs : x * s⁻¹ = s⁻¹ * x := (Commute.inv_right (show Commute x s from hx)).eq
    have hgs' : g⁻¹ * s⁻¹ * g = s := by
      calc g⁻¹ * s⁻¹ * g = (g⁻¹ * s * g)⁻¹ := by group
        _ = s := by rw [hs, inv_inv]
    calc g⁻¹ * x * g * s = g⁻¹ * (x * (g * s * g⁻¹)) * g := by group
      _ = g⁻¹ * (x * s⁻¹) * g := by rw [hg]
      _ = g⁻¹ * (s⁻¹ * x) * g := by rw [hxs]
      _ = (g⁻¹ * s⁻¹ * g) * (g⁻¹ * x * g) := by group
      _ = s * (g⁻¹ * x * g) := by rw [hgs']
  rw [mem_normalizer_iff]
  intro x
  constructor
  · exact key x
  · intro hx
    have := key' _ hx
    simpa [mul_assoc] using this

theorem mem_normalizer_oc {X : Subgroup G} {g : G} (hg : g ∈ normalizer (X : Set G)) :
    g ∈ normalizer ((oc X : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  constructor
  · exact conj_mem_oc_of_mem_normalizer hg
  · intro hx
    have := conj_mem_oc_of_mem_normalizer (inv_mem hg) hx
    simpa [mul_assoc] using this

end CFSG.GH74.Uniqueness.SU.SU13
