module

public import CFSG.GH74.AS16.E2.Rank3
public import CFSG.GH74.AS16.E2.Data

public section

namespace CFSG.GH74.AS16.E2

open Subgroup CFSG CFSG.Blueprint
open CFSG.GH74.E2 hiding Hyp

section Local3

structure Local3Sub {G : Type*} [Group G] (L : Subgroup G) : Prop where
  elemAb9 : ∃ E : Subgroup G, E ≤ L ∧ ElemAb 3 E ∧ Nat.card E = 9
  exists3 : ∀ v ∈ L, orderOf v = 2 → ∃ c ∈ L, orderOf c = 3 ∧ c * v = v * c
  cent3 : ∀ v ∈ L, orderOf v = 2 → ∀ a ∈ L,
    (∀ c ∈ L, orderOf c = 3 → c * v = v * c → a * c = c * a) → a = 1 ∨ a = v
  inner3 : ∀ c ∈ normalizer (L : Set G), c ^ 3 ∈ centralizer (L : Set G) →
    ∃ l ∈ L, l⁻¹ * c ∈ centralizer (L : Set G)

structure Local3Table (K : Type*) [Group K] : Prop where
  elemAb9 : ∃ E : Subgroup K, ElemAb 3 E ∧ Nat.card E = 9
  exists3 : ∀ v : K, orderOf v = 2 → ∃ c : K, orderOf c = 3 ∧ c * v = v * c
  cent3 : ∀ v : K, orderOf v = 2 → ∀ a : K,
    (∀ c : K, orderOf c = 3 → c * v = v * c → a * c = c * a) → a = 1 ∨ a = v

@[expose] def Local3Data (P : (K : Type) → [Group K] → Prop) : Prop :=
  ∀ (K : Type) [Group K] [Finite K], P K → Local3Table K

variable {G : Type*} [Group G]

theorem normalizerMonoidHom_eq_one {L : Subgroup G} {c : G} (hc : c ∈ normalizer (L : Set G))
    (hcC : c ∈ centralizer (L : Set G)) : L.normalizerMonoidHom ⟨c, hc⟩ = 1 := by
  ext x
  have := mem_centralizer_iff.1 hcC x x.2
  show c * (x : G) * c⁻¹ = (x : G)
  rw [← this]
  group

theorem Local3Sub.of_table {L : Subgroup G} (hT : Local3Table ↥L)
    (hin : ∀ φ : MulAut ↥L, φ ^ 3 = 1 → ∃ k : ↥L, ∀ x : ↥L, φ x = k * x * k⁻¹) :
    Local3Sub L where
  elemAb9 := by
    obtain ⟨E, hE, hcard⟩ := hT.elemAb9
    refine ⟨E.map L.subtype, ?_, ⟨?_, ?_⟩, ?_⟩
    · rintro _ ⟨x, -, rfl⟩
      exact x.2
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      exact congrArg Subtype.val (hE.1 a ha b hb)
    · rintro _ ⟨a, ha, rfl⟩
      simpa using congrArg Subtype.val (hE.2 a ha)
    · rw [Subgroup.card_map_of_injective L.subtype_injective]
      exact hcard
  exists3 := by
    intro v hv hv2
    have hv2' : orderOf (⟨v, hv⟩ : ↥L) = 2 := by rw [← Subgroup.orderOf_coe]; exact hv2
    obtain ⟨c, hc3, hcv⟩ := hT.exists3 ⟨v, hv⟩ hv2'
    exact ⟨c, c.2, by rw [Subgroup.orderOf_coe]; exact hc3, congrArg Subtype.val hcv⟩
  cent3 := by
    intro v hv hv2 a ha hac
    have hv2' : orderOf (⟨v, hv⟩ : ↥L) = 2 := by rw [← Subgroup.orderOf_coe]; exact hv2
    have := hT.cent3 ⟨v, hv⟩ hv2' ⟨a, ha⟩ (fun c hc3 hcv => Subtype.ext
      (hac c c.2 (by rw [Subgroup.orderOf_coe]; exact hc3) (congrArg Subtype.val hcv)))
    rcases this with h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val h)
  inner3 := by
    intro c hcN hc3C
    have hφ : (L.normalizerMonoidHom ⟨c, hcN⟩) ^ 3 = 1 := by
      rw [← map_pow]
      have : (⟨c, hcN⟩ : normalizer (L : Set G)) ^ 3 = ⟨c ^ 3, (normalizer (L : Set G)).pow_mem hcN 3⟩ :=
        Subtype.ext (by simp)
      rw [this]
      exact normalizerMonoidHom_eq_one _ hc3C
    obtain ⟨k, hk⟩ := hin _ hφ
    refine ⟨(k : G), k.2, mem_centralizer_iff.2 fun x hx => ?_⟩
    have h1 := congrArg Subtype.val (hk ⟨x, hx⟩)
    have h2 : c * x * c⁻¹ = (k : G) * x * (k : G)⁻¹ := h1
    calc x * ((k : G)⁻¹ * c) = (k : G)⁻¹ * ((k : G) * x * (k : G)⁻¹) * c := by group
      _ = (k : G)⁻¹ * (c * x * c⁻¹) * c := by rw [h2]
      _ = ((k : G)⁻¹ * c) * x := by group

theorem Local3Sub.elemAb9_conj {L : Subgroup G} (h : Local3Sub L) (g : G) :
    ∃ E : Subgroup G, E ≤ L.map (MulAut.conj g).toMonoidHom ∧ ElemAb 3 E ∧ Nat.card E = 9 := by
  obtain ⟨E, hEL, hE, hcard⟩ := h.elemAb9
  refine ⟨E.map (MulAut.conj g).toMonoidHom, Subgroup.map_mono hEL, ⟨?_, ?_⟩, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have := hE.1 a ha b hb
    show g * a * g⁻¹ * (g * b * g⁻¹) = g * b * g⁻¹ * (g * a * g⁻¹)
    calc g * a * g⁻¹ * (g * b * g⁻¹) = g * (a * b) * g⁻¹ := by group
      _ = g * (b * a) * g⁻¹ := by rw [this]
      _ = g * b * g⁻¹ * (g * a * g⁻¹) := by group
  · rintro _ ⟨a, ha, rfl⟩
    have := hE.2 a ha
    show (g * a * g⁻¹) ^ 3 = 1
    calc (g * a * g⁻¹) ^ 3 = g * a ^ 3 * g⁻¹ := by
          rw [pow_three, pow_three]; group
      _ = 1 := by rw [this]; group
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hcard

theorem Local3Sub.inner3_conj {L : Subgroup G} (h : Local3Sub L) (g : G) :
    ∀ c ∈ normalizer ((L.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G),
      c ^ 3 ∈ centralizer ((L.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) →
      ∃ l ∈ L.map (MulAut.conj g).toMonoidHom,
        l⁻¹ * c ∈ centralizer ((L.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  intro c hcN hc3C
  have hmem : ∀ y : G, y ∈ L.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * y * g ∈ L := by
    intro y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have : g⁻¹ * (g * x * g⁻¹) * g = x := by group
      show g⁻¹ * (g * x * g⁻¹) * g ∈ L
      rw [this]
      exact hx
    · intro hy
      refine ⟨g⁻¹ * y * g, hy, ?_⟩
      show g * (g⁻¹ * y * g) * g⁻¹ = y
      group
  have hc' : g⁻¹ * c * g ∈ normalizer (L : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have h1 := (Subgroup.mem_normalizer_iff.1 hcN) (g * x * g⁻¹)
    rw [hmem, hmem] at h1
    have e1 : g⁻¹ * (g * x * g⁻¹) * g = x := by group
    have e2 : g⁻¹ * (c * (g * x * g⁻¹) * c⁻¹) * g = (g⁻¹ * c * g) * x * (g⁻¹ * c * g)⁻¹ := by
      group
    rw [e1, e2] at h1
    exact h1
  have hc3' : (g⁻¹ * c * g) ^ 3 ∈ centralizer (L : Set G) := by
    rw [mem_centralizer_iff] at hc3C ⊢
    intro x hx
    have hx' : g * x * g⁻¹ ∈ L.map (MulAut.conj g).toMonoidHom := ⟨x, hx, rfl⟩
    have h1 := hc3C _ hx'
    have e : (g⁻¹ * c * g) ^ 3 = g⁻¹ * c ^ 3 * g := by
      rw [pow_three, pow_three]; group
    rw [e]
    calc x * (g⁻¹ * c ^ 3 * g) = g⁻¹ * ((g * x * g⁻¹) * c ^ 3) * g := by group
      _ = g⁻¹ * (c ^ 3 * (g * x * g⁻¹)) * g := by rw [h1]
      _ = (g⁻¹ * c ^ 3 * g) * x := by group
  obtain ⟨l, hl, hlc⟩ := h.inner3 _ hc' hc3'
  refine ⟨g * l * g⁻¹, ⟨l, hl, rfl⟩, mem_centralizer_iff.2 fun y hy => ?_⟩
  have hy' : g⁻¹ * y * g ∈ L := (hmem y).1 hy
  have h1 := mem_centralizer_iff.1 hlc _ hy'
  have e3 : (g * l * g⁻¹)⁻¹ * c = g * (l⁻¹ * (g⁻¹ * c * g)) * g⁻¹ := by group
  rw [e3]
  calc y * (g * (l⁻¹ * (g⁻¹ * c * g)) * g⁻¹)
      = g * ((g⁻¹ * y * g) * (l⁻¹ * (g⁻¹ * c * g))) * g⁻¹ := by group
    _ = g * ((l⁻¹ * (g⁻¹ * c * g)) * (g⁻¹ * y * g)) * g⁻¹ := by rw [h1]
    _ = (g * (l⁻¹ * (g⁻¹ * c * g)) * g⁻¹) * y := by group

end Local3

section Standard

variable {G : Type} [Group G] [Finite G]

theorem not_isCompIn_conj_centralizer (he : Assembly.evenRank G ≤ 2) {L : Subgroup G}
    (hq : CFSG.IsQuasisimple ↥L) (hZ : ∀ x ∈ L, x ∈ centralizer (L : Set G) → x = 1)
    (hE : ∃ E : Subgroup G, E ≤ L ∧ ElemAb 3 E ∧ Nat.card E = 9)
    (h3 : ∀ v ∈ L, orderOf v = 2 → ∃ c ∈ L, orderOf c = 3 ∧ c * v = v * c) (g : G) :
    ¬ GLS.IsCompIn (centralizer (L : Set G)) (conjugate L g) := by
  intro hcomp
  have hle : conjugate L g ≤ centralizer (L : Set G) := hcomp.1
  obtain ⟨v₀, hv₀L, hv₀⟩ := AS16.exists_involution_of_isQuasisimple hq
  obtain ⟨c₀, hc₀L, hc₀, hc₀v⟩ := h3 v₀ hv₀L hv₀
  obtain ⟨E, hEL, hE3, hEcard⟩ := hE
  have hconjmem : ∀ x : G, x ∈ L → g⁻¹ * x * g ∈ conjugate L g := by
    intro x hx
    rw [AS16.mem_conjugate_iff']
    have : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    rw [this]
    exact hx
  have hord : ∀ x : G, orderOf (g⁻¹ * x * g) = orderOf x := by
    intro x
    calc orderOf (g⁻¹ * x * g) = orderOf ((MulAut.conj g⁻¹) x) := by simp
      _ = orderOf x := (MulAut.conj g⁻¹).orderOf_eq x
  have hv'C : g⁻¹ * v₀ * g ∈ centralizer (L : Set G) := hle (hconjmem v₀ hv₀L)
  have hc'C : g⁻¹ * c₀ * g ∈ centralizer (L : Set G) := hle (hconjmem c₀ hc₀L)
  have hc'1 : g⁻¹ * c₀ * g ∈ L → g⁻¹ * c₀ * g = 1 := fun hL => hZ _ hL hc'C
  refine false_of_elemAb9_order3 he (r := g⁻¹ * v₀ * g) (by rw [hord]; exact hv₀) hE3 hEcard
    (c := g⁻¹ * c₀ * g) (by rw [hord]; exact hc₀) ?_ ?_ ?_ ?_
  · intro e he'
    exact (mem_centralizer_iff.1 hc'C e (hEL he')).symm
  · intro hcE
    have h1 := hc'1 (hEL hcE)
    have : orderOf (g⁻¹ * c₀ * g) = 1 := by rw [h1]; exact orderOf_one
    rw [hord, hc₀] at this
    omega
  · intro e he'
    exact (mem_centralizer_iff.1 hv'C e (hEL he')).symm
  · calc g⁻¹ * v₀ * g * (g⁻¹ * c₀ * g) = g⁻¹ * (v₀ * c₀) * g := by group
      _ = g⁻¹ * (c₀ * v₀) * g := by rw [← hc₀v]
      _ = g⁻¹ * c₀ * g * (g⁻¹ * v₀ * g) := by group

variable {T : Sylow 2 G} {z : G} {L : Subgroup G}

theorem Cfg.isStandard (h : Cfg G T z L) (hterm : GLS.IsTerminalPair 2 z L)
    (hZ : center ↥L = ⊥) (hL3 : Local3Sub L) : IsStandardSubgroup L :=
  AS16.isStandardSubgroup_of_terminal h.pair.isQuasisimple h.pair.orderOf_eq
    h.pair.mem_centralizer (fun t htL ht2 => hterm.2.2.2 t ht2 htL)
    (not_isCompIn_conj_centralizer h.quasithin h.pair.isQuasisimple (center_trivial hZ)
      hL3.elemAb9 hL3.exists3)

theorem Cfg.lNormal (h : Cfg G T z L) : AS16.LNormal z L := by
  refine ⟨fun x hx c => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  have hc : (c : G) ∈ normalizer (L : Set G) := h.cen_le_normalizer c.2
  have := (Subgroup.mem_normalizer_iff.1 hc x).1 hx
  simpa using this

end Standard

section Order3

variable {G : Type} [Group G] [Finite G]

theorem mem_of_order_three (he : Assembly.evenRank G ≤ 2) {L : Subgroup G} {r : G}
    (hr : orderOf r = 2) (hrL : r ∈ centralizer (L : Set G))
    (hZ : ∀ x ∈ L, x ∈ centralizer (L : Set G) → x = 1)
    (hE : ∃ E : Subgroup G, E ≤ L ∧ ElemAb 3 E ∧ Nat.card E = 9)
    (hinn : ∀ c ∈ normalizer (L : Set G), c ^ 3 ∈ centralizer (L : Set G) →
      ∃ l ∈ L, l⁻¹ * c ∈ centralizer (L : Set G))
    (hN : ∀ g : G, g * r = r * g → g ∈ normalizer (L : Set G))
    {c : G} (hc3 : orderOf c = 3) (hcr : c * r = r * c) : c ∈ L := by
  obtain ⟨E, hEL, hE3, hEcard⟩ := hE
  have hcN := hN c hcr
  have hc3' : c ^ 3 = 1 := hc3 ▸ pow_orderOf_eq_one c
  obtain ⟨l, hl, hc2⟩ := hinn c hcN (by rw [hc3']; exact one_mem _)
  by_cases h : l⁻¹ * c = 1
  · have : c = l := by
      have := congrArg (fun y => l * y) h
      simpa using this
    rw [this]
    exact hl
  · exfalso
    set c₂ : G := l⁻¹ * c with hc₂def
    have hc₂C : ∀ x ∈ L, x * c₂ = c₂ * x := fun x hx => mem_centralizer_iff.1 hc2 x hx
    have hcl : c = l * c₂ := by rw [hc₂def]; group
    have hlc₂ : l * c₂ = c₂ * l := hc₂C l hl
    have hc₂3 : c₂ ^ 3 = 1 := by
      have hcm : Commute l c₂ := hlc₂
      have h1 : (l * c₂) ^ 3 = l ^ 3 * c₂ ^ 3 := hcm.mul_pow 3
      rw [← hcl, hc3'] at h1
      have h2 : c₂ ^ 3 = (l ^ 3)⁻¹ := eq_inv_of_mul_eq_one_right h1.symm
      have h3 : c₂ ^ 3 ∈ L := by rw [h2]; exact L.inv_mem (L.pow_mem hl 3)
      have h4 : c₂ ^ 3 ∈ centralizer (L : Set G) := (centralizer (L : Set G)).pow_mem hc2 3
      exact hZ _ h3 h4
    have hc₂o : orderOf c₂ = 3 := orderOf_eq_prime hc₂3 h
    have hrc₂ : r * c₂ = c₂ * r := by
      have h1 : r * l = l * r := (mem_centralizer_iff.1 hrL l hl).symm
      have hcm : Commute r l := h1
      have h2 : r * l⁻¹ = l⁻¹ * r := hcm.inv_right.eq
      calc r * (l⁻¹ * c) = (r * l⁻¹) * c := by group
        _ = (l⁻¹ * r) * c := by rw [h2]
        _ = l⁻¹ * (r * c) := by group
        _ = l⁻¹ * (c * r) := by rw [← hcr]
        _ = (l⁻¹ * c) * r := by group
    refine false_of_elemAb9_order3 he hr hE3 hEcard hc₂o (fun e he' => (hc₂C e (hEL he')).symm) ?_
      (fun e he' => (mem_centralizer_iff.1 hrL e (hEL he')).symm) hrc₂
    intro hcE
    have := hZ _ (hEL hcE) (mem_centralizer_iff.2 hc₂C)
    rw [this, orderOf_one] at hc₂o
    omega

end Order3

end CFSG.GH74.AS16.E2
