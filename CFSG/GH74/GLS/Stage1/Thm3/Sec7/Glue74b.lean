module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.Glue73

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec7

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
  CFSG.GH74.GLS.Stage1.Thm2.Recip
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G} {t u : G} {q : ℕ}

theorem dih_transport {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {n : ℕ}
    (h : IVK.IsDihedralTwoGroup X n) : IVK.IsDihedralTwoGroup Y n := by
  obtain ⟨hn, k, hk, hk2, ⟨e'⟩⟩ := h
  exact ⟨hn, k, hk, hk2, ⟨e.symm.trans e'⟩⟩

theorem sd_transport {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {n : ℕ}
    (h : IVK.IsSemidihedralTwoGroup X n) : IVK.IsSemidihedralTwoGroup Y n := by
  obtain ⟨hn, ⟨e'⟩⟩ := h
  exact ⟨hn, ⟨e.symm.trans e'⟩⟩

theorem dihOrder_transport {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {m : ℕ}
    (h : IVK.IsDihedralOrder X m) : IVK.IsDihedralOrder Y m := by
  obtain ⟨k, hk, hk2, ⟨e'⟩⟩ := h
  exact ⟨k, hk, hk2, ⟨e.symm.trans e'⟩⟩

omit [Finite G] in
theorem dih_of_eq {X N N' : Subgroup G} (hNN : N = N') [(N.subgroupOf X).Normal]
    [(N'.subgroupOf X).Normal] {n : ℕ}
    (h : IVK.IsDihedralTwoGroup (↥X ⧸ N.subgroupOf X) n) :
    IVK.IsDihedralTwoGroup (↥X ⧸ N'.subgroupOf X) n := by
  subst hNN
  exact h

omit [Finite G] in
theorem sd_of_eq {X N N' : Subgroup G} (hNN : N = N') [(N.subgroupOf X).Normal]
    [(N'.subgroupOf X).Normal] {n : ℕ}
    (h : IVK.IsSemidihedralTwoGroup (↥X ⧸ N.subgroupOf X) n) :
    IVK.IsSemidihedralTwoGroup (↥X ⧸ N'.subgroupOf X) n := by
  subst hNN
  exact h

namespace Cfg7

theorem t_normalizes_P (hII : II4_4_4_center) (h : Cfg7 G z S K₁ K₂ t u q) :
    zpowers t ≤ normalizer ((Pof S K₁ ⊔ Pof S K₂ : Subgroup G) : Set G) := by
  rw [zpowers_le, Subgroup.mem_normalizer_iff]
  intro x
  have hS := h.S_normalizes_P hII
  constructor
  · intro hx; exact hS t h.ch.t_mem x hx
  · intro hx
    have := hS t⁻¹ (S.inv_mem h.ch.t_mem) _ hx
    simpa [mul_assoc] using this

theorem t_nP (hII : II4_4_4_center) (h : Cfg7 G z S K₁ K₂ t u q) : t ∉ Pof S K₁ ⊔ Pof S K₂ :=
  fun ht => h.t_nS1 (h.P_le_S1 hII ht)

theorem Y0_le (hII : II4_4_4_center) (h : Cfg7 G z S K₁ K₂ t u q) :
    (Pof S K₁ ⊔ Pof S K₂) ⊔ zpowers t ≤ S :=
  sup_le ((h.P_le_S1 hII).trans S1_le_S) (zpowers_le.2 h.ch.t_mem)

theorem Y0_relIndex (hII : II4_4_4_center) (h : Cfg7 G z S K₁ K₂ t u q)
    (hc73 : Concl73 z S K₁ K₂) : ((Pof S K₁ ⊔ Pof S K₂) ⊔ zpowers t).relIndex S ≤ 2 := by
  set P := Pof S K₁ ⊔ Pof S K₂ with hP
  have hPS₁ : P ≤ S1 S K₁ := h.P_le_S1 hII
  have hY0S : P ⊔ zpowers t ≤ S := h.Y0_le hII
  have hn : zpowers t ≤ normalizer (P : Set G) := h.t_normalizes_P hII
  have h1 := A.card_sup_mul_card_inf hn
  have hbot : P ⊓ zpowers t = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxP, hxt⟩
    rw [Subgroup.mem_bot]
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hxt
    rcases B.zpow_of_sq_eq_one h.t_sq k with h' | h'
    · exact h'
    · exfalso
      rw [h'] at hxP
      exact h.t_nP hII hxP
  have hcw : Nat.card ↥(zpowers t) = 2 := by rw [Nat.card_zpowers, h.t_ord]
  rw [hbot, Subgroup.card_bot, hcw] at h1
  have hY : Nat.card ↥(P ⊔ zpowers t) = Nat.card ↥P * 2 := by omega
  have e1 := Subgroup.relIndex_mul_card (P ⊔ zpowers t) S
  rw [inf_eq_left.2 hY0S] at e1
  have e2 := A.card_eq_two_mul_of_relIndex_two (S1_le_S : S1 S K₁ ≤ S) h.S1_relIndex
  have e3 := Subgroup.relIndex_mul_card P (S1 S K₁)
  rw [inf_eq_left.2 hPS₁] at e3
  have hr : P.relIndex (S1 S K₁) ≤ 2 := by
    have := hc73.1
    rwa [h.Pz_eq_sup hII] at this
  have hpos : 0 < Nat.card ↥P * 2 := Nat.mul_pos Nat.card_pos (by norm_num)
  have key : (P ⊔ zpowers t).relIndex S * (Nat.card ↥P * 2) =
      P.relIndex (S1 S K₁) * (Nat.card ↥P * 2) := by
    calc (P ⊔ zpowers t).relIndex S * (Nat.card ↥P * 2)
        = (P ⊔ zpowers t).relIndex S * Nat.card ↥(P ⊔ zpowers t) := by rw [hY]
      _ = Nat.card ↥S := e1
      _ = 2 * Nat.card ↥(S1 S K₁) := e2
      _ = 2 * (P.relIndex (S1 S K₁) * Nat.card ↥P) := by rw [e3]
      _ = P.relIndex (S1 S K₁) * (Nat.card ↥P * 2) := by ring
  exact (Nat.eq_of_mul_eq_mul_right hpos key).le.trans hr

theorem Y0_normal (hII : II4_4_4_center) (h : Cfg7 G z S K₁ K₂ t u q) (hc73 : Concl73 z S K₁ K₂) :
    ∀ s ∈ S, ∀ y ∈ (Pof S K₁ ⊔ Pof S K₂) ⊔ zpowers t,
      s * y * s⁻¹ ∈ (Pof S K₁ ⊔ Pof S K₂) ⊔ zpowers t := by
  intro s hs y hy
  have hle := h.Y0_relIndex hII hc73
  have hpos := C73.relIndex_pos ((Pof S K₁ ⊔ Pof S K₂) ⊔ zpowers t) S
  have hY0S := h.Y0_le hII
  rcases (show ((Pof S K₁ ⊔ Pof S K₂) ⊔ zpowers t).relIndex S = 1 ∨
      ((Pof S K₁ ⊔ Pof S K₂) ⊔ zpowers t).relIndex S = 2 by omega) with h1 | h2
  · have hsY := Subgroup.relIndex_eq_one.1 h1 hs
    exact (Subgroup.mul_mem _ (Subgroup.mul_mem _ hsY hy) (Subgroup.inv_mem _ hsY))
  · exact A.conj_mem_of_relIndex_two h2 hs hy hY0S

theorem Y0_elems (hII : II4_4_4_center) (h : Cfg7 G z S K₁ K₂ t u q) {y : G}
    (hy : y ∈ (Pof S K₁ ⊔ Pof S K₂) ⊔ zpowers t) :
    y ∈ Pof S K₁ ⊔ Pof S K₂ ∨ ∃ p ∈ Pof S K₁ ⊔ Pof S K₂, y = p * t := by
  have hy' : y ∈ zpowers t ⊔ (Pof S K₁ ⊔ Pof S K₂) := by rw [sup_comm]; exact hy
  obtain ⟨a, ha, b, hb, rfl⟩ := A.mem_sup_of_le_normalizer (h.t_normalizes_P hII) hy'
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 ha
  rcases B.zpow_of_sq_eq_one h.t_sq k with h1 | h1
  · left; rw [h1, one_mul]; exact hb
  · right
    refine ⟨t * b * t⁻¹, h.S_normalizes_P hII t h.ch.t_mem b hb, ?_⟩
    rw [h1]; group

theorem frat (hII : II4_4_4_center) (hg : IG_10_32_P) (h : Cfg7 G z S K₁ K₂ t u q)
    (hc73 : Concl73 z S K₁ K₂) :
    ∀ s ∈ S, ∃ c ∈ Pof S K₁ ⊔ Pof S K₂, c⁻¹ * s ∈ S ⊓ centralizer ({t} : Set G) := by
  intro s hs
  have hv : s * t * s⁻¹ ∈ (Pof S K₁ ⊔ Pof S K₂) ⊔ zpowers t :=
    h.Y0_normal hII hc73 s hs t (mem_sup_right (mem_zpowers t))
  have hord : orderOf (s * t * s⁻¹) = 2 := by
    have := orderOf_injective (MulAut.conj s).toMonoidHom (MulAut.conj s).injective t
    simpa [MulAut.conj_apply, h.t_ord] using this
  have hvP : (s * t * s⁻¹) * t⁻¹ ∈ Pof S K₁ ⊔ Pof S K₂ := by
    rcases h.Y0_elems hII hv with hP | ⟨p, hp, hpe⟩
    · exfalso
      apply h.t_nP hII
      have := h.S_normalizes_P hII s⁻¹ (S.inv_mem hs) _ hP
      simpa [mul_assoc] using this
    · rw [hpe]; simpa using hp
  obtain ⟨c, hcP, hc⟩ := hg G z S K₁ K₂ h.std.std t h.ch.t_mem h.t_ord h.ch.t_swap (s * t * s⁻¹)
    (by rw [h.Pz_eq_sup hII]; exact hvP) hord
  rw [h.Pz_eq_sup hII] at hcP
  have hcS : c ∈ S := (h.P_le_S1 hII hcP).1
  rcases hc with h1 | h2
  · refine ⟨c, hcP, ?_⟩
    have hcom : c⁻¹ * s * t = t * (c⁻¹ * s) := by
      have e : c⁻¹ * s * t = c⁻¹ * (s * t * s⁻¹) * s := by group
      rw [e, ← h1]; group
    exact Subgroup.mem_inf.2 ⟨S.mul_mem (S.inv_mem hcS) hs,
      Subgroup.mem_centralizer_singleton_iff.2 hcom⟩
  · exfalso
    have hz1 : IsConj t (s * t * s⁻¹) := isConj_iff.2 ⟨s, rfl⟩
    have hz2 : IsConj (t * z) (s * t * s⁻¹) := isConj_iff.2 ⟨c, h2⟩
    exact h.ch.tz_ne (h.ch.t_conj.trans (hz1.trans hz2.symm))

end Cfg7

end CFSG.GH74.GLS.Stage1.Thm3.Sec7
