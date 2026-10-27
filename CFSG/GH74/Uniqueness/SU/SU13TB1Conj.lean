module

public import CFSG.GH74.Uniqueness.SU.SU10Z
public import CFSG.GH74.Uniqueness.SU.SU4Sylow

public section

namespace CFSG.GH74.Uniqueness.SU.SU13.TB

open Subgroup CFSG.GH74.Uniqueness.SU.SU4

variable {G : Type} [Group G] [Finite G]

@[expose] def Rank1 (s : G) : Prop :=
  ∀ a b : G, a * s = s * a → b * s = s * b → orderOf a = 2 → orderOf b = 2 → a * b = b * a → a = b

omit [Finite G] in
theorem sq_eq_one_of_orderOf_eq_two {a : G} (ha : orderOf a = 2) : a ^ 2 = 1 := by
  rw [← ha]; exact pow_orderOf_eq_one a

omit [Finite G] in
theorem orderOf_conj_eq {a : G} (g : G) : orderOf (g * a * g⁻¹) = orderOf a := by
  have := (MulAut.conj g).orderOf_eq a
  rwa [MulAut.conj_apply] at this

omit [Finite G] in
theorem exists_isPGroup_of_commute {X : Subgroup G} {a b : G} (haX : a ∈ X) (hbX : b ∈ X)
    (ha : orderOf a = 2) (hb : orderOf b = 2) (hab : a * b = b * a) :
    ∃ K : Subgroup G, K ≤ X ∧ IsPGroup 2 K ∧ a ∈ K ∧ b ∈ K := by
  have hA := SU1.isElemAbelian_zpowers (p := 2) (sq_eq_one_of_orderOf_eq_two ha)
  have hB := SU1.isElemAbelian_zpowers (p := 2) (sq_eq_one_of_orderOf_eq_two hb)
  have hc : ∀ x ∈ zpowers a, ∀ y ∈ zpowers b, x * y = y * x := by
    rintro x ⟨m, rfl⟩ y ⟨n, rfl⟩
    exact ((Commute.zpow_zpow (show Commute a b from hab) m n).eq)
  have hK := SU1.IsElemAbelian.sup hA hB hc
  have hexp := (SU1.isElemAbelian_iff.mp hK).2
  refine ⟨zpowers a ⊔ zpowers b, sup_le ((zpowers_le).mpr haX) ((zpowers_le).mpr hbX), ?_,
    mem_sup_left (mem_zpowers a), mem_sup_right (mem_zpowers b)⟩
  intro x
  exact ⟨1, by apply Subtype.ext; simpa using hexp x.1 x.2⟩

theorem eq_of_commute_of_sylow_uniq {X T : Subgroup G} {z : G} (hT : IsSylowIn X T)
    (hu : ∀ y ∈ T, orderOf y = 2 → y = z) {a b : G} (haX : a ∈ X) (hbX : b ∈ X)
    (ha : orderOf a = 2) (hb : orderOf b = 2) (hab : a * b = b * a) : a = b := by
  obtain ⟨K, hKX, hK, haK, hbK⟩ := exists_isPGroup_of_commute haX hbX ha hb hab
  obtain ⟨c, -, hcK⟩ := hT.exists_conj_le hKX hK
  have h1 : c⁻¹ * a * c ∈ T := hcK (mem_conjSub.mpr (by simpa [mul_assoc] using haK))
  have h2 : c⁻¹ * b * c ∈ T := hcK (mem_conjSub.mpr (by simpa [mul_assoc] using hbK))
  have o1 : orderOf (c⁻¹ * a * c) = 2 := by
    have := orderOf_conj_eq (a := a) c⁻¹
    rw [inv_inv] at this
    rw [this]; exact ha
  have o2 : orderOf (c⁻¹ * b * c) = 2 := by
    have := orderOf_conj_eq (a := b) c⁻¹
    rw [inv_inv] at this
    rw [this]; exact hb
  have e : c⁻¹ * a * c = c⁻¹ * b * c := (hu _ h1 o1).trans (hu _ h2 o2).symm
  calc a = c * (c⁻¹ * a * c) * c⁻¹ := by group
    _ = c * (c⁻¹ * b * c) * c⁻¹ := by rw [e]
    _ = b := by group

theorem rank1_of_sylow {s z : G} {T : Subgroup G} (hT : IsSylowIn (centralizer ({s} : Set G)) T)
    (hu : ∀ y ∈ T, orderOf y = 2 → y = z) : Rank1 s := by
  intro a b ha hb ha2 hb2 hab
  exact eq_of_commute_of_sylow_uniq hT hu (mem_centralizer_singleton_iff.mpr ha)
    (mem_centralizer_singleton_iff.mpr hb) ha2 hb2 hab

omit [Finite G] in
theorem rank1_conj {s : G} (g : G) : Rank1 (g * s * g⁻¹) ↔ Rank1 s := by
  have key : ∀ (s : G) (g : G), Rank1 (g * s * g⁻¹) → Rank1 s := by
    intro s g h a b ha hb ha2 hb2 hab
    have hcomm : ∀ x : G, x * s = s * x → (g * x * g⁻¹) * (g * s * g⁻¹) = (g * s * g⁻¹) * (g * x * g⁻¹) := by
      intro x hx
      calc g * x * g⁻¹ * (g * s * g⁻¹) = g * (x * s) * g⁻¹ := by group
        _ = g * (s * x) * g⁻¹ := by rw [hx]
        _ = g * s * g⁻¹ * (g * x * g⁻¹) := by group
    have := h (g * a * g⁻¹) (g * b * g⁻¹) (hcomm a ha) (hcomm b hb)
      (by rw [orderOf_conj_eq]; exact ha2) (by rw [orderOf_conj_eq]; exact hb2)
      (by
        calc g * a * g⁻¹ * (g * b * g⁻¹) = g * (a * b) * g⁻¹ := by group
          _ = g * (b * a) * g⁻¹ := by rw [hab]
          _ = g * b * g⁻¹ * (g * a * g⁻¹) := by group)
    calc a = g⁻¹ * (g * a * g⁻¹) * g := by group
      _ = g⁻¹ * (g * b * g⁻¹) * g := by rw [this]
      _ = b := by group
  refine ⟨key s g, fun h => ?_⟩
  have := key (g * s * g⁻¹) g⁻¹ (by simpa [mul_assoc] using h)
  simpa [mul_assoc] using this

omit [Finite G] in
theorem centralizer_conj_eq (s g : G) :
    centralizer ({g * s * g⁻¹} : Set G) = conjSub g (centralizer ({s} : Set G)) := by
  ext x
  rw [mem_centralizer_singleton_iff, mem_conjSub, mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc g⁻¹ * x * g * s = g⁻¹ * (x * (g * s * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * s * g⁻¹) * x) * g := by rw [h]
      _ = s * (g⁻¹ * x * g) := by group
  · intro h
    calc x * (g * s * g⁻¹) = g * ((g⁻¹ * x * g) * s) * g⁻¹ := by group
      _ = g * (s * (g⁻¹ * x * g)) * g⁻¹ := by rw [h]
      _ = (g * s * g⁻¹) * x := by group

theorem card_sylow_eq_of_conj {s s' : G} {T T' : Subgroup G}
    (hT : IsSylowIn (centralizer ({s} : Set G)) T) (hT' : IsSylowIn (centralizer ({s'} : Set G)) T')
    {g : G} (hg : g * s * g⁻¹ = s') : Nat.card T = Nat.card T' := by
  subst hg
  rw [centralizer_conj_eq] at hT'
  have h1 := hT.conj g
  obtain ⟨c, -, hc⟩ := hT'.exists_conj_eq h1
  rw [← card_conjSub g T, hc, card_conjSub]

abbrev GConj (a b : G) : Prop := ∃ g : G, g * a * g⁻¹ = b

omit [Finite G] in
theorem GConj.symm {a b : G} (h : GConj a b) : GConj b a := by
  obtain ⟨g, hg⟩ := h
  exact ⟨g⁻¹, by rw [← hg]; group⟩

theorem not_gconj_of_sylow {s₁ s₂ s₃ z t : G} {T₁ T₃ : Subgroup G}
    (h1 : IsSylowIn (centralizer ({s₁} : Set G)) T₁)
    (hu1 : ∀ y ∈ T₁, orderOf y = 2 → y = z) (hcard1 : 2 < Nat.card T₁)
    (h3 : IsSylowIn (centralizer ({s₃} : Set G)) T₃)
    (hu3 : ∀ y ∈ T₃, orderOf y = 2 → y = z) (hcard3 : Nat.card T₃ = 2)
    (hzs : z * s₂ = s₂ * z) (hts : t * s₂ = s₂ * t) (hz : orderOf z = 2) (ht : orderOf t = 2)
    (hzt : z ≠ t) (hzt' : z * t = t * z) :
    ¬ GConj s₁ s₂ ∧ ¬ GConj s₁ s₃ ∧ ¬ GConj s₂ s₃ := by
  have r1 : Rank1 s₁ := rank1_of_sylow h1 hu1
  have r3 : Rank1 s₃ := rank1_of_sylow h3 hu3
  have r2 : ¬ Rank1 s₂ := fun h => hzt (h z t hzs hts hz ht hzt')
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨g, hg⟩
    exact r2 (by rw [← hg]; exact (rank1_conj g).mpr r1)
  · rintro ⟨g, hg⟩
    have := card_sylow_eq_of_conj h1 h3 hg
    omega
  · rintro ⟨g, hg⟩
    exact r2 ((rank1_conj g).mp (by rw [hg]; exact r3))

theorem exists_centralizer_conj {s₁ s₂ s₃ z w : G} (hz : orderOf z = 2)
    (hs : IsSimpleGroup G) (hn : ∃ a b : G, a * b ≠ b * a)
    (hz3 : ∀ u : G, u * z = z * u → orderOf u = 3 →
      ∃ h : G, h * z = z * h ∧ (h * u * h⁻¹ = s₁ ∨ h * u * h⁻¹ = s₂ ∨ h * u * h⁻¹ = s₃))
    (hinv : ∀ u v : G, u * z = z * u → v * z = z * v → orderOf u = 2 → orderOf v = 2 → u ≠ z →
      v ≠ z → ∃ h : G, h * z = z * h ∧ h * u * h⁻¹ = v)
    (hn12 : ¬ GConj s₂ s₁) (hn23 : ¬ GConj s₂ s₃) (hs₂ : orderOf s₂ = 3)
    (hw : w * z = z * w) (hw2 : orderOf w = 2) (hwz : w ≠ z) (hws : w * s₂ = s₂ * w) :
    ∃ k : G, k * s₂ = s₂ * k ∧ k * z * k⁻¹ = w := by
  obtain ⟨g, hne, hcomm⟩ := SU10.exists_commuting_conj_ne hs hn hz
  have hu2 : orderOf (g * z * g⁻¹) = 2 := by rw [orderOf_conj_eq]; exact hz
  obtain ⟨h, hh, hhu⟩ := hinv (g * z * g⁻¹) w hcomm hw hu2 hw2 hne hwz
  set g₁ : G := h * g with hg₁
  have hgz : g₁ * z * g₁⁻¹ = w := by
    rw [hg₁]
    calc h * g * z * (h * g)⁻¹ = h * (g * z * g⁻¹) * h⁻¹ := by group
      _ = w := hhu
  have hgw : g₁ * z = w * g₁ := by
    calc g₁ * z = (g₁ * z * g₁⁻¹) * g₁ := by group
      _ = w * g₁ := by rw [hgz]
  have hu'z : (g₁⁻¹ * s₂ * g₁) * z = z * (g₁⁻¹ * s₂ * g₁) := by
    calc g₁⁻¹ * s₂ * g₁ * z = g₁⁻¹ * s₂ * (g₁ * z) := by group
      _ = g₁⁻¹ * s₂ * (w * g₁) := by rw [hgw]
      _ = g₁⁻¹ * (s₂ * w) * g₁ := by group
      _ = g₁⁻¹ * (w * s₂) * g₁ := by rw [hws]
      _ = (g₁⁻¹ * w * g₁) * (g₁⁻¹ * s₂ * g₁) := by group
      _ = z * (g₁⁻¹ * s₂ * g₁) := by
        congr 1
        calc g₁⁻¹ * w * g₁ = g₁⁻¹ * (w * g₁) := by group
          _ = g₁⁻¹ * (g₁ * z) := by rw [hgw]
          _ = z := by group
  have hu'3 : orderOf (g₁⁻¹ * s₂ * g₁) = 3 := by
    have := orderOf_conj_eq (a := s₂) g₁⁻¹
    rw [inv_inv] at this
    rw [this]; exact hs₂
  obtain ⟨c, hc, hcases⟩ := hz3 _ hu'z hu'3
  rcases hcases with h1 | h2 | h3
  · exact absurd ⟨c * g₁⁻¹, by rw [← h1]; group⟩ hn12
  · refine ⟨g₁ * c⁻¹, ?_, ?_⟩
    · have hk : (g₁ * c⁻¹)⁻¹ * s₂ * (g₁ * c⁻¹) = s₂ := by
        calc (g₁ * c⁻¹)⁻¹ * s₂ * (g₁ * c⁻¹) = c * (g₁⁻¹ * s₂ * g₁) * c⁻¹ := by group
          _ = s₂ := h2
      calc g₁ * c⁻¹ * s₂ = (g₁ * c⁻¹) * ((g₁ * c⁻¹)⁻¹ * s₂ * (g₁ * c⁻¹)) := by rw [hk]
        _ = s₂ * (g₁ * c⁻¹) := by group
    · calc g₁ * c⁻¹ * z * (g₁ * c⁻¹)⁻¹ = g₁ * (c⁻¹ * z * c) * g₁⁻¹ := by group
        _ = g₁ * z * g₁⁻¹ := by
          congr 2
          calc c⁻¹ * z * c = c⁻¹ * (z * c) := by group
            _ = c⁻¹ * (c * z) := by rw [hc]
            _ = z := by group
        _ = w := hgz
  · exact absurd ⟨c * g₁⁻¹, by rw [← h3]; group⟩ hn23

end CFSG.GH74.Uniqueness.SU.SU13.TB
