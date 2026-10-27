module

public import CFSG.LargeExtraspecial.S10EightJ

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S10

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

universe u

theorem perm_three_eq_of_cube : ∀ ρ w : Equiv.Perm (Fin 3), ρ ^ 3 = 1 → ρ ≠ 1 → w ^ 3 = 1 →
    w = 1 ∨ w = ρ ∨ w = ρ * ρ := by
  decide +kernel

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

namespace DirDec

variable {Xb Yb : Subgroup S.O} (D : DirDec S g t Xb Yb)
include D

theorem eq_of_mem_commutator {d : S.O} (hd : d ∈ ⁅Yb, Yb⁆) (hd1 : d ≠ 1) {w : S.O}
    (hw : w ∈ ⁅Yb, Yb⁆) : w = 1 ∨ w = d ∨ w = d * d := by
  obtain ⟨hdY, hd3⟩ := (D.mem_commutator_iff).mp hd
  obtain ⟨hwY, hw3⟩ := (D.mem_commutator_iff).mp hw
  obtain ⟨e⟩ := D.iso
  have h := perm_three_eq_of_cube (e ⟨d, hdY⟩) (e ⟨w, hwY⟩)
    (by rw [← map_pow, show (⟨d, hdY⟩ : Yb) ^ 3 = 1 from Subtype.ext hd3, map_one])
    (fun h => hd1 (congrArg Subtype.val (e.injective (h.trans (map_one e).symm))))
    (by rw [← map_pow, show (⟨w, hwY⟩ : Yb) ^ 3 = 1 from Subtype.ext hw3, map_one])
  rcases h with h | h | h
  · exact Or.inl (congrArg Subtype.val (e.injective (h.trans (map_one e).symm)))
  · exact Or.inr (Or.inl (congrArg Subtype.val (e.injective h)))
  · refine Or.inr (Or.inr ?_)
    have := e.injective (h.trans (map_mul e _ _).symm)
    exact congrArg Subtype.val this

end DirDec

namespace Dec108

variable {X : Hyp10 S g t} {Xb Yb : Subgroup S.O} (D : Dec108 X Xb Yb)
include D

theorem card_Ebar (hCE : CentralExtInput.{u}) (h7 : 7 ≤ S.width) :
    Nat.card (S.Lbar g ⊓ Xb : Subgroup S.O) = 2 ^ (S.width - 2) := by
  have h1 := D.two_mul_card_Ebar hCE
  rw [X.C.card_Lbar] at h1
  have h2 : 2 ^ (S.width - 1) = 2 * 2 ^ (S.width - 2) := by
    rw [← pow_succ']
    congr 1
    omega
  omega

theorem conj_mem_commutator_of_commute (hCE : CentralExtInput.{u}) {k : S.M}
    (hk : S.ρ k * t = t * S.ρ k) {w : S.O} (hw : w ∈ ⁅Yb, Yb⁆) :
    S.ρ k * w * (S.ρ k)⁻¹ ∈ ⁅Yb, Yb⁆ := by
  have h1 := (D.dec.isOp_commutator hCE X).map_conj (S.ρ k)
  have hR : (Rbar S g t).map (MulAut.conj (S.ρ k)).toMonoidHom = Rbar S g t := by
    have := Rbar_conj (g := g) k t
    rw [show S.ρ k * t * (S.ρ k)⁻¹ = t by rw [hk]; group] at this
    exact this.symm
  rw [hR] at h1
  have heq := h1.eq (D.dec.isOp_commutator hCE X)
  rw [← heq]
  exact ⟨w, hw, rfl⟩

theorem mem_sup_of_commute_Xb (hCE : CentralExtInput.{u}) {k₁ : S.M} (hk₁ : S.ρ k₁ ∈ Yb)
    {l : S.O} (hl : l ∈ S.Lbar ((k₁ : G) * g)) (hlX : ∀ x ∈ Xb, l * x = x * l) :
    l ∈ zpowers t ⊔ Yb := by
  rw [mem_Lbar_mul_iff] at hl
  set l' := (S.ρ k₁)⁻¹ * l * S.ρ k₁ with hl'
  have hkX : ∀ x ∈ Xb, S.ρ k₁ * x = x * S.ρ k₁ := fun x hx => (D.dec.comm x hx _ hk₁).symm
  have hl'X : ∀ x ∈ Xb, l' * x = x * l' := by
    intro x hx
    have h1 := hkX x hx
    have h2 := hlX x hx
    calc l' * x = (S.ρ k₁)⁻¹ * l * (S.ρ k₁ * x) := by rw [hl']; group
      _ = (S.ρ k₁)⁻¹ * (l * x) * S.ρ k₁ := by rw [h1]; group
      _ = (S.ρ k₁)⁻¹ * (x * l) * S.ρ k₁ := by rw [h2]
      _ = (S.ρ k₁)⁻¹ * x * S.ρ k₁ * l' := by rw [hl']; group
      _ = x * l' := by
          have : (S.ρ k₁)⁻¹ * x * S.ρ k₁ = x := by
            calc (S.ρ k₁)⁻¹ * x * S.ρ k₁ = (S.ρ k₁)⁻¹ * (x * S.ρ k₁) := by group
              _ = (S.ρ k₁)⁻¹ * (S.ρ k₁ * x) := by rw [h1]
              _ = x := by group
          rw [this]
  obtain ⟨e, he, u, hu, he'⟩ := exists_mul_of_mem_sup_of_commute (A := S.Lbar g ⊓ Xb)
    (B := Yb) (fun a ha b hb => D.dec.comm a ha.2 b hb) (D.Lbar_le_sup hCE hl)
  have heZ : e ∈ centralizer (Rbar S g t : Set S.O) ⊓ S.Lbar g := by
    refine ⟨mem_centralizer_iff.mpr fun r hr => ?_, he.1⟩
    obtain ⟨x, hx, v, hv, rfl⟩ := D.dec.exists_mul hr
    have hex : e * x = x * e := by
      have h1 := hl'X x hx
      rw [he'] at h1
      have hux : u * x = x * u := (D.dec.comm x hx u hu).symm
      calc e * x = e * x * u * u⁻¹ := by group
        _ = e * (u * x) * u⁻¹ := by rw [mul_assoc e x u, ← hux]
        _ = (e * u) * x * u⁻¹ := by group
        _ = x * (e * u) * u⁻¹ := by rw [h1]
        _ = x * e := by group
    have hev : e * v = v * e := D.dec.comm e he.2 v hv
    calc x * v * e = x * (v * e) := by group
      _ = x * (e * v) := by rw [hev]
      _ = (x * e) * v := by group
      _ = (e * x) * v := by rw [hex]
      _ = e * (x * v) := by group
  rw [timmesfeld_4_7_c X.H X.C X.ht X.ht1 X.hVQ] at heZ
  have hl1 : l = S.ρ k₁ * l' * (S.ρ k₁)⁻¹ := by rw [hl']; group
  have hek : e * S.ρ k₁ = S.ρ k₁ * e := D.dec.comm e he.2 _ hk₁
  rw [hl1, he']
  have e1 : S.ρ k₁ * (e * u) * (S.ρ k₁)⁻¹ = e * (S.ρ k₁ * u * (S.ρ k₁)⁻¹) := by
    calc S.ρ k₁ * (e * u) * (S.ρ k₁)⁻¹ = (S.ρ k₁ * e) * u * (S.ρ k₁)⁻¹ := by group
      _ = (e * S.ρ k₁) * u * (S.ρ k₁)⁻¹ := by rw [hek]
      _ = e * (S.ρ k₁ * u * (S.ρ k₁)⁻¹) := by group
  rw [e1]
  exact mul_mem (Subgroup.mem_sup_left heZ)
    (Subgroup.mem_sup_right (mul_mem (mul_mem hk₁ hu) (inv_mem hk₁)))

theorem card_zpowers_sup_Yb_le (hCE : CentralExtInput.{u}) :
    Nat.card (zpowers t ⊔ Yb : Subgroup S.O) ≤ 12 := by
  have htX : t ∈ Xb := (D.t_mem_Ebar hCE).2
  have hc : ∀ u ∈ Yb, t * u = u * t := fun u hu => D.dec.comm t htX u hu
  have hN : zpowers t ≤ normalizer (Yb : Set S.O) := by
    rw [zpowers_le, mem_normalizer_iff]
    intro u
    constructor
    · intro hu
      rw [hc u hu, mul_inv_cancel_right]
      exact hu
    · intro hu
      have h1 := hc _ hu
      have h2 : t * u * t⁻¹ = u := by
        have : t * (t * u * t⁻¹) = t * u := by rw [h1]; group
        exact mul_left_cancel this
      rw [← h2]
      exact hu
  have h1 := card_sup_mul_card_inf hN
  rw [Nat.card_zpowers, X.orderOf_t, D.dec.card_Yb] at h1
  have hpos : 0 < Nat.card (zpowers t ⊓ Yb : Subgroup S.O) := Nat.card_pos
  nlinarith

theorem conj_y_mem (hCE : CentralExtInput.{u}) {d : S.O} (hd : d ∈ ⁅Yb, Yb⁆) (hd1 : d ≠ 1)
    {k : S.M} (hk : S.ρ k * t = t * S.ρ k) (hkE : ∀ e ∈ S.Lbar g ⊓ Xb, S.ρ k * e = e * S.ρ k)
    (hkX : ∀ x ∈ Xb, (S.ρ k)⁻¹ * x * S.ρ k ∈ Xb) {y : S.O} (hyY : y ∈ Yb)
    (hyL : y ∈ S.Lbar g) : S.ρ k * y * (S.ρ k)⁻¹ ∈ zpowers t ⊔ Yb := by
  obtain ⟨k₁, hk₁, hkk₁⟩ := D.exists_Lbar_eq_of_commute hCE hd hd1 hk hkE
  have hdY := ((D.dec.mem_commutator_iff).mp hd).1
  have hk₁Y : S.ρ k₁ ∈ Yb := by
    rcases hk₁ with h | h | h <;> rw [h]
    · exact one_mem _
    · exact hdY
    · exact mul_mem hdY hdY
  have hl : S.ρ k * y * (S.ρ k)⁻¹ ∈ S.Lbar ((k₁ : G) * g) := hkk₁ ▸ conj_mem_Lbar_mul S k hyL
  refine D.mem_sup_of_commute_Xb hCE hk₁Y hl fun x hx => ?_
  have h1 := D.dec.comm _ (hkX x hx) y hyY
  calc S.ρ k * y * (S.ρ k)⁻¹ * x =
        S.ρ k * (y * ((S.ρ k)⁻¹ * x * S.ρ k)) * (S.ρ k)⁻¹ := by group
    _ = S.ρ k * (((S.ρ k)⁻¹ * x * S.ρ k) * y) * (S.ρ k)⁻¹ := by rw [h1]
    _ = x * (S.ρ k * y * (S.ρ k)⁻¹) := by group

end Dec108

end CFSG.LargeExtraspecial.S10
