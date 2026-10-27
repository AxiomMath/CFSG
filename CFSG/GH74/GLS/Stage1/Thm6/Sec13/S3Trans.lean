module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.S3Gen
public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.ExtB
public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.S3Basic

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec13

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G]

theorem no_cyclic_quotient (hs : IsSimpleGroup G) (hna : ∃ a b : G, a * b ≠ b * a) {u : G} :
    ¬ ∃ (N : Subgroup G) (_ : N.Normal), IsCyclic (G ⧸ N) ∧ IsPGroup 2 (G ⧸ N) ∧ u ∉ N := by
  rintro ⟨N, hN, hcyc, -, huN⟩
  have := hs
  have := hN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · subst h
    have hG : IsCyclic G := (QuotientGroup.quotientBot (G := G)).isCyclic.1 hcyc
    obtain ⟨a, b, hab⟩ := hna
    exact hab ((IsCyclic.isMulCommutative (α := G)).is_comm.comm a b)
  · apply huN
    rw [h]
    exact Subgroup.mem_top u

theorem transfer_index_two [Finite G] (h15 : IG_15_15) (hs : IsSimpleGroup G)
    (hna : ∃ a b : G, a * b ≠ b * a) {S S₁ : Subgroup G} {x : G} (hS : Sylow2In S ⊤)
    (hS₁ : S₁ ≤ S) (hidx : S₁.relIndex S = 2) (hxS : x ∈ S) (hx : x ∉ S₁) (hx2 : x * x = 1) :
    ∃ w : G, w * x * w⁻¹ ∈ S₁ ∧ IsExtremal2 S (w * x * w⁻¹) := by
  have hidx' : (S₁.subgroupOf S).index = 2 := hidx
  have hprod : ∀ a ∈ S, ∀ b ∈ S, a ∉ S₁ → b ∉ S₁ → a * b ∈ S₁ := by
    intro a ha b hb haS hbS
    have h := (Subgroup.mul_mem_iff_of_index_two hidx' (a := ⟨a, ha⟩) (b := ⟨b, hb⟩)).2
      (by
        constructor
        · intro h1; exact absurd (mem_subgroupOf.1 h1) haS
        · intro h1; exact absurd (mem_subgroupOf.1 h1) hbS)
    exact mem_subgroupOf.1 h
  have hnot : ∀ a ∈ S, ∀ q ∈ S₁, a ∉ S₁ → a * q ∉ S₁ := by
    intro a ha q hq haS hmem
    apply haS
    have : a = (a * q) * q⁻¹ := by group
    rw [this]
    exact S₁.mul_mem hmem (S₁.inv_mem hq)
  have hnorm : ∀ g ∈ S, ∀ q ∈ S₁, g * q * g⁻¹ ∈ S₁ := by
    intro g hg q hq
    by_cases hgS : g ∈ S₁
    · exact S₁.mul_mem (S₁.mul_mem hgS hq) (S₁.inv_mem hgS)
    · have h1 : g * q ∉ S₁ := hnot g hg q hq hgS
      have h2 : g⁻¹ ∉ S₁ := fun h => hgS (by simpa using S₁.inv_mem h)
      exact hprod (g * q) (S.mul_mem hg (hS₁ hq)) g⁻¹ (S.inv_mem hg) h1 h2
  have hxinv : x⁻¹ ∉ S₁ := fun h => hx (by simpa using S₁.inv_mem h)
  have hdecomp : ∀ p ∈ S, p ∈ S₁ ∨ ∃ q ∈ S₁, p = q * x := by
    intro p hp
    by_cases hpS : p ∈ S₁
    · exact Or.inl hpS
    · right
      refine ⟨p * x⁻¹, hprod p hp x⁻¹ (S.inv_mem hxS) hpS hxinv, by group⟩
  have hne : S₁ ≠ S := by
    intro h
    exact hx (h ▸ hxS)
  have hcyc : ∃ g ∈ S, S = S₁ ⊔ zpowers g := by
    refine ⟨x, hxS, le_antisymm ?_ (sup_le hS₁ ((zpowers_le).2 hxS))⟩
    intro p hp
    rcases hdecomp p hp with h | ⟨q, hq, rfl⟩
    · exact Subgroup.mem_sup_left h
    · exact (S₁ ⊔ zpowers x).mul_mem (Subgroup.mem_sup_left hq)
        (Subgroup.mem_sup_right (mem_zpowers x))
  have hc : ∀ w : G, IsExtremal2 S (w * x * w⁻¹) →
      w * x * w⁻¹ ∈ S₁ ∨ ∃ q ∈ S₁, w * x * w⁻¹ = q * x := fun w hw => hdecomp _ hw.1
  rcases h15 G S S₁ x hS hS₁ hnorm hne hcyc hxS hx hx2 hc with h | ⟨w, hw1, hw2, -⟩
  · exact absurd h (no_cyclic_quotient hs hna)
  · exact ⟨w, hw1, hw2⟩

theorem transfer_cyclic [Finite G] (h15 : IG_15_15) (hs : IsSimpleGroup G)
    (hna : ∃ a b : G, a * b ≠ b * a) {S P : Subgroup G} {x g : G} (hS : Sylow2In S ⊤)
    (hPS : P ≤ S) (hPn : ∀ s ∈ S, ∀ q ∈ P, s * q * s⁻¹ ∈ P) (hxS : x ∈ S) (hxP : x ∉ P)
    (hx2 : x * x = 1) (hg : g ∈ S) (hcyc : S = P ⊔ zpowers g)
    (hc : ∀ p ∈ S, p * p = 1 → p ∈ P ∨ ∃ q ∈ P, p = q * x) :
    ∃ w : G, w * x * w⁻¹ ∈ P ∧ IsExtremal2 S (w * x * w⁻¹) := by
  have hne : P ≠ S := by
    intro h
    exact hxP (h ▸ hxS)
  have hc' : ∀ w : G, IsExtremal2 S (w * x * w⁻¹) →
      w * x * w⁻¹ ∈ P ∨ ∃ q ∈ P, w * x * w⁻¹ = q * x := by
    intro w hw
    apply hc _ hw.1
    calc (w * x * w⁻¹) * (w * x * w⁻¹) = w * (x * x) * w⁻¹ := by group
      _ = 1 := by rw [hx2]; group
  rcases h15 G S P x hS hPS hPn hne ⟨g, hg, hcyc⟩ hxS hxP hx2 hc' with h | ⟨w, hw1, hw2, -⟩
  · exact absurd h (no_cyclic_quotient hs hna)
  · exact ⟨w, hw1, hw2⟩

namespace Ctx3

variable {x : G} {T V H : Subgroup G} {f : G} (c : Ctx3 G x T V H f)
include c

theorem Hstar_card_two [Finite G] {s : G} (hs : s ∈ H ⊔ T) (hsH : s ∉ H) :
    (H.relIndex (H ⊔ T) = 2) ∧ Nat.card ↥(H ⊔ T) = 2 * Nat.card H := by
  have hle := c.relIndex_le_two
  have hne1 : H.relIndex (H ⊔ T) ≠ 1 := by
    intro h1
    rw [relIndex_eq_one] at h1
    exact hsH (h1 hs)
  have hm := relIndex_mul_card H (H ⊔ T)
  have hpos : 0 < Nat.card ↥(H ⊔ T) := Nat.card_pos
  have hne0 : H.relIndex (H ⊔ T) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hm
    omega
  have h2 : H.relIndex (H ⊔ T) = 2 := by omega
  refine ⟨h2, ?_⟩
  rw [h2, inf_of_le_left le_sup_left] at hm
  exact hm.symm

theorem exists_y [Finite G] (h15 : IG_15_15) (hs : IsSimpleGroup G)
    (hna : ∃ a b : G, a * b ≠ b * a) (hSsyl : Sylow2In (H ⊔ T) ⊤)
    (hPn : ∀ s ∈ H ⊔ T, ∀ q ∈ Hzero H f, s * q * s⁻¹ ∈ Hzero H f)
    (hfus : ∀ g : G, g * x * g⁻¹ ∉ Hzero H f) :
    ∃ w : G, w * x * w⁻¹ ∈ H ⊔ T ∧ w * x * w⁻¹ ∉ H ∧ IsExtremal2 (H ⊔ T) (w * x * w⁻¹) := by
  have hxS : x ∈ H ⊔ T := Subgroup.mem_sup_left c.x_mem_H
  have hPS : Hzero H f ≤ H ⊔ T := c.H0_le.trans le_sup_left
  by_cases hB1 : ∃ s ∈ H ⊔ T, s ∉ H ∧ s * s ∈ Hzero H f
  · obtain ⟨s, hsS, hsH, hss⟩ := hB1
    have hsP : s ∉ Hzero H f := fun h => hsH (c.H0_le h)
    have hsn : ∀ q ∈ Hzero H f, s * q * s⁻¹ ∈ Hzero H f := hPn s hsS
    obtain ⟨hrelH, hcardS⟩ := c.Hstar_card_two hsS hsH
    have hcard1 := card_sup_zpowers_sq hss hsn hsP
    have hS₁S : Hzero H f ⊔ zpowers s ≤ H ⊔ T :=
      sup_le hPS ((zpowers_le).2 hsS)
    have hrel1 : (Hzero H f ⊔ zpowers s).relIndex (H ⊔ T) = 2 := by
      have hm := relIndex_mul_card (Hzero H f ⊔ zpowers s) (H ⊔ T)
      rw [inf_of_le_left hS₁S, hcard1, hcardS, c.card_H] at hm
      have hpos : 0 < Nat.card (Hzero H f) := Nat.card_pos
      have : (Hzero H f ⊔ zpowers s).relIndex (H ⊔ T) * (2 * Nat.card (Hzero H f)) =
          2 * (2 * Nat.card (Hzero H f)) := hm
      exact Nat.eq_of_mul_eq_mul_right (by omega) this
    have hxS₁ : x ∉ Hzero H f ⊔ zpowers s := by
      intro hx
      obtain ⟨q, hq, h1 | h1⟩ := (mem_sup_zpowers_sq hss hsn).1 hx
      · exact c.x_notin_H0 (h1 ▸ hq)
      · apply hsH
        have : s = q⁻¹ * x := by rw [h1]; group
        rw [this]
        exact H.mul_mem (H.inv_mem (c.H0_le hq)) c.x_mem_H
    obtain ⟨w, hw1, hw2⟩ := transfer_index_two h15 hs hna hSsyl hS₁S hrel1 hxS hxS₁ c.x_sq
    refine ⟨w, hS₁S hw1, ?_, hw2⟩
    obtain ⟨q, hq, h1 | h1⟩ := (mem_sup_zpowers_sq hss hsn).1 hw1
    · exact absurd (h1 ▸ hq) (hfus w)
    · intro hy
      apply hsH
      have : s = q⁻¹ * (w * x * w⁻¹) := by rw [h1]; group
      rw [this]
      exact H.mul_mem (H.inv_mem (c.H0_le hq)) hy
  · exfalso
    push Not at hB1
    have hsqH : ∀ p ∈ H ⊔ T, p * p = 1 → p ∈ H := by
      intro p hp hp2
      by_contra hpH
      have := hB1 p hp hpH
      apply this
      rw [hp2]
      exact (Hzero H f).one_mem
    have hcyc : ∃ g ∈ H ⊔ T, H ⊔ T = Hzero H f ⊔ zpowers g := by
      by_cases hSH : H ⊔ T ≤ H
      · have hSeq : H ⊔ T = H := le_antisymm hSH le_sup_left
        refine ⟨x, hxS, ?_⟩
        rw [hSeq]
        exact c.hc.b_eq
      · obtain ⟨g, hgS, hgH⟩ := IsConcreteLE.not_le_iff_exists.1 hSH
        obtain ⟨hrelH, hcardS⟩ := c.Hstar_card_two hgS hgH
        have hg2H : g * g ∈ H := by
          have hidx : (H.subgroupOf (H ⊔ T)).index = 2 := hrelH
          have := Subgroup.mul_self_mem_of_index_two hidx ⟨g, hgS⟩
          exact mem_subgroupOf.1 this
        have hg2P : g * g ∉ Hzero H f := hB1 g hgS hgH
        obtain ⟨q, hq, h1 | h1⟩ := (c.mem_H_iff).1 hg2H
        · exact absurd (h1 ▸ hq) hg2P
        · have hxK : x ∈ Hzero H f ⊔ zpowers g := by
            have : x = q⁻¹ * (g * g) := by rw [h1]; group
            rw [this]
            exact (Hzero H f ⊔ zpowers g).mul_mem
              (Subgroup.mem_sup_left ((Hzero H f).inv_mem hq))
              ((Hzero H f ⊔ zpowers g).mul_mem (Subgroup.mem_sup_right (mem_zpowers g))
                (Subgroup.mem_sup_right (mem_zpowers g)))
          have hHK : H ≤ Hzero H f ⊔ zpowers g := by
            calc H = Hzero H f ⊔ zpowers x := c.hc.b_eq
              _ ≤ Hzero H f ⊔ zpowers g := sup_le le_sup_left ((zpowers_le).2 hxK)
          have hKS : Hzero H f ⊔ zpowers g ≤ H ⊔ T := sup_le hPS ((zpowers_le).2 hgS)
          have hHlt : H < Hzero H f ⊔ zpowers g := by
            refine lt_of_le_of_ne hHK ?_
            intro h
            apply hgH
            rw [h]
            exact Subgroup.mem_sup_right (mem_zpowers g)
          have h1c := Subgroup.card_lt_of_lt hHlt
          have h2c : Nat.card H ∣ Nat.card ↥(Hzero H f ⊔ zpowers g) := Subgroup.card_dvd_of_le hHK
          have h3c : Nat.card ↥(Hzero H f ⊔ zpowers g) ≤ Nat.card ↥(H ⊔ T) :=
            Subgroup.card_le_of_le hKS
          obtain ⟨m, hm⟩ := h2c
          have hHpos : 0 < Nat.card H := Nat.card_pos
          have hm2 : m = 2 := by
            rw [hm] at h1c h3c
            rw [hcardS] at h3c
            have hm1 : 1 < m := by
              by_contra hle
              have : m ≤ 1 := by omega
              have : Nat.card H * m ≤ Nat.card H * 1 := Nat.mul_le_mul_left _ this
              omega
            have hm3 : m ≤ 2 := by
              by_contra hgt
              have : 3 ≤ m := by omega
              have : Nat.card H * 3 ≤ Nat.card H * m := Nat.mul_le_mul_left _ this
              omega
            omega
          refine ⟨g, hgS, ?_⟩
          symm
          apply Subgroup.eq_of_le_of_card_ge hKS
          rw [hcardS, hm, hm2]
          omega
    obtain ⟨g, hgS, hgcyc⟩ := hcyc
    have hc : ∀ p ∈ H ⊔ T, p * p = 1 → p ∈ Hzero H f ∨ ∃ q ∈ Hzero H f, p = q * x := by
      intro p hp hp2
      obtain ⟨q, hq, h1 | h1⟩ := (c.mem_H_iff).1 (hsqH p hp hp2)
      · exact Or.inl (h1 ▸ hq)
      · exact Or.inr ⟨q, hq, h1⟩
    obtain ⟨w, hw1, -⟩ := transfer_cyclic h15 hs hna hSsyl hPS hPn hxS c.x_notin_H0 c.x_sq hgS
      hgcyc hc
    exact hfus w hw1

end Ctx3

end CFSG.GH74.GLS.Stage1.Thm6.Sec13
