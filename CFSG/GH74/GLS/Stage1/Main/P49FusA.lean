module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R9Rest2

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm2.Recip
open scoped commutatorElement

section FusA


variable {G : Type} [Group G] [Finite G] {z : G} {S P Q : Subgroup G} {FA : G → Prop}
  {U : Subgroup G} {x u₁ u₂ : G}

theorem u_sq49 (c : R1.Setup9 G z S P Q FA U x u₁ u₂) : (u₁ * u₂) * (u₁ * u₂) = 1 := by
  have hc : u₁ * u₂ = u₂ * u₁ := c.cfg.PQ_comm u₁ c.u₁_mem u₂ c.u₂_mem
  calc (u₁ * u₂) * (u₁ * u₂) = u₁ * (u₂ * u₁) * u₂ := by group
    _ = u₁ * (u₁ * u₂) * u₂ := by rw [← hc]
    _ = (u₁ * u₁) * (u₂ * u₂) := by group
    _ = 1 := by rw [c.u₁_sq, c.u₂_sq, c.hz2]

theorem isConj_u49 (c : R1.Setup9 G z S P Q FA U x u₁ u₂) (hx3 : IsPGroup 3 ↥(zpowers x)) :
    IsConj z (u₁ * u₂) := by
  have hz2 := c.hz2
  have hz1 := c.hz1
  have hUS : U ≤ S := c.U_le_S
  have hzu : (u₁ * u₂) * z = z * (u₁ * u₂) := c.z_comm (hUS c.u_mem)
  have hu2 := u_sq49 c
  have hu1 := c.u_ne.1
  have huz := c.u_ne.2
  rcases c.z'_cases with e | e
  · exact isConj_iff.2 ⟨x, e⟩
  · have hw := c.x_U _ c.u_mem
    have hzu1 : z * (u₁ * u₂) ≠ 1 := by
      intro h1
      apply huz
      have : u₁ * u₂ = z⁻¹ := by
        calc u₁ * u₂ = z⁻¹ * (z * (u₁ * u₂)) := by group
          _ = z⁻¹ := by rw [h1, mul_one]
      rw [this, inv_eq_of_mul_eq_one_right hz2]
    rcases c.mem_U hw with w | w | w | w
    · exfalso
      apply hu1
      calc u₁ * u₂ = x⁻¹ * (x * (u₁ * u₂) * x⁻¹) * x := by group
        _ = 1 := by rw [w]; group
    · refine isConj_iff.2 ⟨x * x, ?_⟩
      calc x * x * z * (x * x)⁻¹ = x * (x * z * x⁻¹) * x⁻¹ := by group
        _ = x * (z * (u₁ * u₂)) * x⁻¹ := by rw [e]
        _ = (x * z * x⁻¹) * (x * (u₁ * u₂) * x⁻¹) := by group
        _ = (z * (u₁ * u₂)) * z := by rw [e, w]
        _ = u₁ * u₂ := by
          calc (z * (u₁ * u₂)) * z = z * ((u₁ * u₂) * z) := by group
            _ = z * (z * (u₁ * u₂)) := by rw [hzu]
            _ = (z * z) * (u₁ * u₂) := by group
            _ = u₁ * u₂ := by rw [hz2, one_mul]
    · exfalso
      have hxx : (x * x) * z * (x * x)⁻¹ = z := by
        calc x * x * z * (x * x)⁻¹ = x * (x * z * x⁻¹) * x⁻¹ := by group
          _ = x * (z * (u₁ * u₂)) * x⁻¹ := by rw [e]
          _ = (x * z * x⁻¹) * (x * (u₁ * u₂) * x⁻¹) := by group
          _ = (z * (u₁ * u₂)) * (u₁ * u₂) := by rw [e, w]
          _ = z * ((u₁ * u₂) * (u₁ * u₂)) := by group
          _ = z := by rw [hu2, mul_one]
      obtain ⟨m, hm⟩ := (IsPGroup.iff_card.1 hx3)
      have hord : orderOf x = 3 ^ m := by rw [← Nat.card_zpowers]; exact hm
      have hodd : Odd (orderOf x) := by rw [hord]; exact Odd.pow (by decide)
      obtain ⟨k, hk⟩ := hodd
      have hxk : x = (x * x) ^ (k + 1) := by
        calc x = x ^ (orderOf x + 1) := by rw [pow_succ, pow_orderOf_eq_one, one_mul]
          _ = x ^ (2 * (k + 1)) := by rw [hk]; ring_nf
          _ = (x * x) ^ (k + 1) := by rw [pow_mul, sq]
      have hcomm : Commute (x * x) z := by
        have : (x * x) * z = z * (x * x) := by
          calc (x * x) * z = ((x * x) * z * (x * x)⁻¹) * (x * x) := by group
            _ = z * (x * x) := by rw [hxx]
        exact this
      have hc2 : Commute x z := by
        rw [hxk]
        exact hcomm.pow_left _
      exact c.x_z (by rw [hc2.eq]; group)
    · exfalso
      have h1 : x * (z * (u₁ * u₂)) * x⁻¹ = 1 := by
        calc x * (z * (u₁ * u₂)) * x⁻¹ = (x * z * x⁻¹) * (x * (u₁ * u₂) * x⁻¹) := by group
          _ = (z * (u₁ * u₂)) * (z * (u₁ * u₂)) := by rw [e, w]
          _ = (z * z) * ((u₁ * u₂) * (u₁ * u₂)) := by
            calc (z * (u₁ * u₂)) * (z * (u₁ * u₂)) = z * ((u₁ * u₂) * z) * (u₁ * u₂) := by group
              _ = z * (z * (u₁ * u₂)) * (u₁ * u₂) := by rw [hzu]
              _ = (z * z) * ((u₁ * u₂) * (u₁ * u₂)) := by group
          _ = 1 := by rw [hz2, hu2, one_mul]
      apply hzu1
      calc z * (u₁ * u₂) = x⁻¹ * (x * (z * (u₁ * u₂)) * x⁻¹) * x := by group
        _ = 1 := by rw [h1]; group


theorem szs49 (c : R1.Setup9 G z S P Q FA U x u₁ u₂) {s : G} (hs : s ∈ S) : s * z * s⁻¹ = z := by
  calc s * z * s⁻¹ = z * s * s⁻¹ := by rw [c.z_comm hs]
    _ = z := by group

theorem conj_u₂_w49 (c : R1.Setup9 G z S P Q FA U x u₁ u₂) {s : G} (hs : s ∈ S) :
    ∃ w : G, (w = 1 ∨ w = z) ∧ s * u₂ * s⁻¹ = u₂ * w := by
  rcases (c.norm_u hs).2 with h | h
  · exact ⟨1, Or.inl rfl, by rw [h, mul_one]⟩
  · exact ⟨z, Or.inr rfl, h⟩

theorem conj_comm_u₂49 (c : R1.Setup9 G z S P Q FA U x u₁ u₂) {s t : G} (hs : s ∈ S) (ht : t ∈ S) :
    s * (t * u₂ * t⁻¹) * s⁻¹ = t * (s * u₂ * s⁻¹) * t⁻¹ := by
  obtain ⟨wt, hwt, hwt'⟩ := conj_u₂_w49 c ht
  obtain ⟨ws, hws, hws'⟩ := conj_u₂_w49 c hs
  have hswt : s * wt * s⁻¹ = wt := by
    rcases hwt with rfl | rfl
    · group
    · exact szs49 c hs
  have htws : t * ws * t⁻¹ = ws := by
    rcases hws with rfl | rfl
    · group
    · exact szs49 c ht
  have hcomm : wt * ws = ws * wt := by
    rcases hwt with rfl | rfl <;> rcases hws with rfl | rfl <;> simp
  calc s * (t * u₂ * t⁻¹) * s⁻¹ = (s * u₂ * s⁻¹) * (s * wt * s⁻¹) := by rw [hwt']; group
    _ = (u₂ * ws) * wt := by rw [hws', hswt]
    _ = u₂ * (ws * wt) := by group
    _ = u₂ * (wt * ws) := by rw [hcomm]
    _ = (u₂ * wt) * ws := by group
    _ = (t * u₂ * t⁻¹) * (t * ws * t⁻¹) := by rw [hwt', htws]
    _ = t * (s * u₂ * s⁻¹) * t⁻¹ := by rw [hws']; group

theorem commutator_u₂49 (c : R1.Setup9 G z S P Q FA U x u₁ u₂) {s t : G} (hs : s ∈ S) (ht : t ∈ S) :
    (s * t * s⁻¹ * t⁻¹) * u₂ = u₂ * (s * t * s⁻¹ * t⁻¹) := by
  have h := conj_comm_u₂49 c (S.inv_mem hs) (S.inv_mem ht)
  simp only [inv_inv] at h
  have key : (s * t * s⁻¹ * t⁻¹) * u₂ * (s * t * s⁻¹ * t⁻¹)⁻¹ = u₂ := by
    calc (s * t * s⁻¹ * t⁻¹) * u₂ * (s * t * s⁻¹ * t⁻¹)⁻¹
        = s * t * (s⁻¹ * (t⁻¹ * u₂ * t) * s) * t⁻¹ * s⁻¹ := by group
      _ = s * t * (t⁻¹ * (s⁻¹ * u₂ * s) * t) * t⁻¹ * s⁻¹ := by rw [h]
      _ = u₂ := by group
  calc (s * t * s⁻¹ * t⁻¹) * u₂
      = ((s * t * s⁻¹ * t⁻¹) * u₂ * (s * t * s⁻¹ * t⁻¹)⁻¹) * (s * t * s⁻¹ * t⁻¹) := by group
    _ = u₂ * (s * t * s⁻¹ * t⁻¹) := by rw [key]

end FusA

section FusA2

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} {U : Subgroup G} {x u₁ u₂ : G}

theorem relIndex_M49 {P Q : Subgroup G} {FA : G → Prop}
    (c : R1.Setup9 G z S P Q FA U x u₁ u₂) {y : G} (hyS : y ∈ S) (hy : y * u₂ * y⁻¹ = u₂ * z) :
    (S ⊓ centralizer ({u₂} : Set G)).relIndex S ≤ 2 := by
  have hz2 := c.hz2
  have hz1 := c.hz1
  have h2 : ((S ⊓ centralizer ({u₂} : Set G)).subgroupOf S).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨y, hyS⟩, fun b => ?_⟩
    have hb := b.2
    obtain ⟨w, hw, hw'⟩ := conj_u₂_w49 c hb
    have hmem : ∀ g : G, g ∈ S → (g ∈ S ⊓ centralizer ({u₂} : Set G) ↔ g * u₂ * g⁻¹ = u₂) := by
      intro g hg
      rw [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
      constructor
      · rintro ⟨-, h1⟩
        calc g * u₂ * g⁻¹ = u₂ * g * g⁻¹ := by rw [h1]
          _ = u₂ := by group
      · intro h1
        refine ⟨hg, ?_⟩
        calc g * u₂ = (g * u₂ * g⁻¹) * g := by group
          _ = u₂ * g := by rw [h1]
    have hmemS : ∀ g : S, g ∈ (S ⊓ centralizer ({u₂} : Set G)).subgroupOf S ↔
        (g : G) * u₂ * (g : G)⁻¹ = u₂ := by
      intro g
      rw [Subgroup.mem_subgroupOf]
      exact hmem g g.2
    rw [hmemS, hmemS]
    have hby : ((b * ⟨y, hyS⟩ : S) : G) * u₂ * ((b * ⟨y, hyS⟩ : S) : G)⁻¹ = (u₂ * w) * z := by
      show (b : G) * y * u₂ * ((b : G) * y)⁻¹ = (u₂ * w) * z
      calc (b : G) * y * u₂ * ((b : G) * y)⁻¹ = (b : G) * (y * u₂ * y⁻¹) * (b : G)⁻¹ := by group
        _ = (b : G) * (u₂ * z) * (b : G)⁻¹ := by rw [hy]
        _ = ((b : G) * u₂ * (b : G)⁻¹) * ((b : G) * z * (b : G)⁻¹) := by group
        _ = (u₂ * w) * z := by rw [hw', szs49 c hb]
    have hne : u₂ * z ≠ u₂ := fun e => hz1 (by simpa using e)
    have hzz : u₂ * z * z = u₂ := by rw [mul_assoc, hz2, mul_one]
    rcases hw with rfl | rfl
    · right
      refine ⟨by simpa using hw', ?_⟩
      intro hcon
      rw [hby] at hcon
      exact hne (by simpa using hcon)
    · left
      refine ⟨by rw [hby]; exact hzz, ?_⟩
      intro hcon
      rw [hw'] at hcon
      exact hne hcon
  exact h2.le


end FusA2

end CFSG.GH74.GLS.Stage1.Thm3.Sec6
