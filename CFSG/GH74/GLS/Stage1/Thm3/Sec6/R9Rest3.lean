module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R9Rest2

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6.R1

open Subgroup CFSG.GH74.GLS.Stage1.Thm3.Sec4.M CFSG.GH74.GLS CFSG.GH74

variable {G : Type} [Group G] [Finite G] {z : G} {S P Q : Subgroup G} {FA : G → Prop}

namespace Setup9

variable {U : Subgroup G} {x u₁ u₂ : G} (c : Setup9 G z S P Q FA U x u₁ u₂)
include c

section Uprime

variable {p₀ q₀ : G} (hp : p₀ ∈ P) (hq : q₀ ∈ Q) (hp' : p₀ ∉ P ⊓ centralizer ({u₁} : Set G))
  (hq' : q₀ ∉ Q ⊓ centralizer ({u₂} : Set G))
include hp hq hp' hq'

theorem u'_sq : (p₀ * q₀) * (p₀ * q₀) = 1 := by
  have h1 := (c.quatOut₁ p₀ hp hp').1
  have h2 := (c.quatOut₂ q₀ hq hq').1
  have hc : q₀ * p₀ = p₀ * q₀ := (c.cfg.PQ_comm p₀ hp q₀ hq).symm
  calc (p₀ * q₀) * (p₀ * q₀) = p₀ * (q₀ * p₀) * q₀ := by group
    _ = (p₀ * p₀) * (q₀ * q₀) := by rw [hc]; group
    _ = 1 := by rw [h1, h2, c.hz2]

omit hq' in
theorem u'_inv₁ : ∀ v ∈ P ⊓ centralizer ({u₁} : Set G),
    (p₀ * q₀) * v * (p₀ * q₀)⁻¹ = v⁻¹ := by
  intro v hv
  have hqv : q₀ * v = v * q₀ := (c.cfg.PQ_comm v hv.1 q₀ hq).symm
  calc (p₀ * q₀) * v * (p₀ * q₀)⁻¹ = p₀ * (q₀ * v) * q₀⁻¹ * p₀⁻¹ := by group
    _ = p₀ * (v * q₀) * q₀⁻¹ * p₀⁻¹ := by rw [hqv]
    _ = p₀ * v * p₀⁻¹ := by group
    _ = v⁻¹ := (c.quatOut₁ p₀ hp hp').2 v hv

omit hp' in
theorem u'_inv₂ : ∀ v ∈ Q ⊓ centralizer ({u₂} : Set G),
    (p₀ * q₀) * v * (p₀ * q₀)⁻¹ = v⁻¹ := by
  intro v hv
  have hqv : q₀ * v * q₀⁻¹ ∈ Q := Q.mul_mem (Q.mul_mem hq hv.1) (Q.inv_mem hq)
  have hpc : p₀ * (q₀ * v * q₀⁻¹) = (q₀ * v * q₀⁻¹) * p₀ := c.cfg.PQ_comm p₀ hp _ hqv
  calc (p₀ * q₀) * v * (p₀ * q₀)⁻¹ = p₀ * (q₀ * v * q₀⁻¹) * p₀⁻¹ := by group
    _ = (q₀ * v * q₀⁻¹) * p₀ * p₀⁻¹ := by rw [hpc]
    _ = q₀ * v * q₀⁻¹ := by group
    _ = v⁻¹ := (c.quatOut₂ q₀ hq hq').2 v hv


theorem u'_mem_W : p₀ * q₀ ∈ S ⊓ centralizer (U : Set G) := by
  have hS : p₀ * q₀ ∈ S := S.mul_mem (c.cfg.P_le hp) (c.cfg.Q_le hq)
  have e1 := c.u'_inv₁ hp hq hp' u₁ c.u₁_mem_V₁
  have e2 := c.u'_inv₂ hp hq hq' u₂ c.u₂_mem_V₂
  have hz2c : u₂ * z = z * u₂ := c.z_comm (c.cfg.Q_le c.u₂_mem)
  have hconj : (p₀ * q₀) * (u₁ * u₂) * (p₀ * q₀)⁻¹ = u₁ * u₂ := by
    calc (p₀ * q₀) * (u₁ * u₂) * (p₀ * q₀)⁻¹
        = ((p₀ * q₀) * u₁ * (p₀ * q₀)⁻¹) * ((p₀ * q₀) * u₂ * (p₀ * q₀)⁻¹) := by group
      _ = u₁⁻¹ * u₂⁻¹ := by rw [e1, e2]
      _ = (u₁ * z) * (u₂ * z) := by rw [c.u₁_inv, c.u₂_inv]
      _ = u₁ * (z * u₂) * z := by group
      _ = u₁ * (u₂ * z) * z := by rw [← hz2c]
      _ = u₁ * u₂ * (z * z) := by group
      _ = u₁ * u₂ := by rw [c.hz2, mul_one]
  have hu : (p₀ * q₀) * (u₁ * u₂) = (u₁ * u₂) * (p₀ * q₀) := mul_inv_eq_iff_eq_mul.1 hconj
  exact ⟨hS, Subgroup.mem_centralizer_iff.2 (fun w hw =>
    (c.comm_U_of (c.z_comm hS) hu w hw).symm)⟩


end Uprime

section Struct

variable {a₀ p₀ q₀ : G}

theorem A_mem (ha₀ : a₀ ∈ P ⊓ centralizer ({u₁} : Set G))
    (hgen : ∀ v ∈ P ⊓ centralizer ({u₁} : Set G), v ∈ zpowers a₀) {a : G}
    (ha : a ∈ (P ⊓ centralizer ({u₁} : Set G)) ⊔ zpowers (x * a₀ * x⁻¹)) :
    ∃ v ∈ P ⊓ centralizer ({u₁} : Set G), ∃ t ∈ zpowers (x * a₀ * x⁻¹), a = v * t :=
  mem_sup_of_commute (fun v hv t ht => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ht
    exact c.V₁_comm_gpow ha₀ hgen hv k) ha

theorem A_comm_V (ha₀ : a₀ ∈ P ⊓ centralizer ({u₁} : Set G))
    (hgen : ∀ v ∈ P ⊓ centralizer ({u₁} : Set G), v ∈ zpowers a₀) {a v : G}
    (ha : a ∈ (P ⊓ centralizer ({u₁} : Set G)) ⊔ zpowers (x * a₀ * x⁻¹))
    (hv : v ∈ P ⊓ centralizer ({u₁} : Set G)) : a * v = v * a := by
  obtain ⟨v', hv', t, ht, rfl⟩ := c.A_mem ha₀ hgen ha
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ht
  have h1 : v' * v = v * v' := comm_of_cyclic c.V₁_cyc hv' hv
  have h2 := c.V₁_comm_gpow ha₀ hgen hv k
  calc v' * (x * a₀ * x⁻¹) ^ k * v = v' * ((x * a₀ * x⁻¹) ^ k * v) := by group
    _ = v' * (v * (x * a₀ * x⁻¹) ^ k) := by rw [← h2]
    _ = (v' * v) * (x * a₀ * x⁻¹) ^ k := by group
    _ = (v * v') * (x * a₀ * x⁻¹) ^ k := by rw [h1]
    _ = v * (v' * (x * a₀ * x⁻¹) ^ k) := by group

theorem A_comm_g (ha₀ : a₀ ∈ P ⊓ centralizer ({u₁} : Set G))
    (hgen : ∀ v ∈ P ⊓ centralizer ({u₁} : Set G), v ∈ zpowers a₀) {a : G}
    (ha : a ∈ (P ⊓ centralizer ({u₁} : Set G)) ⊔ zpowers (x * a₀ * x⁻¹)) :
    a * (x * a₀ * x⁻¹) = (x * a₀ * x⁻¹) * a := by
  obtain ⟨v', hv', t, ht, rfl⟩ := c.A_mem ha₀ hgen ha
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ht
  have h1 : v' * (x * a₀ * x⁻¹) = (x * a₀ * x⁻¹) * v' := by
    simpa using c.V₁_comm_gpow ha₀ hgen hv' 1
  have h2 : (x * a₀ * x⁻¹) ^ k * (x * a₀ * x⁻¹) = (x * a₀ * x⁻¹) * (x * a₀ * x⁻¹) ^ k :=
    (Commute.zpow_left (Commute.refl (x * a₀ * x⁻¹)) k).eq
  generalize x * a₀ * x⁻¹ = g at h1 h2 ⊢
  calc v' * g ^ k * g = v' * (g ^ k * g) := mul_assoc _ _ _
    _ = v' * (g * g ^ k) := by rw [h2]
    _ = (v' * g) * g ^ k := (mul_assoc _ _ _).symm
    _ = (g * v') * g ^ k := by rw [h1]
    _ = g * (v' * g ^ k) := mul_assoc _ _ _

theorem A_card (ha₀ : a₀ ∈ P ⊓ centralizer ({u₁} : Set G))
    (hgen : ∀ v ∈ P ⊓ centralizer ({u₁} : Set G), v ∈ zpowers a₀) :
    Nat.card ↥((P ⊓ centralizer ({u₁} : Set G)) ⊔ zpowers (x * a₀ * x⁻¹)) =
      Nat.card ↥(P ⊓ centralizer ({u₁} : Set G)) * Nat.card ↥(P ⊓ centralizer ({u₁} : Set G)) := by
  have hcomm : ∀ a ∈ P ⊓ centralizer ({u₁} : Set G), ∀ b ∈ zpowers (x * a₀ * x⁻¹), a * b = b * a := by
    intro a ha b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact c.V₁_comm_gpow ha₀ hgen ha k
  have h := card_sup_mul_card_inf (le_normalizer_of_commute hcomm)
  have hinf : (P ⊓ centralizer ({u₁} : Set G)) ⊓ zpowers (x * a₀ * x⁻¹) = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha.2
    rw [Subgroup.mem_bot]
    exact c.gpow_P ha₀ hgen k ha.1.1
  rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, orderOf_g ha₀ hgen] at h
  exact h

theorem card_P_eq : Nat.card ↥P = 2 * Nat.card ↥(P ⊓ centralizer ({u₁} : Set G)) := by
  have := Subgroup.relIndex_mul_card (P ⊓ centralizer ({u₁} : Set G)) P
  rw [c.V₁_idx, inf_of_le_left inf_le_left] at this
  exact this.symm

theorem card_R : Nat.card ↥(P ⊔ Q) * 2 = Nat.card ↥P * Nat.card ↥Q := by
  have h := card_sup_mul_card_inf (A := P) (B := Q)
    (le_normalizer_of_commute (fun a ha b hb => c.cfg.PQ_comm a ha b hb))
  have hinf : P ⊓ Q = zpowers z := by
    ext y
    constructor
    · intro hy
      exact (mem_zpowers_of_sq c.hz2).2 (c.cfg.PQ_inf y hy.1 hy.2)
    · intro hy
      rcases (mem_zpowers_of_sq c.hz2).1 hy with rfl | rfl
      · exact ⟨one_mem _, one_mem _⟩
      · exact ⟨c.cfg.z_P, c.cfg.z_Q⟩
  have hcard : Nat.card ↥(P ⊓ Q) = 2 := by
    rw [hinf, Nat.card_zpowers]
    exact orderOf_two_of_sq_one c.hz2 c.hz1
  rw [hcard] at h
  exact h

theorem card_S : Nat.card ↥S = 2 * Nat.card ↥(P ⊔ Q) := by
  have := Subgroup.relIndex_mul_card (P ⊔ Q) S
  rw [c.idx, inf_of_le_left (sup_le c.cfg.P_le c.cfg.Q_le)] at this
  exact this.symm

theorem W_card_le : 2 * Nat.card ↥(S ⊓ centralizer (U : Set G)) ≤ Nat.card ↥S := by
  have hex : ∃ s ∈ S, s ∉ S ⊓ centralizer (U : Set G) := by
    by_contra hcon
    push Not at hcon
    have hu := c.U_four.1 (u₁ * u₂) c.u_mem
    have hcent : ∀ s ∈ S, (u₁ * u₂) * s = s * (u₁ * u₂) := fun s hs =>
      Subgroup.mem_centralizer_iff.1 (hcon s hs).2 (u₁ * u₂) c.u_mem
    rcases c.cfg.Z_inv (u₁ * u₂) (c.U_le_S c.u_mem) hcent hu with h | h
    · exact c.u_ne.1 h
    · exact c.u_ne.2 h
  obtain ⟨s, hsS, hsW⟩ := hex
  have hWS : S ⊓ centralizer (U : Set G) ≤ S := inf_le_left
  have h1 := Subgroup.relIndex_mul_card (S ⊓ centralizer (U : Set G)) S
  rw [inf_of_le_left hWS] at h1
  have hne1 : (S ⊓ centralizer (U : Set G)).relIndex S ≠ 1 := by
    intro h
    exact hsW (Subgroup.relIndex_eq_one.1 h hsS)
  have hne0 : (S ⊓ centralizer (U : Set G)).relIndex S ≠ 0 := B.relIndex_ne_zero'
  have h2 : 2 ≤ (S ⊓ centralizer (U : Set G)).relIndex S := by omega
  nlinarith

end Struct

end Setup9

end CFSG.GH74.GLS.Stage1.Thm3.Sec6.R1
