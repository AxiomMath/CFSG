module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8I13R

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

theorem mem_zpowers_iff_one_or_self {G : Type} [Group G] {t g : G} (ht : t * t = 1) :
    g ∈ zpowers t ↔ g = 1 ∨ g = t := by
  constructor
  · intro hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    have h2 : t ^ (2 : ℤ) = 1 := by rw [zpow_two, ht]
    obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
    · left
      rw [zpow_mul, h2, one_zpow]
    · right
      rw [zpow_add_one, zpow_mul, h2, one_zpow, one_mul]
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact mem_zpowers _

namespace OI13Ctx

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T E : Subgroup G}
  {β : G} {B S : Subgroup G} {α σ : G}
  (c : OI13Ctx L z t T E B β S α σ)

theorem card_W2_eq : Nat.card ↥c.W2 = 64 := c.h.card_W2 c.hα c.hF c.hM c.hp

theorem exists_W1_not_W2 : ∃ w ∈ c.W1, w ∉ c.W2 := by
  by_contra hcon
  have hcon' : ∀ w ∈ c.W1, w ∈ c.W2 := fun w hw => by_contra fun hh => hcon ⟨w, hw, hh⟩
  have hQW : c.Qs ≤ c.W2 := by
    intro q hq
    obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := c.Qs_eq hq
    exact mul_mem (hcon' w₁ hw₁) hw₂
  have := Subgroup.card_le_of_le hQW
  rw [c.card_Qs, c.card_W2_eq] at this
  omega

theorem Zs_comm_z {x : G} (hx : x ∈ c.Zs) (hxz : z * x = x * z) : x = 1 ∨ x = t := by
  rcases c.mem_Zs.1 hx with h | h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exfalso
    rw [h] at hxz
    have h2 : z * α * z⁻¹ = α := by
      calc z * α * z⁻¹ = (α * z) * z⁻¹ := by rw [hxz]
        _ = α := by group
    rw [c.h.z_conj_alpha c.hα] at h2
    exact c.h.t_ne (mul_left_cancel (h2.trans (mul_one α).symm))
  · exfalso
    rw [h] at hxz
    have h2 : z * (α * t) * z⁻¹ = α * t := by
      calc z * (α * t) * z⁻¹ = (α * t * z) * z⁻¹ := by rw [hxz]
        _ = α * t := by group
    have h3 : z * (α * t) * z⁻¹ = α := by
      calc z * (α * t) * z⁻¹ = (z * α * z⁻¹) * (z * t * z⁻¹) := by group
        _ = α * t * t := by rw [c.h.z_conj_alpha c.hα, c.h.z_conj_t]
        _ = α := by rw [mul_assoc, c.h.t_sq, mul_one]
    rw [h3] at h2
    exact c.h.t_ne (mul_left_cancel (h2.symm.trans (mul_one α).symm))

theorem comm_alpha_mem {s : G} (hs : s ∈ c.Nc) :
    α * s * α⁻¹ * s⁻¹ = 1 ∨ α * s * α⁻¹ * s⁻¹ = t := by
  have htα : α * t = t * α := c.h.t_comm_S α c.hα.mem
  have ht2 : t⁻¹ = t := inv_eq_of_mul_eq_one_right c.h.t_sq
  rcases c.Nc_perm hs with ⟨h1, -, -⟩ | ⟨h1, -, -⟩
  · left
    have hsa : s * α = α * s := by
      calc s * α = (s * α * s⁻¹) * s := by group
        _ = α * s := by rw [h1]
    calc α * s * α⁻¹ * s⁻¹ = (s * α) * α⁻¹ * s⁻¹ := by rw [hsa]
      _ = 1 := by group
  · right
    have hinv : s * α⁻¹ * s⁻¹ = t * α⁻¹ := by
      have e : s * α⁻¹ * s⁻¹ = (s * α * s⁻¹)⁻¹ := by group
      rw [e, h1, mul_inv_rev, ht2]
    calc α * s * α⁻¹ * s⁻¹ = α * (s * α⁻¹ * s⁻¹) := by group
      _ = α * (t * α⁻¹) := by rw [hinv]
      _ = (α * t) * α⁻¹ := by group
      _ = (t * α) * α⁻¹ := by rw [htα]
      _ = t := by group

theorem Zs_comm_mem {x s : G} (hx : x ∈ c.Zs) (hs : s ∈ c.Nc) :
    x * s * x⁻¹ * s⁻¹ ∈ zpowers t := by
  have hts : t * s = s * t := by
    calc t * s = (s * t * s⁻¹) * s := by rw [c.Nc_t hs]
      _ = s * t := by group
  have hdisj : x * s * x⁻¹ * s⁻¹ = 1 ∨ x * s * x⁻¹ * s⁻¹ = t := by
    rcases c.mem_Zs.1 hx with h | h | h | h
    · left
      rw [h]
      group
    · left
      rw [h]
      calc t * s * t⁻¹ * s⁻¹ = (s * t) * t⁻¹ * s⁻¹ := by rw [hts]
        _ = 1 := by group
    · rw [h]
      exact c.comm_alpha_mem hs
    · rw [h]
      have e : α * t * s * (α * t)⁻¹ * s⁻¹ = α * s * α⁻¹ * s⁻¹ := by
        calc α * t * s * (α * t)⁻¹ * s⁻¹ = α * (t * s) * (t⁻¹ * α⁻¹) * s⁻¹ := by group
          _ = α * (s * t) * (t⁻¹ * α⁻¹) * s⁻¹ := by rw [hts]
          _ = α * s * (t * t⁻¹) * α⁻¹ * s⁻¹ := by group
          _ = α * s * α⁻¹ * s⁻¹ := by group
      rw [e]
      exact c.comm_alpha_mem hs
  rw [mem_zpowers_iff_one_or_self c.h.t_sq]
  exact hdisj

namespace IsRs

variable {c}
variable {Rs : Subgroup G} (hR : c.IsRs Rs)

include hR

theorem conj_inv_mem {n s : G} (hn : n ∈ normalizer (Rs : Set G)) (hs : s ∈ Rs) :
    n⁻¹ * s * n ∈ Rs := by
  apply (mem_normalizer_iff.1 hn (n⁻¹ * s * n)).2
  rw [show n * (n⁻¹ * s * n) * n⁻¹ = s by group]
  exact hs

theorem rho_eq_one_of_comm {n : G} (hn : n ∈ Rs ⊓ c.N1)
    (hcomm : ∀ s ∈ Rs, n * s * n⁻¹ * s⁻¹ = 1 ∨ n * s * n⁻¹ * s⁻¹ = t) :
    c.rho ⟨n, hn.2⟩ = 1 := by
  have key : ∀ m : G, (hm : m ∈ c.N1) → (∀ w ∈ c.W1, m * w * m⁻¹ = w ∨ m * w * m⁻¹ = w * t) →
      c.rho1 ⟨m, hm⟩ = 1 := by
    intro m hm hmw
    refine MulEquiv.ext fun e => ?_
    obtain ⟨w, rfl⟩ := c.thetaHom_surjective e
    rw [c.rho1_theta]
    show c.thetaHom (c.conjW1 ⟨m, hm⟩ w) = c.thetaHom w
    refine Eq.symm ?_
    rw [c.thetaHom_eq_iff]
    rcases hmw w w.2 with h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
  have hRw : ∀ w ∈ c.Qs, w ∈ Rs := fun w hw => hR.Qs_le hw
  have hc1 : ∀ w ∈ c.W1, n * w * n⁻¹ = w ∨ n * w * n⁻¹ = w * t := by
    intro w hw
    have hwq : w ∈ c.Qs := c.W1_le_Qs hw
    rcases hcomm w (hRw w hwq) with h1 | h1
    · left
      calc n * w * n⁻¹ = (n * w * n⁻¹ * w⁻¹) * w := by group
        _ = w := by rw [h1, one_mul]
    · right
      calc n * w * n⁻¹ = (n * w * n⁻¹ * w⁻¹) * w := by group
        _ = t * w := by rw [h1]
        _ = w * t := c.Zs_comm_Qs c.t_mem_Zs hwq
  have hc2 : ∀ w ∈ c.W1, (z * n * z⁻¹) * w * (z * n * z⁻¹)⁻¹ = w ∨
      (z * n * z⁻¹) * w * (z * n * z⁻¹)⁻¹ = w * t := by
    intro w hw
    have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right c.h.z_sq
    have hs : z⁻¹ * w * z ∈ c.W2 := by
      have h0 := c.z_conj_W1 hw
      rw [hzi] at h0 ⊢
      exact h0
    have hsq : z⁻¹ * w * z ∈ c.Qs := c.W2_le_Qs hs
    have hev : (z * n * z⁻¹) * w * (z * n * z⁻¹)⁻¹ =
        z * (n * (z⁻¹ * w * z) * n⁻¹ * (z⁻¹ * w * z)⁻¹) * z⁻¹ * w := by
      group
    have hz1 : z * (1 : G) * z⁻¹ * w = w := by group
    have hzt : z * t * z⁻¹ * w = w * t := by
      rw [c.h.z_conj_t]
      exact c.Zs_comm_Qs c.t_mem_Zs (c.W1_le_Qs hw)
    rcases hcomm _ (hRw _ hsq) with h1 | h1
    · left
      rw [hev, h1, hz1]
    · right
      rw [hev, h1, hzt]
  refine Prod.ext ?_ ?_
  · exact key n hn.2 hc1
  · show c.rho1 (c.zconjN1 ⟨n, hn.2⟩) = 1
    exact key _ (c.z_conj_N1 hn.2) hc2

theorem Z2_le {n : G} (hn : n ∈ Rs) (hcomm : ∀ s ∈ Rs, n * s * n⁻¹ * s⁻¹ ∈ zpowers t) :
    n ∈ c.Zs := by
  have hcomm' : ∀ s ∈ Rs, n * s * n⁻¹ * s⁻¹ = 1 ∨ n * s * n⁻¹ * s⁻¹ = t :=
    fun s hs => (mem_zpowers_iff_one_or_self c.h.t_sq).1 (hcomm s hs)
  by_cases hnN : n ∈ c.N1
  · have hnR : n ∈ Rs ⊓ c.N1 := ⟨hn, hnN⟩
    have hρ := hR.rho_eq_one_of_comm hnR hcomm'
    exact hR.R_inf_KR_le ⟨hnR, c.mem_KR.2 ⟨hnN, hρ⟩⟩
  · exfalso
    rcases c.Nc_perm (hR.le_Nc hn) with ⟨h1, -, -⟩ | ⟨-, h1, -⟩
    · exact hnN (c.mem_N1.2 ⟨hR.le_Nc hn, h1⟩)
    · obtain ⟨w, hw1, hw2⟩ := c.exists_W1_not_W2
      have hwq : w ∈ c.Qs := c.W1_le_Qs hw1
      have hnw : n * w * n⁻¹ ∈ c.W2 := h1 w hw1
      apply hw2
      rcases hcomm' w (hR.Qs_le hwq) with h3 | h3
      · have : n * w * n⁻¹ = w := by
          calc n * w * n⁻¹ = (n * w * n⁻¹ * w⁻¹) * w := by group
            _ = w := by rw [h3, one_mul]
        rwa [this] at hnw
      · have : n * w * n⁻¹ = w * t := by
          calc n * w * n⁻¹ = (n * w * n⁻¹ * w⁻¹) * w := by group
            _ = t * w := by rw [h3]
            _ = w * t := c.Zs_comm_Qs c.t_mem_Zs hwq
        rw [this] at hnw
        have e : w = (w * t) * t⁻¹ := by group
        rw [e]
        exact mul_mem hnw (inv_mem (c.Zs_le_W2 c.t_mem_Zs))

theorem mem_Zs_iff {x : G} :
    x ∈ c.Zs ↔ x ∈ Rs ∧ ∀ s ∈ Rs, x * s * x⁻¹ * s⁻¹ ∈ zpowers t := by
  constructor
  · intro hx
    exact ⟨hR.Qs_le (c.Zs_le_Qs hx), fun s hs => c.Zs_comm_mem hx (hR.le_Nc hs)⟩
  · rintro ⟨hxR, hcomm⟩
    exact hR.Z2_le hxR hcomm

theorem normalizer_t {n : G} (hn : n ∈ normalizer (Rs : Set G)) : n * t * n⁻¹ = t := by
  have ht : t ∈ Rs := hR.Qs_le (c.Zs_le_Qs c.t_mem_Zs)
  have huR : n * t * n⁻¹ ∈ Rs := (mem_normalizer_iff.1 hn t).1 ht
  have hcomm_u : ∀ s ∈ Rs, (n * t * n⁻¹) * s * (n * t * n⁻¹)⁻¹ = s := by
    intro s hs
    have hs' : n⁻¹ * s * n ∈ Rs := hR.conj_inv_mem hn hs
    have hts' : (n⁻¹ * s * n) * t = t * (n⁻¹ * s * n) := by
      have h := c.Nc_t (hR.le_Nc hs')
      calc (n⁻¹ * s * n) * t = ((n⁻¹ * s * n) * t * (n⁻¹ * s * n)⁻¹) * (n⁻¹ * s * n) := by group
        _ = t * (n⁻¹ * s * n) := by rw [h]
    calc n * t * n⁻¹ * s * (n * t * n⁻¹)⁻¹
        = n * (t * (n⁻¹ * s * n) * t⁻¹) * n⁻¹ := by group
      _ = n * ((n⁻¹ * s * n) * t * t⁻¹) * n⁻¹ := by rw [← hts']
      _ = n * (n⁻¹ * s * n) * n⁻¹ := by group
      _ = s := by group
  have huZ : n * t * n⁻¹ ∈ c.Zs := by
    refine (hR.mem_Zs_iff).2 ⟨huR, fun s hs => ?_⟩
    have : n * t * n⁻¹ * s * (n * t * n⁻¹)⁻¹ * s⁻¹ = 1 := by
      rw [hcomm_u s hs]
      group
    rw [this]
    exact one_mem _
  have hzu : z * (n * t * n⁻¹) = (n * t * n⁻¹) * z := by
    have h := hcomm_u z hR.z_mem
    calc z * (n * t * n⁻¹) = (n * t * n⁻¹ * z * (n * t * n⁻¹)⁻¹) * (n * t * n⁻¹) := by
          rw [h]
      _ = (n * t * n⁻¹) * z := by group
  rcases c.Zs_comm_z huZ hzu with h | h
  · exfalso
    apply c.h.t_ne
    calc t = n⁻¹ * (n * t * n⁻¹) * n := by group
      _ = 1 := by rw [h]; group
  · exact h

theorem normalizer_Zs {n x : G} (hn : n ∈ normalizer (Rs : Set G)) (hx : x ∈ c.Zs) :
    n * x * n⁻¹ ∈ c.Zs := by
  obtain ⟨hxR, hcomm⟩ := (hR.mem_Zs_iff).1 hx
  refine (hR.mem_Zs_iff).2 ⟨(mem_normalizer_iff.1 hn x).1 hxR, fun s hs => ?_⟩
  have hs' : n⁻¹ * s * n ∈ Rs := hR.conj_inv_mem hn hs
  have key : n * x * n⁻¹ * s * (n * x * n⁻¹)⁻¹ * s⁻¹ =
      n * (x * (n⁻¹ * s * n) * x⁻¹ * (n⁻¹ * s * n)⁻¹) * n⁻¹ := by
    group
  rw [key]
  rcases (mem_zpowers_iff_one_or_self c.h.t_sq).1 (hcomm _ hs') with h | h
  · rw [h, mul_one, mul_inv_cancel]
    exact one_mem _
  · rw [h, hR.normalizer_t hn]
    exact mem_zpowers t

theorem conj_inv_Zs {n x : G} (hn : n ∈ normalizer (Rs : Set G)) (hx : x ∈ c.Zs) :
    n⁻¹ * x * n ∈ c.Zs := by
  have h := hR.normalizer_Zs (inv_mem hn) hx
  rwa [inv_inv] at h

end IsRs

end OI13Ctx

end CFSG.EvenSporadicStandard.Fin76b
