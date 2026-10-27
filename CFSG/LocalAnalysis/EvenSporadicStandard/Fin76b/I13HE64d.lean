module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.I13HE64c

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

namespace E64

variable {G : Type*} [Group G]

@[expose] def P2 (P : Subgroup G) (z : G) : Subgroup G := P.comap (MulAut.conj z).toMonoidHom

theorem mem_P2 {P : Subgroup G} {z p : G} : p ∈ P2 P z ↔ z * p * z⁻¹ ∈ P := Iff.rfl

theorem mem_grp_of {b₁ b₂ b : G} (hb : b = b₁ ∨ b = b₂ ∨ b = b₁ * b₂) :
    b ∈ closure ({b₁, b₂} : Set G) := by
  rcases hb with h | h | h <;> rw [h]
  exacts [IsKlein.b₁_mem_grp, IsKlein.b₂_mem_grp,
    mul_mem IsKlein.b₁_mem_grp IsKlein.b₂_mem_grp]

end E64

namespace I13Ctx

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T₀ E : Subgroup G}
  {Q : Sylow 2 G} {x β : G} {B S : Subgroup G} {α : G}
  (c : I13Ctx L z t T₀ E Q x β B S α) {P : Subgroup G} (pd : c.PData P)

include c pd

theorem P2_le_W2 : E64.P2 P z ≤ c.W2 := by
  intro p hp
  have h1 : z * p * z⁻¹ ∈ c.W1 := pd.le hp
  have := c.z_conj_W1 h1
  rwa [c.z_conj_conj] at this

omit pd in
theorem z_conj_mem_P2 {p : G} (hp : p ∈ P) : z * p * z⁻¹ ∈ E64.P2 P z := by
  rw [E64.mem_P2, c.z_conj_conj]
  exact hp

theorem P_comm_P2 {a a' : G} (ha : a ∈ P) (ha' : a' ∈ E64.P2 P z) : a * a' = a' * a :=
  c.W1_comm_W2 (pd.le ha) (c.P2_le_W2 pd ha')

theorem t_not_mem_P : t ∉ P := by
  intro ht
  have h1 : t * (z * t * z⁻¹) = 1 * (z * 1 * z⁻¹) := by
    rw [c.z_conj_t, c.h.t_sq]
    group
  exact c.h.t_ne (pd.inj t ht 1 P.one_mem h1)

theorem alpha_t_not_mem_P : α * t ∉ P := by
  intro h
  apply c.t_not_mem_P pd
  have := mul_mem (inv_mem pd.alpha_mem) h
  have e : α⁻¹ * (α * t) = t := by group
  rwa [e] at this

theorem alpha_t_mem_P2 : α * t ∈ E64.P2 P z := by
  have := c.z_conj_mem_P2 pd.alpha_mem
  rwa [c.z_conj_alpha] at this

theorem P_inf_P2 {p : G} (h1 : p ∈ P) (h2 : p ∈ E64.P2 P z) : p = 1 := by
  have hZ : p ∈ c.Zs := c.mem_Zs_of_W1_W2 (pd.le h1) (c.P2_le_W2 pd h2)
  rcases c.mem_Zs.1 hZ with h | h | h | h
  · exact h
  · rw [h] at h1
    exact absurd h1 (c.t_not_mem_P pd)
  · have h2' := E64.mem_P2.1 h2
    rw [h, c.z_conj_alpha] at h2'
    exact absurd h2' (c.alpha_t_not_mem_P pd)
  · rw [h] at h1
    exact absurd h1 (c.alpha_t_not_mem_P pd)

theorem P_le_Qs : P ≤ c.Qs := pd.le.trans c.W1_le_Qs

theorem P2_le_Qs : E64.P2 P z ≤ c.Qs := (c.P2_le_W2 pd).trans c.W2_le_Qs

theorem Qs_decomp {q : G} (hq : q ∈ c.Qs) : ∃ p₁ ∈ P, ∃ p₂ ∈ E64.P2 P z, q = p₁ * p₂ := by
  obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := c.Qs_eq hq
  obtain ⟨p, hp, hpθ⟩ := pd.surj _ (c.theta_mem hw₁)
  have hw1 : w₁ = p ∨ w₁ = p * t := (c.theta_eq_iff' (pd.le hp) hw₁).1 hpθ
  have hw₂' := c.z_conj_W2 hw₂
  obtain ⟨p', hp', hpθ'⟩ := pd.surj _ (c.theta_mem hw₂')
  have hw2 : z * w₂ * z⁻¹ = p' ∨ z * w₂ * z⁻¹ = p' * t :=
    (c.theta_eq_iff' (pd.le hp') hw₂').1 hpθ'
  have hp'' : z * p' * z⁻¹ ∈ E64.P2 P z := c.z_conj_mem_P2 hp'
  have hw2' : w₂ = z * p' * z⁻¹ ∨ w₂ = (z * p' * z⁻¹) * t := by
    have hw₂e : w₂ = z * (z * w₂ * z⁻¹) * z⁻¹ := (c.z_conj_conj w₂).symm
    rcases hw2 with h | h
    · left
      rw [hw₂e, h]
    · right
      rw [hw₂e, h]
      calc z * (p' * t) * z⁻¹ = (z * p' * z⁻¹) * (z * t * z⁻¹) := by group
        _ = (z * p' * z⁻¹) * t := by rw [c.z_conj_t]
  generalize z * p' * z⁻¹ = p'' at hp'' hw2'
  have htα : t = α * (α * t) := by
    calc t = (α * α) * t := by rw [c.hα.sq, one_mul]
      _ = α * (α * t) := by group
  have hαc : α * p'' = p'' * α := c.P_comm_P2 pd pd.alpha_mem hp''
  have htc : t * p'' = p'' * t := c.t_comm_Qs (c.P2_le_Qs pd hp'')
  have hmain : ∀ p₀ ∈ P, p₀ * (p'' * t) = (p₀ * α) * (p'' * (α * t)) := by
    intro p₀ _
    calc p₀ * (p'' * t) = p₀ * (p'' * (α * (α * t))) := by rw [← htα]
      _ = p₀ * ((p'' * α) * (α * t)) := by group
      _ = p₀ * ((α * p'') * (α * t)) := by rw [hαc]
      _ = (p₀ * α) * (p'' * (α * t)) := by group
  rcases hw1 with h1 | h1 <;> rcases hw2' with h2 | h2
  · exact ⟨p, hp, p'', hp'', by rw [h1, h2]⟩
  · refine ⟨p * α, mul_mem hp pd.alpha_mem, p'' * (α * t), mul_mem hp'' (c.alpha_t_mem_P2 pd),
      ?_⟩
    rw [h1, h2]
    exact hmain p hp
  · refine ⟨p * α, mul_mem hp pd.alpha_mem, p'' * (α * t), mul_mem hp'' (c.alpha_t_mem_P2 pd),
      ?_⟩
    rw [h1, h2]
    calc p * t * p'' = p * (t * p'') := by group
      _ = p * (p'' * t) := by rw [htc]
      _ = (p * α) * (p'' * (α * t)) := hmain p hp
  · refine ⟨p, hp, p'', hp'', ?_⟩
    rw [h1, h2]
    calc p * t * (p'' * t) = p * (t * p'') * t := by group
      _ = p * (p'' * t) * t := by rw [htc]
      _ = p * p'' * (t * t) := by group
      _ = p * p'' := by rw [c.h.t_sq, mul_one]

omit pd in
theorem P2_conj {b₁ b₂ : G} (k : IsKlein B b₁ b₂)
    (hinv : ∀ b ∈ closure ({b₁, b₂} : Set G), ∀ p ∈ P, b * p * b⁻¹ ∈ P)
    {b : G} (hbg : b ∈ closure ({b₁, b₂} : Set G)) {p : G} (hp : p ∈ E64.P2 P z) :
    b * p * b⁻¹ ∈ E64.P2 P z := by
  have hbz : b * z = z * b := c.B_comm_z (k.grp_le hbg)
  rw [E64.mem_P2] at hp ⊢
  have e : z * (b * p * b⁻¹) * z⁻¹ = b * (z * p * z⁻¹) * b⁻¹ := by
    calc z * (b * p * b⁻¹) * z⁻¹ = (z * b) * p * (z * b)⁻¹ := by group
      _ = (b * z) * p * (b * z)⁻¹ := by rw [hbz]
      _ = b * (z * p * z⁻¹) * b⁻¹ := by group
  rw [e]
  exact hinv b hbg _ hp

theorem lift_P {b₁ b₂ : G} (k : IsKlein B b₁ b₂) (kE : c.KleinE b₁ b₂)
    (hinv : ∀ b ∈ closure ({b₁, b₂} : Set G), ∀ p ∈ P, b * p * b⁻¹ ∈ P)
    {b : G} (hb : b = b₁ ∨ b = b₂ ∨ b = b₁ * b₂) {p : G} (hp : p ∈ P)
    (hpp : p * (b * p * b⁻¹) = 1) : ∃ g ∈ P, p = g * b * g⁻¹ * b⁻¹ := by
  have hbg : b ∈ closure ({b₁, b₂} : Set G) := E64.mem_grp_of hb
  have hbB : b ∈ B := k.grp_le hbg
  have hbpP : b * p * b⁻¹ ∈ P := hinv b hbg p hp
  have hθ := c.theta_mem (pd.le hp)
  have hee : (p * (z * p * z⁻¹)) * (b * (p * (z * p * z⁻¹)) * b⁻¹) = 1 := by
    calc (p * (z * p * z⁻¹)) * (b * (p * (z * p * z⁻¹)) * b⁻¹)
        = (p * (z * p * z⁻¹)) * ((b * p * b⁻¹) * (z * (b * p * b⁻¹) * z⁻¹)) := by
          rw [c.theta_conj_B' hbB p]
      _ = (p * (b * p * b⁻¹)) * (z * (p * (b * p * b⁻¹)) * z⁻¹) :=
          (c.theta_mul' (pd.le hp) (pd.le hbpP)).symm
      _ = 1 * (z * 1 * z⁻¹) := by rw [hpp]
      _ = 1 := by group
  obtain ⟨c', hc'E, hc'⟩ := kE.cocycle b hb _ hθ hee
  obtain ⟨g, hg, hgθ⟩ := pd.surj c' hc'E
  have hbgP : b * g * b⁻¹ ∈ P := hinv b hbg g hg
  have key : (p * (b * g * b⁻¹)) * (z * (p * (b * g * b⁻¹)) * z⁻¹) = g * (z * g * z⁻¹) := by
    rw [c.theta_mul' (pd.le hp) (pd.le hbgP), c.theta_conj_B' hbB g, hgθ]
    exact hc'
  have h := pd.inj _ (mul_mem hp hbgP) g hg key
  refine ⟨g, hg, ?_⟩
  calc p = (p * (b * g * b⁻¹)) * (b * g * b⁻¹)⁻¹ := by group
    _ = g * (b * g * b⁻¹)⁻¹ := by rw [h]
    _ = g * b * g⁻¹ * b⁻¹ := by group

theorem lift_P2 {b₁ b₂ : G} (k : IsKlein B b₁ b₂) (kE : c.KleinE b₁ b₂)
    (hinv : ∀ b ∈ closure ({b₁, b₂} : Set G), ∀ p ∈ P, b * p * b⁻¹ ∈ P)
    {b : G} (hb : b = b₁ ∨ b = b₂ ∨ b = b₁ * b₂) {p : G} (hp : p ∈ E64.P2 P z)
    (hpp : p * (b * p * b⁻¹) = 1) : ∃ g ∈ E64.P2 P z, p = g * b * g⁻¹ * b⁻¹ := by
  have hbB : b ∈ B := k.grp_le (E64.mem_grp_of hb)
  have hbz : b * z = z * b := c.B_comm_z hbB
  have hzb : z * b * z⁻¹ = b := by rw [← hbz]; group
  have hp' : z * p * z⁻¹ ∈ P := hp
  have hpp' : (z * p * z⁻¹) * (b * (z * p * z⁻¹) * b⁻¹) = 1 := by
    have e : b * (z * p * z⁻¹) * b⁻¹ = z * (b * p * b⁻¹) * z⁻¹ := by
      calc b * (z * p * z⁻¹) * b⁻¹ = (b * z) * p * (b * z)⁻¹ := by group
        _ = (z * b) * p * (z * b)⁻¹ := by rw [hbz]
        _ = z * (b * p * b⁻¹) * z⁻¹ := by group
    calc (z * p * z⁻¹) * (b * (z * p * z⁻¹) * b⁻¹)
        = (z * p * z⁻¹) * (z * (b * p * b⁻¹) * z⁻¹) := by rw [e]
      _ = z * (p * (b * p * b⁻¹)) * z⁻¹ := by group
      _ = 1 := by rw [hpp]; group
  obtain ⟨g', hg', hg'eq⟩ := c.lift_P pd k kE hinv hb hp' hpp'
  refine ⟨z * g' * z⁻¹, c.z_conj_mem_P2 hg', ?_⟩
  calc p = z * (z * p * z⁻¹) * z⁻¹ := (c.z_conj_conj p).symm
    _ = z * (g' * b * g'⁻¹ * b⁻¹) * z⁻¹ := by rw [hg'eq]
    _ = (z * g' * z⁻¹) * (z * b * z⁻¹) * (z * g' * z⁻¹)⁻¹ * (z * b * z⁻¹)⁻¹ := by group
    _ = (z * g' * z⁻¹) * b * (z * g' * z⁻¹)⁻¹ * b⁻¹ := by rw [hzb]

theorem exists_conj_of_inv {b₁ b₂ : G} (k : IsKlein B b₁ b₂) (kE : c.KleinE b₁ b₂)
    (hinv : ∀ b ∈ closure ({b₁, b₂} : Set G), ∀ p ∈ P, b * p * b⁻¹ ∈ P)
    {b : G} (hb : b = b₁ ∨ b = b₂ ∨ b = b₁ * b₂) {q : G} (hq : q ∈ c.Qs)
    (hx : (q * b) * (q * b) = 1) : ∃ g ∈ c.Qs, q * b = g * b * g⁻¹ := by
  have hbg : b ∈ closure ({b₁, b₂} : Set G) := E64.mem_grp_of hb
  have hbb : b * b = 1 := k.sq_grp hbg
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hbb
  obtain ⟨p₁, hp₁, p₂, hp₂, rfl⟩ := c.Qs_decomp pd hq
  have hu₁ : b * p₁ * b⁻¹ ∈ P := hinv b hbg p₁ hp₁
  have hu₂ : b * p₂ * b⁻¹ ∈ E64.P2 P z := c.P2_conj k hinv hbg hp₂
  have h1 : (p₁ * p₂) * (b * (p₁ * p₂) * b⁻¹) = 1 := by
    calc (p₁ * p₂) * (b * (p₁ * p₂) * b⁻¹)
        = ((p₁ * p₂) * b) * ((p₁ * p₂) * b) * (b⁻¹ * b⁻¹) := by group
      _ = 1 := by rw [hx, one_mul, hbi, hbb]
  have hc : p₂ * (b * p₁ * b⁻¹) = (b * p₁ * b⁻¹) * p₂ := (c.P_comm_P2 pd hu₁ hp₂).symm
  have h2 : (p₁ * (b * p₁ * b⁻¹)) * (p₂ * (b * p₂ * b⁻¹)) = 1 := by
    calc (p₁ * (b * p₁ * b⁻¹)) * (p₂ * (b * p₂ * b⁻¹))
        = p₁ * ((b * p₁ * b⁻¹) * p₂) * (b * p₂ * b⁻¹) := by group
      _ = p₁ * (p₂ * (b * p₁ * b⁻¹)) * (b * p₂ * b⁻¹) := by rw [hc]
      _ = (p₁ * p₂) * ((b * p₁ * b⁻¹) * (b * p₂ * b⁻¹)) := by group
      _ = (p₁ * p₂) * (b * (p₁ * p₂) * b⁻¹) := by group
      _ = 1 := h1
  have h3 : p₁ * (b * p₁ * b⁻¹) = 1 := by
    have hinvmem : (p₂ * (b * p₂ * b⁻¹))⁻¹ ∈ E64.P2 P z := inv_mem (mul_mem hp₂ hu₂)
    have h5 : p₁ * (b * p₁ * b⁻¹) = (p₂ * (b * p₂ * b⁻¹))⁻¹ := eq_inv_of_mul_eq_one_left h2
    exact c.P_inf_P2 pd (mul_mem hp₁ hu₁) (h5 ▸ hinvmem)
  have h4 : p₂ * (b * p₂ * b⁻¹) = 1 := by
    rw [h3, one_mul] at h2
    exact h2
  obtain ⟨g₁, hg₁, hp₁eq⟩ := c.lift_P pd k kE hinv hb hp₁ h3
  obtain ⟨g₂, hg₂, hp₂eq⟩ := c.lift_P2 pd k kE hinv hb hp₂ h4
  refine ⟨g₁ * g₂, mul_mem (c.P_le_Qs pd hg₁) (c.P2_le_Qs pd hg₂), ?_⟩
  have e1 : g₁ * b * g₁⁻¹ = p₁ * b := by rw [hp₁eq]; group
  have e2 : g₂ * b * g₂⁻¹ = p₂ * b := by rw [hp₂eq]; group
  have hg₁p₂ : g₁ * p₂ = p₂ * g₁ := c.P_comm_P2 pd hg₁ hp₂
  have hp₁p₂ : p₁ * p₂ = p₂ * p₁ := c.P_comm_P2 pd hp₁ hp₂
  calc p₁ * p₂ * b = p₂ * p₁ * b := by rw [hp₁p₂]
    _ = p₂ * (p₁ * b) := by group
    _ = p₂ * (g₁ * b * g₁⁻¹) := by rw [e1]
    _ = (p₂ * g₁) * b * g₁⁻¹ := by group
    _ = (g₁ * p₂) * b * g₁⁻¹ := by rw [hg₁p₂]
    _ = g₁ * (p₂ * b) * g₁⁻¹ := by group
    _ = g₁ * (g₂ * b * g₂⁻¹) * g₁⁻¹ := by rw [e2]
    _ = g₁ * g₂ * b * (g₁ * g₂)⁻¹ := by group

end I13Ctx

end CFSG.EvenSporadicStandard.Fin76b
