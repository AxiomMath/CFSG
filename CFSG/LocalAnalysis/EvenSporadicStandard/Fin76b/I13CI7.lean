module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.I13CI2
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.I13Cl1

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

theorem V4_comm_mem {H : Type*} [Group H] [Finite H] {V : Subgroup H} (hV : Nat.card V = 4)
    {τ : H} (hτV : τ ∈ V) (hτ1 : τ ≠ 1) (hτ2 : τ * τ = 1) {r : H}
    (hrV : ∀ v ∈ V, r * v * r⁻¹ ∈ V) (hrτ : r * τ * r⁻¹ = τ) {v : H} (hv : v ∈ V) :
    r * v * r⁻¹ * v⁻¹ = 1 ∨ r * v * r⁻¹ * v⁻¹ = τ := by
  set K : Subgroup H := zpowers τ with hK
  have hKV : K ≤ V := zpowers_le.2 hτV
  have hKcard : Nat.card K = 2 := by
    rw [hK, Nat.card_zpowers]
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [pow_two]; exact hτ2) hτ1
  have hrel : K.relIndex V = 2 := by
    have h1 := Subgroup.relIndex_mul_card (H := K) (K := V)
    rw [inf_eq_left.2 hKV, hKcard, hV] at h1
    omega
  have hidx : (K.subgroupOf V).index = 2 := hrel
  have hKmem : ∀ w : H, w ∈ K ↔ w = 1 ∨ w = τ := by
    intro w
    constructor
    · exact mem_zpowers_sq_eq_one hτ2
    · rintro (h | h)
      · rw [h]; exact K.one_mem
      · rw [h]; exact mem_zpowers τ
  have hrK : ∀ w : H, w ∈ K ↔ r * w * r⁻¹ ∈ K := by
    intro w
    rw [hKmem, hKmem]
    constructor
    · rintro (h | h)
      · left; rw [h]; group
      · right; rw [h]; exact hrτ
    · rintro (h | h)
      · left
        have : w = r⁻¹ * (r * w * r⁻¹) * r := by group
        rw [this, h]; group
      · right
        have : r * w * r⁻¹ = r * τ * r⁻¹ := by rw [h, hrτ]
        exact mul_left_cancel (mul_right_cancel this)
  have hiff := (Subgroup.mul_mem_iff_of_index_two hidx
    (a := (⟨r * v * r⁻¹, hrV v hv⟩ : ↥V)) (b := (⟨v⁻¹, inv_mem hv⟩ : ↥V))).2 (by
      show (r * v * r⁻¹ ∈ K) ↔ (v⁻¹ ∈ K)
      rw [← hrK, inv_mem_iff])
  have h2 : r * v * r⁻¹ * v⁻¹ ∈ K := hiff
  exact (hKmem _).1 h2

namespace I13Ctx

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T₀ E : Subgroup G}
  {Q : Sylow 2 G} {x β : G} {B S : Subgroup G} {α : G}
  (c : I13Ctx L z t T₀ E Q x β B S α)

include c

theorem Nc_conj_Zs {g : G} (hg : g ∈ c.Nc) {a : G} (ha : a ∈ c.Zs) : g * a * g⁻¹ ∈ c.Zs := by
  have ht := c.Nc_t hg
  have hα : g * α * g⁻¹ = α ∨ g * α * g⁻¹ = α * t := by
    rcases c.Nc_perm hg with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact Or.inl h1
    · exact Or.inr h1
  rcases c.mem_Zs.1 ha with h | h | h | h
  · rw [h]; simp
  · rw [h, ht]; exact c.t_mem_Zs
  · rw [h]
    rcases hα with h1 | h1
    · rw [h1]; exact c.alpha_mem_Zs
    · rw [h1]; exact c.alpha_t_mem_Zs
  · rw [h]
    have e : g * (α * t) * g⁻¹ = (g * α * g⁻¹) * (g * t * g⁻¹) := by group
    rw [e, ht]
    rcases hα with h1 | h1
    · rw [h1]; exact c.alpha_t_mem_Zs
    · rw [h1]
      have : α * t * t = α := by rw [mul_assoc, c.h.t_sq, mul_one]
      rw [this]; exact c.alpha_mem_Zs

variable {c}

namespace IsRs

variable {Rs : Subgroup G} (hR : c.IsRs Rs)

include hR

theorem map_Zs_eq {n : G} (hn : ∀ r : G, r ∈ Rs ↔ n * r * n⁻¹ ∈ Rs) :
    c.Zs.map (MulAut.conj n).toMonoidHom = c.Zs := by
  set V : Subgroup G := c.Zs.map (MulAut.conj n).toMonoidHom with hV
  have hmemV : ∀ y : G, y ∈ V ↔ n⁻¹ * y * n ∈ c.Zs := by
    intro y
    constructor
    · rintro ⟨u, hu, rfl⟩
      have : n⁻¹ * (MulAut.conj n).toMonoidHom u * n = u := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group
      rw [this]; exact hu
    · intro h
      refine ⟨n⁻¹ * y * n, h, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group
  have hVcard : Nat.card V = 4 := by
    rw [hV, Subgroup.card_map_of_injective (MulAut.conj n).injective, c.card_Zs']
  have hZsR : c.Zs ≤ Rs := c.Zs_le_Qs.trans hR.Qs_le
  have hVR : V ≤ Rs := by
    rintro _ ⟨u, hu, rfl⟩
    exact (hn u).1 (hZsR hu)
  have hnorm : ∀ r ∈ Rs, ∀ v ∈ V, r * v * r⁻¹ ∈ V := by
    intro r hr v hv
    rw [hmemV] at hv ⊢
    have hr' : n⁻¹ * r * n ∈ Rs := (hn _).2 (by
      have : n * (n⁻¹ * r * n) * n⁻¹ = r := by group
      rw [this]; exact hr)
    have h1 := c.Nc_conj_Zs (hR.le_Nc hr') hv
    have e : n⁻¹ * (r * v * r⁻¹) * n = (n⁻¹ * r * n) * (n⁻¹ * v * n) * (n⁻¹ * r * n)⁻¹ := by
      group
    rw [e]; exact h1
  have : Group.IsNilpotent ↥Rs := IsPGroup.isNilpotent hR.pgroup
  let V' : Subgroup ↥Rs := V.subgroupOf Rs
  have : V'.Normal := ⟨fun v hv r => by
    show (r : G) * (v : G) * (r : G)⁻¹ ∈ V
    exact hnorm r r.2 v hv⟩
  have hV'ne : V' ≠ ⊥ := by
    intro hbot
    have h1 : ∀ v ∈ V, v = 1 := by
      intro v hv
      have : (⟨v, hVR hv⟩ : ↥Rs) ∈ V' := hv
      rw [hbot, Subgroup.mem_bot] at this
      exact congrArg Subtype.val this
    have : Nat.card V ≤ 1 := by
      rw [Finite.card_le_one_iff_subsingleton]
      exact ⟨fun a b => Subtype.ext ((h1 _ a.2).trans (h1 _ b.2).symm)⟩
    omega
  obtain ⟨⟨a, haV, haC⟩, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hV'ne)
  have hv₀V : (a : G) ∈ V := haV
  have hv₀C : ∀ r ∈ Rs, r * (a : G) = (a : G) * r := by
    intro r hr
    have := (Subgroup.mem_center_iff.1 haC) ⟨r, hr⟩
    exact congrArg Subtype.val this
  have hv₀1 : (a : G) ≠ 1 := by
    intro h
    exact ha1 (Subtype.ext (Subtype.ext h))
  have hv₀Zs : (a : G) ∈ c.Zs := by
    refine hR.Z2_le a.2 (fun s hs => Or.inl ?_)
    have := hv₀C s hs
    calc (a : G) * s * (a : G)⁻¹ * s⁻¹ = (s * (a : G)) * (a : G)⁻¹ * s⁻¹ := by rw [this]
      _ = 1 := by group
  have hv₀t : (a : G) = t := by
    have hzc := hv₀C z hR.z_mem
    rcases c.mem_Zs.1 hv₀Zs with h | h | h | h
    · exact absurd h hv₀1
    · exact h
    · exfalso
      rw [h] at hzc
      have h2 := c.h.z_conj_alpha c.hα
      have h3 : z * α * z⁻¹ = α := by rw [hzc]; group
      rw [h3] at h2
      have : t = 1 := by
        have h4 : α * 1 = α * t := by rw [mul_one]; exact h2
        exact (mul_left_cancel h4).symm
      exact c.h.t_ne this
    · exfalso
      rw [h] at hzc
      have e : z * (α * t) * z⁻¹ = (z * α * z⁻¹) * (z * t * z⁻¹) := by group
      rw [c.h.z_conj_alpha c.hα, c.h.z_conj_t] at e
      have h3 : z * (α * t) * z⁻¹ = α * t := by rw [hzc]; group
      rw [h3] at e
      have h5 : α * t * t = α := by rw [mul_assoc, c.h.t_sq, mul_one]
      rw [h5] at e
      have : t = 1 := by
        have h4 : α * t = α * 1 := by rw [mul_one]; exact e
        exact mul_left_cancel h4
      exact c.h.t_ne this
  have htV : t ∈ V := hv₀t ▸ hv₀V
  have hVZ : V ≤ c.Zs := by
    intro v hv
    refine hR.Z2_le (hVR hv) (fun s hs => ?_)
    have h1 := V4_comm_mem hVcard htV c.h.t_ne c.h.t_sq (r := s) (hnorm s hs)
      (c.Nc_t (hR.le_Nc hs)) hv
    have e : v * s * v⁻¹ * s⁻¹ = (s * v * s⁻¹ * v⁻¹)⁻¹ := by group
    rw [e]
    rcases h1 with h | h
    · left; rw [h]; simp
    · right; rw [h]; exact inv_eq_of_mul_eq_one_right c.h.t_sq
  exact Subgroup.eq_of_le_of_card_ge hVZ (by rw [hVcard, c.card_Zs'])

end IsRs

end I13Ctx

end CFSG.EvenSporadicStandard.Fin76b
