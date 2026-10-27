module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.L2Quot
public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.L2Basic

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec13

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def S0 (S P : Subgroup G) : Subgroup G := S ⊓ normalizer (P : Set G)

theorem mem_S0 {S P : Subgroup G} {g : G} : g ∈ S0 S P ↔ g ∈ S ∧ ∀ q, q ∈ P ↔ g * q * g⁻¹ ∈ P := by
  unfold S0
  rw [mem_inf, mem_normalizer_iff]

namespace Ctx2S

variable {x : G} {T V H : Subgroup G} {f : G} {S : Subgroup G} (c : Ctx2S G x T V H f S)
include c

theorem Hs_le_S0 : H ⊔ T ≤ S0 S (Hzero H f) := by
  intro s hs
  rw [mem_S0]
  refine ⟨c.le hs, fun q => ⟨fun hq => c.hPT s hs q hq, fun hq => ?_⟩⟩
  have := c.hPT s⁻¹ ((H ⊔ T).inv_mem hs) _ hq
  have e : s⁻¹ * (s * q * s⁻¹) * s⁻¹⁻¹ = q := by group
  rwa [e] at this

theorem normIn_S0 : NormIn (Hzero H f) (S0 S (Hzero H f)) := by
  refine ⟨fun q hq => ?_, fun m hm n hn => ?_⟩
  · rw [mem_S0]
    refine ⟨c.P_le_S hq, fun q' => ⟨fun h => ?_, fun h => ?_⟩⟩
    · exact (Hzero H f).mul_mem ((Hzero H f).mul_mem hq h) ((Hzero H f).inv_mem hq)
    · have := (Hzero H f).mul_mem ((Hzero H f).mul_mem ((Hzero H f).inv_mem hq) h) hq
      have e : q⁻¹ * (q * q' * q⁻¹) * q = q' := by group
      rwa [e] at this
  · exact ((mem_S0.1 hm).2 n).1 hn

theorem S0_two : IsPGroup 2 ↥(S0 S (Hzero H f)) := c.syl.2.1.to_le inf_le_left

theorem x_mem_S0 : x ∈ S0 S (Hzero H f) := c.Hs_le_S0 (Subgroup.mem_sup_left c.c2.c3.x_mem_H)

theorem T_le_S0 : T ≤ S0 S (Hzero H f) := fun _ ht => c.Hs_le_S0 (Subgroup.mem_sup_right ht)

theorem isFree_x : IsFreeConj x (Hzero H f) x :=
  ⟨⟨1, by simp⟩, fun q hq => c.c2.c3.H0_norm_H x c.c2.c3.x_mem_H q hq⟩

theorem cenMod_S0_eq [Finite G] (h10 : IG_10_31) :
    cenMod (S0 S (Hzero H f)) (Hzero H f) x c.normIn_S0.norm = H ⊔ T := by
  ext g
  constructor
  · rintro ⟨hgS0, hg⟩
    obtain ⟨k, hk, hkg⟩ := IsFreeConj.lift c.c2 h10 c.isFree_x hg
    have hkgS : k * g ∈ S := S.mul_mem (c.P_le_S hk) (mem_S0.1 hgS0).1
    have hkgC : k * g ∈ centralizer ({x} : Set G) := by
      rw [mem_centralizer_iff]
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      rw [hw]
      calc x * (k * g) = (x * (k * g) * x⁻¹) * x := by group
        _ = (k * g) * x := by rw [hkg]
    have hkgT : k * g ∈ T := by
      rw [c.T_eq_cent]
      exact ⟨hkgS, hkgC⟩
    have : g = k⁻¹ * (k * g) := by group
    rw [this]
    exact (H ⊔ T).mul_mem ((H ⊔ T).inv_mem (Subgroup.mem_sup_left (c.c2.c3.H0_le hk)))
      (Subgroup.mem_sup_right hkgT)
  · intro hg
    refine ⟨c.Hs_le_S0 hg, ?_⟩
    obtain ⟨p, hp, t, ht, rfl⟩ := c.Hstar_decomp g hg
    have hxt : x * t * x⁻¹ = t := by
      have := c.c2.c3.T_comm_x ht
      calc x * t * x⁻¹ = (t * x) * x⁻¹ := by rw [← this]
        _ = t := by group
    have e : x * (p * t) * x⁻¹ * (p * t)⁻¹ = (x * p * x⁻¹) * p⁻¹ := by
      calc x * (p * t) * x⁻¹ * (p * t)⁻¹ = (x * p * x⁻¹) * (x * t * x⁻¹) * t⁻¹ * p⁻¹ := by group
        _ = (x * p * x⁻¹) * t * t⁻¹ * p⁻¹ := by rw [hxt]
        _ = (x * p * x⁻¹) * p⁻¹ := by group
    rw [e]
    exact (Hzero H f).mul_mem (c.c2.c3.H0_norm_H x c.c2.c3.x_mem_H p hp) ((Hzero H f).inv_mem hp)

theorem T_card_cases [Finite G] : Nat.card T = 8 ∨ Nat.card T = 16 := by
  have h8 : 8 ≤ Nat.card T := by
    have := Subgroup.card_le_of_le c.c2.c3.out.E_le_T
    rw [c.c2.c3.out.card_EV] at this
    exact this
  have h16 := c.c2.c3.out.T_card
  obtain ⟨k, hk⟩ := (c.c2.c3.out.T_sylow.2.1).exists_card_eq (p := 2)
  have : k = 3 ∨ k = 4 := by
    by_contra hne
    push Not at hne
    rcases Nat.lt_or_gt_of_ne hne.1 with h | h
    · have : 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    · have : 2 ^ 5 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
  rcases this with rfl | rfl
  · left; rw [hk]; norm_num
  · right; rw [hk]; norm_num

theorem card_Hs_le [Finite G] : Nat.card ↥(H ⊔ T) ≤ 4 * Nat.card T := by
  have h := card_mul_inf_le (N := Hzero H f) (C := T) (F := H ⊔ T) (fun s hs => by
    obtain ⟨p, hp, t, ht, e⟩ := c.Hstar_decomp s hs
    exact ⟨p, hp, t, ht, e⟩)
  have hV : Nat.card ↥(Hzero H f ⊓ T) = 4 := by
    rw [inf_comm, c.c2.T_inf_P]
    exact c.c2.c3.out.V_four.2
  rw [hV, c.c2.P_card] at h
  omega

theorem cenMod_card_le [Finite G] (h10 : IG_10_31) :
    Nat.card (cenMod (S0 S (Hzero H f)) (Hzero H f) x c.normIn_S0.norm) ≤
      4 * Nat.card (Hzero H f) := by
  rw [c.cenMod_S0_eq h10, c.c2.P_card]
  have := c.card_Hs_le
  rcases c.T_card_cases with h | h <;> omega

end Ctx2S

end CFSG.GH74.GLS.Stage1.Thm6.Sec13
