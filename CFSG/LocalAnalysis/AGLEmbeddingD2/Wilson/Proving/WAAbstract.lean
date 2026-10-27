module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Proving.CardInfBound

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Proving

open Subgroup

theorem wa_abstract {G H : Type*} [Group G] [Group H] [Finite G]
    (M : Subgroup G) (ρ : M →* H) (Kg Qg C : Subgroup G) (K3 Q8 : Set G)
    (hKg : ∀ g (hg : g ∈ M), g ∈ Kg ↔ ρ ⟨g, hg⟩ = 1) (hKgM : Kg ≤ M) (hQK : Qg ≤ Kg)
    (hidx : Qg.relIndex Kg = 3) (hCM : C ≤ M)
    (hQ8 : Q8 ⊆ ↑(C ⊓ Qg)) (hQ8c : Q8.ncard = 8) (hK3 : K3 ⊆ ↑(C ⊓ Kg)) (hK3c : K3.ncard = 24)
    (r : Fin 7 → G) (hwit : ∀ p ∈ Qg, p ∉ Q8 → ∃ i, ∃ w ∈ C, ∃ q ∈ Q8, w * p * w⁻¹ = r i * q)
    (m : G) (hmM : m ∈ M)
    (h77 : ∀ L : Subgroup H, (C.subgroupOf M).map ρ ≤ L → L ≤ ρ.range →
      ¬ L ≤ (C.subgroupOf M).map ρ → ρ ⟨m, hmM⟩ ∈ L)
    (hmK3 : ∀ x ∈ K3, m * x * m⁻¹ ∈ K3)
    (hnorm : ∀ k ∈ Kg, (∀ x ∈ K3, k * x * k⁻¹ ∈ K3) → k ∈ K3)
    (T : Subgroup G) (hCT : C ≤ T) (hTM : T ≤ M) (hTC : ¬ T ≤ C) :
    (∃ i, r i ∈ T) ∨ m ∈ T := by
  classical
  by_cases hout : ∃ p ∈ T ⊓ Qg, p ∉ Q8
  · obtain ⟨p, hpT, hpQ⟩ := hout
    obtain ⟨i, w, hw, q, hq, hwp⟩ := hwit p (Subgroup.mem_inf.1 hpT).2 hpQ
    have hqCK : q ∈ C ⊓ Qg := hQ8 hq
    have hqT : q ∈ T := hCT (Subgroup.mem_inf.1 hqCK).1
    have hpT' : p ∈ T := (Subgroup.mem_inf.1 hpT).1
    have hr : r i = w * p * w⁻¹ * q⁻¹ := by rw [hwp, mul_inv_cancel_right]
    left
    refine ⟨i, ?_⟩
    rw [hr]
    exact T.mul_mem (T.mul_mem (T.mul_mem (hCT hw) hpT') (T.inv_mem (hCT hw))) (T.inv_mem hqT)
  push Not at hout
  have hnat : ∀ S : Subgroup G, Nat.card S = (S : Set G).ncard :=
    fun S => (Nat.card_coe_set_eq (S : Set G)).symm
  have hTQ : (↑(T ⊓ Qg) : Set G) ⊆ Q8 := fun p hp => hout p (show p ∈ T ⊓ Qg from hp)
  have hcardQ : Nat.card (T ⊓ Qg : Subgroup G) ≤ 8 := by
    rw [hnat, ← hQ8c]
    exact Set.ncard_le_ncard hTQ
  have hcardK : Nat.card (T ⊓ Kg : Subgroup G) ≤ 24 := by
    have h := card_inf_le_relIndex_mul T Qg Kg hQK
    rw [hidx] at h
    omega
  have hK3sub : K3 ⊆ ↑(T ⊓ Kg) := by
    intro x hx
    have hxCK : x ∈ C ⊓ Kg := hK3 hx
    exact Subgroup.mem_inf.2 ⟨hCT (Subgroup.mem_inf.1 hxCK).1, (Subgroup.mem_inf.1 hxCK).2⟩
  have hKeq : K3 = ↑(T ⊓ Kg) := by
    apply Set.eq_of_subset_of_ncard_le hK3sub
    rw [hK3c, ← hnat]
    exact hcardK
  have hK3T : ∀ x ∈ K3, x ∈ T ∧ x ∈ Kg := by
    intro x hx
    rw [hKeq] at hx
    exact Subgroup.mem_inf.1 hx
  have hTK : ∀ x, x ∈ T → x ∈ Kg → x ∈ K3 := by
    intro x h1 h2
    rw [hKeq]
    exact Subgroup.mem_inf.2 ⟨h1, h2⟩
  have hconj : ∀ g ∈ M, ∀ y ∈ Kg, g⁻¹ * y * g ∈ Kg := by
    intro g hg y hy
    have hyM : y ∈ M := hKgM hy
    have hy1 : ρ ⟨y, hyM⟩ = 1 := (hKg y hyM).1 hy
    have hgM : g⁻¹ * y * g ∈ M := M.mul_mem (M.mul_mem (M.inv_mem hg) hyM) hg
    refine (hKg _ hgM).2 ?_
    have e : (⟨g⁻¹ * y * g, hgM⟩ : M) = ⟨g, hg⟩⁻¹ * ⟨y, hyM⟩ * ⟨g, hg⟩ := rfl
    rw [e, map_mul, map_mul, map_inv, hy1, mul_one, inv_mul_cancel]
  by_cases hL : (T.subgroupOf M).map ρ ≤ (C.subgroupOf M).map ρ
  ·
    exfalso
    apply hTC
    intro t ht
    have htM : t ∈ M := hTM ht
    have hx : (⟨t, htM⟩ : M) ∈ T.subgroupOf M := Subgroup.mem_subgroupOf.2 ht
    obtain ⟨c', hc', hceq⟩ := Subgroup.mem_map.1 (hL (Subgroup.mem_map_of_mem ρ hx))
    have hcC : (c' : G) ∈ C := Subgroup.mem_subgroupOf.1 hc'
    have hkM : (c' : G)⁻¹ * t ∈ M := M.mul_mem (M.inv_mem c'.2) htM
    have hkK : (c' : G)⁻¹ * t ∈ Kg := by
      refine (hKg _ hkM).2 ?_
      have e : (⟨(c' : G)⁻¹ * t, hkM⟩ : M) = c'⁻¹ * ⟨t, htM⟩ := rfl
      rw [e, map_mul, map_inv, hceq, inv_mul_cancel]
    have hkT : (c' : G)⁻¹ * t ∈ T := T.mul_mem (T.inv_mem (hCT hcC)) ht
    have hkK3 : (c' : G)⁻¹ * t ∈ K3 := hTK _ hkT hkK
    have hkCK : (c' : G)⁻¹ * t ∈ C ⊓ Kg := hK3 hkK3
    have hkC : (c' : G)⁻¹ * t ∈ C := (Subgroup.mem_inf.1 hkCK).1
    have := C.mul_mem hcC hkC
    rwa [mul_inv_cancel_left] at this
  ·
    right
    have hCL : (C.subgroupOf M).map ρ ≤ (T.subgroupOf M).map ρ :=
      Subgroup.map_mono (fun x hx => Subgroup.mem_subgroupOf.2 (hCT (Subgroup.mem_subgroupOf.1 hx)))
    have hrange : (T.subgroupOf M).map ρ ≤ ρ.range := by
      rintro _ ⟨y, _, rfl⟩
      exact ⟨y, rfl⟩
    obtain ⟨t', ht', heq⟩ := Subgroup.mem_map.1 (h77 _ hCL hrange hL)
    have htT : (t' : G) ∈ T := Subgroup.mem_subgroupOf.1 ht'
    have hkM : (t' : G)⁻¹ * m ∈ M := M.mul_mem (M.inv_mem t'.2) hmM
    have hkK : (t' : G)⁻¹ * m ∈ Kg := by
      refine (hKg _ hkM).2 ?_
      have e : (⟨(t' : G)⁻¹ * m, hkM⟩ : M) = t'⁻¹ * ⟨m, hmM⟩ := rfl
      rw [e, map_mul, map_inv, heq, inv_mul_cancel]
    have hnormK : ∀ x ∈ K3, (t' : G)⁻¹ * m * x * ((t' : G)⁻¹ * m)⁻¹ ∈ K3 := by
      intro x hx
      have hy := hK3T _ (hmK3 x hx)
      have hconjT : (t' : G)⁻¹ * (m * x * m⁻¹) * (t' : G) ∈ T :=
        T.mul_mem (T.mul_mem (T.inv_mem htT) (hK3T _ (hmK3 x hx)).1) htT
      have hconjK : (t' : G)⁻¹ * (m * x * m⁻¹) * (t' : G) ∈ Kg :=
        hconj (t' : G) t'.2 _ (hy.2)
      have e : (t' : G)⁻¹ * m * x * ((t' : G)⁻¹ * m)⁻¹
          = (t' : G)⁻¹ * (m * x * m⁻¹) * (t' : G) := by
        simp only [mul_inv_rev, inv_inv, mul_assoc]
      rw [e]
      exact hTK _ hconjT hconjK
    have hkK3 : (t' : G)⁻¹ * m ∈ K3 := hnorm _ hkK hnormK
    have hkT : (t' : G)⁻¹ * m ∈ T := (hK3T _ hkK3).1
    have := T.mul_mem htT hkT
    rwa [mul_inv_cancel_left] at this

end CFSG.AGLEmbeddingD2.Wilson.Proving

end
