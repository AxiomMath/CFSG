module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.U43CoverIndex
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S7Catalog
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43Tables
public import CFSG.LieType.Multipliers.U43
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.Basic

public section

namespace CFSG.EvenSporadicStandard.HSStd.U43

open Subgroup CFSG.EvenSporadicStandard.M24Std.CU43
  CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

theorem u43CoverOrbit_proved :
    U43CoverOrbit := by
  intro T X _ _ _ _ κ hκ E _ hE hZ hL hC t ht hCt y hyE hy3 hyC hcard
  have : (E.map κ).Normal := Subgroup.Normal.map ‹E.Normal› κ hκ
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨eX⟩ := CFSG.LieType.Multipliers.U43.nonempty_mulEquiv_X₀ hL
  let θ : ↥(E.map κ) ≃* P := eX.trans psiEquiv
  have h8 : (E.map κ).index ∣ 8 := card_quotient_dvd_eight (E.map κ) θ hC
  have hypow : y ^ 3 = 1 := by
    have := pow_orderOf_eq_one y
    rwa [hy3] at this
  have hykN : κ y ∈ E.map κ := ⟨y, hyE, rfl⟩
  have hne : κ y ≠ 1 := by
    intro h1
    have htop : centralizer ({κ y} : Set X) = ⊤ := by
      refine eq_top_iff.2 fun g _ => ?_
      rw [mem_centralizer_singleton_iff, h1]
      simp
    have hle : Nat.card ↥(E.map κ) ≤ Nat.card X := Subgroup.card_le_card_group _
    have hN : Nat.card ↥(E.map κ) = 3265920 := by rw [Nat.card_congr θ.toEquiv, card_P]
    have hX : Nat.card ↥(centralizer ({κ y} : Set X)) = Nat.card X := by
      rw [htop]
      exact Subgroup.card_top
    omega
  have hky3 : orderOf (κ y) = 3 := by
    refine orderOf_eq_prime ?_ hne
    rw [← map_pow, hypow, map_one]
  have hβP : emb (E.map κ) θ (κ y) ∈ P := (emb_mem_P_iff (E.map κ) θ hC).2 hykN
  have hβo : orderOf (emb (E.map κ) θ (κ y)) = 3 := by
    rw [orderOf_injective (emb (E.map κ) θ) (emb_injective (E.map κ) θ hC) (κ y), hky3]
  have hDcard : Nat.card ↥(E.map κ ⊓ centralizer ({κ y} : Set X)) = 972 := by
    have h2 := card_inf_centralizer_order_three hβP hβo
    rw [← card_inf_centralizer_emb (E.map κ) θ hC (κ y)] at h2
    have h3 := relIndex_mul_card (E.map κ) (centralizer ({κ y} : Set X))
    rw [hcard] at h3
    have hr : (E.map κ).relIndex (centralizer ({κ y} : Set X)) ∣ 8 :=
      (relIndex_dvd_index_of_normal _ _).trans h8
    rcases h2 with h | h | h
    · rw [h] at h3
      omega
    · exact h
    · rw [h] at h3
      have h24 : (E.map κ).relIndex (centralizer ({κ y} : Set X)) = 24 := by omega
      rw [h24] at hr
      exact absurd hr (by norm_num)
  have hKcard : 324 ≤ Nat.card ↥(cubeCore (E.map κ ⊓ centralizer ({κ y} : Set X)) (κ y)) := by
    have hmap : (E.map κ ⊓ centralizer ({κ y} : Set X)).map (emb (E.map κ) θ) =
        P ⊓ centralizer ({emb (E.map κ) θ (κ y)} : Set (Equiv.Perm (Fin 820))) := by
      ext p
      constructor
      · rintro ⟨x, hx, rfl⟩
        obtain ⟨hxN, hxc⟩ := mem_inf.1 hx
        refine mem_inf.2 ⟨(emb_mem_P_iff (E.map κ) θ hC).2 hxN, ?_⟩
        rw [mem_centralizer_singleton_iff] at hxc ⊢
        rw [← map_mul, ← map_mul, hxc]
      · intro hp
        obtain ⟨hpP, hpc⟩ := mem_inf.1 hp
        obtain ⟨c, hcN, rfl⟩ := exists_emb_eq (E.map κ) θ hpP
        refine ⟨c, mem_inf.2 ⟨hcN, ?_⟩, rfl⟩
        rw [mem_centralizer_singleton_iff] at hpc ⊢
        apply emb_injective (E.map κ) θ hC
        rw [map_mul, map_mul]
        exact hpc
    have hge := card_cubeCore_ge hβP hβo
      (by rw [← card_inf_centralizer_emb (E.map κ) θ hC (κ y)]; exact hDcard)
    rw [← Subgroup.card_map_of_injective (emb_injective (E.map κ) θ hC),
      map_cubeCore, hmap]
    exact hge
  have hmain := orbit_mul_card_le κ hκ E hE hZ hyE hypow
  rw [hcard] at hmain
  have h324 : {w : T | ∃ g : T, κ g ∈ centralizer ({κ y} : Set X) ∧ w = g * y * g⁻¹}.ncard * 324 ≤
      1944 := le_trans (Nat.mul_le_mul_left _ hKcard) hmain
  omega

end CFSG.EvenSporadicStandard.HSStd.U43
