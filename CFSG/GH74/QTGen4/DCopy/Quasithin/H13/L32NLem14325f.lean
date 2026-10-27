module

public import CFSG.Quasithin.H13.L32NLem14325f
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem14325e

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint

namespace L14325

variable {Γ : Type*} [Group Γ] [Finite Γ]

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V V₂ : Subgroup G} {g : G} {D : HatModelU (fsuU T V)}

namespace Ctx14325

variable (C : Ctx14325 G T L V V₂ g D)
include C

theorem not_case_iii_F4 (h1332 : Stmt13_3_2_F4) (h1352 : A6.Stmt13_5_2_F4) (h1381 : Stmt13_8_1_F4)
    (h36 : A36ForSQTK) (h39 : A39ForSQTK) (hd : Module.finrank (ZMod 2) D.V = 4)
    (hiii : Case14323iii T V g D) : False := by
  have := L14332.finite_linearEquiv D
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set Hd := D.img (l32nH T V) with hHd
  have h6 : 5 ≤ Nat.card (Fin 6) := by simp

  obtain ⟨hcardH, hbig, P₀, hP₀1, hP₀p⟩ := a6_facts (Y := ↥Hd) hiii.iso
  set P := P₀.map Hd.subtype with hP
  have hPH : P ≤ Hd := Subgroup.map_le_iff_le_comap.mpr (fun x _ => x.2)
  have hP1 : P ≠ ⊥ := by
    rw [Ne, hP, Subgroup.map_eq_bot_iff_of_injective _ Hd.subtype_injective]
    exact hP₀1
  have hPp : ⁅P, P⁆ = P := by rw [hP, ← Subgroup.map_commutator, hP₀p]
  have h25 : ¬ 5 ^ 2 ∣ Nat.card Hd := fun h => by
    have := Nat.dvd_trans h hcardH
    norm_num at this

  have hfive : ∀ X : Subgroup (D.V ≃ₗ[ZMod 2] D.V), X ≤ Hd → X ≠ ⊥ → ⁅X, X⁆ = X →
      5 ∣ Nat.card X := fun X hXH hX1 hXp =>
    prime_dvd_of_perfect hX1 hXp (by norm_num) ((Subgroup.card_dvd_of_le hXH).trans hcardH)
  obtain ⟨X, hXsub, hX1, hXp, hX60⟩ := C.exists_comp_img_F4 h1332 h1352 h1381 h36 h39 hPH hP1 hPp
    (fun X hXsub hX1 hXp hmaps => by
      obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥X) 5
        (hfive X (le_of_isSubnormal hXsub) hX1 hXp)
      have hy5 : (y : D.V ≃ₗ[ZMod 2] D.V) ^ (5 ^ 1) = 1 := by
        have := pow_orderOf_eq_one (y : D.V ≃ₗ[ZMod 2] D.V)
        rwa [Subgroup.orderOf_coe, hy, ← pow_one 5] at this
      have hy1 : (y : D.V ≃ₗ[ZMod 2] D.V) ≠ 1 := fun h => by
        rw [← Subgroup.orderOf_coe, h, orderOf_one] at hy
        omega
      exact C.not_maps_of_five hd hy5 hy1 fun w hw => hmaps _ y.2 w hw)
  have h5X := hfive X (le_of_isSubnormal hXsub) hX1 hXp

  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥X) 5 h5X
  have hyH : (y : D.V ≃ₗ[ZMod 2] D.V) ∈ Hd := le_of_isSubnormal hXsub y.2
  set N := Subgroup.normalClosure ({⟨y, hyH⟩} : Set ↥Hd) with hN
  have hNX : N.map Hd.subtype ≤ X := by
    rw [Subgroup.map_le_iff_le_comap, hN, Subgroup.normalClosure, Subgroup.closure_le]
    intro c hc
    obtain ⟨b, hb, hbc⟩ := Group.mem_conjugatesOfSet_iff.mp hc
    rw [Set.mem_singleton_iff] at hb
    subst hb
    have hb5 : orderOf (⟨y, hyH⟩ : ↥Hd) = 5 := by
      rw [← Subgroup.orderOf_coe (⟨(y : D.V ≃ₗ[ZMod 2] D.V), hyH⟩ : ↥Hd)]
      exact (Subgroup.orderOf_coe y).trans hy
    have hco : orderOf c = 5 := by rw [← hbc.orderOf_eq, hb5]
    have hc5 : (c : D.V ≃ₗ[ZMod 2] D.V) ^ 5 = 1 := by
      have := pow_orderOf_eq_one c
      rw [hco] at this
      exact congrArg Subtype.val this
    exact mem_of_subnormal_of_dvd hXsub (by norm_num) h5X h25 c.2 hc5
  have hN1 : N ≠ ⊥ := by
    intro hb
    have hmem : (⟨y, hyH⟩ : ↥Hd) ∈ N := Subgroup.subset_normalClosure (Set.mem_singleton _)
    rw [hb, Subgroup.mem_bot] at hmem
    have : (y : D.V ≃ₗ[ZMod 2] D.V) = 1 := congrArg Subtype.val hmem
    rw [← Subgroup.orderOf_coe, this, orderOf_one] at hy
    omega
  have h360 := hbig N (Subgroup.normalClosure_normal) hN1
  have hle := Subgroup.card_le_of_le hNX
  rw [Subgroup.card_map_of_injective Hd.subtype_injective] at hle
  rcases hX60 with h | h
  · have := Nat.le_of_dvd (by norm_num) h
    omega
  · have := Nat.le_of_dvd (by norm_num) h
    omega

end Ctx14325

end L14325

end CFSG.Quasithin.H13
