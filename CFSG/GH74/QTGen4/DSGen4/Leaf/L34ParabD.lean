module

public import CFSG.GH74.QTGen4.DSGen4.Leaf.L34ParabB
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherFieldFourFixed
public import CFSG.Quasithin.Vol2.GoldschmidtF431SpBorel
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2BorelL3

public section

namespace CFSG.GH74.QTGen4.DSGen4.L34

open CFSG.Quasithin.H13.F431.L3.P3
open CFSG.QuasithinUnique.Fin257.L3
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped Pointwise

theorem card_projUnitriangular_four {F : Type} [Field F] [Finite F] (hq : Nat.card F = 4) :
    Nat.card (projUnitriangular 3 F) = 64 := by
  rw [card_projUnitriangular_three hq]
  norm_num

theorem card_sup_eq_mul_of_le_normalizer {G : Type} [Group G] (H K : Subgroup G)
    (hK : K ≤ Subgroup.normalizer (H : Set G)) (hHK : H ⊓ K = ⊥) :
    Nat.card ↥(H ⊔ K) = Nat.card ↥H * Nat.card ↥K := by
  have hset := Subgroup.coe_mul_of_right_le_normalizer_left H K hK
  let f : ↥H × ↥K → ↥(H ⊔ K) := fun p =>
    ⟨(p.1 : G) * (p.2 : G), Subgroup.mul_mem_sup p.1.2 p.2.2⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨⟨h1, hh1⟩, ⟨k1, hk1⟩⟩ ⟨⟨h2, hh2⟩, ⟨k2, hk2⟩⟩ hfe
      have e1 : h1 * k1 = h2 * k2 := congrArg Subtype.val hfe
      have e2 : h2⁻¹ * h1 = k2 * k1⁻¹ := by
        calc h2⁻¹ * h1 = h2⁻¹ * (h1 * k1) * k1⁻¹ := by group
          _ = h2⁻¹ * (h2 * k2) * k1⁻¹ := by rw [e1]
          _ = k2 * k1⁻¹ := by group
      have h3 : h2⁻¹ * h1 ∈ H ⊓ K :=
        ⟨H.mul_mem (H.inv_mem hh2) hh1, e2 ▸ K.mul_mem hk2 (K.inv_mem hk1)⟩
      rw [hHK, Subgroup.mem_bot] at h3
      have hh : h2 = h1 := inv_mul_eq_one.mp h3
      subst hh
      have hk : k1 = k2 := mul_left_cancel e1
      subst hk
      rfl
    · rintro ⟨x, hx⟩
      have hx' : x ∈ (H : Set G) * (K : Set G) := by
        rw [← hset]
        exact hx
      obtain ⟨h, hh, k, hk, rfl⟩ := Set.mem_mul.mp hx'
      exact ⟨(⟨h, hh⟩, ⟨k, hk⟩), rfl⟩
  rw [← Nat.card_prod]
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm

theorem card_normalizer_U {F : Type} [Field F] [Finite F] [CharP F 2] (hq : Nat.card F = 4) :
    Nat.card ↥(Subgroup.normalizer ((projUnitriangular 3 F : Subgroup (projectiveSL 3 F)) :
      Set (projectiveSL 3 F))) = 192 := by
  have hsup := card_sup_eq_mul_of_le_normalizer (projUnitriangular 3 F) (torus3 F)
    torus3_le_normalizer projUnitriangular_inf_torus3
  rw [normalizer_U_eq_sup_torus3, hsup, card_projUnitriangular_four hq, card_torus3 hq]

theorem normalizer_U_eq_inf_V {F : Type} [Field F] [Finite F] [CharP F 2] :
    Subgroup.normalizer ((projUnitriangular 3 F : Subgroup (projectiveSL 3 F)) :
        Set (projectiveSL 3 F)) =
      Subgroup.normalizer ((CFSG.QuasithinUnique.Fin257.L3.V2 : Subgroup (projectiveSL 3 F)) :
        Set (projectiveSL 3 F)) ⊓
      Subgroup.normalizer ((CFSG.QuasithinUnique.Fin257.L3.V1 : Subgroup (projectiveSL 3 F)) :
        Set (projectiveSL 3 F)) := by
  rw [inf_comm]
  exact (CFSG.QuasithinUnique.Borel252.BorelData.inf_norm
    CFSG.QuasithinUnique.Borel252.L3.borelData_L3).symm

theorem card_normalizer_inf_V {F : Type} [Field F] [Finite F] [CharP F 2] (hq : Nat.card F = 4) :
    Nat.card ↥(Subgroup.normalizer ((CFSG.QuasithinUnique.Fin257.L3.V2 :
        Subgroup (projectiveSL 3 F)) : Set (projectiveSL 3 F)) ⊓
      Subgroup.normalizer ((CFSG.QuasithinUnique.Fin257.L3.V1 :
        Subgroup (projectiveSL 3 F)) : Set (projectiveSL 3 F))) = 192 := by
  rw [← normalizer_U_eq_inf_V]
  exact card_normalizer_U hq

end CFSG.GH74.QTGen4.DSGen4.L34

end
