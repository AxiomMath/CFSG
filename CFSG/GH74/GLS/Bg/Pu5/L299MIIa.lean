module

public import CFSG.GH74.GLS.Bg.Pu5.L299MAbs
public import CFSG.GH74.GLS.Bg.Pu5.L299MStatements
public import CFSG.GH74.GLS.Bg.Pu5.L299Abs2
public import CFSG.GH74.GLS.Bg.Pu5.L299FC1
public import CFSG.GH74.GLS.C3.Layer1.Thm1GlueJ

public section

namespace CFSG.GH74.GLS.Bg.Pu5

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.ABGLocalTools CFSG.GH74.GLS.Bg.Iii2 CFSG.GH74.GLS.Stage1.Thm3.Sec4
  CFSG.GH74.GLS.Stage1.Thm3.Sec6 CFSG.GH74.GLS.C3.Layer1

variable {G : Type} [Group G] [Finite G] {z t : G} {S : Subgroup G}

theorem l299m_caseIIa (h44 : II4_44) (hquat : II4_4_quat) (h296 : L296) (hFour : L299FourS)
    (hC : Cfg G z t S) (hcard : Set.ncard {K : Subgroup G | IsRigidRankOneComp z K} = 1)
    {K : Subgroup G} (hK : IsRigidRankOneComp z K)
    (hIIa : ∀ q ∈ S ⊓ cSec K, q * t = t * q → q ∈ zpowers z) :
    IsCyclic ↥(S ⊓ cSec K) ∨ IsNonabelianMaximalClassTwoGroup ↥(S ⊓ cSec K) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q : Subgroup G := S ⊓ cSec K with hQ
  have hz2 : z * z = 1 := hC.z_mul_self
  have ht2 : t * t = 1 := hC.t_mul_self
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hzt : z * t = t * z := (Subgroup.mem_centralizer_singleton_iff.1 hC.tC).symm
  have hz1 : z ≠ 1 := by
    intro h
    have := hC.hz
    rw [h, orderOf_one] at this
    omega
  have hto : orderOf t = 2 := hC.t_orderOf
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hto
    omega
  have htQ : t ∉ Q := fun h => hC.t_not_mem_cSec h44 hquat h296 hK h.2
  have hQ2 : IsPGroup 2 ↥Q := hC.sylow.isPGroup.to_inf_left
  have htNQ : t ∈ normalizer (Q : Set G) :=
    mem_normalizer_of_forall_conj_mem fun x hx => Q_conj hC hcard hK hC.tS hx
  set X : Subgroup G := Q ⊔ zpowers t with hX
  have hX2 : IsPGroup 2 ↥X := isPGroup_sup_zpowers_of_normalizes hQ2 htNQ
    ⟨1, by rw [pow_one, sq]; exact ht2⟩
  have hQX : Q ≤ X := le_sup_left
  have htX : t ∈ X := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have hzQ : z ∈ Q := hC.z_mem_Q h44 hquat hK
  have hzX : z ∈ X := hQX hzQ
  have hidx : (Q.subgroupOf X).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨t, htX⟩, fun b => ?_⟩
    have hbQ : (b : G) ∈ Q → (b : G) * t ∈ Q → False := fun h1 h2 => htQ (by
      have : t = (b : G)⁻¹ * ((b : G) * t) := by group
      rw [this]
      exact mul_mem (inv_mem h1) h2)
    rcases mem_or_mul_mem_of_mem_sup ht2 htNQ b.2 with h1 | h1
    · right
      exact ⟨Subgroup.mem_subgroupOf.2 h1, fun h2 => hbQ h1 (Subgroup.mem_subgroupOf.1 h2)⟩
    · left
      refine ⟨Subgroup.mem_subgroupOf.2 h1, fun h2 => hbQ (Subgroup.mem_subgroupOf.1 h2) h1⟩
  set b0 : ↥X := ⟨t, htX⟩ with hb0
  set z0 : ↥X := ⟨z, hzX⟩ with hz0
  have hb02 : orderOf b0 = 2 := by
    rw [hb0, Subgroup.orderOf_mk]
    exact hto
  have hcent : Nat.card ↥(centralizer ({b0} : Set ↥X)) = 4 := by
    set E : Finset ↥X := {1, z0, z0 * b0, b0} with hE
    have hset : (centralizer ({b0} : Set ↥X) : Set ↥X) = ↑E := by
      ext y
      simp only [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff, hE, Finset.coe_insert,
        Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · intro hy
        have hg : (y : G) * t = t * (y : G) := congrArg Subtype.val hy
        rcases mem_or_mul_mem_of_mem_sup ht2 htNQ y.2 with h1 | h1
        · rcases eq_one_or_eq_of_mem_zpowers_sq hz2 (hIIa _ h1 hg) with h | h
          · left
            exact Subtype.ext h
          · right; left
            exact Subtype.ext h
        · have hg' : (y : G) * t * t = t * ((y : G) * t) := by
            rw [mul_assoc, ht2, mul_one, ← mul_assoc, ← hg, mul_assoc, ht2, mul_one]
          rcases eq_one_or_eq_of_mem_zpowers_sq hz2 (hIIa _ h1 hg') with h | h
          · right; right; right
            apply Subtype.ext
            have : (y : G) = t⁻¹ := eq_inv_of_mul_eq_one_left h
            rw [this, htinv]
          · right; right; left
            apply Subtype.ext
            show (y : G) = z * t
            calc (y : G) = (y : G) * t * t := by rw [mul_assoc, ht2, mul_one]
              _ = z * t := by rw [h]
      · rintro (h | h | h | h)
        · rw [h]; simp
        · rw [h]
          exact Subtype.ext hzt
        · rw [h]
          apply Subtype.ext
          show z * t * t = t * (z * t)
          rw [mul_assoc, ht2, mul_one, ← mul_assoc, ← hzt, mul_assoc, ht2, mul_one]
        · rw [h]
    have hEcard : E.card = 4 := by
      have h1 : (1 : ↥X) ≠ z0 := fun h => hz1 (congrArg Subtype.val h).symm
      have h2 : (1 : ↥X) ≠ z0 * b0 := fun h => by
        have h' : z * t = 1 := (congrArg Subtype.val h).symm
        exact hC.t_ne_z (by
          have : t = z⁻¹ := eq_inv_of_mul_eq_one_right h'
          rw [this, inv_eq_of_mul_eq_one_right hz2])
      have h3 : (1 : ↥X) ≠ b0 := fun h => ht1 (congrArg Subtype.val h).symm
      have h4 : z0 ≠ z0 * b0 := fun h => by
        have h' : z = z * t := congrArg Subtype.val h
        exact ht1 (by simpa using h'.symm)
      have h5 : z0 ≠ b0 := fun h => hC.t_ne_z (congrArg Subtype.val h).symm
      have h6 : z0 * b0 ≠ b0 := fun h => by
        have h' : z * t = t := congrArg Subtype.val h
        exact hz1 (by simpa using h')
      rw [hE, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair h6]
      · simp [h4, h5]
      · simp [h1, h2, h3]
    rw [show Nat.card ↥(centralizer ({b0} : Set ↥X)) = (centralizer ({b0} : Set ↥X) : Set ↥X).ncard from
      Nat.card_coe_set_eq _, hset, Set.ncard_coe_finset, hEcard]
  have hmax : P34.IsMaximalClassTwoGroup ↥X :=
    Thm1.isMaximalClassTwoGroup_of_card_centralizer hX2 hb02 hcent
  have e : ↥(Q.subgroupOf X) ≃* ↥Q := Subgroup.subgroupOfEquivOfLe hQX
  rcases qShape_of_index_two hmax (Q.subgroupOf X) hidx with h | ⟨h4, hnc⟩ | h
  · exact Or.inl (e.isCyclic.1 h)
  · exfalso
    refine hFour G z t S hC hcard K hK ?_ ?_
    · rw [← Nat.card_congr e.toEquiv]
      exact h4
    · exact fun hc => hnc (e.isCyclic.2 hc)
  · exact Or.inr (isNonabelianMaximalClassTwoGroup_of_mulEquiv e h)

end CFSG.GH74.GLS.Bg.Pu5
