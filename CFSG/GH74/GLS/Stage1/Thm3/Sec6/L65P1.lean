module

public import CFSG.GH74.GLS.IVK.Lifted.PNormalFour
public import CFSG.GH74.KGroups.TwoA7Cover

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6.L65

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm2.Recip

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G}

theorem exists_order_eight {S K : Subgroup G}
    (hP : M.Syl2In (S ⊓ K) K) (hK : IsDoubleCoverOfAlt (Hat K) 7) :
    ∃ a ∈ S ⊓ K, orderOf a = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨π, z₀, hcov, -⟩ := CFSG.GH74.KGroups.TwoA7.exists_cover hK
  have hSyl := isSylow2In_hatImg (K := K) (S := S ⊓ K) hP
  let P : Sylow 2 (Hat K) := hSyl.2.1.toSylow (by simpa [Subgroup.relIndex_top_right] using hSyl.2.2)
  have hPeq : (P : Subgroup (Hat K)) = hatImg K (S ⊓ K) := rfl
  obtain ⟨e⟩ := CFSG.GH74.KGroups.TwoA7.sylow_quaternion hcov P
  set x₀ : ↥(P : Subgroup (Hat K)) := e.symm (QuaternionGroup.a 1) with hx₀
  have hx₀o : orderOf x₀ = 8 := by
    rw [hx₀, MulEquiv.orderOf_eq, QuaternionGroup.orderOf_a_one]
  have hxo : orderOf ((x₀ : ↥(P : Subgroup (Hat K))) : Hat K) = 8 := by
    rw [Subgroup.orderOf_coe]; exact hx₀o
  have hxmem : ((x₀ : ↥(P : Subgroup (Hat K))) : Hat K) ∈ hatImg K (S ⊓ K) := by
    rw [← hPeq]; exact x₀.2
  obtain ⟨a, haS, ha⟩ := mem_hatImg.mp hxmem
  have haPK : (a : G) ∈ S ⊓ K := haS
  refine ⟨(a : G), haPK, ?_⟩
  have hSK : S ⊓ K ≤ K := inf_le_right
  have h2 := orderOf_hatMk (K := K) (S := S ⊓ K) hSK hP.2.1 (a := (a : G)) haPK
  have h3 : hatMk K ⟨(a : G), hSK haPK⟩ = ((x₀ : ↥(P : Subgroup (Hat K))) : Hat K) := ha
  rw [h3, hxo] at h2
  exact h2.symm

namespace M4facts

theorem inf_comps_le_zpowers {O : Subgroup G → Subgroup G} {FA : G → Subgroup G → Prop}
    {SD : Subgroup G → Prop} (h : M.M4 O FA SD z S K₁ K₂) {x : G} (hxS : x ∈ S) (hx₁ : x ∈ K₁)
    (hx₂ : x ∈ K₂) : x ∈ zpowers z := by
  have hZ : x ∈ M.ZsM O K₁ := ⟨hx₁, h.cs₁ hx₂⟩
  have : x ∈ S ⊓ M.ZsM O K₁ := ⟨hxS, hZ⟩
  rwa [(h.S_inf_Zs_comp (Or.inl rfl)).2] at this

end M4facts

theorem pow_four_eq_z_of_order_eight (h : Std4 G z S K₁ K₂) (hII : II4_4_4_center) {a : G} (ha : a ∈ K₁)
    (ha8 : orderOf a = 8) : a ^ 4 = z := by
  have hM := m4_of_std hII h
  have h44 : a ^ 4 * a ^ 4 = 1 := by
    rw [← pow_add, show 4 + 4 = 8 from rfl, ← ha8, pow_orderOf_eq_one]
  have h4K : a ^ 4 ∈ K₁ := pow_mem ha 4
  rcases hM.inv_comp (Or.inl rfl) h4K h44 with h1 | h1
  · exfalso
    have := orderOf_dvd_of_pow_eq_one h1
    rw [ha8] at this
    omega
  · exact h1

theorem exists_u (h : Std4 G z S K₁ K₂) (hII : II4_4_4_center) (hq : II4_4_quat) {a : G} (haK : a ∈ K₁)
    (haS : a ∈ S) (ha8 : orderOf a = 8) :
    ∃ u : G, u ∈ S ∧ u ∈ K₁ ⊔ K₂ ∧ u * u = 1 ∧ u ≠ 1 ∧ u ≠ z ∧ a * u = u * a := by
  classical
  have hM := m4_of_std hII h
  have hz4 : a ^ 4 = z := pow_four_eq_z_of_order_eight h hII haK ha8
  have hPq : ∃ n, IVK.IsQuaternionTwoGroup ↥(S ⊓ K₂) n :=
    hq G h.simple z h.orderOf_z S K₂ h.sylow (h.comp_isPCompIn (Or.inr rfl)) (h.comp_pRank (Or.inr rfl))
  obtain ⟨u₂, hu₂, hu₂sq⟩ := IVK.Lifted.exists_sq_eq_z_of_quat hPq
    (fun x hx hx2 => hM.inv_comp (Or.inr rfl) hx hx2)
  have hz2 : z * z = 1 := hM.z_sq
  have hcomm : ∀ x ∈ K₁, x ∈ S → u₂ * x = x * u₂ := fun x hx hxS =>
    (hM.comm_of_S hx hu₂.2 hxS hu₂.1).symm
  have ha2K : a ^ 2 ∈ K₁ := pow_mem haK 2
  have ha2S : a ^ 2 ∈ S := pow_mem haS 2
  have hcomm2 : a ^ 2 * u₂ = u₂ * a ^ 2 := (hcomm _ ha2K ha2S).symm
  refine ⟨a ^ 2 * u₂, S.mul_mem ha2S hu₂.1, mul_mem (mem_sup_left ha2K) (mem_sup_right hu₂.2), ?_, ?_, ?_, ?_⟩
  · have e : a ^ 2 * u₂ * (a ^ 2 * u₂) = a ^ 2 * a ^ 2 * (u₂ * u₂) := by
      calc a ^ 2 * u₂ * (a ^ 2 * u₂) = a ^ 2 * (u₂ * a ^ 2) * u₂ := by group
        _ = a ^ 2 * (a ^ 2 * u₂) * u₂ := by rw [hcomm2]
        _ = a ^ 2 * a ^ 2 * (u₂ * u₂) := by group
    rw [e, hu₂sq, ← pow_add, show 2 + 2 = 4 from rfl, hz4, hz2]
  · intro h1
    have hu₂eq : u₂ = (a ^ 2)⁻¹ := eq_inv_of_mul_eq_one_right h1
    have hu₂K₁ : u₂ ∈ K₁ := by rw [hu₂eq]; exact inv_mem ha2K
    have hzz := M4facts.inf_comps_le_zpowers hM hu₂.1 hu₂K₁ hu₂.2
    rcases (M.mem_zpowers_of_sq hz2).1 hzz with h1' | h1'
    · rw [h1', one_mul] at hu₂sq
      exact hM.z_ne hu₂sq.symm
    · rw [h1', hz2] at hu₂sq
      exact hM.z_ne hu₂sq.symm
  · intro h1
    have hu₂eq : u₂ = (a ^ 2)⁻¹ * z := by
      calc u₂ = (a ^ 2)⁻¹ * (a ^ 2 * u₂) := by group
        _ = (a ^ 2)⁻¹ * z := by rw [h1]
    have hzK₁ : z ∈ K₁ := hM.z_mem_comp (Or.inl rfl)
    have hu₂K₁ : u₂ ∈ K₁ := by rw [hu₂eq]; exact mul_mem (inv_mem ha2K) hzK₁
    have hzz := M4facts.inf_comps_le_zpowers hM hu₂.1 hu₂K₁ hu₂.2
    rcases (M.mem_zpowers_of_sq hz2).1 hzz with h1' | h1'
    · rw [h1', one_mul] at hu₂sq
      exact hM.z_ne hu₂sq.symm
    · rw [h1', hz2] at hu₂sq
      exact hM.z_ne hu₂sq.symm
  · calc a * (a ^ 2 * u₂) = a ^ 2 * (a * u₂) := by group
      _ = a ^ 2 * (u₂ * a) := by rw [(hcomm a haK haS).symm]
      _ = a ^ 2 * u₂ * a := by group

end CFSG.GH74.GLS.Stage1.Thm3.Sec6.L65
