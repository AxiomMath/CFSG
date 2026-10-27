module

public import CFSG.GH74.Uniqueness.SU.SU13TA3M
public import CFSG.GH74.Uniqueness.SU.SU13TA3Rec

public section

namespace CFSG.GH74.Uniqueness.SU.SU13.TA.L10

open Equiv Equiv.Perm Subgroup CFSG.GH74.Uniqueness.SU.SU13.TA CFSG.GH74.Uniqueness.SU.SU13
  CFSG.GH74.Uniqueness.SU.SU13.TB

variable {H : Type} [Group H] {π : H →* alternatingGroup (Fin 10)}

theorem mpart10_of_recognition [Finite H] (hR1 : Recog1) (hR2 : Recog2) (hπ : TwoCover π)
    (c : Cfg π) {z : H} (hz : z ∈ π.ker) (hz1 : z ≠ 1) : MPart10 z (c.elts hπ hz hz1) := by
  obtain ⟨O, hO3, hOmap, hOcard, hOM, hOnorm, hOt⟩ := exists_O hπ c
  have hcen : ∀ g : H, g * z = z * g := Subgroup.mem_center_iff.mp (hπ.ker_le_center hz)
  have hzz : centralizer ({z} : Set H) = ⊤ := by
    rw [eq_top_iff]
    intro g _
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hcen g)
  have hMh : centralizer ({(c.elts hπ hz hz1).s₂} : Set H) ⊓ centralizer ({z} : Set H) = M0 c := by
    rw [hzz, inf_top_eq]
    rfl
  have hOsN : (O.subgroupOf (M0 c)).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hOnorm g g.2 n hn⟩
  have hQN : ((Qh π).subgroupOf (M0 c)).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact conj_mem_Qh g.2 hn⟩
  have hOs : Nat.card (O.subgroupOf (M0 c)) = 9 := by
    rw [← hOcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOM).toEquiv
  obtain ⟨e0⟩ := nonempty_mulEquiv_Qh hπ hz hz1
  let e : QuaternionGroup 2 ≃* ↥((Qh π).subgroupOf (M0 c)) :=
    e0.trans (Subgroup.subgroupOfEquivOfLe (Qh_le_M0 hπ c)).symm
  have hQ4 : ∀ q ∈ (Qh π).subgroupOf (M0 c), q ^ 4 = 1 := fun q hq =>
    Subtype.ext (by
      rw [Subgroup.coe_pow]
      exact pow_four_of_mem_Qh hπ hz hz1 (Subgroup.mem_subgroupOf.mp hq))
  let x : ↥(M0 c) := ⟨c.s₁, s₁_mem_M0 hπ c⟩
  let y : ↥(M0 c) := ⟨c.t, t_mem_M0 hπ c⟩
  have hts : c.t * c.s₁ * c.t⁻¹ = c.s₁⁻¹ := (c.elts hπ hz hz1).t_s₁
  have hx3 : x ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact c.s₁_pow)
  have hy2 : y ^ 2 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact c.t_sq)
  have hyx : y * x * y⁻¹ = x⁻¹ := Subtype.ext hts
  have hxQ : ∃ q ∈ (Qh π).subgroupOf (M0 c), (x * q * x⁻¹)⁻¹ * q ∉ O.subgroupOf (M0 c) := by
    obtain ⟨q, hq, hqO⟩ := exists_q_comm_not_mem_O hπ c hOmap
    exact ⟨⟨q, Qh_le_M0 hπ c hq⟩, hq, hqO⟩
  have hy1 : y ∉ O.subgroupOf (M0 c) := fun h => by
    have hodd : Odd (orderOf c.t) :=
      TwoCover.odd_orderOf_of_mem_isPGroup_three hO3 (Subgroup.mem_subgroupOf.mp h)
    have h2 : orderOf c.t = 2 := (c.elts hπ hz hz1).t_ord
    rw [h2] at hodd
    exact absurd hodd (by decide)
  obtain ⟨hpc, ⟨φ⟩⟩ := pPrimeCore_eq_of_recognition hR1 hR2 (card_M0 hπ c) (O.subgroupOf (M0 c)) hOs
    ((Qh π).subgroupOf (M0 c)) e hQ4 x y hx3 hy2 hyx hxQ hy1
  refine ⟨?_, ?_, ?_⟩
  · rw [hMh]
    exact card_M0 hπ c
  · rw [hMh]
    exact ⟨φ⟩
  · rw [hMh]
    intro w hw htw
    have hoc : oc (M0 c) = O := by
      unfold oc
      rw [hpc]
      exact Subgroup.map_subgroupOf_eq_of_le hOM
    rw [hoc] at hw
    exact hOt w hw htw

end CFSG.GH74.Uniqueness.SU.SU13.TA.L10
