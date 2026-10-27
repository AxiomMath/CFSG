module

public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.U33
public import CFSG.LieType.ChevTwo.OppCl.SmallGlue
public import CFSG.Open.StatedDefs
public import CFSG.Blueprint.Catalog

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ

open CFSG.Open CFSG.GH74.KGroups CFSG.GH74.KGroups.U33 CFSG.LieType.ChevTwo.OppCl
  CFSG.LieType.BorelTits
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)

theorem radRigid_of_inner_odd {K : Type} [Group K] (hinj : Function.Injective (MulAut.conj : K →* MulAut K))
    (hinner : ∀ α : MulAut K, Odd (orderOf α) → α ∈ (MulAut.conj : K →* MulAut K).range)
    (hI : RadRigidInner 2 K) : RadRigid 2 K := by
  intro R hR α hfix hcop
  obtain ⟨g, rfl⟩ := hinner α (odd_of_coprime_two hcop)
  have hg : ∀ r ∈ R, g * r = r * g := by
    intro r hr
    have h := hfix r hr
    rw [MulAut.conj_apply] at h
    calc g * r = g * r * g⁻¹ * g := by group
      _ = r * g := by rw [h]
  have hord : orderOf g = orderOf (MulAut.conj g) := (orderOf_injective _ hinj g).symm
  have hg1 : g = 1 := hI R hR g hg (by rw [hord]; exact hcop)
  rw [hg1, map_one]

section Final


theorem radRigid_u33 (S : Type) [Group S] [Finite S] (hs : IsSimpleGroup S)
    (h : StatedClassicalModel S .PSU 3 3 1) (hBT : HoldsTits S 2) : RadRigid 2 S := by
  have hL : CFSG.Blueprint.LieModel S .PSU 3 3 1 :=
    Or.inl ⟨by decide, (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel S .PSU 3 3 1)⟩
  obtain ⟨e⟩ := U33.equiv_of_lieModel hL
  have hK : Nat.card S = 6048 := by
    rw [Nat.card_congr e.toEquiv, card_group QP QP_ok]
    exact QP_valid.2
  haveI : Finite (MulAut S) := U33.finite_mulAut e
  have hcardM : Nat.card (MulAut S) = 12096 := U33.card_mulAut e
  have hZ : ∀ z : S, (∀ h : S, h * z = z * h) → z = 1 := by
    intro z hz
    have hcenter : Subgroup.center S = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with hc | hc
      · exact hc
      · exfalso
        let _ : CommGroup S := Group.commGroupOfCenterEqTop hc
        have := IsSimpleGroup.prime_card (α := S)
        rw [hK] at this
        norm_num at this
    have : z ∈ Subgroup.center S := Subgroup.mem_center_iff.2 fun h => hz h
    rw [hcenter] at this
    exact this
  have hinj : Function.Injective (MulAut.conj : S →* MulAut S) := by
    rw [injective_iff_map_eq_one]
    intro z hz
    apply hZ z
    intro h
    have hzh := congrArg (fun a : MulAut S => a h) hz
    simp only [MulAut.conj_apply, MulAut.one_apply] at hzh
    exact (mul_inv_eq_iff_eq_mul.1 hzh).symm
  have hinner : Nat.card (inner S) = 6048 := by
    rw [← hK]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hO : Nat.card (Outer S) ∣ 2 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (inner S)
    rw [hcardM, hinner] at h1
    have h1' : Nat.card (Outer S) * 6048 = 12096 := h1.symm
    have h2 : Nat.card (Outer S) = 2 := by omega
    rw [h2]
  exact radRigid_of_inner_odd hinj
    (fun α hα => mem_inner_of_odd_orderOf_of_card_outer_dvd_two hO hα)
    (U33Fin.radRigidInner_of_model e hBT)

end Final

end CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ
