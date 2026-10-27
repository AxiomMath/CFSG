module

public import CFSG.GF2Type.Smith1979.W4AsOmega
public import CFSG.LargeExtraspecial.S8A5I
public import CFSG.GF2Type.Smith1979.WidthFourKP.OmegaCases

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4Minus

open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S7
  CFSG.LargeExtraspecial.S8 CFSG.Open Subgroup Module
open CFSG.RankThree.OrthogonalInvolutions

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

theorem Wt_eq_Vt_w4 (hw : S.width = 4) (H : Hyp4 S g) {t : S.O} (ht1 : t ≠ 1)
    (h4 : finrank (ZMod 2) (Vt S g t) = 4) : Wt S g t = Vt S g t := by
  have h1 := finrank_Wt (S := S) (g := g) (t := t)
  have h2 := S.finrank_Qt_eq_two_mul_width
  exact (Submodule.eq_of_le_of_finrank_le (Vt_le_Wt H ht1) (by omega)).symm

theorem eq_one_or_t_of_fix_Vt (hCE : CentralExtInput.{0}) (hw : S.width = 4) (H : Hyp4 S g)
    (hNo : NoA2 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
    (hVQ : ¬ V S g t ≤ S.Qa g) (hΩ : OmegaCase H C ht ht1 hVQ)
    (h4 : finrank (ZMod 2) (Vt S g t) = 4) (hP : ¬ PlusAt H C) {c : S.O} (hcM : c ∈ S.Mbar)
    (hct : c * t = t * c) (hcV : ∀ v ∈ Vt S g t, (c : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) :
    c = 1 ∨ c = t := by
  have hN := W4As.Nbar_eq_zpowers_omega4 hCE hw H hNo C ht ht1 hVQ hΩ h4
  obtain ⟨D⟩ := S8.Std.nonempty hCE hNo hΩ
  have hWV : Wt S g t = Vt S g t := Wt_eq_Vt_w4 hw H ht1 h4
  have hmin : ∀ U : Submodule (ZMod 2) (Vt S g t), finrank (ZMod 2) U = 2 →
      ∃ u ∈ U, D.Q u ≠ 0 := by
    intro U hU
    by_contra hcon
    push Not at hcon
    apply hP
    refine ⟨t, ht, ht1, hVQ, hΩ, h4, U, hU, fun v hv hv0 => ?_⟩
    exact (D.hsing v hv0).mp (hcon v hv)
  obtain ⟨hsimple, hnab⟩ := S8.isSimpleGroup_omegaGroup_minus_four D.hQ h4 hmin
  have hs : IsSimpleGroup (RmodN S g t) := D.hX ▸ hsimple
  have hnc : ¬ IsMulCommutative (RmodN S g t) := by
    rw [D.hX]
    intro h
    exact hnab fun x y => h.is_comm.comm x y
  have htop := CFSG.GroupTheory.commutator_eq_top_of_isSimpleGroup hs hnc
  have hperf : ⁅RmodN S g t, RmodN S g t⁆ = RmodN S g t := by
    rw [← Subgroup.map_subtype_commutator, htop, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hσR : ∀ r ∈ Rbar S g t, c * r = r * c := fun r hr =>
    (S7.comm_of_fix_Vt H hN hperf hcM hct hcV hr).symm
  have hσQ : ∀ x : S.Qt, (c : S.Qt ≃ₗ[ZMod 2] S.Qt) x - x ∈ Vt S g t := by
    intro x
    have hv : (t : S.Qt ≃ₗ[ZMod 2] S.Qt) x - x ∈ Vt S g t := by
      rw [← (S4.commSpace_t_eq H C ht ht1 hVQ).1]
      exact mem_commSpace.mpr ⟨x, rfl⟩
    have hfix_c : (c : S.Qt ≃ₗ[ZMod 2] S.Qt)
        ((t : S.Qt ≃ₗ[ZMod 2] S.Qt) x - x) = (t : S.Qt ≃ₗ[ZMod 2] S.Qt) x - x := hcV _ hv
    have hcx : (t : S.Qt ≃ₗ[ZMod 2] S.Qt) ((c : S.Qt ≃ₗ[ZMod 2] S.Qt) x) =
        (c : S.Qt ≃ₗ[ZMod 2] S.Qt) ((t : S.Qt ≃ₗ[ZMod 2] S.Qt) x) := by
      rw [← coe_mul_apply, ← coe_mul_apply, hct]
    have h2 : (t : S.Qt ≃ₗ[ZMod 2] S.Qt) ((c : S.Qt ≃ₗ[ZMod 2] S.Qt) x) -
        (c : S.Qt ≃ₗ[ZMod 2] S.Qt) x = (t : S.Qt ≃ₗ[ZMod 2] S.Qt) x - x := by
      calc (t : S.Qt ≃ₗ[ZMod 2] S.Qt) ((c : S.Qt ≃ₗ[ZMod 2] S.Qt) x) -
            (c : S.Qt ≃ₗ[ZMod 2] S.Qt) x
          = (c : S.Qt ≃ₗ[ZMod 2] S.Qt) ((t : S.Qt ≃ₗ[ZMod 2] S.Qt) x) -
              (c : S.Qt ≃ₗ[ZMod 2] S.Qt) x := by rw [hcx]
        _ = (c : S.Qt ≃ₗ[ZMod 2] S.Qt)
              ((t : S.Qt ≃ₗ[ZMod 2] S.Qt) x - x) := by rw [map_sub]
        _ = (t : S.Qt ≃ₗ[ZMod 2] S.Qt) x - x := hfix_c
    have hmemW : (c : S.Qt ≃ₗ[ZMod 2] S.Qt) x - x ∈ Wt S g t := by
      rw [← (S4.commSpace_t_eq H C ht ht1 hVQ).2]
      refine mem_fixSpace.mpr ?_
      rw [map_sub]
      apply sub_eq_zero.mp
      have h3 : ((t : S.Qt ≃ₗ[ZMod 2] S.Qt) ((c : S.Qt ≃ₗ[ZMod 2] S.Qt) x) -
          (t : S.Qt ≃ₗ[ZMod 2] S.Qt) x) -
          ((c : S.Qt ≃ₗ[ZMod 2] S.Qt) x - x) = 0 := by
        have e : ((t : S.Qt ≃ₗ[ZMod 2] S.Qt) ((c : S.Qt ≃ₗ[ZMod 2] S.Qt) x) -
            (t : S.Qt ≃ₗ[ZMod 2] S.Qt) x) -
            ((c : S.Qt ≃ₗ[ZMod 2] S.Qt) x - x) =
            ((t : S.Qt ≃ₗ[ZMod 2] S.Qt) ((c : S.Qt ≃ₗ[ZMod 2] S.Qt) x) -
              (c : S.Qt ≃ₗ[ZMod 2] S.Qt) x) -
              ((t : S.Qt ≃ₗ[ZMod 2] S.Qt) x - x) := by abel
        rw [e, h2, sub_self]
      exact h3
    rwa [hWV] at hmemW
  have hσW : ∀ w ∈ Wt S g t, (c : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w := by
    intro w hw
    exact hcV w (hWV ▸ hw)
  by_cases hc1 : c = 1
  · exact Or.inl hc1
  · exact Or.inr (S8.eq_t_of_commute_Rbar D hσR hσQ hσW hc1)

end CFSG.GF2Type.Smith1979.W4Minus
