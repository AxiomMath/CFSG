module

public import CFSG.GF2Type.Smith1979.WidthFourKP.MinusCentral.Theta
public import CFSG.GF2Type.Smith1979.WidthFourKP.MinusCentral.TwoCubed
public import CFSG.GF2Type.Smith1979.WidthFourKP.MinusCentral.CentLbar

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4MinusC

open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S7
  CFSG.LargeExtraspecial.S8 CFSG.Open Subgroup Module
open CFSG.RankThree.OrthogonalInvolutions

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

section Context

variable (hCE : CentralExtInput.{0}) (hw : S.width = 4) (H : Hyp4 S g) (hNo : NoA2 S g)
  (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
  (hΩ : OmegaCase H C ht ht1 hVQ) (h4 : finrank (ZMod 2) (Vt S g t) = 4) (hP : ¬ PlusAt H C)
include hCE hw H hNo C ht ht1 hVQ hΩ h4 hP

theorem mem_Lbar_mul_of_cl_mem_Vt (h : S.M)
    (hb : S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹) ∈ Vt S g t) :
    t ∈ S.Lbar ((h : G) * g) := by
  have hb0 : (⟨_, hb⟩ : Vt S g t) ≠ 0 := fun h0 =>
    cl_conj_z_ne_zero S (H.mul h).conj_mem (H.mul h).conj_ne (congrArg Subtype.val h0)
  obtain ⟨θ, hθR, hθ3, hθb, v, hv⟩ :=
    exists_theta_w4 hCE hw H hNo C ht ht1 hVQ hΩ h4 hP hb0
  have hθRbar : θ ∈ Rbar S g t := Subgroup.commutator_le_self _ hθR
  have hθM : θ ∈ S.Mbar := Rbar_le_Mbar hθRbar
  have hθt : θ * t = t * θ := commute_of_mem_Rbar H.conj_mem hθRbar
  have htb : (t : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹)) =
      S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹) := by
    have hbW : S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹) ∈ Wt S g t := by
      rw [W4Minus.Wt_eq_Vt_w4 hw H ht1 h4]
      exact hb
    rw [← (commSpace_t_eq H C ht ht1 hVQ).2, mem_fixSpace] at hbW
    exact hbW
  have hθN : θ ∈ normalizer (S.Lbar ((h : G) * g) : Set S.O) :=
    mem_normalizer_of_fix H.conj_mem H.conj_ne hθM hθb
  have htN : t ∈ normalizer (S.Lbar ((h : G) * g) : Set S.O) :=
    mem_normalizer_of_fix H.conj_mem H.conj_ne (S.Lbar_le_Mbar g ht) htb
  have hA8 : Nat.card (S.Lbar ((h : G) * g)) = 8 := by
    rw [(C.mul h).card_Lbar, hw]
    norm_num
  have hA2 : ∀ a ∈ S.Lbar ((h : G) * g), a * a = 1 := fun a ha =>
    mul_self_of_mem_Lbar S (H.mul h).conj_mem ha
  have hAc : ∀ a ∈ S.Lbar ((h : G) * g), ∀ b ∈ S.Lbar ((h : G) * g), a * b = b * a :=
    fun a ha b hb' => Lbar_comm S (H.mul h).conj_mem ha hb'
  have hθA : ¬ ∀ a ∈ S.Lbar ((h : G) * g), θ * a = a * θ := by
    intro hc
    have hθL := mem_Lbar_mul_of_centralizes_w4 hCE hw H hNo C ht ht1 hVQ hΩ h4 hP h hθM hc
    have h2 : θ * θ = 1 := hA2 θ hθL
    have h1 : θ = 1 := by
      calc θ = θ ^ 3 * (θ * θ)⁻¹ := by group
        _ = 1 := by rw [hθ3, h2]; group
    apply hv
    rw [h1]
    rfl
  have htt : t * t = 1 := mul_self_of_mem_Lbar S H.conj_mem ht
  have hcent := centralizes_of_commute_three (S.Lbar ((h : G) * g)) hA8 hA2 hAc hθN hθ3 hθA htN
    htt hθt.symm
  exact mem_Lbar_mul_of_centralizes_w4 hCE hw H hNo C ht ht1 hVQ hΩ h4 hP h
    (S.Lbar_le_Mbar g ht) hcent

theorem orbit67_w4 : Orbit67 S g t := by
  intro h hb
  have hth := mem_Lbar_mul_of_cl_mem_Vt hCE hw H hNo C ht ht1 hVQ hΩ h4 hP h hb
  have hmem := bV_mem_orbitOf H C ht ht1 hVQ hNo hΩ.not_transitive hth
  rw [mem_orbitOf_RmodN_iff H.conj_mem ht, coe_bV] at hmem
  exact hmem

theorem conj_mem_Lbar_of_mem_normalizer_w4 {x : S.O} (hx : x ∈ S.Mbar)
    (hxN : x * t * x⁻¹ ∈ normalizer (S.Lbar g : Set S.O)) : x * t * x⁻¹ ∈ S.Lbar g := by
  obtain ⟨k, rfl⟩ := MonoidHom.mem_range.mp hx
  have hfix := fix_of_mem_normalizer H hxN
  have htw : (t : S.Qt ≃ₗ[ZMod 2] S.Qt)
      ((((S.ρ k)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹))) =
      (((S.ρ k)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) := by
    have h1 := congrArg (((S.ρ k)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) hfix
    rwa [S4.coe_mul_apply, S4.coe_mul_apply, S4.inv_apply_apply_O] at h1
  have hmemW : (((S.ρ k)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) ∈
      Wt S g t := by
    rw [← (commSpace_t_eq H C ht ht1 hVQ).2, mem_fixSpace]
    exact htw
  have hmem : (((S.ρ k)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
      (S.cl (((1 : S.M) : G) * g * S.z * (((1 : S.M) : G) * g)⁻¹)) ∈ Vt S g t := by
    have e : ((1 : S.M) : G) * g * S.z * (((1 : S.M) : G) * g)⁻¹ = g * S.z * g⁻¹ := by
      simp [mul_assoc]
    rw [e, ← W4Minus.Wt_eq_Vt_w4 hw H ht1 h4]
    exact hmemW
  have key := conj_mem_Lbar_of_inv_apply_mem H ht
    (orbit67_w4 hCE hw H hNo C ht ht1 hVQ hΩ h4 hP) k 1 hmem
  have e2 : ((1 : S.M) : G) * g = g := by simp
  rw [e2] at key
  exact key

end Context

end CFSG.GF2Type.Smith1979.W4MinusC
