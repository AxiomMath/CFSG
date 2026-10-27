module

public import CFSG.GH74.GLS.SP.Local.SPLPumpXCtx
public import CFSG.GH74.GLS.SP.Local.SPLPumpXA
public import CFSG.GH74.GLS.SP.Local.SPLTabL2
public import CFSG.GH74.GLS.SP.Local.SPLTabA7

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS
open scoped commutatorElement

@[expose] def conjAutL {X : Type} [Group X] {L : Subgroup X} {g : X}
    (hg : g ∈ normalizer (L : Set X)) : MulAut ↥L where
  toFun y := ⟨g * y * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg y).mp y.2⟩
  invFun y := ⟨g⁻¹ * y * g, by
    have h := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) y).mp y.2
    rwa [inv_inv] at h⟩
  left_inv y := Subtype.ext (by simp [mul_assoc])
  right_inv y := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

theorem conjAutL_apply {X : Type} [Group X] {L : Subgroup X} {g : X}
    (hg : g ∈ normalizer (L : Set X)) (y : ↥L) : (conjAutL hg y : X) = g * y * g⁻¹ := rfl

theorem normalizer_of_stable {X : Type} [Group X] {L : Subgroup X} {z : X} (hz : z * z = 1)
    (h : ∀ x ∈ L, z * x * z⁻¹ ∈ L) : z ∈ normalizer (L : Set X) := by
  have hinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  exact mem_normalizer_of_conj h (fun i hi => by rw [hinv]; simpa [hinv] using h i hi)

namespace XCtx

variable {X : Type} [Group X] [Finite X] {z t : X} {A T₁ : Subgroup X}

theorem zt_comm_A (hX : XCtx X z t A T₁) :
    ∀ ζ ∈ zpowers z ⊔ zpowers t, ∀ a ∈ A, ζ * a = a * ζ := by
  have hle : zpowers z ⊔ zpowers t ≤ centralizer (A : Set X) := by
    refine sup_le ?_ ?_
    · rw [zpowers_le, mem_centralizer_iff]
      intro a ha
      exact (hX.A_cen a ha).symm
    · rw [zpowers_le, mem_centralizer_iff]
      intro a _
      exact hX.t_central a
  intro ζ hζ a ha
  exact (mem_centralizer_iff.mp (hle hζ) a ha).symm

theorem A_isSimple (hX : XCtx X z t A T₁) : IsSimpleGroup ↥A := by
  obtain ⟨q, hq, hq5, F, _, _, hF, ⟨e⟩⟩ := hX.A_L2
  have hF' : IVK.L2Field F := ⟨hF ▸ hq, by rw [hF]; omega⟩
  exact IVK.Proofs2.isSimpleGroup_of_l2 hF' e

theorem A_even (hX : XCtx X z t A T₁) : Even (Nat.card ↥A) := by
  obtain ⟨q, hq, hq5, F, _, _, hF, ⟨e⟩⟩ := hX.A_L2
  have hF' : IVK.L2Field F := ⟨hF ▸ hq, by rw [hF]; omega⟩
  exact IVK.Proofs2.even_card_of_l2 hF' e

theorem A_noncomm (hX : XCtx X z t A T₁) : ∃ a b : ↥A, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  have hle : A ≤ centralizer (A : Set X) := fun a ha =>
    mem_centralizer_iff.mpr fun b hb => congrArg Subtype.val (hcon ⟨b, hb⟩ ⟨a, ha⟩)
  have hbot : ⁅A, A⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hle
  rw [hX.A_perf] at hbot
  have hcard : Nat.card ↥A = 1 := by rw [hbot]; exact Subgroup.card_bot
  have := hX.A_even
  rw [hcard] at this
  exact absurd this (by decide)

theorem A_quasisimple (hX : XCtx X z t A T₁) : IsQuasisimple ↥A ∧ center ↥A = ⊥ := by
  have := hX.A_isSimple
  exact CFSG.LocalCores.isQuasisimple_of_isSimpleGroup (Q := ↥A) hX.A_noncomm

theorem A_sub_quasisimple (hX : XCtx X z t A T₁) {L : Subgroup X} (hAL : A ≤ L) :
    IsQuasisimple ↥(A.subgroupOf L) :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hAL).symm
    hX.A_quasisimple.1

theorem orderOf_t (hX : XCtx X z t A T₁) : orderOf t = 2 :=
  orderOf_eq_prime (by rw [sq]; exact hX.t_sq) hX.t_ne_one

theorem false_of_outer (hX : XCtx X z t A T₁) {L : Subgroup X} (hL : StableL z A L)
    (hout : HasOuterTwoElement
      (fixedSubgroup ↥L (conjAutL (normalizer_of_stable hX.z_sq hL.stable))) (A.subgroupOf L)) :
    False := by
  obtain ⟨c, hcfix, ⟨k, hck⟩, -, hcnot⟩ := hout
  have hzc : z * (c : X) = (c : X) * z := by
    have h1 : (conjAutL (normalizer_of_stable hX.z_sq hL.stable) c : X) = c := congrArg Subtype.val hcfix
    rw [conjAutL_apply] at h1
    calc z * (c : X) = z * c * z⁻¹ * z := by group
      _ = c * z := by rw [h1]
  have hc2 : (c : X) ^ (2 ^ k) = 1 := congrArg Subtype.val hck
  have hmem := hX.two_elt (c : X) hzc ⟨k, hc2⟩
  obtain ⟨ζ, hζ, a, ha, hζa⟩ := mem_sup_of_comm (A := zpowers z ⊔ zpowers t) (B := A)
    (fun ζ hζ a ha => hX.zt_comm_A ζ hζ a ha) hmem
  have hζL : ζ ∈ L := by
    have : ζ = (c : X) * a⁻¹ := by rw [← hζa]; group
    rw [this]
    exact mul_mem c.2 (inv_mem (hL.A_le ha))
  have hcomm : ∀ y ∈ A.subgroupOf L, y * (⟨ζ, hζL⟩ : ↥L) = ⟨ζ, hζL⟩ * y := by
    intro y hy
    exact Subtype.ext (hX.zt_comm_A ζ hζ y hy).symm
  have hcen : (⟨ζ, hζL⟩ : ↥L) ∈ centralizer ((A.subgroupOf L : Subgroup ↥L) : Set ↥L) :=
    mem_centralizer_iff.mpr fun y hy => hcomm y hy
  have hc : c = (⟨a, hL.A_le ha⟩ : ↥L) * ⟨ζ, hζL⟩ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← hζa, ← hX.zt_comm_A ζ hζ a ha]
  exact hcnot (hc ▸ mul_mem_sup (show (⟨a, hL.A_le ha⟩ : ↥L) ∈ A.subgroupOf L from ha) hcen)

theorem conjAutL_sq (hX : XCtx X z t A T₁) {L : Subgroup X} (hL : StableL z A L) :
    conjAutL (normalizer_of_stable hX.z_sq hL.stable) ^ 2 = 1 := by
  ext y
  show (z * (z * (y : X) * z⁻¹) * z⁻¹ : X) = y
  calc z * (z * (y : X) * z⁻¹) * z⁻¹ = (z * z) * (y : X) * (z * z)⁻¹ := by group
    _ = y := by rw [hX.z_sq]; group

theorem conjAutL_ne_one (hX : XCtx X z t A T₁) {L : Subgroup X} (hL : StableL z A L) :
    conjAutL (normalizer_of_stable hX.z_sq hL.stable) ≠ 1 := by
  obtain ⟨x, hx, hne⟩ := hL.moves
  intro h
  apply hne
  have h1 := congrArg (fun f : MulAut ↥L => (f ⟨x, hx⟩ : X)) h
  simp only [conjAutL_apply, MulAut.one_apply] at h1
  calc z * x = z * x * z⁻¹ * z := by group
    _ = x * z := by rw [h1]

theorem A_sub_fixed (hX : XCtx X z t A T₁) {L : Subgroup X} (hL : StableL z A L) :
    ∀ x ∈ A.subgroupOf L, conjAutL (normalizer_of_stable hX.z_sq hL.stable) x = x := by
  intro x hx
  apply Subtype.ext
  show z * (x : X) * z⁻¹ = x
  have h := hX.A_cen (x : X) hx
  calc z * (x : X) * z⁻¹ = x * z * z⁻¹ := by rw [h]
    _ = x := by group

theorem A_sub_subnormal (hX : XCtx X z t A T₁) {L : Subgroup X} (hL : StableL z A L) :
    ((A.subgroupOf L).subgroupOf
      (fixedSubgroup ↥L (conjAutL (normalizer_of_stable hX.z_sq hL.stable)))).IsSubnormal := by
  have hle : A.subgroupOf L ≤ fixedSubgroup ↥L (conjAutL (normalizer_of_stable hX.z_sq hL.stable)) :=
    fun x hx => hX.A_sub_fixed hL x hx
  have : ((A.subgroupOf L).subgroupOf
      (fixedSubgroup ↥L (conjAutL (normalizer_of_stable hX.z_sq hL.stable)))).Normal := by
    refine (Subgroup.normal_subgroupOf_iff hle).mpr fun h k hh hk => ?_
    have hkz : z * ((k : ↥L) : X) = ((k : ↥L) : X) * z := by
      have h1 : (conjAutL (normalizer_of_stable hX.z_sq hL.stable) k : X) = k := congrArg Subtype.val hk
      rw [conjAutL_apply] at h1
      calc z * ((k : ↥L) : X) = z * k * z⁻¹ * z := by group
        _ = k * z := by rw [h1]
    exact hX.A_norm _ hkz h hh
  exact Subgroup.Normal.isSubnormal this

theorem A_sub_L2 (hX : XCtx X z t A T₁) {L : Subgroup X} (hAL : A ≤ L) :
    ∃ q : ℕ, Odd q ∧ 5 ≤ q ∧ IVK.IsL2 ↥(A.subgroupOf L) (fun r => r = q) := by
  obtain ⟨q, hq, hq5, F, hF, hFin, hFq, ⟨e⟩⟩ := hX.A_L2
  exact ⟨q, hq, hq5, F, hF, hFin, hFq, ⟨(Subgroup.subgroupOfEquivOfLe hAL).trans e⟩⟩

theorem stable_L2 (hX : XCtx X z t A T₁) {L : Subgroup X} (hL : StableL z A L)
    {F : Type} [Field F] [Finite F] (hF : IVK.L2Field F) (e : ↥L ≃* IVK.L2 F) : False := by
  obtain ⟨q, hq, hq5, hAq⟩ := hX.A_sub_L2 hL.A_le
  exact hX.false_of_outer hL (tabL2Outer F hF ↥L ⟨e⟩ _ (hX.conjAutL_sq hL) (hX.conjAutL_ne_one hL)
    q hq hq5 _ (hX.A_sub_fixed hL) hAq (hX.A_sub_subnormal hL))

theorem stable_A7 (hX : XCtx X z t A T₁) {L : Subgroup X} (hL : StableL z A L)
    (e : ↥L ≃* alternatingGroup (Fin 7)) : False := by
  obtain ⟨q, hq, hq5, hAq⟩ := hX.A_sub_L2 hL.A_le
  exact hX.false_of_outer hL (tabA7Outer ↥L ⟨e⟩ _ (hX.conjAutL_sq hL) (hX.conjAutL_ne_one hL)
    q hq hq5 _ (hX.A_sub_fixed hL) hAq (hX.A_sub_subnormal hL))

end XCtx

end CFSG.GH74.GLS.SP.Local
