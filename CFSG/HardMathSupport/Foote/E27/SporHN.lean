module

public import CFSG.HardMathSupport.Foote.E27.PermCent
public import CFSG.HardMathSupport.Foote.E27.SplitIn
public import CFSG.Sporadic.HNSchreier.Sylow3
public import CFSG.Sporadic.HNSchreier.Faithful
public import CFSG.Sporadic.Bridge.Catalogue
public import CFSG.Certificates.CentralKernel
public import CFSG.Certificates.CosetTableWalkC
public import CFSG.Certificates.FusionF2
public import CFSG.Certificates.WordSubgroupHom
public import CFSG.Sporadic.Bridge.M11CheckInputs
public import CFSG.Sporadic.Presentation.Co2Base
public import CFSG.Sporadic.Presentation.Co2Cover
public import CFSG.Sporadic.Presentation.Co2Fusion
public import CFSG.Sporadic.Presentation.Co2FusionInputs
public import CFSG.Sporadic.Presentation.McLExactData
public import CFSG.Sporadic.Presentation.McLExactInputs
public import CFSG.YGroups.DCE.B433Check
public import Certificates.Certificate9124

public section

namespace CFSG.HardMathSupport.Foote.E27

open CFSG.Sporadic.HNSchreier CFSG.Blueprint Subgroup Equiv

theorem card_comm_eq_of_isConj {G : Type*} [Group G] {a b : G} (h : IsConj a b) :
    Nat.card {y : G // a * y = y * a} = Nat.card {y : G // b * y = y * b} := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  refine Nat.card_congr (Equiv.subtypeEquiv (MulAut.conj c).toEquiv fun y => ?_)
  show a * y = y * a ↔ b * (c * y * c⁻¹) = (c * y * c⁻¹) * b
  rw [← hc]
  constructor
  · intro hy
    calc c * a * c⁻¹ * (c * y * c⁻¹) = c * (a * y) * c⁻¹ := by group
      _ = c * (y * a) * c⁻¹ := by rw [hy]
      _ = c * y * c⁻¹ * (c * a * c⁻¹) := by group
  · intro hy
    have h1 : c * (a * y) * c⁻¹ = c * (y * a) * c⁻¹ :=
      calc c * (a * y) * c⁻¹ = c * a * c⁻¹ * (c * y * c⁻¹) := by group
        _ = c * y * c⁻¹ * (c * a * c⁻¹) := hy
        _ = c * (y * a) * c⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h1)

theorem dvd81_card_comm_sJ
    {k : ℕ} (hk : k < 4) :
    81 ∣ Nat.card {y : JH // sJ k * y = y * sJ k} := by
  set h : HJ := ⟨sJ k, sJ_mem k⟩ with hh
  have hσ : orderOf (thetaJ h : Perm (Fin 12)) = 3 := by
    rw [hh, thetaJ_sJ hk]
    exact orderOf_tripleNat (by omega) (by omega)
  have h81 := dvd81_card_alt_commuting (n := 12) le_rfl hσ
  have e1 : {a : alternatingGroup (Fin 12) //
      (thetaJ h : Perm (Fin 12)) * (a : Perm (Fin 12)) = a * (thetaJ h : Perm (Fin 12))} ≃
      {u : HJ // h * u = u * h} :=
    Equiv.subtypeEquiv thetaJ.symm.toEquiv fun a => by
      show _ ↔ h * thetaJ.symm a = thetaJ.symm a * h
      rw [← thetaJ.injective.eq_iff, map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact ⟨fun h' => Subtype.ext h', fun h' => congrArg Subtype.val h'⟩
  have e2 : {u : HJ // h * u = u * h} ≃ ↥(HJ ⊓ centralizer ({sJ k} : Set JH)) :=
    { toFun := fun u => ⟨u.1.1, u.1.2, mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val u.2).symm⟩
      invFun := fun v => ⟨⟨v.1, v.2.1⟩, Subtype.ext (mem_centralizer_singleton_iff.mp v.2.2).symm⟩
      left_inv := fun u => rfl
      right_inv := fun v => rfl }
  have e3 : {y : JH // sJ k * y = y * sJ k} ≃ ↥(centralizer ({sJ k} : Set JH)) :=
    { toFun := fun y => ⟨y.1, mem_centralizer_singleton_iff.mpr y.2.symm⟩
      invFun := fun y => ⟨y.1, (mem_centralizer_singleton_iff.mp y.2).symm⟩
      left_inv := fun y => rfl
      right_inv := fun y => rfl }
  rw [Nat.card_congr e3]
  rw [Nat.card_congr e1, Nat.card_congr e2] at h81
  exact dvd_trans h81 (Subgroup.card_dvd_of_le inf_le_right)

theorem e27_not_HN
    (hbr : Nonempty (NativeSporadic.HN ≃*
      (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.HN).Group))
    {X : Type} [Group X] [Finite X] {K R T : Subgroup X} {z : X} (hc : E27Config X K R T z)
    (hz : z ∈ K)
    (e : Nonempty (↥K ≃* (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.HN).Group)) :
    False := by
  let φ : ↥K ≃* JH := e.some.trans (hbr.some.symm.trans hnEquivJ)
  let z0 : ↥K := ⟨z, hz⟩
  have hz1 : z ≠ 1 := fun h => hc.z_not_mem (h ▸ T.one_mem)
  have hz3 : z ^ 3 = 1 := hc.elem.2 z hc.z_mem
  have hz0 : orderOf z0 = 3 :=
    orderOf_eq_prime (Subtype.ext (by simpa [z0] using hz3))
      (fun h => hz1 (congrArg Subtype.val h))
  have hx : orderOf (φ z0) = 3 := by rw [MulEquiv.orderOf_eq]; exact hz0
  obtain ⟨k, hk, hconj⟩ := order_three_isConj hx
  have h81 := dvd81_card_comm_sJ hk
  rw [card_comm_eq_of_isConj hconj] at h81
  have e3 : {y : JH // φ z0 * y = y * φ z0} ≃ {y : ↥K // z0 * y = y * z0} :=
    Equiv.subtypeEquiv φ.symm.toEquiv fun y => by
      show _ ↔ z0 * φ.symm y = φ.symm y * z0
      rw [← φ.injective.eq_iff, map_mul, map_mul, MulEquiv.apply_symm_apply]
  have e4 : {y : ↥K // z0 * y = y * z0} ≃ ↥(centralizer ({z} : Set X) ⊓ K) :=
    { toFun := fun y => ⟨y.1.1, mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val y.2).symm, y.1.2⟩
      invFun := fun v => ⟨⟨v.1, v.2.2⟩, Subtype.ext (mem_centralizer_singleton_iff.mp v.2.1).symm⟩
      left_inv := fun y => rfl
      right_inv := fun v => rfl }
  rw [Nat.card_congr e3, Nat.card_congr e4] at h81
  have h3 : 3 ^ 4 ∣ Nat.card ↥(centralizer ({z} : Set X) ⊓ K) := by
    simpa using h81
  have h4 := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three Nat.card_pos.ne').mp h3
  have h5 := hc.factorization_card_centralizer_inf_of_mem hz
  omega

end CFSG.HardMathSupport.Foote.E27
