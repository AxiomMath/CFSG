module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CIProdL
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7NPLift
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CA6
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CA7

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

namespace Eight2

namespace CtxA0

variable {X : Type} [Group X] [Finite X] (c : CtxA0 X)

theorem hbS : c.b ∈ c.s.h.S := c.s.h.B_le_S (c.s.h.secB0_le_B c.s.y c.hbB)

theorem hbP : c.b ∈ c.s.h.P := c.s.B0_le_P c.hbB

theorem hza : c.Z.z * c.s.h.a = c.s.h.a * c.Z.z := (c.Z.hzS _ (c.s.h.P_le_S c.s.h.a_mem_P)).symm

theorem hba : c.b * c.s.h.a = c.s.h.a * c.b := c.s.h.comm_a c.hbS

theorem hbz : c.b * c.Z.z = c.Z.z * c.b := c.Z.hzS _ c.hbS

theorem conj_t_b : c.s.t⁻¹ * c.b * c.s.t = c.b := by
  have h1 := mem_centralizer_iff.mp (c.s.Lay_le_centralizer c.htL) c.b c.hbB
  rw [mul_assoc, h1, inv_mul_cancel_left]

theorem conj_t_ab : c.s.t⁻¹ * (c.s.h.a * c.b) * c.s.t = c.Z.z := by
  have h1 := c.Z.hzS _ (mem_inf.mp c.ht2).1
  calc c.s.t⁻¹ * (c.s.h.a * c.b) * c.s.t = c.s.t⁻¹ * (c.s.t⁻¹ * c.Z.z * c.s.t) * c.s.t := by
        rw [c.hzb]
    _ = (c.s.t * c.s.t)⁻¹ * c.Z.z * (c.s.t * c.s.t) := by group
    _ = (c.s.t * c.s.t)⁻¹ * ((c.s.t * c.s.t) * c.Z.z) := by rw [mul_assoc, h1]
    _ = c.Z.z := by group

theorem conj_t_a : c.s.t⁻¹ * c.s.h.a * c.s.t = c.Z.z * c.b := by
  have h1 : c.s.h.a = c.s.h.a * c.b * c.b := by rw [mul_assoc, c.hbb, mul_one]
  calc c.s.t⁻¹ * c.s.h.a * c.s.t =
      (c.s.t⁻¹ * (c.s.h.a * c.b) * c.s.t) * (c.s.t⁻¹ * c.b * c.s.t) := by
        nth_rewrite 1 [h1]; group
    _ = c.Z.z * c.b := by rw [c.conj_t_ab, c.conj_t_b]

theorem conj_tu_a {u : X} (hu : u ∈ c.s.h.S) (hub : u⁻¹ * c.b * u = c.s.h.a * c.b) :
    (c.s.t * u)⁻¹ * c.s.h.a * (c.s.t * u) = c.s.h.a * c.b * c.Z.z := by
  have h1 := c.conj_t_a
  have hzu : u * c.Z.z = c.Z.z * u := c.Z.hzS u hu
  calc (c.s.t * u)⁻¹ * c.s.h.a * (c.s.t * u) = u⁻¹ * (c.s.t⁻¹ * c.s.h.a * c.s.t) * u := by group
    _ = u⁻¹ * (c.Z.z * u) * (u⁻¹ * c.b * u) := by rw [h1]; group
    _ = c.Z.z * (c.s.h.a * c.b) := by rw [← hzu, hub]; group
    _ = c.s.h.a * c.b * c.Z.z := by
        rw [← mul_assoc, c.hza, mul_assoc, ← c.hbz, ← mul_assoc]

theorem conj_tu_z {u : X} (hu : u ∈ c.s.h.S) (hub : u⁻¹ * c.b * u = c.s.h.a * c.b) :
    (c.s.t * u)⁻¹ * c.Z.z * (c.s.t * u) = c.b := by
  have hau : u⁻¹ * c.s.h.a * u = c.s.h.a := by
    rw [mul_assoc, ← c.s.h.comm_a hu, ← mul_assoc, inv_mul_cancel, one_mul]
  calc (c.s.t * u)⁻¹ * c.Z.z * (c.s.t * u) = u⁻¹ * (c.s.t⁻¹ * c.Z.z * c.s.t) * u := by group
    _ = (u⁻¹ * c.s.h.a * u) * (u⁻¹ * c.b * u) := by rw [c.hzb]; group
    _ = c.b := by rw [hau, hub, ← mul_assoc, Six.a_mul_a_self c.s.h, one_mul]

theorem z_mem_Lay : c.Z.z ∈ Seven.Lay c.s.h c.s.y :=
  Seven.J0_le_Lay c.s.h c.s.y (c.s.D_le_J0 c.Z.hzD)

theorem ab_mem_Lay : c.s.h.a * c.b ∈ Seven.Lay c.s.h c.s.y := by
  rw [← c.hzb]
  exact mul_mem (mul_mem (inv_mem c.htL) c.z_mem_Lay) c.htL

theorem delta_mem_Lay : c.s.h.a * c.b * c.Z.z ∈ Seven.Lay c.s.h c.s.y :=
  mul_mem c.ab_mem_Lay c.z_mem_Lay

theorem Lay_le_centralizer_b : Seven.Lay c.s.h c.s.y ≤ centralizer ({c.b} : Set X) := by
  intro w hw
  have h1 : w ∈ centralizer (Seven.B0 c.s.h c.s.y : Set X) := map_subtype_le _ hw
  exact mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp h1 c.b c.hbB).symm)

theorem isPComponent_inf_of_subnormal
    (hLb : ((Seven.Lay c.s.h c.s.y).subgroupOf (centralizer ({c.b} : Set X))).IsSubnormal)
    {δ : X} {N : Subgroup X} (hNX : N ≤ Seven.Lay c.s.h c.s.y ⊓ centralizer ({δ} : Set X))
    (hN : IsPComponent 2 (N.subgroupOf (Seven.Lay c.s.h c.s.y ⊓ centralizer ({δ} : Set X)))) :
    N ≤ centralizer ({c.b} : Set X) ⊓ centralizer ({δ} : Set X) ∧
      IsPComponent 2 (N.subgroupOf (centralizer ({c.b} : Set X) ⊓ centralizer ({δ} : Set X))) :=
  ⟨le_inf (hNX.trans (inf_le_left.trans c.Lay_le_centralizer_b)) (hNX.trans inf_le_right),
    Seven.isPComponent_inf_of_isSubnormal c.Lay_le_centralizer_b hLb hNX hN⟩

theorem a_not_mem_J : c.s.h.a ∉ c.s.h.J := by
  intro haJ
  have h1 : c.s.h.a ∈ c.s.h.D ⊓ c.s.h.P :=
    mem_inf.mpr ⟨mem_inf.mpr ⟨c.s.h.a_mem_S, haJ⟩, c.s.h.a_mem_P⟩
  rw [c.s.h.D_inf_P_eq_bot c.s.center_J, mem_bot] at h1
  have h2 := c.s.h.orderOf_a
  rw [h1, orderOf_one] at h2
  exact absurd h2 (by norm_num)

theorem ab_mul_ab : c.s.h.a * c.b * (c.s.h.a * c.b) = 1 := by
  calc c.s.h.a * c.b * (c.s.h.a * c.b) = c.s.h.a * (c.b * c.s.h.a) * c.b := by group
    _ = c.s.h.a * (c.s.h.a * c.b) * c.b := by rw [c.hba]
    _ = (c.s.h.a * c.s.h.a) * (c.b * c.b) := by group
    _ = 1 := by rw [Six.a_mul_a_self c.s.h, c.hbb, one_mul]

theorem ab_ne_one : c.s.h.a * c.b ≠ 1 := by
  intro h1
  apply c.Z.hz1
  have h2 : c.s.t⁻¹ * c.Z.z * c.s.t = 1 := by rw [c.hzb, h1]
  calc c.Z.z = c.s.t * (c.s.t⁻¹ * c.Z.z * c.s.t) * c.s.t⁻¹ := by group
    _ = 1 := by rw [h2]; group

theorem z_ne_ab : c.Z.z ≠ c.s.h.a * c.b := by
  intro h1
  apply c.Z.hzP
  rw [h1]
  exact mul_mem c.s.h.a_mem_P c.hbP

theorem ab_comm_z : c.s.h.a * c.b * c.Z.z = c.Z.z * (c.s.h.a * c.b) := by
  rw [mul_assoc, c.hbz, ← mul_assoc, ← c.hza, mul_assoc]

theorem J0_le_centralizer_ab :
    Seven.J0 c.s.h c.s.y ≤ centralizer ({c.s.h.a * c.b} : Set X) := by
  intro g hg
  obtain ⟨hga, hgB⟩ := mem_inf.mp (c.s.h.secJ0_le c.s.y hg)
  have h1 : Commute g c.s.h.a := mem_centralizer_singleton_iff.mp hga
  have h2 : Commute g c.b := (mem_centralizer_iff.mp hgB c.b c.hbB).symm
  exact mem_centralizer_singleton_iff.mpr (h1.mul_right h2)

theorem Lay_inf_centralizer_ab_le :
    Seven.Lay c.s.h c.s.y ⊓ centralizer ({c.s.h.a * c.b} : Set X) ≤
      centralizer ({c.s.h.a} : Set X) ⊓ centralizer (c.s.h.secB0 c.s.y : Set X) := by
  intro g hg
  obtain ⟨hgL, hgab⟩ := mem_inf.mp hg
  have hgB : g ∈ centralizer (c.s.h.secB0 c.s.y : Set X) := map_subtype_le _ hgL
  have h1 : Commute g (c.s.h.a * c.b) := mem_centralizer_singleton_iff.mp hgab
  have h2 : Commute g c.b := (mem_centralizer_iff.mp hgB c.b c.hbB).symm
  have h3 : Commute g (c.s.h.a * c.b * c.b⁻¹) := h1.mul_right h2.inv_right
  rw [mul_inv_cancel_right] at h3
  exact mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr h3, hgB⟩

theorem isSec8JType_J0 :
    IsSec8JType (↥(Seven.J0 c.s.h c.s.y) ⧸ pPrimeCore 2 ↥(Seven.J0 c.s.h c.s.y)) c.s.p c.s.f := by
  obtain ⟨eJ⟩ := c.s.sec_J_equiv
  obtain ⟨e0⟩ := Hyp52.nonempty_secJ0_equiv (h := c.s.h) (y := c.s.y)
  exact CatFactsL4U4.Cover82.isSec8JType_of_mulEquiv (eJ.trans e0.symm) c.s.J_type

theorem lieModel_Lay
    (hA : ¬ Nonempty (↥(generalizedFitting (c.s.h.subQuot c.s.y)) ≃* alternatingGroup (Fin 10))) :
    Blueprint.LieModel (↥(Seven.Lay c.s.h c.s.y) ⧸ pPrimeCore 2 ↥(Seven.Lay c.s.h c.s.y)) .PSL 4
        c.s.p c.s.f ∧ c.s.p ^ c.s.f % 4 = 3 ∨
      Blueprint.LieModel (↥(Seven.Lay c.s.h c.s.y) ⧸ pPrimeCore 2 ↥(Seven.Lay c.s.h c.s.y)) .PSU 4
        c.s.p c.s.f ∧ c.s.p ^ c.s.f % 4 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L := Seven.Lay c.s.h c.s.y with hL
  have hF : Blueprint.LieModel ↥(generalizedFitting (c.s.h.subQuot c.s.y)) .PSL 4 c.s.p c.s.f ∨
      Blueprint.LieModel ↥(generalizedFitting (c.s.h.subQuot c.s.y)) .PSU 4 c.s.p c.s.f := by
    rcases c.s.type with h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
    · exact absurd h1 hA
  have hLC : L ≤ centralizer (Seven.B0 c.s.h c.s.y : Set X) := map_subtype_le _
  have hq : IsQuasisimple (↥L ⧸ pPrimeCore 2 ↥L) :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 L _ hLC).mp c.s.L_pc).2.2
  have hZ2 : IsPGroup 2 (center (↥L ⧸ pPrimeCore 2 ↥L)) :=
    CatFactsL4U4.isPGroup_two_center_of_pPrimeCore_eq_bot
      (pPrimeCore_quotient_pPrimeCore_eq_bot 2)
  obtain ⟨eF⟩ := c.s.L_equiv
  let eZ := (oddBarCenterEquiv ↥L).trans eF
  obtain ⟨hMt, hMpc, ⟨eM⟩⟩ := Seven.isPComponent_map_of_le_inf c.ab_mem_Lay c.ab_mul_ab
    (Seven.J0_le_Lay c.s.h c.s.y) c.J0_le_centralizer_ab c.Lay_inf_centralizer_ab_le
    (Hyp52.isPComponent_secJ0 (h := c.s.h) (y := c.s.y))
  have hℓ : QuotientGroup.mk' (pPrimeCore 2 ↥L) (⟨c.s.h.a * c.b, c.ab_mem_Lay⟩ : ↥L) *
      QuotientGroup.mk' (pPrimeCore 2 ↥L) ⟨c.s.h.a * c.b, c.ab_mem_Lay⟩ = 1 := by
    rw [← map_mul, show (⟨c.s.h.a * c.b, c.ab_mem_Lay⟩ : ↥L) * ⟨c.s.h.a * c.b, c.ab_mem_Lay⟩ = 1
      from Subtype.ext c.ab_mul_ab, map_one]
  have hZ := CatFactsL4U4.Cover82.center_eq_bot_of_isPGroup_center c.s.hp c.s.hp2 c.s.hf hq hZ2
    (hF.imp (LieType.CurtisTits.lieModel_of_mulEquiv eZ.symm)
      (LieType.CurtisTits.lieModel_of_mulEquiv eZ.symm)) hℓ hMt hMpc
    (CatFactsL4U4.Cover82.isSec8JType_of_mulEquiv eM c.isSec8JType_J0)
  let e₁ : (↥L ⧸ pPrimeCore 2 ↥L) ≃* ↥(generalizedFitting (c.s.h.subQuot c.s.y)) :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans eZ
  rcases hF with h1 | h1
  · exact Or.inl ⟨LieType.CurtisTits.lieModel_of_mulEquiv e₁.symm h1, c.s.mod4_L h1⟩
  · exact Or.inr ⟨LieType.CurtisTits.lieModel_of_mulEquiv e₁.symm h1, c.s.mod4_U h1⟩

end CtxA0

end Eight2

end CFSG.ComponentClassification.GSThmB
