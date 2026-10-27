module

public import CFSG.LargeExtraspecial.AS35IMain
public import CFSG.LargeExtraspecial.AS62F431b
public import CFSG.LargeExtraspecial.AS62Insp
public import CFSG.LargeExtraspecial.AS62Mbar
import CFSG.LargeExtraspecial.AS62C36NormV
import CFSG.LargeExtraspecial.AS62C36Sub
import CFSG.LargeExtraspecial.AS62C36AutIso
import CFSG.LargeExtraspecial.AS62C36Tau

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
  CFSG.Quasithin.H13.F431.U42 CFSG.ComponentClassification.CatFactsSmall.PSp43
open scoped Pointwise

theorem lieModel_of_autCtx
    {G : Type} [Group G] [Finite G]
    {M₁ M₂ : Subgroup G} {z : G} (c : AutCtx G M₁ M₂ z) : LieModel G .PSL 4 3 1 := by
  obtain ⟨f₀, hf₀⟩ := u42AutModelGood
  let f' : Bh := ⟨f₀, hf₀.1⟩
  set f : G := c.iso.toG f' with hf
  have hgood : c.IsGoodAt f := ⟨f', hf₀, rfl⟩
  have hf2 : f ^ 2 = 1 := by
    have h1 : f' * f' = 1 := Subtype.ext (by simpa [sq] using hf₀.2.2.1)
    have := congrArg c.iso.toG h1
    rw [AutIso.toG_mul] at this
    have h0 : c.iso.toG 1 = 1 := by simp only [AutIso.toG, map_one, Subgroup.coe_one]
    rw [h0] at this
    rw [sq]
    exact this
  have hfB : f ∈ M₁ ⊓ M₂ := c.iso.toG_mem f'
  have hfp : IsPGroup 2 ↥(Subgroup.zpowers f) := by
    have hdvd : orderOf f ∣ 2 := orderOf_dvd_of_pow_eq_one hf2
    have hdvd' : orderOf f ∣ 2 ^ 1 := by rw [pow_one]; exact hdvd
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd'
    exact IsPGroup.of_card (n := m) (by rw [Nat.card_zpowers, hm])
  obtain ⟨T, hT, hfT⟩ := A4.exists_isSylowTwoOf_ge (Subgroup.zpowers_le.mpr hfB) hfp
  have hfT' : f ∈ T := hfT (Subgroup.mem_zpowers f)
  have hTp : IsPGroup 2 ↥(T ⊓ cenOf f) := hT.2.1.to_le inf_le_left
  obtain ⟨R, hR, hTR⟩ := A4.exists_isSylowTwoOf_ge (inf_le_right : T ⊓ cenOf f ≤ cenOf f) hTp
  have hconf := u42AutInv u42AutSylow (u42AutNotExtremal u42AutSylow u42AutFusion) u42AutFusionZ
    G M₁ M₂ z c T hT f hfT' hgood R hR hTR
  have h54 := u42AutF54 G M₁ M₂ z c T hT f hfT' hgood R hR hTR hconf
  have h55 := u42AutF55 G M₁ M₂ z c T hT f hfT' hgood R hR hTR hconf h54
  have h56 := u42AutF56 G M₁ M₂ z c T hT f hfT' hgood R hR hTR hconf h54 h55
  exact u42AutIdent_of_rho u42AutRho G M₁ M₂ z c T hT f hfT' hgood R hR hTR hconf h54 h55 h56

end CFSG.Quasithin.H13.F431.U42Aut

namespace CFSG.LargeExtraspecial

open Subgroup

namespace AS62

variable {G : Type} [Group G] [Finite G] {S : Setting G} {H : Subgroup G}

theorem ConfHyp.lieModel_of_card_Mbar_eq_36
    (hc : ConfHyp S H) (h : W2Hyp S)
    (htop : S.zGen ⊔ S.QG = ⊤) (h36 : Nat.card S.Mbar = 36) :
    CFSG.Blueprint.LieModel G .PSL 4 3 1 := by
  have h384 := hc.card_M_inf_normalizer_V h h36
  have h1920 := hc.card_normalizer_V_of_card_Mbar h h36
  obtain ⟨hO2, hzc, hnorm⟩ := hc.f431Side
  obtain ⟨M₀, hM₀, hB, hidx, ⟨φ⟩⟩ := hc.exists_subAmalgam h36
  obtain ⟨iso⟩ := hc.autIso_of_tau h384 h1920 M₀ hM₀ hB hidx φ
    (hc.tauMatch h36 h384 h1920 M₀ hM₀ hB hidx φ)
  exact CFSG.Quasithin.H13.F431.U42Aut.lieModel_of_autCtx
    (CFSG.Quasithin.H13.F431.U42Aut.AutCtx.ofSimple (hc.isSimpleGroup htop h.hsimp)
      hc.exists_not_commute iso hO2 (by rw [pow_two]; exact S.z_mul_z) S.z_ne_one hzc le_rfl
      (normalizer_centerOf_pCoreOf_M S) hnorm)

end AS62

namespace S14


theorem aschbacherWidthTwoResidual_holds : AschbacherWidthTwoResidual := by
  intro G _ _ S hw hW hO hsimp hC htop
  have h22 : S14.AschbacherTwoTwoStmt := S14.aschbacherTwoTwoStmt_of
  have h : AS62.W2Hyp S := ⟨hw, hW, hO, hsimp, hC⟩
  obtain ⟨H₁, hH₁⟩ := AS62.exists_isHSet h22 h
  obtain ⟨H, -, hmin⟩ := (Set.toFinite {H : Subgroup G | S.IsHSet H}).exists_le_minimal hH₁
  have hH : S.IsHStar H := ⟨hmin.prop, fun H' hH' hle => le_antisymm hle (hmin.2 hH' hle)⟩
  have hcf : AS62.ConfHyp S H := ⟨h22, hw, hW, hH⟩
  have hLie : CFSG.Blueprint.LieModel G .PSU 4 2 1 ∨ CFSG.Blueprint.LieModel G .PSL 4 3 1 := by
    have hmem := hcf.card_Mbar_mem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with h18 | h36 | h72
    · exact AS62.lieModel S h22 h htop hH h18
    · exact Or.inr (hcf.lieModel_of_card_Mbar_eq_36 h htop h36)
    · exact absurd (Subgroup.eq_top_of_card_eq _ (by rw [h72, hcf.card_O]))
        (AS62.mbar_ne_top h22 h)
  have hzG : S.zGen = ⊤ := hcf.zGen_eq_top htop
  have hGood : AS35W.W2Good S.zGen :=
    AS35W.W2Good.of_mulEquiv ((MulEquiv.subgroupCongr hzG).trans Subgroup.topEquiv)
      (AS62.w2Good_of_lieModel hLie)
  intro g₁ g₂
  have : S.zGen.Normal := S.zGen_normal
  have hzL : S.z ∈ S.zGen := S.z_mem_zGen
  have hD := S.w2Data_of_normal hzL hw hW hO hC
  have hconj : ∀ g : G, ∃ l : S.zGen, g * S.z * g⁻¹ = (l : G) * S.z * (l : G)⁻¹ := by
    intro g
    have hg : g ∈ S.zGen ⊔ S.QG := by rw [htop]; exact Subgroup.mem_top g
    obtain ⟨y, hy, q, hq, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hg
    refine ⟨⟨y, hy⟩, ?_⟩
    have hqz : q * S.z * q⁻¹ = S.z := by
      rw [S.mem_M_iff.mp (S.QG_le_M hq), mul_inv_cancel_right]
    calc y * q * S.z * (y * q)⁻¹ = y * (q * S.z * q⁻¹) * y⁻¹ := by group
      _ = y * S.z * y⁻¹ := by rw [hqz]
  obtain ⟨l₁, hl₁⟩ := hconj g₁
  obtain ⟨l₂, hl₂⟩ := hconj g₂
  rw [hl₁, hl₂]
  have hc := hGood _ hD l₁ l₂
  rw [← Subgroup.orderOf_coe] at hc
  simpa using hc

end S14

end CFSG.LargeExtraspecial
