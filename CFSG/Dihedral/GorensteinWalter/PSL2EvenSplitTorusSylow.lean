module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2RootGroups
import CFSG.Assembly.OrderReductions.EigenlineGeometry
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2FixedPointBound
import CFSG.GroupTheory.SL2OddSplitTorus
import CFSG.GroupTheory.SylowMulAutTransport
import CFSG.LocalAnalysis.ShultStronglyClosedTI.LinearModelPointStructureBasic

public section

namespace CFSG

noncomputable section

namespace GorensteinWalter

open scoped MatrixGroups

open CFSG.GH74.GLS.IVK.L2Torus

attribute [local instance] Fintype.ofFinite

theorem psl2_even_exists_sylow_normalizer
    {F : Type} [Field F] [Finite F] [CharP F 2]
    {y : PSL2 F} (hy1 : y ≠ 1) (hyq : y ^ (Nat.card F - 1) = 1) :
    ∃ ω : Sylow 2 (PSL2 F),
      y ∈ Subgroup.normalizer ((ω : Subgroup (PSL2 F)) : Set (PSL2 F)) := by
  classical
  obtain ⟨n, -, hFc⟩ := FiniteField.card F 2
  have hF : Nat.card F = 2 ^ (n : ℕ) := by
    rw [Nat.card_eq_fintype_card, hFc]
  have hqinj := CFSG.ShultStronglyClosedTI.LinearModel.psl2QuotientMap_injective (K := F)
  obtain ⟨z, hz⟩ := psl2QuotientMap_surjective (K := F) y
  have hz1 : z ≠ 1 := by
    intro h
    exact hy1 (by rw [← hz, h, map_one])
  have hzq : z ^ (Nat.card F - 1) = 1 := by
    apply hqinj
    rw [map_pow, hz, hyq, map_one]
  have hzdvd : orderOf z ∣ Nat.card F - 1 :=
    orderOf_dvd_iff_pow_eq_one.mpr hzq
  have hpos : 1 ≤ Nat.card F := by
    rw [hF]
    exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by norm_num))
  have hEven : Even (Nat.card F) := by
    rw [hF, Nat.even_pow]
    exact ⟨even_two, n.pos.ne'⟩
  have hoddOrd : Odd (orderOf z) :=
    (Nat.Even.sub_odd hpos hEven odd_one).of_dvd_nat hzdvd
  obtain ⟨P, hP⟩ :=
    CFSG.GroupTheory.exists_conj_mem_diagSub_of_odd_order_dvd_card_sub_one
      (F := F) hoddOrd hzdvd hz1
  let d : SL2m F := P⁻¹ * z * P
  have hdmem : d ∈ diagSub F := hP
  have hdinf : d • psl2ProjectiveInfinity F = psl2ProjectiveInfinity F := by
    rw [← MulAction.mem_stabilizer_iff]
    exact (sl2_mem_stabilizer_infinity_iff d).mpr (mem_diagSub.mp hdmem).2
  have hzd : z * P = P * d := by
    change z * P = P * (P⁻¹ * z * P)
    group
  set x : PSL2ProjectiveLine F := P • psl2ProjectiveInfinity F with hx
  have hyx : y • x = x := by
    rw [← hz]
    rw [psl2QuotientMap_smul]
    calc
      z • x = z • (P • psl2ProjectiveInfinity F) := by rw [hx]
      _ = (z * P) • psl2ProjectiveInfinity F := by rw [mul_smul]
      _ = (P * d) • psl2ProjectiveInfinity F := by rw [hzd]
      _ = P • (d • psl2ProjectiveInfinity F) := by rw [mul_smul]
      _ = P • psl2ProjectiveInfinity F := by rw [hdinf]
      _ = x := by rw [hx]
  refine ⟨psl2ProjectiveLineEquivSylow F hF x, ?_⟩
  rw [← psl2ProjectiveLineEquivSylow_stabilizer F hF x]
  exact MulAction.mem_stabilizer_iff.mpr hyx

theorem psl2_even_normalizerSylow_natCard_le_two
    {F : Type} [Field F] [Finite F] [CharP F 2]
    {y : PSL2 F} (hy1 : y ≠ 1) :
    Nat.card {ω : Sylow 2 (PSL2 F) //
      y ∈ Subgroup.normalizer ((ω : Subgroup (PSL2 F)) : Set (PSL2 F))} ≤ 2 := by
  classical
  obtain ⟨n, -, hFc⟩ := FiniteField.card F 2
  have hF : Nat.card F = 2 ^ (n : ℕ) := by
    rw [Nat.card_eq_fintype_card, hFc]
  let e := psl2ProjectiveLineEquivSylow F hF
  have hiff : ∀ x : PSL2ProjectiveLine F,
      y • x = x ↔
        y ∈ Subgroup.normalizer ((e x : Subgroup (PSL2 F)) : Set (PSL2 F)) := by
    intro x
    change y • x = x ↔
      y ∈ Subgroup.normalizer
        ((psl2ProjectiveLineEquivSylow F hF x : Subgroup (PSL2 F)) : Set (PSL2 F))
    rw [← psl2ProjectiveLineEquivSylow_stabilizer F hF x]
    exact MulAction.mem_stabilizer_iff.symm
  let toS : {x : PSL2ProjectiveLine F // y • x = x} ≃
      {ω : Sylow 2 (PSL2 F) //
        y ∈ Subgroup.normalizer ((ω : Subgroup (PSL2 F)) : Set (PSL2 F))} :=
    { toFun := fun x => ⟨e x.1, (hiff x.1).1 x.2⟩
      invFun := fun ω => ⟨e.symm ω.1, by
        rw [hiff]
        simpa using ω.2⟩
      left_inv := fun x => by
        apply Subtype.ext
        exact e.symm_apply_apply x.1
      right_inv := fun ω => by
        apply Subtype.ext
        exact e.apply_symm_apply ω.1 }
  calc
    Nat.card {ω : Sylow 2 (PSL2 F) //
        y ∈ Subgroup.normalizer ((ω : Subgroup (PSL2 F)) : Set (PSL2 F))} =
        Nat.card {x : PSL2ProjectiveLine F // y • x = x} := Nat.card_congr toS.symm
    _ ≤ 2 := psl2_fixedPoint_card_le_two F y hy1

theorem psl2_even_exists_sylow_fixed_of_fixes
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (A : Subgroup (MulAut (PSL2 F))) (hodd : Odd (Nat.card A))
    {y : PSL2 F} (hy1 : y ≠ 1)
    (hyq : y ^ (Nat.card F - 1) = 1)
    (hfix : ∀ a ∈ A, a y = y) :
    ∃ ω : Sylow 2 (PSL2 F),
      y ∈ Subgroup.normalizer ((ω : Subgroup (PSL2 F)) : Set (PSL2 F)) ∧
        ∀ a ∈ A, a • ω = ω := by
  classical
  obtain ⟨ω, hωN⟩ := psl2_even_exists_sylow_normalizer hy1 hyq
  have hS : Nat.card {σ : Sylow 2 (PSL2 F) //
      y ∈ Subgroup.normalizer ((σ : Subgroup (PSL2 F)) : Set (PSL2 F))} ≤ 2 :=
    psl2_even_normalizerSylow_natCard_le_two hy1
  have hfiniteA : Finite ↥A := by
    have hposA : 0 < Nat.card ↥A := Nat.pos_of_ne_zero (by
      intro h0
      rw [h0] at hodd
      exact Nat.not_odd_zero hodd)
    exact (Nat.card_pos_iff.mp hposA).2
  let toS : MulAction.orbit ↥A ω →
      {σ : Sylow 2 (PSL2 F) //
        y ∈ Subgroup.normalizer ((σ : Subgroup (PSL2 F)) : Set (PSL2 F))} :=
    fun σ => ⟨σ.1, by
      obtain ⟨a, ha⟩ := σ.2
      rw [← ha]
      exact CFSG.GroupTheory.mem_normalizer_smul_sylow_of_apply_eq
        (a : MulAut (PSL2 F)) (hfix (a : MulAut (PSL2 F)) a.2) hωN⟩
  have hsmall : Nat.card (MulAction.orbit ↥A ω) ≤ 2 := by
    refine (Nat.card_le_card_of_injective toS ?_).trans ?_
    · intro σ τ h
      apply Subtype.ext
      simpa using
        congrArg (fun u : {σ : Sylow 2 (PSL2 F) //
          y ∈ Subgroup.normalizer ((σ : Subgroup (PSL2 F)) : Set (PSL2 F))} => u.1) h
    · exact hS
  have hfixA : ∀ a : ↥A, a • ω = ω :=
    @CFSG.OrderReductions.EigenlineGeometry.odd_action_small_orbit_fixed
      ↥A (Sylow 2 (PSL2 F)) _ hfiniteA _ (by simpa using hodd) ω hsmall
  exact ⟨ω, hωN, fun a ha => hfixA ⟨a, ha⟩⟩

end GorensteinWalter

end

end CFSG
