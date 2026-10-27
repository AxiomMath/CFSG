module

public import CFSG.ClassicalInvolution.Q3.Sec13End10
import CFSG.ClassicalInvolution.Q3.TL3T25
import CFSG.ClassicalInvolution.Q3.TL3T29
public import CFSG.ClassicalInvolution.Asc77.AscE18FromM
public import CFSG.ClassicalInvolution.Asc77.AscFusionR7
public import CFSG.ClassicalInvolution.Asc77.AscP1SevenTwelve
public import CFSG.ClassicalInvolution.Asc77.AscT7AFinal
public import CFSG.ClassicalInvolution.Asc77.AscT7ASectD
public import CFSG.ClassicalInvolution.Asc77.AscT7CFinal
public import CFSG.ClassicalInvolution.Asc77.AscT7EFinal3
public import CFSG.ClassicalInvolution.Asc77.AscT7FJ
public import CFSG.ClassicalInvolution.Asc77.AscT7HFinal
public import CFSG.ClassicalInvolution.Asc77.AscT7QFinal
public import CFSG.ClassicalInvolution.Asc77.WP2Branch
public import CFSG.ClassicalInvolution.AschTight.S1916F2a
public import CFSG.ClassicalInvolution.Q3.OddCoreCentral
public import CFSG.ClassicalInvolution.Q3.Q3CPOmega
public import CFSG.ClassicalInvolution.Q3.Q3T7E9Comp
public import CFSG.ClassicalInvolution.Q3.Q3T7E9Main
public import CFSG.ClassicalInvolution.Q3.Q3T7LayerQ
public import CFSG.ClassicalInvolution.Q3.Q3T8Std8
public import CFSG.ClassicalInvolution.Q3.Q3TIMain
public import CFSG.ClassicalInvolution.Q3.Q3TIYOAMain
public import CFSG.ClassicalInvolution.Q3.Q3TKMem
public import CFSG.ClassicalInvolution.Q3.Q3WAEDict
public import CFSG.ClassicalInvolution.Q3.Q3WMain
public import CFSG.ClassicalInvolution.Q3.Q3ZFraStd
public import CFSG.ClassicalInvolution.Q3.RankThreeBootstrap
public import CFSG.ClassicalInvolution.Q3.Sec13StarBasic
public import CFSG.ClassicalInvolution.SmallCases.NobqFinal
public import CFSG.ClassicalInvolution.Uniform.U3IH8
public import CFSG.ClassicalInvolution.Uniform.U4Basic
public import CFSG.Sporadic.J4.QT2LocProof
public import CFSG.Sporadic.J4.QTOutChar
import CFSG.ClassicalInvolution.Asc77.AscT8V1
import CFSG.ClassicalInvolution.Asc77.AscT8V2
import CFSG.ClassicalInvolution.Asc77.AscT8V3
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FStarBasic
import CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge.CentQuotAEmpty
import CFSG.ClassicalInvolution.Q3.Q3DBFuzzyEdge
import CFSG.ClassicalInvolution.Q3.Q3KCGen
import CFSG.ClassicalInvolution.Q3.Q3NFLink
import CFSG.ClassicalInvolution.Q3.Q3T6BSymEx
import CFSG.ClassicalInvolution.Q3.TL3T28
import CFSG.ClassicalInvolution.Q3.TL4SepAlphaB
import CFSG.ClassicalInvolution.Q3.TL4SepMainB

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin

variable {G : Type} [Group G] [Finite G]

private theorem perm_fin3_not_commute :
    ∀ x y : Equiv.Perm (Fin 3), x ≠ 1 → x * x = 1 → y ≠ 1 → y * y = 1 → x ≠ y →
      x * y ≠ y * x := by
  decide

open CFSG.ClassicalInvolution.Asc77.Thompson in
private theorem exists_commuting_invol_pair {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω)
    {W K J : Subgroup G} (hW : W ∈ WSet Ω) (hKΩ : K ∈ Ω) (hKD : K ∈ DSet Ω W)
    (hJD : J ∈ DSet Ω W) (hK2 : IsPGroup 2 K) (hcomm : Commutes K J)
    {S : Subgroup G} (hS2 : IsPGroup 2 S) (hKS : K ≤ S) (hJS : J ≤ S) :
    ∃ a b : ↥(muGroup Ω W), a ≠ 1 ∧ b ≠ 1 ∧ a * a = 1 ∧ b * b = 1 ∧ a ≠ b ∧ a * b = b * a := by
  have hW2 : IsPGroup 2 W := isPGroup_of_mem_WSet hW
  have hKK : IsSylow2In K K := ⟨le_rfl, hK2, fun _ hV' _ hKV' => le_antisymm hV' hKV'⟩
  obtain ⟨k, hk, hkW⟩ := Q3CL.Thompson.exists_not_mem_of_mem_D hΩ hW hKD
  obtain ⟨k', hk', hk'W⟩ := Q3CL.Thompson.exists_not_mem_of_mem_D hΩ hW hJD
  have hkN : k ∈ Subgroup.normalizer (W : Set G) := hKD.2 hk
  have hk'N : k' ∈ Subgroup.normalizer (W : Set G) := hJD.2 hk'
  have ha2 : piG W k * piG W k = 1 := by
    rw [← piG_mul hkN hkN]
    exact piG_of_mem_sup (Subgroup.mem_sup_left (Q3CL.Thompson.D_sq_mem hΩ hW hKD hk))
  have hb2 : piG W k' * piG W k' = 1 := by
    rw [← piG_mul hk'N hk'N]
    exact piG_of_mem_sup (Subgroup.mem_sup_left (Q3CL.Thompson.D_sq_mem hΩ hW hJD hk'))
  have ha1 : piG W k ≠ 1 := fun h1 => D_not_mem_sup hW hKD hk hkW ((piG_eq_one_iff hkN).mp h1)
  have hb1 : piG W k' ≠ 1 := fun h1 =>
    D_not_mem_sup hW hJD hk' hk'W ((piG_eq_one_iff hk'N).mp h1)
  have hkk' : piG W k * piG W k' = piG W k' * piG W k := by
    refine (piG_comm_iff hkN hk'N).mpr ?_
    have h1 : k * k' * k⁻¹ * k'⁻¹ = 1 := by
      rw [hcomm k hk k' hk']
      group
    rw [h1]
    exact Subgroup.one_mem _
  have hne : piG W k ≠ piG W k' := by
    intro heq
    have hw : k⁻¹ * k' ∈ W :=
      mem_of_isPGroup_of_mem_sup_OCW hW2
        (hS2.to_le (Subgroup.zpowers_le.mpr (S.mul_mem (S.inv_mem (hKS hk)) (hJS hk'))))
        ((piG_eq_iff hkN hk'N).mp heq)
    obtain ⟨-, -, hcyc, h4, -⟩ := Q3CL.Thompson.inf_W_of_mem_D hΩ hW hKD hKΩ hKK
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥(K ⊓ W))
    have hgo : orderOf (g : G) = Nat.card ↥(K ⊓ W) := by
      rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg]
    have hgK : (g : G) ∈ K := g.2.1
    have hgW : (g : G) ∈ W := g.2.2
    have hwg := Q3CL.Thompson.commutes_of_mem_WSet hΩ hW _ (W.inv_mem hw) _ hgW
    have hkg : k * g = g * k := by
      calc k * g = k' * ((k⁻¹ * k')⁻¹ * g) := by group
        _ = k' * (g * (k⁻¹ * k')⁻¹) := by rw [hwg]
        _ = (k' * g) * (k⁻¹ * k')⁻¹ := by group
        _ = (g * k') * (k⁻¹ * k')⁻¹ := by rw [hcomm g hgK k' hk']
        _ = g * k := by group
    have hKc := Q3CL.Thompson.le_centralizer_of_mem hΩ hW hKD hk hkW hgW hkg
    have hgg := (Sec6Gen.isQuatSub_of_mem_RSet hΩ hKD.1).sq_eq_one_of_central hgK
      fun y hy => (Subgroup.mem_centralizer_singleton_iff.mp (hKc hy)).symm
    have h2 : orderOf (g : G) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hgg)
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  have hkmem : piG W k ∈ muGroup Ω W :=
    piG_mem_muGroup (Subgroup.mem_sup_left (le_MGrp_of_mem_D hKD hk))
  have hk'mem : piG W k' ∈ muGroup Ω W :=
    piG_mem_muGroup (Subgroup.mem_sup_left (le_MGrp_of_mem_D hJD hk'))
  exact ⟨⟨piG W k, hkmem⟩, ⟨piG W k', hk'mem⟩, fun h1 => ha1 (congrArg Subtype.val h1),
    fun h1 => hb1 (congrArg Subtype.val h1), Subtype.ext ha2, Subtype.ext hb2,
    fun h1 => hne (congrArg Subtype.val h1), Subtype.ext hkk'⟩

namespace EndHyp

variable {Ω : Set (Subgroup G)} (h : EndHyp Ω)
include h

private theorem involution_mem_of_mem_dSet {W : Subgroup G} (hW : W ∈ WSet Ω) {K : Subgroup G}
    (hK : K ∈ DSet Ω W) {z : G} (hz : IsUniqueInvolution K z) : z ∈ W := by
  have hKΩ : K ∈ Ω := (h.mem_dSet_iff.mp hK).1
  have hKK : IsSylow2In K K :=
    ⟨le_rfl, h.thmD.two K hKΩ, fun _ hV' _ hKV' => le_antisymm hV' hKV'⟩
  obtain ⟨-, -, -, h4, -⟩ := Q3CL.Thompson.inf_W_of_mem_D h.thmD.hyp hW hK hKΩ hKK
  exact (hz.mem_of_le inf_le_left ((h.thmD.two K hKΩ).to_le inf_le_left) (by omega)).2

theorem twinSet_eq_of_muIsoS3 (h9 : Perp9 Ω) {W : Subgroup G} (hW : W ∈ WSet Ω)
    (hS3 : MuIsoS3 Ω W) {K : Subgroup G} (hK : K ∈ DSet Ω W) : twinSet Ω K = {K} := by
  have hKΩ : K ∈ Ω := (h.mem_dSet_iff.mp hK).1
  obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution h.thmD.hyp hKΩ
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨hKΩ, z, hz, hz⟩, fun J hJ => ?_⟩
  obtain ⟨hJΩ, zJ, hzK, hzJ⟩ := hJ
  by_contra hJK
  have hzW : z ∈ W := h.involution_mem_of_mem_dSet hW hK hz
  have hJz : IsUniqueInvolution J z := by
    rw [← hzK.eq hz]
    exact hzJ
  have hJD : J ∈ DSet Ω W := h.mem_dSet_of_mem hW hJΩ hJz hzW
  have hcomm : Commutes K J :=
    TC.Thin.twin_comm h.thmD.hyp h.thmD.two hKΩ hJΩ (fun e => hJK e.symm) hz hJz
  have hK2 : IsPGroup 2 K := h.thmD.two K hKΩ
  have hJ2 : IsPGroup 2 J := h.thmD.two J hJΩ
  have hKN : K ≤ Subgroup.normalizer (J : Set G) := fun x hx =>
    Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun y hy => (hcomm x hx y hy).symm)
  have hKJ2 : IsPGroup 2 ↥(K ⊔ J) := hK2.to_sup_of_normal_right' hJ2 hKN
  have hKJW : IsPGroup 2 ↥((K ⊔ J) ⊔ W) :=
    hKJ2.to_sup_of_normal_right' (Asc77.Thompson.isPGroup_of_mem_WSet hW) (sup_le hK.2 hJD.2)
  obtain ⟨S, hS⟩ := hKJW.exists_le_sylow
  obtain ⟨a, b, ha1, hb1, ha2, hb2, hab, habc⟩ :=
    exists_commuting_invol_pair h.thmD.hyp hW hKΩ hK hJD hK2 hcomm S.isPGroup'
      (le_sup_left.trans (le_sup_left.trans hS)) (le_sup_right.trans (le_sup_left.trans hS))
  obtain ⟨φ⟩ := hS3
  exact perm_fin3_not_commute (φ a) (φ b)
    (fun e => ha1 (φ.injective (e.trans φ.map_one.symm)))
    (by rw [← map_mul, ha2, map_one])
    (fun e => hb1 (φ.injective (e.trans φ.map_one.symm)))
    (by rw [← map_mul, hb2, map_one])
    (fun e => hab (φ.injective e))
    (by rw [← map_mul, ← map_mul, habc])

theorem twinSet_eq_of_twinSet_eq {K : Subgroup G} (hK : K ∈ Ω) (hV : twinSet Ω K = {K})
    {L : Subgroup G} (hL : L ∈ Ω) : twinSet Ω L = {L} := by
  obtain ⟨g, rfl⟩ := h.thmD.trans K hK L hL
  have hgK : conjSub g K ∈ Ω := h.thmD.hyp.conjInvariant g K hK
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨?_, fun J hJ => ?_⟩
  · obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution h.thmD.hyp hgK
    exact ⟨hgK, z, hz, hz⟩
  · have h1 := twinSet_conj h.thmD.hyp.conjInvariant hJ g⁻¹
    rw [conjSub_inv_conjSub, hV, Set.mem_singleton_iff] at h1
    exact (conjSub_conjSub_inv g J).symm.trans (congrArg (conjSub g) h1)

theorem pCore_le_normalizer (h9 : Perp9 Ω) (hV : ∀ L ∈ Ω, twinSet Ω L = {L}) {K : Subgroup G}
    (hK : K ∈ Ω) : pCore 2 G ≤ Subgroup.normalizer (K : Set G) := by
  intro q hq
  rw [mem_normalizer_iff_conjSub_eq]
  by_contra hne
  have hL : conjSub q K ∈ Ω := h.thmD.hyp.conjInvariant q K hK
  have hQn : (pCore 2 G).Normal := CFSG.pCore_normal
  have hLle : conjSub q K ≤ K ⊔ pCore 2 G := by
    intro x hx
    rw [mem_conjSub_iff] at hx
    have hc : q * ((q⁻¹ * x * q) * q⁻¹ * (q⁻¹ * x * q)⁻¹) ∈ pCore 2 G :=
      Subgroup.mul_mem _ hq (hQn.conj_mem q⁻¹ (Subgroup.inv_mem _ hq) _)
    have hxe : x = (q * ((q⁻¹ * x * q) * q⁻¹ * (q⁻¹ * x * q)⁻¹)) * (q⁻¹ * x * q) := by
      group
    rw [hxe]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hc) (Subgroup.mem_sup_left hx)
  have hP2 : IsPGroup 2 ↥(K ⊔ pCore 2 G) :=
    (h.thmD.two K hK).to_sup_of_normal_right CFSG.pCore_isPGroup
  obtain ⟨S, hS⟩ := hP2.exists_le_sylow
  have hKS : K ≤ (S : Subgroup G) := le_sup_left.trans hS
  have hLS : conjSub q K ≤ (S : Subgroup G) := hLle.trans hS
  have hcomm : Commutes K (conjSub q K) :=
    Q3CP.l67Gen G Ω h.thmD.hyp S K (TC.mem_RSet_of_isPGroup hK (h.thmD.two K hK))
      (conjSub q K) (TC.mem_RSet_of_isPGroup hL (h.thmD.two _ hL)) hKS hLS
      (fun e => hne e.symm)
  obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution h.thmD.hyp hK
  obtain ⟨j, hj⟩ := Sec6Gen.exists_uniqueInvolution h.thmD.hyp hL
  have hzj : z = j := h9 K hK (conjSub q K) hL hcomm z j hz hj
  have htw : conjSub q K ∈ twinSet Ω K := ⟨hL, z, hz, by rw [hzj]; exact hj⟩
  rw [hV K hK, Set.mem_singleton_iff] at htw
  exact hne htw

end EndHyp

end CFSG.ClassicalInvolution.Q3.Sec13
