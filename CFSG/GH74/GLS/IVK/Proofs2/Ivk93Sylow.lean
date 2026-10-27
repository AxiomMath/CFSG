module

public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Theorem5_1
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.GLS.Stage2.Local.Bar
public import CFSG.GH74.GLS.Stage2.Local.Basic
public import CFSG.GH74.GLS.Stage2.Local.P34Bar
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk93Adapt

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Local.P34


variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S : Subgroup G}

theorem card_barIn_S (hctx : Stage2Ctx G z k S) {H : Subgroup G} (hCH : Cen z ≤ H) :
    Nat.card ↥(barIn H S) = Nat.card ↥S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSH : S ≤ H := hctx.S_le_Cen.trans hCH
  have hS2 : IsPGroup 2 ↥S := (CFSG.ABGLocalTools.isSylowOf_iff.1 hctx.sylow_top).2.1
  let K : Subgroup ↥H := S.subgroupOf H
  have hK2 : IsPGroup 2 ↥K := hS2.of_equiv (Subgroup.subgroupOfEquivOfLe hSH).symm
  let f := (mkH H).subgroupMap K
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro s hs
    have h1 : mkH H (s : ↥H) = 1 := by
      have := congrArg Subtype.val hs
      exact this
    have hodd := odd_orderOf_of_mem_core H ((mkH_eq_one_iff H).1 h1)
    obtain ⟨n, hn⟩ := hK2 s
    have h2 : orderOf s ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn
    have h3 : orderOf (s : ↥H) = orderOf s := Subgroup.orderOf_coe s
    have h4 : orderOf s = 1 := by
      have hodd' : Odd (orderOf s) := by rwa [h3] at hodd
      exact Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right n (Nat.coprime_two_right.2 hodd')) h2
    exact orderOf_eq_one_iff.1 h4
  have hbij : Function.Bijective f := ⟨hinj, MonoidHom.subgroupMap_surjective _ K⟩
  have e : ↥K ≃* ↥(K.map (mkH H)) := MulEquiv.ofBijective f hbij
  calc Nat.card ↥(barIn H S) = Nat.card ↥(K.map (mkH H)) := rfl
    _ = Nat.card ↥K := (Nat.card_congr e.toEquiv).symm
    _ = Nat.card ↥S := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSH).toEquiv


theorem exists_sylow_barIn (hctx : Stage2Ctx G z k S) {H : Subgroup G} (hCH : Cen z ≤ H) :
    ∃ T : Sylow 2 (HBar H), (T : Subgroup (HBar H)) = barIn H S :=
  barIn_sylow H hctx.sylow_top (hctx.S_le_Cen.trans hCH)

theorem zbar_mem_barIn (hctx : Stage2Ctx G z k S) {H : Subgroup G} (hCH : Cen z ≤ H) :
    mkH H ⟨z, hCH (mem_Cen_self z)⟩ ∈ barIn H S :=
  Subgroup.mem_map.2 ⟨⟨z, hCH (mem_Cen_self z)⟩, Subgroup.mem_subgroupOf.2 hctx.z_mem, rfl⟩

theorem zbar_comm_barIn (hctx : Stage2Ctx G z k S) {H : Subgroup G} (hCH : Cen z ≤ H)
    {t : HBar H} (ht : t ∈ barIn H S) :
    t * mkH H ⟨z, hCH (mem_Cen_self z)⟩ = mkH H ⟨z, hCH (mem_Cen_self z)⟩ * t := by
  obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 ht
  have hsS : (s : G) ∈ S := Subgroup.mem_subgroupOf.1 hs
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (hctx.S_comm_z hsS)

theorem isCentralInvolution_zbar (hctx : Stage2Ctx G z k S) {H : Subgroup G} (hCH : Cen z ≤ H)
    (hzJ : mkH H ⟨z, hCH (mem_Cen_self z)⟩ ∈ generalizedFitting (HBar H)) :
    IsCentralInvolution (⟨mkH H ⟨z, hCH (mem_Cen_self z)⟩, hzJ⟩ : ↥(generalizedFitting (HBar H))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz2 : orderOf z = 2 := hctx.orderOf_z
  obtain ⟨T, hT⟩ := exists_sylow_barIn hctx hCH
  have : (generalizedFitting (HBar H)).Normal := LocalCores.generalized_fitting_characteristic.2
  obtain ⟨P, hP⟩ := Glauberman.sylow_inf_normal T (N := generalizedFitting (HBar H))
  refine ⟨?_, P, ?_, ?_⟩
  · rw [← Subgroup.orderOf_coe]
    exact orderOf_mk_eq_two H (by rw [← Subgroup.orderOf_coe]; exact hz2)
  · rw [hP, Subgroup.mem_subgroupOf]
    exact ⟨by rw [hT]; exact zbar_mem_barIn hctx hCH, hzJ⟩
  · intro s hs
    rw [hP, Subgroup.mem_subgroupOf] at hs
    have := zbar_comm_barIn hctx hCH (hT ▸ hs.1)
    exact Subtype.ext this

end CFSG.GH74.GLS.IVK.Proofs2.Ivk93Adapt
