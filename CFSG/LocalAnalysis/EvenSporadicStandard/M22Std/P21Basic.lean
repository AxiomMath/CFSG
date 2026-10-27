module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResH4Norm
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.LayerA10Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.XbarCentralizer
import CFSG.Walter.Cited.OddQuotient
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.Open CFSG.EvenSporadicStandard.M24Std CFSG.EvenSporadicStandard.M23Std

theorem fusionOddCore_z2s6 :
    fusionOddCore (Multiplicative (ZMod 2) × Equiv.Perm (Fin 6)) = ⊥ :=
  CResH4.normal_z2s6_eq_bot_of_odd _ inferInstance (natCard_fusionOddCore_odd _)

variable {G : Type} [Group G] [Finite G] {z : G}

theorem fusionOddCore_centralizer_eq_bot
    (hC : Nonempty (↥(centralizer ({z} : Set G)) ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 6))) :
    fusionOddCore ↥(centralizer ({z} : Set G)) = ⊥ := by
  obtain ⟨e⟩ := hC
  exact fusionOddCore_eq_bot_of_equiv e fusionOddCore_z2s6

theorem centralizer_quot_oddCore_equiv
    (hC : Nonempty (↥(centralizer ({z} : Set G)) ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 6))) :
    Nonempty (↥(centralizer ({z} : Set G)) ⧸ fusionOddCore ↥(centralizer ({z} : Set G)) ≃*
      Multiplicative (ZMod 2) × Equiv.Perm (Fin 6)) := by
  obtain ⟨e⟩ := id hC
  have hbot := fusionOddCore_centralizer_eq_bot hC
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot).trans e⟩

theorem inf_fusionOddCore_centralizer_eq_bot
    (hC : Nonempty (↥(centralizer ({z} : Set G)) ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 6))) :
    fusionOddCore G ⊓ centralizer ({z} : Set G) = ⊥ := by
  have hn := inf_centralizer_subgroupOf_normal (E := fusionOddCore G) inferInstance z
  have hodd : Odd (Nat.card ((fusionOddCore G ⊓ centralizer ({z} : Set G)).subgroupOf
      (centralizer ({z} : Set G)))) := by
    have h1 : Nat.card ((fusionOddCore G ⊓ centralizer ({z} : Set G)).subgroupOf
        (centralizer ({z} : Set G))) = Nat.card (fusionOddCore G ⊓ centralizer ({z} : Set G) :
          Subgroup G) := by
      rw [← Subgroup.card_map_of_injective (centralizer ({z} : Set G)).subtype_injective
        (K := (fusionOddCore G ⊓ centralizer ({z} : Set G)).subgroupOf
          (centralizer ({z} : Set G))), Subgroup.subgroupOf_map_subtype, inf_assoc, inf_idem]
    rw [h1]
    exact Odd.of_dvd_nat (natCard_fusionOddCore_odd G) (Subgroup.card_dvd_of_le inf_le_left)
  have hle := le_fusionOddCore_of_odd (X := ↥(centralizer ({z} : Set G))) hodd
  rw [fusionOddCore_centralizer_eq_bot hC, le_bot_iff] at hle
  rw [eq_bot_iff]
  intro x hx
  have hx' : (⟨x, (mem_inf.1 hx).2⟩ : ↥(centralizer ({z} : Set G))) ∈
      (fusionOddCore G ⊓ centralizer ({z} : Set G)).subgroupOf (centralizer ({z} : Set G)) :=
    mem_subgroupOf.2 hx
  rw [hle, mem_bot] at hx'
  exact mem_bot.2 (congrArg Subtype.val hx')

@[expose] noncomputable def centralizerMk (z : G) :
    ↥(centralizer ({z} : Set G)) →*
      ↥(centralizer ({QuotientGroup.mk' (fusionOddCore G) z} : Set (G ⧸ fusionOddCore G))) where
  toFun c := ⟨QuotientGroup.mk' (fusionOddCore G) (c : G), by
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      mem_centralizer_singleton_iff.1 c.2]⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul _ _ _)

omit [Finite G] in
@[simp] theorem coe_centralizerMk (z : G) (c : ↥(centralizer ({z} : Set G))) :
    ((centralizerMk z c : ↥(centralizer ({QuotientGroup.mk' (fusionOddCore G) z} :
      Set (G ⧸ fusionOddCore G)))) : G ⧸ fusionOddCore G) =
      QuotientGroup.mk' (fusionOddCore G) (c : G) := rfl

theorem centralizerMk_bijective (hz : orderOf z = 2)
    (h : fusionOddCore G ⊓ centralizer ({z} : Set G) = ⊥) :
    Function.Bijective (centralizerMk z) := by
  have htt : z * z = 1 := by rw [← sq, ← hz, pow_orderOf_eq_one]
  constructor
  · rw [injective_iff_map_eq_one]
    intro c hc
    have h1 : QuotientGroup.mk' (fusionOddCore G) (c : G) = 1 := congrArg Subtype.val hc
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have : (c : G) ∈ fusionOddCore G ⊓ centralizer ({z} : Set G) := mem_inf.2 ⟨h1, c.2⟩
    rw [h, mem_bot] at this
    exact Subtype.ext this
  · intro y
    have hy := CFSG.Walter.Suzuki.centralizer_mk_le_map (fusionOddCore G)
      (natCard_fusionOddCore_odd G) htt y.2
    obtain ⟨c, hc, hcy⟩ := hy
    exact ⟨⟨c, hc⟩, Subtype.ext hcy⟩

noncomputable def centralizerMkEquiv (hz : orderOf z = 2)
    (h : fusionOddCore G ⊓ centralizer ({z} : Set G) = ⊥) :
    ↥(centralizer ({z} : Set G)) ≃*
      ↥(centralizer ({QuotientGroup.mk' (fusionOddCore G) z} : Set (G ⧸ fusionOddCore G))) :=
  MulEquiv.ofBijective (centralizerMk z) (centralizerMk_bijective hz h)

end CFSG.EvenSporadicStandard.M22Std
