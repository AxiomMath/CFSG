module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResH4Core
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.LayerA10Basic
import CFSG.Walter.Cited.OddQuotient

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup CFSG.Open

theorem central_of_layer_alt6 {Y : Type} [Group Y] [Finite Y] {z : Y} (hz : z * z = 1)
    (φ : (Subgroup.centralizer ({z} : Set Y)) →* Multiplicative (ZMod 2) × Equiv.Perm (Fin 6))
    (hφ : Function.Surjective φ) (hk : Nat.card φ.ker = 3) (hA6 : AutA6Table)
    (e : Nonempty (egaLayer (Y ⧸ fusionOddCore Y) ≃* alternatingGroup (Fin 6))) :
    ∀ y : Y, ∃ o ∈ fusionOddCore Y, ∃ p ∈ Subgroup.centralizer ({z} : Set Y), y = o * p := by
  obtain ⟨e⟩ := e
  have : (egaLayer (Y ⧸ fusionOddCore Y)).Normal := egaLayer_normal _
  have hπs : Function.Surjective (QuotientGroup.mk' (fusionOddCore Y)) :=
    QuotientGroup.mk'_surjective _
  have hcop : centralizer ({QuotientGroup.mk' (fusionOddCore Y) z} :
      Set (Y ⧸ fusionOddCore Y)) ≤
      (centralizer ({z} : Set Y)).map (QuotientGroup.mk' (fusionOddCore Y)) :=
    CFSG.Walter.Suzuki.centralizer_mk_le_map (fusionOddCore Y) (odd_natCard_fusionOddCore Y) hz
  have hodd : Odd (Nat.card (QuotientGroup.mk' (fusionOddCore Y)).ker) := by
    rw [QuotientGroup.ker_mk']
    exact odd_natCard_fusionOddCore Y
  have hker : ∀ p : centralizer ({z} : Set Y), QuotientGroup.mk' (fusionOddCore Y) (p : Y) = 1 →
      φ p = 1 := fun p hp => CResH4.map_eq_one_of_odd_ker _ hodd φ hφ p hp
  have hX : ∀ N : Subgroup (Y ⧸ fusionOddCore Y), N.Normal → Odd (Nat.card N) → N = ⊥ := by
    intro N hN hodd'
    have h := standardComponentOddCore_quotient_fusionOddCore_eq_bot Y
    exact le_bot_iff.1 (h ▸ le_sSup ⟨hN, hodd'⟩)
  intro y
  have hc := CResH4.conj_eq_of_layer hA6 (QuotientGroup.mk' (fusionOddCore Y)) hπs hz hcop φ hφ hk
    hker hX _ e (QuotientGroup.mk' (fusionOddCore Y) y)
  have hcomm : QuotientGroup.mk' (fusionOddCore Y) y * QuotientGroup.mk' (fusionOddCore Y) z =
      QuotientGroup.mk' (fusionOddCore Y) z * QuotientGroup.mk' (fusionOddCore Y) y :=
    mul_inv_eq_iff_eq_mul.1 hc
  obtain ⟨p, hp, hpy⟩ := hcop (mem_centralizer_singleton_iff.2 hcomm)
  refine ⟨y * p⁻¹, ?_, p, hp, by group⟩
  rw [← QuotientGroup.ker_mk' (fusionOddCore Y), MonoidHom.mem_ker, map_mul, map_inv, hpy,
    mul_inv_cancel]

end CFSG.EvenSporadicStandard.M24Std
