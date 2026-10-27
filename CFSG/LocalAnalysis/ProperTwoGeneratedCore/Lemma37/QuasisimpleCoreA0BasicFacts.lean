module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreA0Basic
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreXQuotient

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J} {z u : J}
  {N : Subgroup J}

namespace A0Config

theorem le_of_odd_of_quasiNormalizer (hc : A0Config Q B z u N) {O : Subgroup J}
    (hOX : O ≤ quasiNormalizer (u * z))
    (hXO : quasiNormalizer (u * z) ≤ Subgroup.normalizer (O : Set J))
    (hodd : Odd (Nat.card O)) : O ≤ B := by
  by_contra hOB
  have h := hc.setting
  have hz := hc.fourGen
  obtain ⟨t, htQ, ht, htV⟩ := hz.exists_involution_not_mem_fourGroup h
  obtain ⟨htZ, htzZ, htzc⟩ := hc.not_mem_center_of_not_mem htQ ht htV
  have hcc := hc.mul_mul_self
  have htc : t * (u * z) = u * z * t := by
    calc t * (u * z) = t * (u * z) * t⁻¹ * t := by group
      _ = u * z * t := by rw [hc.conj_mul_eq_of_not_mem htQ ht htV]
  have hzc : z * (u * z) = u * z * z := by rw [← mul_assoc, ← hc.comm]
  have hcomm : t * z * (u * z) = u * z * (t * z) := by
    rw [mul_assoc, hzc, ← mul_assoc, htc, mul_assoc]
  have hzz := hz.mul_self
  rcases h.eq_of_commute_of_odd (B.mul_mem hc.mem_core (hz.mem_of_setting h)) hcc hOX hXO hodd
      hOB (h.sylow_le htQ) (hz.mem_of_setting h) (h.mem_quasiNormalizer_of_mul_eq hcc htc)
      (h.mem_quasiNormalizer_of_mul_eq hcc hzc) ht hzz htZ hz.not_mem_center htzc htzZ
      hcomm with h1 | h1
  · have htu : t = u := by
      calc t = t * z * z := by rw [mul_assoc, hzz, mul_one]
        _ = u := by rw [h1, mul_assoc, hzz, mul_one]
    rw [htu, hc.sq] at ht
    exact h.centralElt_ne_one ht
  · have htu : t = centralElt J * u := by
      calc t = t * z * z := by rw [mul_assoc, hzz, mul_one]
        _ = centralElt J * u := by rw [h1, mul_assoc, mul_assoc, hzz, mul_one]
    rw [htu, h.central_mul_central, hc.sq] at ht
    exact h.centralElt_ne_one ht

theorem quasiImage_ne_top (hc : A0Config Q B z u N) {z' : J}
    (hesc : EscapingLift B z' (u * z)) : quasiImage B (u * z) ≠ ⊤ := by
  intro htop
  set X := quasiNormalizer (u * z) with hX
  set N₀ := (CFSG.pPrimeCore 2 X).map X.subtype with hN₀
  have hN₀X : N₀ ≤ X := Subgroup.map_subtype_le _
  have hXN₀ : X ≤ Subgroup.normalizer (N₀ : Set J) := by
    intro x hx
    have hmem : (⟨x, hx⟩ : X) ∈
        Subgroup.normalizer ((CFSG.pPrimeCore 2 X : Subgroup X) : Set X) := by
      rw [Subgroup.normalizer_eq_top]
      exact Subgroup.mem_top _
    exact Subgroup.le_normalizer_map X.subtype (Subgroup.mem_map_of_mem X.subtype hmem)
  have hN₀odd : Odd (Nat.card N₀) := by
    rw [hN₀, Subgroup.card_map_of_injective X.subtype_injective]
    exact quasi_oddCore_odd (u * z)
  have hle := hc.le_of_odd_of_quasiNormalizer hN₀X hXN₀ hN₀odd
  apply hesc.subgroupOf_ne_top hc.setting
  have hker : (quasiMk (u * z)).ker ≤ B.subgroupOf X := by
    rw [QuotientGroup.ker_mk']
    exact fun o ho => Subgroup.mem_subgroupOf.mpr (hle ⟨o, ho, rfl⟩)
  have hcomap := congrArg (Subgroup.comap (quasiMk (u * z))) htop
  rwa [Subgroup.comap_map_eq_self hker, Subgroup.comap_top] at hcomap

end A0Config

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
