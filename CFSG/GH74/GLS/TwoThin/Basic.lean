module

public import CFSG.GH74.GLS.AssemblyComponents
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingPrime

public section

namespace CFSG.GH74.GLS.TwoThin

open Subgroup Blueprint Assembly.LowTwoRank CFSG.ComponentClassification

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isPCompIn_two_iff {X K : Subgroup G} :
    IsPCompIn 2 X K ↔ K ≤ X ∧ TwoComponents.IsTwoComponent (K.subgroupOf X) :=
  and_congr_right fun _ => CatalogueBAlternating.pComponent_two_iff _

theorem isQuasisimple_hat_of_isPComponent {C : Type} [Group C] [Finite C] {L : Subgroup C}
    (hL : IsPComponent 2 L) : IsQuasisimple (↥L ⧸ pPrimeCore 2 ↥L) := by
  obtain ⟨Kc, hKc, hsub, hmap, -⟩ := hL
  let π : C →* C ⧸ pPrimeCore 2 C := QuotientGroup.mk' (pPrimeCore 2 C)
  let φ : ↥L →* ↥Kc := (π.comp L.subtype).codRestrict Kc fun l => by
    rw [← hmap]
    exact ⟨l, l.2, rfl⟩
  have hφ : Function.Surjective φ := by
    intro k
    have hk : (k : C ⧸ pPrimeCore 2 C) ∈ L.map π := by
      rw [hmap]
      exact k.2
    obtain ⟨c, hc, hck⟩ := hk
    exact ⟨⟨c, hc⟩, Subtype.ext hck⟩
  have hker : φ.ker = pPrimeCore 2 ↥L := by
    rw [MonoidHom.ker_codRestrict]
    exact ker_restrict_eq_pPrimeCore hsub
  let e : (↥L ⧸ φ.ker) ≃* ↥Kc := QuotientGroup.quotientKerEquivOfSurjective φ hφ
  let e' : (↥L ⧸ pPrimeCore 2 ↥L) ≃* (↥L ⧸ φ.ker) := QuotientGroup.quotientMulEquivOfEq hker.symm
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (e'.trans e).symm hKc.1

theorem isQuasisimple_hat {X K : Subgroup G} (hK : IsPCompIn 2 X K) :
    IsQuasisimple (↥K ⧸ pPrimeCore 2 ↥K) := by
  have h := isQuasisimple_hat_of_isPComponent hK.2
  let e := Subgroup.subgroupOfEquivOfLe hK.1
  have hmap := pPrimeCore_map_iso 2 e
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (QuotientGroup.congr _ _ e hmap) h

omit [Finite G] in
theorem pPrimeCoreOf_le (K : Subgroup G) : pPrimeCoreOf 2 K ≤ K := by
  rintro _ ⟨o, -, rfl⟩
  exact o.2

theorem card_pPrimeCoreOf_odd (K : Subgroup G) : Odd (Nat.card (pPrimeCoreOf 2 K)) := by
  unfold pPrimeCoreOf
  rw [Subgroup.card_map_of_injective K.subtype_injective]
  exact Nat.coprime_two_left.mp pPrimeCore_coprime_card

omit [Finite G] in
theorem pPrimeCoreOf_normalized (K : Subgroup G) {k : G} (hk : k ∈ K) {o : G}
    (ho : o ∈ pPrimeCoreOf 2 K) : k * o * k⁻¹ ∈ pPrimeCoreOf 2 K := by
  obtain ⟨o', ho', rfl⟩ := ho
  refine ⟨⟨k, hk⟩ * o' * ⟨k, hk⟩⁻¹, ?_, by simp⟩
  exact (inferInstance : (pPrimeCore 2 ↥K).Normal).conj_mem o' ho' ⟨k, hk⟩

end CFSG.GH74.GLS.TwoThin
