module

public import CFSG.ClassicalInvolution.Q3.Q3T7M02

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

namespace Asc77.AscE186

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.AscE186
open CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem lemma33 (hΩ : HypOmegaGen Ω) {K R V : Subgroup G} (hK : K ∈ Ω) (hR : IsSylow2In R K)
    (hV : IsPGroup 2 ↥V) (hVK : V ≤ Subgroup.normalizer (K : Set G)) (hVR : Commutes V R) :
    ⁅V, K⁆ ≤ oddCoreOf K :=
  Subgroup.commutator_le.mpr fun v hv k hk =>
    Disconnected.AschTight.Sec6Gen.centSylow hΩ hK hR hV
      (fun _ hy => mem_normalizer_iff_conjSub_eq.mp (hVK hy))
      (fun r hr w hw => (hVR w hw r hr).symm) k hk v hv

theorem commutes_sylow_of_mem_omegaNbr (hΩ : HypOmega Ω) {K J : Subgroup G} (hK : K ∈ Ω)
    (hJ : J ∈ omegaNbr Ω K) {V : Subgroup G} (hV : IsSylow2In V K) : Commutes V J := by
  have hΩg : HypOmegaMod Ω := hΩ.toGen
  have hΩm : Q3T7M.HM Ω := hΩ.toMod
  obtain ⟨R, T, hR, hTsyl, hTN, hcomm⟩ := exists_commuting_sylow_pair hΩm hK hJ
  obtain ⟨hJΩ, hne, -⟩ := hJ
  have hT2 : IsPGroup 2 ↥T := hTsyl.2.1
  have hTK : Commutes T K :=
    commutes_of_commutator_le_oddCoreOf_of_exact (oddCoreOf_eq_bot_of_exact hΩ.exact hK)
      (lemma33 hΩg hK hR hT2 hTN hcomm.symm)
  obtain ⟨t, ht⟩ := hΩg.exists_uniqueInvolution hJΩ
  have h8T : 8 ≤ Nat.card T := hΩg.eight_le_of_mem_RSet (mem_RSet_of_isSylow2In hJΩ hTsyl)
  have htT : t ∈ T := AscL62.mem_of_uniqueInvolution_of_pGroup ht hTsyl.1 hT2 (by omega)
  have h8V := hΩg.eight_le_of_mem_RSet (mem_RSet_of_isSylow2In hK hV)
  have hVc : V ≤ Subgroup.centralizer ({t} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hTK t htT x (hV.1 hx)).symm
  have hVN : V ≤ Subgroup.normalizer (J : Set G) :=
    hΩg.le_normalizer_of_le_centralizer hJΩ hK hne ht hV.1 hV.2.1 (by omega) hVc
  have hVT : Commutes V T := fun x hx y hy => (hTK y hy x (hV.1 hx)).symm
  exact commutes_of_commutator_le_oddCoreOf_of_exact (oddCoreOf_eq_bot_of_exact hΩ.exact hJΩ)
    (lemma33 hΩg hJΩ hTsyl hV.2.1 hVN hVT)

end Asc77.AscE186

end CFSG.ClassicalInvolution.Q3.Q3T8
