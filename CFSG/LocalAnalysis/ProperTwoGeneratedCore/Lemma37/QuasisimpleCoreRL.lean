module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreZSummary
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCorePConfig
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCorePSetup

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open CFSG.Open

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J} {z u : J}

theorem BadLift.exists_partC_of_ne_top
    (hu : BadLift B z u) (h : Setting J Q B)
    (hz : FourGen Q z) (IH : CanonicalBelow (Nat.card J)) (hne : quasiImage B u ≠ ⊤) :
    ∃ T : Sylow 2 (quasiNormalizer u),
      (T : Subgroup (quasiNormalizer u)) ≤ B.subgroupOf (quasiNormalizer u) ∧
      quasiSelf u ∈ (T : Subgroup (quasiNormalizer u)) ∧ z ∈ partCSylow T ∧
      ∃ L : Subgroup (QuasiQuotient u),
        OneComponent (quasiImage B u) (quasiCentral u) (quasiBar u) L ∧
        Nat.card (Subgroup.center L) = 2 ∧
        Nonempty (L ⧸ Subgroup.center L ≃* alternatingGroup (Fin 5)) ∧
        PartC (partCSylow T) (partCLeft T L) (partCRight T L) (centralElt J) u := by
  obtain ⟨T, hTB, huT, hzT⟩ := hu.exists_sylow h hz
  obtain ⟨L, hL, hZ, -, ⟨eA⟩, hα⟩ := hu.exists_alternating_component_of_ne_top h hz IH hne
  have hc := hu.baseConfig_of_ne_top h hz hne
  set T' := T.mapSurjective (QuotientGroup.mk'_surjective (pPrimeCore 2 (quasiNormalizer u)))
  have hT' : (T' : Subgroup (QuasiQuotient u)) =
      (T : Subgroup (quasiNormalizer u)).map (quasiMk u) := Sylow.coe_mapSurjective _ _
  have hP := hL.partC hc (quasiBar_mul_self u) (zpowers_quasiBar_normal u) hZ eA hα T'
  rw [hT'] at hP
  have heT : (⟨centralElt J, h.centralElt_mem_quasiNormalizer u⟩ : quasiNormalizer u) ∈
      (T : Subgroup (quasiNormalizer u)) := by
    rw [hu.centralElt_mk_eq h]
    exact (T : Subgroup (quasiNormalizer u)).mul_mem huT huT
  rw [← hu.quasiMk_centralElt h] at hP
  have hP' := PartC.transport (quasiMk u) (quasiNormalizer u).subtype
    (fun a ha b hb hab => quasiMk_injOn_twoGroup u T.isPGroup' ha hb hab)
    (quasiNormalizer u).subtype_injective heT huT hP h.centralElt_mem_center
  have hinf : ∀ M : Subgroup (QuasiQuotient u),
      (T : Subgroup (quasiNormalizer u)) ⊓
          (((T : Subgroup (quasiNormalizer u)).map (quasiMk u)) ⊓ M).comap (quasiMk u) =
        (T : Subgroup (quasiNormalizer u)) ⊓ M.comap (quasiMk u) := fun M => by
    ext x
    exact ⟨fun hx => ⟨hx.1, hx.2.2⟩, fun hx => ⟨hx.1, Subgroup.mem_map_of_mem _ hx.1, hx.2⟩⟩
  rw [hinf, hinf] at hP'
  exact ⟨T, hTB, huT, ⟨_, hzT, rfl⟩, L, hL, hZ, ⟨eA⟩, hP'⟩

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
