module

public import CFSG.GH74.Generic.GKFFusion
public import CFSG.GH74.Generic.NativeCerts
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsFp
public meta import CFSG.GH74.Generic.GKFFusion
public meta import CFSG.GH74.Generic.NativeCerts
public meta import Certificates.Data.CFSGNative.Filter.Sec2
public meta import Certificates.Data.CFSGNative.SectionRank.Fp
import all CFSG.Blueprint.NativeSporadic
public import CFSG.GH74.Generic.GKFLyInputs
public meta import CFSG.GH74.Generic.GKFLyInputs
public import Certificates.Certificate5104

public section

namespace CFSG.GH74.Generic

open CFSG CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native CFSG.GH74.Generic.Fusion
  Subgroup

theorem lyFus_check :
    fusCheck (opsP 5 111) lyFus = true :=
  Certificates.certificate5104

theorem exists_e_Ly : ∃ e : Fin 4 → NativeSporadic.Ly,
    (∀ i, e i * e i = 1) ∧ (∀ i j, e i * e j = e j * e i) ∧
    (∀ a : Fin 4 → Fin 2, a ≠ 0 → (List.ofFn fun i => e i ^ (a i : ℕ)).prod ≠ 1) ∧
    ∀ a : Fin 4 → Fin 2, a ≠ 0 →
      ∃ g : NativeSporadic.Ly, g * e 0 * g⁻¹ = (List.ofFn fun i => e i ^ (a i : ℕ)).prod :=
  exists_of_fusCheck (specP 5 111) lyFus lyFus_check

theorem coverGen4_Ly
    (S : Type) [Group S] (h : NativeSporadic.IsSporadic S .Ly) :
    ∀ (K : Type) [Group K] [Finite K], IsQuasisimple K → IsPGroup 2 ↥(center K) → Gen4 K →
      Nonempty (K ⧸ center K ≃* S) → center K = ⊥ := by
  intro K _ _ hK hZ2 hG4 ⟨e⟩
  by_contra hZ
  obtain ⟨eS⟩ := h
  have eS' : K ⧸ center K ≃* NativeSporadic.Ly := e.trans eS
  exact @not_gen4_cover_of_fused_E16 NativeSporadic.Ly inferInstance exists_e_Ly K
    inferInstance inferInstance hK hZ2 ⟨eS'⟩ hZ hG4

end CFSG.GH74.Generic
