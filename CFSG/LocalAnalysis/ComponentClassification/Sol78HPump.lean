module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSigPump
public import CFSG.LocalAnalysis.ComponentClassification.Sol78HMember

public section

namespace CFSG.ComponentClassification.SolMax.Sig36

open CFSG Subgroup

variable {X : Type} [Group X] [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}
  (S : Sig36 X t J n e E D)
include S

theorem isSolomonMember_of_trivial_pump {Y M : Subgroup X} (hMY : M ≤ Y)
    (hMpc : IsPComponent 2 (M.subgroupOf Y)) (hCY : centralizer ({t} : Set X) ≤ Y)
    (htM : t ∈ normalizer (M : Set X)) (hsup : J ⊔ FooteLit.oddCoreIn M = M) :
    FooteLit.IsSolomonMember M := by
  have ht := S.pair.1.1
  have hCT : centralizer ((zpowers t : Subgroup X) : Set X) = centralizer ({t} : Set X) := by
    rw [zpowers_eq_closure, centralizer_closure]
  refine Sol78H.isSolomonMember_of_centralizer_le ⟨hMY, hMpc⟩ ?_
    (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one]))
    (zpowers_le.mpr (Sol78H.mem_coreActionKernel_of_sup_le_centralizer htM S.pair.1.2.1 hsup))
    (zpowers_le.mpr (hCY (mem_centralizer_singleton_iff.mpr rfl))) (hCT ▸ hCY)
  intro h
  rw [zpowers_eq_bot] at h
  rw [h, orderOf_one] at ht
  omega

theorem normal_of_trivial_pump_of_member (h13 : Sol76T13.SolomonThm13Simple)
    (hmax : Sol78.MaximalityLemmaInput) (hS : SolAltLit.SchurAlternatingMultiplierInput)
    {Y M : Subgroup X} (hMY : M ≤ Y) (hMpc : IsPComponent 2 (M.subgroupOf Y)) (hJM : J ≤ M)
    (eM : M ⧸ Open.fusionZStar M ≃* alternatingGroup (Fin n))
    (hCY : centralizer ({t} : Set X) ≤ Y) (htM : t ∈ normalizer (M : Set X)) :
    J ⊔ FooteLit.oddCoreIn M = M ∧ Nonempty (M ⧸ pPrimeCore 2 M ≃* alternatingGroup (Fin n)) ∧
      Y ≤ normalizer (M : Set X) := by
  have hMperf : ⁅M, M⁆ = M := UnbalancedCorr.commutator_eq_of_isPComponent hMY hMpc
  obtain ⟨hsup, hM⟩ := exact_of_le_of_alt hJM hMperf (by have := S.nine_le; omega) e eM
  exact ⟨hsup, hM, S.le_normalizer_of_isPComponent_alt_of_member h13 hmax hS hMY hMpc
    (S.isSolomonMember_of_trivial_pump hMY hMpc hCY htM hsup) hM⟩

end CFSG.ComponentClassification.SolMax.Sig36
