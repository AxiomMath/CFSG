module

public import CFSG.LocalAnalysis.OddStandard.Solomon75StdBasic
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5FinalCtx
import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionZStarSylow

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS

open scoped Pointwise

section

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {L : Subgroup G} {n : ℕ} {z : G}

theorem StdSetup.le_oddCore_sup_of_card_two (h : StdSetup G L n z) {K : Subgroup G}
    (hK : K = centralizer (L : Set G))
    (hK2 : ∀ S : Sylow 2 ↥K, Nat.card ↥(S : Subgroup ↥K) = 2) :
    K ≤ oddCoreOf (centralizer ({z} : Set G)) ⊔ zpowers z := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzK : z ∈ K := hK ▸ h.z_cent
  have hKC : K ≤ centralizer ({z} : Set G) := hK ▸ h.centralizer_le_centralizer_singleton
  have hKnorm : ∀ c ∈ centralizer ({z} : Set G), c ∈ normalizer (K : Set G) := fun c hc => by
    have hcL : c ∈ normalizer (L : Set G) := h.mem_normalizer_of_mem_centralizer hc
    have h1 : normalizer (centralizer (L : Set G) : Set G) = normalizer (L : Set G) :=
      h.standard.2.2.2.1
    rw [hK, h1]
    exact hcL
  obtain ⟨S⟩ : Nonempty (Sylow 2 ↥K) := inferInstance
  have hS2 := hK2 S
  set z' : ↥K := ⟨z, hzK⟩ with hz'
  have hz'ord : orderOf z' = 2 := by rw [Subgroup.orderOf_mk]; exact h.hz
  have hz'cen : z' ∈ center ↥K := by
    rw [Subgroup.mem_center_iff]
    intro k
    have hkc : (k : G) ∈ centralizer (L : Set G) := by
      rw [← hK]
      exact k.2
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hkc z h.z_mem).symm
  have hz'S : z' ∈ (S : Subgroup ↥K) :=
    CFSG.ComponentClassification.StandardRecognition.mem_sylow_of_mem_center_of_orderOf_eq_two
      hz'cen hz'ord S
  have hSz : (S : Subgroup ↥K) = zpowers z' := by
    symm
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hz'S) ?_
    rw [hS2, Nat.card_zpowers, hz'ord]
  have hScyc : IsCyclic ↥(S : Subgroup ↥K) := isCyclic_of_prime_card (p := 2) hS2
  obtain ⟨-, hprod, -⟩ := CFSG.cyclic_sylow_normal_odd_complement S hScyc
  have hOKC : oddCoreOf K ≤ oddCoreOf (centralizer ({z} : Set G)) := by
    refine le_oddCoreOf_of_normalized ((oddCoreOf_le K).trans hKC) (fun c hc => ?_)
      (odd_card_oddCoreOf K)
    exact mem_normalizer_oddCoreOf_of_mem_normalizer (hKnorm c hc)
  intro k hk
  have hmem : (⟨k, hk⟩ : ↥K) ∈ ((pPrimeCore 2 ↥K : Set ↥K) * (S : Set ↥K)) := by
    rw [hprod]
    exact Set.mem_univ _
  obtain ⟨a, ha, s, hs, has⟩ := Set.mem_mul.1 hmem
  have hk' : k = (a : G) * (s : G) := by
    have := congrArg (fun w : ↥K => (w : G)) has
    simpa using this.symm
  rw [hk']
  refine Subgroup.mul_mem_sup (hOKC ?_) ?_
  · exact Subgroup.mem_map_of_mem _ ha
  · have hs' : s ∈ (S : Subgroup ↥K) := hs
    rw [hSz] at hs'
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hs'
    have : (s : G) = z ^ i := by
      rw [← hi]
      simp [hz']
    rw [this]
    exact Subgroup.zpow_mem_zpowers z i

theorem StdSetup.sec5Ctx (h : StdSetup G L n z)
    (hQ : centralizer (L : Set G) ≤ oddCoreOf (centralizer ({z} : Set G)) ⊔ zpowers z) :
    Sec5Ctx G n z (centralizer ({z} : Set G)) L h.model :=
  ⟨h.hn, h.hz, fun _ hc => (Subgroup.mem_centralizer_singleton_iff.1 hc).symm,
    h.le_centralizer_singleton, h.cent_eq.le, h.z_mem, fun _ hc h1 =>
      hQ ((h.perm_eq_one_iff h.model (h.cent_eq.le hc)).1 h1)⟩

end

end CFSG.OddStandard.Solomon75
