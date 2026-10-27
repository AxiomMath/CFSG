module

public import CFSG.LocalAnalysis.OddStandard.Solomon75StdOddKer
public import CFSG.LocalAnalysis.OddStandard.Solomon75StdOddSylow
public import CFSG.LocalAnalysis.OddStandard.Solomon75StdOdd
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5Final
import CFSG.LocalAnalysis.OddStandard.Solomon75AhatDataBalance
public import CFSG.LocalAnalysis.OddStandard.Solomon75StdBasicConj

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS

section

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {L : Subgroup G} {n : ℕ} {z : G}

theorem StdSetup.isDoubleCover_centralizer (h : StdSetup G L n z) (hn11 : n ≤ 11)
    (hK : ∀ S : Sylow 2 ↥(centralizer (L : Set G)),
      Nat.card ↥(S : Subgroup ↥(centralizer (L : Set G))) = 2)
    (hpar : ∀ (M : AhatModel G n L) (a : G) (ha : a ∈ normalizer (L : Set G)),
      a ∈ centralizer ({z} : Set G) → a ≠ z → (∃ g : G, g⁻¹ * z * g = a) →
        sign (M.perm a ha) = 1) :
    IsDoubleCoverOfAlt (↥(centralizer ({z} : Set G)) ⧸ pPrimeCore 2 ↥(centralizer ({z} : Set G)))
      n := by
  have hctx := h.sec5Ctx (h.le_oddCore_sup_of_card_two rfl hK)
  refine hctx.isDoubleCover_of_even ?_ h.cover_quot
  by_contra hodd
  push Not at hodd
  obtain ⟨t, htN, ht⟩ := hodd
  have hsign : sign (hctx.psi ⟨t, htN⟩) = -1 := by
    rcases Int.units_eq_one_or (sign (hctx.psi ⟨t, htN⟩)) with h2 | h2
    · exact absurd h2 ht
    · exact h2
  obtain ⟨S⟩ : Nonempty (Sylow 2 ↥(centralizer ({z} : Set G))) := inferInstance
  have hSyl := h.isSylowTwoIn_top S
  obtain ⟨g, hg1, hg2⟩ := h.exists_partner
  have hs₁N : g⁻¹ * z * g ∈ centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 hg2
  have hpar' : ∀ (t : G) (htN : t ∈ centralizer ({z} : Set G)), t * t = 1 → t ≠ 1 → t ≠ z →
      (∃ g : G, g⁻¹ * z * g = t) → sign (hctx.psi ⟨t, htN⟩) = 1 :=
    fun t htN _ _ htz hc => hpar h.model t (h.cent_eq.le htN) htN htz hc
  exact hctx.odd_false' (fun u v hu hv hu' hv' =>
      AhatData.one_class_of_cover h.hn hn11 h.model.C.hX hu hv hu' hv')
    inferInstance h.nonab S hSyl hs₁N (h.conj g).hz hg1 ⟨g, rfl⟩
    (hpar' _ hs₁N (by
        have := (h.conj g).hz
        have h2 := pow_orderOf_eq_one (g⁻¹ * z * g)
        rwa [this, sq] at h2)
      (fun h1 => by
        have := (h.conj g).hz
        rw [h1, orderOf_one] at this
        omega) hg1 ⟨g, rfl⟩)
    hpar' htN hsign

end

theorem solomon2AnStdCyclic_of_theorem44 (hMcL : Solomon44McL) (hLy : Solomon44Ly)
    (hNT : Solomon44NineTen) (hCore : Solomon2AnStdCore) : Solomon2AnStdCyclic := by
  intro G _ _ _ L hL n hn hθ hZ hS
  obtain ⟨z, hz⟩ := exists_stdSetup hL hn hθ hZ hS
  obtain ⟨hn11, hK, hpar⟩ := hCore G L n z hz
  have hcov := hz.isDoubleCover_centralizer hn11 hK hpar
  interval_cases n
  · exact Or.inl (hMcL G hz.nonab z hz.hz hcov)
  · exact absurd hcov (hNT G hz.nonab z hz.hz 9 (Or.inl rfl))
  · exact absurd hcov (hNT G hz.nonab z hz.hz 10 (Or.inr rfl))
  · exact Or.inr (hLy G hz.nonab z hz.hz hcov)

end CFSG.OddStandard.Solomon75
