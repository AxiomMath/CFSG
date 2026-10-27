module

public import CFSG.ClassicalInvolution.Asc77.AscT7ERAlg
import CFSG.ClassicalInvolution.Asc77.AscE187P1a
public import CFSG.ClassicalInvolution.Asc77.AscT7BHyp23

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

namespace T7ER

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K K' : Subgroup G} {z : G}

theorem exists_conj_mem_sylow_of_centralizes (S : Sylow 2 G)
    (hzS : ∀ s ∈ (S : Subgroup G), s * z = z * s) {s : G} (hs2 : s * s = 1) (hsz : s * z = z * s) :
    ∃ c : G, c * z = z * c ∧ c⁻¹ * s * c ∈ (S : Subgroup G) := by
  have hSM : (S : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hzS x hx)
  have hsM : Subgroup.zpowers s ≤ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hsz)
  obtain ⟨c, hcM, hc⟩ := exists_conj_sylow_ge hSM (isPGroup_zpowers_of_sq hs2) hsM
  refine ⟨c, Subgroup.mem_centralizer_singleton_iff.mp hcM, ?_⟩
  have : s ∈ conjSub c (S : Subgroup G) := hc (Subgroup.mem_zpowers s)
  rwa [mem_conjSub_iff] at this

theorem conjSub_eq_of_centralizes (hs : Hyp23Setting p f Ω K K' z) {u : G} (hu : u * z = z * u) :
    conjSub u K = K ∨ conjSub u K = K' := by
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have hmem : conjSub u K ∈ twinSet Ω K := by
    refine ⟨hΩ.conjInvariant u K hK, z, hs.hz, ?_⟩
    have := hs.hz.conj u
    have hz : u * z * u⁻¹ = z := by rw [hu]; group
    rwa [hz] at this
  rw [hs.twinSet_eq] at hmem
  exact hmem

theorem normalizes_iff_of_centralizes (hs : Hyp23Setting p f Ω K K' z) {u : G}
    (hu : u * z = z * u) : conjSub u K = K ↔ conjSub u K' = K' := by
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have hK' : K' ∈ Ω := hs.hK'.1
  have hne : K' ≠ K := hs.hne
  have hz' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hs.hz hs.hK'
  have hmem' : conjSub u K' ∈ twinSet Ω K := by
    refine ⟨hΩ.conjInvariant u K' hK', z, hs.hz, ?_⟩
    have := hz'.conj u
    have hz : u * z * u⁻¹ = z := by rw [hu]; group
    rwa [hz] at this
  rw [hs.twinSet_eq] at hmem'
  constructor
  · intro h
    rcases hmem' with h' | h'
    · exact absurd (conjSub_injective u (h.trans h'.symm)) hne.symm
    · exact h'
  · intro h
    rcases conjSub_eq_of_centralizes hs hu with h' | h'
    · exact h'
    · exact absurd (conjSub_injective u (h.trans h'.symm)) hne

end T7ER

end CFSG.ClassicalInvolution.Asc77
