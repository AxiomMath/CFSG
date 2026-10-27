module

public import CFSG.ClassicalInvolution.Q3.Sec13End15I

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin

variable {G : Type} [Group G] [Finite G]

namespace EndHyp

variable {Ω : Set (Subgroup G)} {K K' : Subgroup G} {z : G}

private theorem e15e_eGroup_le (h : EndHyp Ω) (s : TwinSit Ω K K' z) {A Λ : Subgroup G}
    (hEA : eGroup Ω K ≤ A) (hΛ : Λ ≤ Subgroup.normalizer (A : Set G))
    (htr : ∀ a ∈ A, a ≠ 1 → ∃ l ∈ Λ, a = l * z * l⁻¹) {R : Subgroup G} (hR : R ∈ Ω)
    (hRA : ∀ u, IsUniqueInvolution R u → u ∈ A) : eGroup Ω R ≤ A := by
  obtain ⟨v, hv⟩ := Sec6Gen.exists_uniqueInvolution h.thmD.hyp hR
  obtain ⟨l, hl, hvl⟩ := htr v (hRA v hv) hv.ne_one
  have hlK : conjSub l K ∈ Ω := h.thmD.hyp.conjInvariant l K s.mem
  have htw : R ∈ twinSet Ω (conjSub l K) := by
    refine ⟨hR, v, ?_, hv⟩
    rw [hvl]
    exact s.isInv.conj l
  rw [h.eGroup_eq_of_mem_twinSet hlK htw, h.eGroup_conj s.mem l]
  have hl' : l ∈ Subgroup.normalizer (A : Set G) := hΛ hl
  intro x hx
  rw [mem_conjSub_iff] at hx
  have hx' := (Subgroup.mem_normalizer_iff.mp hl' (l⁻¹ * x * l)).mp (hEA hx)
  have e : l * (l⁻¹ * x * l) * l⁻¹ = x := by group
  rw [e] at hx'
  exact hx'

theorem zGroup_le_of_transitive (h : EndHyp Ω) (s : TwinSit Ω K K' z) {A Λ : Subgroup G}
    (hEA : eGroup Ω K ≤ A) (hΛ : Λ ≤ Subgroup.normalizer (A : Set G))
    (htr : ∀ a ∈ A, a ≠ 1 → ∃ l ∈ Λ, a = l * z * l⁻¹) : zGroup Ω ≤ A := by
  have key : ∀ R, Relation.ReflTransGen (dstarAdj Ω) K R →
      R ∈ Ω ∧ ∀ u, IsUniqueInvolution R u → u ∈ A := by
    intro R hR
    induction hR with
    | refl =>
      refine ⟨s.mem, fun u hu => ?_⟩
      rw [← s.isInv.eq hu]
      exact hEA (h.mem_eGroup_of_isUniqueInvolution s.isInv)
    | tail _ hadj ih =>
      obtain ⟨hR, hRA⟩ := ih
      obtain ⟨hc, hcadj⟩ := hadj
      have hE := e15e_eGroup_le h s hEA hΛ htr hR hRA
      refine ⟨hc, fun u hu => ?_⟩
      rcases hcadj with hcR | hRc
      · exact hE (h.mem_eGroup_of_mem_omegaStarNbr hcR hu)
      · exact hE (h.mem_eGroup_of_mem_omegaStarNbr
          (Q3T6.Mu.omegaStarNbr_symm h.thmD.hyp hc hR hRc) hu)
  refine (Subgroup.closure_le _).mpr ?_
  rintro u ⟨L, hL, hu⟩
  exact (key L (h.star K s.mem L hL)).2 u hu

theorem exists_transitive_pair (h : EndHyp Ω) (h9 : Perp9 Ω) (s : TwinSit Ω K K' z)
    (h13 : zGroup Ω ≠ eGroup Ω K) (hE : eGroup Ω K ≤ K ⊔ K') :
    ∃ A : Subgroup G, A ≤ zGroup Ω ∧ eGroup Ω K ≤ A ∧ Nat.card A = 16 ∧
      ∃ Λ : Subgroup G, Λ ≤ Subgroup.normalizer (A : Set G) ∧
        ∀ a ∈ A, a ≠ 1 → ∃ l ∈ Λ, a = l * z * l⁻¹ :=
  h.exists_transitive_pair_of_local h9 s h13 hE

theorem natCard_zGroup_eq_sixteen (h : EndHyp Ω) (h9 : Perp9 Ω) (s : TwinSit Ω K K' z)
    (h13 : zGroup Ω ≠ eGroup Ω K) (hE : eGroup Ω K ≤ K ⊔ K') :
    Nat.card (zGroup Ω) = 16 ∧ ∀ a ∈ zGroup Ω, a ≠ 1 → ∃ g : G, a = g * z * g⁻¹ := by
  obtain ⟨A, hAD, hEA, hA16, Λ, hΛ, htr⟩ := h.exists_transitive_pair h9 s h13 hE
  have hDA : zGroup Ω = A := le_antisymm (h.zGroup_le_of_transitive s hEA hΛ htr) hAD
  refine ⟨?_, fun a ha ha1 => ?_⟩
  · rw [hDA]
    exact hA16
  · rw [hDA] at ha
    obtain ⟨l, -, hl⟩ := htr a ha ha1
    exact ⟨l, hl⟩

theorem exists_aeRecog_six (h : EndHyp Ω) (h9 : Perp9 Ω) (s : TwinSit Ω K K' z)
    (h13 : zGroup Ω ≠ eGroup Ω K) (hE : eGroup Ω K ≤ K ⊔ K')
    (hD16 : Nat.card (zGroup Ω) = 16) (hQ : pCore 2 G = zGroup Ω) :
    Nonempty (AERecog Ω 6) :=
  h.exists_aeRecog_six_of_local h9 s h13 hE hD16 hQ

theorem aeIdent_six_of_twinSit (h : EndHyp Ω) (h9 : Perp9 Ω) (s : TwinSit Ω K K' z)
    (h13 : zGroup Ω ≠ eGroup Ω K) (hE : eGroup Ω K ≤ K ⊔ K') : Nonempty (AEIdent Ω 6) := by
  have hD16 : Nat.card (zGroup Ω) = 16 := (h.natCard_zGroup_eq_sixteen h9 s h13 hE).1
  have hQ : pCore 2 G = zGroup Ω := h.pCore_eq_zGroup_of_local h9 s h13 hE
  obtain ⟨R⟩ := h.exists_aeRecog_six h9 s h13 hE hD16 hQ
  exact R.nonempty_aeIdent (by norm_num) h.thmD.hyp.conjInvariant h.thmD.trans h.thmD.gen

end EndHyp

end CFSG.ClassicalInvolution.Q3.Sec13
