module

public import CFSG.ClassicalInvolution.Q3.Sec13EndHyp
import CFSG.ClassicalInvolution.Q3.TL3T28

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isNormalTwoIn_oTwoCore (z : G) :
    TC.IsNormalTwoIn (oTwoCore (Subgroup.centralizer ({z} : Set G))) z := by
  set C := Subgroup.centralizer ({z} : Set G)
  refine ⟨Subgroup.map_subtype_le _, (CFSG.pCore_isPGroup (p := 2) (G := ↥C)).map C.subtype, ?_⟩
  rintro c hc _ ⟨y, hy, rfl⟩
  exact ⟨⟨c, hc⟩ * y * ⟨c, hc⟩⁻¹, (CFSG.pCore_normal (p := 2) (G := ↥C)).conj_mem y hy ⟨c, hc⟩,
    rfl⟩

theorem uAt_of_etaSpan_le {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω) {N : Subgroup G}
    (hN : N ∈ Ω) {u : G} {U : Subgroup G} (hU : U ∈ USet Ω) (hUN : U ≤ N)
    (hUu : U ≤ Subgroup.centralizer ({u} : Set G)) {η : Set (Subgroup G)} (hη : η ∈ etaG Ω)
    {P : Subgroup G} (hP : TC.IsNormalTwoIn P u) (hηP : TC.etaSpan η ≤ P) : TC.UAt Ω u N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPn := hP.2.2
  have hUP : U ≤ Subgroup.normalizer (P : Set G) := fun x hx =>
    Subgroup.mem_normalizer_iff.mpr fun p => ⟨hPn x (hUu hx) p, fun hp => by
      simpa [mul_assoc] using hPn x⁻¹ (Subgroup.inv_mem _ (hUu hx)) _ hp⟩
  obtain ⟨S, hS⟩ :=
    ((Sec6Gen.isPGroup_of_mem_USet hΩ hU).to_sup_of_normal_right' hP.2.1 hUP).exists_le_sylow
  have hηS : ∀ V ∈ η, V ≤ (S : Subgroup G) := fun V hV =>
    (TC.le_etaSpan hV).trans (hηP.trans (le_sup_right.trans hS))
  obtain ⟨-, -, -, -, -, -, -, -, h4⟩ := Sec6Gen.exists_data_of_mem_USet hΩ hU
  have hNη : N ⊓ TC.etaSpan η ∈ η := Sec6Gen.l6_11Gen G Ω hΩ S η hη hηS N hN (by
    have := Subgroup.card_le_of_le (le_inf hUN (le_sup_left.trans hS))
    omega)
  obtain ⟨S₀, hS₀, -⟩ := hη
  exact ⟨_, (hS₀.1 hNη).1, inf_le_left, P, hP, inf_le_right.trans hηP⟩

namespace EndHyp

variable {Ω : Set (Subgroup G)} (h : EndHyp Ω)
include h

theorem not_le_oTwoCore {K : Subgroup G} (hK : K ∈ Ω) {z : G} (hz : IsUniqueInvolution K z)
    {W : Subgroup G} (hW : W ∈ WSet Ω) :
    ¬ W ≤ oTwoCore (Subgroup.centralizer ({z} : Set G)) := by
  intro hWO
  have hΩ := h.thmD.hyp
  have h2 := h.thmD.two
  have hall : ∀ M ∈ Ω, ∀ u : G, IsUniqueInvolution M u →
      ∃ η ∈ etaG Ω, ∃ P : Subgroup G, TC.IsNormalTwoIn P u ∧ TC.etaSpan η ≤ P := by
    intro M hM u hu
    obtain ⟨g, hg⟩ := h.thmD.trans K hK M hM
    have hz' := hz.conj g
    rw [hg] at hz'
    obtain ⟨η, hη, hWη⟩ := WSet.conj hΩ.conjInvariant hW g
    refine ⟨η, hη, conjSub g (oTwoCore (Subgroup.centralizer ({z} : Set G))), ?_,
      hWη.symm.le.trans (conjSub_mono hWO)⟩
    rw [hu.eq hz']
    exact (isNormalTwoIn_oTwoCore z).conj g
  have hA : ∀ {M N : Subgroup G}, dstarAdj Ω M N → M ∈ Ω →
      N ∈ Ω ∧ ∀ u : G, IsUniqueInvolution M u → TC.UAt Ω u N := by
    intro M N hMN hM
    obtain ⟨hN, hstar⟩ := hMN
    refine ⟨hN, fun u hu => ?_⟩
    obtain ⟨-, -, U, hU, hUN, hUM⟩ : N ∈ omegaStarNbr Ω M :=
      hstar.elim id (Q3T6.Mu.omegaStarNbr_symm hΩ hN hM)
    obtain ⟨η, hη, P, hP, hηP⟩ := hall M hM u hu
    exact uAt_of_etaSpan_le hΩ hN hU hUN (Asc77.T3.le_centralizer_of_le_normalizer' hu hUM) hη
      hP hηP
  obtain ⟨η, hη, hηn⟩ := exists_normal_etaSpan_of_reach hΩ h2 (A := dstarAdj Ω) hA
    (uAt_self_of hΩ h2) hK (fun L hL => h.star K hK L hL) h.thmD.gen hz
  exact h.wSet_ne _ (wSet_eq_singleton_of_normal hΩ h2 h.thmD.trans h.thmD.gen
    (fun hs => h.not (Or.inl hs)) ⟨η, hη, rfl⟩ hηn)

theorem exists_wSet_not_le {K : Subgroup G} (hK : K ∈ Ω) {z : G}
    (hz : IsUniqueInvolution K z) :
    ∃ W ∈ WSet Ω, z ∈ W ∧ K ≤ Subgroup.normalizer (W : Set G) ∧
      ¬ W ≤ oTwoCore (Subgroup.centralizer ({z} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hKS⟩ := (h.thmD.two K hK).exists_le_sylow
  obtain ⟨η, hη, -, -, hKη⟩ := h.exists_wSet_of_le hK S hKS
  have hW : TC.etaSpan η ∈ WSet Ω := ⟨η, hη, rfl⟩
  have hKηU : K ⊓ TC.etaSpan η ∈ USet Ω := by
    obtain ⟨S₀, hS₀, -⟩ := hη
    exact (hS₀.1 hKη).1
  obtain ⟨-, -, -, -, -, -, -, -, h4⟩ := Sec6Gen.exists_data_of_mem_USet h.thmD.hyp hKηU
  have hzW : z ∈ TC.etaSpan η :=
    (hz.mem_of_le inf_le_left ((TC.etaSpan_isPGroup hη).to_le inf_le_right) (by omega)).2
  exact ⟨_, hW, hzW, (h.mem_dSet_of_mem hW hK hz hzW).2, h.not_le_oTwoCore hK hz hW⟩

theorem exists_uSet_not_le {K : Subgroup G} (hK : K ∈ Ω) {z : G} (hz : IsUniqueInvolution K z)
    {W : Subgroup G} (hW : W ∈ WSet Ω) :
    ∃ U ∈ USet Ω, U ≤ W ∧ ¬ U ≤ oTwoCore (Subgroup.centralizer ({z} : Set G)) := by
  have hWO := h.not_le_oTwoCore hK hz hW
  obtain ⟨η, ⟨S, hηS, -⟩, rfl⟩ := hW
  by_contra hcon
  refine hWO (iSup₂_le fun U hU => ?_)
  by_contra hUO
  exact hcon ⟨U, (hηS.1 hU).1, TC.le_etaSpan hU, hUO⟩

theorem exists_wSet_uSet_not_le {K : Subgroup G} (hK : K ∈ Ω) {z : G}
    (hz : IsUniqueInvolution K z) :
    ∃ W ∈ WSet Ω, z ∈ W ∧ K ≤ Subgroup.normalizer (W : Set G) ∧
      ∃ U ∈ USet Ω, U ≤ W ∧ ¬ U ≤ oTwoCore (Subgroup.centralizer ({z} : Set G)) := by
  obtain ⟨W, hW, hzW, hKW, -⟩ := h.exists_wSet_not_le hK hz
  exact ⟨W, hW, hzW, hKW, h.exists_uSet_not_le hK hz hW⟩

end EndHyp

end CFSG.ClassicalInvolution.Q3.Sec13
