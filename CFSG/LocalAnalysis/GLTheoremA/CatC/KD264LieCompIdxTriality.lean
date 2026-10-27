module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdx
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompRel
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.OuterDispatch
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.InnerTw
import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.OutTriD4
import CFSG.GroupTheory.CenterlessInnerCentralizer
import CFSG.LocalAnalysis.GLTheoremA.CatC.RationalTypeAModel
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Inner
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcInnerLang
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSL
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleOrbit
public import CFSG.LieType.SeitzGeneration.SeitzStatus

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.RootAut
  CFSG.HardMathSupport.Dickson.Sec6.Up34Exc
  CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.ComponentClassification.OuterAutomorphisms
open scoped MatrixGroups

section TypeA

open CFSG.LocalAnalysis.GLTheoremA.RationalModel


variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)

theorem catalogueOver_rationalComponent_rankOne
    {ta : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ ta ∈ S.D.torus) (i : KernelComponent (rootCharHom ta))
    (h1 : compRank (componentRoots (rootCharHom ta) i) = 1)
    (hn : (componentRoots (rootCharHom ta) i).ncard = 2)
    (hQS : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom ta) i)) :
    CatalogueOver (ringChar L)
      (S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom ta) i))
      ↥(rationalComponent S.ρ S.Γ (rootCharHom ta) i) := by
  classical
  obtain ⟨K, hfield, hfinite, f, hf1, hKcard, hfeq, hring, hK4, g, hgsurj, hgker⟩ :=
    exists_slCover_rationalComponent_rankOne S hT i h1 hn hQS
  letI : Fintype K := Fintype.ofFinite K
  have hcat := catalogueOver_of_surjective_sl (E := K) (m := 2) le_rfl
    (fun _ => by rw [← Nat.card_eq_fintype_card]; exact hK4) g hgsurj hgker
  rwa [hring, ← Nat.card_eq_fintype_card, hKcard, hfeq] at hcat

theorem catalogueOver_rationalComponent_splitFrame {ta : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ ta ∈ S.D.torus) (i : KernelComponent (rootCharHom ta)) {ν : ℕ}
    (hν : 3 ≤ ν) {ψ : SL(ν, L) →* ModGL τ L} {σ : Fin ν → Fin ν → Fin τ.rank → ℤ}
    (hψ : IsSLFrame ψ σ) (hΨ : componentRoots (rootCharHom ta) i = frameRoots σ)
    (π : Equiv.Perm (Fin ν))
    (hπ : ∀ a b, a ≠ b → (S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
      (componentRoots (rootCharHom ta) i)] (σ a b) = σ (π a) (π b)) :
    CatalogueOver (ringChar L)
      (S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom ta) i))
      ↥(rationalComponent S.ρ S.Γ (rootCharHom ta) i) := by
  classical
  obtain ⟨K, hfield, hfinite, f, hf1, hKcard, hfeq, hring, g, hgsurj, hgker⟩ :=
    exists_slCover_rationalComponent_splitFrame S hT i hν hψ hΨ π hπ
  letI : Fintype K := Fintype.ofFinite K
  have hcat := catalogueOver_of_surjective_sl (E := K) (m := ν) (by omega) (fun _ => by omega)
    g hgsurj hgker
  rwa [hring, ← Nat.card_eq_fintype_card, hKcard, hfeq] at hcat

theorem catalogueOver_rationalComponent_unitaryFrame {ta : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ ta ∈ S.D.torus) (i : KernelComponent (rootCharHom ta)) {ν : ℕ}
    (hν : 3 ≤ ν) {ψ : SL(ν, L) →* ModGL τ L} {σ : Fin ν → Fin ν → Fin τ.rank → ℤ}
    (hψ : IsSLFrame ψ σ) (hΨ : componentRoots (rootCharHom ta) i = frameRoots σ)
    (π : Equiv.Perm (Fin ν))
    (hπ : ∀ a b, a ≠ b → (S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
      (componentRoots (rootCharHom ta) i)] (σ a b) = σ (π b) (π a))
    (hQS : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom ta) i)) :
    CatalogueOver (ringChar L)
      (S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom ta) i))
      ↥(rationalComponent S.ρ S.Γ (rootCharHom ta) i) := by
  classical
  obtain ⟨K, hfield, hfinite, f, hf1, hKcard, hfeq, hring, h32, g, hgsurj, hgker⟩ :=
    exists_suCover_rationalComponent_unitaryFrame S hT i hν hψ hΨ π hπ hQS
  letI : Fintype K := Fintype.ofFinite K
  have hK' : Fintype.card K = (ringChar L ^ f) ^ 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact hKcard
  have hcat := catalogueOver_of_surjective_su hK' hν h32 g hgsurj hgker
  rwa [hring, hfeq] at hcat

theorem catalogueOver_rationalComponent_typeA
    {p : ℕ} (hp : p.Prime)
    {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ i, a i ^ p = 1) (h1 : rootDiagUnit τ a ≠ 1)
    (i : KernelComponent (rootCharHom a))
    (hA : 1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1))
    (hQS : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    CatalogueOver (ringChar L)
      (S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i))
      ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  classical
  rcases typeA_frame_cases S hp hT hap h1 i hA with ⟨hr1, hn⟩ | h | h
  · exact catalogueOver_rationalComponent_rankOne S hT i hr1 hn hQS
  · obtain ⟨ν, ψ, σ, π, hν, hψ, hΨ, hπ⟩ := h
    exact catalogueOver_rationalComponent_splitFrame S hT i hν hψ hΨ π hπ
  · obtain ⟨ν, ψ, σ, π, hν, hψ, hΨ, hπ⟩ := h
    exact catalogueOver_rationalComponent_unitaryFrame S hT i hν hψ hΨ π hπ hQS

end TypeA

section D4Class

private def d4θ_kd264Tri : Fin Tag.D4.rank → ℤ := ![1, 1, 2, 1]

private theorem d4AllRootsPass_kd264Tri : ∀ c ∈ d4Conn, c.length = 4 →
    kacCount Tag.D4 d4θ_kd264Tri (c.map (idxNode (r := Tag.D4.rank))).toFinset = 24 →
    ∀ r ∈ Tag.D4.artifactRoots,
      kacTest d4θ_kd264Tri (c.map (idxNode (r := Tag.D4.rank))).toFinset
        (CFSG.RankThree.Lattice.toVec Tag.D4.rank r) := by
  decide +kernel


theorem typeAShape_d4Class {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ}
    (S : LangSetup Tag.D4 L p₀) (hp : p.Prime) (hpL : (p : L) ≠ 0)
    {a : Fin Tag.D4.rank → Lˣ} (hTp : rootDiagUnit Tag.D4 a ^ p = 1)
    (h1 : rootDiagUnit Tag.D4 a ≠ 1) (i : KernelComponent (rootCharHom a)) :
    1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard =
        compRank (componentRoots (rootCharHom a) i) *
          (compRank (componentRoots (rootCharHom a) i) + 1) := by
  classical
  obtain ⟨v, μ, x, c, -, hc, -, hlen, hroots, hrank, hncard⟩ :=
    exists_cand_of_class kacD4 facts_D4 d4_tree d4_adj d4_check d4_lt d4_card S hp hpL hTp i
  have hshape := d4_shape_raw c hc hlen
  rw [hrank, hncard]
  rcases hshape with hA | hD
  · exact hA
  · exfalso
    have hrk : Tag.D4.rank = 4 := rfl
    have hc4 : c.length = 4 := by have := hD.1; omega
    have h24 : kacCount Tag.D4 d4θ_kd264Tri (c.map (idxNode (r := Tag.D4.rank))).toFinset =
        24 := by
      have h := hD.2
      rw [hc4] at h
      exact h
    have hCp : ∃ y, y ∉ (c.map (idxNode (r := Tag.D4.rank))).toFinset := by
      by_contra hcon
      push Not at hcon
      have h1' : (c.map (idxNode (r := Tag.D4.rank))).toFinset = Finset.univ :=
        Finset.eq_univ_of_forall hcon
      have h2 := d4_card c hc
      rw [h1', Finset.card_univ, Fintype.card_option, Fintype.card_fin, hc4] at h2
      omega
    apply h1
    have ha : a = 1 := by
      funext j
      have hmem : (Pi.single j 1 : Fin Tag.D4.rank → ℤ) ∈ componentRoots (rootCharHom a) i := by
        rw [hroots]
        have hγ : IsRoot Tag.D4 (v⁻¹ • (Pi.single j 1 : Fin Tag.D4.rank → ℤ)) :=
          IsRoot.smul (isRoot_single _ j) v⁻¹
        refine ⟨v⁻¹ • Pi.single j 1, ?_, smul_inv_smul v _⟩
        refine (mem_rootsOf_iff kacD4 facts_D4 hCp).2 ⟨hγ, ?_⟩
        have hpass := d4AllRootsPass_kd264Tri c hc hc4 h24 _ (isRoot_iff_mem_artifactRoots.1 hγ)
        rw [toVec_ofFn_gen] at hpass
        exact hpass
      obtain ⟨hker, -⟩ := hmem
      have h1 : rootChar a (Pi.single j 1) = 1 := hker.2
      rw [CFSG.RankThree.PartOne.KE.CTTorus.rootChar_single] at h1
      exact h1
    rw [ha]
    exact rootDiagUnit_one

end D4Class

section Triality


theorem compIdxAt_trialityModel
    {q : TauCeti.PrimePower} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (q.p ^ q.exponent) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (q.p ^ q.exponent)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ≠ q.p) :
    CompIdxAt p (.trialityD4 q) ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  classical
  intro β hβmem hβp hβ1 J hJ
  haveI : Finite ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := Subtype.finite
  have hβinn : β ∈ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →*
      MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range :=
    sup_le le_rfl (CFSG.HardMathSupport.Dickson.Sec6.I1431.t6outtrid4_commutator_le_range
      q.prime_p q.exponent_pos hK σ hσ) hβmem
  obtain ⟨x, rfl⟩ := hβinn
  have hZ : Subgroup.center ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ :=
    CFSG.LieType.Chevalley.center_graphFixedRootGroup_eq_bot σ.surjective
  have hxp : x ^ p = 1 :=
    CFSG.mulAutConj_injective_of_center_eq_bot hZ (by rw [map_pow, hβp, map_one])
  have hx1 : x ≠ 1 := fun h => hβ1 (by rw [h, map_one])
  have hmon : MonomialToralAt Tag.D4 p := by
    by_cases hp3 : p = 3
    · subst hp3
      exact monomialToralAt_three_of_block a2BlockToral_D4
    · exact monomialToralAt_of_not_dvd hp
        (CFSG.RankThree.PartOne.KGD.not_dvd_card_weylGroup_D4 hp
          (by have := hp.two_le; omega))
  obtain ⟨p₀, hp₀, hp₀ℓ, hq₀⟩ := exists_setup_prime q.prime_p q.exponent_pos hp hp2 hpq
  obtain ⟨S, a, ι, hSq, -, hT, hap, h1, hinj, hrange, hconj⟩ :=
    exists_langSetup_of_inner_triD4_of_prime q.prime_p q.exponent_pos hK σ hσ hp hpq hp₀ hp₀ℓ
      hq₀ hmon x hxp hx1
  have hpL : ((p : ℕ) : AlgebraicClosure K) ≠ 0 :=
    natCast_ne_zero_algebraicClosure_of_ne q.prime_p hp hK hpq
  have hTame := langSetup_hTame_of_prime S hp hpL (fun h => absurd h (by decide)) hT hap h1
  obtain ⟨i, hqs, hJR⟩ :=
    components_of_langSetup S hp ι hinj hrange (MulAut.conj x) hconj hT hap h1 hTame hJ
  have hTp := rootDiagUnit_pow_eq_one_of_forall hap
  have hA := typeAShape_d4Class S hp hpL hTp h1 i
  have hcat := catalogueOver_rationalComponent_typeA S hp hT hap h1 i hA hqs
  have hs0 := (outer_componentOrbitLength_spec S hT i).1
  have hAC : ringChar (AlgebraicClosure K) = q.p := by
    rw [ringChar_algebraicClosure]
    exact ringChar_eq_of_card_eq_pow (n := q.exponent * 3) q.prime_p
      (by have := q.exponent_pos; omega) (by rw [hK, ← pow_mul])
  let eJ : ↥J ≃* ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
    (J.equivMapOfInjective ι hinj).trans (MulEquiv.subgroupCongr hJR)
  obtain ⟨i', hφ, hidx⟩ := hcat.of_mulEquiv eJ.symm
  refine ⟨i', hφ, compRelC_of_idxOver hs0 ?_⟩
  have hfs : fieldSize (TauCeti.LieTypeIndex.trialityD4 q) = q.p ^ q.exponent :=
    TauCeti.PrimePower.card_def q
  rw [TauCeti.LieTypeIndex.characteristic_trialityD4, hfs, ← hSq, ← hAC]
  exact hidx

theorem lieCompIdx_triality :
    LieCompIdx isTrialityIdx := by
  intro d p hp hp2 hpc hP
  obtain ⟨e, hv⟩ := d
  cases e with
  | trialityD4 q =>
    have hpq : p ≠ q.p := by
      rw [TauCeti.LieTypeIndex.characteristic_trialityD4] at hpc
      exact hpc
    obtain ⟨K, hfield, hfinite, σ, hK, hσ, -, ⟨eK⟩⟩ :=
      CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_catEquiv_trialityD4 q hv
    letI := hfield
    letI := hfinite
    exact compIdxAt_of_mulEquiv eK.symm (compIdxAt_trialityModel hK σ hσ hp hp2 hpq)
  | _ => exact absurd hP (by simp [isTrialityIdx])

end Triality

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
