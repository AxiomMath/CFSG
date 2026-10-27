module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusBase
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeTwo
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusNodeGroup

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus

open CFSG.AGLEmbedding CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime CFSG.AGLEmbedding.ToralCensus
  CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.Steinberg

variable {K X : Type*} [Group K] [Group X] [Finite X] {D : UniversalRootDatum K}
  {nW : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {π' : K →* X} {M : ℕ}

theorem rankOne_le_of_orthogonal (hQ : BorelQuotient D nW H π' M) {J : Subgroup X}
    (hcyc : CycPerfect 3 J) {v : X} (hv3 : v ^ 3 = 1)
    (hvJ : v ∈ perfectJoin J) (hfix : ∀ g : X, g * v = v * g → g ∈ J) {s : Fin D.rank}
    (hs : (rankOne D.rootGroup s).map π' ≤ J) {A : Subgroup X}
    (hA : A ≤ (rankOne D.rootGroup s).map π') (hAperf : ⁅A, A⁆ = A) {x : X} (hxA : x ∈ A)
    (hx3 : orderOf x = 3) {i : Fin D.rank} (his : i ≠ s) (hcart : D.cartan i s = 0) :
    (rankOne D.rootGroup i).map π' ≤ J := by
  have hAJ : A ≤ J := hA.trans hs
  have hcycP : ∀ Q : Subgroup X, Q ≤ perfectJoin J → IsPGroup 3 Q → IsCyclic Q :=
    hcyc (perfectJoin J) (perfectJoin_le J) (perfectJoin_perfect J)
  have hxP : x ∈ perfectJoin J := le_perfectJoin hAJ hAperf hxA
  obtain ⟨g, hgP, hg⟩ := exists_conj_mem_zpowers_of_cyclic Nat.prime_three hcycP hvJ hxP hv3 hx3
  have hgJ : g ∈ J := perfectJoin_le J hgP
  have hcomm := (commutes_rankOne_of_cartan_eq_zero hQ.extras his hcart).map π'
  intro c hc
  have hcx : c * x = x * c := hcomm c hc x (hA hxA)
  have hcg : c * (g * v * g⁻¹) = (g * v * g⁻¹) * c := by
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hg
    rw [← hm]
    exact ((Commute.zpow_right (show Commute c x from hcx) m)).eq
  have h1 : (g⁻¹ * c * g) * v = v * (g⁻¹ * c * g) := by
    have := congrArg (fun y => g⁻¹ * y * g) hcg
    simp only [mul_assoc, inv_mul_cancel_left] at this ⊢
    simpa [mul_assoc] using this
  have h2 := hfix _ h1
  have := J.mul_mem (J.mul_mem hgJ h2) (J.inv_mem hgJ)
  simpa [mul_assoc] using this

omit [Finite X] in
theorem exists_node_not_rankOne_le (hQ : BorelQuotient D nW H π' M) {J : Subgroup X}
    (hBJ : (borel D H).map π' ≤ J) (hJ : J ≠ ⊤) :
    ∃ j, ¬ (rankOne D.rootGroup j).map π' ≤ J := by
  by_contra hcon
  push Not at hcon
  apply hJ
  have hBA : borel D H ≤ J.comap π' := fun b hb => hBJ ⟨b, hb, rfl⟩
  have htop := eq_borel_sup_rankOne hQ.ct hQ.extras (A := ⊤) le_top
  have hcomap : J.comap π' = ⊤ := by
    refine eq_top_iff.2 ?_
    rw [htop]
    exact sup_le hBA (iSup₂_le fun i _ => Subgroup.map_le_iff_le_comap.1 (hcon i))
  rw [← Subgroup.map_comap_eq_self_of_surjective hQ.surj J, hcomap, ← MonoidHom.range_eq_map]
  exact MonoidHom.range_eq_top.2 hQ.surj

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus
