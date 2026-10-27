module

public import CFSG.ClassicalInvolution.AschTight.C195Main
public import CFSG.ClassicalInvolution.AschTight.E2StarTargets
public import CFSG.ClassicalInvolution.AschTight.Sec19Targets2
public import CFSG.ClassicalInvolution.Asc77.AscL62Final

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable (p f : ℕ) [Fact p.Prime]

theorem l6_2ModTmp : L6_2ModTmp p f :=
  Asc77.l6_2 p f

variable {p f}

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem conj_mem_xGroup {K : Subgroup G} {z : G} (hΩ : ConjInvariant (CoreAssembly.conjClass K))
    {c : G} (hc : c ∈ Subgroup.centralizer ({z} : Set G)) {x : G} (hx : x ∈ xGroup K z) :
    c * x * c⁻¹ ∈ xGroup K z := by
  have hle : xGroup K z ≤ conjSub c⁻¹ (xGroup K z) := by
    refine iSup₂_le fun A hA a ha => ?_
    rw [mem_conjSub_iff, inv_inv]
    have hA' : conjSub c A ∈ {V : Subgroup G | (V ∈ RSet (CoreAssembly.conjClass K) ∨
        V ∈ USet (CoreAssembly.conjClass K)) ∧ V ≤ Subgroup.centralizer ({z} : Set G)} := by
      refine ⟨hA.1.imp (fun h => RSet.conj hΩ h c) (fun h => USet.conj hΩ h c), ?_⟩
      rintro _ ⟨y, hy, rfl⟩
      exact (Subgroup.centralizer _).mul_mem ((Subgroup.centralizer _).mul_mem hc (hA.2 hy))
        ((Subgroup.centralizer _).inv_mem hc)
    exact (le_iSup₂ (f := fun (V : Subgroup G) (_ : V ∈ {V : Subgroup G |
      (V ∈ RSet (CoreAssembly.conjClass K) ∨ V ∈ USet (CoreAssembly.conjClass K)) ∧
        V ≤ Subgroup.centralizer ({z} : Set G)}) => V) (conjSub c A) hA') (conj_mem_conjSub ha)
  have h1 := hle hx
  rwa [mem_conjSub_iff, inv_inv] at h1

variable [IsSimpleGroup G] {K : Subgroup G} {z : G} {S : Sylow 2 G} {W : Subgroup G}

theorem mem_xGroup_of_c19_16S (h16 : C19_16STmp p f) (hd : Sec19Data p f K z S W) {x : G}
    (hx : x ∈ Subgroup.centralizer ({z} : Set G)) (hx2 : IsPGroup 2 (Subgroup.zpowers x)) :
    x ∈ xGroup K z := by
  have hΩ := hypOmegaMod_of_tightD hd.tight
  obtain ⟨c, hc, hcx⟩ := exists_conj_le_of_sylow_le S hd.hSz (Subgroup.zpowers_le.mpr hx) hx2
  have h1 : c * x * c⁻¹ ∈ xGroup K z := by
    rw [xGroup_eq_gammaGen]
    exact h16 G K z S W hd (hcx (conj_mem_conjSub (Subgroup.mem_zpowers x)))
  have h2 := conj_mem_xGroup hΩ.conjInvariant (Subgroup.inv_mem _ hc) h1
  rwa [show c⁻¹ * (c * x * c⁻¹) * c⁻¹⁻¹ = x by group] at h2

theorem innerDiagonalTwo_of_sec19 (h16 : C19_16STmp p f) (hd : Sec19Data p f K z S W) :
    InnerDiagonalTwo p f K := by
  intro e hFcard hF h3 x hx
  refine c19_5Tmp_of_l6_2 p f (l6_2ModTmp p f) G K z hd.tight e hFcard hF h3 x ?_
  refine mem_xGroup_of_c19_16S h16 hd ?_ ?_
  · rw [← normalizer_eq_centralizer_of_tight hd.tight.toTightBranch]
    exact x.2
  · have := hx.map (Subgroup.normalizer (K : Set G)).subtype
    rwa [MonoidHom.map_zpowers] at this

theorem exists_wSet_le (ht : S19R.TightStd p f K z) (S : Sylow 2 G) :
    ∃ W ∈ WSet (CoreAssembly.conjClass K), W ≤ (S : Subgroup G) := by
  obtain ⟨η, hη, hinv⟩ := (l6_9_proved p f ht.branch.odd ht.branch.five G _
    (hypOmegaMod_of_tightD ht) S).1
  exact ⟨⨆ U ∈ η, U, ⟨η, ⟨S, hη, hinv⟩, rfl⟩, iSup₂_le fun U hU => (hη.1 hU).2⟩

variable (p f) in
theorem tightControlledD_of_targets (hB3 : GoldschmidtB3Tmp) (h6 : C19_6Tmp p f)
    (h14 : C19_14Tmp p f) (h16 : C19_16STmp p f) (hIH : IHAllD p f) : TightControlledD p f := by
  intro G _ _ _ K z ht0
  have ht := S19R.tightStd_of_tightBranchD ht0
  by_cases hc : ConcOrTF4 G
  · exact hc.conclusionD ht.branch.notFourGenerated
  exfalso
  by_cases hA : AllTypeTwo K z
  · exact false_of_allTypeTwo hB3 ht hA
  obtain ⟨Q₀, S, hRS, -, hSz, -⟩ := exists_sylow_setup ht
  obtain ⟨W, hWmem, hWS⟩ := exists_wSet_le ht S
  have hd : Sec19Data p f K z S W :=
    ⟨ht, hA, hIH G K z ht.branch, hc, ⟨Q₀, hRS⟩, hSz, hWmem, hWS⟩
  have hE2 := cStarTwoRankOne_of_quaternion_of_le hd
    ((h6 G K z S W hd).resolve_left (h14 G K z S W hd)) (h16 G K z S W hd)
  have hE3 := normalizerQuotientTwoGeneratedStar_of_innerDiagonalTwo ht.branch.odd
    ht.branch.five ht.branch.member (innerDiagonalTwo_of_sec19 h16 hd)
  exact ht.branch.notFourGenerated (twoSubgroupsFourGenerated_of_edgeless_star ht.branch.odd
    ht.branch.five ht.branch.member ht0.control (deltaEdgeless_of_dEdgeless ht.edgeless)
    (commutingSylowForcesCommuting_of_tightD ht) hE2 hE3)

end CFSG.ClassicalInvolution.Disconnected.AschTight
