module

public import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2Z_Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.ZJComponent
public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.FF531.Chev
public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542Three.OddCentralize
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.FiveThreeBridge
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.ZJOffender

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.ZJ

open CFSG CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Subgroup
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open scoped commutatorElement

theorem zj_bestOffender_kills_oddCommutator {Y : Type} [Group Y] [Finite Y]
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) Y W) (hρ : Function.Injective ρ)
    {K O A : Subgroup Y} [K.Normal] [O.Normal] (hKperf : ⁅K, K⁆ = K)
    (hA2 : CFSG.IsElementaryAbelian 2 ↥A) (hb : CFSG.RankThree.FFModules.IsBestOffender ρ A)
    (hKA : ⁅K, A⁆ = K) (hOodd : Odd (Nat.card O))
    (h3 : ¬ 3 ∣ Nat.card (⁅K, O⁆ : Subgroup Y)) : ⁅K, O⁆ = ⊥ := by
  classical
  have hRn : (⁅K, O⁆ : Subgroup Y).Normal := inferInstance
  have hRodd : Odd (Nat.card (⁅K, O⁆ : Subgroup Y)) :=
    Odd.of_dvd_nat hOodd (Subgroup.card_dvd_of_le (Subgroup.commutator_le_right K O))
  have hAN : A ≤ Subgroup.normalizer ((⁅K, O⁆ : Subgroup Y) : Set Y) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hRn]
    exact le_top
  have h1 : ⁅(⁅K, O⁆ : Subgroup Y), A⁆ = ⊥ :=
    CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542Three.commutator_eq_bot_of_odd_of_not_three_dvd
      ρ hρ hA2 hb hAN hRodd h3
  have hAR : ⁅A, (⁅K, O⁆ : Subgroup Y)⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact h1
  have hRKA : ⁅⁅(⁅K, O⁆ : Subgroup Y), K⁆, A⁆ = ⊥ := by
    refine le_bot_iff.mp ?_
    calc ⁅⁅(⁅K, O⁆ : Subgroup Y), K⁆, A⁆ ≤ ⁅(⁅K, O⁆ : Subgroup Y), A⁆ :=
          Subgroup.commutator_mono (Subgroup.commutator_le_left _ K) le_rfl
      _ = ⊥ := h1
  have h2 : ⁅⁅K, A⁆, (⁅K, O⁆ : Subgroup Y)⁆ = ⊥ :=
    Subgroup.commutator_commutator_eq_bot_of_rotate (by rw [hAR]; simp) hRKA
  rw [hKA] at h2
  have h4 : ⁅⁅K, K⁆, O⁆ = ⊥ := by
    refine Subgroup.commutator_commutator_eq_bot_of_rotate ?_ ?_
    · rw [Subgroup.commutator_comm]
      exact h2
    · rw [Subgroup.commutator_comm O K, Subgroup.commutator_comm]
      exact h2
  rwa [hKperf] at h4

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
  CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542
  CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs
  CFSG.HardMathSupport.Meierfrankenfeld.AGL81.FF531 in
theorem zj_commutator_le_gnC_of_offender {X : Type} [Group X] [Finite X]
    (hC : CharTwo (⊤ : Subgroup X)) {S K A R : Subgroup X} [K.Normal] [R.Normal]
    (hQS : pCoreOf 2 (⊤ : Subgroup X) ≤ S) (hA : IsMaxElemAbelian S A) (hKperf : ⁅K, K⁆ = K)
    (hKA : ⁅K, A⁆ = K) (hRodd : Odd (Nat.card ↥(R.map (QuotientGroup.mk' (gnC S)))))
    (h3 : ¬ 3 ∣ Nat.card ↥(⁅K, R⁆ : Subgroup X)) : ⁅K, R⁆ ≤ gnC S := by
  have hVT : gnV S ≤ S := gnV_le_of_le hC hQS
  have hV : IsElemAbelian 2 (gnV S) := isElemAbelian_gnV_of_le hC hQS
  letI : Module (ZMod 2) (Additive (IntMod (gnV S) hV)) :=
    binModule (fun v : IntMod (gnV S) hV => IntMod.sq_eq_one v)
  haveI : (K.map (QuotientGroup.mk' (gnC S))).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  haveI : (R.map (QuotientGroup.mk' (gnC S))).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  have key := zj_bestOffender_kills_oddCommutator (gnRep hV) (gnRep_injective hV)
    (K := K.map (QuotientGroup.mk' (gnC S))) (O := R.map (QuotientGroup.mk' (gnC S)))
    (A := A.map (QuotientGroup.mk' (gnC S)))
    (by rw [← Subgroup.map_commutator, hKperf])
    (isElementaryAbelian_map_mk hA) (isBestOffender_gnRep_of_le hV hVT hA)
    (by rw [← Subgroup.map_commutator, hKA]) hRodd
    (by
      rw [← Subgroup.map_commutator]
      exact fun h => h3 (h.trans (Subgroup.card_map_dvd _ _)))
  rw [← Subgroup.map_commutator] at key
  have := (Subgroup.map_eq_bot_iff _).mp key
  rwa [QuotientGroup.ker_mk'] at this

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
  CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542
  CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs
  CFSG.HardMathSupport.Meierfrankenfeld.AGL81.FF531 in
theorem zj_chev_of_component (hFF : FFChevModuleTheorem) {X : Type} [Group X] [Finite X]
    (hsec : CFSG.AGLEmbedding.CatalogSimpleSections X) (hC : CharTwo (⊤ : Subgroup X))
    {S K A : Subgroup X} (hQS : pCoreOf 2 (⊤ : Subgroup X) ≤ S) (hA : IsMaxElemAbelian S A)
    (hO2 : CFSG.pCore 2 (X ⧸ gnC S) = ⊥)
    (hKc : IsComponentOf (K.map (QuotientGroup.mk' (gnC S))) ⊤)
    (hKA : ⁅K.map (QuotientGroup.mk' (gnC S)), A.map (QuotientGroup.mk' (gnC S))⁆ ≠ ⊥) :
    FFChevConclusion (↥(K.map (QuotientGroup.mk' (gnC S))) ⧸
      Subgroup.center ↥(K.map (QuotientGroup.mk' (gnC S)))) := by
  have hVT : gnV S ≤ S := gnV_le_of_le hC hQS
  have hV : IsElemAbelian 2 (gnV S) := isElemAbelian_gnV_of_le hC hQS
  letI : Module (ZMod 2) (Additive (IntMod (gnV S) hV)) :=
    binModule (fun v : IntMod (gnV S) hV => IntMod.sq_eq_one v)
  have hK : CFSG.Open.IsKGroup (X ⧸ gnC S) :=
    CFSG.AGLEmbedding.catalogSimpleSections_iff_isKGroup.mp (hsec.quotient (gnC S))
  exact chevConclusion_of_component hFF (X ⧸ gnC S) (Additive (IntMod (gnV S) hV)) (gnRep hV)
    (gnRep_injective hV) hK hO2 _ (isElementaryAbelian_map_mk hA)
    (isBestOffender_gnRep_of_le hV hVT hA) _ hKc hKA

theorem kFactZJFactorization_of_ffChev
    (hFF : CFSG.HardMathSupport.Meierfrankenfeld.AGL81.FF531.FFChevModuleTheorem) :
    KFactZJFactorization := by
  intro p hp hp2 X _ _ hsec hcent _ _ K hKn hK hT h3 h2cl S hS2 hcore hchar
  haveI : K.Normal := hKn
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨T, hKT⟩ := hT
  haveI : Nontrivial X := zj_nontrivial_of_pComponent hK
  have hCh : CharTwo (⊤ : Subgroup X) := by
    unfold CharTwo
    rw [pCoreOf_top]
    exact inf_le_right.trans hcent
  have hQS : pCoreOf 2 (⊤ : Subgroup X) ≤ S := by
    rw [pCoreOf_top]
    exact hcore
  haveI : (gnC S).Normal := gnC_normal S
  have hKC : ¬ K ≤ gnC S := zj_not_le_centralizer hS2 hcore hcent hchar
  have hcoreC : CFSG.pCore 2 X ≤ gnC S := zj_pCore_le_gnC hcore hcent
  have hO2 := zj_pCore_quotient_eq_bot hp hp2 hK T hKT h2cl hcoreC hKC
  obtain ⟨A, hAmax, hAnot⟩ := zj_exists_offender hS2 hcore hcent hchar
  have hA2 : IsPGroup 2 A := hS2.to_le hAmax.1
  have hKA : ⁅K, A⁆ = K := zj_commutator_eq_of_not_le_pCore hp hp2 hK T hKT h2cl hA2 hAnot
  have hRodd : Odd (Nat.card ↥((K ⊓ CFSG.pPrimeCore p X).map (QuotientGroup.mk' (gnC S)))) :=
    zj_odd_card_map_le_pPrimeCore h2cl hcoreC inf_le_right
  have hle : K ⊓ CFSG.pPrimeCore p X ≤ (CFSG.pPrimeCore p ↥K).map K.subtype := by
    rw [zj_pPrimeCore_eq_subgroupOf, Subgroup.subgroupOf_map_subtype, inf_comm]
  have h3' : ¬ 3 ∣ Nat.card ↥(⁅K, K ⊓ CFSG.pPrimeCore p X⁆ : Subgroup X) := fun h =>
    h3 (h.trans (Subgroup.card_dvd_of_le (Subgroup.commutator_mono le_rfl hle)))
  have hcentC := zj_commutator_le_gnC_of_offender hCh hQS hAmax (zj_pComponent_perfect hK) hKA
    hRodd h3'
  have hcentC' : ⁅K ⊓ CFSG.pPrimeCore p X, K⁆ ≤ gnC S := by
    rw [Subgroup.commutator_comm]
    exact hcentC
  obtain ⟨hq, ⟨e⟩⟩ := zj_component_image hK hKC
    (fun r hr y hy => hcentC' (Subgroup.commutator_mem_commutator hr hy))
  haveI : (K.map (QuotientGroup.mk' (gnC S))).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  have hKc : IsComponentOf (K.map (QuotientGroup.mk' (gnC S))) ⊤ :=
    (CFSG.isComponent_iff_open _).mp ⟨hq, Subgroup.Normal.isSubnormal inferInstance⟩
  have hKA' : ⁅K.map (QuotientGroup.mk' (gnC S)), A.map (QuotientGroup.mk' (gnC S))⁆ ≠ ⊥ := by
    rw [← Subgroup.map_commutator, hKA]
    intro hbot
    apply hKC
    intro k hk
    have hmem : QuotientGroup.mk' (gnC S) k ∈ K.map (QuotientGroup.mk' (gnC S)) := ⟨k, hk, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact (QuotientGroup.eq_one_iff k).mp hmem
  have hFFC := zj_chev_of_component hFF hsec hCh hQS hAmax hO2 hKc hKA'
  have hres := CFSG.HardMathSupport.Meierfrankenfeld.AGL81.FF531.ffChevConclusion_of_mulEquiv
    e.symm hFFC
  rcases hres with h | ⟨m, -, hm⟩
  · exact Or.inl h
  · exact Or.inr ⟨m, hm⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.ZJ
