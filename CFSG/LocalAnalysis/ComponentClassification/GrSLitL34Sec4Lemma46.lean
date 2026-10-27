module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Lemma43
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.ComponentClassification.GrSLit.GrS4

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem normalizer_ne_top_of_odd [IsSimpleGroup G] {W : Subgroup G} (hW : W ≠ ⊥)
    (hWodd : Odd (Nat.card W)) {a : G} (ha2 : orderOf a = 2) :
    normalizer (W : Set G) ≠ ⊤ := by
  intro hMt
  have hWn : W.Normal := by
    constructor
    intro w hw g
    have hg : g ∈ normalizer (W : Set G) := by rw [hMt]; exact mem_top g
    exact (mem_normalizer_iff.mp hg w).mp hw
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal W with h | h
  · exact hW h
  · have h2 : 2 ∣ Nat.card W := by
      rw [h, card_top, ← ha2]
      exact orderOf_dvd_natCard a
    exact (Nat.not_even_iff_odd.mpr hWodd) (even_iff_two_dvd.mpr h2)

omit [Finite G] in
theorem exists_sq_ne_one_of_exponent_eq_four {H : Subgroup G}
    (h : Monoid.exponent ↥H = 4) : ∃ z ∈ H, z * z ≠ 1 := by
  by_contra hno
  push Not at hno
  have hdvd : Monoid.exponent ↥H ∣ 2 := Monoid.exponent_dvd_of_forall_pow_eq_one fun y =>
    Subtype.ext (by simpa [pow_two] using hno y y.2)
  rw [h] at hdvd
  exact absurd hdvd (by norm_num)

end CFSG.ComponentClassification.GrSLit.GrS4

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS GrS4

theorem l34Lemma46_of_inputs (hSol : SolomonCommutingCoreInput) (hKG : L34UnbalancedKGroupInput)
    (h43 : L34Lemma43) (h44 : L34Lemma44) (hU : L34UnbalancingUnitaryStep)
    (hC : L34UnitaryCentralizerFact) (hCF : L34CentralFourFact) (hWS : L34Lemma46WStep)
    (hEnd : L34Lemma46EndStep) : L34Lemma46 := by
  intro G _ _ a x J S A hset hcent hZ hrun
  obtain ⟨h3, hexp⟩ := h43 G a x J S A hset hcent hZ hrun
  by_cases hcyc : IsCyclic ↥(S ⊓ zStarIn J)
  · exact ⟨hcyc, by rw [← hexp, IsCyclic.exponent_eq_card]⟩
  exfalso
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hbase, hU3, hL34, -, hS, haS, hxS⟩ := id hset
  obtain ⟨hsimple, -, hK, -, -, hLB, -, -⟩ := hbase
  have : IsSimpleGroup G := hsimple
  have hGW : GWTwoBalanced G := gwTwoBalanced_of_locallyTwoBalanced hSol hLB
  have ha2 : orderOf a = 2 := hU3.1
  have hx2 : orderOf x = 2 := hU3.2.1
  have hax : a * x = x * a := hU3.2.2.1
  have hJa : J ≤ centralizer ({a} : Set G) := hU3.2.2.2.1
  have hJc := hU3.2.2.2.2.1
  have hJper : ⁅J, J⁆ = J := commutator_eq_of_isPComponent hJa hJc
  have hSN : S ≤ normalizer (J : Set G) := hS.1
  set P : Subgroup G := S ⊓ J with hPdef
  have hP : IsSylowTwoIn P J := isSylowTwoIn_inf hS
  have hZJ : zStarIn J ≤ J := map_subtype_le _
  have hZP : P ⊓ zStarIn J = S ⊓ zStarIn J := by
    rw [hPdef, inf_assoc, inf_eq_right.mpr hZJ]
  have hxU : IsL34Unitary J x := hU G a x J hU3 hL34
  have hxP : x ∈ normalizer (P : Set G) := inf_mem_normalizer (le_normalizer hxS) (hSN hxS)
  obtain ⟨-, h8, -, -, -, hel, -, -⟩ := hC G J P x hJper hL34 hxU hP hxP
  set R : Subgroup G := P ⊓ centralizer ({x} : Set G) with hRdef
  have hR : IsEightGroup R := ⟨hel (by rwa [hZP]), h8⟩
  obtain ⟨⟨hBe, hB16⟩, hgen⟩ := h44 G a x J S A hset hrun hcyc
  set B : Subgroup G := R ⊔ zpowers x with hBdef
  have hRW : R ≤ withKernel J := (inf_le_left.trans inf_le_right).trans le_sup_left
  have hWne : wGroup R ≠ ⊥ := hWS G a x J S A hset hrun hexp hcyc R hRW hR
  set W : Subgroup G := wGroup R with hWdef
  have hWB : wGroup B = W := wGroup_eq_of_le_eight hGW hBe le_sup_left hR.2
  have hWodd : Odd (Nat.card W) := by
    have h := (CFSG.ClassicalInvolution.Balance.isComplete_deltaCore hBe.isElemAbelian
      (by rw [hB16]) (twoBalancedWrt_of_gwTwoBalanced hGW hBe)).1.1
    rw [← hWB, wGroup_eq_completion hBe]
    exact Nat.coprime_two_left.mp h
  set M : Subgroup G := normalizer (W : Set G) with hM
  obtain ⟨C, hCP, hCe, hC16, hRC, hCZ, hNC⟩ := hCF G J P x hJper hL34 hP hxU hxP
    (by rwa [hZP]) (by rw [hZP]; exact exists_sq_ne_one_of_exponent_eq_four hexp)
  have hWC : wGroup C = W := wGroup_eq_of_le_eight hGW hCe hRC hR.2
  have hJeq := hgen C hCP hCe hC16 hRC (by rwa [hZP] at hCZ)
  have hJM : J ≤ M := by
    rw [hJeq]
    refine iSup_le fun E => iSup_le fun hE => iSup_le fun hE8 => ?_
    have hWE : wGroup E = W := by
      rcases hE with hEB | hEC
      · rw [← hWB]
        exact (wGroup_eq_of_le_eight hGW hBe hEB hE8.2).symm
      · rw [← hWC]
        exact (wGroup_eq_of_le_eight hGW hCe hEC hE8.2).symm
    intro g hg
    have := mem_normalizer_wGroup (mem_inf.mp hg).2
    rwa [hWE] at this
  have hNJ : normalizer (J : Set G) ≤ M := by
    intro n hn
    obtain ⟨m, hmJ, k, hkN, rfl⟩ := exists_mul_mem_normalizer_of_isSylowTwoIn hP hn
    have hk : k ∈ M := by
      have := mem_normalizer_wGroup (hNC hkN)
      rwa [hWC] at this
    exact mul_mem (hJM hmJ) hk
  have hMtop : M ≠ ⊤ := normalizer_ne_top_of_odd hWne hWodd ha2
  have hDxN := oddIn_inf_le_normalizer hSol hx2 ha2 hax.symm hJa hJc
  obtain ⟨K, hKM, hKc, hcase⟩ := exists_component_of_unbalancedKGroup hKG hSol hK hMtop hU3 hL34
    (hNJ (hSN haS)) (hNJ (hSN hxS)) hJM (hDxN.trans hNJ)
  exact hEnd G a x J S A hset hcent hZ hrun h3 hexp hcyc W hWne hWodd rfl hNJ K hKM hKc hcase

end CFSG.ComponentClassification.GrSLit
