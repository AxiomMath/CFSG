module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4HDNStep
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4HDNClosed
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4HDCaseTwo
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4HDType
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeSingle
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitSol25
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma45c

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

theorem heldSingleComponentStep_of_normal
    (hSN : HeldSingleNormalStep)
    (hMax : MaximalTwoComponentInputHe) (hS : SchreierFor Blueprint.Catalog)
    (hHN : HeldNotProperFixedInput) (h64 : HeldSylowElementarySixtyFour)
    (hOut : HeldOuterInvolutionRank) (hMult : TBLit.HeldTrivialMultiplier)
    (hGold : GoldschmidtStronglyClosedInput) : HeldSingleComponentStep := by
  intro X _ _ L hset S hSyl W hW hWodd hWB hNL
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hsimp, hnab, hK, hU, hloc, ⟨a, ha2, hLa, hLc⟩, ⟨e⟩⟩ := id hset
  have : IsSimpleGroup X := hsimp
  have hHe := nonempty_fusionZStar_equiv_held e
  have hmax : GSWeakMaximalComponent L :=
    gsWeakMaximalComponent_of_held hS hHN hnab hK ha2 hLa hLc hHe
  have haN : a ∈ normalizer (L : Set X) := mem_normalizer_of_commute fun x hx =>
    (mem_centralizer_singleton_iff.mp (hLa hx)).symm
  obtain ⟨S₀, hSyl₀, -⟩ := exists_isSylowTwoIn_mem haN ha2
  obtain ⟨E, hET, -, hEe, hE64⟩ := exists_elem_sixtyFour e h64 inf_le_right
    (hSyl₀.isPGroup.to_le inf_le_left) (card_inf_eq_1024 e hSyl₀)
  have hrank : 3 ≤ pRank 2 ↥L := three_le_pRank_of_le hEe (by omega) (hET.trans inf_le_right)
  have hgs : GSMaximalSetting X a L :=
    ⟨hsimp, hnab, hK, hU, ha2, hLa, hLc, hmax, hrank, Sol78.not_psp4_of_held e,
      Or.inr (nonempty_fusionZStar_equiv_held e)⟩
  have hMtop : normalizer (W : Set X) ≠ ⊤ := GrS4.normalizer_ne_top_of_odd hW hWodd ha2
  have hLN : L ≤ normalizer (W : Set X) := le_normalizer.trans hNL
  have haM : a ∈ normalizer (W : Set X) := hNL haN
  have hT : L ≤ centralizer ({a} : Set X) ⊓ normalizer (W : Set X) := le_inf hLa hLN
  have hTpc := UnbalancedCorr.isPComponent_subgroupOf_of_le hT inf_le_left hLc
  obtain ⟨K, hKM, hKc, hLKK, hLKKpc⟩ := UnbalancedCorr.exists_orbit_component ha2 haM hT hTpc
    (HeSingle.le_map_pLayer ha2 haM hT hTpc)
  have hCaN := GrS4.centralizer_le_normalizer_of_gsMaximalSetting_he hMax hgs hHe
  have haa : a * a = 1 := by rw [← pow_two, ← ha2, pow_orderOf_eq_one]
  have ha1 : a ≠ 1 := fun h => by rw [h, orderOf_one] at ha2; exact absurd ha2 (by norm_num)
  obtain ⟨S₁, hS₁, haS₁⟩ := exists_isSylowTwoIn_mem
    (mem_centralizer_singleton_iff.mpr rfl : a ∈ centralizer ({a} : Set X)) ha2
  have hS₁M : S₁ ≤ normalizer (W : Set X) := hS₁.1.trans (hCaN.trans hNL)
  have hp : IsPGroup 2 (S₁.subgroupOf (normalizer (W : Set X))) :=
    hS₁.isPGroup.of_equiv (subgroupOfEquivOfLe hS₁M).symm
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  set T : Subgroup X := (P : Subgroup ↥(normalizer (W : Set X))).map
    (normalizer (W : Set X)).subtype with hTdef
  have hTsyl : IsSylowTwoIn T (normalizer (W : Set X)) :=
    ⟨map_subtype_le _, P, (comap_map_eq_self_of_injective (normalizer (W : Set X)).subtype_injective
      _).symm⟩
  have hS₁T : S₁ ≤ T := fun s hs => ⟨⟨s, hS₁M hs⟩, hP (mem_subgroupOf.mpr hs), rfl⟩
  have haT : a ∈ T := hS₁T haS₁
  obtain ⟨A, hAT, -, hAe, hA64⟩ := exists_elem_sixtyFour e h64 inf_le_right
    (hSyl.isPGroup.to_le inf_le_left) (card_inf_eq_1024 e hSyl)
  obtain ⟨A₀, hA₀A, hA₀8⟩ := exists_le_card_eight hAe.isPGroup (by omega)
  have hGWB : GWTwoBalanced X := gwTwoBalanced_of_locallyTwoBalanced solomonCommutingCoreInput hloc
  have hWA : wGroup A = W := (wGroup_eq_of_le_eight hGWB hAe hA₀A hA₀8).trans
    (hWB A₀ ((hA₀A.trans hAT).trans inf_le_left) (hAe.mono hA₀A) hA₀8)
  exfalso
  by_cases hKa : conjugate K a = K
  ·
    rw [hKa, sup_idem] at hLKK hLKKpc
    obtain ⟨hle, heq⟩ := UnbalancedGS.OrbitFixedComponent.stable_case K
      (K ⊓ centralizer ({a} : Set X)) inf_le_left L (le_inf hLKK hLa) hLKKpc
    rcases hle.lt_or_eq with hlt | hidx
    · exact HeSingle.not_isHeldType_of_lt hHN hK hMtop hKM hKc ha2 hKa (le_inf hLKK hLa)
        hLKKpc hlt hHe
    · have hsup := (heq hidx).2
      have hOM := HeSingle.map_pPrimeCore_le_oddIn hKM hKc
      have hsupM : L ⊔ oddIn (normalizer (W : Set X)) = K ⊔ oddIn (normalizer (W : Set X)) := by
        apply le_antisymm (sup_le_sup_right hLKK _)
        refine sup_le ?_ le_sup_right
        rw [← hsup]
        exact sup_le le_sup_left (hOM.trans le_sup_right)
      have hKn := hSN X L hset S hSyl W hW hWodd hWB hNL K hKM hKc hsupM
      obtain ⟨e₁⟩ := HeNormal.held_equiv_of_sup_eq hLKK hsup hidx e
      have hak := HeNormal.mem_coreActionKernel_of_sup_eq hLKK hsup
        (HeDiag.mem_normalizer_iff_conjugate_eq.mpr hKa) hLa
      exact HeNormal.false_of_normal hnab hGWB h64 hOut hGold e₁ hKM hKn hTsyl haT ha1 hak hAe
        (by omega) (by rw [hWA])
  have hLKKO : L ≤ K ⊔ conjugate K a ⊔ oddIn (normalizer (W : Set X)) := hLKK.trans le_sup_left
  by_cases hr : ∃ r : X, orderOf r = 2 ∧ a * r = r * a ∧ r ∈ normalizer (W : Set X) ∧
      r ∈ normalizer (K : Set X) ∧ r ∈ normalizer (conjugate K a : Set X) ∧
      (∀ k ∈ K, k⁻¹ * r⁻¹ * k * r ∈ oddIn (normalizer (W : Set X))) ∧
      (∀ k ∈ conjugate K a, k⁻¹ * r⁻¹ * k * r ∈ oddIn (normalizer (W : Set X)))
  · obtain ⟨r, hr2, har, hrM, hrK, hrK', hrKc, hrK'c⟩ := hr
    exact HeDiag.false_of_core_trivial_involution hMax hS hHN h64 hMult hnab hK hU ha2 hr2 har
      hLa hLc e hCaN hLN haM hrM hKM hKc hKa hLKKO hrK hrK' hrKc hrK'c
  have hno : ∀ r : X, orderOf r = 2 → a * r = r * a → r ∈ normalizer (W : Set X) →
      r ∈ normalizer (K : Set X) → r ∈ normalizer (conjugate K a : Set X) →
      (∀ k ∈ K, k⁻¹ * r⁻¹ * k * r ∈ oddIn (normalizer (W : Set X))) →
      (∀ k ∈ conjugate K a, k⁻¹ * r⁻¹ * k * r ∈ oddIn (normalizer (W : Set X))) → False :=
    fun r h1 h2 h3 h4 h5 h6 h7 => hr ⟨r, h1, h2, h3, h4, h5, h6, h7⟩
  have honly := fun (K₂ : Subgroup X) (hK₂M : K₂ ≤ normalizer (W : Set X))
    (hK₂c : IsPComponent 2 (K₂.subgroupOf (normalizer (W : Set X)))) =>
    HeDiag.eq_or_eq_of_isPComponent ha2 haM hKM hKc hno hK₂M hK₂c
  obtain ⟨e₁⟩ := HeDiag.held_equiv_of_moved hMult ha2 haM hKM hKc hKa hLa hLc hLKK hLKKpc e
  have hK'a : conjugate (conjugate K a) a = K := by
    rw [conjugate_conjugate, haa, conjugate_one]
  obtain ⟨e₂⟩ := HeDiag.held_equiv_of_moved hMult ha2 haM (conjugate_le_of_mem hKM haM)
    (isPComponent_conjugate_subgroupOf haM hKc) (by rw [hK'a]; exact fun h => hKa h.symm) hLa hLc
    (by rw [hK'a, sup_comm]; exact hLKK) (by rw [hK'a, sup_comm]; exact hLKKpc) e
  have hTa : T ⊓ centralizer ({a} : Set X) = S₁ :=
    hS₁.eq_of_le (le_inf hS₁T hS₁.1) inf_le_right (hTsyl.isPGroup.to_le inf_le_left)
  have haext : IsExtremalIn T a := by
    obtain ⟨-, P₁, hP₁⟩ := hS₁
    exact ⟨haT, P₁, by rw [hTa, hP₁]⟩
  obtain ⟨hcard₁, hcard₂⟩ := HeDiag.card_inf_eq_of_isSylowTwoIn e₁ haa haT hKM hKc honly hTsyl
  have hdata : HeDiag.SwapData (normalizer (W : Set X)) K T a :=
    ⟨ha2, haM, hKM, hKc, hKa, honly, HeDiag.inf_coreActionKernel_eq_bot haM hKM hKc honly hno
      hTsyl.isPGroup hTsyl.1 haT, hTsyl.isPGroup, hTsyl.1, haT, hcard₁, hcard₂⟩
  exact HeDiag.false_of_swap hnab hGWB h64 hOut hdata e₁ e₂ hAe (by omega) (by rw [hWA]) hTsyl
    haext

end CFSG.ComponentClassification.GrSLit
