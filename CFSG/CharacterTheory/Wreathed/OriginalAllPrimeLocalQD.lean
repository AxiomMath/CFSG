module

public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeLocalQDCover
public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeWorkingII
public import CFSG.GroupTheory.QuasiDihedralFusion.InvolutionCentralizer
public import CFSG.LocalAnalysis.ABGTheoremB.IV1
public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.OmnibusQuotient
public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.QCover
public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeLocalQDModel

public section

namespace CFSG.Wreathed.OriginalAllPrime

open CFSG.ABGTheoremB CFSG.QuasiDihedralFusion CFSG.ABGQGroups
open CFSG.Wreathed.CentralSL2Abelianization
open SmallerRecognitionOriginalField TwoCommutingComponentCover
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]

theorem wreathedSetting_qCoverFact
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hlocal : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (centralizerSimpleLayer n hn S e) .PSL 2 p f) :
    (wreathedSetting n S e p f).QCoverFact := by
  intro K hKN hCK hK
  have hp2 : p ≠ 2 := fun h => (by decide : ¬ Odd 2) (h ▸ hpodd)
  obtain ⟨F, hfield, hfinite, Sigma, b, hSigma, φ, hcard, hd, hb, hφ⟩ :=
    LocalQD.exists_modelMap hnonab hfour hp hpodd hf hlocal
  let : Field F := hfield
  let : Finite F := hfinite
  have hm2 := NormalComponentLift.two_pow_eq_two_part hnonab hfour hp hp2 hf hlocal
  let ι : K →* (wreathedSetting n S e p f).N := Subgroup.inclusion hKN
  have hA := LocalQD.isQGroup_range (φ.comp ι)
    (LocalQD.odd_card_ker_comp hφ ι (Subgroup.inclusion_injective hKN)) hK
  have hD : ModelSignalizers.modelC b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn)
      Sigma hSigma ⊓ ModelSignalizers.modelBase b (2 ^ n) (wreathModulus_pos n)
        (wreathModulus_even hn) Sigma hSigma ≤ (φ.comp ι).range := by
    intro w hw
    have hwC := (Subgroup.mem_inf.mp hw).1
    rw [ModelSignalizers.modelC, ← hφ.map_C] at hwC
    obtain ⟨c, hc, rfl⟩ := hwC
    exact ⟨⟨c, hCK (Subgroup.mem_subgroupOf.mp hc)⟩, rfl⟩
  have hML := LocalQD.modelLayer_le_of_isQGroup hp hpodd hf hcard hq hm2 hd hb hA hD
  exact LocalQD.subset_mul_ON_of_modelLayer_le hφ ι (fun k => k.2) hML

theorem wreathedSetting_localQD_charPower
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hlocal : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (centralizerSimpleLayer n hn S e) .PSL 2 p f)
    (hrec : SmallerWreathedRecognition G) :
    ∀ H : Subgroup G, (∃ r : ℕ, r.Prime ∧ CFSG.ABGTheoremB.IsPLocal r H) → IsQDGroup H →
      ∀ r : ℕ, HasQDCharPower H r →
        r = 3 ∨ r = 5 ∨
          (r ∣ (wreathedSetting n S e p f).q ∧ r ≠ (wreathedSetting n S e p f).q) := by
  rintro H ⟨ℓ, hℓ, hloc⟩ hQD r hr
  have hσ := wreathedSetting_isValid hnonab n hn S e hfour p f hp hpodd hf hq hlocal
  have hO : oddCoreIn H ≠ ⊥ := by
    rcases eq_or_ne ℓ 2 with rfl | hℓ2
    · exfalso
      obtain ⟨R, hR, hRp, rfl⟩ := hloc
      have hbot := LocalQD.IsQDGroup.eq_bot_of_normal_isPGroup_two hQD
        (Subgroup.normal_in_normalizer (H := R)) hRp.comap_subtype
      rw [Subgroup.subgroupOf_eq_bot] at hbot
      exact hR (disjoint_self.mp (hbot.mono_right Subgroup.le_normalizer))
    · exact oddCoreIn_ne_bot_of_isPLocal hℓ hℓ2 hloc
  have hHtop : H ≠ ⊤ := by
    rintro rfl
    exact hO (TotallyInverted.Omnibus.oddCoreIn_top_eq_bot hσ)
  have hne : r ≠ (wreathedSetting n S e p f).q := by
    rintro rfl
    exact hO (wreathedSetting_workingHypothesisII hnonab n hn S e hfour p f hp hpodd hf hq hlocal
      hrec H hHtop hr)
  by_cases h3 : r = 3
  · exact Or.inl h3
  by_cases h5 : r = 5
  · exact Or.inr (Or.inl h5)
  refine Or.inr (Or.inr ⟨?_, hne⟩)
  obtain ⟨a, -, ha, -, -, -⟩ := exists_commuting_involutions_of_isQDGroup hQD
  obtain ⟨g, hxa⟩ := original_involution_conjugator hnonab n hn S e (a : G)
    (by rw [Subgroup.orderOf_coe]; exact ha)
  have hfour' := original_conjugated_nonSym4 n hn S e hfour g
  have hlocal' := original_conjugated_same_PSL2_model n hn S e p f hlocal g
  obtain ⟨F, hfield, hfinite, Sigma, b, hSigma, φ, hcard, -, -, hφ⟩ :=
    LocalQD.exists_modelMap hnonab hfour' hp hpodd hf hlocal'
  let : Field F := hfield
  let : Finite F := hfinite
  have hxa' : (wreathedSetting n (conjugatedSylow S g) (conjugatedCoordinates S e g) p f).x =
      (a : G) := hxa
  have hxH : (wreathedSetting n (conjugatedSylow S g) (conjugatedCoordinates S e g) p f).x ∈ H :=
    hxa' ▸ a.2
  have hra := hr.2 ⟨_, hxH⟩ (by rw [show (⟨_, hxH⟩ : H) = a from Subtype.ext hxa']; exact ha)
  exact LocalQD.dvd_of_hasQCharPower _ φ hφ.ker_eq.le hp hpodd hf hcard
    (matrixInclusion F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) Sigma hSigma)
    (matrixInclusion_injective F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) Sigma
      hSigma)
    (commutator_le_matrixLayer F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) Sigma
      hSigma)
    hxH hra h3 h5

theorem wreathedSetting_not_qd_of_cover
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hlocal : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (centralizerSimpleLayer n hn S e) .PSL 2 p f)
    (hrec : SmallerWreathedRecognition G) :
    ∀ H : Subgroup G, (wreathedSetting n S e p f).T ≤ H → oddCoreIn H ≠ ⊥ →
      (((wreathedSetting n S e p f).C ⊓ (wreathedSetting n S e p f).L : Subgroup G) : Set G) ⊆
        (H : Set G) * (((wreathedSetting n S e p f).C ⊓ (wreathedSetting n S e p f).ON :
          Subgroup G) : Set G) → ¬ IsQDGroup H := by
  intro H hTH hO hcov hQD
  have hσ := wreathedSetting_isValid hnonab n hn S e hfour p f hp hpodd hf hq hlocal
  have hp2 : p ≠ 2 := fun h => (by decide : ¬ Odd 2) (h ▸ hpodd)
  obtain ⟨F, hfield, hfinite, Sigma, b, hSigma, φ, hcard, hd, hb, hφ⟩ :=
    LocalQD.exists_modelMap hnonab hfour hp hpodd hf hlocal
  let : Field F := hfield
  let : Finite F := hfinite
  have hm2 := NormalComponentLift.two_pow_eq_two_part hnonab hfour hp hp2 hf hlocal
  have hxH : (wreathedSetting n S e p f).x ∈ H :=
    hTH (Subgroup.subset_closure (Set.mem_insert _ _))
  have hx2 : orderOf (⟨(wreathedSetting n S e p f).x, hxH⟩ : H) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact hσ.x_order
  have hK := (hQD.centralizer_isQGroup _ hx2).1
  have hodd := LocalQD.odd_card_ker_comp hφ (LocalQD.centralizerToN _ hxH)
    (LocalQD.centralizerToN_injective _ hxH)
  have hA := LocalQD.isQGroup_range _ hodd hK
  have hD := LocalQD.centralizer_inf_le_range hφ (Subgroup.mem_sup_right hσ.x₂_mem)
    (TIFacts.modelBase_le_map_L hn hφ) hxH hcov
  have hML := LocalQD.modelLayer_le_of_isQGroup hp hpodd hf hcard hq hm2 hd hb hA hD
  have hNSL := LocalQD.hasNormalSL2_of_modelLayer_le
    (LocalQD.isOddPrimePower_card hp hpodd hf hcard) _
    (LocalQD.le_oddCore_of_normal inferInstance hodd) hML
  rw [hcard] at hNSL
  have hKq : HasQCharPower (Subgroup.centralizer
      ({⟨(wreathedSetting n S e p f).x, hxH⟩} : Set H)) (p ^ f) := ⟨hK, hpodd.pow, hNSL⟩
  have hHq : HasQDCharPower H (wreathedSetting n S e p f).q :=
    ⟨hQD, fun z hz => LocalQD.hasQCharPower_of_isConj (hQD.involutions_isConj _ z hx2 hz) hKq⟩
  have hHtop : H ≠ ⊤ := by
    rintro rfl
    exact hO (TotallyInverted.Omnibus.oddCoreIn_top_eq_bot hσ)
  exact hO (wreathedSetting_workingHypothesisII hnonab n hn S e hfour p f hp hpodd hf hq hlocal
    hrec H hHtop hHq)

end CFSG.Wreathed.OriginalAllPrime
