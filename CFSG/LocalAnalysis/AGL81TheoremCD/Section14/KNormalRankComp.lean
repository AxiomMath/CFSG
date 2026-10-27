module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.FiveTypes
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.NineSixStar
import CFSG.LocalAnalysis.RankThreeUC.AGL81CZComm
import CFSG.LocalAnalysis.RankThreeUC.AGL81CZBridge
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenLayer
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineEightB
import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.StarQuot
import CFSG.LocalAnalysis.SectionRank.AmbientRank
import CFSG.Quasithin.EmptyFaithful.S153DGen

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C

variable {G : Type} [Group G] [Finite G]

theorem FiveTypes.exists_pComponentIn_two_le_pRank {M H : Subgroup G} (hfive : FiveTypes M H) :
    ∃ J₀ : Subgroup G, IsPComponentIn 3 J₀ H ∧ 2 ≤ CFSG.Open.pRank 3 (starImg 3 H J₀) := by
  obtain ⟨J₀, hJ₀, htype⟩ := hfive.exists_isKComp
  refine ⟨J₀, hJ₀.isPComponentIn, ?_⟩
  rcases htype with h34 | h11
  · exact two_le_pRank_starImg_of_isL34Type hJ₀.isPComponentIn h34
  · exact le_trans (by norm_num) (three_le_pRank_starImg_of_isA11Star hJ₀.isPComponentIn h11)

namespace NineSettingGen

variable {M Q H E : Subgroup G}

theorem false_of_three_isPComponentIn (h : NineSettingGen G M 3 Q H E 2)
    (hH2 : H ∈ H2Fam M Q) (h3 : 3 ∉ CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM G M)
    {L I J : Subgroup G} (hL : IsPComponentIn 3 L H) (hI : IsPComponentIn 3 I H)
    (hJ : IsPComponentIn 3 J H) (hLI : L ≠ I) (hLJ : L ≠ J) (hIJ : I ≠ J)
    (hL2 : 2 ≤ CFSG.Open.pRank 3 (starImg 3 H L)) : False := by
  have hKG : CFSG.Open.IsKGroup (StarGroup 3 H) := h.isKGroup_quotient 3
  have hO : CFSG.pPrimeCore 3 (StarGroup 3 H) = ⊥ :=
    CFSG.LocalAnalysis.AGL81TheoremCD.Section15.pPrimeCore_starGroup Nat.prime_three
  have hrank : CFSG.Open.pRank 3 (⊤ : Subgroup (StarGroup 3 H)) ≤ 3 :=
    h.openPRank_starGroup_le_three hH2 h3
  have hLc : CFSG.IsComponent (starImg 3 H L) := isComponent_starImg hL
  have hIc : CFSG.IsComponent (starImg 3 H I) := isComponent_starImg hI
  have hJc : CFSG.IsComponent (starImg 3 H J) := isComponent_starImg hJ
  have hLI' : starImg 3 H L ≠ starImg 3 H I := fun hEq =>
    hLI (eq_of_starImg_eq Nat.prime_three hL hI hEq)
  have hLJ' : starImg 3 H L ≠ starImg 3 H J := fun hEq =>
    hLJ (eq_of_starImg_eq Nat.prime_three hL hJ hEq)
  have hIJ' : starImg 3 H I ≠ starImg 3 H J := fun hEq =>
    hIJ (eq_of_starImg_eq Nat.prime_three hI hJ hEq)
  obtain ⟨B, hBL, hBe, hBc⟩ :=
    CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (p := 3) (k := 2) hL2
  have h4 := CFSG.LocalAnalysis.RankThreeUC.AGL81C.add_two_le_pRank_of_three_components
    Nat.prime_three hLc hIc hJc hLI' hLJ' hIJ' hBL hBe hBc
    (exists_noncentral_of_isComponent hKG hO hIc)
    (exists_noncentral_of_isComponent hKG hO hJc)
  have h4' : 2 + 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (StarGroup 3 H)) := by
    rw [show CFSG.pRank 3 ↥(⊤ : Subgroup (StarGroup 3 H)) =
        CFSG.Open.pRank 3 (⊤ : Subgroup (StarGroup 3 H)) from
      CFSG.SectionRank.pRank_coe_eq_openPRank 3 (⊤ : Subgroup (StarGroup 3 H))] at h4
    exact h4
  omega

theorem mem_normalizer_pComponent_of_odd (h : NineSettingGen G M 3 Q H E 2)
    (hH2 : H ∈ H2Fam M Q) (h3 : 3 ∉ CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM G M)
    {J₀ J : Subgroup G} (hJ₀ : IsPComponentIn 3 J₀ H)
    (h2 : 2 ≤ CFSG.Open.pRank 3 (starImg 3 H J₀)) (hJ : IsPComponentIn 3 J H)
    {x : G} (hx : x ∈ H) (hodd : Odd (orderOf x)) : x ∈ normalizer (J : Set G) := by
  by_contra hxn
  let J₁ : Subgroup G := J.map (MulAut.conj x).toMonoidHom
  let J₂ : Subgroup G := J₁.map (MulAut.conj x).toMonoidHom
  have hJ1 : IsPComponentIn 3 J₁ H := isPComponentIn_conj hJ hx
  have hJ2 : IsPComponentIn 3 J₂ H := isPComponentIn_conj hJ1 hx
  have hJne1 : J ≠ J₁ := fun hEq =>
    hxn (CFSG.Quasithin.A38.map_conj_eq_iff.mp hEq.symm)
  have hJ1ne : J₁ ≠ J := hJne1.symm
  have hJ12ne : J₁ ≠ J₂ := fun hEq =>
    hJ1ne (Subgroup.map_injective (MulAut.conj x).injective hEq.symm)
  have hJ2eq : J₂ = J.map (MulAut.conj (x ^ 2)).toMonoidHom := by
    simpa [J₂, J₁, pow_two] using Subgroup.map_conj_map_conj (R := J) x x
  have hJ2ne : J₂ ≠ J := by
    intro hEq
    exact hxn (CFSG.Quasithin.S153D.mem_normalizer_of_sq_mem hodd
      (CFSG.Quasithin.A38.map_conj_eq_iff.mp (hJ2eq ▸ hEq)))
  rcases eq_or_ne J₀ J with hA | hA
  · subst J₀
    exact false_of_three_isPComponentIn h hH2 h3 hJ₀ hJ1 hJ2 hJne1 hJ2ne.symm hJ12ne h2
  · rcases eq_or_ne J₀ J₁ with hB | hB
    · subst J₀
      exact false_of_three_isPComponentIn h hH2 h3 hJ₀ hJ hJ2 hJ1ne hJ12ne hJ2ne.symm h2
    · exact false_of_three_isPComponentIn h hH2 h3 hJ₀ hJ hJ1 hA hB hJne1 h2

theorem mem_normalizer_kSub_of_odd (h : NineSettingGen G M 3 Q H E 2)
    (hH2 : H ∈ H2Fam M Q) (h3 : 3 ∉ CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM G M)
    {J₀ : Subgroup G} (hJ₀ : IsPComponentIn 3 J₀ H)
    (h2 : 2 ≤ CFSG.Open.pRank 3 (starImg 3 H J₀)) (hL : ¬ pLayerIn 3 H ≤ M)
    {x : G} (hx : x ∈ H) (hodd : Odd (orderOf x)) :
    x ∈ normalizer (kSub 3 M H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro n
  unfold kSub
  rw [if_neg hL]
  constructor
  · intro hn
    exact conj_mem_sSup (y := x) (fun Y hY => by
      refine ⟨isPComponentIn_conj hY.1 hx, ?_⟩
      rw [CFSG.Quasithin.A38.map_conj_eq_iff.mpr
        (mem_normalizer_pComponent_of_odd h hH2 h3 hJ₀ h2 hY.1 hx hodd)]
      exact hY.2) hn
  · intro hn
    have hxinv : x⁻¹ ∈ H := H.inv_mem hx
    have hoddinv : Odd (orderOf x⁻¹) := by rwa [orderOf_inv]
    have hconj := conj_mem_sSup (y := x⁻¹) (fun Y hY => by
      refine ⟨isPComponentIn_conj hY.1 hxinv, ?_⟩
      rw [CFSG.Quasithin.A38.map_conj_eq_iff.mpr
        (mem_normalizer_pComponent_of_odd h hH2 h3 hJ₀ h2 hY.1 hxinv hoddinv)]
      exact hY.2) hn
    simpa [mul_assoc] using hconj

end NineSettingGen

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
