module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.FiveTypes
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.NineTwelveOneAt
import CFSG.GroupTheory.PCore.PrimeSetCore
import CFSG.Models.PGLOrders
import CFSG.RankThree.PartOne.S11d.FinalLemmas

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C

variable {G : Type} [Group G] [Finite G]

@[expose] def calKAll (M : Subgroup G) : Set (Subgroup G) :=
  {J | ∃ (p : ℕ) (Q : Subgroup G), Q ∈ QSet M p ∧ J ∈ calK M Q}

@[expose] def KFactL34NotInvolvedA11 : Prop :=
  ∀ (X : Subgroup (alternatingGroup (Fin 11)))
    (φ : ↥X →* CFSG.PGLModel.projSL 3 (GaloisField 2 2)), ¬ Function.Surjective φ

theorem exists_maximal_calKAll {M J₁ : Subgroup G} (hJ₁ : J₁ ∈ calKAll M) :
    ∃ J, J₁ ≤ J ∧ J ∈ calKAll M ∧ ∀ J' ∈ calKAll M, J ≤ J' → J' = J := by
  obtain ⟨J, hmax⟩ := (Set.toFinite {J | J ∈ calKAll M ∧ J₁ ≤ J}).exists_maximal
    ⟨J₁, hJ₁, le_rfl⟩
  refine ⟨J, hmax.1.2, hmax.1.1, fun J' hJ' hle => ?_⟩
  exact le_antisymm (hmax.2 ⟨hJ', hmax.1.2.trans hle⟩ hle) hle

theorem isSL34Star_of_le
    {M J₁ J : Subgroup G} (hinv : KFactL34NotInvolvedA11) (hJ₁ : IsSL34Star J₁)
    (hle : J₁ ≤ J) (hJ : J ∈ calKAll M) : IsSL34Star J := by
  obtain ⟨p, Q, hQ, H, hH, hcomp, htype⟩ := hJ
  have hdvd : Nat.card (threeStar J₁) ∣ Nat.card (threeStar J) :=
    card_threeStar_dvd_of_le hle
  rw [hJ₁.card_threeStar] at hdvd
  rcases htype with hL34 | hA11
  · rcases hcomp.isL34Star_or_isSL34Star hL34 with hL | hSL
    · rw [hL.card_threeStar] at hdvd
      norm_num at hdvd
    · exact hSL
  · exfalso
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨eA⟩ := hA11
    let π : ↥J →* threeStar J := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥J)
    let f : ↥J₁ →* threeStar J := π.comp (Subgroup.inclusion hle)
    let X : Subgroup (threeStar J) := f.range
    let φ : ↥J₁ →* ↥X := f.rangeRestrict
    have hφsurj : Function.Surjective φ := MonoidHom.rangeRestrict_surjective f
    have hφker : φ.ker.map (Subgroup.inclusion hle) ≤ CFSG.pPrimeCore 3 ↥J := by
      rintro _ ⟨x, hx, rfl⟩
      have hx1 : f x = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
      exact (QuotientGroup.eq_one_iff (Subgroup.inclusion hle x)).mp hx1
    have hkerle : φ.ker ≤ CFSG.pPrimeCore 3 ↥J₁ := by
      have hcop : Nat.Coprime 3 (Nat.card φ.ker) := by
        rw [← Subgroup.card_map_of_injective (Subgroup.inclusion_injective hle)]
        exact CFSG.pPrimeCore_coprime_card.of_dvd_right (Subgroup.card_dvd_of_le hφker)
      have hsupp : CFSG.primeSupported {3}ᶜ (Nat.card φ.ker) :=
        (CFSG.primeSupported_compl_singleton_iff_coprime 3 Nat.prime_three).mpr hcop
      have h := (CFSG.primeSetCore_maximal (G := ↥J₁) {3}ᶜ).2 φ.ker
        (MonoidHom.normal_ker φ) hsupp
      rwa [CFSG.primeSetCore_compl_singleton_eq_pPrimeCore (G := ↥J₁)
        Nat.prime_three] at h
    let O : Subgroup ↥J₁ := CFSG.pPrimeCore 3 ↥J₁
    have hO : φ.ker ≤ (QuotientGroup.mk' O).ker := by
      simpa [O, QuotientGroup.ker_mk'] using hkerle
    let eK : (↥J₁ ⧸ φ.ker) ≃* ↥X := QuotientGroup.quotientKerEquivOfSurjective φ hφsurj
    let θ : ↥X →* threeStar J₁ :=
      (QuotientGroup.lift φ.ker (QuotientGroup.mk' O) hO).comp eK.symm.toMonoidHom
    have hθsurj : Function.Surjective θ := by
      have hlift : Function.Surjective
          (QuotientGroup.lift φ.ker (QuotientGroup.mk' O) hO) := by
        intro y
        obtain ⟨j, rfl⟩ := QuotientGroup.mk'_surjective O y
        exact ⟨QuotientGroup.mk j, by simp [QuotientGroup.lift_mk]⟩
      exact hlift.comp eK.symm.surjective
    obtain ⟨e₁⟩ :=
      nonempty_mulEquiv_projSL_quotient_center_of_isL34Type (L := threeStar J₁) hJ₁.1
    let χ : ↥X →* CFSG.PGLModel.projSL 3 (GaloisField 2 2) :=
      e₁.toMonoidHom.comp ((QuotientGroup.mk' (Subgroup.center (threeStar J₁))).comp θ)
    have hχsurj : Function.Surjective χ :=
      e₁.surjective.comp ((QuotientGroup.mk'_surjective _).comp hθsurj)
    let X' : Subgroup (alternatingGroup (Fin 11)) := X.map eA.toMonoidHom
    let eX : ↥X ≃* ↥X' := Subgroup.equivMapOfInjective X eA.toMonoidHom eA.injective
    exact hinv X' (χ.comp eX.symm.toMonoidHom) (hχsurj.comp eX.symm.surjective)

theorem isA11Star_of_le
    {M J₁ J : Subgroup G} (hJ₁ : IsA11Star J₁) (hle : J₁ ≤ J) (hJ : J ∈ calKAll M) :
    IsA11Star J := by
  obtain ⟨p, Q, hQ, H, hH, hcomp, htype⟩ := hJ
  have hdvd : Nat.card (threeStar J₁) ∣ Nat.card (threeStar J) :=
    card_threeStar_dvd_of_le hle
  rw [hJ₁.card_threeStar] at hdvd
  rcases htype with hL34 | hA11
  · rcases hcomp.isL34Star_or_isSL34Star hL34 with hL | hSL
    · rw [hL.card_threeStar] at hdvd
      norm_num at hdvd
    · rw [hSL.card_threeStar] at hdvd
      norm_num at hdvd
  · exact hA11

theorem card_threeStar_center_dvd_card_solvableRadical {J : Subgroup G}
    (hq : CFSG.IsQuasisimple (threeStar J)) :
    Nat.card (threeStar J ⧸ Subgroup.center (threeStar J)) ∣
      Nat.card (↥J ⧸ CFSG.solvableRadical ↥J) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Group.IsPerfect (threeStar J) := hq.1
  haveI : Nontrivial (threeStar J) := CFSG.LocalCores.isQuasisimple_nontrivial hq
  let R : Subgroup ↥J := CFSG.solvableRadical ↥J
  have hRn : R.Normal := CFSG.ABGLocalTools.solvableRadical_normal
  have hRs : Group.IsSolvable R := CFSG.ABGLocalTools.solvableRadical_isSolvable
  let π : ↥J →* threeStar J := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥J)
  let D : Subgroup (threeStar J) := R.map π
  have hDn : D.Normal := hRn.map π (QuotientGroup.mk'_surjective _)
  have hDs : Group.IsSolvable D := by
    haveI : Group.IsSolvable R := hRs
    exact Group.isSolvable_of_surjective (f := π.subgroupMap R) (π.subgroupMap_surjective R)
  have hDcenter : D ≤ Subgroup.center (threeStar J) := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hDn with htop | hle
    · exfalso
      haveI : Group.IsSolvable (⊤ : Subgroup (threeStar J)) := htop ▸ hDs
      have hsolv : Group.IsSolvable (threeStar J) :=
        Group.isSolvable_of_surjective
          (f := (Subgroup.topEquiv : (⊤ : Subgroup (threeStar J)) ≃* threeStar J).toMonoidHom)
          Subgroup.topEquiv.surjective
      exact Group.IsPerfect.not_isSolvable (threeStar J) hsolv
    · exact hle
  let Z : Subgroup (threeStar J) := Subgroup.center (threeStar J)
  let τ : threeStar J →* threeStar J ⧸ Z := QuotientGroup.mk' Z
  let ρ : ↥J →* threeStar J ⧸ Z := τ.comp π
  have hρker : R ≤ ρ.ker := by
    intro r hr
    rw [MonoidHom.mem_ker]
    exact (QuotientGroup.eq_one_iff (N := Z) (π r)).mpr
      (hDcenter (Subgroup.mem_map_of_mem π hr))
  let ρ' : ↥J ⧸ R →* threeStar J ⧸ Z := QuotientGroup.lift R ρ hρker
  have hρ'surj : Function.Surjective ρ' := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Z y
    obtain ⟨j, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pPrimeCore 3 ↥J) x
    exact ⟨QuotientGroup.mk j, rfl⟩
  exact Subgroup.card_dvd_of_surjective hρ'surj

theorem not_mulEquiv_solvableRadical_alternatingGroup_six_of_type {J : Subgroup G}
    (hq : CFSG.IsQuasisimple (threeStar J))
    (htype : IsL34Type (threeStar J) ∨ IsA11Star J) :
    ¬ Nonempty (↥J ⧸ CFSG.solvableRadical ↥J ≃* alternatingGroup (Fin 6)) := by
  rintro ⟨eA⟩
  have hdiv := card_threeStar_center_dvd_card_solvableRadical hq
  have h360 : Nat.card (↥J ⧸ CFSG.solvableRadical ↥J) = 360 := by
    rw [Nat.card_congr eA.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    rfl
  rw [h360] at hdiv
  rcases htype with h34 | h11
  · obtain ⟨e⟩ := nonempty_mulEquiv_projSL_quotient_center_of_isL34Type h34
    have hcard : Nat.card (threeStar J ⧸ Subgroup.center (threeStar J)) = 20160 := by
      rw [Nat.card_congr e.toEquiv, CFSG.PGLModel.card_projSL_three_four]
    rw [hcard] at hdiv
    norm_num at hdiv
  · have hcard : Nat.card (threeStar J ⧸ Subgroup.center (threeStar J)) = 19958400 := by
      calc Nat.card (threeStar J ⧸ Subgroup.center (threeStar J))
          = Nat.card (threeStar J) := by
            rw [h11.center_eq_bot]
            exact Nat.card_congr (QuotientGroup.quotientBot (G := threeStar J)).toEquiv
        _ = 19958400 := h11.card_threeStar
    rw [hcard] at hdiv
    norm_num at hdiv

namespace HypCGen

theorem isTwoPrimeComponentIn_kSub {M E H J : Subgroup G} (h : HypCGen G M 3 E H)
    (hL : PLayerNotLeAt M)
    (hS : CFSG.LocalAnalysis.ComponentInitial.SchreierFor CFSG.Assembly.InCatalog)
    (hJ : IsKComp M H J)
    (htype : IsL34Type (threeStar J) ∨ IsA11Star J) :
    IsTwoPrimeComponentIn J (kSub 3 M H) := by
  have hTwo := h.isTwoPrimeComponentIn_of_type hS (hL 3 E H h) hJ htype
  exact ⟨hJ.1, hJ.isSubnormal, hTwo.2.2.1, hTwo.2.2.2⟩

end HypCGen

theorem s14Choice_of_maximal {M : Subgroup G} (hC : CStarGen G)
    (hM : CFSG.Open.rankThreeIsMaxTwoLocal M) (hσ : (sigmaSet G M).Nonempty)
    (h1211 : TwelveElevenGen) (hU : NineNineOneAt M) (hL : PLayerNotLeAt M)
    (hS : CFSG.LocalAnalysis.ComponentInitial.SchreierFor CFSG.Assembly.InCatalog)
    {J₀ : Subgroup G} (hJ₀ : J₀ ∈ calKAll M)
    (hmax : ∀ J' ∈ calKAll M, J₀ ≤ J' → J' = J₀)
    (hA : (∃ H' ∈ H2StarAll M, TypeA M H') → IsSL34Star J₀)
    (hB : (¬ ∃ H' ∈ H2StarAll M, TypeA M H') → (∃ H' ∈ H2StarAll M, TypeB M H') →
      IsA11Star J₀) :
    ∃ H E Q : Subgroup G, S14Choice G M H E Q J₀ := by
  obtain ⟨p₀, Q₀, hQ₀, H₀, hH₀, hcomp, htype⟩ := hJ₀
  obtain rfl : p₀ = 3 := eq_three_of_mem_H2StarFam h1211 hC hM hσ hQ₀ hH₀
  obtain ⟨E, -, hE⟩ := exists_hypCGen_of_mem hC hM hσ hQ₀ hH₀
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q, hQ, hEQ⟩ := CFSG.RankThree.PartOne.exists_isSylowOf_ge (p := 3)
    (K := kSub 3 M H₀ ⊔ E) (Q := E) le_sup_right hE.isPGroup
  have hQM : Q ≤ M := hE.le_M_of_isPGroup hU hEQ hQ.isPGroup
  have hQset : Q ∈ QSet M 3 := hE.mem_QSet_of_le hEQ hQM hQ.isPGroup
  have hHQ : H₀ ∈ H2StarFam M Q :=
    mem_H2StarFam_of_le hE.mem (hQ.le.trans (sup_le (kSub_le 3 M H₀) hE.E_le_H))
  have hJstar : J₀ ∈ calKStar M Q :=
    ⟨⟨H₀, hHQ, hcomp, htype⟩, fun J' hJ' hle => hmax J' ⟨3, Q, hQset, hJ'⟩ hle⟩
  exact ⟨H₀, E, Q,
    { cstar := hC
      maxLocal := hM
      sigma_nonempty := hσ
      mem := ⟨3, Q₀, hQ₀, hH₀⟩
      E_le_H := hE.E_le_H
      elem := hE.elem
      card := by rw [hE.card]; norm_num
      gamma := hE.gamma
      E_le_Q := hEQ
      sylow := hQ
      J_comp := hE.isTwoPrimeComponentIn_kSub hL hS hcomp htype
      J_star := hJstar
      prefA := fun h => ⟨J₀, hcomp, hA h⟩
      prefB := fun h h' => ⟨J₀, hcomp, hB h h'⟩ }⟩

theorem choiceExists_of
    {M : Subgroup G} (hC : CStarGen G) (hM : CFSG.Open.rankThreeIsMaxTwoLocal M)
    (hσ : (sigmaSet G M).Nonempty) (h1211 : TwelveElevenGen) (hpre : PreambleTypes M)
    (hU : NineNineOneAt M) (hL : PLayerNotLeAt M)
    (hS : CFSG.LocalAnalysis.ComponentInitial.SchreierFor CFSG.Assembly.InCatalog)
    (hinv : KFactL34NotInvolvedA11) : ChoiceExists M := by
  rintro ⟨H₁, p₁, Q₁, hQ₁, hH₁⟩
  obtain ⟨J₁, hJ₁, hseedA, hseedB⟩ : ∃ J₁ ∈ calKAll M,
      ((∃ H' ∈ H2StarAll M, TypeA M H') → IsSL34Star J₁) ∧
      ((¬ ∃ H' ∈ H2StarAll M, TypeA M H') → (∃ H' ∈ H2StarAll M, TypeB M H') →
        IsA11Star J₁) := by
    by_cases hA : ∃ H' ∈ H2StarAll M, TypeA M H'
    · obtain ⟨H', ⟨p, Q, hQ, hH'⟩, J, hJ, hSL⟩ := hA
      exact ⟨J, ⟨p, Q, hQ, H', hH', hJ, Or.inl hSL.1⟩, fun _ => hSL,
        fun h => absurd ⟨H', ⟨p, Q, hQ, hH'⟩, J, hJ, hSL⟩ h⟩
    · by_cases hB : ∃ H' ∈ H2StarAll M, TypeB M H'
      · obtain ⟨H', ⟨p, Q, hQ, hH'⟩, J, hJ, hA11⟩ := hB
        exact ⟨J, ⟨p, Q, hQ, H', hH', hJ, Or.inr hA11⟩, fun h => absurd h hA,
          fun _ _ => hA11⟩
      · obtain ⟨J, hJ, htype⟩ := FiveTypes.exists_isKComp (hpre p₁ Q₁ hQ₁ H₁ hH₁).2
        exact ⟨J, ⟨p₁, Q₁, hQ₁, H₁, hH₁, hJ, htype⟩, fun h => absurd h hA,
          fun _ h => absurd h hB⟩
  obtain ⟨J₀, hJ₁J₀, hJ₀, hmax⟩ := exists_maximal_calKAll hJ₁
  obtain ⟨H, E, Q, hchoice⟩ := s14Choice_of_maximal hC hM hσ h1211 hU hL hS hJ₀ hmax
    (fun h => isSL34Star_of_le hinv (hseedA h) hJ₁J₀ hJ₀)
    (fun h h' => isA11Star_of_le (hseedB h h') hJ₁J₀ hJ₀)
  exact ⟨H, E, Q, J₀, hchoice⟩

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
