module

public import CFSG.ClassicalInvolution.Q3.Q3T6CoreLift
public import CFSG.ClassicalInvolution.AschTight.Sec6Gen64A

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinADescent2

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

section Quot

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {N : Subgroup G} [N.Normal]

theorem exists_conj_normalizer_gen (hΩ : HypOmegaGen Ω) (hN : Odd (Nat.card N)) {K : Subgroup G}
    (hK : K ∈ Ω) {U : Subgroup G} (hU2 : IsPGroup 2 U)
    (hUN : ∀ u ∈ U, QuotientGroup.mk' N u ∈
      Subgroup.normalizer ((K.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N))) :
    ∃ n ∈ N, U ≤ Subgroup.normalizer ((conjSub n K : Subgroup G) : Set G) := by
  exact E187C.exists_conj_normalizer_of hΩ.conjInvariant (fun hK hL h => Q3T6.exists_conj_of_map_eq_gen hΩ hN hK hL h) hN hK hU2 hUN

theorem exists_lift_USet_gen (hΩ' : HypOmegaGen (quotFamily Ω N)) (hN : Odd (Nat.card N))
    {J : Subgroup G} (hJ : J ∈ Ω) {Ub : Subgroup (G ⧸ N)} (hUb : Ub ∈ USet (quotFamily Ω N))
    (hUbJ : Ub ≤ J.map (QuotientGroup.mk' N)) :
    ∃ U ∈ USet Ω, U ≤ J ∧ U.map (QuotientGroup.mk' N) = Ub := by
  exact E187C.exists_lift_USet_of (fun hU => Sec6Gen.exists_data_of_mem_USet hΩ' hU)
    (fun hK hJ hA h4 hAK hAJ => Sec6Gen.eq_of_le_of_le hΩ' hK hJ hA h4 hAK hAJ) hN hJ hUb hUbJ

theorem aEmpty_quotFamily_gen (hΩ : HypOmegaGen Ω) (hΩ' : HypOmegaGen (quotFamily Ω N))
    (hN : Odd (Nat.card N)) (hA : ∀ J ∈ Ω, AEmpty Ω J) :
    ∀ M ∈ quotFamily Ω N, AEmpty (quotFamily Ω N) M := by
  rintro _ ⟨K, hK, rfl⟩
  beta_reduce
  intro Jb hJbstar hJbnbr zKb zJb hzKb hzJb
  obtain ⟨J, hJ, rfl⟩ := hJbstar.1
  beta_reduce at hJbstar hJbnbr hzKb hzJb ⊢
  have hstar0 := hJbstar
  obtain ⟨-, hne, Ub, hUb, hUbJ, hUbN⟩ := hstar0
  obtain ⟨U, hU, hUJ, hUmap⟩ := exists_lift_USet_gen hΩ' hN hJ hUb hUbJ
  have hU2 : IsPGroup 2 U := Sec6Gen.isPGroup_of_mem_USet hΩ hU
  obtain ⟨n, hn, hUn⟩ := exists_conj_normalizer_gen hΩ hN hK hU2 (fun u hu =>
    hUbN (hUmap ▸ Subgroup.mem_map_of_mem _ hu))
  have hstar : J ∈ omegaStarNbr Ω (conjSub n K) := by
    refine ⟨hJ, ?_, U, hU, hUJ, hUn⟩
    intro hJK
    apply hne
    rw [hJK, AscQuot.map_conjSub, show QuotientGroup.mk' N n = 1 from
      (QuotientGroup.eq_one_iff _).mpr hn, conjSub_one]
  have hnN : QuotientGroup.mk' N n = 1 := (QuotientGroup.eq_one_iff _).mpr hn
  set K₁ : Subgroup G := conjSub n K with hK₁def
  have hK₁ : K₁ ∈ Ω := hΩ.conjInvariant n K hK
  have himg : K₁.map (QuotientGroup.mk' N) = K.map (QuotientGroup.mk' N) := by
    rw [hK₁def, AscQuot.map_conjSub, hnN, conjSub_one]
  have hnbr : J ∉ omegaNbr Ω K₁ := by
    rintro ⟨-, -, T, hT, hTJ, hTN⟩
    apply hJbnbr
    have hTsyl : IsSylow2In T J := Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hJ hT hTJ
    refine ⟨map_mem_quotFamily hJ, hJbstar.2.1, T.map (QuotientGroup.mk' N),
      mem_RSet_of_isSylow2In (map_mem_quotFamily hJ) (isSylow2In_map_mk hN hTsyl),
      Subgroup.map_mono hTJ, ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    have := mk_mem_normalizer_map (N := N) (hTN ht)
    rwa [himg] at this
  obtain ⟨z₁, hz₁⟩ := Sec6Gen.exists_uniqueInvolution hΩ hK₁
  obtain ⟨zJ, hzJ⟩ := Sec6Gen.exists_uniqueInvolution hΩ hJ
  have e1 : QuotientGroup.mk' N z₁ = zKb := by
    have h1 := isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hN K₁) hz₁
    rw [himg] at h1
    exact h1.eq hzKb
  have e2 : QuotientGroup.mk' N zJ = zJb :=
    (isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hN J) hzJ).eq hzJb
  obtain ⟨g, hg, hgK⟩ := hA K₁ hK₁ J hstar hnbr z₁ zJ hz₁ hzJ
  refine ⟨QuotientGroup.mk' N g, ?_, ?_⟩
  · have h2 := map_pairNormalizers_le (N := N) K₁ J z₁ zJ (Subgroup.mem_map_of_mem _ hg)
    rw [himg, e1, e2] at h2
    exact h2
  · have h3 := congrArg (Subgroup.map (QuotientGroup.mk' N)) hgK
    rw [AscQuot.map_conjSub, himg] at h3
    exact h3

end Quot

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinADescent2
