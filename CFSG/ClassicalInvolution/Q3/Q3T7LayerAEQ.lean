module

public import CFSG.ClassicalInvolution.Q3.Q3T7LayerQ
public import CFSG.ClassicalInvolution.Q3.Q3T7LayerAE
public import CFSG.ClassicalInvolution.Q3.Q3T6CoreLift
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinADescent2Quot

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Q3.Q3T6
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Disc3
open scoped commutatorElement

section Quot

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {N : Subgroup G} [N.Normal]

theorem exists_conj_normalizer3 (hΩ : HypOmegaGen Ω) (hN : Odd (Nat.card N)) {K : Subgroup G}
    (hK : K ∈ Ω) {U : Subgroup G} (hU2 : IsPGroup 2 U)
    (hUN : ∀ u ∈ U, QuotientGroup.mk' N u ∈
      Subgroup.normalizer ((K.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N))) :
    ∃ n ∈ N, U ≤ Subgroup.normalizer ((conjSub n K : Subgroup G) : Set G) := by
  refine exists_conj_normalizer_of_perm hN K hU2 fun u hu => ?_
  have himg : K.map (QuotientGroup.mk' N) = (conjSub u K).map (QuotientGroup.mk' N) := by
    rw [AscQuot.map_conjSub]
    exact (mem_normalizer_iff_conjSub_eq.mp (hUN u hu)).symm
  obtain ⟨n, hn, hnK⟩ := exists_conj_of_map_eq_gen hΩ hN hK (hΩ.conjInvariant u K hK) himg
  exact ⟨n, hn, hnK⟩

theorem exists_lift_USet3 (hΩ' : HypOmegaGen (quotFamily Ω N)) (hN : Odd (Nat.card N))
    {J : Subgroup G} (hJ : J ∈ Ω) {Ub : Subgroup (G ⧸ N)} (hUb : Ub ∈ USet (quotFamily Ω N))
    (hUbJ : Ub ≤ J.map (QuotientGroup.mk' N)) :
    ∃ U ∈ USet Ω, U ≤ J ∧ U.map (QuotientGroup.mk' N) = Ub :=
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinADescent2.exists_lift_USet_gen hΩ' hN hJ hUb hUbJ

theorem exists_conj_omegaStarNbr3 (hΩ : HypOmegaGen Ω) (hΩ' : HypOmegaGen (quotFamily Ω N))
    (hN : Odd (Nat.card N)) {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω)
    (h : J.map (QuotientGroup.mk' N) ∈
      omegaStarNbr (quotFamily Ω N) (K.map (QuotientGroup.mk' N))) :
    ∃ n ∈ N, J ∈ omegaStarNbr Ω (conjSub n K) := by
  obtain ⟨-, hne, Ub, hUb, hUbJ, hUbN⟩ := h
  obtain ⟨U, hU, hUJ, hUmap⟩ := exists_lift_USet3 hΩ' hN hJ hUb hUbJ
  have hU2 : IsPGroup 2 U := Sec6Gen.isPGroup_of_mem_USet hΩ hU
  obtain ⟨n, hn, hUn⟩ := exists_conj_normalizer3 hΩ hN hK hU2 (fun u hu =>
    hUbN (hUmap ▸ Subgroup.mem_map_of_mem _ hu))
  refine ⟨n, hn, hJ, ?_, U, hU, hUJ, hUn⟩
  intro hJK
  apply hne
  rw [hJK, AscQuot.map_conjSub, show QuotientGroup.mk' N n = 1 from
    (QuotientGroup.eq_one_iff _).mpr hn, conjSub_one]

theorem aEmpty_quotFamily3 (hΩ : HypOmegaGen Ω) (hΩ' : HypOmegaGen (quotFamily Ω N))
    (hN : Odd (Nat.card N)) (hA : ∀ J ∈ Ω, AEmpty Ω J) :
    ∀ M ∈ quotFamily Ω N, AEmpty (quotFamily Ω N) M := by
  rintro _ ⟨K, hK, rfl⟩
  intro Jb hJbstar hJbnbr zKb zJb hzKb hzJb
  obtain ⟨J, hJ, rfl⟩ := hJbstar.1
  obtain ⟨n, hn, hstar⟩ := exists_conj_omegaStarNbr3 hΩ hΩ' hN hK hJ hJbstar
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

section Layer


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {c : G}

theorem aEmpty_exactPair3_of_stand3 (hs : AscStand3 Ω K) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    (hne : (tqMembers3 Ω c).Nonempty) :
    ∀ L ∈ exactPair3 Ω c, AEmpty (exactPair3 Ω c) L :=
  aEmpty_exactPair3 (hypOmegaGenU_of_modU (MemberType.cert_sl2 3 1) hs.hyp)
    (hypOmegaGenU_of_modU (MemberType.cert_sl2 3 1) (hypOmegaModU_exactPair3 hs hc2 hne))
    hs.aEmpty hc2

theorem aEmpty_layerFam3 (hs : AscStand3 Ω K) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    (hne : (tqMembers3 Ω c).Nonempty) :
    ∀ L ∈ layerFam3 Ω c, AEmpty (layerFam3 Ω c) L :=
  aEmpty_quotFamily3 (hypOmegaGenU_of_modU (MemberType.cert_sl2 3 1)
      (hypOmegaModU_exactPair3 hs hc2 hne))
    (hypOmegaGenU_of_modU (MemberType.cert_sl2 3 1) (hypOmegaModU_layerFam3 hs hc2 hne))
    (CFSG.ComponentClassification.OddCore.odd_card ↥(exactLayer3 Ω c))
    (aEmpty_exactPair3_of_stand3 hs hc2 hne)

end Layer

end CFSG.ClassicalInvolution.Q3.Q3T7
