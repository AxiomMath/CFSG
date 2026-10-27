module

public import CFSG.ClassicalInvolution.Q3.Q3T7LayerAE
public import CFSG.ClassicalInvolution.Asc77.AscE184Graph
public import CFSG.ClassicalInvolution.Uniform.UHypOmegaGen

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

section Transfer


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem exists_of_mem_RSet_exactFamily3 {R₀ : Subgroup G} (hR₀ : R₀ ∈ RSet (exactFamily3 Ω c)) :
    ∃ J ∈ tqMembers3 Ω c, IsSylow2In R₀ (exactCore3 c J) := by
  obtain ⟨M, hM, hRM⟩ := exists_isSylow2In_of_mem_RSet hR₀
  obtain ⟨J, hJ, rfl⟩ := hM
  exact ⟨J, hJ, hRM⟩

theorem mem_RSet_of_mem_RSet_exactFamily3 (hc2 : IsPGroup 2 (Subgroup.zpowers c)) {R₀ : Subgroup G}
    (hR₀ : R₀ ∈ RSet (exactFamily3 Ω c)) : R₀ ∈ RSet Ω := by
  obtain ⟨J, hJ, hT⟩ := exists_of_mem_RSet_exactFamily3 hR₀
  exact mem_RSet_of_isSylow2In hJ.1 ((isSylow2In_exactCore3_iff hc2 hJ.2).mp hT).1

theorem mem_USet_of_mem_USet_exactFamily3 (hc2 : IsPGroup 2 (Subgroup.zpowers c)) {U : Subgroup G}
    (hU : U ∈ USet (exactFamily3 Ω c)) : U ∈ USet Ω := by
  have := mem_USet_of_exact3 hc2 (Ω := Ω)
    (U := U) (by rwa [centralizingMembers_exactFamily3])
  exact this

theorem isSylow2In_exactCore3_of_le_centralizer {J R₀ : Subgroup G}
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) (hJ : c ∈ trivialOnQuot J) (hR : IsSylow2In R₀ J)
    (hRc : R₀ ≤ Subgroup.centralizer ({c} : Set G)) : IsSylow2In R₀ (exactCore3 c J) :=
  (isSylow2In_exactCore3_iff hc2 hJ).mpr ⟨hR, hRc⟩

theorem eq_of_exactCore3_eq (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    {J L : Subgroup G} (hJ : J ∈ tqMembers3 Ω c) (hL : L ∈ tqMembers3 Ω c)
    (h : exactCore3 c J = exactCore3 c L) : J = L := by
  have hcomm : ⁅Subgroup.zpowers c, J⁆ ≤ oddCoreOf J :=
    Subgroup.commutator_le.mpr fun a ha x hx =>
      (mem_trivialOnQuot_iff.mp (Subgroup.zpowers_le.mpr hJ.2 ha)).2 x hx
  obtain ⟨P, hP, hPc⟩ := AscE184Sect.exists_isSylow2In_centralizer hc2 hcomm
  have hPc' : P ≤ Subgroup.centralizer ({c} : Set G) := by
    rwa [centralizer_zpowers_eq_singleton'] at hPc
  have hPJc : P ≤ exactCore3 c J := le_inf hP.1 hPc'
  have hPL : P ≤ L := (hPJc.trans (h ▸ le_rfl)).trans (exactCore3_le_left c L)
  have h8 : 8 ≤ Nat.card P := by
    have := Sec6Gen.eight_le_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hJ.1 hP)
    omega
  exact Sec6Gen.eq_of_le_of_le hΩ hJ.1 hL.1 hP.2.1 (by omega) hP.1 hPL

theorem isUniqueInvolution_of_exactCore3 (hΩ : HypOmegaGen Ω) {J : Subgroup G}
    (hJ : J ∈ tqMembers3 Ω c) {z : G} (hz : IsUniqueInvolution (exactCore3 c J) z) :
    IsUniqueInvolution J z :=
  isUniqueInvolution_of_le_member3 hΩ hJ.1 (exactCore3_le_left c J) hz

theorem modU_toGen3 (hΩ : HypOmegaModU (.sl2 3 1) Ω) : HypOmegaGen Ω :=
  hypOmegaGenU_of_modU (MemberType.cert_sl2 3 1) hΩ

theorem isUniqueInvolution_exactCore3 (hΩ : HypOmegaModU (.sl2 3 1) Ω)
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) {J : Subgroup G} (hJ : J ∈ tqMembers3 Ω c) {z : G}
    (hz : IsUniqueInvolution J z) : IsUniqueInvolution (exactCore3 c J) z := by
  obtain ⟨z₀, hz₀⟩ := hΩ.classical J hJ.1
  have hz₀3 : IsClassicalMember3 J z₀ := hz₀.toQ3 (by norm_num)
  have hz₀U : IsUniqueInvolution J z₀ := hz₀.isUniqueInvolution (MemberType.cert_sl2 3 1)
  have hzz : z₀ = z := (hz.unique z₀ hz₀U.mem hz₀U.sq).resolve_left hz₀U.ne_one
  have hzc : z ∈ exactCore3 c J := hzz ▸ mem_exactCore3 hz₀3 hc2 hJ.2
  exact { mem := hzc
          ne_one := hz.ne_one
          sq := hz.sq
          unique := fun y hy hy2 => hz.unique y (exactCore3_le_left c J hy) hy2 }

theorem mem_twinSet_of_exactCore3 (hΩ : HypOmegaGen Ω) {K L : Subgroup G}
    (hK : K ∈ tqMembers3 Ω c) (hL : L ∈ tqMembers3 Ω c)
    (h : exactCore3 c L ∈ twinSet (exactFamily3 Ω c) (exactCore3 c K)) : L ∈ twinSet Ω K := by
  obtain ⟨-, z, hzK, hzL⟩ := h
  exact ⟨hL.1, z, isUniqueInvolution_of_exactCore3 hΩ hK hzK,
    isUniqueInvolution_of_exactCore3 hΩ hL hzL⟩

theorem exactCore3_mem_twinSet (hΩ : HypOmegaModU (.sl2 3 1) Ω)
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) {K L : Subgroup G} (hK : K ∈ tqMembers3 Ω c)
    (hL : L ∈ tqMembers3 Ω c) (h : L ∈ twinSet Ω K) :
    exactCore3 c L ∈ twinSet (exactFamily3 Ω c) (exactCore3 c K) := by
  obtain ⟨-, z, hzK, hzL⟩ := h
  exact ⟨exactCore3_mem_exactFamily3 hL, z, isUniqueInvolution_exactCore3 hΩ hc2 hK hzK,
    isUniqueInvolution_exactCore3 hΩ hc2 hL hzL⟩

theorem le_normalizer_of_le_centralizer_exact (hΩ : HypOmegaGen Ω) {K J T : Subgroup G}
    (hK : K ∈ Ω) (hJ : J ∈ Ω) (hJK : J ≠ K) {z : G} (hz : IsUniqueInvolution K z)
    (hTJ : T ≤ J) (hT2 : IsPGroup 2 T) (hT3 : 3 ≤ Nat.card T)
    (hTc : T ≤ Subgroup.centralizer ({z} : Set G)) : T ≤ Subgroup.normalizer (K : Set G) :=
  Sec6Gen.le_normalizer_of_le_centralizer hΩ hK hJ (Ne.symm hJK) hz hTJ hT2 hT3 hTc

theorem mem_omegaNbr_of_exactFamily3 (hΩ' : HypOmegaModU (.sl2 3 1) Ω)
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) {K J : Subgroup G} (hK : K ∈ tqMembers3 Ω c)
    (hJ : J ∈ tqMembers3 Ω c)
    (h : exactCore3 c J ∈ omegaNbr (exactFamily3 Ω c) (exactCore3 c K)) : J ∈ omegaNbr Ω K := by
  have hΩ := modU_toGen3 hΩ'
  obtain ⟨-, hne, T, hT, hTJ, hTN⟩ := h
  have hJK : J ≠ K := fun h' => hne (by rw [h'])
  obtain ⟨J', hJ', hTfix⟩ := exists_of_mem_RSet_exactFamily3 hT
  have hTfix' := (isSylow2In_exactCore3_iff hc2 hJ'.2).mp hTfix
  have h8 : 8 ≤ Nat.card T :=
    Sec6Gen.eight_le_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hJ'.1 hTfix'.1)
  have hTJG : T ≤ J := hTJ.trans (exactCore3_le_left c J)
  have hJJ' : J = J' := Sec6Gen.eq_of_le_of_le hΩ hJ.1 hJ'.1 hTfix'.1.2.1 (by omega) hTJG hTfix'.1.1
  subst hJJ'
  obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution hΩ hK.1
  have hzA := isUniqueInvolution_exactCore3 hΩ' hc2 hK hz
  have hTc : T ≤ Subgroup.centralizer ({z} : Set G) := by
    intro u hu
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : u * z * u⁻¹ = z := hzA.conj_eq (mem_normalizer_iff_conjSub_eq.mp (hTN hu))
    calc u * z = (u * z * u⁻¹) * u := by group
      _ = z * u := by rw [h1]
  have hTN' : T ≤ Subgroup.normalizer (K : Set G) :=
    le_normalizer_of_le_centralizer_exact hΩ hK.1 hJ.1 hJK hz hTJG hTfix'.1.2.1 (by omega) hTc
  exact ⟨hJ.1, hJK, T, mem_RSet_of_isSylow2In hJ.1 hTfix'.1, hTJG, hTN'⟩

theorem mem_omegaStarNbr_of_exactFamily3 (hΩ' : HypOmegaModU (.sl2 3 1) Ω)
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) {K J : Subgroup G} (hK : K ∈ tqMembers3 Ω c)
    (hJ : J ∈ tqMembers3 Ω c)
    (h : exactCore3 c J ∈ omegaStarNbr (exactFamily3 Ω c) (exactCore3 c K)) :
    J ∈ omegaStarNbr Ω K := by
  have hΩ := modU_toGen3 hΩ'
  obtain ⟨-, hne, U, hU, hUJ, hUN⟩ := h
  have hJK : J ≠ K := fun h' => hne (by rw [h'])
  have hUΩ : U ∈ USet Ω := mem_USet_of_mem_USet_exactFamily3 hc2 hU
  obtain ⟨R₀, hR₀, J', hJ', hR₀J', hUR₀, hcyc, hcard, h4⟩ :=
    Sec6Gen.exists_data_of_mem_USet hΩ hUΩ
  have hU2 : IsPGroup 2 U := Sec6Gen.isPGroup_of_mem_USet hΩ hUΩ
  have hUJG : U ≤ J := hUJ.trans (exactCore3_le_left c J)
  obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution hΩ hK.1
  have hzA := isUniqueInvolution_exactCore3 hΩ' hc2 hK hz
  have hUc : U ≤ Subgroup.centralizer ({z} : Set G) := by
    intro u hu
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : u * z * u⁻¹ = z := hzA.conj_eq (mem_normalizer_iff_conjSub_eq.mp (hUN hu))
    calc u * z = (u * z * u⁻¹) * u := by group
      _ = z * u := by rw [h1]
  have hUN' : U ≤ Subgroup.normalizer (K : Set G) :=
    le_normalizer_of_le_centralizer_exact hΩ hK.1 hJ.1 hJK hz hUJG hU2 (by omega) hUc
  exact ⟨hJ.1, hJK, U, hUΩ, hUJG, hUN'⟩

theorem dstarAdj_of_exactFamily3 (hΩ : HypOmegaModU (.sl2 3 1) Ω)
    (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    {K J : Subgroup G} (hK : K ∈ tqMembers3 Ω c) (hJ : J ∈ tqMembers3 Ω c)
    (h : dstarAdj (exactFamily3 Ω c) (exactCore3 c K) (exactCore3 c J)) : dstarAdj Ω K J := by
  rcases h.2 with h1 | h1
  · exact ⟨hJ.1, Or.inl (mem_omegaStarNbr_of_exactFamily3 hΩ hc2 hK hJ h1)⟩
  · exact ⟨hJ.1, Or.inr (mem_omegaStarNbr_of_exactFamily3 hΩ hc2 hJ hK h1)⟩

theorem mem_dstarComp_of_dstarComp_exactFamily3 (hΩ : HypOmegaModU (.sl2 3 1) Ω)
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) {K : Subgroup G} (hK : K ∈ tqMembers3 Ω c)
    {L : Subgroup G} (hL : L ∈ dstarComp (exactFamily3 Ω c) (exactCore3 c K)) :
    ∀ M ∈ tqMembers3 Ω c, exactCore3 c M = L → M ∈ dstarComp Ω K := by
  induction hL with
  | refl =>
    intro M hM hMK
    rw [eq_of_exactCore3_eq (modU_toGen3 hΩ) hc2 hM hK hMK]
    exact Relation.ReflTransGen.refl
  | tail hab hbc ih =>
    rename_i b d
    intro M hM hMd
    have hbΛ : b ∈ exactFamily3 Ω c := by
      rcases dstarComp_subset_insert _ hab with h | h
      · rw [h]
        exact exactCore3_mem_exactFamily3 hK
      · exact h
    obtain ⟨M₀, hM₀, rfl⟩ := hbΛ
    have h1 := ih M₀ hM₀ rfl
    rw [← hMd] at hbc
    exact h1.tail (dstarAdj_of_exactFamily3 hΩ hc2 hM₀ hM hbc)

theorem le_normalizer_exactLayer3 (hΩ : ConjInvariant Ω) :
    Subgroup.centralizer ({c} : Set G) ≤ Subgroup.normalizer (exactLayer3 Ω c : Set G) := by
  have hle : ∀ {x : G}, x ∈ Subgroup.centralizer ({c} : Set G) →
      conjSub x (exactLayer3 Ω c) ≤ exactLayer3 Ω c := by
    intro x hx
    unfold exactLayer3 centralizingLayer conjSub
    rw [Subgroup.map_iSup]
    refine iSup_le fun L => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hL => ?_
    have hL' : L ∈ exactFamily3 Ω c := hL.1
    exact le_centralizingLayer (L := conjSub x L)
      ⟨conjSub_mem_exactFamily3 hΩ hx hL', le_centralizer_of_mem_exactFamily3
        (conjSub_mem_exactFamily3 hΩ hx hL')⟩
  intro x hx
  refine mem_normalizer_iff_conjSub_eq.mpr (le_antisymm (hle hx) ?_)
  have := conjSub_mono (n := x) (hle ((Subgroup.centralizer ({c} : Set G)).inv_mem hx))
  rwa [conjSub_conjSub_inv] at this

end Transfer

end CFSG.ClassicalInvolution.Q3.Q3T7
