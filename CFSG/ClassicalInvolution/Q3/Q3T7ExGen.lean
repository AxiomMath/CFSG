module

public import CFSG.ClassicalInvolution.Q3.Q3DStand
public import CFSG.ClassicalInvolution.Q3.Q3NLExact

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Q3.Disc3 CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement

section ExGen


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem secData3_exactFamily_of_modU (hΩ : HypOmegaModU (.sl2 3 1) Ω)
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) (hne : (tqMembers3 Ω c).Nonempty) :
    SecData3 c (exactFamily3 Ω c) := by
  refine ⟨?_, fun K' hK' => le_centralizer_of_mem_exactFamily3 hK',
    fun n hn K' hK' => conjSub_mem_exactFamily3 hΩ.conjInvariant hn hK', ?_⟩
  · obtain ⟨K, hK⟩ := hne
    exact ⟨exactCore3 c K, exactCore3_mem_exactFamily3 hK⟩
  · rintro K' ⟨K, hK, rfl⟩
    obtain ⟨z, hz⟩ := hΩ.classical K hK.1
    exact ⟨z, isSectionMember3_exactCore3 (hz.toQ3 (by norm_num)) hc2 hK.2⟩

theorem inClass3_exactPair3_of_modU (hΩ : HypOmegaModU (.sl2 3 1) Ω)
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) (hne : (tqMembers3 Ω c).Nonempty) :
    InClass3 (exactPair3 Ω c) :=
  (secData3_exactFamily_of_modU hΩ hc2 hne).inClass3

theorem omega4_exactCore3_of_modU (hΩ : HypOmegaModU (.sl2 3 1) Ω)
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) {K₀ J₀ : Subgroup G} (hK₀ : K₀ ∈ tqMembers3 Ω c)
    (hJ₀ : J₀ ∈ tqMembers3 Ω c) (hKJ : K₀ ≠ J₀) :
    padicValNat 2 (Nat.card ↥(exactCore3 c K₀ ⊓ exactCore3 c J₀)) ≤ 1 ∧
      (padicValNat 2 (Nat.card ↥(exactCore3 c K₀ ⊓ exactCore3 c J₀)) = 1 →
        ⁅exactCore3 c K₀, exactCore3 c J₀⁆ ≤
          oddCoreOf (exactCore3 c K₀) ⊓ oddCoreOf (exactCore3 c J₀)) := by
  obtain ⟨h1, h2⟩ := hΩ.omega4 K₀ hK₀.1 J₀ hJ₀.1 hKJ
  obtain ⟨zK, hzK⟩ := hΩ.classical K₀ hK₀.1
  obtain ⟨zJ, hzJ⟩ := hΩ.classical J₀ hJ₀.1
  have hK3 : IsClassicalMember3 K₀ zK := hzK.toQ3 (by norm_num)
  have hJ3 : IsClassicalMember3 J₀ zJ := hzJ.toQ3 (by norm_num)
  have hdvd : Nat.card ↥(exactCore3 c K₀ ⊓ exactCore3 c J₀) ∣ Nat.card ↥(K₀ ⊓ J₀) :=
    Subgroup.card_dvd_of_le (inf_le_inf (exactCore3_le_left c K₀) (exactCore3_le_left c J₀))
  have hle : padicValNat 2 (Nat.card ↥(exactCore3 c K₀ ⊓ exactCore3 c J₀)) ≤
      padicValNat 2 (Nat.card ↥(K₀ ⊓ J₀)) :=
    (padicValNat_dvd_iff_le Nat.card_pos.ne').mp (dvd_trans pow_padicValNat_dvd hdvd)
  refine ⟨hle.trans h1, fun h => ?_⟩
  have hv : padicValNat 2 (Nat.card ↥(K₀ ⊓ J₀)) = 1 := le_antisymm h1 (h ▸ hle)
  have hcomm := h2 hv
  have hoK : oddCoreOf (exactCore3 c K₀) = exactCore3 c K₀ ⊓ oddCoreOf K₀ :=
    oddCoreIn_exactCore3 hK3 hc2 hK₀.2
  have hoJ : oddCoreOf (exactCore3 c J₀) = exactCore3 c J₀ ⊓ oddCoreOf J₀ :=
    oddCoreIn_exactCore3 hJ3 hc2 hJ₀.2
  rw [hoK, hoJ]
  refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
  have hab : ⁅a, b⁆ ∈ ⁅K₀, J₀⁆ :=
    Subgroup.commutator_mem_commutator (exactCore3_le_left c K₀ ha) (exactCore3_le_left c J₀ hb)
  have ho := hcomm hab
  have hac : a ∈ Subgroup.centralizer ({c} : Set G) := exactCore3_le_centralizer c K₀ ha
  have hbc : b ∈ Subgroup.centralizer ({c} : Set G) := exactCore3_le_centralizer c J₀ hb
  have hcc : ⁅a, b⁆ ∈ Subgroup.centralizer ({c} : Set G) := by
    have h1 : ⁅a, b⁆ = a * b * a⁻¹ * b⁻¹ := rfl
    rw [h1]
    exact (Subgroup.centralizer ({c} : Set G)).mul_mem
      ((Subgroup.centralizer ({c} : Set G)).mul_mem
        ((Subgroup.centralizer ({c} : Set G)).mul_mem hac hbc)
        ((Subgroup.centralizer ({c} : Set G)).inv_mem hac))
      ((Subgroup.centralizer ({c} : Set G)).inv_mem hbc)
  exact ⟨⟨⟨(Subgroup.map_subtype_le _) ho.1, hcc⟩, ho.1⟩,
    ⟨⟨(Subgroup.map_subtype_le _) ho.2, hcc⟩, ho.2⟩⟩

theorem hypOmegaModU_exactPair3_of_modU (hΩ : HypOmegaModU (.sl2 3 1) Ω)
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) (hne : (tqMembers3 Ω c).Nonempty) :
    HypOmegaModU (.sl2 3 1) (exactPair3 Ω c) := by
  have hcl := inClass3_exactPair3_of_modU hΩ hc2 hne
  refine ⟨hcl.conjInvariant, fun L hL => ?_, ?_, ?_⟩
  · obtain ⟨z, hz⟩ := hcl.classical L hL
    exact ⟨z, IsClassicalMemberU.ofQ3 hz⟩
  · rintro _ ⟨Kc, hKc, hKcY, rfl⟩ _ ⟨Jc, hJc, hJcY, rfl⟩ hne'
    obtain ⟨⟨K₀, hK₀, rfl⟩, -⟩ := hKc
    obtain ⟨⟨J₀, hJ₀, rfl⟩, -⟩ := hJc
    have hKJ : K₀ ≠ J₀ := fun e => hne' (by rw [e])
    obtain ⟨h1, h2⟩ := omega4_exactCore3_of_modU hΩ hc2 hK₀ hJ₀ hKJ
    have hcard : Nat.card ↥((exactCore3 c K₀).subgroupOf (exactLayer3 Ω c) ⊓
        (exactCore3 c J₀).subgroupOf (exactLayer3 Ω c)) =
        Nat.card ↥(exactCore3 c K₀ ⊓ exactCore3 c J₀) := by
      rw [inf_subgroupOf_eq]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hKcY)).toEquiv
    rw [hcard]
    refine ⟨h1, fun h => ?_⟩
    have hle := h2 h
    rw [oddCoreOf_subgroupOf hKcY, oddCoreOf_subgroupOf hJcY]
    refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
    have hab : (⁅(a : G), (b : G)⁆) ∈ ⁅exactCore3 c K₀, exactCore3 c J₀⁆ :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.mp ha)
        (Subgroup.mem_subgroupOf.mp hb)
    exact ⟨Subgroup.mem_subgroupOf.mpr (hle hab).1, Subgroup.mem_subgroupOf.mpr (hle hab).2⟩
  · rintro _ ⟨Kc, hKc, hKcY, rfl⟩ _ ⟨Jc, hJc, hJcY, rfl⟩ hne' z hz v hv hnc hv2 hvz
    obtain ⟨⟨K₀, hK₀, rfl⟩, -⟩ := hKc
    obtain ⟨⟨J₀, hJ₀, rfl⟩, -⟩ := hJc
    have hKJ : K₀ ≠ J₀ := fun e => hne' (by rw [e])
    obtain ⟨z₀, hz₀⟩ := hΩ.classical K₀ hK₀.1
    have hz₀3 : IsClassicalMember3 K₀ z₀ := hz₀.toQ3 (by norm_num)
    have hz₀U : IsUniqueInvolution K₀ z₀ := hz₀.isUniqueInvolution (MemberType.cert_sl2 3 1)
    have hz₀A : z₀ ∈ exactCore3 c K₀ := mem_exactCore3 hz₀3 hc2 hK₀.2
    have hzA : IsUniqueInvolution (exactCore3 c K₀) (z : G) :=
      isUniqueInvolution_of_subgroupOf hz hKcY
    have hzz : z₀ = (z : G) :=
      (hzA.unique z₀ hz₀A hz₀U.sq).resolve_left hz₀U.ne_one
    have hzK : IsUniqueInvolution K₀ (z : G) := hzz ▸ hz₀U
    have hvJ : (v : G) ∈ J₀ := exactCore3_le_left c J₀ (Subgroup.mem_subgroupOf.mp hv)
    have hnc' : ¬ ∀ w ∈ J₀, (v : G) * w = w * (v : G) := fun h => hnc (by
      rintro ⟨w, hw⟩ hw'
      exact Subtype.ext (h w (exactCore3_le_left c J₀ (Subgroup.mem_subgroupOf.mp hw'))))
    have hv2' : IsPGroup 2 (Subgroup.zpowers (v : G)) := isPGroup_zpowers_coe_iff.mpr hv2
    have hn := hΩ.omega5 K₀ hK₀.1 J₀ hJ₀.1 hKJ (z : G) hzK (v : G) hvJ hnc' hv2'
      (congrArg Subtype.val hvz)
    have hvc : (v : G) ∈ Subgroup.centralizer ({c} : Set G) := exactLayer3_le_centralizer Ω c v.2
    exact (mem_normalizer_subgroupOf_iff hKcY).mp
      (mem_normalizer_inf hn (Subgroup.le_normalizer hvc))

end ExGen

end CFSG.ClassicalInvolution.Q3.Q3T7
