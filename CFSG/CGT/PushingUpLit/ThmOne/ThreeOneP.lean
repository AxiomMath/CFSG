module

public import CFSG.CGT.PushingUpLit.ThmOne.ThreeOneQuot
public import CFSG.CGT.PushingUpLit.ThmOne.ThreeOneFStar

public section

namespace CFSG.CGT.PushingUpLit.ThmOne

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem le_centralizerModCore_of_le_normalizer {X M P : Subgroup G} (hO2 : oResidualTwo X = ⊤)
    (hXM : X ≤ M) (hsub : (X.subgroupOf M).IsSubnormal) (hP : IsPGroup 2 P) (hPM : P ≤ M)
    (hXP : X ≤ Subgroup.normalizer (P : Set G)) : P ≤ centralizerModCore X := by
  have hPX := le_normalizer_of_isSubnormal_of_isPGroup hO2 hXM hsub hP hPM hXP
  have hXPO : X ⊓ P ≤ oTwoIn X :=
    SixThree.le_oTwoIn_of_isPGroup inf_le_left (hP.to_le inf_le_right)
      ((le_inf Subgroup.le_normalizer hXP).trans Subgroup.inf_normalizer_le_normalizer_inf)
  refine fun p hp => ⟨hPX hp, fun x hx => hXPO (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)⟩
  · exact X.mul_mem ((Subgroup.mem_normalizer_iff.mp (hPX hp) x).mp hx) (X.inv_mem hx)
  · have h1 : x * p⁻¹ * x⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp (hXP hx) _).mp (P.inv_mem hp)
    rw [show p * x * p⁻¹ * x⁻¹ = p * (x * p⁻¹ * x⁻¹) by group]
    exact P.mul_mem hp h1

theorem le_oTwoIn_of_le_normalizer {X M P : Subgroup G} (hX : InClassX X) (hXM : X ≤ M)
    (hsub : (X.subgroupOf M).IsSubnormal) (hP : IsPGroup 2 P) (hPM : P ≤ M)
    (hXP : X ≤ Subgroup.normalizer (P : Set G))
    (hCP : M ⊓ Subgroup.centralizer (blockU X : Set G) ≤ Subgroup.normalizer (P : Set G)) :
    P ≤ oTwoIn M := by
  have hO2 := hX.1.residual_eq
  have hPC := le_centralizerModCore_of_le_normalizer hO2 hXM hsub hP hPM hXP
  have hPU : P ≤ Subgroup.centralizer (blockU X : Set G) :=
    le_centralizer_blockU_of_le_centralizerModCore hX.1 hP hPC
  set Xb := (X.subgroupOf M).map (QuotientGroup.mk' (pCore 2 M)) with hXb
  set Pb := (P.subgroupOf M).map (QuotientGroup.mk' (pCore 2 M)) with hPb
  have h2 : pCore 2 (M ⧸ pCore 2 M) = ⊥ := pCore_quotient_by_pCore_eq_bot _ 2
  have hPb2 : IsPGroup 2 Pb := (hP.comap_subtype).map _
  have hXbs : Xb.IsSubnormal := hsub.map (QuotientGroup.mk'_surjective _)
  have hXPb : Xb ≤ Subgroup.centralizer (Pb : Set _) := map_mk_le_centralizer hXM hsub hPC
  have hN : ∀ c : M, (c : G) ∈ M ⊓ Subgroup.centralizer (blockU X : Set G) →
      QuotientGroup.mk' (pCore 2 M) c ∈ Subgroup.normalizer (Pb : Set _) :=
    fun c hc => mk_oTwo_mem_normalizer_map (hCP hc)
  have hC : ∀ c : M, QuotientGroup.mk' (pCore 2 M) c ∈ Subgroup.centralizer (Xb : Set _) →
      (c : G) ∈ centralizerModCore X :=
    fun c hc => mem_centralizerModCore_of_mk_mem_centralizer hO2 hXM hsub hc
  have hE : ∀ J : Subgroup (M ⧸ pCore 2 M), IsComponent J → ⁅J, Pb⁆ = ⊥ := by
    intro J hJ
    rcases LocalCores.component_subnormal_subgroup hJ hXbs with hle | hcomm
    · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (hle.trans hXPb)
    · have hJC := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
      refine commutator_eq_bot_of_isComponent_of_le_normalizer hJ hPb2 ?_
      rw [← Subgroup.isPerfect_iff.mp hJ.1.1, Subgroup.commutator_le]
      intro a ha b hb
      obtain ⟨a', rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 M) a
      obtain ⟨b', rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 M) b
      rw [← map_commutatorElement]
      exact hN _ ⟨(⁅a', b'⁆ : M).2,
        commutatorElement_mem_centralizer_blockU hX.1 (hC a' (hJC ha)) (hC b' (hJC hb))⟩
  have hkey : ∀ f ∈ fittingSubgroup (M ⧸ pCore 2 M), f ∈ Subgroup.centralizer (Xb : Set _) →
      f ∈ Subgroup.centralizer (Pb : Set _) := by
    intro f hf hfX
    obtain ⟨f', rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 M) f
    have hf'C := hC f' hfX
    refine mem_centralizer_of_commutator_mem_normalizer h2 hPb2 hf fun p hp => ?_
    obtain ⟨p', hp', rfl⟩ := Subgroup.mem_map.mp hp
    rw [← map_commutatorElement]
    exact hN _ ⟨(⁅f', p'⁆ : M).2,
      commutatorElement_mem_centralizer_of_normalizer hf'C.1 (hPU hp')⟩
  have hF : ⁅fittingSubgroup (M ⧸ pCore 2 M), Pb⁆ = ⊥ := by
    rcases hX.1.quotient_type with hq | hp
    ·
      have hXbE : Xb ≤ layer _ := le_sSup (isComponent_map_mk_oTwo hq hXM hsub)
      have hFX : fittingSubgroup (M ⧸ pCore 2 M) ≤ Subgroup.centralizer (Xb : Set _) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp (le_bot_iff.mp
          ((Subgroup.commutator_mono le_rfl hXbE).trans LocalCores.fitting_layer_commute.le))
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr fun f hf => hkey f hf (hFX hf)
    ·
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have hXb3 : IsPGroup 3 Xb :=
        isPGroup_map_mk_oTwo (card_top_eq_three_of_inClassX hX hp) hXM hsub
      have hXbF : Xb ≤ fittingSubgroup (M ⧸ pCore 2 M) :=
        (le_pCore_of_isSubnormal_of_isPGroup hXbs hXb3).trans (pCore_le_fitting _ 3)
      exact commutator_fittingSubgroup_eq_bot_of_le_centralizer h2 hPb2 hXbF hXPb hkey
  exact le_oTwoIn_of_map_mk_eq_bot hPM (eq_bot_of_commutator_eq_bot h2 hPb2 hE hF)

theorem oTwoIn_inf_eq {X M H : Subgroup G} (hX : InClassX X) (hXM : X ≤ M)
    (hsub : (X.subgroupOf M).IsSubnormal) (hXH : X ≤ H)
    (hCH : M ⊓ Subgroup.centralizer (blockU X : Set G) ≤ H) : oTwoIn (H ⊓ M) = oTwoIn M := by
  have hNP := SixThree.le_normalizer_oTwoIn (H ⊓ M)
  refine le_antisymm (le_oTwoIn_of_le_normalizer hX hXM hsub (isPGroup_oTwoIn _)
    ((oTwoIn_le _).trans inf_le_right) ((le_inf hXH hXM).trans hNP)
    ((le_inf hCH inf_le_left).trans hNP)) ?_
  have hQU : oTwoIn M ≤ Subgroup.centralizer (blockU X : Set G) :=
    le_centralizer_blockU_of_le_centralizerModCore hX.1 (isPGroup_oTwoIn M)
      (oTwoIn_le_centralizerModCore_of_isSubnormal hX.1.residual_eq hXM hsub)
  exact SixThree.le_oTwoIn_of_isPGroup (le_inf ((le_inf (oTwoIn_le M) hQU).trans hCH) (oTwoIn_le M))
    (isPGroup_oTwoIn M) (inf_le_right.trans (SixThree.le_normalizer_oTwoIn M))

end CFSG.CGT.PushingUpLit.ThmOne
