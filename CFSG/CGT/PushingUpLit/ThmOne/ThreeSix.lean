module

public import CFSG.CGT.PushingUpLit.ThmOne.ThreeTwoThree
public import CFSG.CGT.PushingUpLit.SixThree
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.CGT.PushingUpLit.SixThreeC
public import CFSG.CGT.PushingUpLit.SixThreeSylow
public import CFSG.CGT.PushingUpLit.SixThreeV

public section

namespace CFSG.CGT.PushingUpLit.ThmOne

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem ThreeSix.normalizer_le_normalizer_omegaOneCenterIn_gen (P : Subgroup G) :
    Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (omegaOneCenterIn P : Set G) := by
  have key : ∀ g ∈ Subgroup.normalizer (P : Set G), ∀ z ∈ omegaOneCenterIn P,
      g * z * g⁻¹ ∈ omegaOneCenterIn P := by
    intro g hg z hz
    obtain ⟨hzP, hzc, hz2⟩ := mem_omegaOneCenterIn_iff.mp hz
    refine mem_omegaOneCenterIn_iff.mpr
      ⟨(Subgroup.mem_normalizer_iff.mp hg z).mp hzP, fun k hk => ?_, ?_⟩
    · have hk' : g⁻¹ * k * g ∈ P := by
        simpa using (Subgroup.mem_normalizer_iff.mp (inv_mem hg) k).mp hk
      have h1 := hzc _ hk'
      calc k * (g * z * g⁻¹) = g * ((g⁻¹ * k * g) * z) * g⁻¹ := by group
        _ = g * (z * (g⁻¹ * k * g)) * g⁻¹ := by rw [h1]
        _ = g * z * g⁻¹ * k := by group
    · rw [conj_pow, hz2, mul_one, mul_inv_cancel]
  intro g hg
  refine Subgroup.mem_normalizer_iff.mpr fun z => ⟨key g hg z, fun hz => ?_⟩
  simpa [mul_assoc] using key g⁻¹ (inv_mem hg) _ hz

omit [Finite G] in
theorem ThreeSix.le_normalizer_omegaOneCenterIn (H : Subgroup G) :
    H ≤ Subgroup.normalizer (omegaOneCenterIn (oTwoIn H) : Set G) :=
  (SixThree.le_normalizer_oTwoIn H).trans (ThreeSix.normalizer_le_normalizer_omegaOneCenterIn_gen _)

omit [Finite G] in
theorem ThreeSix.le_normalizer_self_inf_centralizer {H V : Subgroup G}
    (hHV : H ≤ Subgroup.normalizer (V : Set G)) :
    H ≤ Subgroup.normalizer ((H ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) := by
  have key : ∀ h ∈ H, ∀ c ∈ H ⊓ Subgroup.centralizer (V : Set G),
      h * c * h⁻¹ ∈ H ⊓ Subgroup.centralizer (V : Set G) := by
    intro h hh c hc
    obtain ⟨hcH, hcC⟩ := Subgroup.mem_inf.mp hc
    refine Subgroup.mem_inf.mpr ⟨H.mul_mem (H.mul_mem hh hcH) (H.inv_mem hh),
      Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
    have hv' : h⁻¹ * v * h ∈ V := by
      simpa using (Subgroup.mem_normalizer_iff.mp (hHV (H.inv_mem hh)) v).mp hv
    have h1 := Subgroup.mem_centralizer_iff.mp hcC _ hv'
    calc v * (h * c * h⁻¹) = h * ((h⁻¹ * v * h) * c) * h⁻¹ := by group
      _ = h * (c * (h⁻¹ * v * h)) * h⁻¹ := by rw [h1]
      _ = h * c * h⁻¹ * v := by group
  intro h hh
  refine Subgroup.mem_normalizer_iff.mpr fun c => ⟨key h hh c, fun hc => ?_⟩
  simpa [mul_assoc] using key h⁻¹ (H.inv_mem hh) _ hc

theorem oTwoIn_le_of_isSylowOf_centralizerModCore_of_le {X R H : Subgroup G}
    (hX : oResidualTwo ↥X = ⊤) (hR : IsSylowOf 2 R (centralizerModCore X))
    (hXR : X ≤ Subgroup.normalizer (R : Set G))
    (hsub : (X.subgroupOf (Subgroup.normalizer (R : Set G))).IsSubnormal)
    (hXH : X ≤ H) (hRH : R ≤ H) : oTwoIn H ≤ R := by
  have hP : IsPGroup 2 (oTwoIn H ⊔ R : Subgroup G) :=
    IsPGroup.to_sup_of_normal_left' (isPGroup_oTwoIn H) hR.2.1
      (hRH.trans (SixThree.le_normalizer_oTwoIn H))
  have hXP : X ≤ Subgroup.normalizer ((oTwoIn H ⊔ R : Subgroup G) : Set G) :=
    (le_inf (hXH.trans (SixThree.le_normalizer_oTwoIn H)) hXR).trans
      (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  have h := SixThree.eq_of_le_isPGroup (SubTwo.noTwoQuotient_of_oResidualTwo hX) hR hXR hsub hP
    hXP le_sup_right
  exact le_sup_left.trans h.ge

theorem ThreeSix.commutator_eq_blockU_of_le {X R W : Subgroup G} (hX : oResidualTwo ↥X = ⊤)
    (hRC : R ≤ centralizerModCore X) (hUW : blockU X ≤ W) (hWR : W ≤ R) :
    ⁅W, X⁆ = blockU X := by
  refine le_antisymm (Subgroup.commutator_le.mpr fun w hw x hx => ?_) ?_
  · exact commutator_mem_blockU_of_mem_centralizerModCore hX (hRC (hWR hw)) hx
  · calc blockU X = ⁅blockU X, X⁆ := (blockU_commutator_eq_self hX).symm
      _ ≤ ⁅W, X⁆ := Subgroup.commutator_mono hUW le_rfl

theorem blockU_le_omegaOneCenterIn {X R H : Subgroup G} (hX : IsShortGroup ↥X)
    (hR : IsSylowOf 2 R (centralizerModCore X)) (hH : IsCharacteristicP 2 ↥H) (hXH : X ≤ H)
    (hOR : oTwoIn H ≤ R) : blockU X ≤ omegaOneCenterIn (oTwoIn H) := by
  have hRU : R ≤ Subgroup.centralizer (blockU X : Set G) :=
    le_centralizer_blockU_of_le_centralizerModCore hX hR.2.1 hR.1
  intro u hu
  have hc : ∀ k ∈ oTwoIn H, k * u = u * k := fun k hk =>
    (Subgroup.mem_centralizer_iff.mp (hRU (hOR hk)) u hu).symm
  refine mem_omegaOneCenterIn_iff.mpr ⟨?_, hc, pow_two_eq_one_of_mem_blockU hX hu⟩
  exact ThreeSix.mem_oTwoIn_of_mem_centralizer hH (hXH (blockU_le X hu))
    (Subgroup.mem_centralizer_iff.mpr hc)

theorem commutator_oTwoIn_eq_blockU {X R H : Subgroup G} (hX : IsShortGroup ↥X)
    (hR : IsSylowOf 2 R (centralizerModCore X)) (hH : IsCharacteristicP 2 ↥H) (hXH : X ≤ H)
    (hOR : oTwoIn H ≤ R) : ⁅oTwoIn H, X⁆ = blockU X :=
  ThreeSix.commutator_eq_blockU_of_le hX.residual_eq hR.1
    ((blockU_le_omegaOneCenterIn hX hR hH hXH hOR).trans (omegaOneCenterIn_le _)) hOR

theorem commutator_omegaOneCenterIn_eq_blockU {X R H : Subgroup G} (hX : IsShortGroup ↥X)
    (hR : IsSylowOf 2 R (centralizerModCore X)) (hH : IsCharacteristicP 2 ↥H) (hXH : X ≤ H)
    (hOR : oTwoIn H ≤ R) : ⁅omegaOneCenterIn (oTwoIn H), X⁆ = blockU X :=
  ThreeSix.commutator_eq_blockU_of_le hX.residual_eq hR.1
    (blockU_le_omegaOneCenterIn hX hR hH hXH hOR) ((omegaOneCenterIn_le _).trans hOR)

theorem ThreeSix.map_omegaOneCenterIn_pCore (H : Subgroup G) :
    (omegaOneCenterIn (pCore 2 ↥H)).map H.subtype = omegaOneCenterIn (oTwoIn H) := by
  have h := map_omegaOneCenterIn_subgroupOf (oTwoIn_le H)
  have e : (oTwoIn H).subgroupOf H = pCore 2 ↥H :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  rwa [e] at h

theorem ThreeSix.subgroupOf_le_centralizer_omegaOneCenterIn {H A : Subgroup G}
    (hA : A ≤ Subgroup.centralizer (omegaOneCenterIn (oTwoIn H) : Set G)) :
    A.subgroupOf H ≤
      Subgroup.centralizer ((omegaOneCenterIn (pCore 2 ↥H) : Subgroup ↥H) : Set ↥H) := by
  intro a ha
  refine Subgroup.mem_centralizer_iff.mpr fun v hv => Subtype.ext ?_
  have hv' : (v : G) ∈ omegaOneCenterIn (oTwoIn H) := by
    rw [← ThreeSix.map_omegaOneCenterIn_pCore H]
    exact ⟨v, hv, rfl⟩
  exact Subgroup.mem_centralizer_iff.mp (hA (Subgroup.mem_subgroupOf.mp ha)) _ hv'

theorem ThreeSix.subgroupOf_hyps_of_sylow {X R H : Subgroup G} (hX : IsShortGroup ↥X)
    (hR : IsSylowOf 2 R (centralizerModCore X)) (hXR : X ≤ Subgroup.normalizer (R : Set G))
    (hsub : (X.subgroupOf (Subgroup.normalizer (R : Set G))).IsSubnormal)
    (hNH : Subgroup.normalizer (R : Set G) ≤ H) (hH : IsCharacteristicP 2 ↥H) :
    IsSylowOf 2 (R.subgroupOf H) (centralizerModCore (X.subgroupOf H)) ∧
      X.subgroupOf H ≤ Subgroup.normalizer ((R.subgroupOf H : Subgroup ↥H) : Set ↥H) ∧
      ((X.subgroupOf H).subgroupOf
        (Subgroup.normalizer ((R.subgroupOf H : Subgroup ↥H) : Set ↥H))).IsSubnormal ∧
      ¬ X.subgroupOf H ≤
        Subgroup.centralizer ((omegaOneCenterIn (pCore 2 ↥H) : Subgroup ↥H) : Set ↥H) ∧
      Subgroup.centralizer ((omegaOneCenterIn (pCore 2 ↥H) : Subgroup ↥H) : Set ↥H) ≤
        centralizerModCore (X.subgroupOf H) := by
  have hRH : R ≤ H := Subgroup.le_normalizer.trans hNH
  have hXH : X ≤ H := hXR.trans hNH
  have hR' : IsSylowOf 2 (R.subgroupOf H) (centralizerModCore (X.subgroupOf H)) :=
    (EightOneRel.isSylowOf_subgroupOf_iff hXH hRH).mpr
      (SixThree.isSylowOf_of_le hR (le_inf hR.1 hRH) inf_le_left)
  obtain ⟨hYR, hsub'⟩ := (EightOneRel.sylowClause_subgroupOf_iff hXH hRH).mpr
    ⟨hXR, by rwa [inf_eq_left.mpr hNH]⟩
  have hsh : IsShortGroup ↥(X.subgroupOf H) :=
    isShortGroup_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hXH).symm hX
  have hNo : SubTwo.NoTwoQuotient (X.subgroupOf H) :=
    SubTwo.noTwoQuotient_of_oResidualTwo hsh.residual_eq
  have hQ2 : IsPGroup 2 (pCore 2 ↥H) := pCore_isPGroup
  have hmax : ∀ N : Subgroup ↥H, N.Normal → IsPGroup 2 N → N ≤ pCore 2 ↥H :=
    fun N hN hp => le_sSup ⟨hN, hp⟩
  have hQC : pCore 2 ↥H ≤ centralizerModCore (X.subgroupOf H) :=
    (SixThree.normal_le_of_isSylowOf hNo hR' hYR hsub' hQ2).trans hR'.1
  obtain ⟨hQU, -, hUV, hnot⟩ := SixThree.step_two hsh hQ2 hH hQC
  have hVn : (omegaOneCenterIn (pCore 2 ↥H)).Normal := SixThree.normal_omegaOneCenterIn _
  exact ⟨hR', hYR, hsub', hnot, SixThree.step_three hNo hQ2 hH hmax (fun g hg => (hQC hg).1)
    (hQU.le.trans hUV)⟩

theorem inf_centralizer_omegaOneCenterIn_le_centralizerModCore {X R H : Subgroup G}
    (hX : IsShortGroup ↥X) (hR : IsSylowOf 2 R (centralizerModCore X))
    (hXR : X ≤ Subgroup.normalizer (R : Set G))
    (hsub : (X.subgroupOf (Subgroup.normalizer (R : Set G))).IsSubnormal)
    (hNH : Subgroup.normalizer (R : Set G) ≤ H) (hH : IsCharacteristicP 2 ↥H) :
    H ⊓ Subgroup.centralizer (omegaOneCenterIn (oTwoIn H) : Set G) ≤ centralizerModCore X := by
  have hXH : X ≤ H := hXR.trans hNH
  have hCC := (ThreeSix.subgroupOf_hyps_of_sylow hX hR hXR hsub hNH hH).2.2.2.2
  intro g hg
  have hgH : g ∈ H := (Subgroup.mem_inf.mp hg).1
  have h1 := ThreeSix.subgroupOf_le_centralizer_omegaOneCenterIn
    (inf_le_right : H ⊓ Subgroup.centralizer (omegaOneCenterIn (oTwoIn H) : Set G) ≤ _)
    (show (⟨g, hgH⟩ : ↥H) ∈ (H ⊓ Subgroup.centralizer
      (omegaOneCenterIn (oTwoIn H) : Set G)).subgroupOf H from hg)
  have h2 : g ∈ (centralizerModCore (X.subgroupOf H)).map H.subtype := ⟨⟨g, hgH⟩, hCC h1, rfl⟩
  rw [map_centralizerModCore_subgroupOf hXH] at h2
  exact (Subgroup.mem_inf.mp h2).1

theorem inf_centralizer_omegaOneCenterIn_le_normalizer {X R H : Subgroup G}
    (hX : IsShortGroup ↥X) (hR : IsSylowOf 2 R (centralizerModCore X))
    (hXR : X ≤ Subgroup.normalizer (R : Set G))
    (hsub : (X.subgroupOf (Subgroup.normalizer (R : Set G))).IsSubnormal)
    (hNH : Subgroup.normalizer (R : Set G) ≤ H) (hH : IsCharacteristicP 2 ↥H) :
    H ⊓ Subgroup.centralizer (omegaOneCenterIn (oTwoIn H) : Set G) ≤
      Subgroup.normalizer (X : Set G) :=
  (inf_centralizer_omegaOneCenterIn_le_centralizerModCore hX hR hXR hsub hNH hH).trans
    (Glue.centralizerModCore_le_normalizer X)

theorem commutator_inf_centralizer_omegaOneCenterIn_le_blockU {X R H : Subgroup G}
    (hX : IsShortGroup ↥X) (hR : IsSylowOf 2 R (centralizerModCore X))
    (hXR : X ≤ Subgroup.normalizer (R : Set G))
    (hsub : (X.subgroupOf (Subgroup.normalizer (R : Set G))).IsSubnormal)
    (hNH : Subgroup.normalizer (R : Set G) ≤ H) (hH : IsCharacteristicP 2 ↥H) :
    ⁅H ⊓ Subgroup.centralizer (omegaOneCenterIn (oTwoIn H) : Set G), X⁆ ≤ blockU X :=
  Subgroup.commutator_le.mpr fun _ hc _ hx =>
    commutator_mem_blockU_of_mem_centralizerModCore hX.residual_eq
      (inf_centralizer_omegaOneCenterIn_le_centralizerModCore hX hR hXR hsub hNH hH hc) hx

theorem isSylowOf_inf_centralizer_omegaOneCenterIn {X R H : Subgroup G}
    (hX : IsShortGroup ↥X) (hR : IsSylowOf 2 R (centralizerModCore X))
    (hXR : X ≤ Subgroup.normalizer (R : Set G))
    (hsub : (X.subgroupOf (Subgroup.normalizer (R : Set G))).IsSubnormal)
    (hNH : Subgroup.normalizer (R : Set G) ≤ H) (hH : IsCharacteristicP 2 ↥H) :
    IsSylowOf 2 (R ⊓ Subgroup.centralizer (omegaOneCenterIn (oTwoIn H) : Set G))
      (H ⊓ Subgroup.centralizer (omegaOneCenterIn (oTwoIn H) : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRH : R ≤ H := Subgroup.le_normalizer.trans hNH
  have hK : IsSylowOf 2 R (centralizerModCore X ⊓ H) :=
    SixThree.isSylowOf_of_le hR (le_inf hR.1 hRH) inf_le_left
  have hNK : H ⊓ Subgroup.centralizer (omegaOneCenterIn (oTwoIn H) : Set G) ≤
      centralizerModCore X ⊓ H :=
    le_inf (inf_centralizer_omegaOneCenterIn_le_centralizerModCore hX hR hXR hsub hNH hH)
      inf_le_left
  have hKN := (inf_le_right : centralizerModCore X ⊓ H ≤ H).trans
    (ThreeSix.le_normalizer_self_inf_centralizer (ThreeSix.le_normalizer_omegaOneCenterIn H))
  have h := (CFSG.ABGLocalTools.isSylowOf_iff.mpr hK).inf_of_le_normalizer hNK hKN
  rw [CFSG.ABGLocalTools.isSylowOf_iff, ← inf_assoc, inf_eq_left.mpr hRH] at h
  exact h

end CFSG.CGT.PushingUpLit.ThmOne
