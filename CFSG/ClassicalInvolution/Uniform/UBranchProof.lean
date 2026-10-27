module

public import CFSG.ClassicalInvolution.Uniform.UBranch
public import CFSG.ClassicalInvolution.Uniform.UHypOmegaGen
public import CFSG.ClassicalInvolution.Uniform.UPilot
public import CFSG.ClassicalInvolution.Asc77.AscHypOmegaMain

public section

namespace CFSG.ClassicalInvolution.Uniform

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.AscHypOmega
  CFSG.ClassicalInvolution.Disconnected
open scoped MatrixGroups

section Stand

variable {p f : ℕ} [Fact p.Prime]

theorem ascStandOfBranchU_of (hΩ : HypOmegaModDU p f) (hA : AEmptyDU p f) (hall : IHAllDU p f)
    (hih : IHInterface8U p) : AscStandOfBranchU p f := by
  intro G _ _ _ K z h
  have hK := h.member_satU
  exact
    { odd := h.odd
      three := h.three
      hyp := hΩ G K z h
      below := hall G K z h
      ih := hih _ (hall G K z h)
      aEmpty := hA G K z h
      mem := CoreAssembly.mem_conjClass_self _
      trans := fun J hJ => by
        obtain ⟨g, rfl⟩ := hJ
        exact ⟨g, rfl⟩
      gen := gen_conjClass _ hK.mem hK.ne_one }

omit [Fact p.Prime] in
theorem ihAllDU_of_minimal {n : ℕ} (hn : CITBelowAllT p n)
    (hbig : ¬ CITBelowT (.sl2 p f) (n + 1)) : IHAllDU p f := by
  intro G _ _ _ K z h e he
  by_cases hle : Nat.card G ≤ n
  · exact CITBelowT.mono hle (hn e he)
  · exact absurd (CITBelowT.mono (by omega) h.below) hbig

end Stand

section Fusion

variable {t : MemberType} {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G}

theorem omega5At_of_fusionAtU (hc : t.Cert) (h₀ : IsClassicalMemberU t K z)
    (hint : IsIntrinsicU t K z) (hfus : FusionAt K z) :
    Omega5At (CoreAssembly.conjClass K) K z := by
  intro J hJ _ v hvJ hvnc hv2 hvz
  have hU₀ := h₀.isUniqueInvolution hc
  obtain ⟨b, rfl⟩ := CoreAssembly.single_class K J hJ
  have hUb := (h₀.conj b).isUniqueInvolution hc
  by_cases ht : b * z * b⁻¹ = z
  · exact normalizer_of_twinsU hc h₀ hint (CoreAssembly.mem_conjClass_self K) hJ hU₀
      (ht ▸ hUb) hvJ
  · by_cases htw : HasTwin K z
    · exact hfus htw _ hJ _ hUb ht v hvJ hv2 hvnc hvz
    · exact centralizer_le_normalizer_of_not_hasTwin hU₀ htw
        (Subgroup.mem_centralizer_singleton_iff.mpr hvz)

theorem hypOmegaModU_of_fusionAtU (hc : t.Cert) (h₀ : IsClassicalMemberU t K z)
    (hint : IsIntrinsicU t K z) (hfus : FusionAt K z) :
    HypOmegaModU t (CoreAssembly.conjClass K) :=
  hypOmegaModU_conjClass hc h₀ hint (omega5At_of_fusionAtU hc h₀ hint hfus)

theorem fusionAt_of_twoElementsNormalize (h₀ : IsClassicalMemberU t K z)
    (h : Hat2A7R.TwoElementsNormalize K z) : FusionAt K z := by
  intro _ J hJ _ _ _ v hvJ hv2 hvnc hvz
  obtain ⟨b, rfl⟩ := CoreAssembly.single_class K J hJ
  have hk : b⁻¹ * v * b ∈ K := mem_conjSub_iff.mp hvJ
  have hk2 : IsPGroup 2 (Subgroup.zpowers (b⁻¹ * v * b)) := by
    have := isPGroup_zpowers_conj hv2 b⁻¹
    rwa [inv_inv] at this
  have hkz : b⁻¹ * v * b ∉ Subgroup.zpowers z := by
    intro hmem
    apply hvnc
    intro w hw
    have hwK : b⁻¹ * w * b ∈ K := mem_conjSub_iff.mp hw
    have hcomm : (b⁻¹ * v * b) * (b⁻¹ * w * b) = (b⁻¹ * w * b) * (b⁻¹ * v * b) := by
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
      rw [← hn]
      have hzc : Commute z (b⁻¹ * w * b) := h₀.comm_of_mem hwK
      exact (hzc.zpow_left n).eq
    calc v * w = b * ((b⁻¹ * v * b) * (b⁻¹ * w * b)) * b⁻¹ := by group
      _ = b * ((b⁻¹ * w * b) * (b⁻¹ * v * b)) * b⁻¹ := by rw [hcomm]
      _ = w * v := by group
  have hbk : b * (b⁻¹ * v * b) * b⁻¹ = v := by group
  have := h _ hk hk2 hkz b (by rw [hbk]; exact Subgroup.mem_centralizer_singleton_iff.mpr hvz)
  rwa [hbk] at this

end Fusion

section HypOmega

variable {p f : ℕ}

@[expose] def ClassicalFusionStmtU (t : MemberType) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), IsClassicalMemberU t K z → IsIntrinsicU t K z →
      CITBelowT t (Nat.card G) → FusionAt K z

theorem hypOmegaModDU_of_fusionU (h : ClassicalFusionStmtU (.sl2 p f)) : HypOmegaModDU p f := by
  intro G _ _ _ K z hb
  have hm := hb.member_satU
  have hi := hb.intrinsic_satU
  exact hypOmegaModU_of_fusionAtU (MemberType.cert_sl2 p f) hm hi
    (h G hb.nonabelian _ z hm hi hb.below)

theorem classicalFusionStmtU_of_twoElementsNormalizeU {t : MemberType}
    (h : TwoElementsNormalizeU t) : ClassicalFusionStmtU t :=
  fun G _ _ _ hnab K z hK hi _ => fusionAt_of_twoElementsNormalize hK (h G hnab K z hK hi)

theorem hypOmegaModDU_of_twoElementsNormalizeU (h : TwoElementsNormalizeU (.sl2 p f)) :
    HypOmegaModDU p f := by
  intro G _ _ _ K z hb
  have hm := hb.member_satU
  have hi := hb.intrinsic_satU
  exact hypOmegaModU_conjClass (MemberType.cert_sl2 p f) hm hi
    (omega5At_of_twoElementsNormalize hm (h G hb.nonabelian _ z hm hi))

variable [Fact p.Prime]

theorem classicalFusionStmtU_iff (hq : 5 ≤ p ^ f) :
    ClassicalFusionStmtU (.sl2 p f) ↔ ClassicalFusionStmt p f := by
  have hns := not_isSolvableType_sl2_of_five_le hq
  have hf : 0 < f := Nat.pos_of_ne_zero (by rintro rfl; simp at hq)
  constructor
  · intro h G _ _ _ hnab hp2 _ K z hz hbelow
    exact h G hnab K z (IsClassicalMemberU.ofGeneric hp2 hf hz)
      (IsIntrinsicU.of_not_isSolvableType hns)
      ((citBelowT_iff_citBelowU hp2 hq _).mpr hbelow)
  · intro h G _ _ _ hnab K z hz _ hbelow
    exact h G hnab hz.admissible.2.1 hq K z (hz.toGeneric hq)
      ((citBelowT_iff_citBelowU hz.admissible.2.1 hq _).mp hbelow)

end HypOmega

section Assembly

variable {p f : ℕ} [Fact p.Prime]

theorem ascStandOfBranchU_of_inputs (hF : ClassicalFusionStmtU (.sl2 p f)) (hA : AEmptyDU p f)
    (hall : IHAllDU p f) (hih : IHInterface8U p) : AscStandOfBranchU p f :=
  ascStandOfBranchU_of (hypOmegaModDU_of_fusionU hF) hA hall hih

end Assembly

end CFSG.ClassicalInvolution.Uniform
