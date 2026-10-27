module

public import CFSG.ClassicalInvolution.AschTight.MuZ2Final
public import CFSG.ClassicalInvolution.AschTight.WreathedData
public import CFSG.ClassicalInvolution.AschTight.C19Bridge
public import CFSG.ClassicalInvolution.AschTight.CStarCount

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable (p f : ℕ) [Fact p.Prime]

@[expose] def E2StarS3Tmp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    TightBranchD p f K z → ¬ AllTypeTwo K z → CITBelowAll p (Nat.card G) → ¬ ConcOrTF4 G →
      CStarTwoRankOne K

variable {p f}

variable {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G}

theorem exists_sylow_setup (ht : S19R.TightStd p f K z) :
    ∃ (Q₀ : Sylow 2 K) (S : Sylow 2 G), (Q₀ : Subgroup K).map K.subtype ≤ (S : Subgroup G) ∧
      (S : Subgroup G) ≤ Subgroup.normalizer (((Q₀ : Subgroup K).map K.subtype : Subgroup G) :
        Set G) ∧
      (S : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G) ∧
      (S : Subgroup G) ⊓ K ≤ (Q₀ : Subgroup K).map K.subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htb := ht.toTightBranch
  obtain ⟨Q₀⟩ : Nonempty (Sylow 2 K) := inferInstance
  set R : Subgroup G := (Q₀ : Subgroup K).map K.subtype with hRdef
  have hR : R ∈ RSet (CoreAssembly.conjClass K) :=
    ⟨K, CoreAssembly.mem_conjClass_self K, Q₀, rfl⟩
  have hzR : IsUniqueInvolution R z :=
    isUniqueInvolution_of_mem_rSet_of_le htb hR (Subgroup.map_subtype_le _)
  obtain ⟨S, hRS⟩ := (Q₀.isPGroup'.map K.subtype).exists_le_sylow
  have hSN : (S : Subgroup G) ≤ Subgroup.normalizer (R : Set G) := by
    intro s hs
    have hle : conjSubgroup s R ≤ (S : Subgroup G) := by
      intro x hx
      have hx' := mem_conjSubgroup_iff.mp hx
      have e : x = s * (s⁻¹ * x * s) * s⁻¹ := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hs (hRS hx')) (Subgroup.inv_mem _ hs)
    exact conjSubgroup_eq_self_iff.mp
      (conjSubgroup_sylow_eq_of_tightD ht Q₀ S.isPGroup' hRS hle)
  refine ⟨Q₀, S, hRS, hSN, fun s hs => ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := hzR.conj_eq (conjSub_eq_of_mem_normalizer (hSN hs))
    calc s * z = s * z * s⁻¹ * s := by group
      _ = z * s := by rw [h1]
  · have h2 : IsPGroup 2 (((S : Subgroup G) ⊓ K).subgroupOf K) :=
      (S.isPGroup'.to_le inf_le_left).comap_subtype
    have hle : (Q₀ : Subgroup K) ≤ ((S : Subgroup G) ⊓ K).subgroupOf K := by
      intro x hx
      exact Subgroup.mem_subgroupOf.mpr ⟨hRS ⟨x, hx, rfl⟩, x.2⟩
    have heq := Q₀.3 h2 hle
    intro x hx
    have hxK : x ∈ K := hx.2
    have : (⟨x, hxK⟩ : K) ∈ ((S : Subgroup G) ⊓ K).subgroupOf K :=
      Subgroup.mem_subgroupOf.mpr hx
    rw [heq] at this
    exact ⟨⟨x, hxK⟩, this, rfl⟩

theorem ascStand_of_tightD [IsSimpleGroup G] (hIH : IHAllD p f) (h8 : IHInterface8 p)
    (hAE : AEmptyD p f) (ht : S19R.TightStd p f K z) :
    AscStand p f (CoreAssembly.conjClass K) K where
  odd := ht.branch.odd
  five := ht.branch.five
  hyp := hypOmegaMod_of_tightD ht
  below := hIH G K z ht.branch
  ih := h8 _ (hIH G K z ht.branch)
  aEmpty := hAE G K z ht.branch
  mem := CoreAssembly.mem_conjClass_self K
  trans := fun J hJ => by
    obtain ⟨g, rfl⟩ := CoreAssembly.single_class K J hJ
    exact ⟨g, rfl⟩
  gen := (inClass_conjugates ht.branch.member).generated

variable (p f) in
theorem tightControlledD_of_inputs (hB3 : GoldschmidtB3Tmp) (h62 : L6_2ModTmp p f)
    (h5 : C19_5 p f) (h16 : C19_16Tmp p f) (hE2 : E2StarS3Tmp p f) (hW : W69 p f)
    (hIH : IHAllD p f) (h8 : IHInterface8 p) (hAE : AEmptyD p f) : TightControlledD p f := by
  intro G _ _ _ K z ht0
  have ht := S19R.tightStd_of_tightBranchD ht0
  by_cases hc : ConcOrTF4 G
  · exact hc.conclusionD ht.branch.notFourGenerated
  exfalso
  by_cases hA : AllTypeTwo K z
  · exact false_of_allTypeTwo hB3 ht hA
  have htb := ht.toTightBranch
  have hI := isUniqueInvolution_of_tight htb
  have hstand := ascStand_of_tightD hIH h8 hAE ht
  obtain ⟨Q₀, S, hRS, -, hSz, -⟩ := exists_sylow_setup ht
  set R : Subgroup G := (Q₀ : Subgroup K).map K.subtype with hRdef
  have hstd : Std6 p f (CoreAssembly.conjClass K) K S R z :=
    ⟨hstand, ht.edgeless, hI, ⟨K, CoreAssembly.mem_conjClass_self K, Q₀, rfl⟩,
      Subgroup.map_subtype_le _, hRS, hc⟩
  obtain ⟨W, hWmem, hWS⟩ := hW G _ K hstand S
  obtain ⟨L, hL, t, htL, htz, V, hV, hVS, htV⟩ := exists_data_of_not_allTypeTwo h62 ht hA S hSz
  have hE3 := normalizerQuotientTwoGeneratedStar_of_c19_5 h5 h16 ht (hIH G K z ht.branch) hstd
    hWmem hWS hL htL htz hV hVS htV
  have hE2' := hE2 G K z ht0 hA (hIH G K z ht.branch) hc
  exact ht.branch.notFourGenerated (twoSubgroupsFourGenerated_of_edgeless_star ht.branch.odd
    ht.branch.five ht.branch.member ht0.control (deltaEdgeless_of_dEdgeless ht.edgeless)
    (commutingSylowForcesCommuting_of_tightD ht) hE2' hE3)

end CFSG.ClassicalInvolution.Disconnected.AschTight
