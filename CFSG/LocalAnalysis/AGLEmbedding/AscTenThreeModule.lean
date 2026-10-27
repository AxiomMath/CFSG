module

public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs
import CFSG.LocalAnalysis.AGLEmbedding.AscEightFourAux
import CFSG.CGT.PushingUpLit.Glue.CStarBridge
import CFSG.LocalAnalysis.AGLEmbedding.LocalCGTBridge

public section

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

namespace CFSG.AGLEmbedding

namespace AscTenThree

variable {G : Type} [Group G] [Finite G] {X S L : Subgroup G}

omit [Finite G] in
theorem le_centralizer_omegaOneCenterOf_self (Y : Subgroup G) :
    Y ≤ Subgroup.centralizer (omegaOneCenterOf Y : Set G) := by
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  exact (Subgroup.mem_centralizer_iff.mp (C1GN.omegaOneCenterOf_le_centerOf _ hv).2 y hy).symm

omit [Finite G] in
theorem le_normalizer_omegaOneCenterOf_twoCore (X : Subgroup G) :
    X ≤ Subgroup.normalizer (omegaOneCenterOf (pCoreOf 2 X) : Set G) :=
  le_normalizer_omegaOneCenterOf_of_le_normalizer
    (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 X)

theorem omegaOneCenterOf_le_V (hyp : Asc81bHyp X S) :
    omegaOneCenterOf S ≤ omegaOneCenterOf (pCoreOf 2 X) := by
  have hQS : pCoreOf 2 X ≤ S := hyp.twoCore_le
  have hSX : S ≤ X := hyp.twoRadical.1
  have hZ : centerOf S ≤ centerOf (pCoreOf 2 X) := by
    rintro z ⟨hzS, hzC⟩
    have hzQ : z ∈ X ⊓ Subgroup.centralizer (pCoreOf 2 X : Set G) := by
      refine ⟨hSX hzS, ?_⟩
      exact Subgroup.centralizer_le (fun q hq => hQS hq) hzC
    exact ⟨hyp.charTwo hzQ, hzQ.2⟩
  exact Subgroup.closure_mono fun x hx => ⟨hZ hx.1, hx.2⟩

theorem inf_centralizer_V_le_normalizer (hyp : Asc81bHyp X S) :
    X ⊓ Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 X) : Set G) ≤
      Subgroup.normalizer (S : Set G) := by
  have h := LocalCGT.centralizer_inf_le_cgsIn (X := X) hyp.twoRadical.isPGroup hyp.twoRadical.2.1
  rw [CFSG.CGT.PushingUpLit.Glue.omegaOneCenterIn_eq, inf_comm] at h
  refine le_trans ?_ (h.trans (hyp.cgs.le.trans inf_le_right))
  exact inf_le_inf_left X (Subgroup.centralizer_le (omegaOneCenterOf_le_V hyp))

theorem inf_centralizer_V_le_twoCore (hyp : Asc81bHyp X S) :
    S ⊓ Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 X) : Set G) ≤ pCoreOf 2 X := by
  set V := omegaOneCenterOf (pCoreOf 2 X) with hV
  set C := X ⊓ Subgroup.centralizer (V : Set G) with hC
  have hSX : S ≤ X := hyp.twoRadical.1
  have hXV : X ≤ Subgroup.normalizer (V : Set G) := le_normalizer_omegaOneCenterOf_twoCore X
  have hDC : S ⊓ Subgroup.centralizer (V : Set G) ≤ C := inf_le_inf_right _ hSX
  have hCX : C ≤ X := inf_le_left
  have hCnorm : X ≤ Subgroup.normalizer (C : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro c
    have key : ∀ g ∈ X, ∀ c ∈ C, g * c * g⁻¹ ∈ C := by
      intro g hg c hc
      refine ⟨X.mul_mem (X.mul_mem hg hc.1) (X.inv_mem hg), ?_⟩
      show g * c * g⁻¹ ∈ Subgroup.centralizer (V : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have hv' : g⁻¹ * v * g ∈ V := by
        have := (Subgroup.mem_normalizer_iff.mp (hXV (X.inv_mem hg)) v).mp hv
        simpa using this
      have h1 := Subgroup.mem_centralizer_iff.mp hc.2 _ hv'
      calc v * (g * c * g⁻¹) = g * ((g⁻¹ * v * g) * c) * g⁻¹ := by group
        _ = g * (c * (g⁻¹ * v * g)) * g⁻¹ := by rw [h1]
        _ = g * c * g⁻¹ * v := by group
    constructor
    · exact key g hg c
    · intro h
      have := key g⁻¹ (X.inv_mem hg) _ h
      rwa [show g⁻¹ * (g * c * g⁻¹) * g⁻¹⁻¹ = c by group] at this
  have hDnorm : C ≤ Subgroup.normalizer ((S ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) :
      Set G) := by
    intro c hc
    have hcS := Subgroup.mem_normalizer_iff.mp (inf_centralizer_V_le_normalizer hyp hc)
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨hyS, hyC⟩
      refine ⟨(hcS y).mp hyS, ?_⟩
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hc.2 hyC) (Subgroup.inv_mem _ hc.2)
    · rintro ⟨hyS, hyC⟩
      refine ⟨(hcS y).mpr hyS, ?_⟩
      have := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hc.2) hyC) hc.2
      rwa [show c⁻¹ * (c * y * c⁻¹) * c = y by group] at this
  have hsub : CFSG.Open.IsSubnormal (S ⊓ Subgroup.centralizer (V : Set G)) X :=
    CFSG.Open.IsSubnormal.step hDC ((Subgroup.normal_subgroupOf_iff_le_normalizer hDC).mpr hDnorm)
      (CFSG.Open.IsSubnormal.step hCX ((Subgroup.normal_subgroupOf_iff_le_normalizer hCX).mpr
        hCnorm) (CFSG.Open.IsSubnormal.refl X))
  exact CFSG.RankThreeEvenClassification.Helpers.subnormal_pSubgroup_le_pCoreOf 2 hsub
    (hyp.twoRadical.isPGroup.to_le inf_le_left)

omit [Finite G] in
theorem mk_eq_one_of_mem_pCoreOf {x : ↥X} (hx : (x : G) ∈ pCoreOf 2 X) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥X) x = 1 := by
  obtain ⟨y, hy, hyx⟩ := hx
  obtain rfl : y = x := Subtype.ext hyx
  exact (QuotientGroup.eq_one_iff y).mpr hy

theorem barM_le_normalizer_of_le_centralizer_V (hyp : Asc81bHyp X S) (hLX : L ≤ X)
    (hLV : L ≤ Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 X) : Set G)) :
    barM X S ≤ Subgroup.normalizer (barM X L : Set (↥X ⧸ CFSG.pCore 2 ↥X)) := by
  set V := omegaOneCenterOf (pCoreOf 2 X) with hV
  have hSX : S ≤ X := hyp.twoRadical.1
  have hXV : X ≤ Subgroup.normalizer (V : Set G) := le_normalizer_omegaOneCenterOf_twoCore X
  have key : ∀ ℓ ∈ L, ∀ s ∈ S, ℓ * s * ℓ⁻¹ * s⁻¹ ∈ pCoreOf 2 X := by
    intro ℓ hℓ s hs
    have hℓN : ℓ ∈ Subgroup.normalizer (S : Set G) :=
      inf_centralizer_V_le_normalizer hyp ⟨hLX hℓ, hLV hℓ⟩
    apply inf_centralizer_V_le_twoCore hyp
    refine ⟨S.mul_mem ((Subgroup.mem_normalizer_iff.mp hℓN s).mp hs) (S.inv_mem hs), ?_⟩
    have hsV : s * ℓ⁻¹ * s⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have hv' : s⁻¹ * v * s ∈ V := by
        have := (Subgroup.mem_normalizer_iff.mp (hXV (X.inv_mem (hSX hs))) v).mp hv
        simpa using this
      have h1 := Subgroup.mem_centralizer_iff.mp (Subgroup.inv_mem _ (hLV hℓ)) _ hv'
      calc v * (s * ℓ⁻¹ * s⁻¹) = s * ((s⁻¹ * v * s) * ℓ⁻¹) * s⁻¹ := by group
        _ = s * (ℓ⁻¹ * (s⁻¹ * v * s)) * s⁻¹ := by rw [h1]
        _ = s * ℓ⁻¹ * s⁻¹ * v := by group
    show ℓ * s * ℓ⁻¹ * s⁻¹ ∈ Subgroup.centralizer (V : Set G)
    rw [show ℓ * s * ℓ⁻¹ * s⁻¹ = ℓ * (s * ℓ⁻¹ * s⁻¹) by group]
    exact Subgroup.mul_mem _ (hLV hℓ) hsV
  refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
  rintro _ ⟨s, hs, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨ℓ, hℓ, rfl⟩
  have h1 := mk_eq_one_of_mem_pCoreOf (x := ℓ * s * ℓ⁻¹ * s⁻¹)
    (key (ℓ : G) (Subgroup.mem_subgroupOf.mp hℓ) (s : G) (Subgroup.mem_subgroupOf.mp hs))
  simp only [map_mul, map_inv] at h1
  have h2 : QuotientGroup.mk' (CFSG.pCore 2 ↥X) ℓ * QuotientGroup.mk' (CFSG.pCore 2 ↥X) s =
      QuotientGroup.mk' (CFSG.pCore 2 ↥X) s * QuotientGroup.mk' (CFSG.pCore 2 ↥X) ℓ := by
    calc _ = (QuotientGroup.mk' (CFSG.pCore 2 ↥X) ℓ * QuotientGroup.mk' (CFSG.pCore 2 ↥X) s *
          (QuotientGroup.mk' (CFSG.pCore 2 ↥X) ℓ)⁻¹ *
          (QuotientGroup.mk' (CFSG.pCore 2 ↥X) s)⁻¹) *
          (QuotientGroup.mk' (CFSG.pCore 2 ↥X) s * QuotientGroup.mk' (CFSG.pCore 2 ↥X) ℓ) := by
          group
      _ = _ := by rw [h1, one_mul]
  exact h2

end AscTenThree

end CFSG.AGLEmbedding
