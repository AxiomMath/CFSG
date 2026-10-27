module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265Fam
public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4TCore
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BAct
import CFSG.LocalAnalysis.GLTheoremA.CatA.S171Basic
import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FDynBridge
import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FDynTri
import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bO8
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs141c
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I137Facts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265Cfg
public import CFSG.LocalAnalysis.GLTheoremA.S3.ChevTools
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatTypeDet
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265A

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.S265
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

variable {Ω : Type} [Group Ω] [Finite Ω] {S B T : Subgroup Ω} {x : Ω} {D K : Subgroup Ω}

omit [Finite Ω] in
private theorem commute_of_chevQuotHom_eq (hcore : GLAPPrimeCore 3 ↥S = ⊥) {a b : ↥S}
    (h : chevQuotHom 3 S a = chevQuotHom 3 S b) (s : ↥S) : a⁻¹ * b * s = s * (a⁻¹ * b) := by
  have h' : (QuotientGroup.mk (pQuotHom 3 S a) : PSimple 3 S) =
      QuotientGroup.mk (pQuotHom 3 S b) := h
  have hc := Subgroup.mem_center_iff.1 (QuotientGroup.eq.1 h') (pQuotHom 3 S s)
  have hinj : Function.Injective (pQuotHom 3 S) := by
    rw [← MonoidHom.ker_eq_bot_iff]
    show (QuotientGroup.mk' (GLAPPrimeCore 3 ↥S)).ker = ⊥
    rw [QuotientGroup.ker_mk', hcore]
  apply hinj
  simp only [map_mul, map_inv]
  exact hc.symm

omit [Finite Ω] in
private theorem chevQuotHom_eq_of_chevQuotHom_eq (hcore : GLAPPrimeCore 3 ↥S = ⊥) (hKS : K ≤ S)
    {a b : ↥K} (h : chevQuotHom 3 S ⟨a, hKS a.2⟩ = chevQuotHom 3 S ⟨b, hKS b.2⟩) :
    chevQuotHom 3 K a = chevQuotHom 3 K b := by
  have hcen : pQuotHom 3 K (a⁻¹ * b) ∈ Subgroup.center (PQuot 3 K) := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨k, rfl⟩ := pQuotHom_surjective 3 K q
    rw [← map_mul, ← map_mul]
    congr 1
    have hk := congrArg Subtype.val (commute_of_chevQuotHom_eq hcore h ⟨k, hKS k.2⟩)
    exact Subtype.ext (by simpa using hk.symm)
  show (QuotientGroup.mk (pQuotHom 3 K a) : PSimple 3 K) = QuotientGroup.mk (pQuotHom 3 K b)
  exact QuotientGroup.eq.2 (by rwa [← map_inv, ← map_mul])

section Derived


private theorem d4_not_derived {X : Type} [Group X] [Finite X] (hcen : Subgroup.center X = ⊥)
    {lab : GLALabel} (hX : Y10F.HasLabel X (· = lab)) (h3 : 3 ^ 5 ∣ Nat.card X) :
    lab.tag ≠ .B2der ∧ lab.tag ≠ .G2der ∧ lab.tag ≠ .twF4der := by
  have hlam := CanonSubcomp.lambda2_of_hasLabel hX
  have hM := CanonSubcomp.markedModel_of_hasLabel hX
  have hZ : Nat.card (X ⧸ Subgroup.center X) = Nat.card X :=
    Nat.card_congr (CanonInn.quotCenterEquivOfBot hcen).toEquiv
  obtain ⟨t, r, n⟩ := lab
  refine ⟨?_, ?_, ?_⟩ <;> intro ht <;> simp only at ht <;> subst ht
  · obtain ⟨-, rfl, rfl⟩ := hlam
    rw [← hZ, card_of_B2der hM] at h3
    norm_num at h3
  · obtain ⟨-, rfl, rfl⟩ := hlam
    rw [← hZ, card_of_G2der hM] at h3
    norm_num at h3
  · obtain ⟨-, rfl, rfl⟩ := hlam
    have hc := CanonTriL.card_of_label_char_two hcen hX rfl
    simp only [CFSG.StandardType.markTag, CFSG.StandardType.markRank,
      CFSG.StandardType.markDeg, CFSG.SeitzReduction.F4Pilot.evenLieOrder] at hc
    rw [hc] at h3
    norm_num [CFSG.Open.ordTits] at h3

end Derived

section Main


theorem QSNL.triD4_data (h : QSNL 3 S B T x D K) (hJ : catalogIs (PSimple 3 K) S9.isD4two)
    (hout : ∃ e ∈ B, ∃ he : e ∈ Subgroup.normalizer (K : Set Ω),
      chevAut 3 K ⟨e, he⟩ ∉ D4T.innerAut (PSimple 3 K)) :
    IsSimpleGroup (PSimple 3 S) ∧ (∃ a b : PSimple 3 S, a * b ≠ b * a) ∧
    ∃ (d : TauCeti.ValidLieTypeIndex) (α β : MulAut (PSimple 3 S)) (J : Subgroup (PSimple 3 S)),
      d.1.characteristic = 2 ∧ Nonempty (PSimple 3 S ≃* (TauCeti.CFSGIndex.lie d).Group) ∧
      α ∈ innAutDerived (PSimple 3 S) ∧ α ^ 3 = 1 ∧ α ≠ 1 ∧
      β ∈ innAutDerived (PSimple 3 S) ∧ β ^ 3 = 1 ∧ Commute α β ∧
      GLAPComponent 3 (fixSubgroup α) J ∧ catalogIs (PSimple 3 J) S9.isD4two ∧
      (∀ y ∈ J, β y ∈ J) ∧ ¬ ∃ j ∈ J, ∀ y ∈ J, β y = j * y * j⁻¹ := by
  have hp : Nat.Prime 3 := Nat.prime_three
  obtain ⟨e, heB, heK, hne⟩ := hout
  have hSN : ∀ g : Ω, g ∈ Subgroup.normalizer (S : Set Ω) := fun g =>
    (Subgroup.normalizer_eq_top_iff.2 h.cfg.normal) ▸ Subgroup.mem_top g
  have hq : CFSG.Open.IsQuasisimple (PQuot 3 S) :=
    isQuasisimple_pQuot_of_glaPComponent hp h.cfg.comp
  have hcen : Subgroup.center (PSimple 3 S) = ⊥ := Y10F.center_centerQuot_eq_bot hq
  obtain ⟨y, hyD, hyx⟩ := S171.exists_y hp h.cfg.x1 h.cfg.std
  have hyB : y ∈ B := h.cfg.std.1 hyD
  have hpK : 3 ∣ Nat.card K :=
    (show 3 ∣ Nat.card (PSimple 3 K) by rw [card_o8p2 hJ]; norm_num).trans
      ((Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_quotient_dvd_card _))
  have hN := h.nlAct hpK
  have hKS : K ≤ S := hN.comp.1.trans inf_le_left
  have hCx : Subgroup.centralizer ({x} : Set Ω) = ⊤ :=
    eq_top_iff.2 fun g _ => Subgroup.mem_centralizer_singleton_iff.2 (h.cfg.xcen g)
  have hKy : GLAPComponent 3 (S ⊓ Subgroup.centralizer ({y} : Set Ω)) K := by
    convert hN.comp using 1
    rw [S10.cs, S171.cs_eq hp h.cfg.x1 h.cfg.std hyD hyx, hCx, top_inf_eq]
  have hy3 : IsPGroup 3 (Subgroup.zpowers y) := isPGroup_zpowers_of_mem h.cfg.elem hyB
  obtain ⟨eJ⟩ := nonempty_pSimple_equiv_chevTransfer hp (hSN y) hy3 hKy
  have hT : catalogIs (PSimple 3 (chevTransfer 3 S K)) S9.isD4two := by
    obtain ⟨i, hi, ⟨f⟩⟩ := hJ
    exact ⟨i, hi, ⟨eJ.symm.trans f⟩⟩
  have hdvd : 3 ^ 5 * 716800 ∣ Nat.card (PSimple 3 S) := by
    rw [← card_o8p2 hT]
    exact (Subgroup.card_quotient_dvd_card _).trans ((Subgroup.card_quotient_dvd_card _).trans
      (Subgroup.card_subgroup_dvd_card _))
  obtain ⟨d, hd, hSd⟩ : ∃ d : TauCeti.ValidLieTypeIndex, d.1.characteristic = 2 ∧
      Nonempty (PSimple 3 S ≃* (TauCeti.CFSGIndex.lie d).Group) := by
    rcases h.cfg.chev with ⟨i, hi, hiS⟩ | ⟨i, hi, ⟨f⟩⟩
    · cases i with
      | lie d => exact ⟨d, hi, hiS⟩
      | _ => exact False.elim hi
    · have h1 := GLTheoremB.MovingAround.Inputs141c.card_le_of_ambiguousChev_two hi f
      have h2 := Nat.le_of_dvd Nat.card_pos hdvd
      omega
  have hmem : ∀ a ∈ B, chevAut 3 S ⟨a, hSN a⟩ ∈ innAutDerived (PSimple 3 S) := by
    intro a ha
    have hInnZ : S10.InnDiagOn 3 (Subgroup.zpowers a) S :=
      ⟨fun z _ => hSN z, CFSG.StandardType.Canonical.largeEvenMarking_mono
        (fun _ _ _ _ _ _ hP b hb => hP b (Subgroup.zpowers_le.mpr ha hb)) h.cfg.inn.2⟩
    obtain ⟨lab, -, hkind⟩ := I141F.innDiagKind_chevAut (hSN a) hq hInnZ
    have hlab : Y10F.HasLabel (PSimple 3 S) (· = lab) :=
      CFSG.StandardType.Canonical.largeEvenMarking_mono (fun _ _ _ _ _ _ hP => hP.1) hkind
    exact I141F.Tri.mem_innAutDerived_of_innDiagKind_of_not_derived hcen
      (d4_not_derived hcen hlab ((dvd_mul_right _ _).trans hdvd)) hkind
  refine ⟨hq.2, ?_, d, chevAut 3 S ⟨y, hSN y⟩, chevAut 3 S ⟨e, hSN e⟩, chevTransfer 3 S K, hd,
    hSd, hmem y hyB, chevAut_pow_eq_one 3 S (hSN y) (h.cfg.elem.2 y hyB), fun h1 => hyx
      ((h.cfg.centB y hyB).1 ((chevAut_eq_one_iff hp h.cfg.comp (hSN y)).1 h1)),
    hmem e heB, chevAut_pow_eq_one 3 S (hSN e) (h.cfg.elem.2 e heB), ?_,
    glaPComponent_chevTransfer hp (hSN y) hy3 hKy, hT, ?_, ?_⟩
  ·
    obtain ⟨-, lab, -, hraw⟩ := h.cfg.inn.2
    obtain ⟨R, _, -, -, -, ⟨a, b, hab⟩, θ, -⟩ :=
      CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
    exact ⟨θ.symm a, θ.symm b, fun h' => hab (by simpa using congrArg θ h')⟩
  · show chevAut 3 S _ * chevAut 3 S _ = chevAut 3 S _ * chevAut 3 S _
    rw [← map_mul, ← map_mul]
    exact congrArg _ (Subtype.ext (isElemAbelian_commute h.cfg.elem hyB heB))
  ·
    rintro s hs
    obtain ⟨k, hkK, rfl⟩ := Subgroup.mem_map.1 hs
    rw [chevAut_chevQuotHom]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2
      ((Subgroup.mem_normalizer_iff.1 (hN.norm heB) k).1 (Subgroup.mem_subgroupOf.1 hkK)))
  ·
    rintro ⟨j, hj, hjβ⟩
    obtain ⟨k₀, hk₀K, rfl⟩ := Subgroup.mem_map.1 hj
    apply hne
    refine MonoidHom.mem_range.2 ⟨chevQuotHom 3 K ⟨k₀, Subgroup.mem_subgroupOf.1 hk₀K⟩, ?_⟩
    ext t
    obtain ⟨k, rfl⟩ := chevQuotHom_surjective 3 K t
    rw [chevAut_chevQuotHom, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
    apply chevQuotHom_eq_of_chevQuotHom_eq h.cfg.core hKS
    have h1 := hjβ (chevQuotHom 3 S ⟨k, hKS k.2⟩)
      (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 k.2))
    rw [chevAut_chevQuotHom, ← map_inv, ← map_mul, ← map_mul] at h1
    exact h1.symm

end Main

end CFSG.LocalAnalysis.GLTheoremA.S265A

end
