module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58SubSec
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58SubStar
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58SubCorr
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58SubHypW
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58NFa
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58ReChoice
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58Section
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aSecX0
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bTableReduced
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7SecL
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupExhaustion
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupRanks
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicFourLarge
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicTwoFourGenerators
public import CFSG.LocalAnalysis.LargeEvenClassification.MacWilliamsReduction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourFullObstruction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourProperSubgroups
public import CFSG.Walter.JRFacts
public import CFSG.Walter.W67.Statements
public import Certificates.Certificate100
public import Certificates.Certificate101
public import Certificates.Certificate102
public import Certificates.Certificate103
public import Certificates.Certificate104
public import Certificates.Certificate105
public import Certificates.Certificate106
public import Certificates.Certificate107
public import Certificates.Certificate108
public import Certificates.Certificate109
public import Certificates.Certificate96
public import Certificates.Certificate97
public import Certificates.Certificate98
public import Certificates.Certificate99

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.LocalCores CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open scoped commutatorElement

namespace Hyp52W

variable {H : Type} [Group H] [Finite H]

instance normal_B_subgroupOf_T (h : Hyp52W H) : (h.B.subgroupOf h.T).Normal :=
  (normal_subgroupOf_iff_le_normalizer (le_inf (le_inf (h.B_le.trans inf_le_left) le_normalizer)
    h.B_le)).mpr fun _ ht => (mem_inf.mp (mem_inf.mp ht).1).2

local notation "π" => QuotientGroup.mk' (pPrimeCore 2 H)

theorem quotient_PQT (h : Hyp52W H) (hS2 : IsPGroup 2 h.S) (h' : Hyp52W (H ⧸ pPrimeCore 2 H))
    (hJ : h'.J = h.J.map π) (hS : h'.S = h.S.map π) (hB : h'.B = h.B.map π) :
    h'.P = h.P.map π ∧ h'.Q = h.Q.map π ∧ h'.T = h.T.map π := by
  have hBS : h.B ≤ h.S := h.B_le.trans inf_le_left
  have hP : h'.P = h.P.map π := by
    show h'.S ⊓ coreActionKernel h'.J = (h.S ⊓ coreActionKernel h.J).map π
    rw [hS, hJ, OddQuot.map_inf_coreActionKernel (h.S_le.trans inf_le_right)]
  have hQ : h'.Q = h.Q.map π := by
    show h'.S ⊓ normalizer (h'.B : Set (H ⧸ pPrimeCore 2 H)) =
      (h.S ⊓ normalizer (h.B : Set H)).map π
    rw [hS, hB, OddQuot.map_inf_normalizer hS2 hBS]
  refine ⟨hP, hQ, ?_⟩
  show h'.Q ⊓ h'.P = (h.Q ⊓ h.P).map π
  rw [hP, hQ, OddQuot.map_inf_of_le hS2 inf_le_left inf_le_left]

theorem nonempty_quotient_T_equiv (h : Hyp52W H) (hS2 : IsPGroup 2 h.S)
    (h' : Hyp52W (H ⧸ pPrimeCore 2 H)) (hB : h'.B = h.B.map π) (hT : h'.T = h.T.map π) :
    Nonempty (↥h'.T ⧸ h'.B.subgroupOf h'.T ≃* ↥h.T ⧸ h.B.subgroupOf h.T) := by
  have hTS : h.T ≤ h.S := inf_le_left.trans inf_le_left
  have hmem : ∀ t : ↥h.T, π t ∈ h'.T := fun t => by
    rw [hT]
    exact mem_map_of_mem π t.2
  let f : ↥h.T →* ↥h'.T :=
    ((QuotientGroup.mk' (pPrimeCore 2 H)).comp h.T.subtype).codRestrict _ hmem
  refine B5a.nonempty_quotient_equiv_of_surjective f ?_ fun t => ?_
  · rintro ⟨z, hz⟩
    rw [hT] at hz
    obtain ⟨t, ht, rfl⟩ := mem_map.mp hz
    exact ⟨⟨t, ht⟩, rfl⟩
  · show π t ∈ h'.B ↔ _
    rw [hB]
    constructor
    · intro hb
      obtain ⟨b, hb, hbt⟩ := mem_map.mp hb
      have heq : b = t :=
        OddQuot.injOn_of_isPGroup hS2 (h.B_le.trans inf_le_left hb) (hTS t.2) hbt
      rw [← heq]
      exact hb
    · exact fun ht => mem_map_of_mem π ht

end Hyp52W

variable {X : Type} [Group X] [Finite X] {h : Hyp52 X} {y : X}

namespace Hyp52

@[expose] noncomputable def subHyp52W (hc : h.SecCond y) (S' : Subgroup ↥(h.secSubImg y))
    (hS'le : S' ≤ centralizer ({hc.subA} : Set ↥(h.secSubImg y)) ⊓
      normalizer ((h.subJ y : Subgroup ↥(h.secSubImg y)) : Set ↥(h.secSubImg y)))
    (hS'syl : ∃ R : Sylow 2 ↥(centralizer ({hc.subA} : Set ↥(h.secSubImg y)) ⊓
        normalizer ((h.subJ y : Subgroup ↥(h.secSubImg y)) : Set ↥(h.secSubImg y))),
      (R : Subgroup _) = S'.subgroupOf (centralizer ({hc.subA} : Set ↥(h.secSubImg y)) ⊓
        normalizer ((h.subJ y : Subgroup ↥(h.secSubImg y)) : Set ↥(h.secSubImg y))))
    (hSS' : h.subS y ≤ S')
    (h7i : ∀ E : Subgroup ↥(h.secSubImg y), E ≤ S' ⊓ coreActionKernel (h.subJ y) ⊓
        normalizer ((h.subB y : Subgroup ↥(h.secSubImg y)) : Set ↥(h.secSubImg y)) →
      Nat.card (h.subB y) < Nat.card E →
      ∃ L : Subgroup ↥(h.secSubImg y), IsoCorrSub hc.subA (h.subJ y) E L)
    (h7ii : ∀ E : Subgroup ↥(h.secSubImg y), E ≤ S' ⊓ coreActionKernel (h.subJ y) →
      hc.subA ∈ E → ∃ L : Subgroup ↥(h.secSubImg y), IsoCorrSub hc.subA (h.subJ y) E L) :
    Hyp52W ↥(h.secSubImg y) where
  a := hc.subA
  J := h.subJ y
  S := S'
  B := h.subB y
  K := h.subK y
  x := hc.subX
  kProper := kProper_subBar
  kGroup_normalizer := hc.kGroup_normalizer_subB
  normalizer_ne_top := hc.normalizer_subB_ne_top
  orderOf_a := hc.orderOf_subA
  J_le := hc.subJ_le
  isPComponent_J := hc.isPComponent_subJ
  smallType := smallType_subJ
  S_le := hS'le
  S_sylow := hS'syl
  B_le := subB_le.trans (inf_le_inf_right _ hSS')
  B_ne_bot := hc.subB_ne_bot
  a_mem_normalizer := hc.subA_mem_normalizer
  isComponent_bar := hc.isComponent_subBar
  isStandard_bar := hc.isStandard_subBar
  conjClosure_eq := hc.conjClosure_subW
  commutator_eq := hc.commutator_subW
  B_le_kernel := hc.subB_le_kernel
  B_sylow_kernel := hc.subB_sylow_kernel
  isoCorr_of_le_T := h7i
  isoCorr_of_mem := h7ii
  x_mem := hSS' hc.subX_mem
  inf_conjugate_x := hc.subB_inf_conjugate
  x_sq_mem := inf_le_inf_right _ (inf_le_inf_right _ hSS') hc.subX_sq_mem
  sylow_layer := by
    rw [hc.layerIn_subW]
    obtain ⟨R, hR1, hR2, hR3⟩ := hc.sylow_layer_subBar
    exact ⟨R, hR1.trans (inf_le_inf_right _ hSS'), hR2, hR3⟩
  isPComponent_K := hc.isPComponent_subK
  layer_eq_K := hc.layer_eq_subK
  type_K := hc.type_subK

namespace SecCond

theorem isoCorr_of_le_T_sub (hc : h.SecCond y) {S' : Subgroup ↥(h.secSubImg y)}
    (hQ' : S' ⊓ normalizer ((h.subB y : Subgroup ↥(h.secSubImg y)) : Set ↥(h.secSubImg y)) =
      (h.secImage y h.Q).subgroupOf (h.secSubImg y))
    (E : Subgroup ↥(h.secSubImg y))
    (hE : E ≤ S' ⊓ coreActionKernel (h.subJ y) ⊓
      normalizer ((h.subB y : Subgroup ↥(h.secSubImg y)) : Set ↥(h.secSubImg y)))
    (hlt : Nat.card (h.subB y) < Nat.card E) :
    ∃ L : Subgroup ↥(h.secSubImg y), IsoCorrSub hc.subA (h.subJ y) E L := by
  have hET : E ≤ (h.secImage y h.T).subgroupOf (h.secSubImg y) := by
    rw [hc.secImage_T_eq, Sub58.inf_subgroupOf, ← coreActionKernel_subJ, ← hQ']
    refine hE.trans (le_of_eq ?_)
    rw [inf_right_comm]
  have hTP : (h.secImage y h.T).subgroupOf (h.secSubImg y) ≤
      h.subS y ⊓ coreActionKernel (h.subJ y) := by
    rw [hc.subS_inf_coreActionKernel]
    intro z hz
    exact mem_subgroupOf.mpr (secImage_mono (inf_le_right : h.T ≤ h.P) (mem_subgroupOf.mp hz))
  exact hc.isoCorr_subBar E (hET.trans hTP) (Or.inl hlt)

theorem isoCorr_of_mem_sub (hc : h.SecCond y) {S' : Subgroup ↥(h.secSubImg y)}
    (hS'a : S' ≤ centralizer ({hc.subA} : Set ↥(h.secSubImg y))) (hS'2 : IsPGroup 2 S')
    (E : Subgroup ↥(h.secSubImg y)) (hE : E ≤ S' ⊓ coreActionKernel (h.subJ y))
    (haE : hc.subA ∈ E) :
    ∃ L : Subgroup ↥(h.secSubImg y), IsoCorrSub hc.subA (h.subJ y) E L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJc := hc.isPComponent_subJ
  obtain ⟨-, -, hJsub, -, -⟩ := id hJc
  have hJq := ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 (h.subJ y) _
    hc.subJ_le).mp hJc).2.2
  exact ⟨_, Sub58.isoCorrSub_fixedLayer_of_mem hc.subJ_le hJsub hJq
    ((hE.trans inf_le_left).trans hS'a) (hE.trans inf_le_right)
    (hS'2.to_le (hE.trans inf_le_left)) haE⟩

theorem nonempty_quot_equiv_T (hc : h.SecCond y) {T₁ B₁ : Subgroup ↥(h.secSubImg y)}
    [(B₁.subgroupOf T₁).Normal] (hB₁ : B₁ = h.subB y)
    (hT₁ : T₁ = (h.secImage y h.T).subgroupOf (h.secSubImg y)) :
    Nonempty (↥T₁ ⧸ B₁.subgroupOf T₁ ≃* ↥h.T ⧸ h.B.subgroupOf h.T) := by
  have hTH : h.secImage y h.T ≤ h.secSubImg y :=
    (secImage_mono (inf_le_left.trans inf_le_left : h.T ≤ h.S)).trans (h.secImage_S_le y)
  have hTG : h.T ≤ h.secG0 y := hc.T_le_G0
  have hmem : ∀ t : ↥h.T, h.secMk y (inclusion hTG t) ∈ h.secImage y h.T := fun t =>
    mem_map_of_mem _ (show inclusion hTG t ∈ h.T.subgroupOf (h.secG0 y) from t.2)
  let f₀ : ↥h.T →* ↥(h.secSubImg y) :=
    ((h.secMk y).comp (inclusion hTG)).codRestrict _ fun t => hTH (hmem t)
  have hf₀ : ∀ t, f₀ t ∈ T₁ := fun t => by
    rw [hT₁, mem_subgroupOf]
    exact hmem t
  let f : ↥h.T →* ↥T₁ := f₀.codRestrict _ hf₀
  have hf : Function.Surjective f := by
    rintro ⟨z, hz⟩
    rw [hT₁, mem_subgroupOf] at hz
    obtain ⟨t, ht, htz⟩ := mem_map.mp hz
    exact ⟨⟨t, ht⟩, Subtype.ext (Subtype.ext htz)⟩
  refine B5a.nonempty_quotient_equiv_of_surjective f hf fun t => ?_
  rw [hB₁, mem_subgroupOf]
  exact secMk_mem_secImage_iff (h.secB0_le_B y) _

end SecCond

end Hyp52

end CFSG.ComponentClassification.GSThmB
