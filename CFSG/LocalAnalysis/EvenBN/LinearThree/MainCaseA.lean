module

public import CFSG.LocalAnalysis.EvenBN.LinearThree.MainCaseB
public import CFSG.LocalAnalysis.EvenBN.LinearThree.CaseAThompson
public import CFSG.LocalAnalysis.EvenBN.LinearThree.Excl27G2

public section

namespace CFSG.LocalAnalysis.EvenBN.LinearThree

open Subgroup CFSG.Open CFSG.Blueprint
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.OddStandard.Seitz77
open CFSG.LocalAnalysis.ComponentInitial.FieldFourCover (unipAll)

theorem exists_equiv_radOne {G : Type} [Group G] {S₀ W : Subgroup G} {F : Type} [Field F]
    [Finite F] [CharP F 2] (e₀ : ↥S₀ ≃* ↥(unipAll F)) (hWS : W ≤ S₀) (hWe : IsElemAbelian 2 W)
    (hWc : Nat.card W = Nat.card F ^ 2) :
    ∃ e : ↥S₀ ≃* ↥(unipAll F), ∀ s : S₀, (s : G) ∈ W ↔ e s ∈ radOne F := by
  set E : Subgroup (unipAll F) := (W.subgroupOf S₀).map e₀.toMonoidHom with hE
  have hE2 : ∀ g ∈ E, g * g = 1 := by
    rintro _ ⟨s, hs, rfl⟩
    rw [← map_mul]
    have : s * s = 1 := Subtype.ext (by rw [Subgroup.coe_mul, ← sq]; exact hWe.2 _ hs)
    rw [this, map_one]
  have hEc : Nat.card E = Nat.card F ^ 2 := by
    rw [hE, Subgroup.card_map_of_injective e₀.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWS).toEquiv, hWc]
  have hmem : ∀ s : S₀, (s : G) ∈ W ↔ e₀ s ∈ E := fun s => by
    constructor
    · intro hs
      exact ⟨s, hs, rfl⟩
    · rintro ⟨s', hs', he⟩
      have h1 : s' = s := e₀.injective he
      rw [← h1]
      exact hs'
  rcases eq_radOne_or_radTwo_of_card hE2 hEc with h1 | h1
  · exact ⟨e₀, fun s => by rw [hmem, h1]⟩
  · refine ⟨e₀.trans graphAut, fun s => ?_⟩
    rw [hmem, h1, MulEquiv.trans_apply, graphAut_mem_radOne_iff]

namespace WData

variable {G : Type} [Group G] {A : Subgroup G} {d : Datum A} {Vi : Subgroup G} {q : ℕ}

theorem conj_mem_Ehat (w : WData d Vi q) (L : Subgroup G) {n : G} (hn : n ∈ w.N) {e : G}
    (he : e ∈ w.Ehat L) : n * e * n⁻¹ ∈ w.Ehat L := by
  obtain ⟨heN, heE⟩ := (w.mem_Ehat _).mp he
  refine (w.mem_Ehat _).mpr ⟨mul_mem (mul_mem hn heN) (inv_mem hn), ?_⟩
  have : w.projBar ⟨n * e * n⁻¹, mul_mem (mul_mem hn heN) (inv_mem hn)⟩ =
      w.projBar ⟨n, hn⟩ * w.projBar ⟨e, heN⟩ * (w.projBar ⟨n, hn⟩)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  rw [this]
  exact (inferInstance : (w.Ebar L).Normal).conj_mem _ heE _

end WData

namespace Hyp

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {f : ℕ}

theorem exists_caseAData
    (hf : 3 ≤ f) (d : Datum A) {V₁ V₂ Vi : Subgroup G}
    (hR : Radicals d.V V₁ V₂ (2 ^ f)) (hW : Vi = V₁ ∨ Vi = V₂)
    (hN : normalizer ((Vi ⊔ zpowers d.t : Subgroup G) : Set G) ≤ normalizer (Vi : Set G))
    (w : WData d Vi (2 ^ f)) {K : Type} [Field K] [Finite K] (D : LeviData A Vi K)
    (hKc : Nat.card K = 2 ^ f) (hA : w.CaseA f D.lev.range)
    (hO : ⁅standardComponentOddCore w.Nbar, w.Ebar D.lev.range⁆ = ⊥) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
      Nat.card F = (2 ^ f) ^ 2 ∧ Nonempty (CaseAData d w.W F) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨C₁, -, -, hsyl⟩ := seitz31 hf d hR hW hN w D hKc hA hO
  obtain ⟨-, -, -, w₁, -, S₁, S₀, -, -, hS₁, hS₀, hS₀eq, hS₁eq, hinf, ht, hV⟩ :=
    seitz32 hf d hR hW hN w D hKc hA hO
  obtain ⟨e₀⟩ := hsyl S₀ hS₀
  have hF : Nat.card C₁.F = (2 ^ f) ^ 2 := by rw [C₁.card, pow_mul, ← pow_mul, mul_comm, pow_mul]
  have hWp : IsPGroup 2 w.W := fun x => ⟨1, Subtype.ext (by simpa using w.elem.2 x x.2)⟩
  have hWS₁ : w.W ≤ S₁ := by
    obtain ⟨Q, hQ⟩ := hS₁
    have hn : (w.W.subgroupOf w.N).Normal := Subgroup.normal_in_normalizer
    have hp : IsPGroup 2 (w.W.subgroupOf w.N) := hWp.comap_subtype
    have hle := hp.le_sylow_of_normal Q
    intro x hx
    rw [← hQ]
    exact ⟨⟨x, w.W_le_N hx⟩, hle (mem_subgroupOf.2 hx), rfl⟩
  have hWS₀ : w.W ≤ S₀ := by
    rw [hS₀eq]
    exact le_inf hWS₁ (w.W_le_Ehat _)
  have hWc : Nat.card w.W = Nat.card C₁.F ^ 2 := by rw [w.card, hF]; ring
  obtain ⟨e, he⟩ := exists_equiv_radOne e₀ hWS₀ w.elem hWc
  have hS₁N : S₁ ≤ normalizer (S₀ : Set G) := by
    intro x hx
    refine Subgroup.mem_normalizer_fintype fun s hs => ?_
    rw [hS₀eq] at hs ⊢
    exact Subgroup.mem_inf.2 ⟨S₁.mul_mem (S₁.mul_mem hx (Subgroup.mem_inf.1 hs).1) (S₁.inv_mem hx),
      w.conj_mem_Ehat _ (hS₁.le hx) (Subgroup.mem_inf.1 hs).2⟩
  refine ⟨C₁.F, inferInstance, inferInstance, inferInstance, hF,
    ⟨{ S₁ := S₁, S₀ := S₀, w₁ := w₁, e := e, sylow := hS₁, S₀_le := ?_, S₁_le := hS₁N,
       W_le := hWS₀, sup_eq := hS₁eq, inf_eq := hinf, t_mem := ht, V_le := hV,
       mem_W_iff := he }⟩⟩
  rw [hS₀eq]
  exact inf_le_left

end Hyp

theorem caseAExclusion :
    CaseAExclusion := by
  intro G _ _ A f h d V₁ V₂ Vi hR hW w K _ _ D hKc hA
  obtain ⟨F, _, _, _, hF, ⟨C⟩⟩ := Hyp.exists_caseAData h.three_le d hR hW
    (h.normalizer_adj_le d hR hW) w D hKc hA
    (Hyp.commutator_oddCore_Ebar_of_caseA h.three_le d hR hW (h.normalizer_adj_le d hR hW) w D
      hKc hA)
  have := h.simple
  exact C.false h.nonab h.three_le h.facts.toFusionFacts hR
    (fun _ hVj => h.isSylowOf_centralizer d hR hVj) hW w.elem w.card w.comm_onto hF

section Certified


theorem ctt_bn_psl3_of_exclusions27 (hL3 : LinearThreeExclusion27) (hG23 : G2ThreeExclusion27) :
    ComponentInitial.EvenResidual.BNFamilyStatement
      fun X _ => ∃ f : ℕ, 3 ≤ f ∧ LieModel X .PSL 3 2 f :=
  ctt_bn_psl3_of_exclusions hL3 hG23 caseAExclusion

theorem ctt_bn_psl3_of_G2ThreeExclusion27 (hG23 : G2ThreeExclusion27) :
    ComponentInitial.EvenResidual.BNFamilyStatement
      fun X _ => ∃ f : ℕ, 3 ≤ f ∧ LieModel X .PSL 3 2 f :=
  ctt_bn_psl3_of_exclusions27 linearThreeExclusion27 hG23

theorem ctt_bn_psl3 :
    ComponentInitial.EvenResidual.BNFamilyStatement
      fun X _ => ∃ f : ℕ, 3 ≤ f ∧ LieModel X .PSL 3 2 f :=
  ctt_bn_psl3_of_G2ThreeExclusion27 g2ThreeExclusion27

end Certified

end CFSG.LocalAnalysis.EvenBN.LinearThree
