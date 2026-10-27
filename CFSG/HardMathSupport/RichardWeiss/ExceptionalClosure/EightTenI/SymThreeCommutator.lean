module

public import CFSG.HardMathSupport.Cooperstein.StructureLie.ShortCommutator
public import CFSG.HardMathSupport.Cooperstein.Coordinator.Star

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure

open CFSG.AGLEmbedding (Asc81bHyp IsWeakSBlock blockV)
open CFSG.Open (pCoreOf)
open CFSG.HardMathSupport.Cooperstein.Coordinator
open CFSG.HardMathSupport.Cooperstein.Proving (barMHomSub barMHomSub_surjective ker_barMHomSub)
open CFSG.HardMathSupport.Cooperstein.StructureLie
open CFSG.QuasithinUnique CFSG.Quasithin
open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem commutator_pCore_le_blockV_of_elt
    {X S L : Subgroup G} (hX : CFSG.Open.IsKGroup ↥X) (hA : Asc81bHyp X S)
    (hL : IsWeakSBlock X S L) (hcen : Subgroup.center ↥(CFSG.AGLEmbedding.barM X L) = ⊥)
    {y : G} (hyL : y ∈ L) {k : ℕ} (hyQ : y ^ 2 ^ k ∉ pCoreOf 2 (L ⊔ S))
    (hk : ∀ q ∈ pCoreOf 2 (L ⊔ S), ⁅q, y ^ 2 ^ k⁆ ∈ blockV S L) :
    ⁅pCoreOf 2 (L ⊔ S), L⁆ ≤ blockV S L := by
  have hSL := le_normalizer_of_isWeakSBlock hX hA hL
  set M : Subgroup G := L ⊔ S with hMdef
  set V : Subgroup G := blockV S L with hVdef
  set Q : Subgroup G := pCoreOf 2 M with hQdef
  have hMV : M ≤ normalizer (V : Set G) := sup_le_normalizer_blockV S L
  have hMQ : M ≤ normalizer (Q : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 M
  have hQS : Q ≤ S := twoCore_sup_le hA hL hSL
  have hSM : S ≤ M := le_sup_right
  have hQM : Q ≤ M := hQS.trans hSM
  have hQ2 : IsPGroup 2 Q := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 M
  have hLM : L ≤ M := le_sup_left
  have hyM : y ^ 2 ^ k ∈ M := M.pow_mem (hLM hyL) _
  have hTn : M ≤ normalizer ((commKer' M Q V hMV : Subgroup G) : Set G) := by
    apply TransvIrr.le_normalizer_of_conj_mem
    rintro m hm g ⟨hg, hg'⟩
    refine ⟨M.mul_mem (M.mul_mem hm hg) (M.inv_mem hm), fun w hw => ?_⟩
    have e : ⁅w, m * g * m⁻¹⁆ = m * ⁅m⁻¹ * w * m⁻¹⁻¹, g⁆ * m⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    have := hg' (m⁻¹ * w * m⁻¹⁻¹) (TransvIrr.conj_mem_of_le_normalizer hMQ (M.inv_mem hm) hw)
    exact TransvIrr.conj_mem_of_le_normalizer hMV hm this
  set T : Subgroup G := commKer' M Q V hMV with hTdef
  have hTM : T ≤ M := fun g hg => hg.1
  have hyT : y ^ 2 ^ k ∈ T := ⟨hyM, hk⟩
  have hXM : M ≤ X := sup_le hL.le hA.twoRadical.1
  have hOQM : pCoreOf 2 X ≤ M := hA.twoCore_le.trans le_sup_right
  have hOQ : pCoreOf 2 X ≤ Q :=
    CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 _ _ hOQM
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hOQM).mpr
        (hXM.trans (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 X)))
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 X)
  have hLP : L ≤ T ⊔ Q := by
    set P₀ : Subgroup G := T ⊔ Q with hP₀def
    have hP₀n : M ≤ normalizer (P₀ : Set G) := fun g hg =>
      inf_normalizer_le_normalizer_sup _ _ ⟨hTn hg, hMQ hg⟩
    let hbar := barMHomSub (X := X) (L := L) hL.le
    have hq := hL.component.2.2
    have hP₀Ln : (((P₀ ⊓ L).subgroupOf L)).Normal := by
      refine ⟨fun n hn g => ?_⟩
      have hn' : (n : G) ∈ P₀ ⊓ L := hn
      show ((g * n * g⁻¹ : ↥L) : G) ∈ P₀ ⊓ L
      refine ⟨?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp (hP₀n (hLM g.2)) (n : G)).mp hn'.1
      · exact L.mul_mem (L.mul_mem g.2 hn'.2) (L.inv_mem g.2)
    have hN₁ : (((P₀ ⊓ L).subgroupOf L).map hbar).Normal :=
      hP₀Ln.map hbar (barMHomSub_surjective hL.le)
    rcases CFSG.HardMathSupport.Cooperstein.Coordinator.StarAux.normal_le_center_or_eq_top
      hq.1 hq.2 _ hN₁ with hc | htop
    · exfalso
      have hyP : y ^ 2 ^ k ∈ P₀ := Subgroup.mem_sup_left hyT
      have hyL' : y ^ 2 ^ k ∈ L := L.pow_mem hyL _
      have hmem : hbar ⟨y ^ 2 ^ k, hyL'⟩ ∈ ((P₀ ⊓ L).subgroupOf L).map hbar :=
        ⟨⟨y ^ 2 ^ k, hyL'⟩, Subgroup.mem_subgroupOf.mpr ⟨hyP, hyL'⟩, rfl⟩
      have h1 := hc hmem
      rw [hcen, Subgroup.mem_bot] at h1
      have hker : (⟨y ^ 2 ^ k, hyL'⟩ : ↥L) ∈ hbar.ker := h1
      rw [ker_barMHomSub hL.le, Subgroup.mem_subgroupOf] at hker
      exact hyQ (hOQ hker)
    · intro l₂ hl₂
      have hmem : hbar ⟨l₂, hl₂⟩ ∈ ((P₀ ⊓ L).subgroupOf L).map hbar := by
        rw [htop]; trivial
      obtain ⟨p, hp, hpe⟩ := hmem
      have hker : p⁻¹ * ⟨l₂, hl₂⟩ ∈ hbar.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hpe, inv_mul_cancel]
      rw [ker_barMHomSub hL.le, Subgroup.mem_subgroupOf] at hker
      have hpP : (p : G) ∈ P₀ := (Subgroup.mem_subgroupOf.mp hp).1
      have h1 : (p : G)⁻¹ * l₂ ∈ Q := hOQ hker
      have e : l₂ = (p : G) * ((p : G)⁻¹ * l₂) := by group
      rw [e]
      exact P₀.mul_mem hpP (Subgroup.mem_sup_right h1)
  have hLT : L ≤ T := by
    have hTn' : (T.subgroupOf M).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hTM).mpr hTn
    let ψ : ↥M →* ↥M ⧸ T.subgroupOf M := QuotientGroup.mk' (T.subgroupOf M)
    have hLm : ⁅L.subgroupOf M, L.subgroupOf M⁆ = L.subgroupOf M := by
      apply Subgroup.map_injective M.subtype_injective
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hLM, hL.perfect]
    have hQ2' : IsPGroup 2 ((Q.subgroupOf M).map ψ) :=
      (hQ2.of_equiv (Subgroup.subgroupOfEquivOfLe hQM).symm).map ψ
    have hPle : (L.subgroupOf M).map ψ ≤ (Q.subgroupOf M).map ψ := by
      rintro _ ⟨l₂, hl₂, rfl⟩
      have hl₂' : (l₂ : G) ∈ T ⊔ Q := hLP (Subgroup.mem_subgroupOf.mp hl₂)
      obtain ⟨t, ht, q, hq, hlt⟩ :=
        CFSG.Quasithin.F53Push.mem_sup_of_le_normalizer (N := T) (K := Q)
          (hQM.trans hTn) hl₂'
      refine ⟨⟨q, hQM hq⟩, Subgroup.mem_subgroupOf.mpr hq, ?_⟩
      have h1 : l₂ = ⟨t, hTM ht⟩ * ⟨q, hQM hq⟩ := Subtype.ext hlt
      have h2 : ψ ⟨t, hTM ht⟩ = 1 := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact Subgroup.mem_subgroupOf.mpr ht
      rw [h1, map_mul, h2, one_mul]
    have hPperf : ⁅(L.subgroupOf M).map ψ, (L.subgroupOf M).map ψ⁆ = (L.subgroupOf M).map ψ := by
      rw [← Subgroup.map_commutator, hLm]
    have hPbot := ShortComm.eq_bot_of_perfect_of_isPGroup hPperf (hQ2'.to_le hPle)
    intro l₂ hl₂
    have h1 : ψ ⟨l₂, hLM hl₂⟩ ∈ (L.subgroupOf M).map ψ :=
      ⟨⟨l₂, hLM hl₂⟩, Subgroup.mem_subgroupOf.mpr hl₂, rfl⟩
    rw [hPbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact Subgroup.mem_subgroupOf.mp h1
  refine Subgroup.commutator_le.mpr fun q hq l₂ hl₂ => ?_
  exact (hLT hl₂).2 q hq

end CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure

end
