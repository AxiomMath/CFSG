module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockBasic
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.E1Defs

public section

set_option linter.unusedSectionVars false

namespace CFSG.AGLEmbeddingD2.McLaughlin

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isWeakSBlock_map_conj_of_normalizer {M S L : Subgroup G} (hL : IsWeakSBlock M S L) {t : G}
    (htM : t ∈ M) (htS : t ∈ Subgroup.normalizer (S : Set G)) :
    IsWeakSBlock M S (L.map (MulAut.conj t).toMonoidHom) := by
  refine ⟨hL.toIsTwoPrimeComponent.map_conj htM, fun hle => hL.not_le_normalizer ?_⟩
  intro l hl
  have hlt : t * l * t⁻¹ ∈ Subgroup.normalizer (S : Set G) :=
    hle ⟨l, hl, by simp⟩
  have h1 : t⁻¹ * (t * l * t⁻¹) * t ∈ Subgroup.normalizer (S : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ htS) hlt) htS
  simpa [mul_assoc] using h1

omit [Finite G] in
theorem le_sup_pCoreOf_of_barM_le {M X Y : Subgroup G} (hXM : X ≤ M) (h : barM M X ≤ barM M Y) :
    X ≤ Y ⊔ pCoreOf 2 M := by
  intro x hx
  have hxM : x ∈ M := hXM hx
  have hmem : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨x, hxM⟩ ∈ barM M Y :=
    h (Subgroup.mem_map.mpr ⟨⟨x, hxM⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩)
  obtain ⟨⟨y, hyM⟩, hyY, hxy⟩ := Subgroup.mem_map.mp hmem
  have hyY' : y ∈ Y := Subgroup.mem_subgroupOf.mp hyY
  have hq : (⟨y, hyM⟩ : ↥M)⁻¹ * ⟨x, hxM⟩ ∈ CFSG.pCore 2 ↥M := by
    rw [← QuotientGroup.eq]
    exact hxy
  have hz : y⁻¹ * x ∈ pCoreOf 2 M := by
    have h2 : y⁻¹ * x ∈ (CFSG.pCore 2 ↥M).map M.subtype :=
      ⟨(⟨y, hyM⟩ : ↥M)⁻¹ * ⟨x, hxM⟩, hq, rfl⟩
    assumption
  have : x = y * (y⁻¹ * x) := by group
  rw [this]
  exact Subgroup.mul_mem_sup hyY' hz

@[expose] def trJ (M L₁ L₂ : Subgroup G) : Subgroup G := L₁ ⊔ L₂ ⊔ pCoreOf 2 M

@[expose] def trX (M L₁ L₂ T : Subgroup G) : Subgroup G := trJ M L₁ L₂ ⊔ T

section Setup

variable {M H : Subgroup G} {L₁ L₂ T : Subgroup G}

omit [Finite G] in
theorem le_trJ_left : L₁ ≤ trJ M L₁ L₂ := le_sup_left.trans le_sup_left
omit [Finite G] in
theorem le_trJ_right : L₂ ≤ trJ M L₁ L₂ := le_sup_right.trans le_sup_left
omit [Finite G] in
theorem pCoreOf_le_trJ : pCoreOf 2 M ≤ trJ M L₁ L₂ := le_sup_right

theorem normalizes_trJ (h₁ : IsWeakSBlock M (pCoreOf 2 H) L₁) (h₂ : IsWeakSBlock M (pCoreOf 2 H) L₂)
    (hk2 : ∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' →
      barM M L' = barM M L₁ ∨ barM M L' = barM M L₂)
    (hTM : T ≤ M) (hTS : T ≤ Subgroup.normalizer (pCoreOf 2 H : Set G)) :
    ∀ t ∈ T, ∀ j ∈ trJ M L₁ L₂, t * j * t⁻¹ ∈ trJ M L₁ L₂ := by
  intro t ht
  have hle : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      L.map (MulAut.conj t).toMonoidHom ≤ trJ M L₁ L₂ := by
    intro L hL
    have hL' := isWeakSBlock_map_conj_of_normalizer hL (hTM ht) (hTS ht)
    rcases hk2 _ hL' with h | h
    · exact (le_sup_pCoreOf_of_barM_le hL'.le h.le).trans
        (sup_le (le_trJ_left) pCoreOf_le_trJ)
    · exact (le_sup_pCoreOf_of_barM_le hL'.le h.le).trans
        (sup_le (le_trJ_right) pCoreOf_le_trJ)
  have hO : (pCoreOf 2 M).map (MulAut.conj t).toMonoidHom ≤ trJ M L₁ L₂ := by
    rintro _ ⟨x, hx, rfl⟩
    refine pCoreOf_le_trJ ?_
    have := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M (hTM ht)
    exact (Subgroup.mem_normalizer_iff.mp this x).mp hx
  have hmap : (trJ M L₁ L₂).map (MulAut.conj t).toMonoidHom ≤ trJ M L₁ L₂ := by
    unfold trJ
    rw [Subgroup.map_sup, Subgroup.map_sup]
    exact sup_le (sup_le (hle L₁ h₁) (hle L₂ h₂)) hO
  intro j hj
  exact hmap ⟨j, hj, by simp⟩

theorem trX_le (hL₁ : L₁ ≤ M) (hL₂ : L₂ ≤ M) (hT : T ≤ M) : trX M L₁ L₂ T ≤ M :=
  sup_le (sup_le (sup_le hL₁ hL₂) (pCoreOf_le 2 M)) hT

omit [Finite G] in
theorem le_trX_left : trJ M L₁ L₂ ≤ trX M L₁ L₂ T := le_sup_left
omit [Finite G] in
theorem le_trX_right : T ≤ trX M L₁ L₂ T := le_sup_right

theorem exists_mul_of_mem_trX
    (hN : ∀ t ∈ T, ∀ j ∈ trJ M L₁ L₂, t * j * t⁻¹ ∈ trJ M L₁ L₂) {x : G}
    (hx : x ∈ trX M L₁ L₂ T) : ∃ t ∈ T, ∃ j ∈ trJ M L₁ L₂, x = t * j := by
  have hle : T ≤ Subgroup.normalizer (trJ M L₁ L₂ : Set G) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro j
    refine ⟨fun hj => hN t ht j hj, fun hj => ?_⟩
    have := hN t⁻¹ (T.inv_mem ht) _ hj
    simpa [mul_assoc] using this
  have h := Subgroup.coe_mul_of_left_le_normalizer_right T (trJ M L₁ L₂) hle
  rw [trX, sup_comm, ← SetLike.mem_coe, h] at hx
  obtain ⟨t, ht, j, hj, rfl⟩ := hx
  exact ⟨t, ht, j, hj, rfl⟩

omit [Finite G] in
theorem pCoreOf_le_pCoreOf_of_le {M X : Subgroup G} (hQX : pCoreOf 2 M ≤ X) (hXM : X ≤ M) :
    pCoreOf 2 M ≤ pCoreOf 2 X := by
  refine CFSG.PreuniquenessRankFour.Helpers.normal_pSubgroup_le_pCoreOf 2 hQX ?_
    (pCoreOf_isPGroup 2 M)
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hQX]
  exact hXM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M)

omit [Finite G] in
theorem charTwo_top_of_le {M X : Subgroup G} (hM : CharTwo M) (hQX : pCoreOf 2 M ≤ X)
    (hXM : X ≤ M) : CharTwo (⊤ : Subgroup ↥X) := by
  have hle := pCoreOf_le_pCoreOf_of_le hQX hXM
  have hcore : pCoreOf 2 (⊤ : Subgroup ↥X) = (pCoreOf 2 X).subgroupOf X := by
    rw [← Subgroup.subgroupOf_self (H := X)]
    exact (CFSG.RankThreeEvenClassification.Helpers.pCoreOf_subgroupOf 2 X X le_rfl).symm
  intro c hc
  rw [hcore]
  have hcC : c ∈ Subgroup.centralizer (((pCoreOf 2 X).subgroupOf X : Subgroup ↥X) : Set ↥X) := by
    have := hc.2
    rwa [hcore] at this
  have hcM : (c : G) ∈ M ⊓ Subgroup.centralizer (pCoreOf 2 M : Set G) := by
    refine ⟨hXM c.2, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro q hq
    have hqX : q ∈ pCoreOf 2 X := hle hq
    have := Subgroup.mem_centralizer_iff.mp hcC ⟨q, pCoreOf_le 2 X hqX⟩
      (Subgroup.mem_subgroupOf.mpr hqX)
    exact congrArg Subtype.val this
  exact Subgroup.mem_subgroupOf.mpr (hle (hM hcM))

end Setup

end CFSG.AGLEmbeddingD2.McLaughlin
