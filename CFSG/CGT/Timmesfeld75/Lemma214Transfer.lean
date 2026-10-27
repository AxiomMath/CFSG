module

public import CFSG.CGT.Timmesfeld75.Inputs214
import CFSG.GroupTheory.PCore.Transport
public import CFSG.CGT.Timmesfeld75.Config214
public import CFSG.CGT.Timmesfeld75.Targets

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped MatrixGroups

variable {G : Type*} [Group G]

section SubgroupOf

theorem normIn_subgroupOf_eq {S U X : Subgroup G} (hU : U ≤ X) :
    normIn (S.subgroupOf X) (U.subgroupOf X) = (normIn S U).subgroupOf X := by
  rw [normIn, normIn, ← Subgroup.subgroupOf_normalizer_eq hU]
  exact (Subgroup.comap_inf _ _ _).symm

theorem cfgM_subgroupOf_eq {T T₁ X : Subgroup G} (hT : T ≤ X) (hT₁ : T₁ ≤ X) :
    cfgM (T.subgroupOf X) (T₁.subgroupOf X) = (cfgM T T₁).subgroupOf X := by
  rw [cfgM, cfgM, normIn_subgroupOf_eq hT₁, normIn_subgroupOf_eq hT,
    Subgroup.subgroupOf_sup ((normIn_le T T₁).trans hT) ((normIn_le T₁ T).trans hT₁)]

theorem cfgM_le_of_le {T T₁ X : Subgroup G} (hT : T ≤ X) (hT₁ : T₁ ≤ X) : cfgM T T₁ ≤ X :=
  sup_le ((normIn_le T T₁).trans hT) ((normIn_le T₁ T).trans hT₁)

theorem subgroupOf_ne_bot_of_le {A X : Subgroup G} (hAX : A ≤ X) (hA : A ≠ ⊥) :
    A.subgroupOf X ≠ ⊥ := fun h =>
  hA (by rw [← Subgroup.map_subgroupOf_eq_of_le hAX, h, Subgroup.map_bot])

theorem Cfg.subgroupOf_of_le {T T₁ X : Subgroup G} (c : Cfg T T₁) (hT : T ≤ X) (hT₁ : T₁ ≤ X) :
    Cfg (T.subgroupOf X) (T₁.subgroupOf X) where
  wc := isWC_subgroupOf c.wc X hT
  wc₁ := isWC_subgroupOf c.wc₁ X hT₁
  inf := by
    have h : (T ⊓ T₁).subgroupOf X = T.subgroupOf X ⊓ T₁.subgroupOf X :=
      Subgroup.comap_inf _ _ _
    rw [← h, c.inf, Subgroup.bot_subgroupOf]
  ne := by
    rw [normIn_subgroupOf_eq hT₁]
    exact subgroupOf_ne_bot_of_le ((normIn_le _ _).trans hT) c.ne
  ne₁ := by
    rw [normIn_subgroupOf_eq hT]
    exact subgroupOf_ne_bot_of_le ((normIn_le _ _).trans hT₁) c.ne₁

end SubgroupOf

section Quotient

theorem nonempty_mulEquiv_quotient_of_eq {Y P : Type*} [Group Y] [Group P] {A B : Subgroup Y}
    [A.Normal] [B.Normal] (h : A = B) : Nonempty (Y ⧸ A ≃* P) → Nonempty (Y ⧸ B ≃* P) :=
  fun ⟨e⟩ => ⟨(QuotientGroup.quotientMulEquivOfEq h).symm.trans e⟩

@[expose] def IsLemma214Quotient {Y : Type} [Group Y] (A : Subgroup Y) : Prop :=
  ∃ _ : A.Normal,
    (∃ f : ℕ, 2 ≤ f ∧ Nonempty (Y ⧸ A ≃* PSL(2, GaloisField 2 f))) ∨
    (∃ a : ℕ, 1 ≤ a ∧ Nonempty (Y ⧸ A ≃* Sz a)) ∨
    (∃ n : ℕ, Odd n ∧ 3 ≤ n ∧ Nonempty (Y ⧸ A ≃* DihedralGroup n))

theorem IsLemma214Quotient.of_eq {Y : Type} [Group Y] {A B : Subgroup Y} (h : A = B)
    (hA : IsLemma214Quotient A) : IsLemma214Quotient B := by
  obtain ⟨hAn, hcases⟩ := hA
  have hBn : B.Normal := h ▸ hAn
  refine ⟨hBn, ?_⟩
  rcases hcases with ⟨f, hf, he⟩ | ⟨a, ha, he⟩ | ⟨n, hn, hn3, he⟩
  · exact Or.inl ⟨f, hf, nonempty_mulEquiv_quotient_of_eq h he⟩
  · exact Or.inr (Or.inl ⟨a, ha, nonempty_mulEquiv_quotient_of_eq h he⟩)
  · exact Or.inr (Or.inr ⟨n, hn, hn3, nonempty_mulEquiv_quotient_of_eq h he⟩)

end Quotient

theorem lemma214_openPCore_eq_pCore (p : ℕ) (Y : Type*) [Group Y] :
    CFSG.Open.pCore p Y = CFSG.pCore p Y := CFSG.Open.pCore_eq_pCore p Y

theorem lemma214_of_core_of_cfg (h : Core214) {G : Type} [Group G] [Finite G]
    {T T₁ X : Subgroup G} (c : Cfg T T₁) (hTX : T ≤ X) (hT₁X : T₁ ≤ X) (hX : T ⊔ T₁ = X)
    (hconjx : ∃ x ∈ X, T₁ = conjSubgroup x T) :
    cfgM T T₁ = pCoreOf 2 X ∧ IsLemma214Quotient ((cfgM T T₁).subgroupOf X) := by
  obtain ⟨x, hxX, hx⟩ := hconjx
  have htop : T.subgroupOf X ⊔ T₁.subgroupOf X = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hTX hT₁X, hX, Subgroup.subgroupOf_self]
  have hconj : ∃ y : X, T₁.subgroupOf X = conjSubgroup y (T.subgroupOf X) :=
    ⟨⟨x, hxX⟩, by rw [conjSubgroup_subgroupOf, ← hx]⟩
  obtain ⟨hcore, hquot⟩ := h X (T.subgroupOf X) (T₁.subgroupOf X)
    (c.subgroupOf_of_le hTX hT₁X) htop hconj
  have hM : cfgM (T.subgroupOf X) (T₁.subgroupOf X) = (cfgM T T₁).subgroupOf X :=
    cfgM_subgroupOf_eq hTX hT₁X
  refine ⟨?_, IsLemma214Quotient.of_eq hM hquot⟩
  have hcore' : CFSG.Open.pCore 2 X = (cfgM T T₁).subgroupOf X :=
    (lemma214_openPCore_eq_pCore 2 X).trans (hcore.symm.trans hM)
  rw [pCoreOf, hcore', Subgroup.map_subgroupOf_eq_of_le (cfgM_le_of_le hTX hT₁X)]

theorem lemma214_of_core (h : Core214) : Lemma214 := by
  intro G _ _ T hT g hne hL
  obtain ⟨x, hxX, hx⟩ := exists_mem_conj_eq_of_le hT
    (le_sup_left : T ≤ T ⊔ conjSubgroup g T) le_sup_right
  exact lemma214_of_core_of_cfg h (Cfg.of_conj hT hne hL) le_sup_left le_sup_right rfl
    ⟨x, hxX, hx⟩

end CFSG.CGT.Timmesfeld75
