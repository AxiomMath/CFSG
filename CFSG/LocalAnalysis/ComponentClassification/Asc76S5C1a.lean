module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76S5HypII
public import CFSG.LocalAnalysis.ComponentClassification.Asc76S5Elem

public section

namespace CFSG.ComponentClassification.Asc76.Sec5

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.AschbacherTheorem3

variable {G : Type} [Group G] [Finite G]

structure Overlap (A R : Subgroup G) (g : G) (T : Subgroup G) : Prop where
  standard : standardComponentIsStandard A
  not_mem : g ∉ normalizer (A : Set G)
  sylow : IsSylowOf 2 T (rightConjugate (centralizer (A : Set G)) g ⊓ normalizer (A : Set G))
  ne_bot : T ≠ ⊥
  sylowR : IsSylowOf 2 R (centralizer (A : Set G))
  normalizesR : T ≤ normalizer (R : Set G)

namespace Overlap

variable {A R T : Subgroup G} {g : G}

omit [Finite G] in
theorem tight (h : Overlap A R g T) : TightlyEmbedded (centralizer (A : Set G)) :=
  tightlyEmbedded_centralizer h.standard

omit [Finite G] in
theorem not_mem_K (h : Overlap A R g T) :
    g ∉ normalizer (centralizer (A : Set G) : Set G) := by
  rw [normalizer_centralizer_eq h.standard]
  exact h.not_mem

omit [Finite G] in
theorem sylowK (h : Overlap A R g T) :
    IsSylowOf 2 T (rightConjugate (centralizer (A : Set G)) g ⊓
      normalizer (centralizer (A : Set G) : Set G)) := by
  rw [normalizer_centralizer_eq h.standard]
  exact h.sylow

theorem inf_eq_bot (h : Overlap A R g T) : R ⊓ T = ⊥ := by
  refine two_subgroup_of_odd_eq_bot _ _ (h.sylowR.isPGroup.to_inf_left) (h.tight.2 g h.not_mem_K)
    (inf_le_inf h.sylowR.le (h.sylow.le.trans inf_le_left))

theorem inf_normalizer_eq (h : Overlap A R g T) :
    R ⊓ normalizer (T : Set G) = R ⊓ centralizer (T : Set G) :=
  inf_normalizer_eq_inf_centralizer h.normalizesR h.inf_eq_bot

theorem mulEquiv (h : Overlap A R g T) : Nonempty (↥(R ⊓ centralizer (T : Set G)) ≃* T) :=
  inf_centralizer_mulEquiv_of_tightlyEmbedded h.tight h.not_mem_K h.sylowK h.ne_bot h.sylowR
    h.normalizesR

theorem card_inf_centralizer (h : Overlap A R g T) :
    Nat.card (R ⊓ centralizer (T : Set G) : Subgroup G) = Nat.card T := by
  obtain ⟨e⟩ := h.mulEquiv
  exact Nat.card_congr e.toEquiv

theorem card_lt (h : Overlap A R g T)
    (hnot : ¬ IsSylowOf 2 T (rightConjugate (centralizer (A : Set G)) g)) :
    Nat.card T < Nat.card R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := exists_isSylowOf 2 (rightConjugate (centralizer (A : Set G)) g)
  have hTS : Nat.card T ≤ Nat.card S :=
    Sec5.card_le_of_isSylowOf hS (h.sylow.le.trans inf_le_left) h.sylow.isPGroup
  have hSR : Nat.card S = Nat.card R := by rw [hS.card_eq, h.sylowR.card_eq, rightConjugate_card]
  refine lt_of_le_of_ne (hSR ▸ hTS) fun heq => hnot ?_
  refine isSylowOf_of_card (h.sylow.le.trans inf_le_left) ?_
  rw [heq, h.sylowR.card_eq, rightConjugate_card]

theorem one_lt_pRank_rightConjugate {K : Subgroup G} (hm : 1 < Open.pRank 2 K) (g : G) :
    1 < Open.pRank 2 (rightConjugate K g) := by
  obtain ⟨E, hEK, hE, hE4⟩ := Asc76X.exists_fourGroup_le hm
  exact Asc76X.one_lt_pRank_of_fourGroup (rightConjugate_le_rightConjugate hEK g)
    (Asc76X.isElemAbelian_rightConjugate hE g) (by rw [rightConjugate_card, hE4])

variable (h22 : Asc76Lemma22)

theorem lemma22_hyps (h : Overlap A R g T) (hm : 1 < Open.pRank 2 (centralizer (A : Set G))) :
    TightlyEmbedded (centralizer (A : Set G)) ∧
      TightlyEmbedded (rightConjugate (centralizer (A : Set G)) g) ∧
      Odd (Nat.card (centralizer (A : Set G) ⊓ rightConjugate (centralizer (A : Set G)) g :
        Subgroup G)) ∧
      (Nat.card (centralizer (A : Set G))).factorization 2 =
        (Nat.card (rightConjugate (centralizer (A : Set G)) g)).factorization 2 ∧
      1 < Open.pRank 2 (rightConjugate (centralizer (A : Set G)) g) :=
  ⟨h.tight, tightlyEmbedded_rightConjugate h.tight g, h.tight.2 g h.not_mem_K,
    by rw [rightConjugate_card], one_lt_pRank_rightConjugate hm g⟩

include h22 in
theorem isMulCommutative (h : Overlap A R g T) (hm : 1 < Open.pRank 2 (centralizer (A : Set G)))
    (hnot : ¬ IsSylowOf 2 T (rightConjugate (centralizer (A : Set G)) g)) : IsMulCommutative T := by
  obtain ⟨hK, hKg, hodd, hfac, hmg⟩ := h.lemma22_hyps hm
  obtain ⟨-, -, -, -, h5, -, -⟩ :=
    h22 G _ _ T R hK hKg hodd hfac h.sylowK h.ne_bot h.sylowR h.normalizesR hm hmg
  exact h5 hnot

include h22 in
theorem ne_weakClosure (h : Overlap A R g T) (hm : 1 < Open.pRank 2 (centralizer (A : Set G)))
    (hnot : ¬ IsSylowOf 2 T (rightConjugate (centralizer (A : Set G)) g)) :
    T ≠ ⨆ (k : G) (_ : k ∈ centralizer (A : Set G)) (_ : rightConjugate T k ≤ R ⊔ T),
      rightConjugate T k := by
  obtain ⟨hK, hKg, hodd, hfac, hmg⟩ := h.lemma22_hyps hm
  obtain ⟨⟨h1, -⟩, -, -, -, -, -, -⟩ :=
    h22 G _ _ T R hK hKg hodd hfac h.sylowK h.ne_bot h.sylowR h.normalizesR hm hmg
  intro hTW
  have hW : ∀ k ∈ centralizer (A : Set G), rightConjugate T k ≤ R ⊔ T →
      rightConjugate T k = T := by
    intro k hk hle
    have h' : rightConjugate T k ≤ T := by
      refine le_trans ?_ hTW.symm.le
      exact le_iSup_of_le k (le_iSup_of_le hk (le_iSup_of_le hle le_rfl))
    exact eq_of_le_of_card_ge h' (by rw [rightConjugate_card])
  have hN := le_normalizer_of_weaklyClosed h.sylowR.le h.sylowR.isPGroup h.sylow.isPGroup
    (h.sylowK.le.trans inf_le_right) h.normalizesR hW
  have hRN : R ⊓ normalizer (T : Set G) = R := inf_eq_left.mpr (le_sup_left.trans hN)
  have h1' : Nat.card R = Nat.card T := by
    have := h1
    rwa [hRN] at this
  exact (h.card_lt hnot).ne h1'.symm

include h22 in
theorem not_isCyclic (h : Overlap A R g T) (hm : 1 < Open.pRank 2 (centralizer (A : Set G)))
    (hRd : ¬ IsDihedralTwoGroup R)
    (hnot : ¬ IsSylowOf 2 T (rightConjugate (centralizer (A : Set G)) g)) : ¬ IsCyclic T := by
  obtain ⟨hK, hKg, hodd, hfac, hmg⟩ := h.lemma22_hyps hm
  obtain ⟨-, h2, -, -, -, -, -⟩ :=
    h22 G _ _ T R hK hKg hodd hfac h.sylowK h.ne_bot h.sylowR h.normalizesR hm hmg
  exact fun hc => hRd (h2 (h.ne_weakClosure h22 hm hnot) hc).1

include h22 in
theorem four_le_card_omegaOne (h : Overlap A R g T)
    (hm : 1 < Open.pRank 2 (centralizer (A : Set G))) (hRd : ¬ IsDihedralTwoGroup R)
    (hnot : ¬ IsSylowOf 2 T (rightConjugate (centralizer (A : Set G)) g)) :
    4 ≤ Nat.card (omegaOne T) := by
  have hTc := h.isMulCommutative h22 hm hnot
  by_contra hlt
  apply h.not_isCyclic h22 hm hRd hnot
  refine isCyclic_of_pRank_le_one h.sylow.isPGroup hTc fun hr => hlt ?_
  obtain ⟨E, hET, hE, hE4⟩ := Asc76X.exists_fourGroup_le hr
  rw [← hE4]
  exact card_le_of_le fun x hx => mem_omegaOne (hET hx) (hE.2 x hx)

include h22 in
theorem not_isElemAbelian (h75 : Asc75Theorem4) (hII : Asc76HypII A) (h : Overlap A R g T)
    (hm : 1 < Open.pRank 2 (centralizer (A : Set G))) (hRd : ¬ IsDihedralTwoGroup R)
    (hnot : ¬ IsSylowOf 2 T (rightConjugate (centralizer (A : Set G)) g)) :
    ¬ IsElemAbelian 2 T := by
  intro hTe
  obtain ⟨hK, hKg, hodd, hfac, hmg⟩ := h.lemma22_hyps hm
  obtain ⟨-, -, -, -, -, -, h7⟩ :=
    h22 G _ _ T R hK hKg hodd hfac h.sylowK h.ne_bot h.sylowR h.normalizesR hm hmg
  have hTc := h.isMulCommutative h22 hm hnot
  have hU := omegaOne_le_sup_centralizer h75 h.standard hII h.not_mem h.sylow h.ne_bot hTc
    (h.four_le_card_omegaOne h22 hm hRd hnot)
  have hTU : T ≤ omegaOne T := le_omegaOne hTe.2
  have hCn : ((R ⊓ centralizer (T : Set G)).subgroupOf R).Normal := by
    rw [← h.inf_normalizer_eq]
    exact h7
  exact hnot (isSylowOf_of_le_sup_centralizer h.tight h.not_mem_K h.sylowK h.ne_bot h.sylowR
    h.normalizesR (hTU.trans hU) hCn)

end Overlap

end CFSG.ComponentClassification.Asc76.Sec5
