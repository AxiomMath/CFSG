module

public import CFSG.LocalAnalysis.AGLEmbedding.TwoLocalPair

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type*} [Group G] [Finite G]

theorem exists_mem_normalizer_not_mem_of_lt_of_isPGroup {p : ℕ} [Fact p.Prime]
    {P Q : Subgroup G} (hQ : IsPGroup p Q) (hPQ : P < Q) :
    ∃ x ∈ Q, x ∉ P ∧ x ∈ Subgroup.normalizer (P : Set G) := by
  have : Group.IsNilpotent Q := hQ.isNilpotent
  have hlt : P.subgroupOf Q < ⊤ := by
    refine lt_of_le_of_ne le_top fun htop => hPQ.not_ge fun x hx => ?_
    have hx' : (⟨x, hx⟩ : Q) ∈ P.subgroupOf Q := by
      rw [htop]
      trivial
    exact Subgroup.mem_subgroupOf.mp hx'
  obtain ⟨y, hyN, hyP⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent (G := Q) _ hlt)
  refine ⟨y, y.2, fun h => hyP (Subgroup.mem_subgroupOf.mpr h), ?_⟩
  have hy : y ∈ (Subgroup.normalizer (P : Set G)).subgroupOf Q := by
    rw [Subgroup.subgroupOf_normalizer_eq hPQ.le]
    exact hyN
  exact Subgroup.mem_subgroupOf.mp hy

theorem le_of_two_radical {M S X : Subgroup G} (hSM : S ≤ M)
    (hS : S = pCoreOf 2 (M ⊓ Subgroup.normalizer (S : Set G))) (hXM : X ≤ M)
    (hX : IsPGroup 2 X) (hN : M ⊓ Subgroup.normalizer (S : Set G) ≤
      Subgroup.normalizer (X : Set G)) : X ≤ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let K := M ⊓ Subgroup.normalizer (S : Set G)
  have hS2 : IsPGroup 2 S := hS ▸ CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 K
  have hSK : S ≤ K := _root_.le_inf hSM Subgroup.le_normalizer
  have hSX : S ≤ Subgroup.normalizer (X : Set G) := hSK.trans hN
  have hP2 : IsPGroup 2 (X ⊔ S : Subgroup G) := IsPGroup.to_sup_of_normal_left' hX hS2 hSX
  have hKP : K ≤ Subgroup.normalizer ((X ⊔ S : Subgroup G) : Set G) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_sup X S ⟨hN hg, hg.2⟩
  by_contra hXS
  have hlt : S < X ⊔ S := lt_of_le_of_ne le_sup_right fun heq => hXS (heq ▸ le_sup_left)
  obtain ⟨x, hxP, hxS, hxN⟩ := exists_mem_normalizer_not_mem_of_lt_of_isPGroup hP2 hlt
  have hxK : x ∈ K := ⟨sup_le hXM hSM hxP, hxN⟩
  have hPK : (X ⊔ S) ⊓ K ≤ S := by
    refine (normal_pGroup_le_pCoreOf 2 _ K inf_le_right ?_ (hP2.to_le inf_le_left)).trans
      hS.symm.le
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr fun g hg =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨hKP hg, Subgroup.le_normalizer hg⟩
  exact hxS (hPK ⟨hxP, hxK⟩)

theorem TwoLocalPair.twoCore_M_le {M H : Subgroup G} (h : TwoLocalPair M H)
    (hS : pCoreOf 2 (H ⊓ M) = pCoreOf 2 H) : pCoreOf 2 M ≤ pCoreOf 2 H := by
  refine le_of_two_radical h.twoCore_le ?_ (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 M)
    (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 M)
    (inf_le_left.trans (localGroup_le_normalizer_pCoreOf 2 M))
  rw [h.normalizer_twoCore_H, inf_comm, hS]

namespace D1Escape

variable {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}

theorem normalizer_twoCore_H (h : D1Escape p P M H R) :
    Subgroup.normalizer (pCoreOf 2 H : Set G) = H :=
  h.toTwoLocalPair.normalizer_twoCore_H

theorem normalizer_twoCore_M (h : D1Escape p P M H R) :
    Subgroup.normalizer (pCoreOf 2 M : Set G) = M :=
  h.toTwoLocalPair.normalizer_twoCore_M

theorem twoCore_M_le (h : D1Escape p P M H R) (hS : pCoreOf 2 (H ⊓ M) = pCoreOf 2 H) :
    pCoreOf 2 M ≤ pCoreOf 2 H :=
  h.toTwoLocalPair.twoCore_M_le hS

theorem twoCore_M_ne (h : D1Escape p P M H R) : pCoreOf 2 M ≠ pCoreOf 2 H :=
  h.toTwoLocalPair.twoCore_M_ne

theorem inf_eq_inf_normalizer_twoCore_M (h : D1Escape p P M H R) :
    H ⊓ M = H ⊓ Subgroup.normalizer (pCoreOf 2 M : Set G) :=
  h.toTwoLocalPair.inf_eq_inf_normalizer_twoCore_M

theorem center_twoCore_le_twoCore_M (h : D1Escape p P M H R) (hchar : IsCharTwoType G)
    (hS : pCoreOf 2 (H ⊓ M) = pCoreOf 2 H) :
    (Subgroup.center (pCoreOf 2 H)).map (pCoreOf 2 H).subtype ≤ pCoreOf 2 M := by
  rintro _ ⟨z, hz, rfl⟩
  have hcent : ((z : pCoreOf 2 H) : G) ∈ Subgroup.centralizer (pCoreOf 2 M : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have := Subgroup.mem_center_iff.mp hz ⟨x, h.twoCore_M_le hS hx⟩
    simpa using congrArg Subtype.val this
  exact hchar M h.maxTwoLocal_M.1 ⟨h.twoCore_le z.property, hcent⟩

theorem centralizer_center_twoCore_le (h : D1Escape p P M H R) :
    M ⊓ Subgroup.centralizer
        ((Subgroup.center (pCoreOf 2 H)).map (pCoreOf 2 H).subtype : Set G) ≤ H ⊓ M := by
  intro x hx
  refine ⟨?_, hx.1⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnt : Nontrivial (pCoreOf 2 H) :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr (twoLocal_pCoreOf_ne_bot H h.maxTwoLocal_H.1)
  have hcnt : Nontrivial (Subgroup.center (pCoreOf 2 H)) :=
    (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H).center_nontrivial
  have hne : (Subgroup.center (pCoreOf 2 H)).map (pCoreOf 2 H).subtype ≠ ⊥ := by
    rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ (pCoreOf 2 H).subtype_injective]
    exact (Subgroup.nontrivial_iff_ne_bot _).mp hcnt
  have hchar : (((Subgroup.center (pCoreOf 2 H)).map (pCoreOf 2 H).subtype).subgroupOf
      (pCoreOf 2 H)).Characteristic := by
    rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective
      (pCoreOf 2 H).subtype_injective]
    infer_instance
  have hle := (maxTwoLocal_normalizer_char_eq h.maxTwoLocal_H (Subgroup.map_subtype_le _) hne
    hchar).le
  exact hle (Subgroup.centralizer_le_normalizer _ hx.2)

theorem center_twoCore_le_center_twoCore_M (h : D1Escape p P M H R) (hchar : IsCharTwoType G)
    (hS : pCoreOf 2 (H ⊓ M) = pCoreOf 2 H) :
    (Subgroup.center (pCoreOf 2 H)).map (pCoreOf 2 H).subtype ≤
      (Subgroup.center (pCoreOf 2 M)).map (pCoreOf 2 M).subtype := by
  rintro _ ⟨z, hz, rfl⟩
  have hzQ : (z : G) ∈ pCoreOf 2 M := h.center_twoCore_le_twoCore_M hchar hS ⟨z, hz, rfl⟩
  refine ⟨⟨z, hzQ⟩, Subgroup.mem_center_iff.mpr fun y => Subtype.ext ?_, rfl⟩
  have := Subgroup.mem_center_iff.mp hz ⟨y, h.twoCore_M_le hS y.property⟩
  simpa using congrArg Subtype.val this

theorem centralizer_center_twoCore_M_le (h : D1Escape p P M H R) (hchar : IsCharTwoType G)
    (hS : pCoreOf 2 (H ⊓ M) = pCoreOf 2 H) :
    M ⊓ Subgroup.centralizer
        ((Subgroup.center (pCoreOf 2 M)).map (pCoreOf 2 M).subtype : Set G) ≤ H ⊓ M :=
  fun _ hx => h.centralizer_center_twoCore_le
    ⟨hx.1, Subgroup.centralizer_le (h.center_twoCore_le_center_twoCore_M hchar hS) hx.2⟩

end D1Escape

end CFSG.AGLEmbedding
