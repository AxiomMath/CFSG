module

public import CFSG.LocalAnalysis.EvenBN.U5.LinParts

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.ABGLocalTools (IsSylowOf)
open scoped MatrixGroups

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

theorem sylow_R (hl : d.LinCtx) (k : d.Know12) (c : d.CaseBData) :
    ∃ R : Subgroup G, IsSylowOf 2 R (normalizer (d.D : Set G)) ∧ c.S ≤ R ∧ d.t ∈ R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hd := hl.hyp
  obtain ⟨hSeq, -, hDchar⟩ := k.s9_1 c.S c.S_syl c.P_le_S
  have hES : d.E ≤ c.S := hSeq ▸ le_sup_left
  have hDS : d.D ≤ c.S := hSeq ▸ le_sup_right
  have hSD : c.S ≤ normalizer (d.D : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDS).1 (by haveI := hDchar; infer_instance)
  have htE := hd.t_mem_normalizer_E_caseB hl.gms
  have htD := hd.t_mem_normalizer_D
  have htS : d.t ∈ normalizer (c.S : Set G) := by
    rw [hSeq]
    exact Common.mem_normalizer_sup htE htD
  have htt : d.t * d.t = 1 := by rw [← sq, ← hd.t_two, pow_orderOf_eq_one]
  have hS2 : IsPGroup 2 c.S := c.S_syl.isPGroup
  have hP2 : IsPGroup 2 (c.S ⊔ zpowers d.t : Subgroup G) := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).1 hS2
    have hz : Nat.card (zpowers d.t) = 2 := by rw [Nat.card_zpowers, hd.t_two]
    have hcard := Common.card_sup_mul_card_inf_eq (A := c.S) (B := zpowers d.t)
      (zpowers_le.2 htS)
    have hdvd : Nat.card (c.S ⊔ zpowers d.t : Subgroup G) ∣ 2 ^ (n + 1) := by
      refine Dvd.intro (Nat.card (c.S ⊓ zpowers d.t : Subgroup G)) ?_
      rw [hcard, hn, hz, pow_succ]
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    exact IsPGroup.of_card hm
  have hPN : (c.S ⊔ zpowers d.t : Subgroup G) ≤ normalizer (d.D : Set G) :=
    sup_le hSD (zpowers_le.2 htD)
  have hP2' : IsPGroup 2 ((c.S ⊔ zpowers d.t : Subgroup G).subgroupOf (normalizer (d.D : Set G))) :=
    hP2.comap_subtype
  obtain ⟨Q, hQ⟩ := hP2'.exists_le_sylow
  refine ⟨(Q : Subgroup (normalizer (d.D : Set G))).map (normalizer (d.D : Set G)).subtype,
    ⟨Q, rfl⟩, fun x hx => ?_, ?_⟩
  · exact ⟨⟨x, hSD hx⟩, hQ (mem_subgroupOf.2 (mem_sup_left hx)), rfl⟩
  · exact ⟨⟨d.t, htD⟩, hQ (mem_subgroupOf.2 (mem_sup_right (mem_zpowers _))), rfl⟩

end Data


end CFSG.LocalAnalysis.EvenBN.U5
