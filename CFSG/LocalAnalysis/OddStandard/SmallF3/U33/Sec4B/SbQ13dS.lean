module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13b0

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

theorem q13d_exists_cover (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    ∃ 𝒮 : Subgroup G, IsPGroup 2 𝒮 ∧ ctxU t tau x₁ x₂ lam ≤ 𝒮 ∧
      NormalIn (ctxU t tau x₁ x₂ lam) 𝒮 ∧ Nat.card ↥𝒮 = 2 ^ 11 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU2 : IsPGroup 2 (ctxU t tau x₁ x₂ lam) := q13b_isPGroup_U h
  obtain ⟨P, hUP⟩ := hU2.exists_le_sylow
  have hcardG : Nat.card G ≠ 0 := Nat.card_pos.ne'
  have hfac : 11 ≤ Nat.factorization (Nat.card G) 2 :=
    (Nat.prime_two.pow_dvd_iff_le_factorization hcardG).mp h.glob.dvd
  have hcardP : Nat.card P = 2 ^ Nat.factorization (Nat.card G) 2 :=
    Sylow.card_eq_multiplicity P
  have hUcard : Nat.card ↥(ctxU t tau x₁ x₂ lam) = 2 ^ 10 := q13b_card_U h
  have hcardlt : Nat.card ↥(ctxU t tau x₁ x₂ lam) < Nat.card P := by
    rw [hUcard, hcardP]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hltUP : ctxU t tau x₁ x₂ lam < P := by
    refine lt_of_le_of_ne hUP ?_
    intro heq
    rw [heq] at hcardlt
    exact absurd hcardlt (lt_irrefl _)
  haveI : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
  let s : Set (Subgroup G) := {K | ctxU t tau x₁ x₂ lam < K ∧ K ≤ P}
  have hsne : s.Nonempty := ⟨P, hltUP, le_rfl⟩
  obtain ⟨𝒮, hSmem, hmin⟩ := (Set.toFinite s).exists_minimal hsne
  have hUS : ctxU t tau x₁ x₂ lam < 𝒮 := hSmem.1
  have hSP : 𝒮 ≤ P := hSmem.2
  have hcov : ctxU t tau x₁ x₂ lam ⋖ 𝒮 := by
    refine ⟨hUS, ?_⟩
    intro K hUK hKlt
    have hKs : K ∈ s := ⟨hUK, hKlt.le.trans hSP⟩
    exact absurd (hmin hKs hKlt.le) (not_le_of_gt hKlt)
  have hS2 : IsPGroup 2 𝒮 := P.isPGroup'.to_le hSP
  have hrel : (ctxU t tau x₁ x₂ lam).relIndex 𝒮 = 2 := relIndex_eq_two_of_covBy hS2 hcov
  have hcardS : Nat.card ↥𝒮 = 2 ^ 11 := by
    have hrelcard := Subgroup.relIndex_mul_card (H := ctxU t tau x₁ x₂ lam) (K := 𝒮)
    rw [inf_eq_left.mpr hUS.le] at hrelcard
    rw [← hrelcard, hrel, hUcard]
    norm_num
  refine ⟨𝒮, hS2, hUS.le, ?_, hcardS⟩
  refine ⟨hUS.le, ?_⟩
  have hnorm : ((ctxU t tau x₁ x₂ lam).subgroupOf 𝒮).Normal :=
    Subgroup.normal_of_index_eq_two (by simpa only [Subgroup.relIndex] using hrel)
  intro g hg k hk
  have hx : (⟨k, hUS.le hk⟩ : ↥𝒮) ∈ (ctxU t tau x₁ x₂ lam).subgroupOf 𝒮 := by
    rw [Subgroup.mem_subgroupOf]
    exact hk
  have hconj := hnorm.conj_mem (⟨k, hUS.le hk⟩ : ↥𝒮) hx (⟨g, hg⟩ : ↥𝒮)
  rw [Subgroup.mem_subgroupOf] at hconj
  simpa using hconj

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
