module

public import CFSG.CGT.PushingUpLit.EightOneRel
public import CFSG.CGT.PushingUpLit.BlocksCommute
public import CFSG.CGT.PushingUpLit.Glue.ClassXBasic
public import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank

public section

namespace CFSG.CGT.PushingUpLit.Glue

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit
open CFSG.CGT.PushingUpLit.EightOneRel
open CFSG.QuasithinUnique.Setup.Campbell (pRank_mono)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_normalizer_of_conjugate_eq' {H : Subgroup G} {g : G} (h : conjugate H g = H) :
    g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have := ThreeFromEight.mem_conjugate_iff (H := H) (g := g) (x := x)
  rw [h] at this
  exact this

theorem le_normalizer_of_contains {K X Y I : Subgroup G} (hK : IsCharacteristicP 2 ↥K)
    (hX : IsBlockOfInX K X) (hY : InClassX ↥Y) (hYX : Y ≤ X) (hIK : I ≤ K)
    (hIY : I ≤ Subgroup.normalizer (Y : Set G)) : I ≤ Subgroup.normalizer (X : Set G) := by
  intro i hi
  have hiK : i ∈ K := hIK hi
  have hX' : IsBlockOfInX K (conjugate X i) := by
    refine ⟨?_, isSubnormal_conjugate hX.2.1 hiK, inClassX_conjugate hX.2.2 i⟩
    intro x hx
    have h1 : i * x * i⁻¹ ∈ X := ThreeFromEight.mem_conjugate_iff.1 hx
    have h2 : i * x * i⁻¹ ∈ K := hX.1 h1
    have : x = i⁻¹ * (i * x * i⁻¹) * i := by group
    rw [this]
    exact K.mul_mem (K.mul_mem (K.inv_mem hiK) h2) hiK
  by_cases heq : conjugate X i = X
  · exact mem_normalizer_of_conjugate_eq' heq
  · exfalso
    have hcomm : ⁅X, conjugate X i⁆ = ⊥ :=
      distinct_blocks_commute_of_isBlockOfInX hK hX hX' fun h => heq h.symm
    have hYc : Y ≤ conjugate X i := by
      have h1 : conjugate Y i = Y := ThreeFromEight.conjugate_eq_self_of_mem_normalizer (hIY hi)
      rw [← h1]
      exact Subgroup.map_mono hYX
    refine isShortGroup_not_commutative hY.1 fun a ha b hb => ?_
    have h1 : ⁅a, b⁆ ∈ ⁅X, conjugate X i⁆ := Subgroup.commutator_mem_commutator (hYX ha) (hYc hb)
    rw [hcomm, Subgroup.mem_bot] at h1
    exact commutatorElement_eq_one_iff_mul_comm.1 h1

theorem commutator_eq_of_contains {X Y I : Subgroup G} (hX : InClassX ↥X) (hY : InClassX ↥Y)
    (hYX : Y ≤ X) (hIX : I ≤ Subgroup.normalizer (X : Set G)) (hcomm : ⁅Y, I⁆ = Y) :
    ⁅X, I⁆ = X := by
  have hNX : ⁅X, I⁆ ≤ X := Subgroup.le_normalizer_iff_commutator_le_left.1 hIX
  have hXN : X ≤ Subgroup.normalizer ((⁅X, I⁆ : Subgroup G) : Set G) :=
    Subgroup.normalizer_commutator_ge_left X I
  rcases inClassX_normal_le_or_sup hX hNX hXN with h1 | h1
  · exfalso
    have hYN : Y ≤ ⁅X, I⁆ :=
      calc Y = ⁅Y, I⁆ := hcomm.symm
        _ ≤ ⁅X, I⁆ := Subgroup.commutator_mono hYX le_rfl
    exact isShortGroup_not_isPGroup hY.1 ((isPGroup_oTwoIn X).to_le (hYN.trans h1))
  · exact isShortGroup_eq_of_sup_oTwoIn hX.1 hNX hXN h1

theorem pRank_eq_of_isSylowOf {Q N : Subgroup G} (hQ : IsSylowOf 2 Q N) :
    pRank 2 ↥Q = pRank 2 ↥N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q', hQ'⟩ := sylow_of_isSylowOf hQ
  have h1 := (CFSG.SectionRank.pRank_sylow Q').2
  rw [hQ'] at h1
  have h2 := Nine.pRank_map_injective N.subtype N.subtype_injective (Q.subgroupOf N) 2
  rw [Subgroup.map_subgroupOf_eq_of_le hQ.1] at h2
  exact h2.trans h1

theorem le_jIn_of_isSylowOf {N Q T I : Subgroup G} (hQ : IsSylowOf 2 Q N) (hQT : Q ≤ T)
    (hIT : jIn T = I) (hIQ : I ≤ Q) (hII : jIn I = I) : I ≤ jIn N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : pRank 2 ↥I = pRank 2 ↥Q :=
    le_antisymm (pRank_mono hIQ) ((pRank_mono hQT).trans (by rw [← hIT, pRank_jIn]))
  have h2 : jIn I ≤ jIn Q := jIn_mono_of_pRank_eq hIQ h1
  have h3 : jIn Q ≤ jIn N := jIn_mono_of_pRank_eq hQ.1 (pRank_eq_of_isSylowOf hQ)
  rw [hII] at h2
  exact h2.trans h3

end CFSG.CGT.PushingUpLit.Glue
