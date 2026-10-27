module

public import CFSG.CGT.PushingUpLit.BHS.LLemmaBasic
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.CGT.PushingUpLit.T2K.Setup

public section

namespace CFSG.CGT.PushingUpLit.T2K

open CFSG CFSG.RankThree.PartOne
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L M T : Subgroup G} {n : ℕ}

theorem le_of_isPGroup_normal {N : Subgroup G} (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M)
    (hNM : N ≤ M)
    (hn : M ≤ Subgroup.normalizer (N : Set G)) (hN : IsPGroup 2 N) : N ≤ T := by
  have h1 : IsPGroup 2 (N ⊔ T : Subgroup G) :=
    hN.to_sup_of_normal_left' hT.isPGroup (hT.le.trans hn)
  have h2 := hT.eq_of_le le_sup_right (sup_le hNM hT.le) h1
  exact le_sup_left.trans h2.le

omit [Finite G] in
theorem mem_normalizer_centralizer {V : Subgroup G} {m : G}
    (hm : m ∈ Subgroup.normalizer (V : Set G)) :
    m ∈ Subgroup.normalizer (Subgroup.centralizer (V : Set G) : Set G) := by
  have key : ∀ m ∈ Subgroup.normalizer (V : Set G), ∀ x ∈ Subgroup.centralizer (V : Set G),
      m * x * m⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
    intro m hm x hx
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hv' : m⁻¹ * v * m ∈ V := by
      have := (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer (V : Set G)).inv_mem hm) v).1 hv
      simpa using this
    have h1 := Subgroup.mem_centralizer_iff.1 hx _ hv'
    calc v * (m * x * m⁻¹) = m * ((m⁻¹ * v * m) * x) * m⁻¹ := by group
      _ = m * (x * (m⁻¹ * v * m)) * m⁻¹ := by rw [h1]
      _ = m * x * m⁻¹ * v := by group
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key m hm y, fun hy => ?_⟩
  have := key m⁻¹ ((Subgroup.normalizer (V : Set G)).inv_mem hm) _ hy
  simpa [mul_assoc] using this

namespace NatBlock

omit [Finite G] in
theorem le_normalizer_blockU_of_le (hMN : M ≤ Subgroup.normalizer (L : Set G)) :
    M ≤ Subgroup.normalizer (blockU L : Set G) := by
  intro m hm
  rw [Subgroup.mem_normalizer_iff]
  intro u
  refine ⟨fun hu => conj_mem_blockU (hMN hm) hu, fun hu => ?_⟩
  have := conj_mem_blockU (hMN (M.inv_mem hm)) hu
  simpa [mul_assoc] using this

omit [Finite G] in
theorem le_normalizer_centralizer (hMN : M ≤ Subgroup.normalizer (L : Set G)) :
    M ≤ Subgroup.normalizer
      ((M ⊓ Subgroup.centralizer (blockU L : Set G) : Subgroup G) : Set G) := by
  intro m hm
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have h1 := Subgroup.mem_normalizer_iff.1
    (mem_normalizer_centralizer (le_normalizer_blockU_of_le hMN hm)) y
  have h2 := Subgroup.mem_normalizer_iff.1 (Subgroup.le_normalizer hm : m ∈ Subgroup.normalizer
    (M : Set G)) y
  simp only [Subgroup.mem_inf, h1, h2]

theorem blockU_le_sylow (hLM : L ≤ M)
    (hMN : M ≤ Subgroup.normalizer (L : Set G)) (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) :
    blockU L ≤ T := by
  refine le_of_isPGroup_normal hT ((blockU_le L).trans hLM)
    (le_normalizer_blockU_of_le hMN) ?_
  exact (isPGroup_oTwoIn L).to_le (blockU_le_oTwoIn L)

theorem oTwoIn_le_sylow (hLM : L ≤ M) (hMN : M ≤ Subgroup.normalizer (L : Set G))
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) : oTwoIn L ≤ T := by
  refine le_of_isPGroup_normal hT ((oTwoIn_le L).trans hLM) ?_ (isPGroup_oTwoIn L)
  intro m hm
  exact normalizer_le_normalizer_oTwoIn L (hMN hm)

theorem mem_of_mul_mem_centralizer (h : NatBlock L n) (hLM : L ≤ M)
    (hMN : M ≤ Subgroup.normalizer (L : Set G)) (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M)
    {a l : G} (ha : a ∈ T)
    (hl : l ∈ L) (hu : l⁻¹ * a ∈ Subgroup.centralizer (blockU L : Set G)) : l ∈ T := by
  set U : Subgroup G := M ⊓ Subgroup.centralizer (blockU L : Set G) with hU
  have hUn : M ≤ Subgroup.normalizer (U : Set G) := le_normalizer_centralizer hMN
  have hTn : T ≤ Subgroup.normalizer (U : Set G) := hT.le.trans hUn
  have hTL : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ L) L := hT.inf_of_le_normalizer hLM hMN
  set K : Subgroup G := L ⊓ (T ⊔ U) with hK
  have hTLK : T ⊓ L ≤ K := fun x hx => ⟨hx.2, Subgroup.mem_sup_left hx.1⟩
  have hK2 : IsPGroup 2 K := by
    intro g
    obtain ⟨hgL, hgTU⟩ := g.2
    obtain ⟨t, ht, u, hu', hg⟩ :=
      (CFSG.CGT.PushingUpLit.BHS.mem_sup_iff_of_le_normalizer hTn).1 hgTU
    obtain ⟨i, hi⟩ := hT.isPGroup ⟨t, ht⟩
    have hti : t ^ 2 ^ i = 1 := congrArg Subtype.val hi
    have hu'' : t * u * t⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.1 (hTn ht) u).1 hu'
    have e : (g : G) = (t * u * t⁻¹) * t := by rw [hg]; group
    obtain ⟨y, hy, hpow⟩ := SubTwo.exists_pow_mul_eq hUn hu'' (hT.le ht) (2 ^ i)
    have h1 : (g : G) ^ 2 ^ i = y := by rw [e, hpow, hti, mul_one]
    have h2 : y ∈ oTwoIn L := by
      rw [← h.inf_centralizer_blockU]
      refine Subgroup.mem_inf.2 ⟨?_, hy.2⟩
      rw [← h1]
      exact L.pow_mem hgL _
    obtain ⟨j, hj⟩ := (isPGroup_oTwoIn L) ⟨y, h2⟩
    have hj' : y ^ 2 ^ j = 1 := congrArg Subtype.val hj
    refine ⟨i + j, Subtype.ext ?_⟩
    show (g : G) ^ 2 ^ (i + j) = 1
    rw [pow_add, pow_mul, h1]
    exact hj'
  have hKeq : K = T ⊓ L := hTL.eq_of_le hTLK inf_le_left hK2
  have hlK : l ∈ K := by
    refine ⟨hl, ?_⟩
    have hu1 : l⁻¹ * a ∈ U := ⟨M.mul_mem (M.inv_mem (hLM hl)) (hT.le ha), hu⟩
    have e : l = a * (l⁻¹ * a)⁻¹ := by group
    rw [e]
    exact mul_mem (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right (U.inv_mem hu1))
  rw [hKeq] at hlK
  exact hlK.1

end NatBlock

end CFSG.CGT.PushingUpLit.T2K
