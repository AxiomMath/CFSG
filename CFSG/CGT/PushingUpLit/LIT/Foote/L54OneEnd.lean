module

public import CFSG.CGT.PushingUpLit.LIT.Foote.L54One
public import CFSG.CGT.PushingUpLit.LIT.Foote.L54Strong
public import CFSG.CGT.PushingUpLit.LIT.Foote.L53C
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingLemma34Borel

public section

namespace CFSG.CGT.PushingUpLit.LIT.Foote

open CFSG CFSG.CGT.PushingUpLit CFSG.CGT.PushingUp CFSG.Assembly
open CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AschbacherStrongEmbedding CFSG.ShultStronglyClosedTI
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace CE

variable {M J : Subgroup G} (c : CE G M J)
include c

theorem false_of_stronglyEmbedded
    (hse : CFSG.Open.fusionStronglyEmbedded M) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨E, hEV, hE⟩ := c.block.exists_subgroup_card_pow (k := 2) (by norm_num)
  have hr : CFSG.BenderSuzuki.PFchapter1section1.TwoRankAtLeastTwo G := by
    refine ⟨E, by rw [hE]; norm_num, fun x => ?_⟩
    have := c.block.isElemAbelian_blockU.2 (x : G) (hEV x.2)
    exact Subtype.ext (by simpa using this)
  obtain ⟨T, hT⟩ := Lemma34.eq_normalizer_of_stronglyEmbedded c.simple hse hr
  have hJT : J ≤ Subgroup.normalizer ((T : Subgroup G) : Set G) := hT ▸ c.le
  obtain ⟨P, hP⟩ := exists_isSylowOf 2 J
  have hPT : P ≤ (T : Subgroup G) := by
    have hsup : IsPGroup 2 ↥(P ⊔ (T : Subgroup G)) :=
      hP.isPGroup.to_sup_of_normal_right' T.isPGroup' (hP.le.trans hJT)
    have := T.3 hsup le_sup_right
    exact this ▸ le_sup_left
  have hN : J ⊓ (T : Subgroup G) = J := by
    refine eq_of_isSylowOf_le c.block.perfect inf_le_left ?_ hP (le_inf hP.le hPT)
    intro g hg n hn
    refine ⟨J.mul_mem (J.mul_mem hg (Subgroup.mem_inf.1 hn).1) (J.inv_mem hg), ?_⟩
    have := (Subgroup.mem_normalizer_iff.1 (hJT hg) n).1 (Subgroup.mem_inf.1 hn).2
    exact this
  have hJle : J ≤ (T : Subgroup G) := hN ▸ inf_le_right
  have hJ2 : IsPGroup 2 J := T.isPGroup'.to_le hJle
  have : Group.IsNilpotent ↥J := hJ2.isNilpotent
  have : Group.IsPerfect ↥J := Subgroup.isPerfect_iff.2 c.block.perfect
  have : Nontrivial ↥J := (Subgroup.nontrivial_iff_ne_bot J).2 c.block.ne_bot
  exact Group.IsPerfect.not_isSolvable ↥J inferInstance

theorem part_one
    (hA : FooteTheoremA) {z₀ : G} (hz₀ : ZData J z₀) (hth : Three M J)
    (hno : ∀ h : G, h ∉ M → ∀ t ∈ J, t ∈ rightConjugate M h → t * t = 1 → t = 1) : False := by
  have hs := c.simple
  have hz2 : orderOf z₀ = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz₀.sq) hz₀.ne_one
  have hz₀2 : ∃ n : ℕ, z₀ ^ 2 ^ n = 1 := twoElem_of_mul_self hz₀.sq
  have huniq : ∀ g : G, z₀ ∈ rightConjugate M g ↔ g ∈ M := by
    intro g
    constructor
    · intro hz
      by_contra hg
      exact hz₀.ne_one (hno g hg z₀ hz₀.mem hz hz₀.sq)
    · intro hg
      rw [mem_rightConjugate_iff]
      exact M.mul_mem (M.mul_mem hg (c.le hz₀.mem)) (M.inv_mem hg)
  have hPUC : ProductUniqueContainment M z₀ := by
    intro t ht hcomm htne g
    obtain ⟨h', hh'⟩ := ht
    have htdef : t = h'⁻¹ * z₀ * h' := hh'.symm
    have htt : t * t = 1 := by
      rw [htdef]
      calc h'⁻¹ * z₀ * h' * (h'⁻¹ * z₀ * h') = h'⁻¹ * (z₀ * z₀) * h' := by group
        _ = 1 := by rw [hz₀.sq]; group
    have htc : t * z₀ = z₀ * t := hcomm.symm.eq
    have htM : t ∈ M :=
      c.centralizer_le_of_mem hz₀.mem hz₀2 hz₀.ne_one (Subgroup.mem_centralizer_singleton_iff.2 htc)
    have hh'M : h' ∈ M := by
      have : z₀ ∈ rightConjugate M h'⁻¹ := by
        rw [mem_rightConjugate_iff, inv_inv, ← htdef]
        exact htM
      simpa using M.inv_mem ((huniq h'⁻¹).1 this)
    have htJ : t ∈ rightConjugate J h' := by
      rw [mem_rightConjugate_iff, htdef]
      have e : h' * (h'⁻¹ * z₀ * h') * h'⁻¹ = z₀ := by group
      rw [e]
      exact hz₀.mem
    have hy2 : z₀ * t * (z₀ * t) = 1 := by
      calc z₀ * t * (z₀ * t) = z₀ * (t * z₀) * t := by group
        _ = z₀ * (z₀ * t) * t := by rw [htc]
        _ = (z₀ * z₀) * (t * t) := by group
        _ = 1 := by rw [hz₀.sq, htt, one_mul]
    have hy1 : z₀ * t ≠ 1 := by
      intro h1
      apply htne
      have : t = z₀⁻¹ := eq_inv_of_mul_eq_one_right h1
      rw [this]
      exact inv_eq_of_mul_eq_one_right hz₀.sq
    obtain ⟨c₃, hc₃, hX1, hX2⟩ := hth.exists_notin J (rightConjugate J h')
    have hyC : Subgroup.centralizer ({z₀ * t} : Set G) ≤ M := by
      refine c.centralizer_le_of_centralizes hy1 (twoElem_of_mul_self hy2) hc₃ ?_
      intro x hx
      have h1 : z₀ * x = x * z₀ := c.comm_J hc₃ hX1 hz₀.mem hx
      have h2 : t * x = x * t := c.comm_conj hh'M hc₃ (fun h => hX2 h.symm) htJ hx
      calc x * (z₀ * t) = (x * z₀) * t := by group
        _ = (z₀ * x) * t := by rw [h1]
        _ = z₀ * (x * t) := by group
        _ = z₀ * (t * x) := by rw [h2]
        _ = z₀ * t * x := by group
    have hyM : z₀ * t ∈ M := M.mul_mem (c.le hz₀.mem) htM
    constructor
    · intro hmem
      by_contra hgM
      have hh : g⁻¹ ∉ M := fun h => hgM (by simpa using M.inv_mem h)
      have hyh : z₀ * t ∈ rightConjugate M g⁻¹ := by
        rw [mem_rightConjugate_iff]
        simpa using hmem
      exact c.part_one_core hA hz₀ hth hno hy2 hyC hh hyh
    · intro hg
      exact M.mul_mem (M.mul_mem (M.inv_mem hg) hyM) hg
  obtain ⟨E, hEV, hE8⟩ := c.block.exists_subgroup_card_pow (k := 3) le_rfl
  have hE2 : ∀ x ∈ E, x ^ 2 = 1 := fun x hx => c.block.isElemAbelian_blockU.2 x (hEV hx)
  have hse := L54.fusionStronglyEmbedded_of_puc
    hs hE2 (by rw [hE8]; norm_num) hz2 c.ne_top huniq hPUC
  exact c.false_of_stronglyEmbedded hse

end CE

end CFSG.CGT.PushingUpLit.LIT.Foote
