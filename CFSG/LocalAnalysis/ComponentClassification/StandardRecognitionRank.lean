module

public import CFSG.ClassicalInvolution.Basic
public import CFSG.LocalAnalysis.ComponentClassification.SmallLocalClassical
public import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
public import CFSG.LocalAnalysis.ComponentInitial.StandardBasics
public import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank

public section

namespace CFSG.ComponentClassification.StandardRecognition

open Subgroup CFSG.ComponentClassification.SmallLocal

variable {G : Type*} [Group G]

private theorem not_isMulCommutative_of_mulEquiv_quaternionGroup {T : Type*} [Group T] {m : ℕ}
    (hm : 2 ≤ m) (e : T ≃* QuaternionGroup m) : ¬ IsMulCommutative T := by
  intro hT
  have hc : (QuaternionGroup.xa 0 : QuaternionGroup m) ∈ center (QuaternionGroup m) :=
    mem_center_iff.2 fun g => e.symm.injective <| by
      simp only [map_mul]
      exact hT.is_comm.comm _ _
  rcases ((CFSG.GroupTheory.quaternion_centralizers hm).2.2.1 _).1 hc with h | h <;> cases h

private theorem exists_unique_involution_of_quaternion {H : Type*} [Group H] {S : Subgroup H}
    {k : ℕ} (e : S ≃* QuaternionGroup (2 ^ k)) :
    ∃ u ∈ S, orderOf u = 2 ∧ ∀ x ∈ S, orderOf x = 2 → x = u := by
  obtain ⟨u, hu2, hu, -⟩ :=
    CFSG.ClassicalInvolution.exists_unique_involution_of_mulEquiv_quaternionGroup e
  refine ⟨u, u.2, by rwa [Subgroup.orderOf_coe], fun x hx hx2 => ?_⟩
  exact congrArg Subtype.val (hu ⟨x, hx⟩ (by rwa [Subgroup.orderOf_mk]))

theorem normal_quaternion_sylow_classical [Finite G] {t : G} (ht : orderOf t = 2)
    {R : Subgroup G} (hRC : R ≤ centralizer ({t} : Set G))
    (hRn : (R.subgroupOf (centralizer ({t} : Set G))).Normal) (htR : t ∈ R) (S : Sylow 2 R)
    {n : ℕ} (hn : 3 ≤ n) (hS : Nonempty ((S : Subgroup R) ≃* QuaternionGroup (2 ^ (n - 2)))) :
    IsClassicalInvolutionWitness t R ∧ ClassicalInvolution t := by
  obtain ⟨e⟩ := hS
  have hm : 2 ≤ 2 ^ (n - 2) := Nat.le_self_pow (by omega) 2
  exact normal_unique_involution_classical ht hRC hRn htR
    (CFSG.ClassicalInvolution.unique_involution_of_quaternion_sylow htR ht hRC S
      ⟨n, hn, ⟨e⟩⟩).1
    fun P => not_isMulCommutative_of_mulEquiv_quaternionGroup hm ((P.equiv S).trans e)

theorem standard_quaternion_centralizer_classical [Finite G] {L : Subgroup G}
    (hL : CFSG.Assembly.ComponentType.IsStandardSubgroup L)
    (S : Sylow 2 (centralizer (L : Set G))) {n : ℕ} (hn : 3 ≤ n)
    (hS : Nonempty ((S : Subgroup (centralizer (L : Set G))) ≃* QuaternionGroup (2 ^ (n - 2))))
    {t : centralizer (L : Set G)} (htS : t ∈ S) (ht : orderOf t = 2) :
    IsClassicalInvolutionWitness (t : G)
        (centralizer (L : Set G) ⊓ centralizer ({(t : G)} : Set G)) ∧
      ClassicalInvolution (t : G) := by
  obtain ⟨e⟩ := hS
  have ht2 : orderOf (t : G) = 2 := by rwa [Subgroup.orderOf_coe]
  obtain ⟨u, -, -, hu⟩ := exists_unique_involution_of_quaternion e
  have hST : ∀ s ∈ S, (s : G) ∈ centralizer ({(t : G)} : Set G) := fun s hs => by
    have hc : s * t * s⁻¹ = t :=
      (hu _ (mul_mem (mul_mem hs htS) (inv_mem hs))
        (by rw [CFSG.ClassicalInvolution.orderOf_conj_eq, ht])).trans (hu t htS ht).symm
    exact mem_centralizer_singleton_iff.2 (congrArg Subtype.val (mul_inv_eq_iff_eq_mul.1 hc))
  have hle : centralizer (L : Set G) ⊓ centralizer ({(t : G)} : Set G) ≤
      centralizer (L : Set G) := inf_le_left
  have hrange : (S : Subgroup (centralizer (L : Set G))) ≤ (inclusion hle).range :=
    fun s hs => ⟨⟨s, s.2, hST s hs⟩, rfl⟩
  let SR := S.comapOfInjective (inclusion hle) (inclusion_injective hle) hrange
  have eR : (SR : Subgroup ↥(centralizer (L : Set G) ⊓ centralizer ({(t : G)} : Set G))) ≃*
      QuaternionGroup (2 ^ (n - 2)) :=
    (((S : Subgroup _).comap (inclusion hle)).equivMapOfInjective _
      (inclusion_injective hle)).trans ((MulEquiv.subgroupCongr (map_comap_eq_self hrange)).trans e)
  obtain ⟨-, -, -, -, hRn⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.standard_involution_centralizer_normality hL t.2 ht2
  exact normal_quaternion_sylow_classical ht2 inf_le_right hRn
    ⟨t.2, mem_centralizer_singleton_iff.2 rfl⟩ SR hn ⟨eR⟩

theorem standard_centralizer_rank_split [Finite G] {L : Subgroup G}
    (hL : CFSG.Assembly.ComponentType.IsStandardSubgroup L)
    (S : Sylow 2 (centralizer (L : Set G))) :
    2 ≤ CFSG.Open.pRank 2 (centralizer (L : Set G)) ∨
      (IsCyclic (S : Subgroup (centralizer (L : Set G))) ∧
        (S : Subgroup (centralizer (L : Set G))) ≠ ⊥) ∨
      ∃ n : ℕ, 3 ≤ n ∧
        Nonempty ((S : Subgroup (centralizer (L : Set G))) ≃* QuaternionGroup (2 ^ (n - 2))) ∧
        ∃ t : centralizer (L : Set G), t ∈ S ∧ orderOf t = 2 ∧
          (∀ x ∈ S, orderOf x = 2 → x = t) ∧
          IsClassicalInvolutionWitness (t : G)
              (centralizer (L : Set G) ⊓ centralizer ({(t : G)} : Set G)) ∧
            ClassicalInvolution (t : G) := by
  rcases le_or_gt 2 (CFSG.Open.pRank 2 (centralizer (L : Set G))) with h2 | h2
  · exact Or.inl h2
  right
  have hrank : CFSG.pRank 2 (S : Subgroup (centralizer (L : Set G))) ≤ 1 := by
    have h := (CFSG.SectionRank.pRank_sylow S).2.trans
      ((CFSG.SectionRank.pRank_eq_open_pRank_top 2 (centralizer (L : Set G))).trans
        (CFSG.SectionRank.pRank_eq_pRank_top_subgroup (centralizer (L : Set G))).symm)
    omega
  rcases (CFSG.LocalAnalysis.ComponentInitial.pgroup_rank_one_classification Nat.prime_two
      S.isPGroup').1 hrank with hcyc | ⟨-, n, hn, ⟨e⟩⟩
  · obtain ⟨-, heven, -⟩ := hL
    exact Or.inl ⟨hcyc, S.ne_bot_of_dvd_card (even_iff_two_dvd.1 heven)⟩
  · obtain ⟨t, htS, ht, hu⟩ := exists_unique_involution_of_quaternion e
    exact Or.inr ⟨n, hn, ⟨e⟩, t, htS, ht, hu,
      standard_quaternion_centralizer_classical hL S hn ⟨e⟩ htS ht⟩

end CFSG.ComponentClassification.StandardRecognition
