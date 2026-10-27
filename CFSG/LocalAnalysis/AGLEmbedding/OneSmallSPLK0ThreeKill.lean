module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeKill
import CFSG.LocalAnalysis.AGLEmbedding.ChevTwoKill
import CFSG.LocalAnalysis.AGLEmbedding.CoverAbelianSylowAux

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.ComponentClassification.OuterAutomorphisms

namespace ReducedNongeneration

variable {X : Type} [Group X] [Finite X] {p : ℕ} {Rbar : Sylow p X} {X₀ : Subgroup X}

theorem isCyclic_center_of_unique (hred : ReducedNongeneration p X Rbar X₀)
    {K : Subgroup X} (hK : IsComponentOf K ⊤)
    (huniq : ∀ L : Subgroup X, IsComponentOf L ⊤ → L = K) : IsCyclic (Subgroup.center K) := by
  have h := hred.isCyclic_map_center hK (normal_of_forall_isComponentOf_eq hK huniq)
  let e := Subgroup.equivMapOfInjective (Subgroup.center K) K.subtype K.subtype_injective
  exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective

variable [Fact p.Prime]

theorem mem_of_mem_centralizer_of_unique
    {K : Subgroup X} (hK : IsComponentOf K ⊤)
    (huniq : ∀ L : Subgroup X, IsComponentOf L ⊤ → L = K)
    (hcent : ∀ c ∈ (Rbar : Subgroup X) ⊓ Subgroup.centralizer (K : Set X), orderOf c = p →
      c ∈ (Subgroup.center K).map K.subtype) :
    ∀ c ∈ Subgroup.centralizer (K : Set X), orderOf c = p → c ∈ K :=
  fun _ hc hcp => mem_of_mem_centralizer_of_orderOf_eq Rbar
    (normal_of_forall_isComponentOf_eq hK huniq)
    (fun c hc hcp => Subgroup.map_subtype_le _ (hcent c hc hcp)) hc hcp

theorem false_of_caseThreeKFact (hred : ReducedNongeneration p X Rbar X₀)
    {K : Subgroup X} (hK : IsComponentOf K ⊤)
    (huniq : ∀ L : Subgroup X, IsComponentOf L ⊤ → L = K)
    (hnc : ¬ IsCyclic ((Rbar : Subgroup X) ⊓ K : Subgroup X))
    (hcent : ∀ c ∈ (Rbar : Subgroup X) ⊓ Subgroup.centralizer (K : Set X),
      orderOf c = p → c ∈ (Subgroup.center K).map K.subtype)
    (hKD : ¬ HasKlingenData p Rbar X₀)
    [Finite (Outer K)] (hOut : ¬ p ∣ Nat.card (Outer K)) (hS2 : S2Lemma)
    (hKl : KlingenTransport) (hfact : CaseThreeKFact p K) : False := by
  have hp : p.Prime := Fact.out
  have hKn : K.Normal := normal_of_forall_isComponentOf_eq hK huniq
  have hmem := mem_of_mem_centralizer_of_unique hK huniq hcent
  have hCp := isPGroup_centralizer_of_forall_mem hred.prime hred.ne_two hred.core_eq_bot hKn hmem
  have hCR : Subgroup.centralizer (K : Set X) ≤ (Rbar : Subgroup X) :=
    IsPGroup.le_sylow_of_normal hCp Rbar
  have hRK : (Rbar : Subgroup X) ≤ K ⊔ Subgroup.centralizer (K : Set X) := by
    intro x hx
    obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp Rbar.isPGroup') ⟨x, hx⟩
    refine mem_sup_centralizer_of_pow hp hOut (n := n) ?_
    have h1 := pow_orderOf_eq_one (⟨x, hx⟩ : (Rbar : Subgroup X))
    rw [hn] at h1
    exact congrArg Subtype.val h1
  have hnot := not_le_of_le_sup_centralizer hred hnc hCp hRK
  obtain ⟨T₀, hT₀⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal Rbar
    (ComponentClassification.Components.mathlib_subnormal_of_chain hK.2.1
      Subgroup.IsSubnormal.top)
  have hS1 : Subgroup.center K = ⊥ → Open.pRank p (T₀ : Subgroup K) ≤ 2 → False := by
    intro hZ hT2
    have hC := centralizer_eq_bot_of_forall_mem hred.prime hred.ne_two hred.core_eq_bot hKn hmem
      hZ
    have h2 := pRank_le_two_of_centralizer_eq_bot T₀ hT₀ hC hRK hT2
    have h3 := hred.three_le_pRank
    omega
  rcases hfact T₀ with htop | ⟨hT2, hZ | hcard⟩ | hkl
  · exact hnot (le_of_weakCore_eq_top hred T₀ hT₀ htop)
  · exact hS1 hZ hT2
  · by_cases hZ : Subgroup.center K = ⊥
    · exact hS1 hZ hT2
    ·
      have : Group.IsPerfect K := ⟨hK.2.2.1⟩
      have hZp := isPGroup_center_of_isComponentOf hred.prime hred.core_eq_bot hK
      obtain ⟨z, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hZ
      have hzT : (z : K) ∈ ⁅(T₀ : Subgroup K), (T₀ : Subgroup K)⁆ := by
        obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hZp) z
        refine center_le_commutator_of_isPerfect T₀ z.2 ⟨k, ?_⟩
        have h1 := pow_orderOf_eq_one z
        rw [hk] at h1
        exact congrArg Subtype.val h1
      have hna : ∃ a ∈ ((Rbar : Subgroup X) ⊓ K), ∃ b ∈ ((Rbar : Subgroup X) ⊓ K),
          a * b ≠ b * a := by
        by_contra hall
        push Not at hall
        apply hz1
        have hcomm : ⁅(T₀ : Subgroup K), (T₀ : Subgroup K)⁆ = ⊥ := by
          rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
          intro a ha
          rw [Subgroup.mem_centralizer_iff]
          intro b hb
          have hab := hall (a : _) (hT₀ ▸ Subgroup.mem_map_of_mem K.subtype ha)
            (b : _) (hT₀ ▸ Subgroup.mem_map_of_mem K.subtype hb)
          exact Subtype.ext hab.symm
        have hz' : (z : K) ∈ (⊥ : Subgroup K) := hcomm ▸ hzT
        exact Subtype.ext (Subgroup.mem_bot.mp hz')
      have hTcard : Nat.card ((Rbar : Subgroup X) ⊓ K : Subgroup X) = p ^ 3 := by
        rw [← hT₀, Subgroup.card_map_of_injective K.subtype_injective, hcard]
      have hCcyc := isCyclic_centralizer_of_forall_mem hred.prime hred.ne_two
        hred.core_eq_bot hKn hmem (hred.isCyclic_map_center hK hKn)
      have hCT : Subgroup.centralizer (K : Set X) ≤
          Subgroup.centralizer (((Rbar : Subgroup X) ⊓ K : Subgroup X) : Set _) :=
        Subgroup.centralizer_le (fun _ hy => hy.2)
      have hΩ : ∀ c ∈ Subgroup.centralizer (K : Set X),
          c ^ p = 1 → c ∈ ((Rbar : Subgroup X) ⊓ K) := by
        intro c hc hcp
        by_cases hc1 : c = 1
        · rw [hc1]; exact Subgroup.one_mem _
        · have hord : orderOf c = p := orderOf_eq_prime hcp hc1
          exact ⟨hCR hc, Subgroup.map_subtype_le _ (hcent c ⟨hCR hc, hc⟩ hord)⟩
      have h2 := hS2 _ p _ _ hTcard hna hCcyc hCT hΩ
      have h3 := hred.three_le_pRank.trans
        (PreuniquenessRankFour.Helpers.pRank_mono p hp (le_inf_sup_centralizer hCR hRK))
      omega
  · exact hKD (hKl _ p Rbar _ K T₀ hT₀ (weakCore_le_comap hred T₀ hT₀) hnot hkl)

theorem false_of_weakCore_eq_top (hred : ReducedNongeneration p X Rbar X₀)
    {K : Subgroup X} (hK : IsComponentOf K ⊤)
    (huniq : ∀ L : Subgroup X, IsComponentOf L ⊤ → L = K)
    (htop : ∀ T : Sylow p K, GLBWeakCore p (T : Subgroup K) = ⊤) : False := by
  have hp : p.Prime := Fact.out
  have hKn : K.Normal := normal_of_forall_isComponentOf_eq hK huniq
  obtain ⟨T₀, hT₀⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal Rbar
    (ComponentClassification.Components.mathlib_subnormal_of_chain hK.2.1
      Subgroup.IsSubnormal.top)
  have hle := le_of_weakCore_eq_top hred T₀ hT₀ (htop T₀)
  have : IsSimpleGroup (K ⧸ Subgroup.center K) := hK.2.2.2
  have : Nontrivial K := (QuotientGroup.mk'_surjective (Subgroup.center K)).nontrivial
  have h3 := three_le_pRank_of_weakCore_eq_top hp (htop T₀)
  rw [← PreuniquenessRankFour.Helpers.pRank_map_of_injective p hp K.subtype
    K.subtype_injective, hT₀] at h3
  exact false_of_le_of_three_le_pRank hred hle
    (h3.trans (PreuniquenessRankFour.Helpers.pRank_mono p hp inf_le_right))

theorem false_of_le_weakCore {T : Type*} [Group T]
    (hred : ReducedNongeneration p X Rbar X₀) {K : Subgroup X} (hK : IsComponentOf K ⊤)
    (huniq : ∀ L : Subgroup X, IsComponentOf L ⊤ → L = K)
    (hcent : ∀ c ∈ (Rbar : Subgroup X) ⊓ Subgroup.centralizer (K : Set X), orderOf c = p →
      c ∈ (Subgroup.center K).map K.subtype)
    (e : K ⧸ Subgroup.center K ≃* T)
    (hOut : ∀ S : Sylow p (Outer T), (S : Subgroup (Outer T)).Normal)
    (hW : K ≤ GLBWeakCore p (Rbar : Subgroup X)) : False := by
  have hKn : K.Normal := normal_of_forall_isComponentOf_eq hK huniq
  have : Group.IsPerfect K := ⟨hK.2.2.1⟩
  have hCp := isPGroup_centralizer_of_forall_mem hred.prime hred.ne_two hred.core_eq_bot hKn
    (mem_of_mem_centralizer_of_unique hK huniq hcent)
  have hCR := IsPGroup.le_sylow_of_normal hCp Rbar
  exact false_of_le_of_normal_sup hred (hW.trans hred.weakCore_le)
    (normal_sup_of_outer K e Rbar hCR hOut)

end ReducedNongeneration

end CFSG.AGLEmbedding
