module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeSporAlt
public import CFSG.LocalAnalysis.AGLEmbedding.IIIaLists
import CFSG.LocalAnalysis.AGLEmbedding.CoverAbelianSylowAux
import CFSG.LocalAnalysis.AGLEmbedding.SporCaseThreeData
import CFSG.LocalAnalysis.AGLEmbedding.SporCaseThreeDataAux
import CFSG.LocalAnalysis.AGLEmbedding.SporadicBeta

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.RankThree.PartOne.StrongP

@[expose] def CaseThreeMid (p : ℕ) [Fact p.Prime] (K : Type) [Group K] [Finite K] : Prop :=
  ∀ T : Sylow p K, Open.pRank p (T : Subgroup K) ≤ 2 ∧
    (Subgroup.center K = ⊥ ∨ Nat.card (T : Subgroup K) = p ^ 3)

theorem false_of_caseThreeMid {Y : Type} [Group Y] [Finite Y] {p : ℕ} [Fact p.Prime]
    {Rb : Sylow p Y} {Y₀ : Subgroup Y} (h : ReducedNongeneration p Y Rb Y₀) {K : Subgroup Y}
    (hK : IsComponentOf K ⊤) (huniq : ∀ L : Subgroup Y, IsComponentOf L ⊤ → L = K)
    (hcent : ∀ c ∈ (Rb : Subgroup Y) ⊓ Subgroup.centralizer (K : Set Y), orderOf c = p →
      c ∈ (Subgroup.center K).map K.subtype)
    [Finite (Outer K)] (hOut : ¬ p ∣ Nat.card (Outer K)) (hmid : CaseThreeMid p K) : False := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := h.ne_two
  have hKn : K.Normal := normal_of_forall_isComponentOf_eq hK huniq
  have hmem : ∀ c ∈ Subgroup.centralizer (K : Set Y), orderOf c = p → c ∈ K :=
    fun c hc hcp => mem_of_mem_centralizer_of_orderOf_eq Rb hKn
      (fun c hc hcp => Subgroup.map_subtype_le _ (hcent c hc hcp)) hc hcp
  have hCp := isPGroup_centralizer_of_forall_mem hp hp2 h.core_eq_bot hKn hmem
  have hZp := isPGroup_center_of_isComponentOf hp h.core_eq_bot hK
  have hRK : (Rb : Subgroup Y) ≤ K ⊔ Subgroup.centralizer (K : Set Y) := by
    intro x hx
    obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp Rb.isPGroup') ⟨x, hx⟩
    refine mem_sup_centralizer_of_pow hp hOut (n := n) ?_
    have h1 := pow_orderOf_eq_one (⟨x, hx⟩ : (Rb : Subgroup Y))
    rw [hn] at h1
    exact congrArg Subtype.val h1
  obtain ⟨T₀, hT₀⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal Rb
    (ComponentClassification.Components.mathlib_subnormal_of_chain hK.2.1
      Subgroup.IsSubnormal.top)
  have h3 := h.three_le_pRank
  obtain ⟨hT2, hZc⟩ := hmid T₀
  by_cases hZ : Subgroup.center K = ⊥
  · have hC := centralizer_eq_bot_of_forall_mem hp hp2 h.core_eq_bot hKn hmem hZ
    have h2 := pRank_le_two_of_centralizer_eq_bot T₀ hT₀ hC hRK hT2
    omega
  · have hcard : Nat.card (T₀ : Subgroup K) = p ^ 3 := hZc.resolve_left hZ
    have : Group.IsPerfect K := ⟨hK.2.2.1⟩
    obtain ⟨z, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hZ
    have hzT : (z : K) ∈ ⁅(T₀ : Subgroup K), (T₀ : Subgroup K)⁆ := by
      obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hZp) z
      refine center_le_commutator_of_isPerfect T₀ z.2 ⟨k, ?_⟩
      have h1 := pow_orderOf_eq_one z
      rw [hk] at h1
      exact congrArg Subtype.val h1
    have hna : ∃ a ∈ ((Rb : Subgroup Y) ⊓ K), ∃ b ∈ ((Rb : Subgroup Y) ⊓ K), a * b ≠ b * a := by
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
    have hTcard : Nat.card ((Rb : Subgroup Y) ⊓ K : Subgroup Y) = p ^ 3 := by
      rw [← hT₀, Subgroup.card_map_of_injective K.subtype_injective, hcard]
    have hCR : Subgroup.centralizer (K : Set Y) ≤ (Rb : Subgroup Y) :=
      IsPGroup.le_sylow_of_normal hCp Rb
    have hCcyc := isCyclic_centralizer_of_forall_mem hp hp2 h.core_eq_bot hKn hmem
      (h.isCyclic_map_center hK hKn)
    have hCT : Subgroup.centralizer (K : Set Y) ≤
        Subgroup.centralizer (((Rb : Subgroup Y) ⊓ K : Subgroup Y) : Set Y) :=
      Subgroup.centralizer_le (fun _ hy => hy.2)
    have hΩ : ∀ c ∈ Subgroup.centralizer (K : Set Y), c ^ p = 1 →
        c ∈ ((Rb : Subgroup Y) ⊓ K) := by
      intro c hc hcp
      by_cases hc1 : c = 1
      · rw [hc1]
        exact Subgroup.one_mem _
      · exact ⟨hCR hc, hmem c hc (orderOf_eq_prime hcp hc1)⟩
    have h2 := pRank_sup_le_two hTcard hna hCcyc hCT hΩ
    have h3' := h3.trans
      (PreuniquenessRankFour.Helpers.pRank_mono p hp (le_inf_sup_centralizer hCR hRK))
    omega

@[expose] def SporMidAt (X : Type) [Group X] (p : ℕ) : Prop :=
  ¬ p ^ 3 ∣ Nat.card X ∨ (¬ p ^ 4 ∣ Nat.card X ∧ HasNoncommPair p X ∧ KernelTrivialAt X p)

theorem sporMidAt_of_noncomm {X : Type} [Group X] {p : ℕ} (h4 : ¬ p ^ 4 ∣ Nat.card X)
    (hn : HasNoncommPair p X) (hk : KernelTrivialAt X p) : SporMidAt X p :=
  Or.inr ⟨h4, hn, hk⟩

theorem caseThreeMid_of_sporMidAt {X : Type} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    (hX : SporMidAt X p) {K : Type} [Group K] [Finite K] (hK : Open.IsQuasisimple K)
    (e : K ⧸ Subgroup.center K ≃* X) (hZp : IsPGroup p (Subgroup.center K))
    (hZc : IsCyclic (Subgroup.center K)) : CaseThreeMid p K := fun T => by
  have hp : p.Prime := Fact.out
  have : Group.IsPerfect K := ⟨hK.1⟩
  rcases hX with h3 | ⟨h4, hpair, hkt⟩
  · exact pRank_le_two_of_not_dvd_card hZp hZc (by rwa [Nat.card_congr e.toEquiv]) T
  · have hZ := center_eq_bot_of_kernelTrivialAt hkt e hZp
    obtain ⟨π, hπ, hker⟩ := exists_surjective_ker_eq_center e
    have hiso : K ≃* X :=
      MulEquiv.ofBijective π ⟨(MonoidHom.ker_eq_bot_iff π).mp (hker.trans hZ), hπ⟩
    exact ⟨pRank_sylow_le_two_of_mulEquiv hp hiso (pRank_le_two_of_hasNoncommPair hp h4 hpair) T,
      Or.inl hZ⟩

theorem kFactP1ThreeSpor_of_midAt
    (hbr : ∀ s : TauCeti.SporadicName,
      Nonempty (Blueprint.NativeSporadic.Carrier s ≃* (TauCeti.CFSGIndex.sporadic s).Group))
    (hOutS : ∀ s : TauCeti.SporadicName, ∀ p : ℕ, p.Prime → p ≠ 2 →
      ¬ p ∣ Nat.card (Outer (TauCeti.CFSGIndex.sporadic s).Group))
    (hmid : ∀ (s : TauCeti.SporadicName) (p : ℕ) [Fact p.Prime], p ≠ 2 → ¬ P1ThreeSporList p s →
      SporMidAt (Blueprint.NativeSporadic.Carrier s) p) : KFactP1ThreeSpor := by
  intro p _ Y _ _ Rb Y₀ h _ K hK huniq _ hcent s ⟨e⟩
  by_contra hlist
  obtain ⟨b⟩ := hbr s
  have hp : p.Prime := Fact.out
  have hKq : Open.IsQuasisimple K := hK.2.2
  have : Group.IsPerfect K := ⟨hK.2.2.1⟩
  have : Finite (MulAut K) := MulEquiv.finite_left
  have : Finite (TauCeti.CFSGIndex.sporadic s).Group := Finite.of_equiv _ e.toEquiv
  have : Finite (Blueprint.NativeSporadic.Carrier s) := Finite.of_equiv _ b.symm.toEquiv
  have hOutQ : ¬ p ∣ Nat.card (Outer (K ⧸ Subgroup.center K)) := by
    rw [Nat.card_congr (equivalence e).toEquiv]
    exact hOutS s p hp h.ne_two
  have hOut := not_dvd_card_outer_of_quotient hOutQ
  have hZp := isPGroup_center_of_isComponentOf hp h.core_eq_bot hK
  have hZc := h.isCyclic_center hK (normal_of_forall_isComponentOf_eq hK huniq)
  exact false_of_caseThreeMid h hK huniq hcent hOut
    (caseThreeMid_of_sporMidAt (hmid s p h.ne_two hlist) hKq (e.trans b.symm) hZp hZc)

end CFSG.AGLEmbedding
