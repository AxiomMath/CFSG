module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.KlingenIdentLieAux
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLK0ThreeKill
public import CFSG.LocalAnalysis.AGLEmbedding.SporCaseThreeData
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicBeta
public import CFSG.LocalAnalysis.AGLEmbedding.SporCaseThreeDataAux
public import CFSG.LocalAnalysis.AGLEmbedding.CoverWeakGenData
public import CFSG.LocalAnalysis.AGLEmbedding.CoverAbelianSylowAux

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.KlingenIdentSporAux

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.ComponentClassification.OuterAutomorphisms CFSG.RankThree.PartOne.StrongP

theorem two_lt_card_of_nonabelian {G : Type} [Group G] [Finite G]
    (h : ∃ a b : G, a * b ≠ b * a) : 2 < Nat.card G := by
  by_contra hle
  push Not at hle
  obtain ⟨a, b, hab⟩ := h
  apply hab
  have hpos : 0 < Nat.card G := Nat.card_pos
  rcases (by omega : Nat.card G = 1 ∨ Nat.card G = 2) with h1 | h2
  · haveI : Subsingleton G := (Nat.card_eq_one_iff_unique.mp h1).1
    exact Subsingleton.elim _ _
  · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : IsCyclic G := isCyclic_of_prime_card (p := 2) h2
    exact (IsCyclic.commGroup (α := G)).mul_comm a b

@[expose] def GenData (X : Type) [Group X] [Finite X] (p : ℕ) [Fact p.Prime] : Prop :=
  (∀ T : Sylow p X, GLBWeakCore p (T : Subgroup X) = ⊤) ∧ CoverWeakGen X p

theorem genData_of_tc_cp {X : Type} [Group X] [Finite X] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (htc : TCGenDatum X p) (hcp : CoverPointDatum X p) : GenData X p :=
  ⟨fun T => weakCoreOfTC X p htc T, coverWeakGen_of_coverPointDatum hp2 hcp⟩

theorem weakCore_eq_top_of_genData {X : Type} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    (hX : GenData X p) {K : Type} [Group K] [Finite K] (hK : Open.IsQuasisimple K)
    (e : K ⧸ Subgroup.center K ≃* X) (hZp : IsPGroup p (Subgroup.center K))
    (hZc : IsCyclic (Subgroup.center K)) (T : Sylow p K) :
    GLBWeakCore p (T : Subgroup K) = ⊤ := by
  have hp : p.Prime := Fact.out
  have : Group.IsPerfect K := ⟨hK.1⟩
  obtain ⟨π, hπ, hker⟩ := exists_surjective_ker_eq_center e
  by_cases hZ : Subgroup.center K = ⊥
  · let f : K ≃* X :=
      MulEquiv.ofBijective π ⟨(MonoidHom.ker_eq_bot_iff π).mp (hker.trans hZ), hπ⟩
    let T' : Sylow p X := T.mapSurjective (f := f.toMonoidHom) f.surjective
    have hT : (T : Subgroup K) = (T' : Subgroup X).map f.symm.toMonoidHom := by
      ext x
      simp [T']
    exact glbWeakCore_eq_top_of_mulEquiv hp f.symm hT (hX.1 T')
  · exact hX.2 K π hπ hker ⟨hK.1⟩ hZ hZp hZc T

variable {Y : Type} [Group Y] [Finite Y] {p : ℕ} [Fact p.Prime] {Rb : Sylow p Y}
  {Y₀ : Subgroup Y} {K : Subgroup Y}

theorem false_of_genData (hred : ReducedNongeneration p Y Rb Y₀) (hK : IsComponentOf K ⊤)
    (huniq : ∀ L : Subgroup Y, IsComponentOf L ⊤ → L = K) {X : Type} [Group X] [Finite X]
    (hX : GenData X p) (e : K ⧸ Subgroup.center K ≃* X) : False :=
  ReducedNongeneration.false_of_weakCore_eq_top hred hK huniq fun T =>
    weakCore_eq_top_of_genData hX hK.2.2 e (KlingenIdentLieAux.isPGroup_center hred hK)
      (ReducedNongeneration.isCyclic_center_of_unique hred hK huniq) T

theorem card_le_of_klingen (hred : ReducedNongeneration p Y Rb Y₀) (hkl : HasKlingenData p Rb Y₀)
    {W : Subgroup Y} (hWR : W ≤ (Rb : Subgroup Y)) (hWC : W ≤ Subgroup.centralizer (Rb : Set Y))
    (hW : ∀ w ∈ W, w ^ p = 1) : Nat.card W ≤ p := by
  have hp : p.Prime := Fact.out
  obtain ⟨E, D, L, hER, -, -, -, hDE, hD, hDcard, -, hDN, -, -, -, -⟩ := hkl
  have hPY₀ : (Rb : Subgroup Y) ≤ Y₀ :=
    Subgroup.le_normalizer.trans
      ((PreuniquenessRankFour.Helpers.normalizer_le_weakCore_of_rank p hp _
        hred.three_le_pRank).trans hred.weakCore_le)
  obtain ⟨z, -, hzo, -, huniq⟩ := exists_mem_center_of_normalizer_not_le hp hred.ne_two Rb hPY₀
    hred.weakCore_le hred.three_le_pRank hD hDcard (hDE.trans hER) hDN
  have hWz : W ≤ Subgroup.zpowers z := by
    intro w hw
    by_cases h1 : w = 1
    · rw [h1]
      exact Subgroup.one_mem _
    · exact huniq w (hWC hw) (hWR hw) (orderOf_eq_prime (hW w hw) h1)
  calc Nat.card W ≤ Nat.card (Subgroup.zpowers z) := Subgroup.card_le_of_le hWz
    _ = p := by rw [Nat.card_zpowers, hzo]

theorem false_of_rank_two (hred : ReducedNongeneration p Y Rb Y₀) (hK : IsComponentOf K ⊤)
    (huniq : ∀ L : Subgroup Y, IsComponentOf L ⊤ → L = K)
    (hcent : ∀ c ∈ (Rb : Subgroup Y) ⊓ Subgroup.centralizer (K : Set Y), orderOf c = p →
      c ∈ (Subgroup.center K).map K.subtype)
    [Finite (Outer K)] (hOut : ¬ p ∣ Nat.card (Outer K)) (hS2 : S2Lemma)
    (h2 : ∀ T : Sylow p K, Open.pRank p (T : Subgroup K) ≤ 2 ∧
      (Subgroup.center K = ⊥ ∨ Nat.card (T : Subgroup K) = p ^ 3)) : False := by
  have hp : p.Prime := Fact.out
  have hKn : K.Normal := normal_of_forall_isComponentOf_eq hK huniq
  have hCp := KlingenIdentLieAux.isPGroup_centralizer hred hKn hcent
  have hCR : Subgroup.centralizer (K : Set Y) ≤ (Rb : Subgroup Y) :=
    IsPGroup.le_sylow_of_normal hCp Rb
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
  have hS1 : Subgroup.center K = ⊥ → Open.pRank p (T₀ : Subgroup K) ≤ 2 → False := by
    intro hZ hT2
    have hC := KlingenIdentLieAux.centralizer_eq_bot hred hKn hcent hZ
    have h2' := pRank_le_two_of_centralizer_eq_bot T₀ hT₀ hC hRK hT2
    have h3 := hred.three_le_pRank
    omega
  obtain ⟨hT2, hZ | hcard⟩ := h2 T₀
  · exact hS1 hZ hT2
  · by_cases hZ : Subgroup.center K = ⊥
    · exact hS1 hZ hT2
    ·
      have : Group.IsPerfect K := ⟨hK.2.2.1⟩
      have hZp := KlingenIdentLieAux.isPGroup_center hred hK
      obtain ⟨z, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hZ
      have hzT : (z : K) ∈ ⁅(T₀ : Subgroup K), (T₀ : Subgroup K)⁆ := by
        obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hZp) z
        refine center_le_commutator_of_isPerfect T₀ z.2 ⟨k, ?_⟩
        have h1 := pow_orderOf_eq_one z
        rw [hk] at h1
        exact congrArg Subtype.val h1
      have hna : ∃ a ∈ ((Rb : Subgroup Y) ⊓ K), ∃ b ∈ ((Rb : Subgroup Y) ⊓ K),
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
      have hTcard : Nat.card ((Rb : Subgroup Y) ⊓ K : Subgroup Y) = p ^ 3 := by
        rw [← hT₀, Subgroup.card_map_of_injective K.subtype_injective, hcard]
      have hCcyc := KlingenIdentLieAux.isCyclic_centralizer hred hK hKn hcent
      have hCT : Subgroup.centralizer (K : Set Y) ≤
          Subgroup.centralizer (((Rb : Subgroup Y) ⊓ K : Subgroup Y) : Set _) :=
        Subgroup.centralizer_le (fun _ hy => hy.2)
      have hΩ : ∀ c ∈ Subgroup.centralizer (K : Set Y),
          c ^ p = 1 → c ∈ ((Rb : Subgroup Y) ⊓ K) := by
        intro c hc hcp
        by_cases hc1 : c = 1
        · rw [hc1]; exact Subgroup.one_mem _
        · have hord : orderOf c = p := orderOf_eq_prime hcp hc1
          exact ⟨hCR hc, Subgroup.map_subtype_le _ (hcent c ⟨hCR hc, hc⟩ hord)⟩
      have h2' := hS2 _ p _ _ hTcard hna hCcyc hCT hΩ
      have h3 := hred.three_le_pRank.trans
        (PreuniquenessRankFour.Helpers.pRank_mono p hp (le_inf_sup_centralizer hCR hRK))
      omega

@[expose] def RankData (X : Type) [Group X] [Finite X] (p : ℕ) [Fact p.Prime] : Prop :=
  ¬ p ^ 3 ∣ Nat.card X ∨ (¬ p ^ 4 ∣ Nat.card X ∧ HasNoncommPair p X ∧ KernelTrivialAt X p)

theorem false_of_rankData (hred : ReducedNongeneration p Y Rb Y₀) (hK : IsComponentOf K ⊤)
    (huniq : ∀ L : Subgroup Y, IsComponentOf L ⊤ → L = K)
    (hcent : ∀ c ∈ (Rb : Subgroup Y) ⊓ Subgroup.centralizer (K : Set Y), orderOf c = p →
      c ∈ (Subgroup.center K).map K.subtype)
    [Finite (Outer K)] (hOut : ¬ p ∣ Nat.card (Outer K)) (hS2 : S2Lemma) {X : Type} [Group X]
    [Finite X] (hX : RankData X p) (e : K ⧸ Subgroup.center K ≃* X) : False := by
  have hp : p.Prime := Fact.out
  have : Group.IsPerfect K := ⟨hK.2.2.1⟩
  have hZp := KlingenIdentLieAux.isPGroup_center hred hK
  have hZc := ReducedNongeneration.isCyclic_center_of_unique hred hK huniq
  obtain ⟨π, hπ, hker⟩ := exists_surjective_ker_eq_center e
  have hiso : Subgroup.center K = ⊥ → K ≃* X := fun hZ =>
    MulEquiv.ofBijective π ⟨(MonoidHom.ker_eq_bot_iff π).mp (hker.trans hZ), hπ⟩
  refine false_of_rank_two hred hK huniq hcent hOut hS2 ?_
  rcases hX with h3 | ⟨h4, hpair, hkt⟩
  · exact fun T => pRank_le_two_of_not_dvd_card hZp hZc (by rwa [Nat.card_congr e.toEquiv]) T
  · have hZ := center_eq_bot_of_kernelTrivialAt hkt e hZp
    exact fun T => ⟨pRank_sylow_le_two_of_mulEquiv hp (hiso hZ)
      (pRank_le_two_of_hasNoncommPair hp h4 hpair) T, Or.inl hZ⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.KlingenIdentSporAux
