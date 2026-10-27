module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def TheoremD2 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ M : Subgroup G, rankThreeIsMaxTwoLocal M →
    (∀ p ∈ rankThreeSigmaA G, ∀ P : Sylow p G, IsCoreMaxLocal p P M →
      rankThreeGamma 2 p (P : Subgroup G) ≤ M) →
    (3 ∈ rankThreeSigmaA G → ∀ P : Sylow 3 G, IsCoreMaxLocal 3 P M →
      (∀ Q : Subgroup G, Q ≤ P → Q ≠ ⊥ →
          3 ≤ pRank 3 (Q ⊔ ((P : Subgroup G) ⊓ centralizer (Q : Set G))) →
          normalizer (Q : Set G) ≤ M) ∧
        (¬ Group.IsSolvable M → rankThreeGamma 1 3 (P : Subgroup G) ≤ M)) →
    ∀ p ∈ rankThreeSigmaA G, ∀ P : Sylow p G, IsCoreMaxLocal p P M →
      ∀ H R : Subgroup G, IsTwoLocal H → R ≤ H → R ≤ M → IsPGroup p R → ¬ IsCyclic R →
        rankThreeGamma 1 p R ≤ M → H ≤ M

@[expose] def NonStrongEmbeddingCase (G : Type) [Group G] [Finite G] : Prop :=
  (∃ p ∈ rankThreeSigmaA G, ∃ (P : Sylow p G) (M : Subgroup G), IsCoreMaxLocal p P M ∧
      ¬ rankThreeGamma 1 p (P : Subgroup G) ≤ M) →
    AlmostStrongEmbedding G ∧ TheoremE G

private theorem one_le_pRank_of_isPGroup_of_ne_bot {q : ℕ} (hq : q.Prime) {Q : Subgroup G}
    (hQ : IsPGroup q Q) (hne : Q ≠ ⊥) : 1 ≤ CFSG.Open.pRank q Q := by
  have : Fact q.Prime := ⟨hq⟩
  have hdvd : q ∣ Nat.card Q :=
    hQ.card_eq_or_dvd.resolve_left fun h => hne (Subgroup.card_eq_one.mp h)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' q hdvd
  have hx' : orderOf (x : G) = q := (Subgroup.orderOf_coe x).trans hx
  unfold CFSG.Open.pRank
  refine le_csSup (pRank_set_bddAbove q hq.one_lt Q)
    ⟨Subgroup.zpowers (x : G), Subgroup.zpowers_le.mpr x.2, ⟨inferInstance, fun y hy => ?_⟩, ?_⟩
  · obtain ⟨i, rfl⟩ := hy
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hx', pow_orderOf_eq_one,
      one_zpow]
  · rw [Nat.card_zpowers, hx', pow_one]

theorem eq_three_of_three_mem_sigmaA (hrank : evenRank G = 3) (h3 : 3 ∈ rankThreeSigmaA G)
    {p : ℕ} (hp : p ∈ rankThreeSigmaA G) : p = 3 := by
  classical
  have hupper := rankThreeLocalRank_le_evenRank (G := G) 3 Nat.prime_three (by norm_num)
  dsimp only [rankThreeSigmaA] at h3 hp
  split_ifs at h3 hp with h₁ h₂ h₃
  · exact absurd h3.2.2.2 (by omega)
  · exact absurd h3.2.1 (by norm_num)
  · exact absurd h3.2.1 (by norm_num)
  · by_contra hne
    have h2p := hp.1.two_le
    have hp2 := hp.2.1
    refine h₃ ⟨p, ?_⟩
    simp only [Set.mem_ofPred_eq]
    exact ⟨hp.1, by omega, hp.2.2.1, hp.2.2.2⟩

theorem gamma_one_le_of_isPGroup (hS : Setting G) {p : ℕ} (hp : p ∈ rankThreeSigmaA G)
    {P : Sylow p G} {M : Subgroup G} (hM : IsCoreMaxLocal p P M)
    (hΓ : rankThreeGamma 1 p (P : Subgroup G) ≤ M) {R : Subgroup G} (hRp : IsPGroup p R)
    (hRM : R ≤ M) : rankThreeGamma 1 p R ≤ M := by
  have hprime : p.Prime := sigmaA_prime p hp
  obtain ⟨hPM, -⟩ := sylow_le_of_isCoreMaxLocal hS hp hM
  obtain ⟨m, hm⟩ := pGroup_conjugate_into_sylow_within_overgroup p hprime P M hPM R hRp hRM
  refine (gamma_le_iff 1 p R M).mpr fun Q hQR hQrank g hg => ?_
  have hnormalizer : normalizer ((Q.map (MulAut.conj (m : G)).toMonoidHom : Subgroup G) :
      Set G) ≤ M :=
    (gamma_normalizer_le 1 p (P : Subgroup G) _ ((map_mono hQR).trans hm)
      (by rwa [pRank_map_automorphism p hprime.one_lt])).trans hΓ
  have himage : MulAut.conj (m : G) g ∈ M := by
    apply hnormalizer
    rw [← map_equiv_normalizer_eq Q (MulAut.conj (m : G))]
    exact mem_map_of_mem _ hg
  have hproduct := M.mul_mem (M.mul_mem (M.inv_mem m.property) himage) m.property
  simpa [MulAut.conj_apply, mul_assoc] using hproduct

theorem le_of_two_le_pRank_of_gamma_one_le (hS : Setting G) (hD2 : TheoremD2 G)
    (hU0 : FullCoreLocal G) {p : ℕ} (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G}
    {M : Subgroup G} (hM : IsCoreMaxLocal p P M) (hΓ : rankThreeGamma 1 p (P : Subgroup G) ≤ M)
    {H : Subgroup G} (hH : IsTwoLocal H) (h2 : 2 ≤ CFSG.Open.pRank p (H ⊓ M)) : H ≤ M := by
  have hprime : p.Prime := sigmaA_prime p hp
  obtain ⟨R, hRHM, hRelem, hRcard⟩ := pRank_attained p (H ⊓ M) (by omega)
  have hRp : IsPGroup p R := elementary_isPGroup p R hRelem
  have hRnc : ¬ IsCyclic R := by
    intro hcyclic
    obtain ⟨g, hg⟩ := hcyclic.exists_generator
    have hdvd : p ^ CFSG.Open.pRank p (H ⊓ M) ∣ p := by
      rw [← hRcard, ← orderOf_eq_card_of_forall_mem_zpowers hg]
      exact orderOf_dvd_of_pow_eq_one (Subtype.ext (hRelem.2 g g.2))
    have hle := (Nat.pow_le_pow_right hprime.pos h2).trans (Nat.le_of_dvd hprime.pos hdvd)
    nlinarith [hprime.two_le]
  have hRM : R ≤ M := hRHM.trans inf_le_right
  refine hD2 M hM.1 (fun p' hp' P' hM' => hU0 p' hp' P' M hM') (fun h3 P₃ hM₃ => ?_) p hp P hM
    H R hH (hRHM.trans inf_le_left) hRM hRp hRnc (gamma_one_le_of_isPGroup hS hp hM hΓ hRp hRM)
  obtain rfl := eq_three_of_three_mem_sigmaA hS.rank h3 hp
  have hΓ₃ := gamma_one_le_of_isPGroup hS hp hM hΓ P₃.isPGroup'
    (sylow_le_of_isCoreMaxLocal hS h3 hM₃).1
  exact ⟨fun Q hQP hQne _ => (gamma_normalizer_le 1 3 (P₃ : Subgroup G) Q hQP
    (one_le_pRank_of_isPGroup_of_ne_bot Nat.prime_three (P₃.isPGroup'.to_le hQP) hQne)).trans
      hΓ₃, fun _ => hΓ₃⟩

theorem almostStrongEmbedding_and_theoremE_of_strongEmbedding (hS : Setting G)
    (hD2 : TheoremD2 G) (hU0 : FullCoreLocal G)
    (hstrong : ∀ p ∈ rankThreeSigmaA G, ∀ (P : Sylow p G) (M : Subgroup G),
      IsCoreMaxLocal p P M → rankThreeGamma 1 p (P : Subgroup G) ≤ M) :
    AlmostStrongEmbedding G ∧ TheoremE G :=
  ⟨fun p hp P M hM => Or.inl (hstrong p hp P M hM), fun p hp P M hM _ hH h2 =>
    le_of_two_le_pRank_of_gamma_one_le hS hD2 hU0 hp hM (hstrong p hp P M hM) hH h2⟩

theorem rankThreeUC_of_steps (hS : Setting G) (hD2 : TheoremD2 G) (hU0 : FullCoreLocal G)
    (hnon : NonStrongEmbeddingCase G) : rankThreeUC G := by
  by_cases hstrong : ∀ p ∈ rankThreeSigmaA G, ∀ (P : Sylow p G) (M : Subgroup G),
      IsCoreMaxLocal p P M → rankThreeGamma 1 p (P : Subgroup G) ≤ M
  · obtain ⟨hU1, hU2⟩ := almostStrongEmbedding_and_theoremE_of_strongEmbedding hS hD2 hU0 hstrong
    exact rankThreeUC_of_parts hS hU0 hU1 hU2
  · push Not at hstrong
    obtain ⟨p, hp, P, M, hM, hfail⟩ := hstrong
    obtain ⟨hU1, hU2⟩ := hnon ⟨p, hp, P, M, hM, hfail⟩
    exact rankThreeUC_of_parts hS hU0 hU1 hU2

end CFSG.LocalAnalysis.RankThreeTheoremC
