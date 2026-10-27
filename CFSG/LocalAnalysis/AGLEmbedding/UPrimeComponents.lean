module

public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockInputs
public import CFSG.LocalAnalysis.AGLEmbedding.PhaseThreeConfig

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers

variable {p : ℕ}

theorem uPrime_component_of_kFact {X : Type} [Group X] [Finite X] (X₀ L : Subgroup X)
    (TL : Sylow p ↥L) (_hp : p.Prime) (_hL : IsComponentOf L ⊤) (hLX₀ : ¬ L ≤ X₀)
    (hk : KFactUPrime p ↥L) (hΓ : GLBCore p 1 (TL : Subgroup ↥L) ≠ ⊤)
    (hΓX₀ : (GLBCore p 1 (TL : Subgroup ↥L)).map L.subtype ≤ X₀) :
    (∀ N : Subgroup X, N ≤ X₀ ⊓ L → (N.subgroupOf (X₀ ⊓ L)).Normal →
        p.Coprime (Nat.card N) → N = ⊥) ∧
      ∀ w : X, w ∈ Subgroup.normalizer (L : Set X) →
        w ∈ Subgroup.centralizer ((X₀ ⊓ L : Subgroup X) : Set X) →
          w ∈ Subgroup.centralizer (L : Set X) := by
  obtain ⟨hmax, hcore, hfix⟩ := hk TL hΓ
  set Γ := GLBCore p 1 (TL : Subgroup ↥L)
  have hΓsub : Γ ≤ X₀.subgroupOf L := fun k hk => hΓX₀ ⟨k, hk, rfl⟩
  have hY : X₀.subgroupOf L = Γ := by
    rcases hmax _ hΓsub with h | h
    · exact h
    · refine absurd (fun x hx => ?_) hLX₀
      have hx' : (⟨x, hx⟩ : L) ∈ X₀.subgroupOf L := h ▸ Subgroup.mem_top _
      exact hx'
  have hmem : ∀ k : L, k ∈ Γ → (k : X) ∈ X₀ ⊓ L := fun k hk =>
    ⟨(by rw [hY]; exact hk : k ∈ X₀.subgroupOf L), k.2⟩
  refine ⟨fun N hN hNn hNp => ?_, fun w hwN hwC => ?_⟩
  ·
    have hNL : N ≤ L := hN.trans inf_le_right
    have hN'Γ : N.subgroupOf L ≤ Γ := fun k hk => by
      rw [← hY]
      exact (hN hk).1
    have hN'n : ((N.subgroupOf L).subgroupOf Γ).Normal :=
      ⟨fun n hn g => hNn.conj_mem ⟨_, hmem _ n.2⟩ hn ⟨_, hmem _ g.2⟩⟩
    have hcard : Nat.card (N.subgroupOf L) = Nat.card N :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNL).toEquiv
    have hbot := hcore _ hN'Γ hN'n (hcard ▸ hNp)
    rw [← Subgroup.map_subgroupOf_eq_of_le hNL, hbot, Subgroup.map_bot]
  ·
    let f : MulAut L := L.normalizerMonoidHom ⟨w, hwN⟩
    have hfk : ∀ k : L, ((f k : L) : X) = w * k * w⁻¹ := fun k => rfl
    have hf : f = 1 := hfix f fun k hk => Subtype.ext (by
      rw [hfk, ← Subgroup.mem_centralizer_iff.mp hwC k (hmem k hk), mul_inv_cancel_right])
    refine Subgroup.mem_centralizer_iff.mpr fun k hk => ?_
    have h1 : w * k * w⁻¹ = k := by
      rw [← hfk ⟨k, hk⟩, hf]
      rfl
    exact (mul_inv_eq_iff_eq_mul.mp h1).symm

theorem glbCore_map_le_of_normalizer_le {X : Type*} [Group X] [Finite X] (hp : p.Prime)
    {X₀ K S : Subgroup X} {T : Subgroup K} (hT : T.map K.subtype = S ⊓ K)
    (hN : ∀ U : Subgroup X, U ≤ S ⊓ K → U ≠ ⊥ → K ⊓ Subgroup.normalizer (U : Set X) ≤ X₀) :
    (GLBCore p 1 T).map K.subtype ≤ X₀ := by
  rw [Subgroup.map_le_iff_le_comap, fullCore_le_iff]
  intro Q hQT hQ1 k hk
  have hQne : Q ≠ ⊥ := by
    rintro rfl
    obtain ⟨E, hE, -, hEcard⟩ := pRank_attained p hp (⊥ : Subgroup K)
    rw [le_bot_iff] at hE
    rw [hE, Subgroup.card_bot] at hEcard
    have h1 := Nat.pow_le_pow_right hp.pos hQ1
    rw [pow_one, ← hEcard] at h1
    exact absurd h1 (by have := hp.one_lt; omega)
  have hU : Q.map K.subtype ≤ S ⊓ K := hT ▸ Subgroup.map_mono hQT
  have hUne : Q.map K.subtype ≠ ⊥ := by
    rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective]
  exact hN _ hU hUne ⟨k.2, Subgroup.le_normalizer_map K.subtype ⟨k, hk, rfl⟩⟩

theorem uPrime_component_of_normalizer_le {X : Type} [Group X] [Finite X] (hp : p.Prime)
    (R : Sylow p X) {X₀ L : Subgroup X} (hL : IsComponentOf L ⊤) (hLX₀ : ¬ L ≤ X₀)
    (hN : ∀ U : Subgroup X, U ≤ (R : Subgroup X) ⊓ L → U ≠ ⊥ →
      L ⊓ Subgroup.normalizer (U : Set X) ≤ X₀)
    (hk : KFactUPrime p ↥L) :
    (∀ N : Subgroup X, N ≤ X₀ ⊓ L → (N.subgroupOf (X₀ ⊓ L)).Normal →
        p.Coprime (Nat.card N) → N = ⊥) ∧
      ∀ w : X, w ∈ Subgroup.normalizer (L : Set X) →
        w ∈ Subgroup.centralizer ((X₀ ⊓ L : Subgroup X) : Set X) →
          w ∈ Subgroup.centralizer (L : Set X) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨T, hT⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal R
    (ComponentClassification.Components.mathlib_subnormal_of_chain hL.2.1
      Subgroup.IsSubnormal.top)
  have hΓX₀ := glbCore_map_le_of_normalizer_le hp hT hN
  refine uPrime_component_of_kFact X₀ L T hp hL hLX₀ hk (fun htop => hLX₀ fun x hx => ?_) hΓX₀
  exact hΓX₀ ⟨⟨x, hx⟩, htop ▸ Subgroup.mem_top _, rfl⟩

theorem uPrimeHyp_of_forall_kFact {X : Type} [Group X] [Finite X] (hp : p.Prime)
    {X₀ : Subgroup X}
    (hU : ∀ L : Subgroup X, IsComponentOf L ⊤ → ¬ L ≤ X₀ → KFactUPrime p ↥L ∧
      ∃ T : Sylow p ↥L, (GLBCore p 1 (T : Subgroup ↥L)).map L.subtype ≤ X₀) :
    UPrimeHyp p X₀ := by
  intro L hL hLX₀
  obtain ⟨hk, T, hΓX₀⟩ := hU L hL hLX₀
  refine uPrime_component_of_kFact X₀ L T hp hL hLX₀ hk (fun htop => hLX₀ fun x hx => ?_) hΓX₀
  exact hΓX₀ ⟨⟨x, hx⟩, htop ▸ Subgroup.mem_top _, rfl⟩

theorem uPrimeHyp_of_normalizer_le {X : Type} [Group X] [Finite X] (hp : p.Prime)
    (R : Sylow p X) {X₀ : Subgroup X}
    (hU : ∀ L : Subgroup X, IsComponentOf L ⊤ → ¬ L ≤ X₀ →
      (∀ U : Subgroup X, U ≤ (R : Subgroup X) ⊓ L → U ≠ ⊥ →
        L ⊓ Subgroup.normalizer (U : Set X) ≤ X₀) ∧ KFactUPrime p ↥L) :
    UPrimeHyp p X₀ := fun L hL hLX₀ =>
  uPrime_component_of_normalizer_le hp R hL hLX₀ (hU L hL hLX₀).1 (hU L hL hLX₀).2

theorem uPrimeHyp_of_forall_ne_le {X : Type} [Group X] [Finite X] (hp : p.Prime) (R : Sylow p X)
    {X₀ K : Subgroup X} (hK : ∀ L : Subgroup X, IsComponentOf L ⊤ → L ≠ K → L ≤ X₀)
    (hN : ∀ U : Subgroup X, U ≤ (R : Subgroup X) ⊓ K → U ≠ ⊥ →
      K ⊓ Subgroup.normalizer (U : Set X) ≤ X₀)
    (hk : KFactUPrime p ↥K) : UPrimeHyp p X₀ := by
  refine uPrimeHyp_of_normalizer_le hp R fun L hL hLX₀ => ?_
  by_cases hLK : L = K
  · subst hLK
    exact ⟨hN, hk⟩
  · exact absurd (hK L hL hLK) hLX₀

theorem eq_of_le_of_card_eq_of_isCyclic {X : Type*} [Group X] [Finite X] {C A B : Subgroup X}
    (hC : IsCyclic C) (hA : A ≤ C) (hB : B ≤ C) (hcard : Nat.card A = Nat.card B) : A = B := by
  have : IsCyclic C := hC
  have h : A.subgroupOf C = B.subgroupOf C := IsCyclic.subgroup_eq_iff_card_eq.mpr (by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB).toEquiv, hcard])
  rw [← Subgroup.map_subgroupOf_eq_of_le hA, ← Subgroup.map_subgroupOf_eq_of_le hB, h]

theorem normalizer_le_normalizer_of_isCyclic {X : Type*} [Group X] [Finite X] (hp : p.Prime)
    {C U U₀ : Subgroup X} (hC : IsCyclic C) (hCp : IsPGroup p C) (hU₀C : U₀ ≤ C)
    (hU₀ : Nat.card U₀ = p) (hUC : U ≤ C) (hU : U ≠ ⊥) :
    Subgroup.normalizer (U : Set X) ≤ Subgroup.normalizer (U₀ : Set X) := by
  have : Fact p.Prime := ⟨hp⟩
  have hdvd : p ∣ Nat.card U := ((hCp.to_le hUC).card_eq_or_dvd).resolve_left
    (fun h1 => hU (Subgroup.card_eq_one.mp h1))
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hV : Subgroup.zpowers (x : X) = U₀ :=
    eq_of_le_of_card_eq_of_isCyclic hC ((Subgroup.zpowers_le.mpr x.2).trans hUC) hU₀C
      (by rw [Nat.card_zpowers, Subgroup.orderOf_coe, hx, hU₀])
  have hU₀U : U₀ ≤ U := hV ▸ Subgroup.zpowers_le.mpr x.2
  intro g hg
  have hgU : U.map (MulAut.conj g).toMonoidHom ≤ U := by
    rintro _ ⟨u, hu, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hg u).mp hu
  refine mem_normalizer_of_conj_map_le (le_of_eq (eq_of_le_of_card_eq_of_isCyclic hC
    ((Subgroup.map_mono hU₀U).trans (hgU.trans hUC)) hU₀C ?_))
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]

theorem uPrimeHyp_of_isCyclic {X : Type} [Group X] [Finite X] (hp : p.Prime) (R : Sylow p X)
    {X₀ : Subgroup X}
    (hU : ∀ L : Subgroup X, IsComponentOf L ⊤ → ¬ L ≤ X₀ →
      IsCyclic ((R : Subgroup X) ⊓ L : Subgroup X) ∧
        (∃ U₀ : Subgroup X, U₀ ≤ (R : Subgroup X) ⊓ L ∧ Nat.card U₀ = p ∧
          L ⊓ Subgroup.normalizer (U₀ : Set X) ≤ X₀) ∧ KFactUPrime p ↥L) :
    UPrimeHyp p X₀ := by
  refine uPrimeHyp_of_normalizer_le hp R fun L hL hLX₀ => ?_
  obtain ⟨hcyc, ⟨U₀, hU₀, hU₀p, hNU₀⟩, hk⟩ := hU L hL hLX₀
  exact ⟨fun U hUR hU1 => (inf_le_inf_left L (normalizer_le_normalizer_of_isCyclic hp hcyc
    (R.isPGroup'.to_le inf_le_left) hU₀ hU₀p hUR hU1)).trans hNU₀, hk⟩

theorem ReducedNongeneration.uPrimeHyp_of_rankOne {X : Type} [Group X] [Finite X]
    {R : Sylow p X} {X₀ : Subgroup X} (h : ReducedNongeneration p X R X₀) {K : Subgroup X}
    (hK : IsComponentOf K ⊤) (hnc : ¬ IsCyclic ((R : Subgroup X) ⊓ K : Subgroup X)) {z : X}
    (hzR : z ∈ (R : Subgroup X)) (hzK : z ∉ K) (hzp : orderOf z = p)
    (hzc : z ∈ Subgroup.centralizer (K : Set X)) (hk : KFactUPrime p ↥K) : UPrimeHyp p X₀ :=
  uPrimeHyp_of_forall_ne_le h.prime R
    (fun _ hL hLK => h.le_of_ne_component hL hK hLK (two_le_pRank_of_isPGroup_not_isCyclic
      h.prime h.ne_two (R.isPGroup'.to_le inf_le_left) hnc))
    (h.rankOne_principle hK hnc hzR hzK hzp hzc).1 hk

section Config

variable {G : Type} [Group G] [Finite G] {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (↥H ⧸ primeComplementCore (G := H) p)}

theorem D1ComponentConfig.toPhaseThree_of_forall_kFact
    (hcfg : D1ComponentConfig p P M H R Rbar)
    (hU : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ →
      ¬ L ≤ ((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) →
      KFactUPrime p ↥L ∧ ∃ T : Sylow p ↥L, (GLBCore p 1 (T : Subgroup ↥L)).map L.subtype ≤
        ((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p))) :
    D1PhaseThree p P M H R :=
  hcfg.toPhaseThree (uPrimeHyp_of_forall_kFact hcfg.red.prime hU)

theorem D1ComponentConfig.toPhaseThree_of_rankOne (hcfg : D1ComponentConfig p P M H R Rbar)
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hK : IsComponentOf K ⊤)
    (hnc : ¬ IsCyclic ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
      Subgroup (H ⧸ primeComplementCore (G := H) p)))
    (hz : ∃ z ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)), z ∉ K ∧ orderOf z = p ∧
      z ∈ Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)))
    (hk : KFactUPrime p ↥K) : D1PhaseThree p P M H R := by
  obtain ⟨z, hzR, hzK, hzp, hzc⟩ := hz
  exact hcfg.toPhaseThree (hcfg.red.uPrimeHyp_of_rankOne hK hnc hzR hzK hzp hzc hk)

theorem D1ComponentConfig.toPhaseThree_of_isCyclic (hcfg : D1ComponentConfig p P M H R Rbar)
    (hcyc : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ →
      IsCyclic ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ L :
        Subgroup (H ⧸ primeComplementCore (G := H) p)))
    (hU : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ →
      ¬ L ≤ ((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) →
      (∃ U₀ : Subgroup (H ⧸ primeComplementCore (G := H) p),
        U₀ ≤ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ L ∧ Nat.card U₀ = p ∧
        L ⊓ Subgroup.normalizer (U₀ : Set (H ⧸ primeComplementCore (G := H) p)) ≤
          ((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p))) ∧
      KFactUPrime p ↥L) :
    D1PhaseThree p P M H R :=
  hcfg.toPhaseThree (uPrimeHyp_of_isCyclic hcfg.red.prime Rbar fun L hL hLX₀ =>
    ⟨hcyc L hL, hU L hL hLX₀⟩)

theorem D1ComponentConfig.toPhaseThree_of_unique (hcfg : D1ComponentConfig p P M H R Rbar)
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}
    (huniq : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ → L = K)
    (hN : ∀ U : Subgroup (H ⧸ primeComplementCore (G := H) p),
      U ≤ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K → U ≠ ⊥ →
      K ⊓ Subgroup.normalizer (U : Set (H ⧸ primeComplementCore (G := H) p)) ≤
        ((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)))
    (hk : KFactUPrime p ↥K) : D1PhaseThree p P M H R :=
  hcfg.toPhaseThree (uPrimeHyp_of_forall_ne_le hcfg.red.prime Rbar
    (fun L hL hLK => absurd (huniq L hL) hLK) hN hk)

end Config

end CFSG.AGLEmbedding
