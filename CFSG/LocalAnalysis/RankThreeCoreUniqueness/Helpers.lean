module

public import CFSG.Mathlib.GroupTheory.Basic
public import CFSG.Open.RankThreeDefs
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LocalAnalysis.SectionRank.SubgroupRank

public section

open CFSG.Open
open CFSG.Open

namespace CFSG.RankThreeCoreUniqueness.Helpers

theorem nat_sSup_mem_of_pos (values : Set ℕ) (hpos : 0 < sSup values) :
    sSup values ∈ values := by
  classical
  have hnonempty : values.Nonempty := by
    by_contra hempty
    have heq : values = ∅ := Set.not_nonempty_iff_eq_empty.mp hempty
    simp [heq] at hpos
  have hbounded : BddAbove values := by
    by_contra hunbounded
    rw [Nat.sSup_of_not_bddAbove hunbounded] at hpos
    omega
  exact Nat.sSup_mem hnonempty hbounded

variable {G : Type*} [Group G] [Finite G]

theorem pRank_set_bddAbove (prime : ℕ) (hprime : 1 < prime) (ambient : Subgroup G) :
    BddAbove {rank : ℕ | ∃ elementary : Subgroup G, elementary ≤ ambient ∧
      IsElemAbelian prime elementary ∧ Nat.card elementary = prime ^ rank} :=
  CFSG.SectionRank.pRank_bddAbove hprime ambient

theorem pRank_le_card (prime : ℕ) (hprime : 1 < prime) (ambient : Subgroup G) :
    pRank prime ambient ≤ Nat.card G := CFSG.SectionRank.pRank_le_card_of_one_lt hprime ambient

theorem pRank_mono (prime : ℕ) (hprime : 1 < prime)
    {smaller larger : Subgroup G} (hinclusion : smaller ≤ larger) :
    pRank prime smaller ≤ pRank prime larger := CFSG.SectionRank.pRank_mono hprime hinclusion

theorem pRank_attained (prime : ℕ) (ambient : Subgroup G)
    (hpositive : 0 < pRank prime ambient) :
    ∃ elementary : Subgroup G, elementary ≤ ambient ∧ IsElemAbelian prime elementary ∧
      Nat.card elementary = prime ^ pRank prime ambient := by
  exact nat_sSup_mem_of_pos _ hpositive

theorem prime_dvd_card_of_pRank_pos (prime : ℕ) (ambient : Subgroup G)
    (hpositive : 0 < pRank prime ambient) : prime ∣ Nat.card G := by
  obtain ⟨elementary, _, _, hcard⟩ := pRank_attained prime ambient hpositive
  have hdivides : prime ∣ Nat.card elementary := by
    rw [hcard]
    obtain ⟨rank, hrank⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpositive)
    rw [hrank, pow_succ]
    exact dvd_mul_left prime (prime ^ rank)
  exact hdivides.trans elementary.card_subgroup_dvd_card

theorem evenRank_set_bddAbove :
    BddAbove {rank : ℕ | ∃ (prime : ℕ) (localGroup : Subgroup G),
      prime.Prime ∧ prime ≠ 2 ∧ IsTwoLocal localGroup ∧ pRank prime localGroup = rank} := by
  refine ⟨Nat.card G, ?_⟩
  rintro rank ⟨prime, localGroup, hprime, _, _, hrank⟩
  rw [← hrank]
  exact pRank_le_card prime hprime.one_lt localGroup

theorem local_pRank_le_evenRank (prime : ℕ) (hprime : prime.Prime) (hodd : prime ≠ 2)
    (localGroup : Subgroup G) (hlocal : IsTwoLocal localGroup) :
    pRank prime localGroup ≤ evenRank G := by
  exact le_csSup evenRank_set_bddAbove ⟨prime, localGroup, hprime, hodd, hlocal, rfl⟩

theorem rankThreeLocalRank_le_evenRank (prime : ℕ) (hprime : prime.Prime)
    (hodd : prime ≠ 2) : rankThreeLocalRank prime G ≤ evenRank G := by
  unfold rankThreeLocalRank CFSG.Open.twoLocalPrimeRank
  apply csSup_le'
  rintro rank ⟨localGroup, hlocal, hrank⟩
  rw [← hrank]
  exact local_pRank_le_evenRank prime hprime hodd localGroup hlocal

theorem local_pRank_le_localRank (prime : ℕ) (hprime : 1 < prime)
    (localGroup : Subgroup G) (hlocal : IsTwoLocal localGroup) :
    pRank prime localGroup ≤ rankThreeLocalRank prime G := by
  unfold rankThreeLocalRank CFSG.Open.twoLocalPrimeRank
  refine le_csSup ?_ (show pRank prime localGroup ∈
    {rank : ℕ | ∃ otherLocalGroup : Subgroup G,
      IsTwoLocal otherLocalGroup ∧ pRank prime otherLocalGroup = rank} from
    ⟨localGroup, hlocal, rfl⟩)
  refine ⟨Nat.card G, ?_⟩
  rintro rank ⟨otherLocalGroup, _, hrank⟩
  rw [← hrank]
  exact pRank_le_card prime hprime otherLocalGroup

theorem evenRank_attained (hpositive : 0 < evenRank G) :
    ∃ (prime : ℕ) (localGroup : Subgroup G), prime.Prime ∧ prime ≠ 2 ∧
      IsTwoLocal localGroup ∧ pRank prime localGroup = evenRank G := by
  exact nat_sSup_mem_of_pos _ hpositive

theorem rankThreeLocalRank_attained (prime : ℕ)
    (hpositive : 0 < rankThreeLocalRank prime G) :
    ∃ localGroup : Subgroup G, IsTwoLocal localGroup ∧
      pRank prime localGroup = rankThreeLocalRank prime G := by
  exact nat_sSup_mem_of_pos _ hpositive

theorem exists_odd_prime_local_rank_three (hrank : evenRank G = 3) :
    ∃ prime : ℕ, prime.Prime ∧ prime ≠ 2 ∧ prime ∣ Nat.card G ∧
      rankThreeLocalRank prime G = 3 := by
  have hpositive : 0 < evenRank G := by omega
  obtain ⟨prime, localGroup, hprime, hodd, hlocal, hlocalRank⟩ := evenRank_attained hpositive
  have hlocalPositive : 0 < pRank prime localGroup := by omega
  refine ⟨prime, hprime, hodd, prime_dvd_card_of_pRank_pos prime localGroup hlocalPositive, ?_⟩
  have hlower := local_pRank_le_localRank prime hprime.one_lt localGroup hlocal
  have hupper := rankThreeLocalRank_le_evenRank prime hprime hodd (G := G)
  omega

theorem sigmaA_nonempty_of_evenRank_three (hrank : evenRank G = 3) :
    (rankThreeSigmaA G).Nonempty := by
  classical
  dsimp only [rankThreeSigmaA]
  split_ifs with hfirst hsecond hthird
  · exact hfirst
  · exact hsecond
  · exact hthird
  · exact exists_odd_prime_local_rank_three hrank

theorem sigmaA_prime (prime : ℕ) (hselected : prime ∈ rankThreeSigmaA G) :
    prime.Prime := by
  classical
  dsimp only [rankThreeSigmaA] at hselected
  split_ifs at hselected <;> exact hselected.1

theorem sigmaA_odd (prime : ℕ) (hselected : prime ∈ rankThreeSigmaA G) :
    prime ≠ 2 := by
  classical
  dsimp only [rankThreeSigmaA] at hselected
  split_ifs at hselected
  · exact hselected.2.1
  · have hgreater := hselected.2.1
    omega
  · have hgreater := hselected.2.1
    omega
  · exact hselected.2.1

theorem sigmaA_dvd_card (prime : ℕ) (hselected : prime ∈ rankThreeSigmaA G) :
    prime ∣ Nat.card G := by
  classical
  dsimp only [rankThreeSigmaA] at hselected
  split_ifs at hselected <;> exact hselected.2.2.1

theorem sigmaA_local_rank_three (hrank : evenRank G = 3)
    (prime : ℕ) (hselected : prime ∈ rankThreeSigmaA G) :
    rankThreeLocalRank prime G = 3 := by
  classical
  have hupper := rankThreeLocalRank_le_evenRank (G := G) prime (sigmaA_prime prime hselected)
    (sigmaA_odd prime hselected)
  dsimp only [rankThreeSigmaA] at hselected
  split_ifs at hselected
  · have hgreater := hselected.2.2.2
    omega
  · exact hselected.2.2.2
  · exact hselected.2.2.2
  · exact hselected.2.2.2

theorem sigmaA_global_rank_at_least_three (hrank : evenRank G = 3)
    (prime : ℕ) (hselected : prime ∈ rankThreeSigmaA G) :
    3 ≤ pRank prime (⊤ : Subgroup G) := by
  have hlocalRank := sigmaA_local_rank_three hrank prime hselected
  obtain ⟨localGroup, _, hrankLocal⟩ := rankThreeLocalRank_attained (G := G) prime
    (by omega)
  have hmono := pRank_mono prime (sigmaA_prime prime hselected).one_lt
    (show localGroup ≤ (⊤ : Subgroup G) from le_top)
  omega

theorem aschCore_normalizer_le (threshold prime : ℕ) (sylowGroup generator : Subgroup G)
    (hinclusion : generator ≤ sylowGroup) (hrank : threshold ≤ pRank prime generator)
    (hproductRank : 3 ≤ pRank prime
      (generator ⊔ (sylowGroup ⊓ Subgroup.centralizer (generator : Set G)))) :
    Subgroup.normalizer (generator : Set G) ≤ rankThreeAschCore threshold prime sylowGroup := by
  exact le_sSup ⟨generator, hinclusion, hrank, hproductRank, rfl⟩

theorem aschCore_le_iff (threshold prime : ℕ) (sylowGroup target : Subgroup G) :
    rankThreeAschCore threshold prime sylowGroup ≤ target ↔
      ∀ generator : Subgroup G, generator ≤ sylowGroup → threshold ≤ pRank prime generator →
        3 ≤ pRank prime (generator ⊔
          (sylowGroup ⊓ Subgroup.centralizer (generator : Set G))) →
        Subgroup.normalizer (generator : Set G) ≤ target := by
  constructor
  · intro hcore generator hinclusion hrank hproductRank
    exact (aschCore_normalizer_le threshold prime sylowGroup generator
      hinclusion hrank hproductRank).trans hcore
  · intro hnormalizers
    apply sSup_le
    rintro normalizerGroup ⟨generator, hinclusion, hrank, hproductRank, rfl⟩
    exact hnormalizers generator hinclusion hrank hproductRank

theorem aschCore_antitone_threshold (prime : ℕ) (sylowGroup : Subgroup G)
    {lower upper : ℕ} (hthreshold : lower ≤ upper) :
    rankThreeAschCore upper prime sylowGroup ≤ rankThreeAschCore lower prime sylowGroup := by
  apply (aschCore_le_iff upper prime sylowGroup _).mpr
  intro generator hinclusion hrank hproductRank
  exact aschCore_normalizer_le lower prime sylowGroup generator hinclusion
    (hthreshold.trans hrank) hproductRank

theorem aschCore_mono_group (prime : ℕ) (hprime : 1 < prime) (threshold : ℕ)
    {smaller larger : Subgroup G} (hinclusion : smaller ≤ larger) :
    rankThreeAschCore threshold prime smaller ≤ rankThreeAschCore threshold prime larger := by
  apply (aschCore_le_iff threshold prime smaller _).mpr
  intro generator hgenerator hrank hproductRank
  apply aschCore_normalizer_le threshold prime larger generator (hgenerator.trans hinclusion) hrank
  apply hproductRank.trans
  apply pRank_mono prime hprime
  exact sup_le_sup le_rfl (inf_le_inf hinclusion le_rfl)

theorem gamma_normalizer_le (threshold prime : ℕ) (sylowGroup generator : Subgroup G)
    (hinclusion : generator ≤ sylowGroup) (hrank : threshold ≤ pRank prime generator) :
    Subgroup.normalizer (generator : Set G) ≤ rankThreeGamma threshold prime sylowGroup := by
  exact le_sSup ⟨generator, hinclusion, hrank, rfl⟩

theorem gamma_le_iff (threshold prime : ℕ) (sylowGroup target : Subgroup G) :
    rankThreeGamma threshold prime sylowGroup ≤ target ↔
      ∀ generator : Subgroup G, generator ≤ sylowGroup → threshold ≤ pRank prime generator →
        Subgroup.normalizer (generator : Set G) ≤ target := by
  constructor
  · intro hcore generator hinclusion hrank
    exact (gamma_normalizer_le threshold prime sylowGroup generator hinclusion hrank).trans hcore
  · intro hnormalizers
    apply sSup_le
    rintro normalizerGroup ⟨generator, hinclusion, hrank, rfl⟩
    exact hnormalizers generator hinclusion hrank

theorem aschCore_le_gamma (threshold prime : ℕ) (sylowGroup : Subgroup G) :
    rankThreeAschCore threshold prime sylowGroup ≤ rankThreeGamma threshold prime sylowGroup := by
  apply (aschCore_le_iff threshold prime sylowGroup _).mpr
  intro generator hinclusion hrank _
  exact gamma_normalizer_le threshold prime sylowGroup generator hinclusion hrank

theorem gamma_three_le_aschCore_two (prime : ℕ) (hprime : 1 < prime)
    (sylowGroup : Subgroup G) :
    rankThreeGamma 3 prime sylowGroup ≤ rankThreeAschCore 2 prime sylowGroup := by
  apply (gamma_le_iff 3 prime sylowGroup _).mpr
  intro generator hinclusion hrank
  apply aschCore_normalizer_le 2 prime sylowGroup generator hinclusion (by omega)
  exact hrank.trans (pRank_mono prime hprime le_sup_left)

theorem sylowGroup_le_aschCore (threshold prime : ℕ) (sylowGroup : Subgroup G)
    (hthreshold : threshold ≤ pRank prime sylowGroup) (hrank : 3 ≤ pRank prime sylowGroup) :
    sylowGroup ≤ rankThreeAschCore threshold prime sylowGroup := by
  apply Subgroup.le_normalizer.trans
  apply aschCore_normalizer_le threshold prime sylowGroup sylowGroup le_rfl hthreshold
  have hproduct : sylowGroup ⊔
      (sylowGroup ⊓ Subgroup.centralizer (sylowGroup : Set G)) = sylowGroup :=
    sup_eq_left.mpr inf_le_left
  rw [hproduct]
  exact hrank

theorem coreLocal_antitone_threshold {lower upper : ℕ} (hthreshold : lower ≤ upper)
    (hlocal : rankThreeAschCoreLocal G lower) : rankThreeAschCoreLocal G upper := by
  intro prime hselected sylowGroup
  obtain ⟨localGroup, htwoLocal, hcore⟩ := hlocal prime hselected sylowGroup
  exact ⟨localGroup, htwoLocal,
    (aschCore_antitone_threshold prime (sylowGroup : Subgroup G) hthreshold).trans hcore⟩

omit [Finite G] in
theorem elementary_isPGroup (prime : ℕ) (elementary : Subgroup G)
    (helementary : IsElemAbelian prime elementary) : IsPGroup prime elementary :=
  CFSG.Open.IsElemAbelian.isPGroup helementary

theorem exists_sylow_rank_at_least_three (prime : ℕ) (hprime : prime.Prime)
    (hrank : 3 ≤ pRank prime (⊤ : Subgroup G)) :
    ∃ sylowGroup : Sylow prime G, 3 ≤ pRank prime (sylowGroup : Subgroup G) := by
  obtain ⟨elementary, _, helementary, hcard⟩ := pRank_attained prime (⊤ : Subgroup G) (by omega)
  obtain ⟨sylowGroup, hinclusion⟩ := (elementary_isPGroup prime elementary helementary).exists_le_sylow
  refine ⟨sylowGroup, hrank.trans ?_⟩
  unfold pRank
  exact le_csSup (pRank_set_bddAbove prime hprime.one_lt (sylowGroup : Subgroup G))
    ⟨elementary, hinclusion, helementary, hcard⟩

theorem twoLocal_le_maxTwoLocal (localGroup : Subgroup G) (hlocal : IsTwoLocal localGroup) :
    ∃ maximalLocal : Subgroup G, rankThreeIsMaxTwoLocal maximalLocal ∧ localGroup ≤ maximalLocal := by
  classical
  obtain ⟨maximalLocal, hmaximal⟩ := (Set.toFinite
    {overgroup : Subgroup G | IsTwoLocal overgroup ∧ localGroup ≤ overgroup}).exists_maximal
      ⟨localGroup, hlocal, le_rfl⟩
  refine ⟨maximalLocal, ⟨hmaximal.1.1, ?_⟩, hmaximal.1.2⟩
  intro overgroup hovergroup hinclusion
  exact le_antisymm (hmaximal.2 ⟨hovergroup, hmaximal.1.2.trans hinclusion⟩ hinclusion) hinclusion

theorem not_isPGroup_of_simple_nonabelian [IsSimpleGroup G]
    (hnonabelian : ∃ first second : G, first * second ≠ second * first)
    (prime : ℕ) (hprime : prime.Prime) : ¬ IsPGroup prime G := by
  intro hpGroup
  let : Fact prime.Prime := ⟨hprime⟩
  let : Group.IsNilpotent G := hpGroup.isNilpotent
  let : IsCyclic G := inferInstance
  obtain ⟨first, second, hnoncommute⟩ := hnonabelian
  exact hnoncommute (mul_comm first second)

theorem twoLocal_ne_top [IsSimpleGroup G]
    (hnonabelian : ∃ first second : G, first * second ≠ second * first)
    (localGroup : Subgroup G) (hlocal : IsTwoLocal localGroup) : localGroup ≠ ⊤ := by
  intro htop
  obtain ⟨twoGroup, hnontrivial, htwoGroup, hnormalizer⟩ := hlocal
  have hnormal : twoGroup.Normal := Subgroup.normalizer_eq_top_iff.mp (hnormalizer.symm.trans htop)
  rcases CFSG.eq_bot_or_eq_top_of_normal twoGroup hnormal with hbot | htwoTop
  · exact hnontrivial hbot
  · rw [htwoTop] at htwoGroup
    have hwholeGroup : IsPGroup 2 G := htwoGroup.of_injective
      (Subgroup.topEquiv (G := G)).symm.toMonoidHom
      (Subgroup.topEquiv (G := G)).symm.injective
    exact not_isPGroup_of_simple_nonabelian hnonabelian 2 Nat.prime_two hwholeGroup

theorem selected_coreLocal_has_maximal_overgroup (hrank : evenRank G = 3)
    (hcoreLocal : rankThreeAschCoreLocal G 2) (prime : ℕ)
    (hselected : prime ∈ rankThreeSigmaA G) :
    ∃ (sylowGroup : Sylow prime G) (maximalLocal : Subgroup G),
      3 ≤ pRank prime (sylowGroup : Subgroup G) ∧
      rankThreeIsMaxTwoLocal maximalLocal ∧
      rankThreeAschCore 2 prime (sylowGroup : Subgroup G) ≤ maximalLocal ∧
      Subgroup.normalizer (sylowGroup : Set G) ≤ maximalLocal ∧
      (sylowGroup : Subgroup G) ≤ maximalLocal ∧ pRank prime maximalLocal = 3 := by
  have hprime := sigmaA_prime prime hselected
  have hodd := sigmaA_odd prime hselected
  obtain ⟨sylowGroup, hsylowRank⟩ := exists_sylow_rank_at_least_three prime hprime
    (sigmaA_global_rank_at_least_three hrank prime hselected)
  obtain ⟨localGroup, hlocal, hcore⟩ := hcoreLocal prime hselected sylowGroup
  obtain ⟨maximalLocal, hmaximal, hovergroup⟩ := twoLocal_le_maxTwoLocal localGroup hlocal
  have hcoreMaximal := hcore.trans hovergroup
  have hsylowCore := sylowGroup_le_aschCore 2 prime (sylowGroup : Subgroup G) (by omega) hsylowRank
  have hsylowMaximal := hsylowCore.trans hcoreMaximal
  have hnormalizerMaximal : Subgroup.normalizer (sylowGroup : Set G) ≤ maximalLocal := by
    apply (aschCore_normalizer_le 2 prime (sylowGroup : Subgroup G)
      (sylowGroup : Subgroup G) le_rfl (by omega) ?_).trans hcoreMaximal
    have hproduct : (sylowGroup : Subgroup G) ⊔
        ((sylowGroup : Subgroup G) ⊓
          Subgroup.centralizer ((sylowGroup : Subgroup G) : Set G)) = sylowGroup :=
      sup_eq_left.mpr inf_le_left
    rw [hproduct]
    exact hsylowRank
  refine ⟨sylowGroup, maximalLocal, hsylowRank, hmaximal, hcoreMaximal,
    hnormalizerMaximal, hsylowMaximal, ?_⟩
  have hlower := pRank_mono prime hprime.one_lt hsylowMaximal
  have hupper := local_pRank_le_evenRank prime hprime hodd maximalLocal hmaximal.1
  omega

omit [Finite G] in
theorem elementary_transport {otherGroup : Type*} [Group otherGroup] (prime : ℕ)
    (source : Subgroup G) (target : Subgroup otherGroup) (equivalence : source ≃* target)
    (helementary : IsElemAbelian prime source) : IsElemAbelian prime target := by
  constructor
  · apply isMulCommutative_iff.mpr
    intro first second
    obtain ⟨preFirst, rfl⟩ := equivalence.surjective first
    obtain ⟨preSecond, rfl⟩ := equivalence.surjective second
    rw [← equivalence.map_mul, ← equivalence.map_mul,
      isMulCommutative_iff.mp helementary.1 preFirst preSecond]
  · intro element helement
    obtain ⟨preimage, hpreimage⟩ := equivalence.surjective ⟨element, helement⟩
    have hexponent : preimage ^ prime = 1 := by
      apply Subtype.ext
      exact helementary.2 preimage preimage.property
    have htransported := congrArg equivalence hexponent
    rw [map_pow, map_one, hpreimage] at htransported
    exact congrArg Subtype.val htransported

omit [Finite G] in
theorem elementary_map_injective {otherGroup : Type*} [Group otherGroup] (prime : ℕ)
    (elementary : Subgroup G) (homomorphism : G →* otherGroup)
    (_hinjective : Function.Injective homomorphism)
    (helementary : IsElemAbelian prime elementary) :
    IsElemAbelian prime (elementary.map homomorphism) :=
  CFSG.SectionRank.isElemAbelian_map helementary homomorphism

theorem pRank_le_of_subgroup_equiv (prime : ℕ) (hprime : 1 < prime)
    (source target : Subgroup G) (equivalence : source ≃* target) :
    pRank prime source ≤ pRank prime target := by
  unfold pRank
  apply csSup_le'
  rintro rank ⟨elementary, hinclusion, helementary, hcard⟩
  let restricted : Subgroup source := elementary.subgroupOf source
  let homomorphism : source →* G := target.subtype.comp equivalence.toMonoidHom
  have hinjective : Function.Injective homomorphism :=
    target.subtype_injective.comp equivalence.injective
  have hrestricted : IsElemAbelian prime restricted :=
    elementary_transport prime elementary restricted
      (Subgroup.subgroupOfEquivOfLe hinclusion).symm helementary
  have hrestrictedCard : Nat.card restricted = Nat.card elementary :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hinclusion).toEquiv
  have himage : restricted.map homomorphism ≤ target := by
    rintro element ⟨preimage, _, rfl⟩
    exact (equivalence preimage).property
  apply le_csSup (pRank_set_bddAbove prime hprime target)
  refine ⟨restricted.map homomorphism, himage,
    elementary_map_injective prime restricted homomorphism hinjective hrestricted, ?_⟩
  rw [Subgroup.card_map_of_injective hinjective, hrestrictedCard, hcard]

theorem pRank_eq_of_subgroup_equiv (prime : ℕ) (hprime : 1 < prime)
    (source target : Subgroup G) (equivalence : source ≃* target) :
    pRank prime source = pRank prime target := by
  exact le_antisymm (pRank_le_of_subgroup_equiv prime hprime source target equivalence)
    (pRank_le_of_subgroup_equiv prime hprime target source equivalence.symm)

theorem sylow_pRank_eq (prime : ℕ) (hprime : prime.Prime)
    (firstSylow secondSylow : Sylow prime G) :
    pRank prime (firstSylow : Subgroup G) = pRank prime (secondSylow : Subgroup G) := by
  let : Fact prime.Prime := ⟨hprime⟩
  exact pRank_eq_of_subgroup_equiv prime hprime.one_lt
    (firstSylow : Subgroup G) (secondSylow : Subgroup G) (firstSylow.equiv secondSylow)

theorem selected_sylow_rank_at_least_three (hrank : evenRank G = 3)
    (prime : ℕ) (hselected : prime ∈ rankThreeSigmaA G) (sylowGroup : Sylow prime G) :
    3 ≤ pRank prime (sylowGroup : Subgroup G) := by
  obtain ⟨rankThreeSylow, hlarge⟩ := exists_sylow_rank_at_least_three prime
    (sigmaA_prime prime hselected) (sigmaA_global_rank_at_least_three hrank prime hselected)
  rw [← sylow_pRank_eq prime (sigmaA_prime prime hselected) rankThreeSylow sylowGroup]
  exact hlarge

theorem selected_coreLocal_all_sylows_have_maximal_overgroup (hrank : evenRank G = 3)
    (hcoreLocal : rankThreeAschCoreLocal G 2) (prime : ℕ)
    (hselected : prime ∈ rankThreeSigmaA G) (sylowGroup : Sylow prime G) :
    ∃ maximalLocal : Subgroup G, rankThreeIsMaxTwoLocal maximalLocal ∧
      rankThreeAschCore 2 prime (sylowGroup : Subgroup G) ≤ maximalLocal ∧
      Subgroup.normalizer (sylowGroup : Set G) ≤ maximalLocal ∧
      (sylowGroup : Subgroup G) ≤ maximalLocal ∧
      pRank prime (sylowGroup : Subgroup G) = 3 ∧ pRank prime maximalLocal = 3 := by
  have hprime := sigmaA_prime prime hselected
  have hsylowRank := selected_sylow_rank_at_least_three hrank prime hselected sylowGroup
  obtain ⟨localGroup, hlocal, hcore⟩ := hcoreLocal prime hselected sylowGroup
  obtain ⟨maximalLocal, hmaximal, hovergroup⟩ := twoLocal_le_maxTwoLocal localGroup hlocal
  have hcoreMaximal := hcore.trans hovergroup
  have hsylowMaximal := (sylowGroup_le_aschCore 2 prime (sylowGroup : Subgroup G)
    (by omega) hsylowRank).trans hcoreMaximal
  have hnormalizerMaximal : Subgroup.normalizer (sylowGroup : Set G) ≤ maximalLocal := by
    apply (aschCore_normalizer_le 2 prime (sylowGroup : Subgroup G)
      (sylowGroup : Subgroup G) le_rfl (by omega) ?_).trans hcoreMaximal
    have hproduct : (sylowGroup : Subgroup G) ⊔
        ((sylowGroup : Subgroup G) ⊓
          Subgroup.centralizer ((sylowGroup : Subgroup G) : Set G)) = sylowGroup :=
      sup_eq_left.mpr inf_le_left
    rw [hproduct]
    exact hsylowRank
  have hlower := pRank_mono prime hprime.one_lt hsylowMaximal
  have hupper := local_pRank_le_evenRank prime hprime (sigmaA_odd prime hselected)
    maximalLocal hmaximal.1
  exact ⟨maximalLocal, hmaximal, hcoreMaximal, hnormalizerMaximal, hsylowMaximal,
    by omega, by omega⟩

end CFSG.RankThreeCoreUniqueness.Helpers
