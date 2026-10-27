module

public import CFSG.Open.GLBDefs
import CFSG.LocalAnalysis.SectionRank.SubgroupRank

public section

open CFSG.Open
open CFSG.Open

namespace CFSG.PreuniquenessRankFour.Helpers

universe u

variable {G : Type u} [Group G] [Finite G]

theorem pRank_bddAbove (p : ℕ) (hp : p.Prime) (H : Subgroup G) :
    BddAbove {rank | ∃ E : Subgroup G, E ≤ H ∧ IsElemAbelian p E ∧
      Nat.card E = p ^ rank} := by
  refine ⟨Nat.card G, ?_⟩
  rintro rank ⟨E, _, _, hcard⟩
  exact (Nat.lt_pow_self hp.one_lt).le.trans
    (hcard ▸ E.card_le_card_group)

theorem pRank_le_card (p : ℕ) (hp : p.Prime) (H : Subgroup G) :
    pRank p H ≤ Nat.card G := CFSG.SectionRank.pRank_le_card_of_one_lt hp.one_lt H

omit [Finite G] in
theorem pRank_nonempty (p : ℕ) (H : Subgroup G) :
    {rank | ∃ E : Subgroup G, E ≤ H ∧ IsElemAbelian p E ∧
      Nat.card E = p ^ rank}.Nonempty := by
  refine ⟨0, ⊥, bot_le, ?_, ?_⟩
  · refine ⟨inferInstance, ?_⟩
    intro element helement
    simp only [Subgroup.mem_bot] at helement
    simp [helement]
  · simp

theorem pRank_attained (p : ℕ) (hp : p.Prime) (H : Subgroup G) :
    ∃ E : Subgroup G, E ≤ H ∧ IsElemAbelian p E ∧ Nat.card E = p ^ pRank p H :=
  CFSG.SectionRank.exists_pRank hp.one_lt H

theorem pRank_mono (p : ℕ) (hp : p.Prime) {H K : Subgroup G} (hHK : H ≤ K) :
    pRank p H ≤ pRank p K := CFSG.SectionRank.pRank_mono hp.one_lt hHK

theorem twoLocalRank_bddAbove (p : ℕ) (hp : p.Prime) :
    BddAbove {rank | ∃ H : Subgroup G, IsTwoLocal H ∧ pRank p H = rank} := by
  refine ⟨Nat.card G, ?_⟩
  rintro rank ⟨H, _, rfl⟩
  exact pRank_le_card p hp H

theorem twoLocalRank_le_globalRank (p : ℕ) (hp : p.Prime) :
    GLBTwoLocalRank p G ≤ pRank p (⊤ : Subgroup G) := by
  apply csSup_le'
  rintro rank ⟨H, _, rfl⟩
  exact pRank_mono p hp le_top

theorem evenRank_bddAbove :
    BddAbove {rank | ∃ (p : ℕ) (H : Subgroup G), p.Prime ∧ p ≠ 2 ∧
      IsTwoLocal H ∧ pRank p H = rank} := by
  refine ⟨Nat.card G, ?_⟩
  rintro rank ⟨p, H, hp, _, _, rfl⟩
  exact pRank_le_card p hp H

theorem evenRank_attained (hpositive : 0 < evenRank G) :
    ∃ (p : ℕ) (H : Subgroup G), p.Prime ∧ p ≠ 2 ∧ IsTwoLocal H ∧
      pRank p H = evenRank G := by
  apply Nat.sSup_mem _ evenRank_bddAbove
  by_contra hempty
  have hset : {rank | ∃ (p : ℕ) (H : Subgroup G), p.Prime ∧ p ≠ 2 ∧
      IsTwoLocal H ∧ pRank p H = rank} = ∅ := Set.not_nonempty_iff_eq_empty.mp hempty
  have hzero : evenRank G = 0 := by
    change sSup {rank | ∃ (p : ℕ) (H : Subgroup G), p.Prime ∧ p ≠ 2 ∧
      IsTwoLocal H ∧ pRank p H = rank} = 0
    rw [hset]
    exact csSup_empty
  omega

theorem prime_dvd_card_of_positive_rank (p : ℕ) (hp : p.Prime) (H : Subgroup G)
    (hpositive : 0 < pRank p H) : p ∣ Nat.card G := by
  obtain ⟨E, _, _, hcard⟩ := pRank_attained p hp H
  have hpower : p ∣ p ^ pRank p H := dvd_pow_self p (Nat.ne_of_gt hpositive)
  exact (hcard ▸ hpower).trans E.card_subgroup_dvd_card

theorem betaFour_nonempty (he : 4 ≤ evenRank G) : (GLBBetaFour G).Nonempty := by
  obtain ⟨p, H, hp, hodd, hlocal, hrank⟩ := evenRank_attained (G := G) (by omega)
  refine ⟨p, hp, hodd, ?_, ?_⟩
  · apply prime_dvd_card_of_positive_rank p hp H
    omega
  · exact he.trans (le_csSup (twoLocalRank_bddAbove p hp)
      ⟨H, hlocal, hrank⟩)

theorem betaFour_globalRank {p : ℕ} (hp : p ∈ GLBBetaFour G) :
    4 ≤ pRank p (⊤ : Subgroup G) := by
  exact hp.2.2.2.trans (twoLocalRank_le_globalRank p hp.1)

theorem exclusion_iff_not_preuniqueness :
    (∃ p ∈ GLBBetaFour G, ¬ GLBWeakCoreLocal G p) ↔ ¬ GLBPreuniqueness G := by
  classical
  simp only [GLBPreuniqueness, not_forall]
  simp

theorem weakCoreLocal_iff_of_betaFour {p : ℕ} (hp : p ∈ GLBBetaFour G) :
    GLBWeakCoreLocal G p ↔ ∀ P : Sylow p G, ∃ H : Subgroup G,
      IsTwoLocal H ∧ GLBWeakCore p (P : Subgroup G) ≤ H := by
  exact and_iff_right (by have := betaFour_globalRank hp; omega)

theorem exclusion_iff_nonlocal_core :
    (∃ p ∈ GLBBetaFour G, ¬ GLBWeakCoreLocal G p) ↔
      ∃ p ∈ GLBBetaFour G, ∃ P : Sylow p G,
        ∀ H : Subgroup G, IsTwoLocal H → ¬ GLBWeakCore p (P : Subgroup G) ≤ H := by
  classical
  constructor
  · rintro ⟨p, hp, hnonlocal⟩
    rw [weakCoreLocal_iff_of_betaFour hp] at hnonlocal
    push Not at hnonlocal
    exact ⟨p, hp, hnonlocal⟩
  · rintro ⟨p, hp, P, hnonlocal⟩
    refine ⟨p, hp, ?_⟩
    rw [weakCoreLocal_iff_of_betaFour hp]
    intro hlocal
    obtain ⟨H, hH, hcore⟩ := hlocal P
    exact hnonlocal H hH hcore

theorem normalizer_le_weakCore (p : ℕ) {P Q : Subgroup G} (hQP : Q ≤ P)
    (hrank : 2 ≤ pRank p Q)
    (hcentral : 3 ≤ pRank p (Q ⊔ (P ⊓ Subgroup.centralizer (Q : Set G)))) :
    Subgroup.normalizer (Q : Set G) ≤ GLBWeakCore p P := by
  exact le_sSup ⟨Q, hQP, hrank, hcentral, rfl⟩

theorem weakCore_le_iff (p : ℕ) (P H : Subgroup G) :
    GLBWeakCore p P ≤ H ↔ ∀ Q : Subgroup G, Q ≤ P → 2 ≤ pRank p Q →
      3 ≤ pRank p (Q ⊔ (P ⊓ Subgroup.centralizer (Q : Set G))) →
      Subgroup.normalizer (Q : Set G) ≤ H := by
  constructor
  · intro hcore Q hQP hrank hcentral
    exact (normalizer_le_weakCore p hQP hrank hcentral).trans hcore
  · intro hnormalizers
    apply sSup_le
    rintro N ⟨Q, hQP, hrank, hcentral, rfl⟩
    exact hnormalizers Q hQP hrank hcentral

theorem weakCore_mono (p : ℕ) (hp : p.Prime) {P R : Subgroup G} (hPR : P ≤ R) :
    GLBWeakCore p P ≤ GLBWeakCore p R := by
  apply (weakCore_le_iff p P (GLBWeakCore p R)).mpr
  intro Q hQP hrank hcentral
  apply normalizer_le_weakCore p (hQP.trans hPR) hrank
  exact hcentral.trans (pRank_mono p hp (sup_le_sup_left (inf_le_inf_right _ hPR) Q))

theorem weakCore_le_fullCore (p : ℕ) (P : Subgroup G) :
    GLBWeakCore p P ≤ GLBCore p 2 P := by
  apply (weakCore_le_iff p P (GLBCore p 2 P)).mpr
  intro Q hQP hrank _
  exact le_sSup ⟨Q, hQP, hrank, rfl⟩

theorem fullCore_le_iff (p rank : ℕ) (P M : Subgroup G) :
    GLBCore p rank P ≤ M ↔ ∀ Q : Subgroup G, Q ≤ P → rank ≤ pRank p Q →
      Subgroup.normalizer (Q : Set G) ≤ M := by
  constructor
  · intro hcore Q hQP hrank
    have hnormalizer : Subgroup.normalizer (Q : Set G) ≤ GLBCore p rank P :=
      le_sSup ⟨Q, hQP, hrank, rfl⟩
    exact hnormalizer.trans hcore
  · intro hnormalizers
    apply sSup_le
    rintro N ⟨Q, hQP, hrank, rfl⟩
    exact hnormalizers Q hQP hrank

theorem fullCore_escape_of_weakCore_local (p : ℕ) (hp : p.Prime)
    (P M : Subgroup G) (hweak : GLBWeakCore p P ≤ M)
    (hfull : ¬ GLBCore p 2 P ≤ M) :
    ∃ Q : Subgroup G, Q ≤ P ∧ pRank p Q = 2 ∧
      pRank p (Q ⊔ (P ⊓ Subgroup.centralizer (Q : Set G))) = 2 ∧
      pRank p (P ⊓ Subgroup.centralizer (Q : Set G)) ≤ 2 ∧
      ¬ Subgroup.normalizer (Q : Set G) ≤ M := by
  classical
  rw [fullCore_le_iff] at hfull
  push Not at hfull
  obtain ⟨Q, hQP, hQrank, hescape⟩ := hfull
  have hQupper : pRank p Q < 3 := by
    by_contra hlarge
    apply hescape
    exact (normalizer_le_weakCore p hQP hQrank
      ((Nat.le_of_not_gt hlarge).trans (pRank_mono p hp le_sup_left))).trans hweak
  have hjoinupper : pRank p (Q ⊔ (P ⊓ Subgroup.centralizer (Q : Set G))) < 3 := by
    by_contra hlarge
    exact hescape ((normalizer_le_weakCore p hQP hQrank
      (Nat.le_of_not_gt hlarge)).trans hweak)
  have hjoinlower : 2 ≤ pRank p (Q ⊔ (P ⊓ Subgroup.centralizer (Q : Set G))) :=
    hQrank.trans (pRank_mono p hp le_sup_left)
  have hcentral := pRank_mono p hp
    (show P ⊓ Subgroup.centralizer (Q : Set G) ≤
      Q ⊔ (P ⊓ Subgroup.centralizer (Q : Set G)) from le_sup_right)
  exact ⟨Q, hQP, by omega, by omega, by omega, hescape⟩

theorem rankThreeCore_le_weakCore (p : ℕ) (hp : p.Prime) (P : Subgroup G) :
    GLBCore p 3 P ≤ GLBWeakCore p P := by
  apply sSup_le
  rintro N ⟨Q, hQP, hrank, rfl⟩
  apply normalizer_le_weakCore p hQP (by omega)
  exact hrank.trans (pRank_mono p hp le_sup_left)

theorem normalizer_le_weakCore_of_rank (p : ℕ) (hp : p.Prime) (P : Subgroup G)
    (hrank : 3 ≤ pRank p P) : Subgroup.normalizer (P : Set G) ≤ GLBWeakCore p P := by
  apply normalizer_le_weakCore p le_rfl (by omega)
  exact hrank.trans (pRank_mono p hp le_sup_left)

theorem subgroup_le_weakCore_of_rank (p : ℕ) (hp : p.Prime) (P : Subgroup G)
    (hrank : 3 ≤ pRank p P) : P ≤ GLBWeakCore p P := by
  exact Subgroup.le_normalizer.trans (normalizer_le_weakCore_of_rank p hp P hrank)

omit [Finite G] in
theorem commutative_subgroup_le_centralizer {E Q : Subgroup G}
    (hcomm : IsMulCommutative E) (hQE : Q ≤ E) : E ≤ Subgroup.centralizer (Q : Set G) := by
  intro element helement
  apply Subgroup.mem_centralizer_iff.mpr
  intro other hother
  exact congrArg Subtype.val
    ((isMulCommutative_iff.mp hcomm) (⟨other, hQE hother⟩ : E) ⟨element, helement⟩)

theorem normalizer_le_weakCore_of_commutative_overgroup (p : ℕ) (hp : p.Prime)
    {P E Q : Subgroup G} (hEP : E ≤ P) (hQE : Q ≤ E) (hcomm : IsMulCommutative E)
    (hQrank : 2 ≤ pRank p Q) (hErank : 3 ≤ pRank p E) :
    Subgroup.normalizer (Q : Set G) ≤ GLBWeakCore p P := by
  apply normalizer_le_weakCore p (hQE.trans hEP) hQrank
  apply hErank.trans
  apply pRank_mono p hp
  exact (le_inf hEP (commutative_subgroup_le_centralizer hcomm hQE)).trans le_sup_right

theorem weakCore_eq_fullCore_of_commutative (p : ℕ) (hp : p.Prime) (P : Subgroup G)
    (hcomm : IsMulCommutative P) (hrank : 3 ≤ pRank p P) :
    GLBWeakCore p P = GLBCore p 2 P := by
  apply le_antisymm (weakCore_le_fullCore p P)
  apply sSup_le
  rintro N ⟨Q, hQP, hQrank, rfl⟩
  exact normalizer_le_weakCore_of_commutative_overgroup p hp le_rfl hQP hcomm hQrank hrank

theorem betaFour_has_large_sylow {p : ℕ} (hp : p ∈ GLBBetaFour G) :
    ∃ P : Sylow p G, 4 ≤ pRank p (P : Subgroup G) := by
  obtain ⟨E, _, helem, hcard⟩ := pRank_attained p hp.1 (⊤ : Subgroup G)
  obtain ⟨P, hEP⟩ := (IsPGroup.of_card hcard).exists_le_sylow
  refine ⟨P, (betaFour_globalRank hp).trans ?_⟩
  exact le_csSup (pRank_bddAbove p hp.1 (P : Subgroup G))
    ⟨E, hEP, helem, hcard⟩

theorem pGroup_commutative_of_simple [IsSimpleGroup G] (p : ℕ) (hp : p.Prime)
    (hgroup : IsPGroup p G) : ∀ a b : G, a * b = b * a := by
  let : Fact p.Prime := ⟨hp⟩
  have hcenter := hgroup.bot_lt_center
  have htop : Subgroup.center G = ⊤ := by
    rcases (inferInstance : (Subgroup.center G).Normal).eq_bot_or_eq_top with hbot | htop
    · exact False.elim (hcenter.ne' hbot)
    · exact htop
  intro a b
  apply Subgroup.mem_center_iff.mp (show b ∈ Subgroup.center G from ?_) a
  rw [htop]
  exact Subgroup.mem_top b

theorem twoLocal_ne_top [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) {H : Subgroup G} (hlocal : IsTwoLocal H) :
    H ≠ ⊤ := by
  rintro htop
  obtain ⟨P, hnontrivial, hgroup, hnormalizer⟩ := hlocal
  have hnormal : P.Normal := Subgroup.normalizer_eq_top_iff.mp (hnormalizer ▸ htop)
  rcases hnormal.eq_bot_or_eq_top with hbot | hPtop
  · exact hnontrivial hbot
  · have hG : IsPGroup 2 G := by
      rw [hPtop] at hgroup
      exact hgroup.of_equiv (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G)
    obtain ⟨a, b, hab⟩ := hnonab
    exact hab (pGroup_commutative_of_simple 2 (by norm_num) hG a b)

theorem exclusion_of_weakCore_eq_top [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) {p : ℕ} (hp : p ∈ GLBBetaFour G)
    (P : Sylow p G) (hcore : GLBWeakCore p (P : Subgroup G) = ⊤) :
    ∃ q ∈ GLBBetaFour G, ¬ GLBWeakCoreLocal G q := by
  apply exclusion_iff_nonlocal_core.mpr
  refine ⟨p, hp, P, ?_⟩
  intro H hlocal hcontained
  apply twoLocal_ne_top hnonab hlocal
  apply top_le_iff.mp
  exact hcore ▸ hcontained

theorem exists_maximal_twoLocal {H : Subgroup G} (hlocal : IsTwoLocal H) :
    ∃ M : Subgroup G, H ≤ M ∧ GLBIsMaxTwoLocal M := by
  obtain ⟨M, hHM, hmax⟩ := Finite.exists_le_maximal hlocal
  refine ⟨M, hHM, hmax.prop, ?_⟩
  intro K hK hMK
  exact (hmax.eq_of_le hK hMK).symm

theorem twoLocalRank_attained (p : ℕ) (hp : p.Prime)
    (hpositive : 0 < GLBTwoLocalRank p G) :
    ∃ H : Subgroup G, IsTwoLocal H ∧ pRank p H = GLBTwoLocalRank p G := by
  apply Nat.sSup_mem _ (twoLocalRank_bddAbove p hp)
  by_contra hempty
  have hset : {rank | ∃ H : Subgroup G, IsTwoLocal H ∧ pRank p H = rank} = ∅ :=
    Set.not_nonempty_iff_eq_empty.mp hempty
  have hzero : GLBTwoLocalRank p G = 0 := by
    change sSup {rank | ∃ H : Subgroup G, IsTwoLocal H ∧ pRank p H = rank} = 0
    rw [hset]
    exact csSup_empty
  omega

theorem betaFour_has_bmax {p : ℕ} (hp : p ∈ GLBBetaFour G) :
    ∃ B : Subgroup G, GLBIsBmax p B := by
  obtain ⟨H, hlocal, hrank⟩ := twoLocalRank_attained (G := G) p hp.1 (by
    have := hp.2.2.2
    omega)
  obtain ⟨B, hBH, helem, hcard⟩ := pRank_attained p hp.1 H
  obtain ⟨U, hnontrivial, hgroup, hnormalizer⟩ := hlocal
  refine ⟨B, helem, hrank ▸ hcard, U, hnontrivial, hgroup, ?_⟩
  exact hnormalizer ▸ hBH

theorem bmax_rank_lowerBound {p : ℕ} (hp : p.Prime) {B : Subgroup G}
    (hB : GLBIsBmax p B) : GLBTwoLocalRank p G ≤ pRank p B := by
  exact le_csSup (pRank_bddAbove p hp B) ⟨B, le_rfl, hB.1, hB.2.1⟩

theorem bmax_has_large_sylow {p : ℕ} (hp : p ∈ GLBBetaFour G) {B : Subgroup G}
    (hB : GLBIsBmax p B) :
    ∃ P : Sylow p G, B ≤ (P : Subgroup G) ∧ 4 ≤ pRank p (P : Subgroup G) := by
  obtain ⟨P, hBP⟩ := (IsPGroup.of_card hB.2.1).exists_le_sylow
  refine ⟨P, hBP, hp.2.2.2.trans ?_⟩
  exact (bmax_rank_lowerBound hp.1 hB).trans (pRank_mono p hp.1 hBP)

theorem preuniqueness_has_maximal_local {p : ℕ} (hp : p ∈ GLBBetaFour G)
    (hpre : GLBPreuniqueness G) :
    ∃ (B : Subgroup G) (P : Sylow p G) (M : Subgroup G),
      GLBIsBmax p B ∧ B ≤ (P : Subgroup G) ∧ 4 ≤ pRank p (P : Subgroup G) ∧
      GLBIsMaxTwoLocal M ∧ p ∈ GLBSigma M ∧
      GLBWeakCore p (P : Subgroup G) ≤ M ∧ (P : Subgroup G) ≤ M := by
  obtain ⟨B, hB⟩ := betaFour_has_bmax hp
  obtain ⟨P, hBP, hPrank⟩ := bmax_has_large_sylow hp hB
  obtain ⟨H, hHlocal, hcore⟩ := (hpre p hp).2 P
  obtain ⟨M, hHM, hMmax⟩ := exists_maximal_twoLocal hHlocal
  have hcoreM : GLBWeakCore p (P : Subgroup G) ≤ M := hcore.trans hHM
  have hPM : (P : Subgroup G) ≤ M :=
    (subgroup_le_weakCore_of_rank p hp.1 (P : Subgroup G) (by omega)).trans hcoreM
  exact ⟨B, P, M, hB, hBP, hPrank, hMmax, ⟨hp, B, hB, hBP.trans hPM⟩,
    hcoreM, hPM⟩

omit [Finite G] in
theorem pCore_normal (p : ℕ) : (pCore p G).Normal := by
  rw [CFSG.pCore_eq_iSup]
  rw [← sSup_range]
  apply Subgroup.sSup_normal
  intro N hN
  rcases hN with ⟨M, rfl⟩
  change (⨆ (_ : M.Normal), ⨆ (_ : IsPGroup p M), M).Normal
  rw [← sSup_range]
  apply Subgroup.sSup_normal
  rintro K ⟨hnormal, rfl⟩
  change (⨆ (_ : IsPGroup p M), M).Normal
  rw [← sSup_range]
  apply Subgroup.sSup_normal
  rintro K ⟨hgroup, rfl⟩
  exact hnormal

omit [Finite G] in
theorem pCore_isPGroup (p : ℕ) : IsPGroup p (pCore p G) := by
  obtain ⟨P, _⟩ := (IsPGroup.of_bot (p := p) (G := G)).exists_le_sylow
  have hcoreP : pCore p G ≤ (P : Subgroup G) := by
    rw [CFSG.pCore_eq_iSup]
    apply iSup_le
    intro N
    apply iSup_le
    intro hnormal
    let : N.Normal := hnormal
    apply iSup_le
    intro hgroup
    exact hgroup.le_sylow_of_normal P
  exact P.isPGroup'.of_injective (Subgroup.inclusion hcoreP)
    (Subgroup.inclusion_injective hcoreP)

omit [Finite G] in
theorem pCoreOf_isPGroup (p : ℕ) (H : Subgroup G) : IsPGroup p (pCoreOf p H) := by
  exact (pCore_isPGroup (G := H) p).map H.subtype

omit [Finite G] in
theorem pCore_characteristic (p : ℕ) : (pCore p G).Characteristic := by
  apply Subgroup.characteristic_iff_map_le.mpr
  intro automorphism
  rw [CFSG.pCore_eq_iSup]
  simp only [Subgroup.map_iSup]
  apply iSup_le
  intro N
  apply iSup_le
  intro hnormal
  apply iSup_le
  intro hgroup
  exact le_iSup_of_le (N.map automorphism.toMonoidHom)
    (le_iSup_of_le (hnormal.map automorphism.toMonoidHom automorphism.surjective)
      (le_iSup_of_le (hgroup.map automorphism.toMonoidHom) le_rfl))

omit [Finite G] in
theorem normalizer_le_normalizer_characteristic {H : Subgroup G}
    (K : Subgroup H) (hcharacteristic : K.Characteristic) :
    Subgroup.normalizer (H : Set G) ≤ Subgroup.normalizer (K.map H.subtype : Set G) := by
  apply Subgroup.le_normalizer_iff.mpr
  intro element helement member hmember
  obtain ⟨representative, hrepresentative, rfl⟩ := hmember
  let automorphism : H ≃* H := H.normalizerMonoidHom ⟨element, helement⟩
  have hfixed := Subgroup.characteristic_iff_map_le.mp hcharacteristic automorphism
  have himage : automorphism representative ∈ K :=
    hfixed (Subgroup.mem_map.mpr ⟨representative, hrepresentative, rfl⟩)
  apply Subgroup.mem_map.mpr
  exact ⟨automorphism representative, himage,
    H.normalizerMonoidHom_apply_apply_coe ⟨element, helement⟩ representative⟩

omit [Finite G] in
theorem pCoreOf_le (p : ℕ) (H : Subgroup G) : pCoreOf p H ≤ H := by
  exact Subgroup.map_subtype_le (pCore p H)

omit [Finite G] in
theorem subgroup_normalizes_pCoreOf (p : ℕ) (H : Subgroup G) :
    H ≤ Subgroup.normalizer (pCoreOf p H : Set G) := by
  exact Subgroup.le_normalizer.trans
    (normalizer_le_normalizer_characteristic (pCore p H) (pCore_characteristic p))

omit [Finite G] in
theorem normal_pSubgroup_le_pCoreOf (p : ℕ) {N H : Subgroup G} (hNH : N ≤ H)
    (hnormal : (N.subgroupOf H).Normal) (hgroup : IsPGroup p N) : N ≤ pCoreOf p H := by
  have hsubgroup : IsPGroup p (N.subgroupOf H) :=
    hgroup.of_equiv (Subgroup.subgroupOfEquivOfLe hNH).symm
  have hcore : N.subgroupOf H ≤ pCore p H :=
    le_sSup ⟨hnormal, hsubgroup⟩
  rw [← Subgroup.map_subgroupOf_eq_of_le hNH]
  exact Subgroup.map_mono hcore

omit [Finite G] in
theorem twoLocal_pCoreOf_ne_bot {H : Subgroup G} (hlocal : IsTwoLocal H) :
    pCoreOf 2 H ≠ ⊥ := by
  obtain ⟨N, hnontrivial, hgroup, hnormalizer⟩ := hlocal
  have hNH : N ≤ H := hnormalizer ▸ Subgroup.le_normalizer
  have hnormal : (N.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNH).mpr hnormalizer.le
  have hcore := normal_pSubgroup_le_pCoreOf 2 hNH hnormal hgroup
  intro hbot
  apply hnontrivial
  exact bot_unique (hbot ▸ hcore)

omit [Finite G] in
theorem maximal_twoLocal_eq_core_normalizer {M : Subgroup G}
    (hmax : GLBIsMaxTwoLocal M) :
    Subgroup.normalizer (pCoreOf 2 M : Set G) = M := by
  apply hmax.2
  · exact ⟨pCoreOf 2 M, twoLocal_pCoreOf_ne_bot hmax.1,
      pCoreOf_isPGroup 2 M, rfl⟩
  · exact subgroup_normalizes_pCoreOf 2 M

omit [Finite G] in
theorem maximal_twoLocal_self_normalizing {M : Subgroup G}
    (hmax : GLBIsMaxTwoLocal M) : Subgroup.normalizer (M : Set G) = M := by
  apply le_antisymm _ Subgroup.le_normalizer
  have hcore : Subgroup.normalizer (M : Set G) ≤
      Subgroup.normalizer (pCoreOf 2 M : Set G) :=
    normalizer_le_normalizer_characteristic (pCore 2 M) (pCore_characteristic 2)
  rw [maximal_twoLocal_eq_core_normalizer hmax] at hcore
  exact hcore

omit [Finite G] in
theorem charTwoType_pCoreOf_selfCentralizing (hchar : IsCharTwoType G)
    {H : Subgroup G} (hlocal : IsTwoLocal H) :
    H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) ≤ pCoreOf 2 H := by
  exact hchar H hlocal

theorem odd_pSubgroup_inf_twoCore_eq_bot (p : ℕ) (hp : p.Prime) (hodd : p ≠ 2)
    (R M : Subgroup G) (hR : IsPGroup p R) : R ⊓ pCoreOf 2 M = ⊥ := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨rank, hcard⟩ := IsPGroup.iff_card.mp hR
  obtain ⟨twoRank, htwoCard⟩ := IsPGroup.iff_card.mp (pCoreOf_isPGroup 2 M)
  apply disjoint_iff.mp
  apply Subgroup.disjoint_of_coprime_natCard
  rw [hcard, htwoCard]
  exact Nat.coprime_pow_primes rank twoRank hp (by norm_num) hodd

theorem odd_pSubgroup_twoCore_centralizer_eq_bot (p : ℕ) (hp : p.Prime)
    (hodd : p ≠ 2) (hchar : IsCharTwoType G) {R M : Subgroup G}
    (hR : IsPGroup p R) (hRM : R ≤ M) (hlocal : IsTwoLocal M) :
    R ⊓ Subgroup.centralizer (pCoreOf 2 M : Set G) = ⊥ := by
  apply bot_unique
  have hcentral : R ⊓ Subgroup.centralizer (pCoreOf 2 M : Set G) ≤ pCoreOf 2 M :=
    (inf_le_inf_right _ hRM).trans (hchar M hlocal)
  have hcontained : R ⊓ Subgroup.centralizer (pCoreOf 2 M : Set G) ≤
      R ⊓ pCoreOf 2 M := le_inf inf_le_left hcentral
  rw [odd_pSubgroup_inf_twoCore_eq_bot p hp hodd R M hR] at hcontained
  exact hcontained

theorem odd_pSubgroup_twoCore_action_injective (p : ℕ) (hp : p.Prime)
    (hodd : p ≠ 2) (hchar : IsCharTwoType G) {R M : Subgroup G}
    (hR : IsPGroup p R) (hRM : R ≤ M) (hlocal : IsTwoLocal M) :
    Function.Injective
      (((pCoreOf 2 M).normalizerMonoidHom).comp
        (Subgroup.inclusion (hRM.trans (subgroup_normalizes_pCoreOf 2 M)))) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro element helement
  apply Subgroup.mem_bot.mpr
  have hkernel :
      Subgroup.inclusion (hRM.trans (subgroup_normalizes_pCoreOf 2 M)) element ∈
        (pCoreOf 2 M).normalizerMonoidHom.ker := helement
  rw [Subgroup.normalizerMonoidHom_ker] at hkernel
  have hcentral : (element : G) ∈ Subgroup.centralizer (pCoreOf 2 M : Set G) := hkernel
  have hinf : (element : G) ∈ R ⊓ Subgroup.centralizer (pCoreOf 2 M : Set G) :=
    ⟨element.property, hcentral⟩
  rw [odd_pSubgroup_twoCore_centralizer_eq_bot p hp hodd hchar hR hRM hlocal] at hinf
  apply Subtype.ext
  exact Subgroup.mem_bot.mp hinf

end CFSG.PreuniquenessRankFour.Helpers
