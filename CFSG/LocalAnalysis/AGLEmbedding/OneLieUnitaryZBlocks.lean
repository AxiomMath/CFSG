module

public import CFSG.LocalAnalysis.AGLEmbedding.OneLieUnitaryZData
import CFSG.LocalAnalysis.AGLEmbedding.BlockData
import CFSG.LocalAnalysis.AGLEmbedding.BlockInnerNormalizer
import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeKillAux2
import CFSG.LocalAnalysis.AGLEmbedding.ComponentCentralizer
import CFSG.LocalAnalysis.AGLEmbedding.GapROneBSAux
import CFSG.LocalAnalysis.AGLEmbedding.OneLieMSideCore
import CFSG.LocalAnalysis.AGLEmbedding.OneLieUnitaryZRank
import CFSG.LocalAnalysis.AGLEmbedding.PhaseThreeBlockRank
public import CFSG.LocalAnalysis.AGLEmbedding.ComponentRank
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieMSideDefsAux

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Blocks

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {n : ℕ} {P : Sylow p G}
  {M H R X Z Np : Subgroup G}

theorem eq_three_or_five_le_of_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : p = 3 ∨ 5 ≤ p := by
  have := hp.two_le
  rcases Nat.lt_or_ge p 5 with h5 | h5
  · interval_cases p
    · exact absurd rfl hp2
    · exact Or.inl rfl
    · exact absurd hp (by decide)
  · exact Or.inr h5

theorem D1OneLieU3Data.card_barM_center (h : D1OneLieU3Data p n P M H R X Z Np) :
    Nat.card (barM M Z) = p ^ n := by
  have hp : p.Prime := Fact.out
  have hZX : Z ≤ X := h.center_eq ▸ inf_le_left
  have hZM : Z ≤ M := (hZX.trans h.le_R).trans h.ph3.le_M
  have hO2 : p.Coprime (Nat.card (CFSG.pCore 2 ↥M)) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥M))
    rw [hk]
    exact Nat.Coprime.pow_right k ((Nat.coprime_primes hp Nat.prime_two).mpr h.ph3.ne_two)
  have hZp : IsPGroup p (Z.subgroupOf M) :=
    ((h.ph3.isPGroup_R.to_le (hZX.trans h.le_R)).comap_subtype)
  rw [barM, card_map_mk_of_isPGroup hp _ hO2 hZp,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZM).toEquiv, h.card_center]

theorem D1OneLieU3Data.mem_normalizer_weakSBlock (hB3 : StmtBlockThree)
    (h : D1OneLieU3Data p n P M H R X Z Np) {r : ℕ} [Fact r.Prime] {t : G} (hr2n : 2 * n < r)
    (hrp : r ≠ p) (htK : t ∈ H ⊓ M) (htr : IsPGroup r (Subgroup.zpowers t))
    (htZ : ∀ z ∈ Z, t * z * t⁻¹ = z) {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    t ∈ Subgroup.normalizer (L : Set G) := by
  have hp : p.Prime := Fact.out
  have hr : r.Prime := Fact.out
  have hn2 := h.two_le
  have hB3' : ∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' →
      BlockHasThree M (pCoreOf 2 H) L' := fun L' hL' => hB3 h.ph3 hL'
  by_contra htL
  rcases eq_three_or_five_le_of_prime hp h.ph3.ne_two with hp3 | hp5
  swap
  · have hle := h.ph3.le_pRank_three_of_not_mem_normalizer' stmtComponentRank stmtBarPRankLift
      hB3' htK htr hL htL
    exact h.ph3.false_of_four_le_pRank' h.ind Nat.prime_three (by decide) (by omega) (by omega)
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  have htM : t ∈ M := htK.2
  have hKeq := h.ph3.inf_eq_inf_normalizer_twoCore
  set tb : ↥M ⧸ CFSG.pCore 2 ↥M := mk ⟨t, htM⟩ with htb
  set A : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M) := barM M (H ⊓ M) with hA
  have htA : tb ∈ A := Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr htK)
  have htbr : IsPGroup r (Subgroup.zpowers tb) := by
    obtain ⟨k, hk⟩ := htr ⟨t, Subgroup.mem_zpowers t⟩
    have hk' : t ^ r ^ k = 1 := by simpa using congrArg Subtype.val hk
    refine isPGroup_zpowers_of_pow_eq_one (k := k) ?_
    have : (⟨t, htM⟩ : M) ^ r ^ k = 1 := Subtype.ext (by simpa using hk')
    rw [htb, ← map_pow, this, map_one]
  have htbL : tb ∉ Subgroup.normalizer (barM M L : Set _) := by
    intro htbN
    apply htL
    refine hL.toIsTwoPrimeComponent.le_normalizer (S := Subgroup.zpowers t) ?_
      ((Subgroup.zpowers_le).mpr htM) (Subgroup.mem_zpowers t)
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (Subgroup.mem_subgroupOf.mp hx)
    have hxk : x = (⟨t, htM⟩ : M) ^ k := Subtype.ext (by simpa using hk.symm)
    rw [hxk, map_zpow]
    exact Subgroup.zpow_mem _ htbN k
  obtain ⟨y, ⟨hyS, hyL⟩, hy3, l, hlL, hlQ⟩ := hB3' L hL
  have hyM : y ∈ M := hL.le hyL
  set yb : ↥M ⧸ CFSG.pCore 2 ↥M := mk ⟨y, hyM⟩ with hyb
  have hyA : yb ∈ A :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr (hKeq ▸ ⟨hyM, hyS⟩))
  have hyLb : yb ∈ barM M L := Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hyL)
  have hyq : IsPGroup 3 (Subgroup.zpowers yb) := by
    obtain ⟨k, hk⟩ := hy3 ⟨y, Subgroup.mem_zpowers _⟩
    have hk' : y ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
    refine isPGroup_zpowers_of_pow_eq_one (k := k) ?_
    have : (⟨y, hyM⟩ : M) ^ 3 ^ k = 1 := Subtype.ext (by simpa using hk')
    rw [hyb, ← map_pow, this, map_one]
  have hyZ : yb ∉ Subgroup.centralizer (barM M L : Set _) := by
    intro hyC
    have hlM : l ∈ M := hL.le hlL
    have he := Subgroup.mem_centralizer_iff.mp hyC (mk ⟨l, hlM⟩)
      (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hlL))
    apply hlQ
    have h1 : mk (⟨y, hyM⟩ * ⟨l, hlM⟩ * (⟨y, hyM⟩)⁻¹ * (⟨l, hlM⟩)⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv]
      change yb * mk ⟨l, hlM⟩ * yb⁻¹ * (mk ⟨l, hlM⟩)⁻¹ = 1
      rw [← he]
      group
    simpa using coe_mem_pCoreOf_two_of_mk_eq_one _ h1
  have hZX : Z ≤ X := h.center_eq ▸ inf_le_left
  have hZK : Z ≤ H ⊓ M := (hZX.trans h.le_R).trans h.ph3.le_inf
  have hZM : Z ≤ M := hZK.trans inf_le_right
  have hWA : barM M Z ≤ A := barM_mono hZK
  have hWO : barM M Z ≤ CFSG.pCore p (↥M ⧸ CFSG.pCore 2 ↥M) := by
    rw [← barM_preimage (CFSG.pCore p (↥M ⧸ CFSG.pCore 2 ↥M))]
    exact barM_mono h.le_pCore
  have hWL : ∀ L' : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), IsComponentOf L' ⊤ →
      barM M Z ≤ Subgroup.centralizer (L' : Set _) := fun L' hL' =>
    hWO.trans (pCore_le_centralizer_component p hL')
  have htW : ∀ w ∈ barM M Z, tb * w * tb⁻¹ = w := by
    rintro _ ⟨⟨z, hzM⟩, hz, rfl⟩
    have hz' := htZ z (Subgroup.mem_subgroupOf.mp hz)
    have : (⟨t, htM⟩ : M) * ⟨z, hzM⟩ * (⟨t, htM⟩ : M)⁻¹ = ⟨z, hzM⟩ := Subtype.ext hz'
    rw [htb, ← map_inv, ← map_mul, ← map_mul, this]
  have hWq : ∀ w ∈ barM M Z, w ^ 3 = 1 := by
    rintro _ ⟨⟨z, hzM⟩, hz, rfl⟩
    have hz3 : z ^ p = 1 := h.pow_eq_one z (hZX (Subgroup.mem_subgroupOf.mp hz))
    have : (⟨z, hzM⟩ : M) ^ 3 = 1 := Subtype.ext (by rw [← hp3]; simpa using hz3)
    rw [← map_pow, this, map_one]
  have hWc : ¬ IsCyclic (barM M Z) := by
    intro hc
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have h1 := card_le_of_isCyclic_of_pow_eq_one (p := 3) (⊤ : Subgroup (barM M Z))
      (fun w _ => Subtype.ext (by simpa using hWq w w.2))
    rw [Subgroup.card_top, h.card_barM_center, hp3] at h1
    have : 3 < 3 ^ n := by
      calc 3 = 3 ^ 1 := (pow_one 3).symm
        _ < 3 ^ n := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  have hrank := succ_le_pRank_of_not_mem_normalizer Nat.prime_three (hp3 ▸ hrp)
    hL.toIsTwoPrimeComponent.component htbr htbL htA hyA hyLb hyq hyZ hWA hWL htW hWq hWc
  have h1 : Open.pRank 3 A ≤ Open.pRank 3 (H ⊓ M) :=
    pRank_barM_le Nat.prime_three (by decide) M (H ⊓ M) inf_le_right
  have h2 := h.pRank_le
  rw [hp3] at h2
  omega

theorem D1OneLieU3Data.relIndex_eq (h : D1OneLieU3Data p n P M H R X Z Np) :
    Z.relIndex X = p ^ (2 * n) := by
  have hp : p.Prime := Fact.out
  have hZX : Z ≤ X := h.center_eq ▸ inf_le_left
  have h1 := Subgroup.relIndex_mul_card Z X
  rw [inf_of_le_left hZX, h.card_center, h.card_eq] at h1
  have hpn : 0 < p ^ n := pow_pos hp.pos n
  have h2 : p ^ (3 * n) = p ^ (2 * n) * p ^ n := by rw [← pow_add]; congr 1; omega
  rw [h2] at h1
  exact Nat.eq_of_mul_eq_mul_right hpn h1

theorem D1OneLieU3Data.le_normalizer_weakSBlock (hB3 : StmtBlockThree)
    (h : D1OneLieU3Data p n P M H R X Z Np) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) : X ≤ Subgroup.normalizer (L : Set G) := by
  have hp : p.Prime := Fact.out
  have hn2 := h.two_le
  obtain ⟨r, t, hr, hr2n, hrp, -, htK, htX, htr, htZ, -, -, hirr⟩ := h.ppd
  have : Fact r.Prime := ⟨hr⟩
  have hB3' : ∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' →
      BlockHasThree M (pCoreOf 2 H) L' := fun L' hL' => hB3 h.ph3 hL'
  have hXK : X ≤ H ⊓ M := h.le_R.trans h.ph3.le_inf
  have hZc : Z ≤ Subgroup.centralizer (X : Set G) := h.center_eq ▸ inf_le_right
  rcases eq_three_or_five_le_of_prime hp h.ph3.ne_two with hp3 | hp5
  · have htL := h.mem_normalizer_weakSBlock hB3 hr2n hrp htK htr htZ hL
    have htZn : t ∈ Subgroup.normalizer (Z : Set G) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq] at htX ⊢
      rw [← h.commutator_eq, Subgroup.map_commutator, htX]
    have htNXL : t ∈ Subgroup.normalizer
        ((X ⊓ Subgroup.normalizer (L : Set G) : Subgroup G) : Set G) :=
      Subgroup.inf_normalizer_le_normalizer_inf ⟨htX, Subgroup.le_normalizer htL⟩
    rcases eq_or_le_of_mem_normalizer h.commutator_eq hZc htZn hirr inf_le_left htNXL with
      heq | hle
    · exact heq ▸ inf_le_right
    · exfalso
      have hidx := h.ph3.relIndex_le_pRank_three hB3' hXK hL
      have hne : (X ⊓ Subgroup.normalizer (L : Set G)).relIndex X ≠ 0 := by
        intro h0
        have h1 := Subgroup.relIndex_mul_card (X ⊓ Subgroup.normalizer (L : Set G)) X
        rw [h0, zero_mul] at h1
        exact Nat.card_pos.ne' h1.symm
      have h1 : Z.relIndex X ≤ (X ⊓ Subgroup.normalizer (L : Set G)).relIndex X :=
        Subgroup.relIndex_le_of_le_left hle hne
      rw [h.relIndex_eq] at h1
      have h2 := h.pRank_le
      subst hp3
      have h3 : 2 * n - 1 < 3 ^ (2 * n - 1) := Nat.lt_pow_self (by norm_num)
      have h4 : 3 ^ (2 * n) = 3 * 3 ^ (2 * n - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      omega
  · intro u hu
    by_contra huL
    have hup : IsPGroup p (Subgroup.zpowers u) :=
      isPGroup_zpowers_of_pow_eq_one (k := 1) (by simpa using h.pow_eq_one u hu)
    have hle := h.ph3.le_pRank_three_of_not_mem_normalizer' stmtComponentRank
      stmtBarPRankLift hB3' (hXK hu) hup hL huL
    exact h.ph3.false_of_four_le_pRank' h.ind Nat.prime_three (by decide) (by omega)
      (by omega)

theorem D1OneLieU3Data.barM_le_centralizer_of_weakSBlock (hB3 : StmtBlockThree)
    (hLB : StmtLemmaBRelCyc) (h85 : Asc81bEightFive) (hD2 : D1NoXBlock)
    (h : D1OneLieU3Data p n P M H R X Z Np) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    barM M X ≤ Subgroup.centralizer (barM M L : Set _) := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := h.ph3.ne_two
  have hn2 := h.two_le
  obtain ⟨r, t, hr, hr2n, hrp, hrp1, htK, htX, htr, htZ, htrX, htnt, hirr⟩ := h.ppd
  have : Fact r.Prime := ⟨hr⟩
  have htL := h.mem_normalizer_weakSBlock hB3 hr2n hrp htK htr htZ hL
  have hXL := h.le_normalizer_weakSBlock hB3 hL
  have hXK : X ≤ H ⊓ M := h.le_R.trans h.ph3.le_inf
  have hZc : Z ≤ Subgroup.centralizer (X : Set G) := h.center_eq ▸ inf_le_right
  obtain ⟨hnot1, -⟩ := h.ph3.nineThree_not_one h85 hD2 hL
  have hcyc : ∀ Y' : Subgroup G, Y' ≤ M ⊓ Subgroup.normalizer (pCoreOf 2 H : Set G) →
      ⁅Y', Y'⁆ = Y' → ∀ A : Subgroup G, A ≤ Y' → IsPGroup p A → IsCyclic A :=
    fun Y' hY' hperf A hAY hA => h.plus_cyclic A
      (hAY.trans (h.perfect_le Y' (h.ph3.inf_eq_inf_normalizer_twoCore ▸ hY') hperf)) hA
  have hXp : IsPGroup p X := h.ph3.isPGroup_R.to_le h.le_R
  exact hLB G M (pCoreOf 2 H) L X Z p r t h.ph3.isKGroup.1 h.ph3.asc81bHyp hL hnot1
    (h.ph3.not_isSylowTwoOf_inf h85 hD2 hL) hp hp2 hcyc
    (h.ph3.inf_eq_inf_normalizer_twoCore ▸ hXK) hXL hXp h.commutator_eq hZc
    (fun x hx => by rw [h.pow_eq_one x hx]; exact Z.one_mem)
    (by rw [h.relIndex_eq]; exact Nat.pow_le_pow_right hp.pos (by omega))
    (h.ph3.inf_eq_inf_normalizer_twoCore ▸ htK) htL htX hr (by omega) (by omega) hrp hrp1
    (fun x hx => by rw [htrX x hx, mul_inv_cancel]; exact Z.one_mem) htnt hirr

end Blocks

end CFSG.AGLEmbedding
