module

public import CFSG.LocalAnalysis.AGLEmbedding.Extremal
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNoSPTransvect
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBOneChar

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

theorem D1Extremal.odd_card_glbPrimeCore_of_lt {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
    (hext : D1Extremal p P M H R) {z : G}
    (hCM : ¬ Subgroup.centralizer ({z} : Set G) ≤ M)
    (hcore : GLBPrimeCore p (Subgroup.centralizer ({z} : Set G)) ≤ M)
    {T : Subgroup G} (hTp : IsPGroup p T) (hTC : T ≤ Subgroup.centralizer ({z} : Set G))
    (hTM : T ≤ M) (hT3 : 3 ≤ Open.pRank p T) (hRT : Nat.card R < Nat.card T) :
    Odd (Nat.card (GLBPrimeCore p (Subgroup.centralizer ({z} : Set G)))) :=
  odd_card_of_twoLocals_le hext.prime hTp hTC hCM (glbPrimeCore_le p _)
    (glbPrimeCore_normal p _) (glbPrimeCore_coprime p _) hcore
    fun U hU2 hU1 hTU => hext.le_of_card_lt hTM hTp hT3 hRT ⟨U, hU1, hU2, rfl⟩ hTU

theorem exists_mem_normalizer_not_mem_zpowers {p : ℕ} [Fact p.Prime] {Q' T : Subgroup G}
    (hQ' : IsPGroup p Q') (hTQ' : T ≤ Q') (hne : T ≠ Q') {z : G} (hzp : orderOf z = p)
    (hQC : Q' ⊓ Subgroup.centralizer ({z} : Set G) ≤ T) :
    ∃ x ∈ Q', x ∈ Subgroup.normalizer (T : Set G) ∧ x * z * x⁻¹ ∉ Subgroup.zpowers z := by
  by_contra hall
  push Not at hall
  apply hne
  refine (eq_of_isPGroup_of_le_of_normalizer hQ' hTQ' fun g hgQ hgN => ?_).symm
  have hgz := hall g hgQ hgN
  obtain ⟨n, hn⟩ := hQ' ⟨g, hgQ⟩
  have hgn : g ^ p ^ n = 1 := by simpa using congrArg Subtype.val hn
  exact hQC ⟨hgQ, Subgroup.mem_centralizer_singleton_iff.mpr
    (commute_of_mem_normalizer_zpowers_of_pow_prime_pow Fact.out hzp
      (mem_normalizer_zpowers_of_mem_zpowers hgz) hgn).eq⟩

omit [Finite G] in
theorem mem_zpowers_sup_zpowers_iff {t z : G} (htz : Commute t z) {e : G} :
    e ∈ Subgroup.zpowers t ⊔ Subgroup.zpowers z ↔
      ∃ a ∈ Subgroup.zpowers t, ∃ b ∈ Subgroup.zpowers z, a * b = e := by
  have hle : Subgroup.zpowers t ≤ Subgroup.normalizer (Subgroup.zpowers z : Set G) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr ?_)
    intro w hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    exact ((htz.zpow_right k).eq).symm
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hle, Set.mem_mul]
  rfl

theorem twoCore_inf_centralizer_ne_bot (hchar : IsCharTwoType G) {M : Subgroup G}
    (hM : IsTwoLocal M) {p : ℕ} [hpf : Fact p.Prime] (hp2 : p ≠ 2) {Q' T : Subgroup G}
    (hQ' : IsPGroup p Q') (hQ'M : Q' ≤ M) (hTQ' : T ≤ Q') (hne : T ≠ Q') {z t : G}
    (hzT : z ∈ T) (htT : t ∈ T) (hzc : ∀ g ∈ T, Commute z g) (htc : ∀ g ∈ T, Commute t g)
    (hzp : orderOf z = p) (htp : orderOf t = p) (htz : t ∉ Subgroup.zpowers z)
    (hΩ : ∀ g ∈ T, (∀ h ∈ T, Commute g h) → g ^ p = 1 →
      g ∈ Subgroup.zpowers t ⊔ Subgroup.zpowers z)
    (hQC : Q' ⊓ Subgroup.centralizer ({z} : Set G) ≤ T) :
    pCoreOf 2 M ⊓ Subgroup.centralizer ({z} : Set G) ≠ ⊥ := by
  have hp : p.Prime := hpf.out
  intro hbot
  obtain ⟨x, hxQ', hxN, hmove⟩ := exists_mem_normalizer_not_mem_zpowers hQ' hTQ' hne hzp hQC
  set E := Subgroup.zpowers t ⊔ Subgroup.zpowers z with hEdef
  have htzc : Commute t z := htc z hzT
  have hET : E ≤ T := sup_le (Subgroup.zpowers_le.mpr htT) (Subgroup.zpowers_le.mpr hzT)
  have hEcent : ∀ e ∈ E, ∀ h ∈ T, Commute e h := by
    intro e he h hh
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_zpowers_sup_zpowers_iff htzc).mp he
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact ((htc h hh).zpow_left i).mul_left ((hzc h hh).zpow_left j)
  have hEc : ∀ a ∈ E, ∀ b ∈ E, Commute a b := fun a ha b hb => hEcent a ha b (hET hb)
  have hEp : ∀ e ∈ E, e ^ p = 1 := by
    intro e he
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_zpowers_sup_zpowers_iff htzc).mp he
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    have htp1 : t ^ p = 1 := htp ▸ pow_orderOf_eq_one t
    have hzp1 : z ^ p = 1 := hzp ▸ pow_orderOf_eq_one z
    rw [(htzc.zpow_zpow i j).mul_pow, ← zpow_natCast (t ^ i), ← zpow_natCast (z ^ j),
      ← zpow_mul, ← zpow_mul, mul_comm i, mul_comm j, zpow_mul, zpow_mul, zpow_natCast,
      zpow_natCast, htp1, hzp1, one_zpow, one_zpow, one_mul]
  have hbotE := zpowers_inf_zpowers_eq_bot_of_not_mem htp htz
  have hEcard : Nat.card E = p ^ 2 := by
    apply le_antisymm
    · have hpr : Nat.card (Subgroup.zpowers t × Subgroup.zpowers z) = p ^ 2 := by
        rw [Nat.card_prod, Nat.card_zpowers, Nat.card_zpowers, htp, hzp, sq]
      rw [← hpr]
      refine Nat.card_le_card_of_surjective
        (fun y : Subgroup.zpowers t × Subgroup.zpowers z => (⟨(y.1 : G) * (y.2 : G),
          (mem_zpowers_sup_zpowers_iff htzc).mpr ⟨_, y.1.2, _, y.2.2, rfl⟩⟩ : E)) ?_
      rintro ⟨e, he⟩
      obtain ⟨a, ha, b, hb, rfl⟩ := (mem_zpowers_sup_zpowers_iff htzc).mp he
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
    · have h := mul_card_le_of_inf_eq_bot (le_sup_left : Subgroup.zpowers t ≤ E)
        (le_sup_right : Subgroup.zpowers z ≤ E) hbotE
      rwa [Nat.card_zpowers, Nat.card_zpowers, htp, hzp, ← sq] at h
  have hxE : x ∈ Subgroup.normalizer (E : Set G) := by
    apply mem_normalizer_of_conj_map_le
    rintro _ ⟨e, he, rfl⟩
    have heT := hET he
    have hxeT : x * e * x⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp hxN e).mp heT
    refine hΩ _ hxeT (fun h hh => ?_) ?_
    · have hxinv : x⁻¹ ∈ Subgroup.normalizer (T : Set G) := Subgroup.inv_mem _ hxN
      have hh' : x⁻¹ * h * x⁻¹⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp hxinv h).mp hh
      have hc := (hEcent e he _ hh').eq
      show x * e * x⁻¹ * h = h * (x * e * x⁻¹)
      calc x * e * x⁻¹ * h = x * (e * (x⁻¹ * h * x⁻¹⁻¹)) * x⁻¹ := by group
        _ = x * ((x⁻¹ * h * x⁻¹⁻¹) * e) * x⁻¹ := by rw [hc]
        _ = h * (x * e * x⁻¹) := by group
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [conj_pow, hEp e he, mul_one, mul_inv_cancel]
  have hx : IsPGroup p (Subgroup.zpowers x) := hQ'.to_le (Subgroup.zpowers_le.mpr hxQ')
  have hzE : z ∈ E := Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
  have hQ2 : ¬ p ∣ Nat.card (pCoreOf 2 M) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 M)
    rw [hk]
    intro hdvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd))
  have hEQ : E ≤ Subgroup.normalizer (pCoreOf 2 M : Set G) :=
    (hET.trans (hTQ'.trans hQ'M)).trans (localGroup_le_normalizer_pCoreOf 2 M)
  have hxQ : x ∈ Subgroup.normalizer (pCoreOf 2 M : Set G) :=
    localGroup_le_normalizer_pCoreOf 2 M (hQ'M hxQ')
  obtain ⟨w, hwE, hw1, hle⟩ := exists_le_centralizer_of_moves hEc hEp hEcard hxE hx hzE hmove
    hQ2 hEQ hxQ hbot
  have hwM : w ∈ M := hQ'M (hTQ' (hET hwE))
  have hwC : w ∈ Subgroup.centralizer (pCoreOf 2 M : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun q hq => Subgroup.mem_centralizer_singleton_iff.mp
      (hle hq)
  have hwQ := hchar M hM ⟨hwM, hwC⟩
  obtain ⟨k, hk⟩ := (RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 M) ⟨w, hwQ⟩
  have hwk : w ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hwp : orderOf w = p := orderOf_eq_prime (hEp w hwE) hw1
  have hdvd : p ∣ 2 ^ k := hwp ▸ orderOf_dvd_of_pow_eq_one hwk
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd))

end CFSG.AGLEmbedding
