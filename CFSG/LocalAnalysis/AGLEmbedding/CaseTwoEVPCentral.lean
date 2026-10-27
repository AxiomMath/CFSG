module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoEVAxis
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNoSPOdd
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNoSPTransvect
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBOneChar

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

theorem exists_pcentral_axis (hchar : IsCharTwoType G) {M : Subgroup G} (hM : IsTwoLocal M)
    {p : ℕ} [hpf : Fact p.Prime] (hp2 : p ≠ 2) {Q' T : Subgroup G}
    (hQ' : IsPGroup p Q') (hQ'M : Q' ≤ M) (hTQ' : T ≤ Q') (hne : T ≠ Q') {z t : G}
    (hzT : z ∈ T) (htT : t ∈ T) (hzc : ∀ g ∈ T, Commute z g) (htc : ∀ g ∈ T, Commute t g)
    (hzp : orderOf z = p) (htp : orderOf t = p) (htz : t ∉ Subgroup.zpowers z)
    (hΩ : ∀ g ∈ T, (∀ h ∈ T, Commute g h) → g ^ p = 1 →
      g ∈ Subgroup.zpowers t ⊔ Subgroup.zpowers z)
    (hQC : Q' ⊓ Subgroup.centralizer ({z} : Set G) ≤ T) :
    ∃ w ∈ T, orderOf w = p ∧ w ∉ Subgroup.zpowers z ∧ (∀ g ∈ T, Commute w g) ∧
      (∀ g ∈ Q', Commute w g) ∧
      (∀ g ∈ Q', (∀ h ∈ Q', Commute g h) → g ^ p = 1 → g ∈ Subgroup.zpowers w) ∧
      ¬ (pCoreOf 2 M ⊓ Subgroup.centralizer ({z} : Set G) ≤
        Subgroup.centralizer ({w} : Set G)) ∧
      ((∀ y ∈ Subgroup.normalizer (T : Set G), y * z * y⁻¹ = z →
        IsPGroup p (Subgroup.zpowers y) → y ∈ T) →
        ∀ n ∈ Subgroup.normalizer (T : Set G), n * w * n⁻¹ ∈ Subgroup.zpowers w) := by
  have hp : p.Prime := hpf.out
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
  obtain ⟨w, hwE, hw1, hxw, hax⟩ := exists_axis hEc hEp hEcard hxE hx hzE hmove
  have hwT : w ∈ T := hET hwE
  have hwp : orderOf w = p := orderOf_eq_prime (hEp w hwE) hw1
  have hxwk : ∀ k : ℤ, x * w ^ k * x⁻¹ = w ^ k := fun k => by
    rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, hxw]
  have hwz : w ∉ Subgroup.zpowers z := by
    intro hwz
    have heq : Subgroup.zpowers w = Subgroup.zpowers z :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hwz)
        (by rw [Nat.card_zpowers, Nat.card_zpowers, hwp, hzp])
    have hzw : z ∈ Subgroup.zpowers w := heq ▸ Subgroup.mem_zpowers z
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hzw
    apply hmove
    rw [← hk, hxwk k]
    exact Subgroup.mem_zpowers _
  have hΩQ : ∀ g ∈ Q', (∀ h ∈ Q', Commute g h) → g ^ p = 1 → g ∈ Subgroup.zpowers w := by
    intro g hg hgc hgp
    have hgz : g ∈ Subgroup.centralizer ({z} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (hgc z (hTQ' hzT)).eq
    have hgT : g ∈ T := hQC ⟨hg, hgz⟩
    have hgE : g ∈ E := hΩ g hgT (fun h hh => hgc h (hTQ' hh)) hgp
    by_contra hgw
    obtain ⟨n, hn⟩ := hax g hgE hgw
    have hxg : Commute x g := (hgc x hxQ').symm
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hn
    have hzg : z = g ^ k := by
      have h2 : Commute (x ^ n) (g ^ k) := (hxg.pow_left n).zpow_right k
      calc z = (x ^ n)⁻¹ * (x ^ n * z * (x ^ n)⁻¹) * x ^ n := by group
        _ = (x ^ n)⁻¹ * (g ^ k) * x ^ n := by rw [hk]
        _ = g ^ k * (x ^ n)⁻¹ * x ^ n := by rw [(h2.inv_left).eq]
        _ = g ^ k := by group
    apply hmove
    rw [hzg, (hxg.zpow_right k).eq, mul_inv_cancel_right]
    exact Subgroup.mem_zpowers _
  have hwQ' : ∀ g ∈ Q', Commute w g := by
    have hQ'1 : Q' ≠ ⊥ := fun h => by
      have h1 : z ∈ (⊥ : Subgroup G) := h ▸ hTQ' hzT
      rw [Subgroup.mem_bot] at h1
      exact hp.one_lt.ne' (by rw [← hzp, h1, orderOf_one])
    obtain ⟨c, hcQ, hcp, hcc⟩ := exists_center_orderOf_eq hQ' hQ'1
    have hcw : c ∈ Subgroup.zpowers w :=
      hΩQ c hcQ hcc (by rw [← hcp]; exact pow_orderOf_eq_one c)
    have heq : Subgroup.zpowers c = Subgroup.zpowers w :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hcw)
        (by rw [Nat.card_zpowers, Nat.card_zpowers, hcp, hwp])
    have hwc : w ∈ Subgroup.zpowers c := heq ▸ Subgroup.mem_zpowers w
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hwc
    intro g hg
    rw [← hk]
    exact (hcc g hg).zpow_left k
  have hA : ¬ (pCoreOf 2 M ⊓ Subgroup.centralizer ({z} : Set G) ≤
      Subgroup.centralizer ({w} : Set G)) := by
    intro hle
    have hQ2 : ¬ p ∣ Nat.card (pCoreOf 2 M) := by
      obtain ⟨k, hk⟩ :=
        IsPGroup.iff_card.mp (RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 M)
      rw [hk]
      intro hdvd
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd))
    have hEQ : E ≤ Subgroup.normalizer (pCoreOf 2 M : Set G) :=
      (hET.trans (hTQ'.trans hQ'M)).trans (localGroup_le_normalizer_pCoreOf 2 M)
    have hxQ : x ∈ Subgroup.normalizer (pCoreOf 2 M : Set G) :=
      localGroup_le_normalizer_pCoreOf 2 M (hQ'M hxQ')
    have hQw := le_centralizer_of_inf_le hEp hEcard hwE hw1 hxw hax hQ2 hEQ hxQ hle
    have hwM : w ∈ M := hQ'M (hTQ' hwT)
    have hwC : w ∈ Subgroup.centralizer (pCoreOf 2 M : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun q hq =>
        Subgroup.mem_centralizer_singleton_iff.mp (hQw hq)
    have hwQ := hchar M hM ⟨hwM, hwC⟩
    obtain ⟨k, hk⟩ := (RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 M) ⟨w, hwQ⟩
    have hwk : w ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hdvd : p ∣ 2 ^ k := hwp ▸ orderOf_dvd_of_pow_eq_one hwk
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd))
  have hnorm : (∀ y ∈ Subgroup.normalizer (T : Set G), y * z * y⁻¹ = z →
      IsPGroup p (Subgroup.zpowers y) → y ∈ T) →
      ∀ n ∈ Subgroup.normalizer (T : Set G), n * w * n⁻¹ ∈ Subgroup.zpowers w := by
    intro hB0 n hn
    have hxnT : x ∉ T := fun hxT => hmove (by
      rw [(hzc x hxT).symm.eq, mul_inv_cancel_right]
      exact Subgroup.mem_zpowers z)
    refine mem_zpowers_of_mem_normalizer hxN hxnT hx hxw hax hB0 hn ?_
    have hnwT : n * w * n⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp hn w).mp hwT
    refine hΩ _ hnwT (fun h hh => ?_) ?_
    · have hninv : n⁻¹ ∈ Subgroup.normalizer (T : Set G) := Subgroup.inv_mem _ hn
      have hh' : n⁻¹ * h * n⁻¹⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp hninv h).mp hh
      have hc := (hEcent w hwE _ hh').eq
      show n * w * n⁻¹ * h = h * (n * w * n⁻¹)
      calc n * w * n⁻¹ * h = n * (w * (n⁻¹ * h * n⁻¹⁻¹)) * n⁻¹ := by group
        _ = n * ((n⁻¹ * h * n⁻¹⁻¹) * w) * n⁻¹ := by rw [hc]
        _ = h * (n * w * n⁻¹) := by group
    · rw [conj_pow, hEp w hwE, mul_one, mul_inv_cancel]
  exact ⟨w, hwT, hwp, hwz, hEcent w hwE, hwQ', hΩQ, hA, hnorm⟩

end CFSG.AGLEmbedding
