module

public import CFSG.LocalAnalysis.AGLEmbedding.SurvivorTheoremZ
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeAmbientCentralizerGeneration

public section

namespace CFSG.AGLEmbedding

open CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem le_centralizer_of_inf_le {p : ℕ} [Fact p.Prime] {E Q : Subgroup G}
    (hEp : ∀ e ∈ E, e ^ p = 1) (hEcard : Nat.card E = p ^ 2) {x : G}
    {z w : G} (hwE : w ∈ E) (hw1 : w ≠ 1) (hxw : x * w * x⁻¹ = w)
    (hax : ∀ e ∈ E, e ∉ Subgroup.zpowers w →
      ∃ n : ℕ, x ^ n * z * (x ^ n)⁻¹ ∈ Subgroup.zpowers e)
    (hQ : ¬ p ∣ Nat.card Q) (hEQ : E ≤ Subgroup.normalizer (Q : Set G))
    (hxQ : x ∈ Subgroup.normalizer (Q : Set G))
    (hCz : Q ⊓ Subgroup.centralizer ({z} : Set G) ≤ Subgroup.centralizer ({w} : Set G)) :
    Q ≤ Subgroup.centralizer ({w} : Set G) := by
  have hp : p.Prime := Fact.out
  have hgen := CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane
    p hp E Q (fun e => Subtype.ext (by simpa using hEp e e.2)) hEcard hQ hEQ
  rw [hgen]
  refine iSup_le fun e => iSup_le fun he1 => ?_
  have he1' : (e : G) ≠ 1 := fun h => he1 (Subtype.ext h)
  have hep : orderOf (e : G) = p := orderOf_eq_prime (hEp e e.2) he1'
  by_cases hew : (e : G) ∈ Subgroup.zpowers w
  ·
    have hwp : orderOf w = p := orderOf_eq_prime (hEp w hwE) hw1
    have heq : Subgroup.zpowers (e : G) = Subgroup.zpowers w :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hew)
        (by rw [Nat.card_zpowers, Nat.card_zpowers, hep, hwp])
    have hwe : w ∈ Subgroup.zpowers (e : G) := heq ▸ Subgroup.mem_zpowers w
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hwe
    intro q hq
    have hqe : Commute q (e : G) := Subgroup.mem_centralizer_singleton_iff.mp hq.2
    rw [Subgroup.mem_centralizer_singleton_iff, ← hk]
    exact (hqe.zpow_right k).eq
  · have hxpow : ∀ m : ℕ, x ^ m * w * (x ^ m)⁻¹ = w := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        calc x ^ (m + 1) * w * (x ^ (m + 1))⁻¹ = x ^ m * (x * w * x⁻¹) * (x ^ m)⁻¹ := by group
          _ = w := by rw [hxw, ih]
    obtain ⟨n, hn⟩ := hax e e.2 hew
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hn
    intro q hq
    have hxnQ : (x ^ n)⁻¹ ∈ Subgroup.normalizer (Q : Set G) :=
      Subgroup.inv_mem _ (Subgroup.pow_mem _ hxQ n)
    have hq' : (x ^ n)⁻¹ * q * ((x ^ n)⁻¹)⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp hxnQ q).mp hq.1
    have hqe : Commute q (e : G) := Subgroup.mem_centralizer_singleton_iff.mp hq.2
    have hqc : Commute q (x ^ n * z * (x ^ n)⁻¹) := by
      rw [← hk]
      exact hqe.zpow_right k
    have hq'' : (x ^ n)⁻¹ * q * ((x ^ n)⁻¹)⁻¹ ∈ Q ⊓ Subgroup.centralizer ({z} : Set G) := by
      refine ⟨hq', Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have h1 : q * (x ^ n * z * (x ^ n)⁻¹) = (x ^ n * z * (x ^ n)⁻¹) * q := hqc.eq
      calc (x ^ n)⁻¹ * q * ((x ^ n)⁻¹)⁻¹ * z
          = (x ^ n)⁻¹ * (q * (x ^ n * z * (x ^ n)⁻¹)) * x ^ n := by group
        _ = (x ^ n)⁻¹ * ((x ^ n * z * (x ^ n)⁻¹) * q) * x ^ n := by rw [h1]
        _ = z * ((x ^ n)⁻¹ * q * ((x ^ n)⁻¹)⁻¹) := by group
    have hxnw := hxpow n
    have h2 : (x ^ n)⁻¹ * q * ((x ^ n)⁻¹)⁻¹ * w = w * ((x ^ n)⁻¹ * q * ((x ^ n)⁻¹)⁻¹) :=
      Subgroup.mem_centralizer_singleton_iff.mp (hCz hq'')
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc q * w = q * (x ^ n * w * (x ^ n)⁻¹) := by rw [hxnw]
      _ = x ^ n * ((x ^ n)⁻¹ * q * ((x ^ n)⁻¹)⁻¹ * w) * (x ^ n)⁻¹ := by group
      _ = x ^ n * (w * ((x ^ n)⁻¹ * q * ((x ^ n)⁻¹)⁻¹)) * (x ^ n)⁻¹ := by rw [h2]
      _ = (x ^ n * w * (x ^ n)⁻¹) * q := by group
      _ = w * q := by rw [hxnw]

theorem exists_center_orderOf_eq {p : ℕ} [Fact p.Prime] {Q' : Subgroup G} (hQ' : IsPGroup p Q')
    (hne : Q' ≠ ⊥) : ∃ g ∈ Q', orderOf g = p ∧ ∀ h ∈ Q', Commute g h := by
  have hp : p.Prime := Fact.out
  have : Nontrivial Q' := by
    obtain ⟨a, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
    exact ⟨⟨a, 1, ha1⟩⟩
  have hZ : Nontrivial (Subgroup.center Q') := hQ'.center_nontrivial
  have hZp : IsPGroup p (Subgroup.center Q') := hQ'.to_subgroup _
  have hdvd : p ∣ Nat.card (Subgroup.center Q') := by
    rcases hZp.card_eq_or_dvd with h1 | h1
    · exact absurd h1 (Finite.one_lt_card).ne'
    · exact h1
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' p hdvd
  refine ⟨((c : Q') : G), (c : Q').2, ?_, fun h hh => ?_⟩
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hc]
  · have := Subgroup.mem_center_iff.mp c.2 ⟨h, hh⟩
    exact (congrArg Subtype.val this).symm

theorem mem_of_inf_ne_bot {p : ℕ} [Fact p.Prime] {Q' Y : Subgroup G} (hQ' : IsPGroup p Q')
    (hQ'Y : Q' ≤ Subgroup.normalizer (Y : Set G)) (hY : Y ⊓ Q' ≠ ⊥) {w : G}
    (hwp : orderOf w = p)
    (hΩ : ∀ g ∈ Q', (∀ h ∈ Q', Commute g h) → g ^ p = 1 → g ∈ Subgroup.zpowers w) :
    w ∈ Y := by
  have hp : p.Prime := Fact.out
  have : Group.IsNilpotent Q' := hQ'.isNilpotent
  set H : Subgroup Q' := (Y ⊓ Q').subgroupOf Q' with hH
  have hHn : H.Normal := by
    refine ⟨fun a ha g => ?_⟩
    refine ⟨?_, (Subgroup.mul_mem _ (Subgroup.mul_mem _ g.2 a.2) (Subgroup.inv_mem _ g.2))⟩
    exact (Subgroup.mem_normalizer_iff.mp (hQ'Y g.2) a).mp ha.1
  have hH1 : H ≠ ⊥ := by
    intro h
    apply hY
    rw [← Subgroup.map_subgroupOf_eq_of_le (inf_le_right : Y ⊓ Q' ≤ Q'), ← hH, h, Subgroup.map_bot]
  have hHZ := Group.IsNilpotent.inf_center_ne_bot_of_normal hH1
  have hHZp : IsPGroup p (H ⊓ Subgroup.center Q' : Subgroup Q') :=
    (hQ'.to_subgroup (H ⊓ Subgroup.center Q'))
  have : Nontrivial (H ⊓ Subgroup.center Q' : Subgroup Q') := by
    obtain ⟨a, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hHZ
    exact ⟨⟨a, 1, ha1⟩⟩
  have hdvd : p ∣ Nat.card (H ⊓ Subgroup.center Q' : Subgroup Q') := by
    rcases hHZp.card_eq_or_dvd with h1 | h1
    · exact absurd h1 (Finite.one_lt_card).ne'
    · exact h1
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' p hdvd
  set g : G := ((c : Q') : G) with hg
  have hgp : orderOf g = p := by rw [hg, Subgroup.orderOf_coe, Subgroup.orderOf_coe, hc]
  have hgY : g ∈ Y := c.2.1.1
  have hgc : ∀ h ∈ Q', Commute g h := fun h hh =>
    (congrArg Subtype.val (Subgroup.mem_center_iff.mp c.2.2 ⟨h, hh⟩)).symm
  have hgw : g ∈ Subgroup.zpowers w :=
    hΩ g (c : Q').2 hgc (by rw [← hgp]; exact pow_orderOf_eq_one g)
  have hg1 : g ≠ 1 := fun h => hp.one_lt.ne' (by rw [← hgp, h, orderOf_one])
  have heq : Subgroup.zpowers g = Subgroup.zpowers w :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hgw)
      (by rw [Nat.card_zpowers, Nat.card_zpowers, hgp, hwp])
  have hwg : w ∈ Subgroup.zpowers g := heq ▸ Subgroup.mem_zpowers w
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hwg
  exact Subgroup.zpow_mem _ hgY k

omit [Finite G] in
theorem pCorePreimage_inf_le_of_coprime {p : ℕ} [Fact p.Prime] {M X : Subgroup G}
    (hX : Nat.Coprime p (Nat.card X)) : pCorePreimage p M ⊓ X ≤ pCoreOf 2 M := by
  rintro y ⟨⟨m', hm', hmm'⟩, hyX⟩
  have hmm'' : (m' : G) = y := hmm'
  obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (p := p) (G := ↥M ⧸ CFSG.pCore 2 ↥M)
    ⟨QuotientGroup.mk' (CFSG.pCore 2 ↥M) m', hm'⟩
  have hk' : QuotientGroup.mk' (CFSG.pCore 2 ↥M) m' ^ p ^ k = 1 := congrArg Subtype.val hk
  have hord1 : orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥M) m') ∣ p ^ k :=
    orderOf_dvd_of_pow_eq_one hk'
  have hord2 : orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥M) m') ∣ Nat.card X :=
    (orderOf_map_dvd _ _).trans (by
      rw [← Subgroup.orderOf_coe, hmm'']
      exact Subgroup.orderOf_dvd_natCard _ hyX)
  have hcop : Nat.Coprime (p ^ k) (Nat.card X) := Nat.Coprime.pow_left k hX
  have h1 : orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥M) m') = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop hord1 hord2
  rw [← hmm'']
  exact coe_mem_pCoreOf_two_of_mk_eq_one m' (orderOf_eq_one_iff.mp h1)

omit [Finite G] in
theorem mem_zpowers_of_mem_normalizer {R E : Subgroup G} {p : ℕ} {x z w n : G}
    (hxR : x ∈ Subgroup.normalizer (R : Set G)) (hxnR : x ∉ R)
    (hx : IsPGroup p (Subgroup.zpowers x)) (hxw : x * w * x⁻¹ = w)
    (hax : ∀ e ∈ E, e ∉ Subgroup.zpowers w →
      ∃ m : ℕ, x ^ m * z * (x ^ m)⁻¹ ∈ Subgroup.zpowers e)
    (hB0 : ∀ y ∈ Subgroup.normalizer (R : Set G), y * z * y⁻¹ = z →
      IsPGroup p (Subgroup.zpowers y) → y ∈ R)
    (hnR : n ∈ Subgroup.normalizer (R : Set G)) (hnE : n * w * n⁻¹ ∈ E) :
    n * w * n⁻¹ ∈ Subgroup.zpowers w := by
  by_contra h
  obtain ⟨m, hm⟩ := hax _ hnE h
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hm
  set n₀ := n⁻¹ * x ^ m with hn₀
  have hn₀R : n₀ ∈ Subgroup.normalizer (R : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hnR) (Subgroup.pow_mem _ hxR m)
  have hwk : n * w ^ k * n⁻¹ = (n * w * n⁻¹) ^ k := by
    rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply]
  have hn₀z : n₀ * z * n₀⁻¹ = w ^ k := by
    have h1 : x ^ m * z * (x ^ m)⁻¹ = n * w ^ k * n⁻¹ := by rw [hwk, hk]
    calc n₀ * z * n₀⁻¹ = n⁻¹ * (x ^ m * z * (x ^ m)⁻¹) * n := by rw [hn₀]; group
      _ = n⁻¹ * (n * w ^ k * n⁻¹) * n := by rw [h1]
      _ = w ^ k := by group
  set y := n₀⁻¹ * x * n₀ with hy
  have hxwk : x * w ^ k * x⁻¹ = w ^ k := by
    rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, hxw]
  have hyz : y * z * y⁻¹ = z := by
    calc y * z * y⁻¹ = n₀⁻¹ * (x * (n₀ * z * n₀⁻¹) * x⁻¹) * n₀ := by rw [hy]; group
      _ = n₀⁻¹ * (n₀ * z * n₀⁻¹) * n₀ := by rw [hn₀z, hxwk]
      _ = z := by group
  have hyR : y ∈ Subgroup.normalizer (R : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hn₀R) hxR) hn₀R
  obtain ⟨j, hj⟩ := hx ⟨x, Subgroup.mem_zpowers x⟩
  have hxj : x ^ p ^ j = 1 := by simpa using congrArg Subtype.val hj
  have hyj : y ^ p ^ j = 1 := by
    have h1 : y = n₀⁻¹ * x * (n₀⁻¹)⁻¹ := by rw [hy, inv_inv]
    rw [h1, conj_pow, hxj, mul_one, mul_inv_cancel]
  have hyR' : y ∈ R := hB0 y hyR hyz (isPGroup_zpowers_of_pow_eq_one hyj)
  apply hxnR
  have : x = n₀ * y * n₀⁻¹ := by rw [hy]; group
  rw [this]
  exact (Subgroup.mem_normalizer_iff.mp hn₀R y).mp hyR'

end CFSG.AGLEmbedding
