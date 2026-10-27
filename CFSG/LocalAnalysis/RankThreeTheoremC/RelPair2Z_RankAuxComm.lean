module

public import Mathlib.GroupTheory.PGroup
import CFSG.LocalAnalysis.SignalizerFunctor.AmbientCommutators
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeAmbientCentralizerGeneration
import CFSG.RankThree.PartTwo.Sec13.Item135CritProof

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open Subgroup
open scoped commutatorElement

theorem zjr_conj_mem_map {Y : Type*} [Group Y] {Q : Subgroup Y} {Ω : Subgroup Q}
    (hΩ : Ω.Characteristic) {g : Y} (hg : g ∈ normalizer (Q : Set Y)) {h : Y}
    (hh : h ∈ Ω.map Q.subtype) : g * h * g⁻¹ ∈ Ω.map Q.subtype := by
  obtain ⟨x, hx, rfl⟩ := mem_map.1 hh
  have := CFSG.SectionRank.Ccomm.char_apply_mem hΩ (Q.normalizerMonoidHom ⟨g, hg⟩) hx
  exact ⟨_, this, rfl⟩

theorem zjr_exists_reduction {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {Y : Type*} [Group Y]
    [Finite Y] {D Q : Subgroup Y} (hDp : ∀ d ∈ D, d ^ p = 1) (hQ : IsPGroup 3 Q)
    (hDQ : D ≤ normalizer (Q : Set Y)) (hfaith : D ⊓ centralizer (Q : Set Y) = ⊥) :
    ∃ R : Subgroup Y, R ≤ Q ∧ D ≤ normalizer (R : Set Y) ∧ D ⊓ centralizer (R : Set Y) = ⊥ ∧
      (∀ x ∈ R, x ^ 3 = 1) ∧ ⁅R, R⁆ ≤ centralizer (R : Set Y) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨C, -, -, -, -, hchar, -, hcomm, hexp, -, hdet⟩ :=
    CFSG.RankThree.PartTwo.Sec13.CritProof.exists_isThompsonCritical_omega (P := Q) (p := 3)
      (by norm_num) hQ
  set Ω := CFSG.RankThree.PartTwo.Sec13.CritProof.omegaOneIn 3 C with hΩ
  refine ⟨Ω.map Q.subtype, map_subtype_le _, ?_, ?_, ?_, ?_⟩
  · intro d hd
    rw [mem_normalizer_iff]
    intro h
    refine ⟨zjr_conj_mem_map hchar (hDQ hd), fun h1 => ?_⟩
    have := zjr_conj_mem_map hchar (hDQ (inv_mem hd)) h1
    simpa [mul_assoc] using this
  · rw [eq_bot_iff]
    intro d hd
    obtain ⟨hdD, hdR⟩ := mem_inf.1 hd
    have hdQ := hDQ hdD
    set σ : MulAut Q := Q.normalizerMonoidHom ⟨d, hdQ⟩ with hσ
    have hσapp : ∀ y : Q, ((σ y : Q) : Y) = d * y * d⁻¹ := fun y => rfl
    have hord : orderOf σ ∣ p := by
      refine orderOf_dvd_of_pow_eq_one ?_
      rw [hσ, ← map_pow]
      have : (⟨d, hdQ⟩ : normalizer (Q : Set Y)) ^ p = 1 := Subtype.ext (hDp d hdD)
      rw [this, map_one]
    have hcop : (orderOf σ).Coprime 3 :=
      Nat.Coprime.coprime_dvd_left hord ((Nat.coprime_primes hp Nat.prime_three).2 (by omega))
    have hfix : ∀ x ∈ Ω, σ x = x := by
      intro x hx
      apply Subtype.ext
      rw [hσapp]
      have hxR : (x : Y) ∈ Ω.map Q.subtype := ⟨x, hx, rfl⟩
      have hc := mem_centralizer_iff.1 hdR _ hxR
      calc d * (x : Y) * d⁻¹ = ((x : Y) * d) * d⁻¹ := by rw [hc]
        _ = x := by group
    have h1 := hdet σ hcop hfix
    have hdc : d ∈ centralizer (Q : Set Y) := by
      rw [mem_centralizer_iff]
      intro q hq
      have := congrArg (fun τ : MulAut Q => ((τ ⟨q, hq⟩ : Q) : Y)) h1
      simp only [MulAut.one_apply] at this
      rw [hσapp] at this
      change d * q * d⁻¹ = q at this
      calc q * d = (d * q * d⁻¹) * d := by rw [this]
        _ = d * q := by group
    have : d ∈ D ⊓ centralizer (Q : Set Y) := mem_inf.2 ⟨hdD, hdc⟩
    rw [hfaith] at this
    exact this
  · rintro _ ⟨x, hx, rfl⟩
    have := hexp x hx
    rw [← map_pow]
    simp [this]
  · refine commutator_le.2 fun g₁ hg₁ g₂ hg₂ => ?_
    obtain ⟨y₁, hy₁, rfl⟩ := mem_map.1 hg₁
    obtain ⟨y₂, hy₂, rfl⟩ := mem_map.1 hg₂
    have hc : ⁅y₁, y₂⁆ ∈ centralizer (Ω : Set Q) :=
      (hcomm (commutator_mem_commutator hy₁ (mem_top y₂))).2
    rw [mem_centralizer_iff]
    rintro _ ⟨z, hz, rfl⟩
    have := congrArg Q.subtype (mem_centralizer_iff.1 hc z hz)
    simpa [commutatorElement_def] using this

theorem zjr_zpowers_or_top {p : ℕ} (hp : p.Prime) {Y : Type*} [Group Y] [Finite Y]
    {D K : Subgroup Y} (hDp : ∀ d ∈ D, d ^ p = 1) (hDc : Nat.card D = p ^ 2) {a : Y}
    (haD : a ∈ D) (ha1 : a ≠ 1) (hKD : K ≤ D) (hK : a ∈ K) : K = zpowers a ∨ K = D := by
  have : Fact p.Prime := ⟨hp⟩
  have hord : orderOf a = p := orderOf_eq_prime (hDp a haD) ha1
  have hz : zpowers a ≤ K := (zpowers_le).2 hK
  have h1 : p ∣ Nat.card K := by
    have := Subgroup.card_dvd_of_le hz
    rwa [Nat.card_zpowers, hord] at this
  have h2 : Nat.card K ∣ p ^ 2 := hDc ▸ Subgroup.card_dvd_of_le hKD
  obtain ⟨k, hk, hkK⟩ := (Nat.dvd_prime_pow hp).1 h2
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hkK
    rw [hkK] at h1
    exact hp.one_lt.ne' (Nat.dvd_one.1 h1)
  have hk12 : k = 1 ∨ k = 2 := by omega
  rcases hk12 with rfl | rfl
  · left
    refine (Subgroup.eq_of_le_of_card_ge hz ?_).symm
    rw [Nat.card_zpowers, hord, hkK, pow_one]
  · right
    exact Subgroup.eq_of_le_of_card_ge hKD (by rw [hDc, hkK])

theorem zjr_centralizer_le_of_mem_zpowers {Y : Type*} [Group Y] {a b : Y} (hb : b ∈ zpowers a) :
    centralizer ({a} : Set Y) ≤ centralizer ({b} : Set Y) := by
  intro x hx
  rw [mem_centralizer_iff] at hx ⊢
  intro h hh
  rw [Set.mem_singleton_iff.1 hh]
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hb
  have := hx a rfl
  exact ((Commute.zpow_left (show Commute a x from this) k)).eq

theorem zjr_exists_pair {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) {Y : Type*} [Group Y] [Finite Y]
    {D R : Subgroup Y} (hDp : ∀ d ∈ D, d ^ p = 1) (hDc : Nat.card D = p ^ 2)
    (hR : IsPGroup 3 R) (hDR : D ≤ normalizer (R : Set Y))
    (hfaith : D ⊓ centralizer (R : Set Y) = ⊥) :
    ∃ a₁ ∈ D, a₁ ≠ 1 ∧ ∃ a₂ ∈ D, a₂ ∉ zpowers a₁ ∧
      (∀ d ∈ D, d ∈ centralizer ((R ⊓ centralizer ({a₁} : Set Y) : Subgroup Y) : Set Y) →
        d ∈ zpowers a₁) ∧
      (∀ d ∈ D, d ∈ centralizer ((R ⊓ centralizer ({a₂} : Set Y) : Subgroup Y) : Set Y) →
        d ∈ zpowers a₂) := by
  have : Fact p.Prime := ⟨hp⟩
  have hcomplement : ¬ p ∣ Nat.card R := by
    obtain ⟨n, hn⟩ := hR.exists_card_eq
    rw [hn]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h)
    exact hp3 this
  have hpower : ∀ member : D, member ^ p = 1 := fun m => Subtype.ext (hDp m m.2)
  have hgen := CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane
    p hp D R hpower hDc hcomplement hDR
  set S : Y → Subgroup Y := fun a => R ⊓ centralizer ({a} : Set Y) with hS
  have hSR : ∀ a, S a ≤ R := fun a => inf_le_left
  have hdich : ∀ a ∈ D, a ≠ 1 → (D ≤ centralizer ((S a : Subgroup Y) : Set Y)) ∨
      (∀ d ∈ D, d ∈ centralizer ((S a : Subgroup Y) : Set Y) → d ∈ zpowers a) := by
    intro a haD ha1
    have haC : a ∈ centralizer ((S a : Subgroup Y) : Set Y) := by
      rw [mem_centralizer_iff]
      intro h hh
      exact (mem_centralizer_iff.1 (mem_inf.1 hh).2 a rfl).symm
    rcases zjr_zpowers_or_top hp hDp hDc haD ha1
      (K := D ⊓ centralizer ((S a : Subgroup Y) : Set Y)) inf_le_left
      (mem_inf.2 ⟨haD, haC⟩) with h | h
    · right
      intro d hd hdC
      have : d ∈ D ⊓ centralizer ((S a : Subgroup Y) : Set Y) := mem_inf.2 ⟨hd, hdC⟩
      rwa [h] at this
    · left
      rw [← h]
      exact inf_le_right
  have hgen' : R ≤ ⨆ (a : Y) (_ : a ∈ D) (_ : a ≠ 1), S a := by
    rw [hgen]
    refine iSup₂_le fun m hm => ?_
    exact le_iSup_of_le (m : Y) (le_iSup_of_le m.2 (le_iSup_of_le (fun h => hm (Subtype.ext h))
      le_rfl))
  have hD1 : ∀ a ∈ D, a ∈ centralizer (R : Set Y) → a = 1 := by
    intro a haD haR
    have : a ∈ D ⊓ centralizer (R : Set Y) := mem_inf.2 ⟨haD, haR⟩
    rw [hfaith, mem_bot] at this
    exact this
  obtain ⟨a₁, ha₁D, ha₁1, ha₁n⟩ : ∃ a ∈ D, a ≠ 1 ∧
      ¬ D ≤ centralizer ((S a : Subgroup Y) : Set Y) := by
    by_contra hcon
    have hall : ∀ a ∈ D, a ≠ 1 → D ≤ centralizer ((S a : Subgroup Y) : Set Y) := by
      intro a ha ha1
      by_contra h
      exact hcon ⟨a, ha, ha1, h⟩
    have hRD : R ≤ centralizer (D : Set Y) := by
      refine hgen'.trans (iSup₂_le fun a ha => iSup_le fun ha1 => ?_)
      exact le_centralizer_iff.1 (hall a ha ha1)
    have hDR' : D ≤ centralizer (R : Set Y) := le_centralizer_iff.1 hRD
    have hDbot : D = ⊥ := by
      rw [eq_bot_iff]
      intro d hd
      exact mem_bot.2 (hD1 d hd (hDR' hd))
    rw [hDbot, Subgroup.card_bot] at hDc
    have : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp.one_lt
    omega
  have h₁ := (hdich a₁ ha₁D ha₁1).resolve_left ha₁n
  obtain ⟨a₂, ha₂D, ha₂n, ha₂⟩ : ∃ a ∈ D, a ∉ zpowers a₁ ∧
      ¬ D ≤ centralizer ((S a : Subgroup Y) : Set Y) := by
    by_contra hcon
    have hall : ∀ a ∈ D, a ∉ zpowers a₁ → D ≤ centralizer ((S a : Subgroup Y) : Set Y) := by
      intro a ha han
      by_contra h
      exact hcon ⟨a, ha, han, h⟩
    have hRS : R ≤ S a₁ := by
      refine hgen'.trans (iSup₂_le fun a ha => iSup_le fun ha1 => ?_)
      by_cases han : a ∈ zpowers a₁
      · have hord : orderOf a₁ = p := orderOf_eq_prime (hDp a₁ ha₁D) ha₁1
        have hord' : orderOf a = p := orderOf_eq_prime (hDp a ha) ha1
        have hle : zpowers a ≤ zpowers a₁ := (zpowers_le).2 han
        have heq : zpowers a = zpowers a₁ := Subgroup.eq_of_le_of_card_ge hle (by
          rw [Nat.card_zpowers, Nat.card_zpowers, hord, hord'])
        have ha₁a : a₁ ∈ zpowers a := heq ▸ mem_zpowers a₁
        exact le_inf (hSR a) (inf_le_right.trans (zjr_centralizer_le_of_mem_zpowers ha₁a))
      · refine le_inf (hSR a) ?_
        have h1 : S a ≤ centralizer (D : Set Y) := le_centralizer_iff.1 (hall a ha han)
        intro x hx
        have := mem_centralizer_iff.1 (h1 hx) a₁ ha₁D
        rw [mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff.1 hh]
        exact this
    exact ha₁1 (hD1 a₁ ha₁D (by
      rw [mem_centralizer_iff]
      intro r hr
      exact (mem_centralizer_iff.1 (mem_inf.1 (hRS hr)).2 a₁ rfl).symm))
  have h₂ := (hdich a₂ ha₂D (fun h => ha₂n (h ▸ one_mem _))).resolve_left ha₂
  exact ⟨a₁, ha₁D, ha₁1, a₂, ha₂D, ha₂n, h₁, h₂⟩

theorem zjr_centralizer_zpowers {Y : Type*} [Group Y] (a : Y) :
    centralizer ((zpowers a : Subgroup Y) : Set Y) = centralizer ({a} : Set Y) := by
  rw [zpowers_eq_closure, centralizer_closure]

theorem zjr_commutator_zpowers_eq_bot_iff {Y : Type*} [Group Y] (H : Subgroup Y) (a : Y) :
    ⁅H, zpowers a⁆ = ⊥ ↔ H ≤ centralizer ({a} : Set Y) := by
  rw [commutator_eq_bot_iff_le_centralizer, zjr_centralizer_zpowers]

theorem zjr_mem_centralizer_singleton {Y : Type*} [Group Y] {a g : Y} :
    g ∈ centralizer ({a} : Set Y) ↔ a * g = g * a := by
  rw [mem_centralizer_iff]
  simp

theorem zjr_commutator_le_self {Y : Type*} [Group Y] (R : Subgroup Y) : ⁅R, R⁆ ≤ R := by
  refine commutator_le.2 fun g₁ h₁ g₂ h₂ => ?_
  rw [commutatorElement_def]
  exact R.mul_mem (R.mul_mem (R.mul_mem h₁ h₂) (R.inv_mem h₁)) (R.inv_mem h₂)

theorem zjr_commutator_le_center {Y : Type*} [Group Y] {R S : Subgroup Y} (hSR : S ≤ R)
    (hcl : ⁅R, R⁆ ≤ centralizer (R : Set Y)) :
    ⁅S, R⁆ ≤ R ⊓ centralizer (R : Set Y) :=
  le_inf ((commutator_mono hSR le_rfl).trans (zjr_commutator_le_self R))
    ((commutator_mono hSR le_rfl).trans hcl)

theorem zjr_commutator_centralizer {Y : Type*} [Group Y] {R : Subgroup Y} {a : Y}
    (hcl : ⁅R, R⁆ ≤ centralizer (R : Set Y))
    (hZa : R ⊓ centralizer (R : Set Y) ≤ centralizer ({a} : Set Y)) :
    ⁅⁅R, zpowers a⁆, R ⊓ centralizer ({a} : Set Y)⁆ = ⊥ := by
  have h1 : ⁅⁅zpowers a, R ⊓ centralizer ({a} : Set Y)⁆, R⁆ = ⊥ := by
    have : ⁅zpowers a, R ⊓ centralizer ({a} : Set Y)⁆ = ⊥ := by
      rw [commutator_comm, zjr_commutator_zpowers_eq_bot_iff]
      exact inf_le_right
    rw [this]
    exact commutator_bot_left R
  have h2 : ⁅⁅R ⊓ centralizer ({a} : Set Y), R⁆, zpowers a⁆ = ⊥ := by
    rw [zjr_commutator_zpowers_eq_bot_iff]
    exact (zjr_commutator_le_center inf_le_left hcl).trans hZa
  exact commutator_commutator_eq_bot_of_rotate h1 h2

theorem zjr_isPGroup_zpowers {p : ℕ} {Y : Type*} [Group Y] {a : Y} (hap : a ^ p = 1) :
    IsPGroup p (zpowers a) := by
  rintro ⟨g, hg⟩
  refine ⟨1, Subtype.ext ?_⟩
  obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hg
  change (a ^ m) ^ p ^ 1 = 1
  rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hap, one_zpow]

theorem zjr_comm_inf_centralizer_le {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) {Y : Type*} [Group Y]
    [Finite Y] {R : Subgroup Y} {a : Y} (hR : IsPGroup 3 R) (hap : a ^ p = 1)
    (haR : a ∈ normalizer (R : Set Y)) (hcl : ⁅R, R⁆ ≤ centralizer (R : Set Y))
    (hZa : R ⊓ centralizer (R : Set Y) ≤ centralizer ({a} : Set Y)) :
    ⁅R, zpowers a⁆ ⊓ (R ⊓ centralizer ({a} : Set Y)) ≤ R ⊓ centralizer (R : Set Y) := by
  have hnorm : zpowers a ≤ normalizer (R : Set Y) := by rwa [zpowers_le]
  have hcop : p.Coprime (Nat.card R) := by
    obtain ⟨n, hn⟩ := hR.exists_card_eq
    rw [hn]
    exact Nat.Coprime.pow_right n ((Nat.coprime_primes hp Nat.prime_three).2 hp3)
  have hfac := CFSG.SignalizerFunctor.Helpers.coprime_normalized_commutator_factorization p hp
    (zpowers a) R (zjr_isPGroup_zpowers hap) hnorm hcop
  rw [zjr_centralizer_zpowers] at hfac
  have hcomm := zjr_commutator_centralizer hcl hZa
  intro g hg
  obtain ⟨hgN, hgS⟩ := mem_inf.1 hg
  have hgR : g ∈ R := (mem_inf.1 hgS).1
  refine mem_inf.2 ⟨hgR, ?_⟩
  rw [mem_centralizer_iff]
  intro h hh
  have hRle : R ≤ centralizer ({g} : Set Y) := by
    rw [← hfac]
    refine sup_le (fun n hn => ?_) (fun s hs => ?_)
    · have h1 : n ∈ centralizer ((R ⊓ centralizer ({a} : Set Y) : Subgroup Y) : Set Y) :=
        commutator_eq_bot_iff_le_centralizer.1 hcomm hn
      rw [zjr_mem_centralizer_singleton]
      exact (mem_centralizer_iff.1 h1 g hgS)
    · have h1 : s ∈ centralizer ((⁅R, zpowers a⁆ : Subgroup Y) : Set Y) :=
        commutator_eq_bot_iff_le_centralizer.1 ((commutator_comm _ _).trans hcomm) hs
      rw [zjr_mem_centralizer_singleton]
      exact (mem_centralizer_iff.1 h1 g hgN)
  have := hRle hh
  rw [zjr_mem_centralizer_singleton] at this
  exact this.symm

theorem zjr_mem_normalizer_inf_centralizer {Y : Type*} [Group Y] {R : Subgroup Y} {a g : Y}
    (hg : g ∈ normalizer (R : Set Y)) (hga : g * a = a * g) :
    g ∈ normalizer ((R ⊓ centralizer ({a} : Set Y) : Subgroup Y) : Set Y) := by
  have key : ∀ k : Y, k ∈ normalizer (R : Set Y) → k * a = a * k → ∀ h : Y,
      h ∈ R ⊓ centralizer ({a} : Set Y) → k * h * k⁻¹ ∈ R ⊓ centralizer ({a} : Set Y) := by
    intro k hk hka h hh
    obtain ⟨hhR, hhc⟩ := mem_inf.1 hh
    refine mem_inf.2 ⟨(mem_normalizer_iff.1 hk h).1 hhR, ?_⟩
    rw [zjr_mem_centralizer_singleton] at hhc ⊢
    calc a * (k * h * k⁻¹) = (a * k) * h * k⁻¹ := by group
      _ = (k * a) * h * k⁻¹ := by rw [hka]
      _ = k * (a * h) * k⁻¹ := by group
      _ = k * (h * a) * k⁻¹ := by rw [hhc]
      _ = k * h * (a * k⁻¹) := by group
      _ = k * h * (k⁻¹ * a) := by
        congr 1
        calc a * k⁻¹ = k⁻¹ * (k * a) * k⁻¹ := by group
          _ = k⁻¹ * (a * k) * k⁻¹ := by rw [hka]
          _ = k⁻¹ * a := by group
      _ = (k * h * k⁻¹) * a := by group
  rw [mem_normalizer_iff]
  intro h
  refine ⟨key g hg hga h, fun h1 => ?_⟩
  have hginv : g⁻¹ ∈ normalizer (R : Set Y) := inv_mem hg
  have hginva : g⁻¹ * a = a * g⁻¹ := by
    calc g⁻¹ * a = g⁻¹ * (a * g) * g⁻¹ := by group
      _ = g⁻¹ * (g * a) * g⁻¹ := by rw [hga]
      _ = a * g⁻¹ := by group
  have := key g⁻¹ hginv hginva _ h1
  simpa [mul_assoc] using this

theorem zjr_comm_B_pair {Y : Type*} [Group Y] {R : Subgroup Y} {a b : Y}
    (hbR : b ∈ normalizer (R : Set Y)) (hab : a * b = b * a)
    (hcl : ⁅R, R⁆ ≤ centralizer (R : Set Y))
    (hZa : R ⊓ centralizer (R : Set Y) ≤ centralizer ({a} : Set Y)) :
    ⁅⁅R ⊓ centralizer ({a} : Set Y), zpowers b⁆, ⁅R ⊓ centralizer ({b} : Set Y), zpowers a⁆⁆ =
      ⊥ := by
  have hbS : zpowers b ≤ normalizer ((R ⊓ centralizer ({a} : Set Y) : Subgroup Y) : Set Y) := by
    rw [zpowers_le]
    exact zjr_mem_normalizer_inf_centralizer hbR hab.symm
  have h1 : ⁅R ⊓ centralizer ({a} : Set Y), zpowers b⁆ ≤ R ⊓ centralizer ({a} : Set Y) :=
    CFSG.SignalizerFunctor.Helpers.commutator_le_of_normalizing _ _ hbS
  have h2 : ⁅R ⊓ centralizer ({b} : Set Y), zpowers a⁆ ≤ ⁅R, zpowers a⁆ :=
    commutator_mono inf_le_left le_rfl
  refine eq_bot_iff.2 ?_
  calc ⁅⁅R ⊓ centralizer ({a} : Set Y), zpowers b⁆, ⁅R ⊓ centralizer ({b} : Set Y), zpowers a⁆⁆
      ≤ ⁅R ⊓ centralizer ({a} : Set Y), ⁅R, zpowers a⁆⁆ := commutator_mono h1 h2
    _ = ⁅⁅R, zpowers a⁆, R ⊓ centralizer ({a} : Set Y)⁆ := commutator_comm _ _
    _ = ⊥ := zjr_commutator_centralizer hcl hZa
    _ ≤ ⊥ := le_rfl

theorem zjr_B_not_centralized {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) {Y : Type*} [Group Y]
    [Finite Y] {R : Subgroup Y} {a b : Y} (hR : IsPGroup 3 R) (hbp : b ^ p = 1)
    (hbR : b ∈ normalizer (R : Set Y)) (hab : a * b = b * a) (hba : b ∉ zpowers a)
    (hb : b ∈ centralizer ((R ⊓ centralizer ({a} : Set Y) : Subgroup Y) : Set Y) →
      b ∈ zpowers a) :
    ¬ ⁅R ⊓ centralizer ({a} : Set Y), zpowers b⁆ ≤ centralizer ({b} : Set Y) := by
  intro h
  have hbS : zpowers b ≤ normalizer ((R ⊓ centralizer ({a} : Set Y) : Subgroup Y) : Set Y) := by
    rw [zpowers_le]
    exact zjr_mem_normalizer_inf_centralizer hbR hab.symm
  have hcop : p.Coprime (Nat.card (R ⊓ centralizer ({a} : Set Y) : Subgroup Y)) := by
    obtain ⟨n, hn⟩ := (hR.to_le (inf_le_left : R ⊓ centralizer ({a} : Set Y) ≤ R)).exists_card_eq
    rw [hn]
    exact Nat.Coprime.pow_right n ((Nat.coprime_primes hp Nat.prime_three).2 hp3)
  have h0 : ⁅⁅R ⊓ centralizer ({a} : Set Y), zpowers b⁆, zpowers b⁆ = ⊥ :=
    (zjr_commutator_zpowers_eq_bot_iff _ b).2 h
  have h1 := CFSG.SignalizerFunctor.Helpers.coprime_normalized_commutator_idempotent p hp
    (zpowers b) (R ⊓ centralizer ({a} : Set Y)) (zjr_isPGroup_zpowers hbp) hbS hcop
  rw [h0] at h1
  have h2 : R ⊓ centralizer ({a} : Set Y) ≤ centralizer ({b} : Set Y) :=
    (zjr_commutator_zpowers_eq_bot_iff _ b).1 h1.symm
  apply hba
  refine hb ?_
  rw [mem_centralizer_iff]
  intro s hs
  exact (zjr_mem_centralizer_singleton.1 (h2 hs)).symm

end CFSG.LocalAnalysis.RankThreeTheoremC
