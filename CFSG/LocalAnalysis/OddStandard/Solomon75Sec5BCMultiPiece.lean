module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5BCLift
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5OneTrans
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5BCMultiNorm
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5BCMultiSL23

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS
open scoped commutatorElement



section Helpers

variable {X : Type} [Group X] [Finite X] {n : ℕ} {A : Subgroup X}

private noncomputable def pieceProj (M : AhatModel X n A) : ↥A →* M.K :=
  M.e.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 ↥A))

private theorem pieceProj_apply (M : AhatModel X n A) (a : ↥A) :
    pieceProj M a = M.e (QuotientGroup.mk a) := rfl

private theorem pieceProj_eq_iff (M : AhatModel X n A) (a b : ↥A) :
    pieceProj M a = pieceProj M b ↔ (a : X)⁻¹ * (b : X) ∈ oddCoreOf A := by
  rw [pieceProj_apply, pieceProj_apply, M.e.injective.eq_iff, QuotientGroup.eq, mem_oddCoreOf_iff]
  exact ⟨fun hh => ⟨mul_mem (inv_mem a.2) b.2, hh⟩, fun ⟨_, hh⟩ => hh⟩

private theorem pieceProj_eq_one_iff (M : AhatModel X n A) (a : ↥A) :
    pieceProj M a = 1 ↔ (a : X) ∈ oddCoreOf A := by
  have := pieceProj_eq_iff M 1 a
  rw [map_one] at this
  rw [eq_comm]
  simpa using this

private theorem piece_eq_one_of_mem_odd_of_pow {G : Type*} [Group G] {O : Subgroup G}
    (hodd : Odd (Nat.card O)) {x : G} (hx : x ∈ O) {k : ℕ} (hk : x ^ (2 ^ k) = 1) : x = 1 := by
  have h1 : orderOf (⟨x, hx⟩ : O) ∣ Nat.card O := orderOf_dvd_natCard _
  have h2 : orderOf (⟨x, hx⟩ : O) ∣ 2 ^ k := by
    apply orderOf_dvd_of_pow_eq_one
    apply Subtype.ext
    simpa using hk
  have h3 : Nat.Coprime (2 ^ k) (Nat.card O) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hodd)
  have h4 : orderOf (⟨x, hx⟩ : O) = 1 := Nat.eq_one_of_dvd_coprimes h3 h2 h1
  exact congrArg (fun w : O => (w : G)) (orderOf_eq_one_iff.1 h4)

private theorem piece_exists_sq_eq_of_card_eight {K : Type*} [Group K] {Qb : Subgroup K} {c : K}
    (hc2 : c * c = 1) (hc1 : c ≠ 1) (hQ : Nat.card Qb = 8)
    (hpow : ∀ q ∈ Qb, q ≠ 1 → ∃ k : ℕ, q ^ k = c) : ∃ y ∈ Qb, y * y = c := by
  classical
  have hex : ∃ q ∈ Qb, q * q ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hsub : ∀ q ∈ Qb, q ≠ 1 → q = c := by
      intro q hq hq1
      obtain ⟨k, hk⟩ := hpow q hq hq1
      have hq2 : q ^ 2 = 1 := by rw [sq]; exact hcon q hq
      rw [pow_eq_pow_mod k hq2] at hk
      rcases Nat.mod_two_eq_zero_or_one k with h0 | h1
      · rw [h0, pow_zero] at hk
        exact absurd hk.symm hc1
      · rw [h1, pow_one] at hk
        exact hk
    have hle : Nat.card Qb ≤ 2 := by
      have hinj : Function.Injective (fun q : Qb => decide ((q : K) = 1)) := by
        intro q₁ q₂ h12
        simp only [decide_eq_decide] at h12
        by_cases h1 : (q₁ : K) = 1
        · exact Subtype.ext (h1.trans (h12.1 h1).symm)
        · have h2 : (q₂ : K) ≠ 1 := fun h => h1 (h12.2 h)
          exact Subtype.ext ((hsub q₁ q₁.2 h1).trans (hsub q₂ q₂.2 h2).symm)
      have := Nat.card_le_card_of_injective _ hinj
      simpa using this
    omega
  obtain ⟨q, hq, hq2⟩ := hex
  have hord : orderOf q ∣ 2 ^ 3 := by
    have h1 : orderOf (⟨q, hq⟩ : Qb) ∣ Nat.card Qb := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, hQ] at h1
    simpa using h1
  have hord2 : ¬ orderOf q ∣ 2 := by
    intro h2
    apply hq2
    rw [← sq]
    exact orderOf_dvd_iff_pow_eq_one.1 h2
  have h4 : ∃ y ∈ Qb, orderOf y = 4 := by
    obtain ⟨i, hi, hi'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hord
    interval_cases i
    · exact absurd (by rw [hi']; exact one_dvd 2) hord2
    · exact absurd (by rw [hi']; norm_num) hord2
    · exact ⟨q, hq, by rw [hi']; norm_num⟩
    · refine ⟨q ^ 2, pow_mem hq 2, ?_⟩
      rw [orderOf_pow_of_dvd (by norm_num) (by rw [hi']; norm_num), hi']
      norm_num
  obtain ⟨y, hy, hyo⟩ := h4
  have hy4 : y ^ 4 = 1 := by rw [← hyo]; exact pow_orderOf_eq_one y
  have hyy : (y ^ 2) ^ 2 = 1 := by rw [← pow_mul]; exact hy4
  have hyy1 : y ^ 2 ≠ 1 := by
    intro h
    have : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one h
    rw [hyo] at this
    omega
  obtain ⟨k, hk⟩ := hpow (y ^ 2) (pow_mem hy 2) hyy1
  refine ⟨y, hy, ?_⟩
  rw [pow_eq_pow_mod k hyy] at hk
  rcases Nat.mod_two_eq_zero_or_one k with h0 | h1
  · rw [h0, pow_zero] at hk
    exact absurd hk.symm hc1
  · rw [h1, pow_one] at hk
    rw [← sq]
    exact hk

private theorem piece_exists_odd_pow_eq {z : X} (M : AhatModel X n A) (hzA : z ∈ A)
    (hzc : ∀ g ∈ A, z * g = g * z) (hzz : z * z = 1) {g : X} (hg : g ∈ A) {k : ℕ}
    (hk : pieceProj M ⟨g, hg⟩ ^ k = pieceProj M ⟨z, hzA⟩) : ∃ r : ℕ, Odd r ∧ g ^ (k * r) = z := by
  have hgk : g ^ k ∈ A := pow_mem hg k
  have hgk' : pieceProj M ⟨g ^ k, hgk⟩ = pieceProj M ⟨z, hzA⟩ := by
    rw [← hk, ← map_pow]
    rfl
  have hoz : z⁻¹ * g ^ k ∈ oddCoreOf A :=
    (pieceProj_eq_iff M ⟨z, hzA⟩ ⟨g ^ k, hgk⟩).1 hgk'.symm
  set o : X := z⁻¹ * g ^ k with ho
  have hzg : Commute z g := hzc g hg
  have hzgk : z * g ^ k = g ^ k * z := (hzg.pow_right k).eq
  have hzo : z * o = o * z := by
    have h1 : z * o = g ^ k := by rw [ho]; group
    have h2 : o * z = g ^ k := by rw [ho, mul_assoc, ← hzgk]; group
    rw [h1, h2]
  have hoodd : Odd (orderOf o) := by
    have h1' : orderOf (⟨o, hoz⟩ : oddCoreOf A) ∣ Nat.card (oddCoreOf A) := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1'
    exact Odd.of_dvd_nat (odd_card_oddCoreOf A) h1'
  refine ⟨orderOf o, hoodd, ?_⟩
  have hgk_eq : g ^ k = z * o := by rw [ho]; group
  have hzc' : Commute z o := hzo
  calc g ^ (k * orderOf o) = (g ^ k) ^ orderOf o := pow_mul g k _
    _ = (z * o) ^ orderOf o := by rw [hgk_eq]
    _ = z ^ orderOf o * o ^ orderOf o := hzc'.mul_pow _
    _ = z := by
        rw [pow_orderOf_eq_one, mul_one]
        obtain ⟨m, hm⟩ := hoodd
        rw [hm, pow_succ, pow_mul, sq, hzz, one_pow, one_mul]

private theorem pieceProj_mem_fixSub (M : AhatModel X n A) {t : X}
    (htA : t ∈ normalizer (A : Set X)) {y : X} (hyA : y ∈ A)
    (hyt : y ∈ centralizer ({t} : Set X)) :
    pieceProj M ⟨y, hyA⟩ ∈ AhatData.fixSub (M.autOf t htA) := by
  have hty : t * y = y * t := (Subgroup.mem_centralizer_singleton_iff.1 hyt).symm
  have h1 : conjAut htA (⟨y, hyA⟩ : ↥A) = ⟨y, hyA⟩ :=
    Subtype.ext (by rw [coe_conjAut, hty, mul_inv_cancel_right])
  show M.autOf t htA (M.e (QuotientGroup.mk ⟨y, hyA⟩)) = M.e (QuotientGroup.mk ⟨y, hyA⟩)
  rw [M.autOf_mk, h1]

private theorem piece_sylow_bij {T K : Type*} [Group T] [Finite T] [Group K] [Finite K]
    (φ : T →* K) (hodd : Odd (Nat.card φ.ker)) (hrange : Nat.card φ.range = 8) :
    ∃ P : Subgroup T, Nat.card P = 8 ∧
      (∀ p₁ ∈ P, ∀ p₂ ∈ P, φ p₁ = φ p₂ → p₁ = p₂) ∧ ∀ k ∈ φ.range, ∃ p ∈ P, φ p = k := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card T = 8 * Nat.card φ.ker := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, hrange] at h1
    exact h1
  obtain ⟨P⟩ : Nonempty (Sylow 2 T) := inferInstance
  have hPcard : Nat.card (P : Subgroup T) = 8 := by
    have hk0 : Nat.card φ.ker ≠ 0 := Nat.card_pos.ne'
    have h2 : ¬ 2 ∣ Nat.card φ.ker := by
      have := Nat.odd_iff.1 hodd
      omega
    have hfac : (8 * Nat.card φ.ker).factorization 2 = 3 := by
      rw [Nat.factorization_mul (by norm_num) hk0, Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd h2, add_zero]
      have : (8 : ℕ) = 2 ^ 3 := by norm_num
      rw [this, Nat.Prime.factorization_pow Nat.prime_two]
      simp
    rw [Sylow.card_eq_multiplicity, hcard, hfac]
    norm_num
  have hinj : ∀ p₁ ∈ (P : Subgroup T), ∀ p₂ ∈ (P : Subgroup T), φ p₁ = φ p₂ → p₁ = p₂ := by
    intro p₁ hp₁ p₂ hp₂ h12
    have hp : p₁⁻¹ * p₂ ∈ (P : Subgroup T) := mul_mem (inv_mem hp₁) hp₂
    have hφ1 : φ (p₁⁻¹ * p₂) = 1 := by rw [map_mul, map_inv, h12, inv_mul_cancel]
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨p₁⁻¹ * p₂, hp⟩
    have hk' : (p₁⁻¹ * p₂ : T) ^ (2 ^ k) = 1 := by
      have := congrArg (fun w : ↥(P : Subgroup T) => (w : T)) hk
      simpa using this
    have hX : p₁⁻¹ * p₂ ∈ φ.ker := hφ1
    exact inv_mul_eq_one.1 (piece_eq_one_of_mem_odd_of_pow hodd hX hk')
  let ψ : ↥(P : Subgroup T) →* ↥φ.range :=
    (φ.comp (P : Subgroup T).subtype).codRestrict φ.range (fun p => ⟨p, rfl⟩)
  have hψinj : Function.Injective ψ := by
    intro p₁ p₂ h12
    have : φ (p₁ : T) = φ (p₂ : T) := congrArg Subtype.val h12
    exact Subtype.ext (hinj _ p₁.2 _ p₂.2 this)
  have hψbij : Function.Bijective ψ :=
    hψinj.bijective_of_nat_card_le (hrange.trans hPcard.symm).le
  refine ⟨P, hPcard, hinj, ?_⟩
  intro k hk
  obtain ⟨p, hp⟩ := hψbij.2 ⟨k, hk⟩
  exact ⟨p, p.2, congrArg Subtype.val hp⟩

end Helpers

section Lift

variable {X : Type} [Group X] [Finite X] {n : ℕ}

private theorem piece_le_LPlusIn {L : Subgroup X} (M : AhatModel X n L) {t : X}
    (ht2 : t * t = 1) (htL : t ∈ normalizer (L : Set X)) {P : Subgroup M.K}
    (hPfix : P ≤ AhatData.fixSub (M.autOf t htL))
    (hPnorm : ∀ g ∈ AhatData.fixSub (M.autOf t htL), ∀ p ∈ P, g * p * g⁻¹ ∈ P)
    (hPiso : Nonempty (↥P ≃* SL23))
    (hPodd : ∀ N : Subgroup M.K, N ≤ P → (∀ p ∈ P, ∀ x ∈ N, p * x * p⁻¹ ∈ N) →
      Odd (Nat.card ↥N) → N = ⊥)
    {x : X} (hxL : x ∈ L) (hxt : x ∈ centralizer ({t} : Set X))
    (hxP : pieceProj M ⟨x, hxL⟩ ∈ P) :
    x ∈ LPlusIn (L ⊓ centralizer ({t} : Set X)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite M.K := Finite.of_equiv _ M.e.toEquiv
  set Y : Subgroup X := L ⊓ centralizer ({t} : Set X)
  have hYL : Y ≤ L := inf_le_left
  let ρ : ↥Y →* M.K := (pieceProj M).comp (Subgroup.inclusion hYL)
  have hρ : ∀ y : ↥Y, ρ y = pieceProj M ⟨(y : X), hYL y.2⟩ := fun y => rfl
  have hρfix : ∀ y : ↥Y, ρ y ∈ AhatData.fixSub (M.autOf t htL) := fun y =>
    pieceProj_mem_fixSub M htL (hYL y.2) (Subgroup.mem_inf.1 y.2).2
  have hρsurj : ∀ k ∈ AhatData.fixSub (M.autOf t htL), ∃ y : ↥Y, ρ y = k := by
    intro k hk
    obtain ⟨v, hv, htv, hvk⟩ := M.exists_lift_cent htL ht2 (AhatData.mem_fixSub.1 hk)
    exact ⟨⟨v, Subgroup.mem_inf.2 ⟨hv, Subgroup.mem_centralizer_singleton_iff.2 htv.symm⟩⟩, hvk⟩
  set Pt : Subgroup ↥Y := P.comap ρ
  have hPtN : Pt.Normal := ⟨fun y hy g => by
    show ρ (g * y * g⁻¹) ∈ P
    rw [map_mul, map_mul, map_inv]
    exact hPnorm _ (hρfix g) _ (Subgroup.mem_comap.1 hy)⟩
  have hker_le : ρ.ker ≤ pPrimeCore 2 ↥Y := by
    intro y hy
    have h1 : pieceProj M ⟨(y : X), hYL y.2⟩ = 1 := hy
    have h2 : (y : X) ∈ oddCoreOf L := (pieceProj_eq_one_iff M _).1 h1
    have h3 : (y : X) ∈ oddCoreOf Y := inf_oddCoreOf_le_oddCoreOf hYL ⟨y.2, h2⟩
    obtain ⟨_, h5⟩ := mem_oddCoreOf_iff.1 h3
    exact h5
  have hPt_ker : Pt ⊓ pPrimeCore 2 ↥Y ≤ ρ.ker := by
    intro y hy
    set G₀ : Subgroup ↥Y := Pt ⊓ pPrimeCore 2 ↥Y
    set N : Subgroup M.K := G₀.map ρ
    have hNP : N ≤ P := by
      rintro _ ⟨g, hg, rfl⟩
      exact Subgroup.mem_comap.1 (Subgroup.mem_inf.1 hg).1
    have hNnorm : ∀ p ∈ P, ∀ x ∈ N, p * x * p⁻¹ ∈ N := by
      intro p hp x hx
      obtain ⟨g, hg, rfl⟩ := hx
      obtain ⟨w, rfl⟩ := hρsurj p (hPfix hp)
      refine ⟨w * g * w⁻¹, Subgroup.mem_inf.2 ⟨hPtN.conj_mem g (Subgroup.mem_inf.1 hg).1 w, ?_⟩,
        by simp only [map_mul, map_inv]⟩
      exact (inferInstance : (pPrimeCore 2 ↥Y).Normal).conj_mem g (Subgroup.mem_inf.1 hg).2 w
    have hNodd : Odd (Nat.card N) := by
      have h1 : Nat.card N ∣ Nat.card G₀ := Subgroup.card_map_dvd G₀ ρ
      have h2 : Nat.card G₀ ∣ Nat.card (pPrimeCore 2 ↥Y) := Subgroup.card_dvd_of_le inf_le_right
      have h3 : Nat.Coprime 2 (Nat.card (pPrimeCore 2 ↥Y)) := pPrimeCore_coprime_card
      exact Nat.coprime_two_left.1 (Nat.Coprime.coprime_dvd_right (h1.trans h2) h3)
    have hNbot : N = ⊥ := hPodd N hNP hNnorm hNodd
    have hmem : ρ y ∈ N := ⟨y, hy, rfl⟩
    rw [hNbot] at hmem
    exact Subgroup.mem_bot.1 hmem
  let π : ↥Y →* ↥Y ⧸ pPrimeCore 2 ↥Y := QuotientGroup.mk' (pPrimeCore 2 ↥Y)
  set Ph : Subgroup (↥Y ⧸ pPrimeCore 2 ↥Y) := Pt.map π
  have hPhN : Ph.Normal := Subgroup.Normal.map hPtN π (QuotientGroup.mk'_surjective _)
  obtain ⟨e1⟩ : Nonempty (↥Ph ≃* ↥P) := by
    let f1 : ↥Pt →* ↥Ph := (π.comp Pt.subtype).codRestrict Ph (fun y => ⟨y, y.2, rfl⟩)
    let f2 : ↥Pt →* ↥P := (ρ.comp Pt.subtype).codRestrict P (fun y => Subgroup.mem_comap.1 y.2)
    have hf1 : Function.Surjective f1 := by
      rintro ⟨_, y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
    have hf2 : Function.Surjective f2 := by
      intro p
      obtain ⟨y, hy⟩ := hρsurj p (hPfix p.2)
      refine ⟨⟨y, Subgroup.mem_comap.2 (by rw [hy]; exact p.2)⟩, Subtype.ext hy⟩
    have hker : f1.ker = f2.ker := by
      ext y
      constructor
      · intro hy
        have h1 : π (y : ↥Y) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hy)
        have h2 : (y : ↥Y) ∈ pPrimeCore 2 ↥Y := (QuotientGroup.eq_one_iff _).1 h1
        exact MonoidHom.mem_ker.2
          (Subtype.ext (MonoidHom.mem_ker.1 (hPt_ker (Subgroup.mem_inf.2 ⟨y.2, h2⟩))))
      · intro hy
        have h1 : ρ (y : ↥Y) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hy)
        have h2 : (y : ↥Y) ∈ pPrimeCore 2 ↥Y := hker_le (MonoidHom.mem_ker.2 h1)
        exact MonoidHom.mem_ker.2 (Subtype.ext ((QuotientGroup.eq_one_iff _).2 h2))
    exact ⟨(QuotientGroup.quotientKerEquivOfSurjective f1 hf1).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hker).trans
        (QuotientGroup.quotientKerEquivOfSurjective f2 hf2))⟩
  obtain ⟨e2⟩ := hPiso
  have hcomm : IsCommProd SL23 Ph := by
    refine ⟨{Ph}, ?_, ?_, ?_⟩
    · intro F hF
      rw [Finset.mem_singleton] at hF
      subst hF
      exact ⟨e1.trans e2⟩
    · simp
    · simp
  have hPhN1 : Ph ≤ NOne (↥Y ⧸ pPrimeCore 2 ↥Y) := le_NOne hPhN hcomm
  have hxY : x ∈ Y := Subgroup.mem_inf.2 ⟨hxL, hxt⟩
  have hxPt : (⟨x, hxY⟩ : ↥Y) ∈ Pt := Subgroup.mem_comap.2 hxP
  have hmem : π ⟨x, hxY⟩ ∈ EPlus (↥Y ⧸ pPrimeCore 2 ↥Y) :=
    Subgroup.mem_sup_left (Subgroup.mem_sup_right (hPhN1 ⟨_, hxPt, rfl⟩))
  exact Subgroup.mem_map.2 ⟨⟨x, hxY⟩, hmem, rfl⟩

private theorem piece_exists_quat {u t : X} (hu2 : u * u = 1) (hu1 : u ≠ 1)
    (ht2 : t * t = 1) {L E : Subgroup X} (hEL : E ≤ L) (huE : u ∈ E)
    (huc : ∀ g ∈ L, u * g = g * u) (hEcov : ∀ c ∈ L, ∃ a ∈ E, ∃ o ∈ oddCoreOf L, c = a * o)
    (htL : t ∈ normalizer (L : Set X)) (htE : t ∈ normalizer (E : Set X)) (M : AhatModel X n L)
    {Qb : Subgroup M.K} (hQbfix : Qb ≤ AhatData.fixSub (M.autOf t htL))
    (hQbcard : Nat.card Qb = 8)
    (hQbpow : ∀ q ∈ Qb, q ≠ 1 → ∃ k : ℕ, q ^ k ∈ center M.K ∧ q ^ k ≠ 1)
    (hQbcomm : ∃ a ∈ Qb, ∃ b ∈ Qb, ⁅a, b⁆ ∈ center M.K ∧ ⁅a, b⁆ ≠ 1) :
    ∃ Q : Subgroup X, Q ≤ E ⊓ centralizer ({t} : Set X) ∧ Nat.card Q = 8 ∧
      (∀ q ∈ Q, ∃ h : q ∈ L, pieceProj M ⟨q, h⟩ ∈ Qb) ∧
      (∀ x ∈ Qb, ∃ q ∈ Q, ∃ h : q ∈ L, pieceProj M ⟨q, h⟩ = x) ∧
      (∃ y ∈ Q, y * y = u) ∧ (∀ q ∈ Q, q ≠ 1 → u ∈ zpowers q) ∧
      ∃ a ∈ Q, ∃ b ∈ Q, ⁅a, b⁆ = u := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite M.K := Finite.of_equiv _ M.e.toEquiv
  have huL : u ∈ L := hEL huE
  obtain ⟨c, hc⟩ : ∃ c : M.K, pieceProj M ⟨u, huL⟩ = c := ⟨_, rfl⟩
  have hzK : c ∈ center M.K := by
    rw [← hc, Subgroup.mem_center_iff]
    intro k
    obtain ⟨b, hb⟩ := M.surj_mk k
    rw [← hb]
    show pieceProj M b * pieceProj M ⟨u, huL⟩ = pieceProj M ⟨u, huL⟩ * pieceProj M b
    rw [← map_mul, ← map_mul]
    exact congrArg (pieceProj M) (Subtype.ext (huc b b.2).symm)
  have hzK1 : c ≠ 1 := by
    intro h1
    rw [← hc] at h1
    exact hu1 (eq_one_of_sq_eq_one_of_mem_odd (odd_card_oddCoreOf L)
      ((pieceProj_eq_one_iff M ⟨u, huL⟩).1 h1) hu2)
  have hc2 : c * c = 1 := M.C.sq_of_mem_center hzK
  have hcr : ∀ r : ℕ, Odd r → c ^ r = c := by
    rintro r ⟨m, rfl⟩
    rw [pow_succ, pow_mul, sq, hc2, one_pow, one_mul]
  have hpow' : ∀ q ∈ Qb, q ≠ 1 → ∃ k : ℕ, q ^ k = c := by
    intro q hq hq1
    obtain ⟨k, hk, hk1⟩ := hQbpow q hq hq1
    exact ⟨k, M.C.center_eq_of_ne_one hk hzK hk1 hzK1⟩
  have hlift : ∀ x ∈ AhatData.fixSub (M.autOf t htL), ∃ e ∈ E, t * e = e * t ∧
      ∃ he : e ∈ L, pieceProj M ⟨e, he⟩ = x := by
    intro x hx
    have hx' : (M.transport hEL hEcov).autOf t htE x = x := by
      rw [M.autOf_transport hEL hEcov htE htL]
      exact AhatData.mem_fixSub.1 hx
    obtain ⟨e, he, hte, hex⟩ := (M.transport hEL hEcov).exists_lift_cent htE ht2 hx'
    exact ⟨e, he, hte, hEL he, (M.transport_e_mk hEL hEcov ⟨e, he⟩).symm.trans hex⟩
  obtain ⟨Qt, hQt⟩ : ∃ Qt : Subgroup X, Qt =
      ((Qb.comap (pieceProj M)).map L.subtype) ⊓ (E ⊓ centralizer ({t} : Set X)) := ⟨_, rfl⟩
  have mem_Qt : ∀ g : X, g ∈ Qt ↔ ∃ hg : g ∈ L, pieceProj M ⟨g, hg⟩ ∈ Qb ∧ g ∈ E ∧
      g ∈ centralizer ({t} : Set X) := by
    intro g
    rw [hQt]
    simp only [Subgroup.mem_inf, Subgroup.mem_map, Subgroup.mem_comap]
    constructor
    · rintro ⟨⟨a, ha, rfl⟩, hE', hs'⟩
      exact ⟨a.2, ha, hE', hs'⟩
    · rintro ⟨hg, hq, hE', hs'⟩
      exact ⟨⟨⟨g, hg⟩, hq, rfl⟩, hE', hs'⟩
  have hQtL : Qt ≤ L := by
    intro g hg
    obtain ⟨hgL, -⟩ := (mem_Qt g).1 hg
    exact hgL
  have hQtEC : Qt ≤ E ⊓ centralizer ({t} : Set X) := by
    intro g hg
    obtain ⟨-, -, hgE, hgt⟩ := (mem_Qt g).1 hg
    exact ⟨hgE, hgt⟩
  let φ : ↥Qt →* M.K := (pieceProj M).comp (Subgroup.inclusion hQtL)
  have hφQb : ∀ q : ↥Qt, φ q ∈ Qb := by
    intro q
    obtain ⟨hqL, hq, -, -⟩ := (mem_Qt q).1 q.2
    exact hq
  have hrange : φ.range = Qb := by
    ext x
    constructor
    · rintro ⟨q, rfl⟩
      exact hφQb q
    · intro hx
      obtain ⟨e, heE, hte, heL, hex⟩ := hlift x (hQbfix hx)
      have heQt : e ∈ Qt := (mem_Qt e).2 ⟨heL, by rw [hex]; exact hx, heE,
        Subgroup.mem_centralizer_singleton_iff.2 hte.symm⟩
      exact ⟨⟨e, heQt⟩, hex⟩
  have hkerOdd : Odd (Nat.card φ.ker) := by
    have hle : φ.ker.map Qt.subtype ≤ oddCoreOf L := by
      rintro _ ⟨q, hq, rfl⟩
      have h1 : pieceProj M ⟨(q : X), hQtL q.2⟩ = 1 := hq
      exact (pieceProj_eq_one_iff M _).1 h1
    have h1 : Nat.card (φ.ker.map Qt.subtype) = Nat.card φ.ker :=
      Subgroup.card_map_of_injective Qt.subtype_injective
    rw [← h1]
    exact Odd.of_dvd_nat (odd_card_oddCoreOf L) (Subgroup.card_dvd_of_le hle)
  obtain ⟨P, hPcard, hinj, hsurj⟩ :=
    piece_sylow_bij φ hkerOdd (by rw [hrange]; exact hQbcard)
  obtain ⟨Q, hQdef⟩ : ∃ Q : Subgroup X, Q = P.map Qt.subtype := ⟨_, rfl⟩
  have hmemQ : ∀ g : X, g ∈ Q ↔ ∃ p ∈ P, (p : X) = g := by
    intro g
    rw [hQdef]
    exact Subgroup.mem_map
  have hQQt : Q ≤ Qt := by
    rw [hQdef]
    exact Subgroup.map_subtype_le _
  have hcardQ : Nat.card Q = 8 := by
    rw [hQdef, Subgroup.card_map_of_injective Qt.subtype_injective]
    exact hPcard
  have hQmem : ∀ q ∈ Q, ∃ h : q ∈ L, pieceProj M ⟨q, h⟩ ∈ Qb := by
    intro q hq
    obtain ⟨hqL, hqb, -, -⟩ := (mem_Qt q).1 (hQQt hq)
    exact ⟨hqL, hqb⟩
  have hQlift : ∀ x ∈ Qb, ∃ q ∈ Q, ∃ h : q ∈ L, pieceProj M ⟨q, h⟩ = x := by
    intro x hx
    obtain ⟨p, hpP, hpx⟩ := hsurj x (by rw [hrange]; exact hx)
    exact ⟨(p : X), (hmemQ _).2 ⟨p, hpP, rfl⟩, hQtL p.2, hpx⟩
  have hQinj : ∀ q₁ ∈ Q, ∀ q₂ ∈ Q, ∀ (h₁ : q₁ ∈ L) (h₂ : q₂ ∈ L),
      pieceProj M ⟨q₁, h₁⟩ = pieceProj M ⟨q₂, h₂⟩ → q₁ = q₂ := by
    intro q₁ hq₁ q₂ hq₂ h₁ h₂ h12
    obtain ⟨p₁, hp₁, rfl⟩ := (hmemQ q₁).1 hq₁
    obtain ⟨p₂, hp₂, rfl⟩ := (hmemQ q₂).1 hq₂
    exact congrArg Subtype.val (hinj p₁ hp₁ p₂ hp₂ h12)
  obtain ⟨y₀, hy₀Q, hy₀sq⟩ := piece_exists_sq_eq_of_card_eight hc2 hzK1 hQbcard hpow'
  obtain ⟨q, hqQ, hqL, hqy⟩ := hQlift y₀ hy₀Q
  obtain ⟨r, hr, hqr⟩ := piece_exists_odd_pow_eq M huL huc hu2 hqL (k := 2)
    (by rw [hqy, sq, hy₀sq, hc])
  have hqq : q * q = u := by
    have h1 : q * q ∈ Q := mul_mem hqQ hqQ
    have h2 : q ^ (2 * r) ∈ Q := pow_mem hqQ _
    have h1L : q * q ∈ L := mul_mem hqL hqL
    have h2L : q ^ (2 * r) ∈ L := pow_mem hqL _
    have hpi1 : pieceProj M ⟨q * q, h1L⟩ = c := by
      have : (⟨q * q, h1L⟩ : ↥L) = ⟨q, hqL⟩ * ⟨q, hqL⟩ := rfl
      rw [this, map_mul, hqy, hy₀sq]
    have hpi2 : pieceProj M ⟨q ^ (2 * r), h2L⟩ = c := by
      have : (⟨q ^ (2 * r), h2L⟩ : ↥L) = (⟨q, hqL⟩ : ↥L) ^ (2 * r) := rfl
      rw [this, map_pow, hqy, pow_mul, sq, hy₀sq, hcr r hr]
    have h3 := hQinj _ h1 _ h2 h1L h2L (hpi1.trans hpi2.symm)
    rw [h3]
    exact hqr
  have huQ : u ∈ Q := by
    rw [← hqq]
    exact mul_mem hqQ hqQ
  have hQz : ∀ q ∈ Q, q ≠ 1 → u ∈ zpowers q := by
    intro q hq hq1
    obtain ⟨hqL, hqQb⟩ := hQmem q hq
    have hφ1 : pieceProj M ⟨q, hqL⟩ ≠ 1 := by
      intro h1
      apply hq1
      refine hQinj q hq 1 (one_mem Q) hqL (one_mem L) ?_
      rw [h1]
      exact (map_one (pieceProj M)).symm
    obtain ⟨k, hk⟩ := hpow' _ hqQb hφ1
    obtain ⟨r', -, hr'⟩ := piece_exists_odd_pow_eq M huL huc hu2 hqL (k := k)
      (by rw [hc]; exact hk)
    rw [← hr']
    exact pow_mem (Subgroup.mem_zpowers _) _
  obtain ⟨a, haQb, b, hbQb, hab_c, hab_ne⟩ := hQbcomm
  obtain ⟨a', ha'Q, ha'L, ha'⟩ := hQlift a haQb
  obtain ⟨b', hb'Q, hb'L, hb'⟩ := hQlift b hbQb
  have hcQ : ⁅a', b'⁆ ∈ Q := by
    simp only [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha'Q hb'Q) (inv_mem ha'Q)) (inv_mem hb'Q)
  have hcL : ⁅a', b'⁆ ∈ L := by
    simp only [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha'L hb'L) (inv_mem ha'L)) (inv_mem hb'L)
  have hpic : pieceProj M ⟨⁅a', b'⁆, hcL⟩ = ⁅a, b⁆ := by
    have : (⟨⁅a', b'⁆, hcL⟩ : ↥L) = ⁅(⟨a', ha'L⟩ : ↥L), (⟨b', hb'L⟩ : ↥L)⁆ := rfl
    rw [this, map_commutatorElement, ha', hb']
  have hab_eq : ⁅a, b⁆ = c := M.C.center_eq_of_ne_one hab_c hzK hab_ne hzK1
  refine ⟨Q, hQQt.trans hQtEC, hcardQ, hQmem, hQlift, ⟨q, hqQ, hqq⟩, hQz, a', ha'Q, b', hb'Q, ?_⟩
  exact hQinj _ hcQ u huQ hcL huL (by rw [hpic, hab_eq, hc])

end Lift


section Piece

variable {X : Type} [Group X] [Finite X] {n : ℕ}

theorem exists_sl23_piece (hn : 8 ≤ n) {u t : X} (hu2 : u * u = 1) (hu1 : u ≠ 1) (ht2 : t * t = 1)
    (htu : t * u = u * t) {L E : Subgroup X}
    (hL : IsPCompIn 2 (centralizer ({u} : Set X)) L) (hEL : E ≤ L) (huE : u ∈ E)
    (hEcov : ∀ c ∈ L, ∃ a ∈ E, ∃ o ∈ oddCoreOf L, c = a * o)
    (htL : t ∈ normalizer (L : Set X)) (htE : t ∈ normalizer (E : Set X)) (M : AhatModel X n L)
    (hbad : fixCount (M.perm t htL) = 4 ∨
      (transCount (M.perm t htL) = 3 ∧ fixCount (M.perm t htL) ≤ 3)) :
    ∃ Q : Subgroup X, Q ≤ E ⊓ centralizer ({t} : Set X) ∧ IsPGroup 2 ↥Q ∧ Nat.card ↥Q = 8 ∧
      u ∈ Q ∧ (∀ q ∈ Q, q ≠ 1 → u ∈ zpowers q) ∧ (∃ a ∈ Q, ∃ b ∈ Q, ⁅a, b⁆ = u) ∧
      (∃ y ∈ Q, y * y = u) ∧
      Q ≤ oTwoPrimeOf (LPlusIn (centralizer ({u} : Set X) ⊓ centralizer ({t} : Set X))) ∧
      Q ≤ oddTwoCoreOf (centralizer ({u} : Set X) ⊓ centralizer ({t} : Set X)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite M.K := Finite.of_equiv _ M.e.toEquiv
  have hα := M.induces_perm hn t htL
  have hσ2 := perm_sq_eq_one hn M htL ht2
  obtain ⟨P, Qb, hPfix, hPnorm, hPiso, hPodd, hQbP, hQbcard, hQbnorm, hQbpow, hQbcomm⟩ :=
    exists_sl23_model M.C hn hα hσ2 hbad
  have huc : ∀ g ∈ L, u * g = g * u := fun g hg =>
    (Subgroup.mem_centralizer_singleton_iff.1 (hL.1 hg)).symm
  obtain ⟨Q, hQEt, hQcard, hQmem, hQlift, hy, hQz, hcomm⟩ :=
    piece_exists_quat hu2 hu1 ht2 hEL huE huc hEcov htL htE M (hQbP.trans hPfix) hQbcard
      hQbpow hQbcomm
  set Y : Subgroup X := L ⊓ centralizer ({t} : Set X)
  set D : Subgroup X := centralizer ({u} : Set X) ⊓ centralizer ({t} : Set X)
  have hYL : Y ≤ L := inf_le_left
  have hYD : Y ≤ D := inf_le_inf_right _ hL.1
  have hDC : D ≤ centralizer ({u} : Set X) := inf_le_left
  have hYsub : (Y.subgroupOf D).IsSubnormal := by
    have h1 : (L.subgroupOf (centralizer ({u} : Set X))).IsSubnormal :=
      (isPComponent_two_iff.1 hL.2).1
    have h2 := h1.comap (Subgroup.inclusion hDC)
    rw [Subgroup.comap_inclusion_subgroupOf] at h2
    have h3 : Y.subgroupOf D = L.subgroupOf D := by
      ext x
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      exact ⟨fun h => (Subgroup.mem_inf.1 h).1,
        fun h => Subgroup.mem_inf.2 ⟨h, (Subgroup.mem_inf.1 x.2).2⟩⟩
    rw [h3]
    exact h2
  have hQY : Q ≤ Y := hQEt.trans (inf_le_inf_right _ hEL)
  have hQ2 : IsPGroup 2 ↥Q := IsPGroup.of_card (n := 3) (by rw [hQcard]; norm_num)
  have hQL : ∀ q ∈ Q, q ∈ LPlusIn Y := by
    intro q hq
    obtain ⟨hqL, hqQb⟩ := hQmem q hq
    exact piece_le_LPlusIn M ht2 htL hPfix hPnorm hPiso hPodd hqL
      (Subgroup.mem_inf.1 (hQEt hq)).2 (hQbP hqQb)
  refine ⟨Q, hQEt, hQ2, hQcard, ?_, hQz, hcomm, hy, ?_, ?_⟩
  · obtain ⟨y, hyQ, hyy⟩ := hy
    rw [← hyy]
    exact mul_mem hyQ hyQ
  · intro q hq
    obtain ⟨k, hk⟩ := hQ2 ⟨q, hq⟩
    exact mem_oTwoPrimeOf (LPlusIn_le_of_isSubnormal hYD hYsub (hQL q hq)) k
      (by simpa using congrArg Subtype.val hk)
  · refine le_oddTwoCoreOf_of_isSubnormal hYD hYsub hQ2 hQY ?_
    intro y hyY r hrQ
    have hyL : y ∈ L := (Subgroup.mem_inf.1 hyY).1
    have hyt : y ∈ centralizer ({t} : Set X) := (Subgroup.mem_inf.1 hyY).2
    obtain ⟨hrL, hrQb⟩ := hQmem r hrQ
    have hyrY : y * r * y⁻¹ ∈ Y := mul_mem (mul_mem hyY (hQY hrQ)) (inv_mem hyY)
    have hyrL : y * r * y⁻¹ ∈ L := (Subgroup.mem_inf.1 hyrY).1
    have hpi : pieceProj M ⟨y * r * y⁻¹, hyrL⟩ =
        pieceProj M ⟨y, hyL⟩ * pieceProj M ⟨r, hrL⟩ * (pieceProj M ⟨y, hyL⟩)⁻¹ := by
      have : (⟨y * r * y⁻¹, hyrL⟩ : ↥L) = ⟨y, hyL⟩ * ⟨r, hrL⟩ * ⟨y, hyL⟩⁻¹ := rfl
      rw [this, map_mul, map_mul, map_inv]
    have hQbn : pieceProj M ⟨y * r * y⁻¹, hyrL⟩ ∈ Qb := by
      rw [hpi]
      exact hQbnorm _ (pieceProj_mem_fixSub M htL hyL hyt) _ hrQb
    obtain ⟨r', hr'Q, hr'L, hr'⟩ := hQlift _ hQbn
    have ho1 : r'⁻¹ * (y * r * y⁻¹) ∈ Y := mul_mem (inv_mem (hQY hr'Q)) hyrY
    have ho3 : r'⁻¹ * (y * r * y⁻¹) ∈ oddCoreOf L :=
      (pieceProj_eq_iff M ⟨r', hr'L⟩ ⟨y * r * y⁻¹, hyrL⟩).1 hr'
    exact ⟨r', hr'Q, r'⁻¹ * (y * r * y⁻¹), inf_oddCoreOf_le_oddCoreOf hYL ⟨ho1, ho3⟩, by group⟩

end Piece

end CFSG.OddStandard.Solomon75
