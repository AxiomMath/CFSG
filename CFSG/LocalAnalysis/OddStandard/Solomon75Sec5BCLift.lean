module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5BCModel
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5QCor
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5QSide
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5FracSw
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5OneAlt
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5Frac

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS Equiv.Perm.OnCycleFactors
open scoped commutatorElement
open AhatData

structure QuatPiece {X : Type} [Group X] (z : X) (D : Subgroup X) where
  Qt : Subgroup X
  Q : Subgroup X
  y : X
  x : X
  a : X
  Qt_le : Qt ≤ D
  le_normalizer_Qt : D ≤ normalizer (Qt : Set X)
  not_dvd_card_Qt : ¬ 16 ∣ Nat.card Qt
  Q_le : Q ≤ Qt
  card_Q : Nat.card Q = 8
  mem_zpowers_of_Q : ∀ q ∈ Q, q ≠ 1 → z ∈ zpowers q
  y_mem : y ∈ Q
  y_sq : y * y = z
  x_mem : x ∈ D
  a_mem : a ∈ D
  a_sq : a * a = z
  x_comm_a : x * a = a * x
  x_three : IsPGroup 3 ↥(zpowers x)
  x_nontriv : ∃ q ∈ Qt, z ∈ zpowers ⁅x, q⁆

theorem perm_sq_eq_one {X : Type} [Group X] {n : ℕ} {A : Subgroup X} (hn : 8 ≤ n)
    (M : AhatModel X n A) {c : X} (hc : c ∈ normalizer (A : Set X)) (h : c * c = 1) :
    M.perm c hc * M.perm c hc = 1 := by
  have h1 : (⟨c, hc⟩ : ↥(normalizer (A : Set X))) * ⟨c, hc⟩ = 1 := Subtype.ext h
  have h2 := congrArg (M.permHom hn) h1
  rw [map_mul, map_one] at h2
  exact h2

section Helpers

private theorem exists_sq_eq_of_card_eight {K : Type*} [Group K] {Qb : Subgroup K} {c : K}
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

private theorem wb_powers {K : Type*} [Group K] {xb ab : K} (hxa : xb * ab = ab * xb)
    (hx3 : xb ^ 3 = 1) (hab4 : ab ^ 4 = 1) :
    (xb * ab) ^ 4 = xb ∧ (xb * ab) ^ 18 = ab * ab := by
  have hc : Commute xb ab := hxa
  constructor
  · rw [hc.mul_pow, hab4, mul_one]
    have : xb ^ 4 = xb ^ 3 * xb := by group
    rw [this, hx3, one_mul]
  · rw [hc.mul_pow]
    have e1 : xb ^ 18 = (xb ^ 3) ^ 6 := by group
    have e2 : ab ^ 18 = (ab ^ 4) ^ 4 * (ab * ab) := by group
    rw [e1, e2, hx3, hab4, one_pow, one_pow, one_mul, one_mul]

private theorem exists_pow_three_part {G H : Type*} [Group G] [Group H] [Finite G] (f : G →* H)
    {v : G} {xb : H} (hv : f v = xb) (hx3 : xb ^ 3 = 1) (hx1 : xb ≠ 1) :
    ∃ k j : ℕ, orderOf (v ^ k) = 3 ^ j ∧ f (v ^ k) = xb := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hx3o : orderOf xb = 3 := orderOf_eq_prime hx3 hx1
  have hpos : 0 < orderOf v := orderOf_pos v
  have hdvd : 3 ∣ orderOf v := by
    rw [← hx3o]
    apply orderOf_dvd_of_pow_eq_one
    rw [← hv, ← map_pow, pow_orderOf_eq_one, map_one]
  obtain ⟨j, t, h3t, het⟩ := Nat.exists_eq_pow_mul_and_not_dvd hpos.ne' 3 (by norm_num)
  have hj : j ≠ 0 := by
    rintro rfl
    rw [pow_zero, one_mul] at het
    rw [het] at hdvd
    exact h3t hdvd
  have hcop : Nat.Coprime (3 ^ j) t :=
    Nat.Coprime.pow_left j ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3t)
  obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder hcop 1 0
  obtain ⟨k', hk'⟩ := Nat.modEq_zero_iff_dvd.1 hk2
  have hpow : (v ^ k) ^ (3 ^ j) = 1 := by
    rw [← pow_mul, hk', show t * k' * 3 ^ j = orderOf v * k' by rw [het]; ring, pow_mul,
      pow_orderOf_eq_one, one_pow]
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one hpow)
  refine ⟨k, i, hi, ?_⟩
  have hk3 : k % 3 = 1 := by
    have := Nat.ModEq.of_dvd (dvd_pow_self 3 hj) hk1
    simpa [Nat.ModEq] using this
  rw [map_pow, hv, pow_eq_pow_mod k hx3, hk3, pow_one]

end Helpers

section QuatLift

variable {X : Type} [Group X] [Finite X] {n : ℕ} {A : Subgroup X}

private noncomputable def piA (M : AhatModel X n A) : ↥A →* M.K :=
  M.e.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 ↥A))

private theorem piA_apply (M : AhatModel X n A) (a : ↥A) :
    piA M a = M.e (QuotientGroup.mk a) := rfl

private theorem piA_eq_iff (M : AhatModel X n A) (a b : ↥A) :
    piA M a = piA M b ↔ (a : X)⁻¹ * (b : X) ∈ oddCoreOf A := by
  rw [piA_apply, piA_apply, M.e.injective.eq_iff, QuotientGroup.eq, mem_oddCoreOf_iff]
  exact ⟨fun hh => ⟨mul_mem (inv_mem a.2) b.2, hh⟩, fun ⟨_, hh⟩ => hh⟩

private theorem piA_eq_one_iff (M : AhatModel X n A) (a : ↥A) :
    piA M a = 1 ↔ (a : X) ∈ oddCoreOf A := by
  have := piA_eq_iff M 1 a
  rw [map_one] at this
  rw [eq_comm]
  simpa using this

private theorem eq_one_of_mem_odd_of_pow {O : Subgroup X} (hodd : Odd (Nat.card O)) {x : X}
    (hx : x ∈ O) {k : ℕ} (hk : x ^ (2 ^ k) = 1) : x = 1 := by
  have h1 : orderOf (⟨x, hx⟩ : O) ∣ Nat.card O := orderOf_dvd_natCard _
  have h2 : orderOf (⟨x, hx⟩ : O) ∣ 2 ^ k := by
    apply orderOf_dvd_of_pow_eq_one
    apply Subtype.ext
    simpa using hk
  have h3 : Nat.Coprime (2 ^ k) (Nat.card O) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hodd)
  have h4 : orderOf (⟨x, hx⟩ : O) = 1 := Nat.eq_one_of_dvd_coprimes h3 h2 h1
  exact congrArg (fun w : O => (w : X)) (orderOf_eq_one_iff.1 h4)

private theorem exists_odd_pow_eq {z : X} (M : AhatModel X n A) (hzA : z ∈ A)
    (hzc : ∀ g ∈ A, z * g = g * z) (hzz : z * z = 1) {g : X} (hg : g ∈ A) {k : ℕ}
    (hk : piA M ⟨g, hg⟩ ^ k = piA M ⟨z, hzA⟩) : ∃ r : ℕ, Odd r ∧ g ^ (k * r) = z := by
  have hgk : g ^ k ∈ A := pow_mem hg k
  have hgk' : piA M ⟨g ^ k, hgk⟩ = piA M ⟨z, hzA⟩ := by
    rw [← hk, ← map_pow]
    rfl
  have hoz : z⁻¹ * g ^ k ∈ oddCoreOf A := (piA_eq_iff M ⟨z, hzA⟩ ⟨g ^ k, hgk⟩).1 hgk'.symm
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

private theorem exists_quatPiece_of_model (M : AhatModel X n A) (hn : 8 ≤ n) {s z : X}
    (hsA : s ∈ normalizer (A : Set X)) (hss : s * s = 1) (hzA : z ∈ A)
    (hzc : ∀ g ∈ A, z * g = g * z) (hzz : z * z = 1) (hz1 : z ≠ 1)
    (hNA : centralizer ({z} : Set X) ≤ normalizer (A : Set X))
    (hfix : fixCount (M.perm s hsA) = 4) :
    Nonempty (QuatPiece z (centralizer ({z} : Set X) ⊓ centralizer ({s} : Set X))) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite M.K := Finite.of_equiv _ M.e.toEquiv
  have hα := M.induces_perm hn s hsA
  have hσ2 := perm_sq_eq_one hn M hsA hss
  obtain ⟨Qb, xb, ab, hQbfix, hQbcard, hQbpow, hxbfix, habfix, habc, habne, hxbab, hxb3, hxbQ,
    hxbnt, hinv⟩ := exists_quat_model M.C hn hα hσ2 hfix
  have hc2 : (ab * ab) * (ab * ab) = 1 := M.C.sq_of_mem_center habc
  have hab4 : ab ^ 4 = 1 := by
    have : ab ^ 4 = (ab * ab) * (ab * ab) := by
      rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq]
    rw [this]
    exact hc2
  have hcr : ∀ r : ℕ, Odd r → (ab * ab) ^ r = ab * ab := by
    rintro r ⟨m, rfl⟩
    rw [pow_succ, pow_mul, sq, hc2, one_pow, one_mul]
  have hzK : piA M ⟨z, hzA⟩ ∈ center M.K := by
    rw [Subgroup.mem_center_iff]
    intro k
    obtain ⟨b, hb⟩ := M.surj_mk k
    rw [← hb]
    show piA M b * piA M ⟨z, hzA⟩ = piA M ⟨z, hzA⟩ * piA M b
    rw [← map_mul, ← map_mul]
    exact congrArg (piA M) (Subtype.ext (hzc b b.2).symm)
  have hzK1 : piA M ⟨z, hzA⟩ ≠ 1 := by
    intro h1
    exact hz1 (eq_one_of_sq_eq_one_of_mem_odd (odd_card_oddCoreOf A)
      ((piA_eq_one_iff M ⟨z, hzA⟩).1 h1) hzz)
  have hpz : piA M ⟨z, hzA⟩ = ab * ab := M.C.center_eq_of_ne_one hzK habc hzK1 habne
  have hpow' : ∀ q ∈ Qb, q ≠ 1 → ∃ k : ℕ, q ^ k = ab * ab := by
    intro q hq hq1
    obtain ⟨k, hk, hk1⟩ := hQbpow q hq hq1
    exact ⟨k, M.C.center_eq_of_ne_one hk habc hk1 habne⟩
  have hAC : A ≤ centralizer ({z} : Set X) := fun g hg =>
    Subgroup.mem_centralizer_singleton_iff.2 (hzc g hg).symm
  obtain ⟨Qt, hQt⟩ : ∃ Qt : Subgroup X,
      Qt = ((Qb.comap (piA M)).map A.subtype) ⊓ centralizer ({s} : Set X) := ⟨_, rfl⟩
  have mem_Qt : ∀ g : X, g ∈ Qt ↔
      ∃ hg : g ∈ A, piA M ⟨g, hg⟩ ∈ Qb ∧ g ∈ centralizer ({s} : Set X) := by
    intro g
    rw [hQt]
    simp only [Subgroup.mem_inf, Subgroup.mem_map, Subgroup.mem_comap]
    constructor
    · rintro ⟨⟨a, ha, rfl⟩, hs'⟩
      exact ⟨a.2, ha, hs'⟩
    · rintro ⟨hg, hq, hs'⟩
      exact ⟨⟨⟨g, hg⟩, hq, rfl⟩, hs'⟩
  have hQtA : Qt ≤ A := by
    intro g hg
    obtain ⟨hgA, -⟩ := (mem_Qt g).1 hg
    exact hgA
  have hQtD : Qt ≤ centralizer ({z} : Set X) ⊓ centralizer ({s} : Set X) := by
    intro g hg
    obtain ⟨hgA, -, hgs⟩ := (mem_Qt g).1 hg
    exact ⟨hAC hgA, hgs⟩
  let φ : ↥Qt →* M.K := (piA M).comp (Subgroup.inclusion hQtA)
  have hφ : ∀ q : ↥Qt, φ q = piA M ⟨(q : X), hQtA q.2⟩ := fun q => rfl
  have hφQb : ∀ q : ↥Qt, φ q ∈ Qb := by
    intro q
    obtain ⟨_, hq, _⟩ := (mem_Qt q).1 q.2
    exact hq
  have hrange : φ.range = Qb := by
    ext x
    constructor
    · rintro ⟨q, rfl⟩
      exact hφQb q
    · intro hx
      obtain ⟨u, hu, hsu, hux⟩ := M.exists_lift_cent hsA hss (mem_fixSub.1 (hQbfix hx))
      have hpu : piA M ⟨u, hu⟩ = x := hux
      have huQt : u ∈ Qt := (mem_Qt u).2 ⟨hu, by rw [hpu]; exact hx,
        Subgroup.mem_centralizer_singleton_iff.2 hsu.symm⟩
      exact ⟨⟨u, huQt⟩, hpu⟩
  have hkerOdd : Odd (Nat.card φ.ker) := by
    have hle : φ.ker.map Qt.subtype ≤ oddCoreOf A := by
      rintro _ ⟨q, hq, rfl⟩
      have h1 : piA M ⟨(q : X), hQtA q.2⟩ = 1 := hq
      exact (piA_eq_one_iff M _).1 h1
    have h1 : Nat.card (φ.ker.map Qt.subtype) = Nat.card φ.ker :=
      Subgroup.card_map_of_injective Qt.subtype_injective
    rw [← h1]
    exact Odd.of_dvd_nat (odd_card_oddCoreOf A) (Subgroup.card_dvd_of_le hle)
  have hcardQt : Nat.card Qt = 8 * Nat.card φ.ker := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv] at h1
    have h2 : Nat.card φ.range = 8 := by rw [hrange]; exact hQbcard
    rw [h2] at h1
    exact h1
  have h16 : ¬ 16 ∣ Nat.card Qt := by
    rw [hcardQt]
    intro h
    have := Nat.odd_iff.1 hkerOdd
    omega
  obtain ⟨P⟩ : Nonempty (Sylow 2 ↥Qt) := inferInstance
  have hPcard : Nat.card (P : Subgroup ↥Qt) = 8 := by
    have hk0 : Nat.card φ.ker ≠ 0 := Nat.card_pos.ne'
    have h2 : ¬ 2 ∣ Nat.card φ.ker := by
      have := Nat.odd_iff.1 hkerOdd
      omega
    have hfac : (8 * Nat.card φ.ker).factorization 2 = 3 := by
      rw [Nat.factorization_mul (by norm_num) hk0, Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd h2, add_zero]
      have : (8 : ℕ) = 2 ^ 3 := by norm_num
      rw [this, Nat.Prime.factorization_pow Nat.prime_two]
      simp
    rw [Sylow.card_eq_multiplicity, hcardQt, hfac]
    norm_num
  obtain ⟨Q, hQdef⟩ : ∃ Q : Subgroup X, Q = (P : Subgroup ↥Qt).map Qt.subtype := ⟨_, rfl⟩
  have hmemQ : ∀ g : X, g ∈ Q ↔ ∃ p ∈ (P : Subgroup ↥Qt), (p : X) = g := by
    intro g
    rw [hQdef]
    exact Subgroup.mem_map
  have hQQt : Q ≤ Qt := by
    rw [hQdef]
    exact Subgroup.map_subtype_le _
  have hcardQ : Nat.card Q = 8 := by
    rw [hQdef, Subgroup.card_map_of_injective Qt.subtype_injective]
    exact hPcard
  have hinj : ∀ p₁ ∈ (P : Subgroup ↥Qt), ∀ p₂ ∈ (P : Subgroup ↥Qt), φ p₁ = φ p₂ → p₁ = p₂ := by
    intro p₁ hp₁ p₂ hp₂ h12
    have hp : p₁⁻¹ * p₂ ∈ (P : Subgroup ↥Qt) := mul_mem (inv_mem hp₁) hp₂
    have hφ1 : φ (p₁⁻¹ * p₂) = 1 := by rw [map_mul, map_inv, h12, inv_mul_cancel]
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨p₁⁻¹ * p₂, hp⟩
    have hk' : (p₁⁻¹ * p₂ : ↥Qt) ^ (2 ^ k) = 1 := by
      have := congrArg (fun w : ↥(P : Subgroup ↥Qt) => (w : ↥Qt)) hk
      simpa using this
    have hφ1' : piA M ⟨((p₁⁻¹ * p₂ : ↥Qt) : X), hQtA (p₁⁻¹ * p₂).2⟩ = 1 := hφ1
    have hX : ((p₁⁻¹ * p₂ : ↥Qt) : X) ∈ oddCoreOf A := (piA_eq_one_iff M _).1 hφ1'
    have hX1 : ((p₁⁻¹ * p₂ : ↥Qt) : X) = 1 :=
      eq_one_of_mem_odd_of_pow (odd_card_oddCoreOf A) hX (k := k)
        (by have := congrArg (fun w : ↥Qt => (w : X)) hk'; simpa using this)
    exact inv_mul_eq_one.1 (Subtype.ext hX1)
  let ψ : ↥(P : Subgroup ↥Qt) →* ↥Qb :=
    (φ.comp (P : Subgroup ↥Qt).subtype).codRestrict Qb (fun p => hφQb p)
  have hψinj : Function.Injective ψ := by
    intro p₁ p₂ h12
    have : φ (p₁ : ↥Qt) = φ (p₂ : ↥Qt) := congrArg Subtype.val h12
    exact Subtype.ext (hinj _ p₁.2 _ p₂.2 this)
  have hψbij : Function.Bijective ψ :=
    hψinj.bijective_of_nat_card_le (hQbcard.trans hPcard.symm).le
  have hsurj : ∀ y₀ ∈ Qb, ∃ p ∈ (P : Subgroup ↥Qt), φ p = y₀ := by
    intro y₀ hy₀
    obtain ⟨p, hp⟩ := hψbij.2 ⟨y₀, hy₀⟩
    exact ⟨p, p.2, congrArg Subtype.val hp⟩
  obtain ⟨y₀, hy₀Q, hy₀sq⟩ := exists_sq_eq_of_card_eight hc2 habne hQbcard hpow'
  obtain ⟨p, hpP, hpφ⟩ := hsurj y₀ hy₀Q
  have hyA : (p : X) ∈ A := hQtA p.2
  have hyQ : (p : X) ∈ Q := (hmemQ _).2 ⟨p, hpP, rfl⟩
  have hpiy : piA M ⟨(p : X), hyA⟩ = y₀ := hpφ
  obtain ⟨r, hr, hyr⟩ := exists_odd_pow_eq M hzA hzc hzz hyA (k := 2)
    (by rw [hpiy, hpz, sq, hy₀sq])
  have hyy : (p : X) * (p : X) = z := by
    have hp2 : (p * p : ↥Qt) ∈ (P : Subgroup ↥Qt) := mul_mem hpP hpP
    have hp2r : (p ^ (2 * r) : ↥Qt) ∈ (P : Subgroup ↥Qt) := pow_mem hpP _
    have h1 : φ (p * p) = φ (p ^ (2 * r)) := by
      rw [map_mul, map_pow, hpφ, hy₀sq, pow_mul, sq, hy₀sq, hcr r hr]
    have h2 := hinj _ hp2 _ hp2r h1
    have h3 : (((p * p : ↥Qt)) : X) = (((p ^ (2 * r) : ↥Qt)) : X) := congrArg Subtype.val h2
    have e1 : (((p * p : ↥Qt)) : X) = (p : X) * (p : X) := rfl
    have e2 : (((p ^ (2 * r) : ↥Qt)) : X) = (p : X) ^ (2 * r) := rfl
    rw [e1, e2] at h3
    rw [h3]
    exact hyr
  have hQz : ∀ q ∈ Q, q ≠ 1 → z ∈ zpowers q := by
    intro q hq hq1
    obtain ⟨p', hp', rfl⟩ := (hmemQ q).1 hq
    have hqA : (p' : X) ∈ A := hQtA p'.2
    have hφ1 : φ p' ≠ 1 := by
      intro h1
      apply hq1
      have : p' = 1 := hinj p' hp' 1 (Subgroup.one_mem _) (by rw [h1, map_one])
      rw [this]
      rfl
    obtain ⟨k, hk⟩ := hpow' (φ p') (hφQb p') hφ1
    obtain ⟨r', -, hr'⟩ := exists_odd_pow_eq M hzA hzc hzz hqA (k := k) (by rw [hpz]; exact hk)
    rw [← hr']
    exact pow_mem (Subgroup.mem_zpowers _) _
  have hxb1 : xb ≠ 1 := by
    obtain ⟨q0, -, hq0ne⟩ := hxbnt
    rintro rfl
    simp at hq0ne
  obtain ⟨hw4, hw18⟩ := wb_powers hxbab hxb3 hab4
  have hwbfix : xb * ab ∈ fixSub (M.autOf s hsA) := mul_mem hxbfix habfix
  obtain ⟨u, hu, hsu, hux⟩ := M.exists_lift_cent hsA hss (mem_fixSub.1 hwbfix)
  have hpiu : piA M ⟨u, hu⟩ = xb * ab := hux
  obtain ⟨r', hr', hur⟩ := exists_odd_pow_eq M hzA hzc hzz hu (k := 18)
    (by rw [hpiu, hpz]; exact hw18)
  have haa : u ^ (9 * r') * u ^ (9 * r') = z := by
    rw [← pow_add, show 9 * r' + 9 * r' = 18 * r' by ring]
    exact hur
  have hu4 : u ^ 4 ∈ A := pow_mem hu 4
  have hpiu4 : piA M ⟨u ^ 4, hu4⟩ = xb := by
    have : (⟨u ^ 4, hu4⟩ : ↥A) = (⟨u, hu⟩ : ↥A) ^ 4 := rfl
    rw [this, map_pow, hpiu]
    exact hw4
  obtain ⟨k, j, hok, hpk⟩ :=
    exists_pow_three_part (piA M) (v := (⟨u ^ 4, hu4⟩ : ↥A)) hpiu4 hxb3 hxb1
  have hxA : (u ^ 4) ^ k ∈ A := pow_mem hu4 k
  have hpix : piA M ⟨(u ^ 4) ^ k, hxA⟩ = xb := by
    have : (⟨(u ^ 4) ^ k, hxA⟩ : ↥A) = (⟨u ^ 4, hu4⟩ : ↥A) ^ k := rfl
    rw [this]
    exact hpk
  have hxo : orderOf ((u ^ 4) ^ k) = 3 ^ j :=
    (Subgroup.orderOf_coe ((⟨u ^ 4, hu4⟩ : ↥A) ^ k)).trans hok
  have hx3 : IsPGroup 3 ↥(zpowers ((u ^ 4) ^ k)) :=
    IsPGroup.of_card ((Nat.card_zpowers _).trans hxo)
  have hxa : (u ^ 4) ^ k * u ^ (9 * r') = u ^ (9 * r') * (u ^ 4) ^ k := by
    rw [← pow_mul]
    exact (Commute.pow_pow_self u (4 * k) (9 * r')).eq
  have hsu' : Commute s u := hsu
  have hxs : (u ^ 4) ^ k ∈ centralizer ({s} : Set X) :=
    Subgroup.mem_centralizer_singleton_iff.2 (((hsu'.pow_right 4).pow_right k).symm.eq)
  have haA : u ^ (9 * r') ∈ A := pow_mem hu _
  have has : u ^ (9 * r') ∈ centralizer ({s} : Set X) :=
    Subgroup.mem_centralizer_singleton_iff.2 ((hsu'.pow_right (9 * r')).symm.eq)
  have hxnt : ∃ q ∈ Qt, z ∈ zpowers ⁅(u ^ 4) ^ k, q⁆ := by
    obtain ⟨q0, hq0, hq0ne⟩ := hxbnt
    have hq0r : q0 ∈ φ.range := hrange ▸ hq0
    obtain ⟨qt, hqt⟩ := hq0r
    have hqQt : (qt : X) ∈ Qt := qt.2
    have hqA : (qt : X) ∈ A := hQtA hqQt
    have hg : ⁅(u ^ 4) ^ k, (qt : X)⁆ ∈ A := by
      simp only [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hxA hqA) (inv_mem hxA)) (inv_mem hqA)
    have hpiq : piA M ⟨(qt : X), hqA⟩ = q0 := hqt
    have hpig : piA M ⟨⁅(u ^ 4) ^ k, (qt : X)⁆, hg⟩ = xb * q0 * xb⁻¹ * q0⁻¹ := by
      have : (⟨⁅(u ^ 4) ^ k, (qt : X)⁆, hg⟩ : ↥A) =
          ⟨(u ^ 4) ^ k, hxA⟩ * ⟨(qt : X), hqA⟩ * ⟨(u ^ 4) ^ k, hxA⟩⁻¹ * ⟨(qt : X), hqA⟩⁻¹ := by
        apply Subtype.ext
        simp [commutatorElement_def]
      rw [this, map_mul, map_mul, map_mul, map_inv, map_inv, hpix, hpiq]
    have hgQb : xb * q0 * xb⁻¹ * q0⁻¹ ∈ Qb := mul_mem (hxbQ q0 hq0) (inv_mem hq0)
    have hgne : xb * q0 * xb⁻¹ * q0⁻¹ ≠ 1 := fun h => hq0ne (mul_inv_eq_one.1 h)
    obtain ⟨k', hk'⟩ := hpow' _ hgQb hgne
    obtain ⟨r'', -, hr''⟩ := exists_odd_pow_eq M hzA hzc hzz hg (k := k')
      (by rw [hpig, hpz]; exact hk')
    refine ⟨(qt : X), hqQt, ?_⟩
    rw [← hr'']
    exact pow_mem (Subgroup.mem_zpowers _) _
  have hnorm : ∀ d ∈ centralizer ({z} : Set X) ⊓ centralizer ({s} : Set X), ∀ g ∈ Qt,
      d * g * d⁻¹ ∈ Qt := by
    intro d hd g hg
    obtain ⟨hdz, hds⟩ := hd
    have hdA : d ∈ normalizer (A : Set X) := hNA hdz
    obtain ⟨hgA, hgQb, hgs⟩ := (mem_Qt g).1 hg
    have hdgA : d * g * d⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.1 hdA g).1 hgA
    refine (mem_Qt _).2 ⟨hdgA, ?_, mul_mem (mul_mem hds hgs) (inv_mem hds)⟩
    have e1 : piA M ⟨d * g * d⁻¹, hdgA⟩ = M.autOf d hdA (piA M ⟨g, hgA⟩) := by
      rw [piA_apply, piA_apply, M.autOf_mk]
      congr 2
    rw [e1]
    have hds' : d * s = s * d := Subgroup.mem_centralizer_singleton_iff.1 hds
    have hν : M.perm d hdA * M.perm s hsA = M.perm s hsA * M.perm d hdA := by
      have h1 : M.permX d * M.permX s = M.permX s * M.permX d := by
        rw [← M.permX_mul hn hdA hsA, ← M.permX_mul hn hsA hdA, hds']
      simpa only [M.permX_of_mem hdA, M.permX_of_mem hsA] using h1
    have hmap := hinv (M.autOf d hdA) (M.perm d hdA) (M.induces_perm hn d hdA) hν
    have hmem : M.autOf d hdA (piA M ⟨g, hgA⟩) ∈ Qb.map (M.autOf d hdA).toMonoidHom :=
      Subgroup.mem_map.2 ⟨_, hgQb, rfl⟩
    rwa [hmap] at hmem
  have hD : centralizer ({z} : Set X) ⊓ centralizer ({s} : Set X) ≤ normalizer (Qt : Set X) := by
    intro d hd
    rw [Subgroup.mem_normalizer_iff]
    intro g
    refine ⟨fun hg => hnorm d hd g hg, fun hg => ?_⟩
    have := hnorm d⁻¹ (inv_mem hd) _ hg
    simpa [mul_assoc] using this
  exact ⟨{
    Qt := Qt
    Q := Q
    y := (p : X)
    x := (u ^ 4) ^ k
    a := u ^ (9 * r')
    Qt_le := hQtD
    le_normalizer_Qt := hD
    not_dvd_card_Qt := h16
    Q_le := hQQt
    card_Q := hcardQ
    mem_zpowers_of_Q := hQz
    y_mem := hyQ
    y_sq := hyy
    x_mem := ⟨hAC hxA, hxs⟩
    a_mem := ⟨hAC haA, has⟩
    a_sq := haa
    x_comm_a := hxa
    x_three := hx3
    x_nontriv := hxnt }⟩

end QuatLift

section Pieces

variable {X : Type} [Group X] [Finite X] {n : ℕ} {z : X} {Z : Subgroup X}
  {S : Sylow 2 ↥(normalizer (Z : Set X))}

private theorem sec5Comp_map {H A : Subgroup X} (hA : Sec5Comp X n H A) (φ : X ≃* X) :
    Sec5Comp X n (H.map φ.toMonoidHom) (A.map φ.toMonoidHom) := by
  obtain ⟨⟨u, hu⟩, hcov⟩ := hA
  refine ⟨⟨_, hu.map_mulEquiv φ⟩, ?_⟩
  let ψ : ↥A ≃* ↥(A.map φ.toMonoidHom) := Subgroup.equivMapOfInjective A _ φ.injective
  exact isDoubleCoverOfAlt_congr' (QuotientGroup.congr _ _ ψ (pPrimeCore_map_iso 2 ψ)) hcov

private theorem map_symm_map_mulEquiv (φ : X ≃* X) (H : Subgroup X) :
    (H.map φ.toMonoidHom).map φ.symm.toMonoidHom = H := by
  rw [Subgroup.map_map]
  have : φ.symm.toMonoidHom.comp φ.toMonoidHom = MonoidHom.id X := by
    ext x
    simp
  rw [this, Subgroup.map_id]

theorem sec5One_map_conj (h1 : Sec5One X n Z) (g : X) :
    Sec5One X n (Z.map (MulAut.conj g).toMonoidHom) := by
  intro A A' hA hA'
  have hN : normalizer ((Z.map (MulAut.conj g).toMonoidHom : Subgroup X) : Set X) =
      (normalizer (Z : Set X)).map (MulAut.conj g).toMonoidHom := normalizer_map_mulEquiv _ _
  rw [hN] at hA hA'
  have e1 := sec5Comp_map hA (MulAut.conj g).symm
  have e2 := sec5Comp_map hA' (MulAut.conj g).symm
  rw [map_symm_map_mulEquiv] at e1 e2
  exact Subgroup.map_injective (MulAut.conj g).symm.injective (h1 _ _ e1 e2)

theorem sign_perm_eq_one_of_sec5One (h : Sec5Data X n z Z S) (h1 : Sec5One X n Z) {s : X}
    (hs : IsSec5Inv X Z s) {A : Subgroup X} (hA : Sec5Comp X n (normalizer (Z : Set X)) A)
    (hsA : s ∈ normalizer (A : Set X)) (M : AhatModel X n A) : sign (M.perm s hsA) = 1 := by
  classical
  have hn : 8 ≤ n := h.maxdeg.1
  have hZ : Z = zpowers z := h.Z_eq_zpowers h1
  have hz2 : orderOf z = 2 := h.orderOf_z
  have hNC : normalizer (Z : Set X) = centralizer ({z} : Set X) := by
    rw [hZ]; exact normalizer_zpowers_eq_centralizer hz2
  have hKA : K0 X n (normalizer (Z : Set X)) = A := K0_eq_of_sec5Comp_unique h1 hA
  have hNA : normalizer (Z : Set X) ≤ normalizer (A : Set X) :=
    hKA ▸ Sec5Data.le_normalizer_K0 X n _
  have hs1 : s ≠ 1 := fun h1' => hs.notMem (h1' ▸ one_mem Z)
  have hs2 : orderOf s = 2 := orderOf_eq_prime (by rw [sq]; exact hs.sq) hs1
  obtain ⟨g, hgZ, hg1⟩ := hs.conj
  have hgz : g⁻¹ * s * g = z := by
    rw [hZ] at hgZ
    rcases (mem_zpowers_iff_of_orderOf_two hz2).1 hgZ with h0 | h0
    · exact absurd h0 hg1
    · exact h0
  have hgs : (g⁻¹)⁻¹ * z * g⁻¹ = s := by
    rw [← hgz]; group
  obtain ⟨S', h'⟩ := h.mirror g⁻¹
  rw [hgs] at h'
  have hφz : (MulAut.conj (g⁻¹)⁻¹).toMonoidHom z = s := by simp [← hgs]
  have hZ' : Z.map (MulAut.conj (g⁻¹)⁻¹).toMonoidHom = zpowers s := by
    rw [hZ, MonoidHom.map_zpowers, hφz]
  have h1' : Sec5One X n (Z.map (MulAut.conj (g⁻¹)⁻¹).toMonoidHom) :=
    sec5One_map_conj h1 (g⁻¹)⁻¹
  have hsN : s ∈ normalizer (Z : Set X) := hs.mem
  have hsz : s * z = z * s := Subgroup.mem_centralizer_singleton_iff.1 (hNC ▸ hsN)
  have hzN' :
      z ∈ normalizer ((Z.map (MulAut.conj (g⁻¹)⁻¹).toMonoidHom : Subgroup X) : Set X) := by
    rw [hZ', normalizer_zpowers_eq_centralizer hs2]
    exact Subgroup.mem_centralizer_singleton_iff.2 hsz.symm
  have hzz : z * z = 1 := h.Z_sq_eq_one h.z_mem
  obtain ⟨b, -, hbz, hbb⟩ := h'.exists_sq_eq_z h1' hzN' hzz
  have hbN : b ∈ normalizer (Z : Set X) := by
    rw [hNC]; exact Subgroup.mem_centralizer_singleton_iff.2 hbz
  have hbA : b ∈ normalizer (A : Set X) := hNA hbN
  have e1 : M.perm s hsA = M.permX s := (M.permX_of_mem hsA).symm
  have e2 : M.permX s = M.permX b * M.permX b := by
    rw [← hbb, M.permX_mul hn hbA hbA]
  rw [e1, e2, Perm.sign_mul]
  exact Int.units_mul_self _

theorem perm_ne_one_of_mem_Z (h : Sec5Data X n z Z S) {s : X} (hs : IsSec5Inv X Z s) {w : X}
    (hwZ : w ∈ Z) (hw1 : w ≠ 1) (hws : w * s = s * w) {B : Subgroup X}
    (hB : Sec5Comp X n (centralizer ({s} : Set X)) B) (hwB : w ∈ normalizer (B : Set X))
    (MB : AhatModel X n B) : MB.perm w hwB ≠ 1 := by
  intro h1
  have hn : 8 ≤ n := h.maxdeg.1
  have hc : CentModOdd B w := (MB.perm_eq_one_iff hn hwB).1 h1
  have hq : w ∈ centralizerSection B (pPrimeCoreOf 2 B) := mem_QOf_iff.2 ⟨hwB, hc⟩
  have hw2 : w ^ 2 = 1 := by rw [sq]; exact h.Z_sq_eq_one hwZ
  exact K0_K0_inf_ne_bot_of_mem_centralizerSection hw2 hB hq (sec5_K0_inf_eq_bot h hs hwZ hw1 hws)

theorem exists_quatPiece (h : Sec5Data X n z Z S) (h1 : Sec5One X n Z) {s : X}
    (hs : IsSec5Inv X Z s) {A : Subgroup X} (hA : Sec5Comp X n (normalizer (Z : Set X)) A)
    (hsA : s ∈ normalizer (A : Set X)) (M : AhatModel X n A)
    (hfix : fixCount (M.perm s hsA) = 4) :
    Nonempty (QuatPiece z (centralizer ({z} : Set X) ⊓ centralizer ({s} : Set X))) := by
  have hn : 8 ≤ n := h.maxdeg.1
  have hZ : Z = zpowers z := h.Z_eq_zpowers h1
  have hz2 : orderOf z = 2 := h.orderOf_z
  have hNC : normalizer (Z : Set X) = centralizer ({z} : Set X) := by
    rw [hZ]; exact normalizer_zpowers_eq_centralizer hz2
  have hKA : K0 X n (normalizer (Z : Set X)) = A := K0_eq_of_sec5Comp_unique h1 hA
  have hzA : z ∈ A := by rw [← hKA]; exact h.z_mem_K0
  have hzc : ∀ g ∈ A, z * g = g * z := fun g hg => h.Z_le_center_K0 h.z_mem (hKA.ge hg)
  have hzz : z * z = 1 := h.Z_sq_eq_one h.z_mem
  have hz1 : z ≠ 1 := fun h1' => by
    rw [h1', orderOf_one] at hz2
    exact absurd hz2 (by norm_num)
  have hNA : centralizer ({z} : Set X) ≤ normalizer (A : Set X) := by
    rw [← hNC, ← hKA]
    exact Sec5Data.le_normalizer_K0 X n _
  exact exists_quatPiece_of_model M hn hsA hs.sq hzA hzc hzz hz1 hNA hfix

theorem exists_lift_alt_cycles (hn : 8 ≤ n) {B : Subgroup X} (MB : AhatModel X n B) {w : X}
    (hwB : w ∈ normalizer (B : Set X)) (hw2 : w * w = 1) :
    ∀ π ∈ alternatingGroup (MB.perm w hwB).cycleFactorsFinset,
      ∃ b ∈ B ⊓ centralizer ({w} : Set X),
        ∃ hb : MB.permX b ∈ centralizer ({MB.perm w hwB} : Set (Perm (Fin n))),
          toPermHom (MB.perm w hwB) ⟨MB.permX b, hb⟩ = π := by
  classical
  intro π hπ
  haveI : Finite MB.K := Finite.of_equiv _ MB.e.toEquiv
  have hind := MB.induces_perm hn w hwB
  have hσ2 : MB.perm w hwB * MB.perm w hwB = 1 := perm_sq_eq_one hn MB hwB hw2
  obtain ⟨k, hk⟩ := involution_support_even hσ2
  obtain ⟨⟨x, hx⟩, hxπ⟩ := alt_le_range_actC hind hσ2 hk hπ
  obtain ⟨u, hu, hwu, hux⟩ := MB.exists_lift_cent hwB hw2 (mem_fixSub.1 hx)
  have hρ : MB.permX u = MB.C.ρ x := by
    rw [MB.permX_of_mem_A hn hu, hux]
  have hxc : MB.C.ρ x ∈ centralizer ({MB.perm w hwB} : Set (Perm (Fin n))) :=
    Subgroup.mem_centralizer_singleton_iff.2 (hind.ρ_comm_of_mem_fixSub hx)
  have hb : MB.permX u ∈ centralizer ({MB.perm w hwB} : Set (Perm (Fin n))) := hρ ▸ hxc
  refine ⟨u, ⟨hu, Subgroup.mem_centralizer_singleton_iff.2 hwu.symm⟩, hb, ?_⟩
  have : (⟨MB.permX u, hb⟩ : ↥(centralizer ({MB.perm w hwB} : Set (Perm (Fin n))))) =
      ⟨MB.C.ρ x, hxc⟩ := Subtype.ext hρ
  rw [this]
  exact hxπ

end Pieces

end CFSG.OddStandard.Solomon75
