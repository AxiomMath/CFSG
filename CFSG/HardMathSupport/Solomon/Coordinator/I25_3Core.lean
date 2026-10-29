module

public import CFSG.HardMathSupport.Solomon.Coordinator.I25_3Layer
public import CFSG.HardMathSupport.Solomon.Coordinator.I25_3Quot
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeReduction
public import CFSG.LieType.Chevalley.OrdinaryRootCentralizerGeneration

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns
open scoped commutatorElement

theorem i253_exists_char {Y : Type} [Group Y] (hY : IsSLThreeEpsAny Y) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 3 ∧ SL3EpsOfChar p Y := by
  rcases hY with ⟨K, hF, hfin, hmod, ⟨e⟩⟩ | ⟨K, hF, hfin, q, hcard, hq3, hq2, ⟨e⟩⟩
  · have := Fintype.ofFinite K
    obtain ⟨p, hchar⟩ := CharP.exists K
    have hp : p.Prime := CharP.char_is_prime K p
    refine ⟨p, hp, ?_, Or.inl ⟨K, hF, hfin, hchar, hmod, ⟨e⟩⟩⟩
    rintro rfl
    obtain ⟨n, hpn, hcn⟩ := FiniteField.card K 3
    rw [← Nat.card_eq_fintype_card] at hcn
    rw [hcn] at hmod
    have h3 : 3 ∣ 3 ^ (n : ℕ) := dvd_pow_self 3 n.ne_zero
    omega
  · have := Fintype.ofFinite K
    obtain ⟨p, hchar⟩ := CharP.exists K
    have hp : p.Prime := CharP.char_is_prime K p
    refine ⟨p, hp, ?_, Or.inr ⟨K, hF, hfin, q, hchar, hcard, hq3, hq2, ⟨e⟩⟩⟩
    rintro rfl
    obtain ⟨n, hpn, hcn⟩ := FiniteField.card K 3
    rw [← Nat.card_eq_fintype_card] at hcn
    have h3 : 3 ∣ q ^ 2 := by
      rw [← hcard, hcn]; exact dvd_pow_self 3 n.ne_zero
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega

theorem input25_3_core (hF : Input25_3FactsNo38) (h181 : LocalBalance.Lemma514CoverNs.Input18_1)
    (hB : B3Quasi) {Y : Type} [Group Y] [Finite Y] {K J A : Subgroup Y} {b : Y}
    (hKq : CFSG.Open.IsQuasisimple ↥K) (hKK : CFSG.Open.IsKGroup ↥K)
    (hbK : b ∈ K) (hb3 : orderOf b = 3)
    (hJ : CFSG.Open.IsComponentOf J (K ⊓ Subgroup.centralizer ({b} : Set Y))) (hbJ : b ∈ J)
    (hJT : IsSLThreeEpsAny (barOf 3 J))
    (hZ : Subgroup.center (barOf 3 J) = Subgroup.zpowers (QuotientGroup.mk (⟨b, hbJ⟩ : ↥J)))
    (hAN : A ≤ Subgroup.normalizer (K : Set Y)) (hAel : CFSG.Open.IsElemAbelian 3 A)
    (hA9 : Nat.card A = 9) (hbA : b ∈ A) (hfield : ∀ a ∈ A, a ≠ 1 → InducesFieldAut 3 J a)
    (hU8 : IsSU38 (barOf 3 J) → ∀ a ∈ A, ∀ h : a ∈ Subgroup.normalizer (J : Set Y),
      barAut 3 J ⟨a, h⟩ = 1) :
    J = K ∨ ∃ a ∈ A, a ≠ 1 ∧ b ∉ oPrimePOf 3 (K ⊓ Subgroup.centralizer ({a} : Set Y)) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hne, hall⟩ := hcon
  have hb3' : b ^ 3 = 1 := by have := pow_orderOf_eq_one b; rwa [hb3] at this
  have hb1 : b ≠ 1 := fun h => by rw [h, orderOf_one] at hb3; omega
  have hJK : J ≤ K := hJ.1.trans inf_le_left
  have hbN : b ∈ Subgroup.normalizer (K : Set Y) := Subgroup.le_normalizer hbK
  have habel : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy => by
    have := hAel.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
    exact congrArg Subtype.val this
  have hbZK : ¬ ∀ k ∈ K, k * b = b * k := by
    intro hc
    have hKb : K ≤ Subgroup.centralizer ({b} : Set Y) := fun k hk =>
      Subgroup.mem_centralizer_singleton_iff.2 (hc k hk)
    have h1 : K ⊓ Subgroup.centralizer ({b} : Set Y) = K := inf_eq_left.2 hKb
    have h2 := hJ.2.1
    rw [h1] at h2
    exact hne (i253_eq_of_isSubnormal hKq hJ.2.2 h2)
  obtain ⟨p, hp, hp3, hpc⟩ := i253_exists_char hJT
  have h3J : 3 ∣ Nat.card ↥J := by
    have : orderOf (⟨b, hbJ⟩ : ↥J) = 3 := by
      rw [orderOf_eq_prime_iff]
      exact ⟨Subtype.ext (by simpa using hb3'), fun h => hb1 (congrArg Subtype.val h)⟩
    rw [← this]; exact orderOf_dvd_natCard _
  have hcomp : GLAPComponent 3 (K ⊓ Subgroup.centralizer ({b} : Set Y)) J :=
    i253_glaPComponent_of_subnormal hJ.1 hJ.2.1 hJ.2.2 h3J
  have hChev := hF.chev Y K hKq hKK b hbN (by
    rw [hb3']; exact Subgroup.one_mem _) J hcomp p hp hpc
  obtain ⟨a₀, ha₀A, ha₀⟩ := i253_exists_not_mem_zpowers hA9 hbA hb3
  have ha₀1 : a₀ ≠ 1 := fun h => ha₀ (h ▸ Subgroup.one_mem _)
  have ha₀3 : a₀ ^ 3 = 1 := hAel.2 a₀ ha₀A
  have ha₀b : a₀ * b = b * a₀ := habel a₀ ha₀A b hbA
  have hfieldAll : ∀ a ∈ A, a ≠ 1 → ∃ (haJ : a ∈ Subgroup.normalizer (J : Set Y)),
      IsFieldAutThree (barAut 3 J ⟨a, haJ⟩) ∧ (barAut 3 J ⟨a, haJ⟩ ≠ 1 → ¬ IsSU38 (barOf 3 J)) := by
    intro a ha ha1
    obtain ⟨haJ, hfa⟩ := hfield a ha ha1
    exact ⟨haJ, hfa, fun hne h8 => hne (hU8 h8 a ha haJ)⟩
  obtain ⟨ha₀J, hfa₀, h8₀⟩ := hfieldAll a₀ ha₀A ha₀1
  obtain ⟨-, u, hup, hua, hub, huπ⟩ := i253_layer h181 hKK hbK hb3 hJ hbJ hZ hp hp3 hpc
    (hAN ha₀A) ha₀J ha₀3 ha₀b hfa₀ h8₀
  have huJ : (u : Y) ∈ J := u.2
  have huK : (u : Y) ∈ K := hJK huJ
  have huA : ∀ a ∈ A, (u : Y) * a = a * u :=
    i253_comm_of_generators hA9 hbA ha₀A hb3 ha₀ hub hua
  obtain ⟨k₀, hk₀⟩ := hup ⟨(u : Y), Subgroup.mem_zpowers _⟩
  have huk : (u : Y) ^ (p ^ k₀) = 1 := by simpa using congrArg Subtype.val hk₀
  have hunc : ¬ Subgroup.zpowers (u : Y) ≤ centerIn K := by
    intro hle
    have hu : (u : Y) ∈ centerIn K := hle (Subgroup.mem_zpowers _)
    obtain ⟨z, hz, hzu⟩ := hu
    have hcomm : ∀ x : ↥J, u * x = x * u := by
      intro x
      have := Subgroup.mem_center_iff.1 hz ⟨x.1, hJK x.2⟩
      apply Subtype.ext
      have h1 : ((z : ↥K) : Y) = u := hzu
      have h2 := congrArg Subtype.val this
      simp only [Subgroup.coe_mul] at h2 ⊢
      rw [← h1]; exact h2.symm
    have huc : u ∈ Subgroup.center ↥J := Subgroup.mem_center_iff.2 fun g => (hcomm g).symm
    have hπc : QuotientGroup.mk' (GLAPPrimeCore 3 ↥J) u ∈ Subgroup.center (barOf 3 J) := by
      rw [Subgroup.mem_center_iff]
      intro q
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore 3 ↥J) q
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 huc g]
    rw [hZ] at hπc
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hπc
    have hb'3 : (QuotientGroup.mk (⟨b, hbJ⟩ : ↥J) : barOf 3 J) ^ 3 = 1 := by
      rw [← QuotientGroup.mk_pow]
      have : (⟨b, hbJ⟩ : ↥J) ^ 3 = 1 := Subtype.ext (by simpa using hb3')
      rw [this, QuotientGroup.mk_one]
    have h3 : (QuotientGroup.mk' (GLAPPrimeCore 3 ↥J) u) ^ 3 = 1 := by
      rw [← hj, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
      show ((QuotientGroup.mk (⟨b, hbJ⟩ : ↥J) : barOf 3 J) ^ 3) ^ j = 1
      rw [hb'3, one_zpow]
    have hpk : (QuotientGroup.mk' (GLAPPrimeCore 3 ↥J) u) ^ (p ^ k₀) = 1 := by
      rw [← map_pow]
      have : u ^ (p ^ k₀) = 1 := Subtype.ext (by simpa using huk)
      rw [this, map_one]
    have hcop : Nat.Coprime (p ^ k₀) 3 :=
      Nat.Coprime.pow_left _ ((Nat.coprime_primes hp Nat.prime_three).2 hp3)
    have hord : orderOf (QuotientGroup.mk' (GLAPPrimeCore 3 ↥J) u) ∣ Nat.gcd (p ^ k₀) 3 :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hpk) (orderOf_dvd_of_pow_eq_one h3)
    rw [hcop] at hord
    exact huπ (orderOf_eq_one_iff.1 (Nat.dvd_one.1 hord))
  have hex : ∃ Q : Subgroup Y, IsMaxInvSub A K p Q ∧ Subgroup.zpowers (u : Y) ≤ Q := by
    let S : Set (Subgroup Y) := {Q' | Subgroup.zpowers (u : Y) ≤ Q' ∧ Q' ≤ K ∧ IsPGroup p ↥Q' ∧
      A ≤ Subgroup.normalizer (Q' : Set Y)}
    have hAu : A ≤ Subgroup.normalizer ((Subgroup.zpowers (u : Y) : Subgroup Y) : Set Y) := by
      intro a ha
      apply Subgroup.centralizer_le_normalizer
      exact (mem_centralizer_zpowers_iff a u).2 (huA a ha)
    have hne : S.Nonempty :=
      ⟨Subgroup.zpowers (u : Y), le_rfl, (Subgroup.zpowers_le).2 huK, i253_isPGroup_zpowers huk, hAu⟩
    obtain ⟨Q, hQS, hQmax⟩ := (wellFounded_gt (α := Subgroup Y)).has_min S hne
    refine ⟨Q, ⟨hQS.2.1, hQS.2.2.1, hQS.2.2.2, fun Q' hQ'K hQ'p hQ'N hQQ' => ?_⟩, hQS.1⟩
    by_contra hneq
    exact hQmax Q' ⟨hQS.1.trans hQQ', hQ'K, hQ'p, hQ'N⟩
      (lt_of_le_of_ne hQQ' (fun h => hneq h.symm))
  obtain ⟨Q, hmax, hQ0⟩ := hex
  have hQK : Q ≤ K := hmax.1
  have hQp : IsPGroup p ↥Q := hmax.2.1
  have hAQ : A ≤ Subgroup.normalizer (Q : Set Y) := hmax.2.2.1
  have hQnc : ¬ Q ≤ centerIn K := fun h => hunc (hQ0.trans h)
  have hA3 : IsPGroup 3 ↥A := fun g => ⟨1, by
    apply Subtype.ext
    simpa using hAel.2 g g.2⟩
  have hCQ := hF.borelTits Y K A Q p hp hp3 hKq hChev hAN hA3 hmax hQnc
  have hbQ : ∃ x ∈ Q, b * x ≠ x * b := by
    by_contra hno
    push Not at hno
    have hbc : b ∈ Subgroup.centralizer (Q : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact (hno x hx).symm
    have hmem := hCQ b hbK hbc
    have hbZ : b ∈ centerIn K := by
      refine i253_mem_of_mem_sup hp hp3 ?_ hQp hb3' hmem
      rintro _ ⟨z, hz, rfl⟩ x hx
      have := Subgroup.mem_center_iff.1 hz ⟨x, hQK hx⟩
      simpa using congrArg Subtype.val this.symm
    obtain ⟨z, hz, hzb⟩ := hbZ
    apply hbZK
    intro k hk
    have := Subgroup.mem_center_iff.1 hz ⟨k, hk⟩
    have h2 := congrArg Subtype.val this
    simp only [Subgroup.coe_mul] at h2
    have h1 : ((z : ↥K) : Y) = b := hzb
    rw [h1] at h2
    exact h2
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CFSG.IsElementaryAbelian 3 ↥A := i253_isElementaryAbelian hAel
  have hgen : Q ≤ ⨆ a ∈ A, ⨆ (_ : a ≠ 1), Q ⊓ Subgroup.centralizer ({a} : Set Y) := by
    refine CFSG.LieType.Chevalley.le_iSup_inf_centralizer_of_coprime (p := 3) (A := A) (H := Q)
      (C := Q) ?_ ?_ hAQ le_rfl
    · rw [hA9]; norm_num
    · obtain ⟨n, hn⟩ := hQp.exists_card_eq
      rw [hn]
      intro h
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
      exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 this).symm
  have hex2 : ∃ a ∈ A, a ≠ 1 ∧ ∃ x ∈ Q ⊓ Subgroup.centralizer ({a} : Set Y), b * x ≠ x * b := by
    by_contra hno
    push Not at hno
    obtain ⟨x, hxQ, hbx⟩ := hbQ
    have hle : (⨆ a ∈ A, ⨆ (_ : a ≠ 1), Q ⊓ Subgroup.centralizer ({a} : Set Y)) ≤
        Subgroup.centralizer ({b} : Set Y) := by
      refine iSup₂_le fun a ha => iSup_le fun ha1 y hy => ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hno a ha ha1 y hy).symm
    have := hle (hgen hxQ)
    rw [Subgroup.mem_centralizer_singleton_iff] at this
    exact hbx this.symm
  obtain ⟨a, haA, ha1, x, hxQa, hbx⟩ := hex2
  have hxQ : x ∈ Q := hxQa.1
  have hab : a * b = b * a := habel a haA b hbA
  have haK := hAN haA
  have ha3 : a ^ 3 = 1 := hAel.2 a haA
  set X := K ⊓ Subgroup.centralizer ({a} : Set Y) with hXdef
  have hbX : b ∈ X := ⟨hbK, Subgroup.mem_centralizer_singleton_iff.2 hab.symm⟩
  have hxX : x ∈ X := ⟨hQK hxQ, hxQa.2⟩
  have hbO : b ∈ oPrimePOf 3 X := hall a haA ha1
  set g := b * x * b⁻¹ * x⁻¹ with hg
  have hgO : g ∈ oPrimePOf 3 X := by
    have hn := Lemma27Ns.g2_oPrimePOf_normal X
    have h1 : (⟨b, hbX⟩ : ↥X) ∈ (oPrimePOf 3 X).subgroupOf X := hbO
    have h2 := hn.conj_mem _ h1 ⟨x, hxX⟩
    have h2' : x * b * x⁻¹ ∈ oPrimePOf 3 X := Subgroup.mem_subgroupOf.1 h2
    have : g = b * (x * b * x⁻¹)⁻¹ := by rw [hg]; group
    rw [this]
    exact (oPrimePOf 3 X).mul_mem hbO ((oPrimePOf 3 X).inv_mem h2')
  have hgQ : g ∈ Q := by
    have hbn : b * x * b⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.1 (hAQ hbA) x).1 hxQ
    exact Q.mul_mem hbn (Q.inv_mem hxQ)
  obtain ⟨kq, hkq⟩ := hQp ⟨g, hgQ⟩
  have hgk : g ^ (p ^ kq) = 1 := by simpa using congrArg Subtype.val hkq
  have hgP : g ∈ GLAPPrimeCoreOf 3 X := by
    obtain ⟨k, hk⟩ := Lemma27Ns.g2_mem_oPrimePOf hgO
    have hcop : Nat.Coprime (3 ^ k) (orderOf g) := by
      have hord : orderOf g ∣ p ^ kq := orderOf_dvd_of_pow_eq_one hgk
      exact Nat.Coprime.coprime_dvd_right hord
        (Nat.Coprime.pow _ _ ((Nat.coprime_primes Nat.prime_three hp).2 (Ne.symm hp3)))
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
    rw [← hm]
    exact (GLAPPrimeCoreOf 3 X).pow_mem hk m
  obtain ⟨haJ, hfa, h8⟩ := hfieldAll a haA ha1
  obtain ⟨hbL, -⟩ := i253_layer h181 hKK hbK hb3 hJ hbJ hZ hp hp3 hpc haK haJ ha3 hab hfa h8
  have hmapP := CFSG.HardMathSupport.Timmesfeld.Coordinator.map_glaPPrimeCoreOf_of_injective 3 K.subtype K.subtype_injective
    (fixSubgroup (i253α K a haK))
  rw [map_fixSubgroup_i253α] at hmapP
  have hgmem : g ∈ (GLAPPrimeCoreOf 3 (fixSubgroup (i253α K a haK))).map K.subtype := by
    rw [hmapP]; exact hgP
  obtain ⟨r, hr, hrg⟩ := hgmem
  have hK3 : 3 ∣ Nat.card ↥K := by
    have : orderOf (⟨b, hbK⟩ : ↥K) = 3 := by
      rw [orderOf_eq_prime_iff]
      exact ⟨Subtype.ext (by simpa using hb3'), fun h => hb1 (congrArg Subtype.val h)⟩
    rw [← this]; exact orderOf_dvd_natCard _
  have hbg : b * g = g * b := by
    have hx3 : (⟨b, hbK⟩ : ↥K) ^ 3 = 1 := Subtype.ext (by simpa using hb3')
    have h1 := i253_b3_step hB hKq hKK hK3 (i253α K a haK) (i253α_pow_three K a haK ha3) hbL hr hx3
    have h2 := congrArg Subtype.val h1
    simp only [Subgroup.coe_mul] at h2
    have h3 : ((r : ↥K) : Y) = g := hrg
    rw [h3] at h2
    exact h2
  have h1 := i253_cube_trick hp hp3 hb3' (by rw [hg] at hbg; exact hbg) hgk
  apply hbx
  have : b * x * b⁻¹ = x := by
    have h2 : b * x * b⁻¹ * x⁻¹ = 1 := h1
    exact mul_inv_eq_one.1 h2
  calc b * x = b * x * b⁻¹ * b := by group
    _ = x * b := by rw [this]

end CFSG.HardMathSupport.Solomon.Coordinator
