module

public import CFSG.ClassicalInvolution.Q3.TL3S8Std

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped Pointwise

section Small

variable {A : Type*} [Group A]

theorem exists_closure_pair_of_lt_four_mul_orderOf [Finite A] {H : Subgroup A} {g : A}
    (hg : g ∈ H) (hlt : Nat.card H < 4 * orderOf g) : ∃ b : A, Subgroup.closure {g, b} = H := by
  by_cases hH : Subgroup.zpowers g = H
  · exact ⟨g, by rw [Set.pair_eq_singleton, ← Subgroup.zpowers_eq_closure, hH]⟩
  · have hle : Subgroup.zpowers g ≤ H := Subgroup.zpowers_le.mpr hg
    obtain ⟨b, hbH, hbg⟩ : ∃ b ∈ H, b ∉ Subgroup.zpowers g := by
      by_contra hcon
      push Not at hcon
      exact hH (le_antisymm hle hcon)
    refine ⟨b, ?_⟩
    set K : Subgroup A := Subgroup.closure {g, b} with hK
    have hKH : K ≤ H := by
      rw [hK, Subgroup.closure_le]
      rintro x (rfl | rfl)
      · exact hg
      · exact hbH
    have hgK : Subgroup.zpowers g ≤ K := Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
    have hbK : b ∈ K := Subgroup.subset_closure (by simp)
    have hm : Nat.card (Subgroup.zpowers g) = orderOf g := Nat.card_zpowers g
    have hne : Nat.card K ≠ Nat.card (Subgroup.zpowers g) := by
      intro heq
      have := Subgroup.eq_of_le_of_card_ge hgK heq.le
      exact hbg (this ▸ hbK)
    obtain ⟨c, hc⟩ := Subgroup.card_dvd_of_le hgK
    have hc1 : c ≠ 1 := by
      rintro rfl
      exact hne (by rw [hc, mul_one])
    have hKpos : 0 < Nat.card K := Nat.card_pos
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hc
      omega
    have h2m : 2 * Nat.card (Subgroup.zpowers g) ≤ Nat.card K := by
      calc 2 * Nat.card (Subgroup.zpowers g) = Nat.card (Subgroup.zpowers g) * 2 := by ring
        _ ≤ Nat.card (Subgroup.zpowers g) * c := Nat.mul_le_mul_left _ (by omega)
        _ = Nat.card K := hc.symm
    by_contra hKH'
    have hlt' : Nat.card K < Nat.card H := by
      rcases (Subgroup.card_le_of_le hKH).lt_or_eq with h | h
      · exact h
      · exact absurd (Subgroup.eq_of_le_of_card_ge hKH h.ge) hKH'
    obtain ⟨d, hd⟩ := Subgroup.card_dvd_of_le hKH
    have hd1 : d ≠ 1 := by
      rintro rfl
      omega
    have hd0 : d ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hd
      have : 0 < Nat.card H := Nat.card_pos
      omega
    have h2K : 2 * Nat.card K ≤ Nat.card H := by
      calc 2 * Nat.card K = Nat.card K * 2 := by ring
        _ ≤ Nat.card K * d := Nat.mul_le_mul_left _ (by omega)
        _ = Nat.card H := hd.symm
    omega

theorem exists_orderOf_four_of_card_eight [Finite A] (hcard : Nat.card A ≤ 24)
    (h3 : 3 ∣ Nat.card A) (h4 : ∃ x : A, orderOf x = 4) {H : Subgroup A} (hH : Nat.card H = 8) :
    ∃ g ∈ H, orderOf g = 4 := by
  classical
  obtain ⟨x, hx⟩ := h4
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hX : IsPGroup 2 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hx]; norm_num)
  have hHp : IsPGroup 2 H := IsPGroup.of_card (n := 3) (by rw [hH]; norm_num)
  obtain ⟨Q, hXQ⟩ := hX.exists_le_sylow
  obtain ⟨P, hHP⟩ := hHp.exists_le_sylow
  have hpos : 0 < Nat.card A := Nat.card_pos
  set e := (Nat.card A).factorization 2 with he
  have hPe : Nat.card P = 2 ^ e := Sylow.card_eq_multiplicity P
  have he3 : e = 3 := by
    have h8P : 8 ∣ 2 ^ e := hPe ▸ hH ▸ Subgroup.card_dvd_of_le hHP
    have hdvdA : 2 ^ e ∣ Nat.card A := hPe ▸ Subgroup.card_subgroup_dvd_card (P : Subgroup A)
    have hge : 3 ≤ e := by
      by_contra hlt
      push Not at hlt
      have : 2 ^ e ≤ 4 := by
        calc 2 ^ e ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
          _ = 4 := by norm_num
      have := Nat.le_of_dvd (by positivity) h8P
      omega
    by_contra hne
    have h16 : 2 ^ 4 ∣ Nat.card A :=
      (pow_dvd_pow 2 (show 4 ≤ e by omega)).trans hdvdA
    have h48 : 48 ∣ Nat.card A := by
      have hco : Nat.Coprime 16 3 := by norm_num
      have := hco.mul_dvd_of_dvd_of_dvd (by simpa using h16) h3
      simpa using this
    have := Nat.le_of_dvd hpos h48
    omega
  have hHP' : H = P := by
    refine Subgroup.eq_of_le_of_card_ge hHP ?_
    rw [hPe, he3, hH]
    norm_num
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq A Q P
  have hxQ : x ∈ (Q : Subgroup A) := hXQ (Subgroup.mem_zpowers x)
  have h1 : (MulAut.conj c) • x ∈ (MulAut.conj c) • (Q : Subgroup A) :=
    Subgroup.smul_mem_pointwise_smul x (MulAut.conj c) _ hxQ
  rw [← Sylow.coe_subgroup_smul, hc] at h1
  refine ⟨(MulAut.conj c) • x, hHP' ▸ h1, ?_⟩
  rw [MulAut.smul_def, MulEquiv.orderOf_eq, hx]

theorem exists_closure_pair_of_isPGroup_small [Finite A] (hcard : Nat.card A ≤ 24)
    (h3 : 3 ∣ Nat.card A) (h4 : ∃ x : A, orderOf x = 4) {H : Subgroup A} (hH : IsPGroup 2 H) :
    ∃ a b : A, Subgroup.closure {a, b} = H := by
  classical
  obtain ⟨k, hk⟩ := hH.exists_card_eq
  have hpos : 0 < Nat.card A := Nat.card_pos
  have hdvd : Nat.card H ∣ Nat.card A := Subgroup.card_subgroup_dvd_card H
  have hk3 : k ≤ 3 := by
    by_contra hk4
    push Not at hk4
    have h16 : 2 ^ 4 ∣ Nat.card A := (pow_dvd_pow 2 hk4).trans (hk ▸ hdvd)
    have h48 : 48 ∣ Nat.card A := by
      have hco : Nat.Coprime 16 3 := by norm_num
      have := hco.mul_dvd_of_dvd_of_dvd (by simpa using h16) h3
      simpa using this
    have := Nat.le_of_dvd hpos h48
    omega
  by_cases hbot : H = ⊥
  · exact ⟨1, 1, by rw [hbot, Set.pair_eq_singleton, Subgroup.closure_singleton_one]⟩
  · by_cases h8 : Nat.card H = 8
    · obtain ⟨g, hgH, hg4⟩ := exists_orderOf_four_of_card_eight hcard h3 h4 h8
      obtain ⟨b, hb⟩ := exists_closure_pair_of_lt_four_mul_orderOf hgH (by rw [h8, hg4]; norm_num)
      exact ⟨g, b, hb⟩
    · obtain ⟨⟨g, hgH⟩, hg1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hbot
      have hg1 : g ≠ 1 := fun h => hg1' (Subtype.ext h)
      have hH4 : Nat.card H ≤ 4 := by
        have : k ≤ 2 := by
          by_contra hk2
          have : k = 3 := by omega
          exact h8 (by rw [hk, this]; norm_num)
        rw [hk]
        calc 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) this
          _ = 4 := by norm_num
      have hg2 : 2 ≤ orderOf g := by
        have h0 : orderOf g ≠ 0 := (isOfFinOrder_of_finite g).orderOf_pos.ne'
        have h1 : orderOf g ≠ 1 := fun h => hg1 (orderOf_eq_one_iff.mp h)
        omega
      obtain ⟨b, hb⟩ := exists_closure_pair_of_lt_four_mul_orderOf hgH (by omega)
      exact ⟨g, b, hb⟩

end Small

section Q8

open QuaternionGroup

private def q8E (u v : QuaternionGroup 2) : QuaternionGroup 2 → QuaternionGroup 2
  | .a k => u ^ k.val
  | .xa k => v * u ^ k.val

private def Q8Pair (u v : QuaternionGroup 2) : Prop :=
  (∀ x y, q8E u v (x * y) = q8E u v x * q8E u v y) ∧ ∀ x y, q8E u v x = q8E u v y → x = y

private instance (u v : QuaternionGroup 2) : Decidable (Q8Pair u v) := by
  unfold Q8Pair; infer_instance

private noncomputable def q8AutOfPair (u v : QuaternionGroup 2) (h : Q8Pair u v) :
    MulAut (QuaternionGroup 2) :=
  MulEquiv.ofBijective (MonoidHom.mk' (q8E u v) h.1) (Finite.injective_iff_bijective.mp h.2)

private theorem q8AutOfPair_apply (u v : QuaternionGroup 2) (h : Q8Pair u v)
    (x : QuaternionGroup 2) : q8AutOfPair u v h x = q8E u v x := rfl

private theorem q8Pair_three : Q8Pair (xa 0) (xa 3) := by decide +kernel

private theorem q8Pair_four : Q8Pair (xa 0) (a 3) := by decide +kernel

private noncomputable def q8Aut3 : MulAut (QuaternionGroup 2) := q8AutOfPair _ _ q8Pair_three

private noncomputable def q8Aut4 : MulAut (QuaternionGroup 2) := q8AutOfPair _ _ q8Pair_four

private theorem q8Aut3_cube : q8Aut3 ^ 3 = 1 := by
  ext x
  simp only [pow_succ', pow_zero, MulAut.mul_apply, MulAut.one_apply, mul_one, q8Aut3,
    q8AutOfPair_apply]
  revert x
  decide +kernel

private theorem q8Aut3_ne_one : q8Aut3 ≠ 1 := by
  intro h
  have := congrArg (fun φ : MulAut (QuaternionGroup 2) => φ (a 1)) h
  simp only [q8Aut3, q8AutOfPair_apply, MulAut.one_apply] at this
  revert this
  decide +kernel

private theorem q8Aut4_sq_ne_one : q8Aut4 ^ 2 ≠ 1 := by
  intro h
  have := congrArg (fun φ : MulAut (QuaternionGroup 2) => φ (a 1)) h
  simp only [pow_succ', pow_zero, MulAut.mul_apply, MulAut.one_apply, mul_one, q8Aut4,
    q8AutOfPair_apply] at this
  revert this
  decide +kernel

private theorem q8Aut4_pow_four : q8Aut4 ^ 4 = 1 := by
  ext x
  simp only [pow_succ', pow_zero, MulAut.mul_apply, MulAut.one_apply, mul_one, q8Aut4,
    q8AutOfPair_apply]
  revert x
  decide +kernel

private theorem orderOf_q8Aut3 : orderOf q8Aut3 = 3 :=
  orderOf_eq_prime q8Aut3_cube q8Aut3_ne_one

private theorem orderOf_q8Aut4 : orderOf q8Aut4 = 4 := by
  have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := q8Aut4)
    (by simpa using q8Aut4_sq_ne_one) (by simpa using q8Aut4_pow_four)
  simpa using h

theorem q8_mulAut_isPGroup_exists_closure_pair {H : Subgroup (MulAut (QuaternionGroup 2))}
    (hH : IsPGroup 2 H) : ∃ a b : MulAut (QuaternionGroup 2), Subgroup.closure {a, b} = H := by
  refine exists_closure_pair_of_isPGroup_small q8_natCard_mulEquiv_le ?_ ⟨q8Aut4, orderOf_q8Aut4⟩ hH
  have := orderOf_dvd_natCard q8Aut3
  rwa [orderOf_q8Aut3] at this

end Q8

section E3

variable {G : Type} [Group G] {K : Subgroup G}

theorem normalizerQuotientTwoGeneratedStar_of_q8
    (e : K ⧸ classicalInvolutionOddCore K ≃* QuaternionGroup 2) :
    NormalizerQuotientTwoGeneratedStar K := by
  intro P hP hPN
  have hP' : IsPGroup 2 (P.subgroupOf (Subgroup.normalizer (K : Set G))) := hP.comap_subtype
  let Ψ : Subgroup.normalizer (K : Set G) →* MulAut (QuaternionGroup 2) :=
    (MulAut.congr e).toMonoidHom.comp ((oddCoreQuotientAut K).comp (normalizerConj K))
  obtain ⟨a, b, hab⟩ := q8_mulAut_isPGroup_exists_closure_pair (hP'.map Ψ)
  refine closure_pair_sup_eq_of_map (Ψ := Ψ) (C := cStar K) (fun n hn => ?_) hPN hab
  have hn' : MulAut.congr e (oddCoreQuotientAut K (normalizerConj K n)) = 1 := hn
  rw [← map_one (MulAut.congr e)] at hn'
  exact ⟨n, MonoidHom.mem_ker.mpr ((MulAut.congr e).injective hn'), rfl⟩

end E3

section Core

variable {G : Type} [Group G] [Finite G] {R : Subgroup G} {S : Sylow 2 R} {t : G}

theorem TightDatum.exists_hom_core (h : TightDatum R S t)
    (e8 : (S : Subgroup R) ≃* QuaternionGroup 2) :
    ∃ ψ : tightCore R →* QuaternionGroup 2, Function.Surjective ψ ∧
      ∀ x : tightCore R, ψ x = 1 ↔ (x : G) ∈ oddCoreImg R := by
  classical
  have hO : OddByQuat R ((S : Subgroup R).map R.subtype) t :=
    OddByQuat.of_quaternion S h.quat h.mem h.order h.cent h.normal h.twoGroup
  set S' : Subgroup G := (S : Subgroup R).map R.subtype with hS'
  let eS' : ↥S' ≃* QuaternionGroup 2 :=
    (Subgroup.equivMapOfInjective (S : Subgroup R) R.subtype R.subtype_injective).symm.trans e8
  have hι := hO.bijective_restrict
  set ι : ↥S' →* R ⧸ oddCore R :=
    (QuotientGroup.mk' (oddCore R)).comp (Subgroup.inclusion hO.S_le) with hιdef
  let eQ : (R ⧸ oddCore R) ≃* QuaternionGroup 2 := (MulEquiv.ofBijective ι hι).symm.trans eS'
  let φ : R →* QuaternionGroup 2 := eQ.toMonoidHom.comp (QuotientGroup.mk' (oddCore R))
  have hS0K0 : S' ≤ tightCore R := fun s hs =>
    Subgroup.subset_closure ⟨hO.S_le hs, hO.S_two.to_le (Subgroup.zpowers_le.mpr hs)⟩
  have hφ : ∀ y : R, φ y = 1 ↔ (y : G) ∈ oddCoreImg R := by
    intro y
    change eQ (QuotientGroup.mk y) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
    exact (Subgroup.mem_map_iff_mem R.subtype_injective).symm
  refine ⟨φ.comp (Subgroup.inclusion (tightCore_le R)), fun q => ?_, fun x => hφ _⟩
  let s : ↥S' := eS'.symm q
  refine ⟨⟨(s : G), hS0K0 s.2⟩, ?_⟩
  change φ ⟨(s : G), tightCore_le R (hS0K0 s.2)⟩ = q
  have h1 : φ ⟨(s : G), tightCore_le R (hS0K0 s.2)⟩ = eQ (ι s) := rfl
  rw [h1]
  change eS' ((MulEquiv.ofBijective ι hι).symm (ι s)) = q
  have h2 : (MulEquiv.ofBijective ι hι).symm (ι s) = s :=
    (MulEquiv.ofBijective ι hι).symm_apply_apply s
  rw [h2]
  exact eS'.apply_symm_apply q

theorem TightDatum.nonempty_mulEquiv_core (h : TightDatum R S t)
    (e8 : (S : Subgroup R) ≃* QuaternionGroup 2) :
    Nonempty (tightCore R ⧸ classicalInvolutionOddCore (tightCore R) ≃* QuaternionGroup 2) := by
  obtain ⟨ψ, hsurj, hker⟩ := h.exists_hom_core e8
  have hker' : ψ.ker = classicalInvolutionOddCore (tightCore R) := by
    ext x
    rw [MonoidHom.mem_ker, hker]
    constructor
    · intro hx
      have hN : tightCore R ⊓ oddCoreImg R ≤ oddCoreOf (tightCore R) :=
        AscFusion.le_oddCoreOf_of_normal_odd inf_le_left core_le_normalizer_inf
          (Odd.of_dvd_nat (odd_natCard_oddCoreImg R) (Subgroup.card_dvd_of_le inf_le_right))
      obtain ⟨hx', hxO⟩ := mem_oddCoreOf_iff.mp (hN ⟨x.2, hx⟩)
      exact hxO
    · intro hx
      have hodd : Odd (Nat.card (classicalInvolutionOddCore (tightCore R))) :=
        CFSG.ComponentClassification.OddCore.odd_card (tightCore R)
      have h1 : orderOf (ψ x) ∣ Nat.card (classicalInvolutionOddCore (tightCore R)) :=
        (orderOf_map_dvd ψ x).trans (Subgroup.orderOf_dvd_natCard _ hx)
      have h2 : orderOf (ψ x) ∣ 8 := by
        have := orderOf_dvd_natCard (ψ x)
        rwa [Nat.card_eq_fintype_card, QuaternionGroup.card] at this
      have hcop : Nat.Coprime (Nat.card (classicalInvolutionOddCore (tightCore R))) 8 :=
        (Nat.Coprime.pow_right 3 (Odd.coprime_two_right hodd) : _)
      have h3 : orderOf (ψ x) = 1 :=
        Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2
      have h4 : ψ x = 1 := orderOf_eq_one_iff.mp h3
      exact (hker x).mp h4
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker'.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ hsurj)⟩

theorem TightSylowStd.normalizerQuotientTwoGeneratedStar_core {T : Sylow 2 G}
    (h : TightSylowStd R S t T) : NormalizerQuotientTwoGeneratedStar (tightCore R) := by
  obtain ⟨e8⟩ := h.q8
  obtain ⟨e⟩ := h.datum.nonempty_mulEquiv_core e8
  exact normalizerQuotientTwoGeneratedStar_of_q8 e

end Core

end CFSG.ClassicalInvolution.Q3
