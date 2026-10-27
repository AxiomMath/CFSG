module

public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossOrthBase
public import CFSG.LieType.SeitzGeneration.ExcRankVacuous

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.LieType.SeitzGeneration

@[expose] def excIndex : LieFamily → TauCeti.PrimePower → TauCeti.LieTypeIndex
  | .E6 => .E6
  | .E7 => .E7
  | .E8 => .E8
  | .F4 => .F4
  | .G2 => .G2
  | .twistedE6 => .twistedE6
  | .trialityD4 => .trialityD4
  | _ => fun _ => .tits

@[expose] def InnerPlaneBalanceAtP (k : LieFamily) (e : ℕ) (R : ℕ → Prop) : Prop :=
  ∀ (q : TauCeti.PrimePower) (hv : (excIndex k q).Valid) (p : ℕ), p.Prime → 7 ≤ p → R p →
    p ≠ q.p → orderOf ((q.card : ℕ) : ZMod p) = e → InnerPlaneBalance p (CatT ⟨excIndex k q, hv⟩)

@[expose] def InnerPlaneBalanceAt (k : LieFamily) (e : ℕ) : Prop :=
  InnerPlaneBalanceAtP k e fun _ => True

theorem InnerPlaneBalanceAtP.mono {k : LieFamily} {e : ℕ} {R R' : ℕ → Prop}
    (h : InnerPlaneBalanceAtP k e R) (hR : ∀ p, R' p → R p) : InnerPlaneBalanceAtP k e R' :=
  fun q hv p hp hp7 hRp hpq he => h q hv p hp hp7 (hR p hRp) hpq he

theorem InnerPlaneBalanceAt.atP {k : LieFamily} {e : ℕ} (h : InnerPlaneBalanceAt k e)
    (R : ℕ → Prop) : InnerPlaneBalanceAtP k e R :=
  InnerPlaneBalanceAtP.mono h fun _ _ => trivial

theorem InnerPlaneBalanceAtP.or {k : LieFamily} {e : ℕ} {R₁ R₂ : ℕ → Prop}
    (h₁ : InnerPlaneBalanceAtP k e R₁) (h₂ : InnerPlaneBalanceAtP k e R₂) :
    InnerPlaneBalanceAtP k e fun p => R₁ p ∨ R₂ p :=
  fun q hv p hp hp7 hR hpq he => hR.elim (fun h => h₁ q hv p hp hp7 h hpq he)
    fun h => h₂ q hv p hp hp7 h hpq he

theorem dvd_pow_sub_one_of_cast_eq {p a b n : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (h : ((a : ℕ) : ZMod p) = ((b : ℕ) : ZMod p)) (hd : p ∣ a ^ n - 1) : p ∣ b ^ n - 1 := by
  have h1 := (ZMod.natCast_eq_zero_iff (a ^ n - 1) p).2 hd
  rw [Nat.cast_sub (Nat.one_le_pow _ _ ha), Nat.cast_pow, Nat.cast_one, h] at h1
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (Nat.one_le_pow _ _ hb), Nat.cast_pow,
    Nat.cast_one]
  exact h1

theorem dvd_phi12_of_cast_eq {p a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (h : ((a : ℕ) : ZMod p) = ((b : ℕ) : ZMod p)) (hd : p ∣ a ^ 4 - a ^ 2 + 1) :
    p ∣ b ^ 4 - b ^ 2 + 1 := by
  have ha24 : a ^ 2 ≤ a ^ 4 := Nat.pow_le_pow_right ha (by norm_num)
  have hb24 : b ^ 2 ≤ b ^ 4 := Nat.pow_le_pow_right hb (by norm_num)
  have h1 := (ZMod.natCast_eq_zero_iff (a ^ 4 - a ^ 2 + 1) p).2 hd
  rw [Nat.cast_add, Nat.cast_sub ha24, Nat.cast_pow, Nat.cast_pow, Nat.cast_one, h] at h1
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_sub hb24, Nat.cast_pow, Nat.cast_pow,
    Nat.cast_one]
  exact h1

theorem dvd_exponent_of_ringAut {K : Type} [Field K] {ℓ n : ℕ} (hℓ : ℓ.Prime) (hn : 1 ≤ n)
    (hK : Nat.card K = ℓ ^ n) {p : ℕ} (hp : p.Prime) {η : K ≃+* K} (hη1 : η ≠ 1)
    (hηp : η ^ p = 1) : p ∣ n := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, -, -, -, hcard, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality hℓ hn hK
  have h1 : orderOf η = p := orderOf_eq_prime hηp hη1
  have h2 := orderOf_dvd_natCard η
  rwa [h1, hcard] at h2

theorem innerPlaneBalance_of_rankLE1 {K : Type*} [Group K] {p : ℕ} (hp : p.Prime)
    (hinj : Function.Injective (MulAut.conj : K →* MulAut K)) (hr : RankLE1 p K) :
    InnerPlaneBalance p K := fun _ hEin hE hEc _ _ =>
  (false_of_inner_plane_of_rankLE1 hp hinj hr hE hEc hEin).elim

theorem isElemAbelian_zpowers_of_orderOf' {K : Type*} [Group K] {p : ℕ} {g : K}
    (hg : g ^ p = 1) : IsElemAbelian p (Subgroup.zpowers g) := CFSG.Open.isElemAbelian_zpowers hg

theorem outerFields_of_hom {K Q : Type*} [Group K] [Finite K] [Group Q] [IsCyclic Q]
    (Θ : MulAut K →* Q) {p : ℕ} (hp : p.Prime)
    (hinj : Function.Injective (MulAut.conj : K →* MulAut K))
    (hΘ : ∀ x ∈ Θ.ker, x ^ p = 1 → x ∈ innerAut K)
    (h : (∀ F : Subgroup K, IsElemAbelian p F → Nat.card F = 1) ∨
      ∀ x : MulAut K, x ^ p = 1 → x ∉ innerAut K → FieldCoreAt p x) :
    OuterFields p K := by
  intro D hD hcard hDin
  rcases h with hvac | hfc
  · exfalso
    have : Fact p.Prime := ⟨hp⟩
    have : Finite D := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 2 hp.ne_zero)
    let α : D →* Q := Θ.comp D.subtype
    have hle := card_le_mul_card_ker' hp (fun h : D => Subtype.ext (hD.2 h h.2)) α
    rw [hcard] at hle
    have hker : p ≤ Nat.card α.ker := by
      have h2 : p * p ≤ p * Nat.card α.ker := by nlinarith [hle]
      exact Nat.le_of_mul_le_mul_left h2 hp.pos
    have : Finite α.ker := Finite.of_injective _ α.ker.subtype_injective
    have hnt : Nontrivial α.ker := Finite.one_lt_card_iff_nontrivial.1 (lt_of_lt_of_le hp.one_lt hker)
    obtain ⟨⟨d, hdk⟩, hd1⟩ := exists_ne (1 : α.ker)
    have hd1' : d ≠ 1 := fun h => hd1 (Subtype.ext h)
    have hdp : (d : MulAut K) ^ p = 1 := hD.2 d d.2
    obtain ⟨g, hg⟩ := hΘ (d : MulAut K) hdk hdp
    have hgp : g ^ p = 1 := by
      apply hinj
      rw [map_pow, hg, map_one]
      exact hdp
    have hg1 : g ≠ 1 := fun h => hd1' (by
      apply Subtype.ext
      rw [← hg, h, map_one]
      rfl)
    have hord : orderOf g = p := orderOf_eq_prime hgp hg1
    have hcz := hvac _ (isElemAbelian_zpowers_of_orderOf' hgp)
    rw [Nat.card_zpowers, hord] at hcz
    exact hp.one_lt.ne' hcz
  · obtain ⟨x, hxD, hxin⟩ := IsConcreteLE.not_le_iff_exists.1 hDin
    exact ⟨x, hxD, hxin, hfc x (hD.2 x hxD) hxin⟩

theorem elemAbelian_card_eq_one_of_not_dvd {K : Type*} [Group K] [Finite K] {p : ℕ}
    (hp : p.Prime) (h : ¬ p ∣ Nat.card K) :
    ∀ F : Subgroup K, IsElemAbelian p F → Nat.card F = 1 := fun _ hF =>
  elemAbelian_card_eq_one_of_ordProj hp (by
    rw [Nat.factorization_eq_zero_of_not_dvd h, pow_zero]) hF

theorem isLocallyBalancedAbs_two_of_model {S N : Type*} [Group S] [Group N] [Finite N]
    (e : S ≃* N) {p : ℕ} (hp : p.Prime)
    (hinj : Function.Injective (MulAut.conj : N →* MulAut N)) (hin : InnerPlaneBalance p N)
    (hout : OuterFields p N) : IsLocallyBalancedAbs p 2 S :=
  IsLocallyBalancedAbs.of_mulEquiv e (isLocallyBalancedAbs_two_of_planes_and_fields hp hinj hin hout)

end CFSG.HardMathSupport.Timmesfeld.LocalTwo
