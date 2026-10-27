module

public import CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialProductEndModel
public import CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialProductEndBase
public import CFSG.LocalAnalysis.EvenBN.Common.CoprimeQuotient
public import CFSG.Quasithin.Background.F7TwoInvSp4Odd

public section

namespace CFSG.LocalAnalysis.EvenBN.Sp4

namespace BothTrivialProductEnd

open Subgroup
open CFSG.LocalAnalysis.SymplecticFourStandard GomiFusion
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)

namespace Endgame

section Generic

variable {G : Type} [Group G]

theorem mem_sup_decomp {A B : Subgroup G} (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : G}
    (hx : x ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  let P : Subgroup G :=
    { carrier := {x | ∃ a ∈ A, ∃ b ∈ B, x = a * b}
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', mul_mem ha ha', b * b', mul_mem hb hb', ?_⟩
        calc a * b * (a' * b') = a * (b * a') * b' := by group
          _ = a * (a' * b) * b' := by rw [hAB a' ha' b hb]
          _ = a * a' * (b * b') := by group
      one_mem' := ⟨1, one_mem _, 1, one_mem _, by simp⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, inv_mem ha, b⁻¹, inv_mem hb, ?_⟩
        rw [mul_inv_rev, ← hAB a⁻¹ (inv_mem ha) b⁻¹ (inv_mem hb)] }
  have hle : A ⊔ B ≤ P := sup_le (fun a ha => ⟨a, ha, 1, one_mem _, by simp⟩)
    (fun b hb => ⟨1, one_mem _, b, hb, by simp⟩)
  exact hle hx

theorem sq_eq_one_of_mem_sup {A B : Subgroup G} (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hA : ∀ a ∈ A, a * a = 1) (hB : ∀ b ∈ B, b * b = 1) {x : G} (hx : x ∈ A ⊔ B) :
    x * x = 1 := by
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_decomp hAB hx
  calc a * b * (a * b) = a * (b * a) * b := by group
    _ = a * (a * b) * b := by rw [← hAB a ha b hb]
    _ = (a * a) * (b * b) := by group
    _ = 1 := by rw [hA a ha, hB b hb, one_mul]

theorem sq_eq_one_of_mem_zpowers {e : G} (he : e * e = 1) {y : G} (hy : y ∈ zpowers e) :
    y * y = 1 := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
  rw [← zpow_add, ← two_mul, zpow_mul, zpow_two, he, one_zpow]

theorem le_normalizer_of_forall_commute [Finite G] {A B : Subgroup G}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : B ≤ normalizer (A : Set G) := fun b hb =>
  mem_normalizer_fintype fun a ha => by
    rw [← hAB a ha b hb, mul_inv_cancel_right]
    exact ha

theorem card_sup_of_commute_of_inf_eq_bot [Finite G] {A B : Subgroup G}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hinf : A ⊓ B = ⊥) :
    Nat.card (A ⊔ B : Subgroup G) = Nat.card A * Nat.card B := by
  have h := Common.card_sup_mul_card_inf_eq (le_normalizer_of_forall_commute hAB)
  rwa [hinf, Subgroup.card_bot, mul_one] at h

end Generic

section Lift

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isPGroup_zpowers_of_mul_self {x : G} (hx2 : x * x = 1) : IsPGroup 2 (zpowers x) := by
  have hdvd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq, hx2])
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h2
  · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h1, pow_zero])
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h2, pow_one])

omit [Finite G] in
theorem eq_one_of_mem_of_isPGroup_of_odd {P Z : Subgroup G} (hP : IsPGroup 2 P)
    (hZ : Odd (Nat.card Z)) {y : G} (hyP : y ∈ P) (hyZ : y ∈ Z) : y = 1 := by
  obtain ⟨k, hk⟩ := hP ⟨y, hyP⟩
  have h1 : orderOf y ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (by
    simpa using congrArg Subtype.val hk)
  have h2 : orderOf y ∣ Nat.card Z := Subgroup.orderOf_dvd_natCard Z hyZ
  have hcop : Nat.Coprime (2 ^ k) (Nat.card Z) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hZ)
  exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd (hcop.coprime_dvd_left h1) h2)

theorem exists_exp_two_le_centralizer_of_odd {H Z : Subgroup G} (hZodd : Odd (Nat.card Z)) {m : ℕ}
    (hcard : Nat.card H = Nat.card Z * 2 ^ m) (hsq : ∀ a ∈ H, a * a ∈ Z) {x : G}
    (hx2 : x * x = 1) (hxH : x ∈ normalizer (H : Set G))
    (hxZ : ∀ a ∈ H, x * a * x⁻¹ * a⁻¹ ∈ Z) :
    ∃ E : Subgroup G, E ≤ H ∧ E ≤ centralizer ({x} : Set G) ∧ (∀ y ∈ E, y * y = 1) ∧
      Nat.card E = 2 ^ m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K : Subgroup G := H ⊔ zpowers x with hK
  have hHK : H ≤ K := le_sup_left
  have hxK : x ∈ K := mem_sup_right (mem_zpowers x)
  have hKN : K ≤ normalizer (H : Set G) := sup_le le_normalizer ((zpowers_le).2 hxH)
  obtain ⟨Q, hQ⟩ := ((isPGroup_zpowers_of_mul_self hx2).comap_subtype (K := K)).exists_le_sylow
  set R : Subgroup G := (Q : Subgroup K).map K.subtype with hR
  have hRsyl : CFSG.ABGLocalTools.IsSylowOf 2 R K := ⟨Q, rfl⟩
  have hxR : x ∈ R := ⟨⟨x, hxK⟩, hQ (mem_subgroupOf.2 (mem_zpowers x)), rfl⟩
  set P : Subgroup G := R ⊓ H with hP
  have hPsyl : CFSG.ABGLocalTools.IsSylowOf 2 P H := hRsyl.inf_of_le_normalizer hHK hKN
  have hPcard : Nat.card P = 2 ^ m := by
    rw [hPsyl.card_eq, hcard, Nat.factorization_mul (by have := hZodd.pos; omega)
      (by positivity), Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd
      (fun h2 => (Nat.not_even_iff_odd.2 hZodd) (even_iff_two_dvd.2 h2)),
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same, zero_add]
  have hPZ : ∀ y ∈ P, y ∈ Z → y = 1 := fun y hyP hyZ =>
    eq_one_of_mem_of_isPGroup_of_odd hPsyl.isPGroup hZodd hyP hyZ
  have hxP : ∀ p ∈ P, x * p * x⁻¹ ∈ P := fun p hp =>
    mem_inf.2 ⟨mul_mem (mul_mem hxR (mem_inf.1 hp).1) (inv_mem hxR),
      (mem_normalizer_iff.1 hxH p).1 (mem_inf.1 hp).2⟩
  refine ⟨P, inf_le_right, fun p hp => ?_, fun a ha =>
    hPZ _ (mul_mem ha ha) (hsq a (mem_inf.1 ha).2), hPcard⟩
  have h1 : x * p * x⁻¹ * p⁻¹ = 1 :=
    hPZ _ (mul_mem (hxP p hp) (inv_mem hp)) (hxZ p (mem_inf.1 hp).2)
  rw [mem_centralizer_singleton_iff]
  calc p * x = (x * p * x⁻¹ * p⁻¹)⁻¹ * (x * p) := by group
    _ = x * p := by rw [h1, inv_one, one_mul]

end Lift

section Center

variable {G : Type} [Group G]

@[expose] def zc (X : Subgroup G) : Subgroup G := (center X).map X.subtype

theorem zc_le (X : Subgroup G) : zc X ≤ X := Subgroup.map_subtype_le _

theorem card_zc (X : Subgroup G) : Nat.card (zc X) = Nat.card (center X) :=
  Subgroup.card_map_of_injective X.subtype_injective

theorem mem_zc_of_mem_center {X : Subgroup G} {a : X} (ha : a ∈ center X) : (a : G) ∈ zc X :=
  ⟨a, ha, rfl⟩

theorem mem_center_of_mem_zc {X : Subgroup G} {a : X} (ha : (a : G) ∈ zc X) : a ∈ center X := by
  obtain ⟨b, hb, e⟩ := ha
  have : b = a := Subtype.ext e
  rwa [← this]

theorem mem_zc_of_commute {X : Subgroup G} {y : G} (hy : y ∈ X)
    (hc : ∀ a ∈ X, a * y = y * a) : y ∈ zc X :=
  mem_zc_of_mem_center (a := ⟨y, hy⟩) (mem_center_iff.2 fun g => Subtype.ext (hc g g.2))

theorem eq_one_of_sq_eq_one_of_mem_zc {X : Subgroup G} (hZ : Odd (Nat.card (center X))) {y : G}
    (hy2 : y * y = 1) (hy : y ∈ zc X) : y = 1 :=
  eq_one_of_mem_of_isPGroup_of_odd (isPGroup_zpowers_of_mul_self hy2)
    (by rw [card_zc]; exact hZ) (mem_zpowers y) hy

end Center

section Residual

variable {H H' : Type} [Group H] [Group H']

theorem exists_derivedSeries_succ_eq_of_finite [Finite H] :
    ∃ N : ℕ, derivedSeries H (N + 1) = derivedSeries H N := by
  by_contra h
  push Not at h
  have hlt : ∀ n, Nat.card (derivedSeries H (n + 1)) < Nat.card (derivedSeries H n) := by
    intro n
    have hle : derivedSeries H (n + 1) ≤ derivedSeries H n := by
      rw [derivedSeries_succ]
      exact Subgroup.commutator_le_left _ _
    exact Subgroup.card_lt_of_lt (lt_of_le_of_ne hle (h n))
  have hbound : ∀ n, Nat.card (derivedSeries H n) + n ≤ Nat.card H := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have := hlt n
      omega
  have h1 := hbound (Nat.card H + 1)
  have h2 : 0 < Nat.card (derivedSeries H (Nat.card H + 1)) := Nat.card_pos
  omega

theorem commutator_residual [Finite H] : ⁅residual H, residual H⁆ = residual H := by
  obtain ⟨N, hN⟩ := exists_derivedSeries_succ_eq_of_finite (H := H)
  rw [residual_eq_of_stable hN, ← derivedSeries_succ, hN]

theorem map_residual_eq [Finite H] (f : H →* H') (hf : Function.Surjective f) :
    (residual H).map f = residual H' := by
  obtain ⟨N, hN⟩ := exists_derivedSeries_succ_eq_of_finite (H := H)
  have hN' : derivedSeries H' (N + 1) = derivedSeries H' N := by
    rw [← map_derivedSeries_eq hf, ← map_derivedSeries_eq hf, hN]
  rw [residual_eq_of_stable hN, residual_eq_of_stable hN', map_derivedSeries_eq hf]

theorem card_eq_card_map_mul_card_inf_ker (f : H →* H') (S : Subgroup H) :
    Nat.card S = Nat.card (S.map f) * Nat.card (f.ker ⊓ S : Subgroup H) := by
  rw [← Subgroup.relIndex_ker, Subgroup.relIndex_mul_card]

end Residual

section Fixed

variable {G : Type} [Group G]

theorem exists_mem_fixed_mul {Z : Subgroup G} (hZ : Odd (Nat.card Z)) {x : G} (hx2 : x * x = 1)
    {a : G} (hz : a⁻¹ * (x * a * x⁻¹) ∈ Z) : ∃ w ∈ Z, x * (a * w) * x⁻¹ = a * w := by
  set z := a⁻¹ * (x * a * x⁻¹) with hzdef
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hxz : x * z * x⁻¹ = z⁻¹ := by
    rw [hzdef, hxinv]
    calc x * (a⁻¹ * (x * a * x)) * x = x * a⁻¹ * x * a * (x * x) := by group
      _ = x * a⁻¹ * x * a := by rw [hx2, mul_one]
      _ = (a⁻¹ * (x * a * x))⁻¹ := by
        have : (a⁻¹ * (x * a * x))⁻¹ = x⁻¹ * a⁻¹ * x⁻¹ * a := by group
        rw [this, hxinv]
  obtain ⟨k, hk⟩ := hZ
  have hzN : z ^ Nat.card Z = 1 := by
    have := pow_card_eq_one' (G := Z) (x := ⟨z, hz⟩)
    exact congrArg Subtype.val this
  have hww : z ^ (k + 1) * z ^ (k + 1) = z := by
    rw [← pow_add, show k + 1 + (k + 1) = Nat.card Z + 1 by omega, pow_succ, hzN, one_mul]
  have hxw : x * z ^ (k + 1) * x⁻¹ = (z ^ (k + 1))⁻¹ := by
    rw [← conj_pow, hxz, inv_pow]
  have haz : x * a * x⁻¹ = a * z := by rw [hzdef]; group
  refine ⟨z ^ (k + 1), pow_mem hz _, ?_⟩
  calc x * (a * z ^ (k + 1)) * x⁻¹ = (x * a * x⁻¹) * (x * z ^ (k + 1) * x⁻¹) := by group
    _ = a * z * (z ^ (k + 1))⁻¹ := by rw [haz, hxw]
    _ = a * (z ^ (k + 1) * z ^ (k + 1)) * (z ^ (k + 1))⁻¹ := by rw [hww]
    _ = a * z ^ (k + 1) := by group

end Fixed

section Cover

variable {G : Type} [Group G] [Finite G]

@[expose] def quotientCenterConj {X : Subgroup G} (x : normalizer (X : Set G)) :
    MulAut (X ⧸ center X) :=
  QuotientGroup.congr (center X) (center X) (X.normalizerMonoidHom x)
    (characteristic_iff_map_eq.1 inferInstance _)

theorem quotientCenterConj_mk {X : Subgroup G} (x : normalizer (X : Set G)) (a : X) :
    quotientCenterConj x (a : X ⧸ center X) =
      ((X.normalizerMonoidHom x a : X) : X ⧸ center X) :=
  rfl

theorem normalizerMonoidHom_coe {X : Subgroup G} {x : G} (hxX : x ∈ normalizer (X : Set G))
    (a : X) : ((X.normalizerMonoidHom ⟨x, hxX⟩ a : X) : G) = x * a * x⁻¹ := rfl

theorem quotientCenterConj_mul_self {X : Subgroup G} {x : G} (hxX : x ∈ normalizer (X : Set G))
    (hx2 : x * x = 1) :
    quotientCenterConj (⟨x, hxX⟩ : normalizer (X : Set G)) *
      quotientCenterConj (⟨x, hxX⟩ : normalizer (X : Set G)) = 1 := by
  refine MulEquiv.ext fun q => ?_
  induction q using QuotientGroup.induction_on with
  | H a =>
    rw [MulAut.mul_apply, quotientCenterConj_mk, quotientCenterConj_mk, MulAut.one_apply]
    congr 1
    apply Subtype.ext
    rw [normalizerMonoidHom_coe, normalizerMonoidHom_coe]
    calc x * (x * a * x⁻¹) * x⁻¹ = (x * x) * a * (x * x)⁻¹ := by group
      _ = a := by rw [hx2, inv_one, one_mul, mul_one]

theorem exists_exp_two_le_centralizer_of_fixed {X : Subgroup G}
    (hZ : Odd (Nat.card (center X))) {x : G} (hxX : x ∈ normalizer (X : Set G)) (hx2 : x * x = 1)
    (E₀ : Subgroup (X ⧸ center X))
    (hfix : ∀ b ∈ E₀, quotientCenterConj (⟨x, hxX⟩ : normalizer (X : Set G)) b = b)
    (hsq : ∀ b ∈ E₀, b * b = 1) {m : ℕ} (hcard : Nat.card E₀ = 2 ^ m) :
    ∃ E : Subgroup G, E ≤ X ∧ E ≤ centralizer ({x} : Set G) ∧ (∀ y ∈ E, y * y = 1) ∧
      Nat.card E = 2 ^ m := by
  set α := quotientCenterConj (⟨x, hxX⟩ : normalizer (X : Set G)) with hαdef
  have hconj : ∀ a : X, ((X.normalizerMonoidHom ⟨x, hxX⟩ a : X) : G) = x * a * x⁻¹ :=
    normalizerMonoidHom_coe hxX
  set π : X →* X ⧸ center X := QuotientGroup.mk' (center X) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : ∀ a : X, π a = 1 ↔ a ∈ center X := fun a => QuotientGroup.eq_one_iff a
  set H : Subgroup G := (E₀.comap π).map X.subtype with hH
  set Z : Subgroup G := (center X).map X.subtype with hZdef
  have hmemH : ∀ a : X, (a : G) ∈ H ↔ π a ∈ E₀ := fun a =>
    ⟨fun ⟨b, hb, e⟩ => (Subtype.ext e : b = a) ▸ hb, fun ha => ⟨a, ha, rfl⟩⟩
  have hmemZ : ∀ a : X, (a : G) ∈ Z ↔ a ∈ center X := fun a =>
    ⟨fun ⟨b, hb, e⟩ => (Subtype.ext e : b = a) ▸ hb, fun ha => ⟨a, ha, rfl⟩⟩
  have hHX : H ≤ X := map_subtype_le _
  have hlift : ∀ y ∈ H, ∃ a : X, (a : G) = y ∧ π a ∈ E₀ := by
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨a, rfl, ha⟩
  have hcardH : Nat.card H = Nat.card Z * 2 ^ m := by
    rw [hH, hZdef, card_map_of_injective X.subtype_injective,
      card_map_of_injective X.subtype_injective]
    have h1 := Subgroup.card_mul_index (E₀.comap π)
    have h2 := Subgroup.card_mul_index E₀
    have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup (center X)
    rw [index_comap_of_surjective _ hπs] at h1
    have hidx : 0 < E₀.index := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
    have e : Nat.card (E₀.comap π) * E₀.index = Nat.card (center X) * 2 ^ m * E₀.index := by
      rw [h1, h3, ← h2, hcard]
      ring
    exact Nat.eq_of_mul_eq_mul_right hidx e
  obtain ⟨E, hEH, hEx, hEsq, hEc⟩ := exists_exp_two_le_centralizer_of_odd
    (H := H) (Z := Z)
    (by rw [hZdef, card_map_of_injective X.subtype_injective]; exact hZ) hcardH
    (fun y hy => by
      obtain ⟨a, rfl, ha⟩ := hlift y hy
      have e : (a : G) * a = ((a * a : X) : G) := rfl
      rw [e, hmemZ, ← hker, map_mul]
      exact hsq _ ha)
    hx2
    (mem_normalizer_fintype fun y hy => by
      obtain ⟨a, rfl, ha⟩ := hlift y hy
      rw [SetLike.mem_coe, ← hconj, hmemH]
      have := hfix _ ha
      rw [hπ, QuotientGroup.mk'_apply, hαdef, quotientCenterConj_mk] at this
      rw [hπ, QuotientGroup.mk'_apply, this]
      exact ha)
    (fun y hy => by
      obtain ⟨a, rfl, ha⟩ := hlift y hy
      have e : x * (a : G) * x⁻¹ * (a : G)⁻¹ =
          ((X.normalizerMonoidHom ⟨x, hxX⟩ a * a⁻¹ : X) : G) := by
        rw [Subgroup.coe_mul, hconj, Subgroup.coe_inv]
      have hfa := hfix _ ha
      rw [hπ, QuotientGroup.mk'_apply, hαdef, quotientCenterConj_mk] at hfa
      rw [e, hmemZ, ← hker, map_mul, map_inv, hπ, QuotientGroup.mk'_apply,
        QuotientGroup.mk'_apply, hfa, mul_inv_cancel])
  exact ⟨E, hEH.trans hHX, hEx, hEsq, hEc⟩

end Cover

section AntiSp

variable {K : Type} [Field K] [CharP K 2] [Finite K]

theorem exists_exp_two_fixed_of_inner {n : ℕ} (hK : Nat.card K = 2 ^ n) {θ : MulAut (antiSp K)}
    (hθ : θ * θ = 1) (hθi : θ ∈ inner (antiSp K)) :
    ∃ E : Subgroup (antiSp K), (∀ y ∈ E, θ y = y) ∧ (∀ y ∈ E, y * y = 1) ∧
      Nat.card E = 2 ^ (3 * n) := by
  letI : Fintype K := Fintype.ofFinite K
  obtain ⟨g, rfl⟩ := MonoidHom.mem_range.1 hθi
  have hgg : g * g = 1 := by
    apply CFSG.QuasithinUnique.Setup.X7b.conj_injective (K := K)
    rw [map_mul, hθ, map_one]
  obtain ⟨c, hc⟩ := elementary_le_conj_antiUnipotent (zpowers g)
    (fun y hy => sq_eq_one_of_mem_zpowers hgg hy)
  have hu : c⁻¹ * g * c ∈ antiUnipotent K := hc g (mem_zpowers g)
  have hu2 : (c⁻¹ * g * c) * (c⁻¹ * g * c) = 1 := by
    calc (c⁻¹ * g * c) * (c⁻¹ * g * c) = c⁻¹ * (g * g) * c := by group
      _ = 1 := by rw [hgg]; group
  have hq3 : Nat.card K ^ 3 = 2 ^ (3 * n) := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨-, h1, h2, -⟩ := card_radicals (K := K)
  have key : ∀ R : Subgroup (antiSp K), (∀ r ∈ R, (c⁻¹ * g * c) * r = r * (c⁻¹ * g * c)) →
      (∀ r ∈ R, r * r = 1) → Nat.card R = 2 ^ (3 * n) →
      ∃ E : Subgroup (antiSp K), (∀ y ∈ E, (MulAut.conj g) y = y) ∧ (∀ y ∈ E, y * y = 1) ∧
        Nat.card E = 2 ^ (3 * n) := by
    intro R hcomm hsq hcard
    refine ⟨R.map (MulAut.conj c).toMonoidHom, ?_, ?_, ?_⟩
    · rintro _ ⟨r, hr, rfl⟩
      have e := hcomm r hr
      show g * (c * r * c⁻¹) * g⁻¹ = c * r * c⁻¹
      calc g * (c * r * c⁻¹) * g⁻¹ = c * ((c⁻¹ * g * c) * r * (c⁻¹ * g * c)⁻¹) * c⁻¹ := by group
        _ = c * r * c⁻¹ := by rw [e]; group
    · rintro _ ⟨r, hr, rfl⟩
      show c * r * c⁻¹ * (c * r * c⁻¹) = 1
      calc c * r * c⁻¹ * (c * r * c⁻¹) = c * (r * r) * c⁻¹ := by group
        _ = 1 := by rw [hsq r hr]; group
    · rw [Subgroup.card_map_of_injective (MulAut.conj c).injective, hcard]
  rcases (mul_self_eq_one_iff hu).1 hu2 with h | h
  · exact key (radA1 K) (fun r hr => radA1_comm h hr) (fun r hr => mul_self_of_mem_radA1 hr)
      (h1.trans hq3)
  · exact key (radA2 K) (fun r hr => radA2_comm h hr) (fun r hr => mul_self_of_mem_radA2 hr)
      (h2.trans hq3)

end AntiSp

section Dichotomy

variable {G : Type} [Group G] [Finite G] {K : Type} [Field K] [CharP K 2] [Finite K]

@[expose] def actAut {X : Subgroup G} (ψ : X ⧸ center X ≃* antiSp K) {x : G}
    (hxX : x ∈ normalizer (X : Set G)) : MulAut (antiSp K) :=
  MulAut.congr ψ (quotientCenterConj (⟨x, hxX⟩ : normalizer (X : Set G)))

theorem actAut_apply {X : Subgroup G} (ψ : X ⧸ center X ≃* antiSp K) {x : G}
    (hxX : x ∈ normalizer (X : Set G)) (y : antiSp K) :
    actAut ψ hxX y =
      ψ (quotientCenterConj (⟨x, hxX⟩ : normalizer (X : Set G)) (ψ.symm y)) := rfl

theorem actAut_mul_self {X : Subgroup G} (ψ : X ⧸ center X ≃* antiSp K) {x : G}
    (hxX : x ∈ normalizer (X : Set G)) (hx2 : x * x = 1) : actAut ψ hxX * actAut ψ hxX = 1 := by
  rw [actAut, ← map_mul, quotientCenterConj_mul_self hxX hx2, map_one]

theorem actAut_mk {X : Subgroup G} (ψ : X ⧸ center X ≃* antiSp K) {x : G}
    (hxX : x ∈ normalizer (X : Set G)) (a : X) :
    actAut ψ hxX (ψ (a : X ⧸ center X)) =
      ψ ((X.normalizerMonoidHom ⟨x, hxX⟩ a : X) : X ⧸ center X) := by
  rw [actAut_apply, MulEquiv.symm_apply_apply, quotientCenterConj_mk]

theorem inner_or_outer {n : ℕ} (hn : 2 ≤ n)
    (hK : Nat.card K = 2 ^ n) {X : Subgroup G} (hZ : Odd (Nat.card (center X)))
    (ψ : X ⧸ center X ≃* antiSp K) {x : G} (hxX : x ∈ normalizer (X : Set G))
    (hx2 : x * x = 1) :
    (∃ E : Subgroup G, E ≤ X ∧ E ≤ centralizer ({x} : Set G) ∧ (∀ y ∈ E, y * y = 1) ∧
        Nat.card E = 2 ^ (3 * n)) ∨
    ((∀ a ∈ X, ∀ c ∈ centralizer (X : Set G), x ≠ a * c) ∧
      ∃ D : Subgroup G, D ≤ X ∧ D ≤ centralizer ({x} : Set G) ∧ ⁅D, D⁆ = D ∧
        (∃ e ∈ D, e ≠ 1 ∧ e * e = 1) ∧
        Nat.card D = Nat.card (D ⊓ zc X : Subgroup G) * outerResidualOrder n) := by
  classical
  have hθ := actAut_mul_self ψ hxX hx2
  by_cases hθi : actAut ψ hxX ∈ inner (antiSp K)
  · left
    obtain ⟨E₀', hfix', hsq', hcard'⟩ := exists_exp_two_fixed_of_inner hK hθ hθi
    refine exists_exp_two_le_centralizer_of_fixed hZ hxX hx2 (E₀'.map ψ.symm.toMonoidHom) ?_ ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      have h1 := hfix' y hy
      rw [actAut_apply] at h1
      show quotientCenterConj _ (ψ.symm y) = ψ.symm y
      apply ψ.injective
      rw [h1, MulEquiv.apply_symm_apply]
    · rintro _ ⟨y, hy, rfl⟩
      show ψ.symm y * ψ.symm y = 1
      rw [← map_mul, hsq' y hy, map_one]
    · rw [Subgroup.card_map_of_injective ψ.symm.injective]
      exact hcard'
  · right
    refine ⟨?_, ?_⟩
    · intro a ha c hc hxac
      apply hθi
      have hα : quotientCenterConj (⟨x, hxX⟩ : normalizer (X : Set G)) =
          MulAut.conj (((⟨a, ha⟩ : X) : X ⧸ center X)) := by
        refine MulEquiv.ext fun q => ?_
        induction q using QuotientGroup.induction_on with
        | H b =>
          rw [quotientCenterConj_mk, MulAut.conj_apply, ← QuotientGroup.mk_inv,
            ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
          congr 1
          apply Subtype.ext
          rw [normalizerMonoidHom_coe]
          have hcb : (b : G) * c = c * b := mem_centralizer_iff.1 hc b b.2
          calc x * (b : G) * x⁻¹ = a * (c * b * c⁻¹) * a⁻¹ := by rw [hxac]; group
            _ = a * b * a⁻¹ := by rw [← hcb]; group
      show MulAut.congr ψ (quotientCenterConj (⟨x, hxX⟩ : normalizer (X : Set G))) ∈ _
      rw [hα, CFSG.ComponentClassification.OuterAutomorphisms.congr_conj]
      exact ⟨_, rfl⟩
    · set F : Subgroup G := X ⊓ centralizer ({x} : Set G) with hF
      have hFX : F ≤ X := inf_le_left
      let p : F →* antiSp K :=
        ψ.toMonoidHom.comp ((QuotientGroup.mk' (center X)).comp (Subgroup.inclusion hFX))
      have hpapply : ∀ f : F, p f = ψ ((⟨(f : G), hFX f.2⟩ : X) : X ⧸ center X) := fun f => rfl
      have hfx : ∀ f : F, x * (f : G) * x⁻¹ = f := by
        intro f
        have h := mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 f.2).2
        rw [← h]
        group
      have hpfix : ∀ f : F, p f ∈ fixedSubgroup (actAut ψ hxX) := by
        intro f
        rw [mem_fixedSubgroup, hpapply, actAut_mk]
        congr 2
        apply Subtype.ext
        rw [normalizerMonoidHom_coe]
        exact hfx f
      have hpsurj : ∀ y ∈ fixedSubgroup (actAut ψ hxX), ∃ f : F, p f = y := by
        intro y hy
        obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (ψ.symm y)
        have hfixa : quotientCenterConj (⟨x, hxX⟩ : normalizer (X : Set G))
            (a : X ⧸ center X) = (a : X ⧸ center X) := by
          rw [ha]
          have h1 : actAut ψ hxX y = y := mem_fixedSubgroup.1 hy
          rw [actAut_apply] at h1
          apply ψ.injective
          rw [h1, MulEquiv.apply_symm_apply]
        rw [quotientCenterConj_mk] at hfixa
        have hz := QuotientGroup.eq.1 hfixa.symm
        have hz' : (a : G)⁻¹ * (x * (a : G) * x⁻¹) ∈ zc X := by
          have := mem_zc_of_mem_center hz
          rw [Subgroup.coe_mul, Subgroup.coe_inv, normalizerMonoidHom_coe] at this
          exact this
        obtain ⟨w, hw, hxw⟩ :=
          exists_mem_fixed_mul (Z := zc X) (by rw [card_zc]; exact hZ) hx2 hz'
        have hwX : w ∈ X := zc_le X hw
        have hmem : (a : G) * w ∈ F := by
          refine Subgroup.mem_inf.2 ⟨mul_mem a.2 hwX, mem_centralizer_singleton_iff.2 ?_⟩
          calc (a : G) * w * x = x * ((a : G) * w) * x⁻¹ * x := by rw [hxw]
            _ = x * ((a : G) * w) := by group
        refine ⟨⟨(a : G) * w, hmem⟩, ?_⟩
        rw [hpapply, ← MulEquiv.apply_symm_apply ψ y, ← ha]
        congr 1
        rw [QuotientGroup.eq]
        have hcen : (⟨w, hwX⟩ : X) ∈ center X := mem_center_of_mem_zc hw
        convert Subgroup.inv_mem _ hcen using 1
        apply Subtype.ext
        simp
      have hpker : ∀ f : F, p f = 1 ↔ (f : G) ∈ zc X := by
        intro f
        rw [hpapply, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
        exact ⟨fun h => mem_zc_of_mem_center h, fun h => mem_center_of_mem_zc h⟩
      let q : F →* fixedSubgroup (actAut ψ hxX) := p.codRestrict _ hpfix
      have hq : Function.Surjective q := by
        rintro ⟨y, hy⟩
        obtain ⟨f, hf⟩ := hpsurj y hy
        exact ⟨f, Subtype.ext hf⟩
      have hqker : ∀ f : F, q f = 1 ↔ (f : G) ∈ zc X := fun f => by
        rw [← hpker]
        exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
      set R : Subgroup F := residual F with hR
      set D : Subgroup G := R.map F.subtype with hD
      have hRq : R.map q = residual (fixedSubgroup (actAut ψ hxX)) := map_residual_eq q hq
      have hcardR := card_eq_card_map_mul_card_inf_ker q R
      have hDF : D ≤ F := Subgroup.map_subtype_le _
      have hDcard : Nat.card D = Nat.card R := Subgroup.card_map_of_injective F.subtype_injective
      have hinf : (q.ker ⊓ R).map F.subtype = D ⊓ zc X := by
        ext y
        constructor
        · rintro ⟨f, hf, rfl⟩
          exact ⟨⟨f, hf.2, rfl⟩, (hqker f).1 hf.1⟩
        · rintro ⟨⟨f, hfR, rfl⟩, hz⟩
          exact ⟨f, ⟨(hqker f).2 hz, hfR⟩, rfl⟩
      have hinfcard : Nat.card (D ⊓ zc X : Subgroup G) = Nat.card (q.ker ⊓ R : Subgroup F) := by
        rw [← hinf]
        exact Subgroup.card_map_of_injective F.subtype_injective
      have hres : Nat.card (residual (fixedSubgroup (actAut ψ hxX))) = outerResidualOrder n :=
        card_residual_fixedSubgroup hn hK _ hθ hθi
      have hev : Even (outerResidualOrder n) := by
        rw [← hres]
        exact ((even_symplectic_four_outer_involution_rank_and_perfect_residual hn hK).2.2.2 _ hθ
          hθi).2.2
      have hDc : Nat.card D = Nat.card (D ⊓ zc X : Subgroup G) * outerResidualOrder n := by
        rw [hDcard, hcardR, hRq, hres, hinfcard, mul_comm]
      have hDeven : 2 ∣ Nat.card D := by
        rw [hDc]
        exact (even_iff_two_dvd.1 (hev.mul_left _))
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨e, he⟩ := exists_prime_orderOf_dvd_card' (G := D) 2 hDeven
      have he' : orderOf (e : G) = 2 := by rw [Subgroup.orderOf_coe, he]
      refine ⟨D, hDF.trans inf_le_left, hDF.trans inf_le_right, ?_, ⟨e, e.2, ?_, ?_⟩, hDc⟩
      · rw [hD, ← Subgroup.map_commutator, hR, commutator_residual]
      · intro h1
        rw [h1, orderOf_one] at he'
        exact absurd he' (by norm_num)
      · rw [← sq, ← he', pow_orderOf_eq_one]

end Dichotomy

section Contradiction

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  [Finite K] {n : ℕ} {φ : L ≃* antiSp K} {t : G}

theorem false_of_inner_inner (hS : Setup L K n φ (zpowers t) t)
    {X₁ X₂ : Subgroup G} (hcomm : ∀ a ∈ X₁, ∀ b ∈ X₂, a * b = b * a)
    (hZ₁ : Odd (Nat.card (center X₁))) {E₁ E₂ : Subgroup G} (hE₁X : E₁ ≤ X₁)
    (hE₁t : E₁ ≤ centralizer ({t} : Set G)) (hE₁sq : ∀ y ∈ E₁, y * y = 1)
    (hE₁c : Nat.card E₁ = 2 ^ (3 * n)) (hE₂X : E₂ ≤ X₂)
    (hE₂t : E₂ ≤ centralizer ({t} : Set G)) (hE₂sq : ∀ y ∈ E₂, y * y = 1)
    (hE₂c : Nat.card E₂ = 2 ^ (3 * n)) : False := by
  have hc12 : ∀ a ∈ E₁, ∀ b ∈ E₂, a * b = b * a := fun a ha b hb =>
    hcomm a (hE₁X ha) b (hE₂X hb)
  have hinf : E₁ ⊓ E₂ = ⊥ := by
    refine eq_bot_iff.2 fun y hy => ?_
    have hyz : y ∈ zc X₁ :=
      mem_zc_of_commute (hE₁X hy.1) fun a ha => hcomm a ha y (hE₂X hy.2)
    exact mem_bot.2 (eq_one_of_sq_eq_one_of_mem_zc hZ₁ (hE₁sq y hy.1) hyz)
  have hcard := card_sup_of_commute_of_inf_eq_bot hc12 hinf
  have hle := card_le_of_le_centralizer hS (sup_le hE₁t hE₂t)
    (fun y hy => sq_eq_one_of_mem_sup hc12 hE₁sq hE₂sq hy)
  rw [hcard, hE₁c, hE₂c] at hle
  have hc3 : (2 ^ n) ^ 3 = 2 ^ (3 * n) := by rw [← pow_mul, mul_comm]
  rw [hc3] at hle
  have h4 : 4 ≤ 2 ^ (3 * n) := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (3 * n) := Nat.pow_le_pow_right (by norm_num) (by have := hS.two_le; omega)
  nlinarith

theorem false_of_inner_outer (hS : Setup L K n φ (zpowers t) t)
    {X₁ X₂ : Subgroup G} (hcomm : ∀ a ∈ X₁, ∀ b ∈ X₂, a * b = b * a)
    (hZ₁ : Odd (Nat.card (center X₁))) {E : Subgroup G} (hEX : E ≤ X₁)
    (hEt : E ≤ centralizer ({t} : Set G)) (hEsq : ∀ y ∈ E, y * y = 1)
    (hEc : Nat.card E = 2 ^ (3 * n))
    (hout : ∀ a ∈ X₂, ∀ c ∈ centralizer (X₂ : Set G), t ≠ a * c) {e : G} (he : e ∈ X₂)
    (het : e ∈ centralizer ({t} : Set G)) (he1 : e ≠ 1) (he2 : e * e = 1) : False := by
  have htt := hS.t_mul_t
  have hEe : E ≤ centralizer ({e} : Set G) := fun y hy =>
    mem_centralizer_singleton_iff.2 (hcomm y (hEX hy) e he)
  have heE : e ∉ E := by
    intro heE
    have hez : e ∈ zc X₁ := mem_zc_of_commute (hEX heE) fun a ha => hcomm a ha e he
    exact he1 (eq_one_of_sq_eq_one_of_mem_zc hZ₁ he2 hez)
  have hc1 := Common.SwapUnique.card_sup_zpowers_of_le_centralizer he2 hEe heE
  have hecomm : ∀ y ∈ E, ∀ z ∈ zpowers e, y * z = z * y := by
    intro y hy z hz
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hz
    have hye : Commute y e := mem_centralizer_singleton_iff.1 (hEe hy)
    exact (hye.zpow_right k).eq
  have hE₁t : E ⊔ zpowers e ≤ centralizer ({t} : Set G) := sup_le hEt (zpowers_le.2 het)
  have htE₁ : t ∉ E ⊔ zpowers e := by
    intro ht
    obtain ⟨y, hy, z, hz, htyz⟩ := mem_sup_decomp hecomm ht
    have hzX₂ : z ∈ X₂ := (zpowers_le.2 he) hz
    have hyc : y ∈ centralizer (X₂ : Set G) :=
      mem_centralizer_iff.2 fun b hb => (hcomm y (hEX hy) b hb).symm
    exact hout z hzX₂ y hyc (by rw [htyz, hecomm y hy z hz])
  have hc2 := Common.SwapUnique.card_sup_zpowers_of_le_centralizer htt hE₁t htE₁
  have hcomm₂ : ∀ y ∈ E ⊔ zpowers e, ∀ z ∈ zpowers t, y * z = z * y := by
    intro y hy z hz
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hz
    have hyt : Commute y t := mem_centralizer_singleton_iff.1 (hE₁t hy)
    exact (hyt.zpow_right k).eq
  have hsq₁ : ∀ y ∈ E ⊔ zpowers e, y * y = 1 := fun y hy =>
    sq_eq_one_of_mem_sup hecomm hEsq (fun z hz => sq_eq_one_of_mem_zpowers he2 hz) hy
  have hle := card_le_of_le_centralizer hS
    (sup_le hE₁t (zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl)) :
      (E ⊔ zpowers e) ⊔ zpowers t ≤ centralizer ({t} : Set G))
    (fun y hy => sq_eq_one_of_mem_sup hcomm₂ hsq₁
      (fun z hz => sq_eq_one_of_mem_zpowers htt hz) hy)
  rw [hc2, hc1, hEc] at hle
  have hc3 : (2 ^ n) ^ 3 = 2 ^ (3 * n) := by rw [← pow_mul, mul_comm]
  rw [hc3] at hle
  have hpos : 0 < 2 ^ (3 * n) := by positivity
  omega

theorem false_of_outer_outer (hS : Setup L K n φ (zpowers t) t)
    {X₁ X₂ : Subgroup G} (hcomm : ∀ a ∈ X₁, ∀ b ∈ X₂, a * b = b * a) {D₁ D₂ : Subgroup G}
    (hD₁X : D₁ ≤ X₁) (hD₁t : D₁ ≤ centralizer ({t} : Set G)) (hD₁p : ⁅D₁, D₁⁆ = D₁)
    (hD₁c : Nat.card D₁ = Nat.card (D₁ ⊓ zc X₁ : Subgroup G) * outerResidualOrder n)
    (hD₂X : D₂ ≤ X₂) (hD₂t : D₂ ≤ centralizer ({t} : Set G)) (hD₂p : ⁅D₂, D₂⁆ = D₂)
    (hD₂c : Nat.card D₂ = Nat.card (D₂ ⊓ zc X₂ : Subgroup G) * outerResidualOrder n) :
    False := by
  have hD₁L := perfect_le_of_le_centralizer hS hD₁t hD₁p
  have hD₂L := perfect_le_of_le_centralizer hS hD₂t hD₂p
  have hc12 : ∀ a ∈ D₁, ∀ b ∈ D₂, a * b = b * a := fun a ha b hb =>
    hcomm a (hD₁X ha) b (hD₂X hb)
  have hprod := Common.card_sup_mul_card_inf_eq (le_normalizer_of_forall_commute hc12)
  have hinf : D₁ ⊓ D₂ ≤ D₁ ⊓ zc X₁ := fun y hy =>
    ⟨hy.1, mem_zc_of_commute (hD₁X hy.1) fun a ha => hcomm a ha y (hD₂X hy.2)⟩
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hinf
  have hdvdL : Nat.card (D₁ ⊔ D₂ : Subgroup G) ∣ Nat.card L :=
    Subgroup.card_dvd_of_le (sup_le hD₁L hD₂L)
  have hpos : 0 < Nat.card (D₁ ⊓ D₂ : Subgroup G) := Nat.card_pos
  have hsup : Nat.card (D₁ ⊔ D₂ : Subgroup G) =
      m * Nat.card (D₂ ⊓ zc X₂ : Subgroup G) * outerResidualOrder n ^ 2 := by
    apply Nat.eq_of_mul_eq_mul_right hpos
    calc Nat.card (D₁ ⊔ D₂ : Subgroup G) * Nat.card (D₁ ⊓ D₂ : Subgroup G)
        = Nat.card D₁ * Nat.card D₂ := hprod
      _ = (Nat.card (D₁ ⊓ D₂ : Subgroup G) * m) * outerResidualOrder n *
          (Nat.card (D₂ ⊓ zc X₂ : Subgroup G) * outerResidualOrder n) := by
        rw [hD₁c, hD₂c, hm]
      _ = m * Nat.card (D₂ ⊓ zc X₂ : Subgroup G) * outerResidualOrder n ^ 2 *
          Nat.card (D₁ ⊓ D₂ : Subgroup G) := by ring
  have hsq : outerResidualOrder n ^ 2 ∣ Nat.card L := by
    rw [hsup] at hdvdL
    exact (Dvd.intro_left _ rfl).trans hdvdL
  rw [Nat.card_congr φ.toEquiv] at hsq
  exact not_sq_dvd_card_antiSp hS.two_le hS.card_K hsq

theorem false_of_two_covers (hS : Setup L K n φ (zpowers t) t)
    {X₁ X₂ : Subgroup G} (hcomm : ∀ a ∈ X₁, ∀ b ∈ X₂, a * b = b * a)
    (hZ₁ : Odd (Nat.card (center X₁))) (hZ₂ : Odd (Nat.card (center X₂)))
    (ψ₁ : X₁ ⧸ center X₁ ≃* antiSp K) (ψ₂ : X₂ ⧸ center X₂ ≃* antiSp K)
    (ht₁ : t ∈ normalizer (X₁ : Set G)) (ht₂ : t ∈ normalizer (X₂ : Set G)) : False := by
  have htt := hS.t_mul_t
  have hcomm' : ∀ a ∈ X₂, ∀ b ∈ X₁, a * b = b * a := fun a ha b hb => (hcomm b hb a ha).symm
  rcases inner_or_outer hS.two_le hS.card_K hZ₁ ψ₁ ht₁ htt with
    ⟨E₁, hE₁X, hE₁t, hE₁sq, hE₁c⟩ |
      ⟨hout₁, D₁, hD₁X, hD₁t, hD₁p, ⟨e₁, he₁D, he₁1, he₁2⟩, hD₁c⟩ <;>
  rcases inner_or_outer hS.two_le hS.card_K hZ₂ ψ₂ ht₂ htt with
    ⟨E₂, hE₂X, hE₂t, hE₂sq, hE₂c⟩ |
      ⟨hout₂, D₂, hD₂X, hD₂t, hD₂p, ⟨e₂, he₂D, he₂1, he₂2⟩, hD₂c⟩
  · exact false_of_inner_inner hS hcomm hZ₁ hE₁X hE₁t hE₁sq hE₁c hE₂X hE₂t hE₂sq hE₂c
  · exact false_of_inner_outer hS hcomm hZ₁ hE₁X hE₁t hE₁sq hE₁c hout₂ (hD₂X he₂D) (hD₂t he₂D)
      he₂1 he₂2
  · exact false_of_inner_outer hS hcomm' hZ₂ hE₂X hE₂t hE₂sq hE₂c hout₁ (hD₁X he₁D) (hD₁t he₁D)
      he₁1 he₁2
  · exact false_of_outer_outer hS hcomm hD₁X hD₁t hD₁p hD₁c hD₂X hD₂t hD₂p hD₂c

theorem exists_cover {X₀ X : Subgroup G} (e : X₀ ≃* X) (ψ₀ : X₀ ⧸ center X₀ ≃* antiSp K)
    (hZ : Odd (Nat.card (center X₀))) :
    Odd (Nat.card (center X)) ∧ Nonempty (X ⧸ center X ≃* antiSp K) := by
  refine ⟨?_, ⟨(QuotientGroup.congr (center X₀) (center X) e
    (CFSG.ComponentClassification.OuterAutomorphisms.center_map_equiv e)).symm.trans ψ₀⟩⟩
  rw [← Nat.card_congr (Subgroup.centerCongr e).toEquiv]
  exact hZ

end Contradiction

end Endgame

section Setting

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  [Finite K] {n : ℕ} {φ : L ≃* antiSp K} {t : G}

theorem false_of_normalizes_both
    (hS : Setup L K n φ (zpowers t) t) {G₀ : Subgroup G}
    (hZ : Odd (Nat.card (center G₀)))
    (h₁₂ : G₀.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₀ : Set G))
    (hδ : ∀ x ∈ G₀, x * (t * x * t⁻¹) ∈ L)
    (hsurj : ∀ y ∈ L, ∃ x ∈ G₀, x * (t * x * t⁻¹) = y) (h : G)
    (h₁ : t ∈ normalizer ((G₀.map (MulAut.conj h).toMonoidHom : Subgroup G) : Set G))
    (h₂ : t ∈ normalizer (((G₀.map (MulAut.conj t).toMonoidHom).map
      (MulAut.conj h).toMonoidHom : Subgroup G) : Set G)) : False := by
  obtain ⟨ψ₀⟩ := Base.nonempty_mulEquiv_quotient_center φ hS.t_mul_t h₁₂ hδ hsurj
  set Gt : Subgroup G := G₀.map (MulAut.conj t).toMonoidHom with hGt
  let e₁ : G₀ ≃* G₀.map (MulAut.conj h).toMonoidHom :=
    Subgroup.equivMapOfInjective G₀ _ (MulAut.conj h).injective
  let e₂ : G₀ ≃* Gt.map (MulAut.conj h).toMonoidHom :=
    (Subgroup.equivMapOfInjective G₀ _ (MulAut.conj t).injective).trans
      (Subgroup.equivMapOfInjective Gt _ (MulAut.conj h).injective)
  obtain ⟨hZ₁, ⟨ψ₁⟩⟩ := Endgame.exists_cover e₁ ψ₀ hZ
  obtain ⟨hZ₂, ⟨ψ₂⟩⟩ := Endgame.exists_cover e₂ ψ₀ hZ
  refine Endgame.false_of_two_covers hS ?_ hZ₁ hZ₂ ψ₁ ψ₂ h₁ h₂
  rintro _ ⟨a, ha, rfl⟩ _ ⟨_, ⟨b, hb, rfl⟩, rfl⟩
  have hab := mem_centralizer_iff.1 (h₁₂ ⟨b, hb, rfl⟩) a ha
  change (MulAut.conj h) a * (MulAut.conj h) ((MulAut.conj t) b) =
    (MulAut.conj h) ((MulAut.conj t) b) * (MulAut.conj h) a
  rw [← map_mul, ← map_mul]
  exact congrArg (MulAut.conj h) hab

theorem false_of_swap [IsSimpleGroup G]
    (hS : Setup L K n φ (zpowers t) t) {G₀ : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple G₀) (hZ : Odd (Nat.card (center G₀)))
    (h₁₂ : G₀.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₀ : Set G))
    (hδ : ∀ x ∈ G₀, x * (t * x * t⁻¹) ∈ L)
    (hsurj : ∀ y ∈ L, ∃ x ∈ G₀, x * (t * x * t⁻¹) = y) {R : Subgroup G}
    (hR : CFSG.ABGLocalTools.IsSylowOf 2 R (L ⊔ zpowers t))
    (hNR : normalizer (R : Set G) ≤
      normalizer ((G₀ ⊔ G₀.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G)) : False := by
  have hK4 : 4 ≤ Nat.card K := by
    rw [hS.card_K]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hS.two_le
  obtain ⟨hsimple, x, y, hxy⟩ := CFSG.Quasithin.F7Two.isSimpleGroup_antiSp (K := K) hK4
  haveI := hsimple
  have hL : IsSimpleGroup L := φ.isSimpleGroup
  have hLab : ¬ ∀ x ∈ L, ∀ y ∈ L, x * y = y * x := by
    intro hc
    apply hxy
    have h2 : φ.symm x * φ.symm y = φ.symm y * φ.symm x :=
      Subtype.ext (hc _ (φ.symm x).2 _ (φ.symm y).2)
    simpa using congrArg φ h2
  have hLeven : Even (Nat.card L) := by
    rw [Nat.card_congr φ.toEquiv]
    exact even_card_antiSp K
  exact Common.false_of_swap_configuration hS.order_t hL hLab hLeven hS.L_le
    (fun H hH hp => perfect_le_of_le_centralizer hS hH hp) hq hZ h₁₂ hδ hsurj hR hNR
    (fun H hH hp => perfect_le_sup_of_le_normalizer hS hq hZ h₁₂ hδ hsurj hH hp)
    (fun h h₁ h₂ => false_of_normalizes_both hS hZ h₁₂ hδ hsurj h h₁ h₂)

end Setting

end BothTrivialProductEnd

end CFSG.LocalAnalysis.EvenBN.Sp4
