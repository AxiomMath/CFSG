module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QSyl
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3L57
public import CFSG.LocalAnalysis.ComponentClassification.Sol78Residual
public import CFSG.Monster.B.Fischer.Fi22Order
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P58b3L

open CFSG Subgroup
open scoped MatrixGroups

theorem sl23_pow_eight_mul :
    ∀ g h : SL(2, ZMod 3), g ^ 8 = 1 → h ^ 8 = 1 → (g * h) ^ 8 = 1 := by
  decide

theorem sl23_sq_of_pow_eight :
    ∀ g : SL(2, ZMod 3), g ^ 8 = 1 → g * g = 1 ∨ g * g = -1 := by
  decide

theorem sl23_central_of_pow_eight : ∀ g : SL(2, ZMod 3), g ^ 8 = 1 →
    (∀ h : SL(2, ZMod 3), h ^ 8 = 1 → g * h = h * g) → g = 1 ∨ g = -1 := by
  decide

@[expose] def sl23Q : Subgroup SL(2, ZMod 3) where
  carrier := {g | g ^ 8 = 1}
  mul_mem' {g h} hg hh := sl23_pow_eight_mul g h hg hh
  one_mem' := one_pow 8
  inv_mem' {g} hg := by
    change g⁻¹ ^ 8 = 1
    rw [inv_pow, show g ^ 8 = 1 from hg, inv_one]

theorem card_sl23Q : Nat.card sl23Q = 8 := by
  have h : Nat.card sl23Q = Fintype.card {g : SL(2, ZMod 3) // g ^ 8 = 1} := by
    rw [← Nat.card_eq_fintype_card]
    rfl
  rw [h]
  decide

theorem orderOf_neg_one_sl23 : orderOf (-1 : SL(2, ZMod 3)) = 2 :=
  orderOf_eq_prime (by decide) (by decide)

theorem sl23_pow_eight_of_pow {g : SL(2, ZMod 3)} {k : ℕ} (hg : g ^ 2 ^ k = 1) : g ^ 8 = 1 := by
  have h1 : orderOf g ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hg
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  have h2 : orderOf g ∣ 24 := by
    rw [← P51Q.card_sl23]
    exact orderOf_dvd_natCard g
  rw [hj] at h2
  have hj3 : j ≤ 3 := by
    by_contra hj3
    have : 2 ^ 4 ∣ 2 ^ j := Nat.pow_dvd_pow 2 (by omega)
    have := this.trans h2
    norm_num at this
  apply orderOf_dvd_iff_pow_eq_one.mp
  rw [hj]
  exact Nat.pow_dvd_pow 2 hj3

section Klein

variable {M X : Type} [Group M] [Group X] [Finite M] [Finite X]
  (ι : M →* X) (ψ : M →* SL(2, ZMod 3))

omit [Finite M] [Finite X] in
theorem psi_eq_one_of_iota_eq_one (hι : Odd (Nat.card ι.ker)) (hψ8 : ∀ m, ψ m ^ 8 = 1) {k : M}
    (hk : ι k = 1) : ψ k = 1 := by
  have h1 : orderOf (ψ k) ∣ 2 ^ 3 := orderOf_dvd_of_pow_eq_one (hψ8 k)
  have h2 : orderOf (ψ k) ∣ Nat.card ι.ker := by
    refine (orderOf_map_dvd ψ k).trans ?_
    rw [← Subgroup.orderOf_mk k (show k ∈ ι.ker from hk)]
    exact orderOf_dvd_natCard _
  have hcop : Nat.Coprime (Nat.card ι.ker) (2 ^ 3) :=
    Nat.Coprime.pow_right 3 (Nat.coprime_two_right.mpr hι)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h2 h1)

omit [Finite M] [Finite X] in
theorem psi_eq_of_commute (hι : Odd (Nat.card ι.ker)) (hψ8 : ∀ m, ψ m ^ 8 = 1)
    (hsurj : ∀ g : SL(2, ZMod 3), g ^ 8 = 1 → ∃ m, m ^ 8 = 1 ∧ ψ m = g) {m : M}
    (hm : ∀ m', ι m * ι m' = ι m' * ι m) : ψ m = 1 ∨ ψ m = -1 := by
  refine sl23_central_of_pow_eight (ψ m) (hψ8 m) fun h hh => ?_
  obtain ⟨m', -, rfl⟩ := hsurj h hh
  have hk : ι (m * m' * m⁻¹ * m'⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hm m']
    group
  have h1 := psi_eq_one_of_iota_eq_one ι ψ hι hψ8 hk
  rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
  calc ψ m * ψ m' = ψ m * ψ m' * (ψ m)⁻¹ * (ψ m')⁻¹ * (ψ m' * ψ m) := by group
    _ = ψ m' * ψ m := by rw [h1, one_mul]

omit [Finite M] [Finite X] in
theorem psi_eq_of_central (hι : Odd (Nat.card ι.ker)) (hψ8 : ∀ m, ψ m ^ 8 = 1)
    (hsurj : ∀ g : SL(2, ZMod 3), g ^ 8 = 1 → ∃ m, m ^ 8 = 1 ∧ ψ m = g) {m : M}
    (hm : ι m ∈ center X) : ψ m = 1 ∨ ψ m = -1 :=
  psi_eq_of_commute ι ψ hι hψ8 hsurj fun m' => (mem_center_iff.mp hm (ι m')).symm

theorem isKleinFour_of_card {H : Type*} [Group H] (h4 : Nat.card H = 4)
    (hsq : ∀ x : H, x ^ 2 = 1) : IsKleinFour H := by
  refine ⟨h4, ?_⟩
  rcases (Nat.dvd_prime Nat.prime_two).mp (Monoid.exponent_dvd_of_forall_pow_eq_one hsq) with
    h | h
  · have : Subsingleton H := Monoid.exp_eq_one_iff.mp h
    have := Nat.card_of_subsingleton (1 : H)
    omega
  · exact h

theorem isKleinFour_range (hι : Odd (Nat.card ι.ker)) (hψ : Odd (Nat.card ψ.ker))
    (hψ8 : ∀ m, ψ m ^ 8 = 1)
    (hsurj : ∀ g : SL(2, ZMod 3), g ^ 8 = 1 → ∃ m, m ^ 8 = 1 ∧ ψ m = g) {z : M}
    (hz : ψ z = -1) (hzZ : ι z ∈ center X) :
    IsKleinFour (↥((QuotientGroup.mk' (center X)).comp ι).range ⧸
      pPrimeCore 2 ↥((QuotientGroup.mk' (center X)).comp ι).range) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set φ := (QuotientGroup.mk' (center X)).comp ι with hφ
  set O := pPrimeCore 2 ↥φ.range with hO
  set ρ : M →* ↥φ.range ⧸ O := (QuotientGroup.mk' O).comp φ.rangeRestrict with hρ
  have hρs : Function.Surjective ρ :=
    (QuotientGroup.mk'_surjective O).comp φ.rangeRestrict_surjective
  have hOodd : Odd (Nat.card O) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hρ1 : ∀ m, ρ m = 1 ↔ φ.rangeRestrict m ∈ O := fun m => by
    rw [hρ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hK1 : ∀ m, ψ m = 1 → ρ m = 1 := by
    intro m hm
    have hN : (ψ.ker.map φ.rangeRestrict).Normal :=
      (MonoidHom.normal_ker ψ).map _ φ.rangeRestrict_surjective
    have hNodd : Odd (Nat.card (ψ.ker.map φ.rangeRestrict)) :=
      Odd.of_dvd_nat hψ (Subgroup.card_map_dvd _ _)
    exact (hρ1 m).mpr (F3L57.le_pPrimeCore_of_normal hN hNodd ⟨m, hm, rfl⟩)
  have hρz : ρ z = 1 := by
    have h1 : φ.rangeRestrict z = 1 := by
      apply Subtype.ext
      change φ z = 1
      rw [hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hzZ
    rw [hρ, MonoidHom.comp_apply, h1, map_one]
  have hK2 : ∀ m, m ^ 8 = 1 → ρ m = 1 → ψ m = 1 ∨ ψ m = -1 := by
    intro m hm8 hρm
    have h1 : φ.rangeRestrict m = 1 :=
      F3L57.eq_one_of_pow_two_pow_of_mem hOodd ((hρ1 m).mp hρm) (k := 3)
        (by rw [← map_pow, show (2 : ℕ) ^ 3 = 8 by norm_num, hm8, map_one])
    have h2 : φ m = 1 := congrArg Subtype.val h1
    rw [hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    exact psi_eq_of_central ι ψ hι hψ8 hsurj h2
  have hker : ∀ m, ρ m = 1 ↔ ψ m = 1 ∨ ψ m = -1 := by
    intro m
    constructor
    · intro hρm
      obtain ⟨m₀, hm₀8, hm₀⟩ := hsurj (ψ m) (hψ8 m)
      have h1 : ψ (m₀⁻¹ * m) = 1 := by rw [map_mul, map_inv, hm₀, inv_mul_cancel]
      have h2 : ρ m₀ = 1 := by
        have h3 := hK1 _ h1
        rw [map_mul, map_inv, hρm, mul_one, inv_eq_one] at h3
        exact h3
      rw [← hm₀]
      exact hK2 m₀ hm₀8 h2
    · rintro (h | h)
      · exact hK1 m h
      · have h1 : ψ (m * z⁻¹) = 1 := by rw [map_mul, map_inv, h, hz, mul_inv_cancel]
        have h2 := hK1 _ h1
        rw [map_mul, map_inv, hρz, inv_one, mul_one] at h2
        exact h2
  have hsq : ∀ x : ↥φ.range ⧸ O, x ^ 2 = 1 := by
    intro x
    obtain ⟨m, rfl⟩ := hρs x
    rw [← map_pow]
    apply (hker _).mpr
    rw [map_pow, pow_two]
    exact sl23_sq_of_pow_eight (ψ m) (hψ8 m)
  have hψr : ψ.range = sl23Q := by
    ext g
    constructor
    · rintro ⟨m, rfl⟩
      exact hψ8 m
    · intro hg
      obtain ⟨m, -, hm⟩ := hsurj g hg
      exact ⟨m, hm⟩
  have hM1 : Nat.card M = Nat.card ψ.ker * 8 := by
    rw [card_eq_card_quotient_mul_card_subgroup ψ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv, hψr, card_sl23Q, mul_comm]
  have hM2 : Nat.card M = Nat.card (↥φ.range ⧸ O) * Nat.card ρ.ker := by
    rw [card_eq_card_quotient_mul_card_subgroup ρ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ρ hρs).toEquiv]
  have hψρ : ψ.ker ≤ ρ.ker := fun m hm => hK1 m hm
  set ψ' := ψ.comp ρ.ker.subtype with hψ'
  have hψ'k : Nat.card ψ'.ker = Nat.card ψ.ker := by
    have heq : ψ'.ker = ψ.ker.subgroupOf ρ.ker := by
      ext m
      rfl
    rw [heq]
    exact Nat.card_congr (subgroupOfEquivOfLe hψρ).toEquiv
  have hψ'r : ψ'.range = zpowers (-1) := by
    apply le_antisymm
    · rintro _ ⟨m, rfl⟩
      rcases (hker m).mp m.2 with h | h
      · change ψ m ∈ zpowers (-1)
        rw [h]
        exact one_mem _
      · change ψ m ∈ zpowers (-1)
        rw [h]
        exact mem_zpowers _
    · rw [zpowers_le]
      exact ⟨⟨z, hρz⟩, hz⟩
  have hK3 : Nat.card ρ.ker = Nat.card ψ.ker * 2 := by
    rw [card_eq_card_quotient_mul_card_subgroup ψ'.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ').toEquiv, hψ'r, Nat.card_zpowers,
      orderOf_neg_one_sl23, hψ'k, mul_comm]
  have hpos : 0 < Nat.card ψ.ker := Nat.card_pos
  have hcard : Nat.card (↥φ.range ⧸ O) = 4 := by
    rw [hK3] at hM2
    rw [hM1] at hM2
    have h8 : Nat.card ψ.ker * 8 = Nat.card ψ.ker * (2 * Nat.card (↥φ.range ⧸ O)) := by
      rw [hM2]
      ring
    have := Nat.eq_of_mul_eq_mul_left hpos h8
    omega
  exact isKleinFour_of_card hcard hsq

omit [Finite M] [Finite X] in
theorem not_mem_range (hι : Odd (Nat.card ι.ker)) (hψ : Odd (Nat.card ψ.ker))
    (hψ8 : ∀ m, ψ m ^ 8 = 1)
    (hsurj : ∀ g : SL(2, ZMod 3), g ^ 8 = 1 → ∃ m, m ^ 8 = 1 ∧ ψ m = g) {z : M}
    (hz : ψ z = -1) (hzZ : ι z ∈ center X) {t : X} (ht : t * t = 1) (htZ : t ∉ center X)
    (htM : ∀ m, ι m * t = t * ι m) :
    QuotientGroup.mk' (center X) t ∉ ((QuotientGroup.mk' (center X)).comp ι).range := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rintro ⟨m, hm⟩
  rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq] at hm
  obtain ⟨w, hw⟩ : ∃ w, w = (ι m)⁻¹ * t := ⟨_, rfl⟩
  rw [← hw] at hm
  have hwZ : w⁻¹ ∈ center X := inv_mem hm
  have e : ι m = t * w⁻¹ := by rw [hw]; group
  have hcomm : ∀ m', ι m * ι m' = ι m' * ι m := by
    intro m'
    rw [e]
    have h1 := mem_center_iff.mp hwZ (ι m')
    calc t * w⁻¹ * ι m' = t * (w⁻¹ * ι m') := mul_assoc _ _ _
      _ = t * (ι m' * w⁻¹) := by rw [h1]
      _ = t * ι m' * w⁻¹ := (mul_assoc _ _ _).symm
      _ = ι m' * t * w⁻¹ := by rw [← htM m']
      _ = ι m' * (t * w⁻¹) := mul_assoc _ _ _
  have hmk : ∀ x : X, x ∈ center X → QuotientGroup.mk' (center X) x = 1 := fun x hx => by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hx
  obtain ⟨k, hk, hkt⟩ : ∃ k, ψ k = 1 ∧
      QuotientGroup.mk' (center X) t = QuotientGroup.mk' (center X) (ι k) := by
    have htm : QuotientGroup.mk' (center X) t = QuotientGroup.mk' (center X) (ι m) := by
      rw [e, map_mul, hmk _ hwZ, mul_one]
    rcases psi_eq_of_commute ι ψ hι hψ8 hsurj hcomm with h | h
    · exact ⟨m, h, htm⟩
    · refine ⟨z⁻¹ * m, ?_, ?_⟩
      · rw [map_mul, map_inv, hz, h, inv_neg, inv_one, neg_mul_neg, one_mul]
      · rw [htm]
        simp only [map_mul, map_inv, hmk _ hzZ, inv_one, one_mul]
  have h2 : orderOf (QuotientGroup.mk' (center X) t) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow, pow_two, ht, map_one]
    · rw [QuotientGroup.mk'_apply, Ne, QuotientGroup.eq_one_iff]
      exact htZ
  have h3 : orderOf (QuotientGroup.mk' (center X) (ι k)) ∣ Nat.card ψ.ker := by
    refine (orderOf_map_dvd _ _).trans ((orderOf_map_dvd _ _).trans ?_)
    rw [← Subgroup.orderOf_mk k (show k ∈ ψ.ker from hk)]
    exact orderOf_dvd_natCard _
  rw [← hkt, h2] at h3
  exact Nat.not_even_iff_odd.mpr hψ (even_iff_two_dvd.mpr h3)

omit [Finite M] [Finite X] in
theorem isPGroup_range_quotient (hψ : Odd (Nat.card ψ.ker)) (hψ8 : ∀ m, ψ m ^ 8 = 1) :
    IsPGroup 2 (↥ι.range ⧸ pPrimeCore 2 ↥ι.range) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ x
  obtain ⟨m, rfl⟩ := ι.rangeRestrict_surjective y
  refine ⟨3, ?_⟩
  have hN : (ψ.ker.map ι.rangeRestrict).Normal :=
    (MonoidHom.normal_ker ψ).map _ ι.rangeRestrict_surjective
  have hNodd : Odd (Nat.card (ψ.ker.map ι.rangeRestrict)) :=
    Odd.of_dvd_nat hψ (Subgroup.card_map_dvd _ _)
  have hm8 : m ^ 2 ^ 3 ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_pow]
    exact hψ8 m
  rw [← map_pow, ← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact F3L57.le_pPrimeCore_of_normal hN hNodd ⟨_, hm8, rfl⟩

end Klein

section Data

variable {G : Type} [Group G] [Finite G] {L₁ K : Subgroup G}

@[expose] def toK (hO₁ : GH74.GLS.oPrimeResidualOf 2 L₁ ≤ K) :
    ↥(GH74.GLS.oPrimeResidual 2 ↥L₁) →* ↥K :=
  (L₁.subtype.comp (GH74.GLS.oPrimeResidual 2 ↥L₁).subtype).codRestrict K
    fun m => hO₁ ⟨m, m.2, rfl⟩

@[expose] def iota (hO₁ : GH74.GLS.oPrimeResidualOf 2 L₁ ≤ K) :
    ↥(GH74.GLS.oPrimeResidual 2 ↥L₁) →* ↥K ⧸ pPrimeCore 2 ↥K :=
  (QuotientGroup.mk' (pPrimeCore 2 ↥K)).comp (toK hO₁)

@[expose] def psi (e : ↥L₁ ⧸ pPrimeCore 2 ↥L₁ ≃* SL(2, ZMod 3)) :
    ↥(GH74.GLS.oPrimeResidual 2 ↥L₁) →* SL(2, ZMod 3) :=
  e.toMonoidHom.comp ((QuotientGroup.mk' (pPrimeCore 2 ↥L₁)).comp
    (GH74.GLS.oPrimeResidual 2 ↥L₁).subtype)

omit [Finite G] in
theorem coe_toK (hO₁ : GH74.GLS.oPrimeResidualOf 2 L₁ ≤ K)
    (m : ↥(GH74.GLS.oPrimeResidual 2 ↥L₁)) : ((toK hO₁ m : ↥K) : G) = ((m : ↥L₁) : G) := rfl

omit [Finite G] in
theorem iota_apply (hO₁ : GH74.GLS.oPrimeResidualOf 2 L₁ ≤ K)
    (m : ↥(GH74.GLS.oPrimeResidual 2 ↥L₁)) :
    iota hO₁ m = QuotientGroup.mk' (pPrimeCore 2 ↥K) (toK hO₁ m) := rfl

omit [Finite G] in
theorem psi_apply (e : ↥L₁ ⧸ pPrimeCore 2 ↥L₁ ≃* SL(2, ZMod 3))
    (m : ↥(GH74.GLS.oPrimeResidual 2 ↥L₁)) :
    psi e m = e (QuotientGroup.mk' (pPrimeCore 2 ↥L₁) (m : ↥L₁)) := rfl

omit [Finite G] in
theorem toK_injective (hO₁ : GH74.GLS.oPrimeResidualOf 2 L₁ ≤ K) :
    Function.Injective (toK hO₁) := by
  intro x y h
  have h1 : ((x : ↥L₁) : G) = ((y : ↥L₁) : G) := by
    rw [← coe_toK hO₁ x, ← coe_toK hO₁ y, h]
  exact Subtype.ext (Subtype.ext h1)

theorem odd_card_ker_iota (hO₁ : GH74.GLS.oPrimeResidualOf 2 L₁ ≤ K) :
    Odd (Nat.card (iota hO₁).ker) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hker : (iota hO₁).ker = (pPrimeCore 2 ↥K).comap (toK hO₁) := by
    rw [iota, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']
  rw [hker]
  exact Odd.of_dvd_nat (Nat.coprime_two_left.mp pPrimeCore_coprime_card)
    (Subgroup.card_comap_dvd_of_injective _ _ (toK_injective hO₁))

theorem odd_card_ker_psi (e : ↥L₁ ⧸ pPrimeCore 2 ↥L₁ ≃* SL(2, ZMod 3)) :
    Odd (Nat.card (psi e).ker) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hker : (psi e).ker =
      (pPrimeCore 2 ↥L₁).comap (GH74.GLS.oPrimeResidual 2 ↥L₁).subtype := by
    ext m
    rw [MonoidHom.mem_ker, psi_apply, MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, mem_comap]
    rfl
  rw [hker]
  exact Odd.of_dvd_nat (Nat.coprime_two_left.mp pPrimeCore_coprime_card)
    (Subgroup.card_comap_dvd_of_injective _ _ (subtype_injective _))

omit [Finite G] in
theorem psi_pow_eight (e : ↥L₁ ⧸ pPrimeCore 2 ↥L₁ ≃* SL(2, ZMod 3))
    (m : ↥(GH74.GLS.oPrimeResidual 2 ↥L₁)) : psi e m ^ 8 = 1 := by
  rw [psi_apply]
  obtain ⟨x, hx⟩ := m
  change e (QuotientGroup.mk' _ x) ^ 8 = 1
  refine Subgroup.closure_induction (p := fun x _ => e (QuotientGroup.mk' _ x) ^ 8 = 1)
    ?_ ?_ ?_ ?_ hx
  · rintro y ⟨k, hk⟩
    apply sl23_pow_eight_of_pow (k := k)
    rw [← map_pow, ← map_pow, hk, map_one, map_one]
  · rw [map_one, map_one, one_pow]
  · intro a b _ _ ha hb
    rw [map_mul, map_mul]
    exact sl23_pow_eight_mul _ _ ha hb
  · intro a _ ha
    rw [map_inv, map_inv, inv_pow, ha, inv_one]

theorem exists_sylow_data {z₁ : G} (hz₁ : orderOf z₁ = 2) (hz₁L : z₁ ∈ L₁)
    (hL₁z : L₁ ≤ centralizer {z₁}) (e : ↥L₁ ⧸ pPrimeCore 2 ↥L₁ ≃* SL(2, ZMod 3)) :
    (∀ g : SL(2, ZMod 3), g ^ 8 = 1 →
      ∃ m : ↥(GH74.GLS.oPrimeResidual 2 ↥L₁), m ^ 8 = 1 ∧ psi e m = g) ∧
    ∃ z a b : ↥(GH74.GLS.oPrimeResidual 2 ↥L₁), ((z : ↥L₁) : G) = z₁ ∧ psi e z = -1 ∧
      a * a = z ∧ b * b = z ∧ a * b = z * (b * a) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set z₀ : ↥L₁ := ⟨z₁, hz₁L⟩ with hz₀
  have hz₀c : z₀ ∈ center ↥L₁ := by
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (hL₁z g.2))
  have hz₀2 : orderOf z₀ = 2 := by rw [hz₀, Subgroup.orderOf_mk]; exact hz₁
  obtain ⟨S, hS8, hzS, -, -⟩ := P51Q.exists_sylow_quat (Or.inr ⟨e⟩) hz₀c hz₀2
  set f : ↥S →* SL(2, ZMod 3) :=
    e.toMonoidHom.comp ((QuotientGroup.mk' (pPrimeCore 2 ↥L₁)).comp S.subtype) with hf
  have hOodd : Odd (Nat.card (pPrimeCore 2 ↥L₁)) :=
    Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hs8 : ∀ s : ↥S, s ^ 8 = 1 := fun s => by
    have := pow_card_eq_one' (G := ↥S) (x := s)
    rwa [hS8] at this
  have hfinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro s hs
    rw [hf, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hs
    have h1 : (s : ↥L₁) = 1 := F3L57.eq_one_of_pow_two_pow_of_mem hOodd hs (k := 3)
      (by rw [show (2 : ℕ) ^ 3 = 8 by norm_num, ← Subgroup.coe_pow, hs8 s, Subgroup.coe_one])
    exact Subtype.ext h1
  have hfr : f.range = sl23Q := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨s, rfl⟩
      change f s ^ 8 = 1
      rw [← map_pow, hs8 s, map_one]
    · rw [card_sl23Q, ← hS8]
      exact (Nat.card_congr (MonoidHom.ofInjective hfinj).toEquiv).le
  have hSres : ∀ s : ↥S, (s : ↥L₁) ∈ GH74.GLS.oPrimeResidual 2 ↥L₁ := fun s =>
    F3L57.mem_oPrimeResidual_of_pow (k := 3)
      (by rw [show (2 : ℕ) ^ 3 = 8 by norm_num, ← Subgroup.coe_pow, hs8 s, Subgroup.coe_one])
  let incl : ↥S → ↥(GH74.GLS.oPrimeResidual 2 ↥L₁) := fun s => ⟨s, hSres s⟩
  have hincl : ∀ s, psi e (incl s) = f s := fun s => rfl
  have hincl_mul : ∀ s s' : ↥S, incl (s * s') = incl s * incl s' := fun s s' => rfl
  have hpre : ∀ g : SL(2, ZMod 3), g ^ 8 = 1 → ∃ s : ↥S, f s = g := by
    intro g hg
    have hg' : g ∈ f.range := by rw [hfr]; exact hg
    obtain ⟨s, hs⟩ := hg'
    exact ⟨s, hs⟩
  refine ⟨fun g hg => ?_, ?_⟩
  · obtain ⟨s, hs⟩ := hpre g hg
    refine ⟨incl s, ?_, by rw [hincl, hs]⟩
    exact Subtype.ext (by
      change ((s : ↥L₁)) ^ 8 = 1
      rw [← Subgroup.coe_pow, hs8 s, Subgroup.coe_one])
  ·
    set zS : ↥S := ⟨z₀, hzS⟩ with hzS'
    have hfz : f zS = -1 := by
      have hsq : f zS * f zS = 1 := by
        rw [← map_mul]
        have : zS * zS = 1 := by
          apply Subtype.ext
          change z₀ * z₀ = 1
          rw [← pow_two, ← hz₀2, pow_orderOf_eq_one]
        rw [this, map_one]
      rcases P51Q.sl23_mul_self _ hsq with h | h
      · exfalso
        have h1 : zS = 1 := hfinj (h.trans (map_one f).symm)
        have h2 : z₀ = 1 := congrArg Subtype.val h1
        rw [h2, orderOf_one] at hz₀2
        exact absurd hz₀2 (by norm_num)
      · exact h
    obtain ⟨sa, hsa⟩ := hpre P51Q.sl23i (by decide)
    obtain ⟨sb, hsb⟩ := hpre P51Q.sl23j (by decide)
    refine ⟨incl zS, incl sa, incl sb, rfl, by rw [hincl, hfz], ?_, ?_, ?_⟩
    · rw [← hincl_mul]
      congr 1
      apply hfinj
      rw [map_mul, hsa, hfz]
      decide
    · rw [← hincl_mul]
      congr 1
      apply hfinj
      rw [map_mul, hsb, hfz]
      decide
    · rw [← hincl_mul, ← hincl_mul, ← hincl_mul]
      congr 1
      apply hfinj
      rw [map_mul, map_mul, map_mul, hsa, hsb, hfz]
      decide

omit [Finite G] in
theorem centralizer_eq_subgroupOf {z : G} (hzK : z ∈ K) :
    centralizer ({(⟨z, hzK⟩ : ↥K)} : Set ↥K) = (K ⊓ centralizer {z}).subgroupOf K := by
  ext x
  rw [mem_subgroupOf, mem_inf]
  constructor
  · intro h
    exact ⟨x.2, mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_centralizer_singleton_iff.mp h))⟩
  · rintro ⟨-, h⟩
    exact mem_centralizer_singleton_iff.mpr (Subtype.ext (mem_centralizer_singleton_iff.mp h))

omit [Finite G] in
theorem range_iota (hO₁ : GH74.GLS.oPrimeResidualOf 2 L₁ ≤ K) :
    (iota hO₁).range =
      ((GH74.GLS.oPrimeResidualOf 2 L₁).subgroupOf K).map
        (QuotientGroup.mk' (pPrimeCore 2 ↥K)) := by
  rw [iota, MonoidHom.range_comp]
  congr 1
  ext x
  rw [mem_subgroupOf]
  constructor
  · rintro ⟨m, rfl⟩
    exact ⟨m, m.2, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    exact ⟨⟨y, hy⟩, Subtype.ext hyx⟩

theorem range_iota_subnormal {z₁ z₂ : G} (hz₂ : orderOf z₂ = 2)
    (hL₁ : IsSolvableTwoComponentIn L₁ (centralizer {z₁} ⊓ centralizer {z₂}))
    (hK : K ≤ centralizer {z₁}) (hO₁ : GH74.GLS.oPrimeResidualOf 2 L₁ ≤ K) (hz₂K : z₂ ∈ K) :
    (iota hO₁).range ≤ centralizer {QuotientGroup.mk' (pPrimeCore 2 ↥K) ⟨z₂, hz₂K⟩} ∧
      ((iota hO₁).range.subgroupOf
        (centralizer {QuotientGroup.mk' (pPrimeCore 2 ↥K) ⟨z₂, hz₂K⟩})).IsSubnormal := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set MG := GH74.GLS.oPrimeResidualOf 2 L₁ with hMG
  set D := centralizer {z₁} ⊓ centralizer ({z₂} : Set G) with hD
  have hML : MG ≤ L₁ := Sol78.oPrimeResidualOf_le L₁
  have hLD : L₁ ≤ D := hL₁.1
  have hMn : (MG.subgroupOf L₁).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hML]
    intro g hg
    exact Sol78.mem_normalizer_oPrimeResidualOf (le_normalizer hg)
  have hMD : (MG.subgroupOf D).IsSubnormal :=
    CFSG.GroupTheory.isSubnormal_subgroupOf_trans hML hLD hMn.isSubnormal hL₁.2.1
  have hD'D : K ⊓ centralizer ({z₂} : Set G) ≤ D := inf_le_inf_right _ hK
  have hMD' : (MG.subgroupOf (K ⊓ centralizer {z₂})).IsSubnormal :=
    CFSG.GroupTheory.isSubnormal_subgroupOf_of_le hD'D hMD
  have hCK := centralizer_eq_subgroupOf hz₂K
  have hMK : ((MG.subgroupOf K).subgroupOf
      (centralizer ({(⟨z₂, hz₂K⟩ : ↥K)} : Set ↥K))).IsSubnormal := by
    rw [hCK]
    exact (CFSG.GroupTheory.isSubnormal_subgroupOf_subgroupOf_iff inf_le_left).mpr hMD'
  have hMleC : MG.subgroupOf K ≤ centralizer ({(⟨z₂, hz₂K⟩ : ↥K)} : Set ↥K) := by
    intro x hx
    rw [mem_subgroupOf] at hx
    rw [mem_centralizer_singleton_iff]
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp (mem_inf.mp (hLD (hML hx))).2
  have hOodd : Odd (Nat.card (pPrimeCore 2 ↥K)) :=
    Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hz2 : (⟨z₂, hz₂K⟩ : ↥K) * ⟨z₂, hz₂K⟩ = 1 := by
    apply Subtype.ext
    change z₂ * z₂ = 1
    rw [← pow_two, ← hz₂, pow_orderOf_eq_one]
  rw [range_iota, ← UnbalancedLayer.map_centralizer_eq hOodd hz2]
  refine ⟨map_mono hMleC, ?_⟩
  have heq : ((MG.subgroupOf K).subgroupOf
      (centralizer ({(⟨z₂, hz₂K⟩ : ↥K)} : Set ↥K))).map
      ((QuotientGroup.mk' (pPrimeCore 2 ↥K)).subgroupMap
        (centralizer ({(⟨z₂, hz₂K⟩ : ↥K)} : Set ↥K))) =
      ((MG.subgroupOf K).map (QuotientGroup.mk' (pPrimeCore 2 ↥K))).subgroupOf
        ((centralizer ({(⟨z₂, hz₂K⟩ : ↥K)} : Set ↥K)).map
          (QuotientGroup.mk' (pPrimeCore 2 ↥K))) := by
    ext y
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact mem_subgroupOf.mpr ⟨c, mem_subgroupOf.mp hc, rfl⟩
    · intro hy
      obtain ⟨l, hl, hly⟩ := mem_map.mp (mem_subgroupOf.mp hy)
      exact ⟨⟨l, hMleC hl⟩, mem_subgroupOf.mpr hl, Subtype.ext hly⟩
  rw [← heq]
  exact hMK.map (MonoidHom.subgroupMap_surjective _ _)

end Data

end CFSG.ComponentClassification.HarrisLit.T1.P58b3L
