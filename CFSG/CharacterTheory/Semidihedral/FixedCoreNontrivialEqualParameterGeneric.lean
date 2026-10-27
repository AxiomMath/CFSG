module

public import CFSG.GroupTheory.CyclicSylowNormalOddComplement
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialLocal
public import Mathlib.GroupTheory.SpecificGroups.KleinFour

public section

namespace CFSG.Semidihedral.FixedCoreNontrivial

section Generic

variable {X : Type*} [Group X] [Finite X]

omit [Finite X] in
theorem isKleinFour_sup_zpowers {u z : X} (hu2 : orderOf u = 2) (hz2 : orderOf z = 2)
    (huz : u ≠ z) (hc : u * z = z * u) :
    IsKleinFour (Subgroup.zpowers u ⊔ Subgroup.zpowers z : Subgroup X) := by
  have hu : u * u = 1 := by rw [← pow_two, ← hu2, pow_orderOf_eq_one]
  have hz : z * z = 1 := by rw [← pow_two, ← hz2, pow_orderOf_eq_one]
  have hcomm : ∀ a ∈ Subgroup.zpowers u, ∀ b ∈ Subgroup.zpowers z, a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (Commute.zpow_zpow hc i j).eq
  have hnorm : Subgroup.zpowers z ≤ Subgroup.normalizer (Subgroup.zpowers u : Set X) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · intro ha
      rw [← hcomm a ha b hb, mul_inv_cancel_right]
      exact ha
    · intro ha
      have h1 := hcomm _ ha b⁻¹ ((Subgroup.zpowers z).inv_mem hb)
      have : a = b * a * b⁻¹ := by
        calc a = b⁻¹ * (b * a * b⁻¹) * b := by group
          _ = (b * a * b⁻¹) * b⁻¹ * b := by rw [h1]
          _ = b * a * b⁻¹ := by group
      rw [this]
      exact ha
  have hdisj : Disjoint (Subgroup.zpowers u) (Subgroup.zpowers z) := by
    rw [disjoint_iff, eq_bot_iff]
    rintro x ⟨hxu, hxz⟩
    rw [Subgroup.mem_bot]
    rcases zpowers_cases_of_mul_self hu x hxu with h1 | h1
    · exact h1
    · rcases zpowers_cases_of_mul_self hz x hxz with h2 | h2
      · exact h2
      · exact absurd (h1.symm.trans h2) huz
  have hcard : Nat.card (Subgroup.zpowers u ⊔ Subgroup.zpowers z : Subgroup X) = 4 := by
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hnorm hdisj,
      Nat.card_zpowers, Nat.card_zpowers, hu2, hz2]
  have hsq : ∀ x ∈ (Subgroup.zpowers u ⊔ Subgroup.zpowers z : Subgroup X), x * x = 1 := by
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup hcomm hx
    have ha2 : a * a = 1 := by
      rcases zpowers_cases_of_mul_self hu a ha with rfl | rfl
      · simp
      · exact hu
    have hb2 : b * b = 1 := by
      rcases zpowers_cases_of_mul_self hz b hb with rfl | rfl
      · simp
      · exact hz
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [hcomm a ha b hb]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [ha2, hb2, one_mul]
  have : Finite (Subgroup.zpowers u ⊔ Subgroup.zpowers z : Subgroup X) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  refine ⟨hcard, ?_⟩
  have hdvd : Monoid.exponent (Subgroup.zpowers u ⊔ Subgroup.zpowers z : Subgroup X) ∣ 2 :=
    Monoid.exponent_dvd_of_forall_pow_eq_one fun x => by
      rw [pow_two]; exact Subtype.ext (hsq x x.2)
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
  · exfalso
    have hall : ∀ x : (Subgroup.zpowers u ⊔ Subgroup.zpowers z : Subgroup X), x = 1 := fun x => by
      have := Monoid.pow_exponent_eq_one x
      rwa [h1, pow_one] at this
    have hsub : Subsingleton (Subgroup.zpowers u ⊔ Subgroup.zpowers z : Subgroup X) :=
      ⟨fun a b => by rw [hall a, hall b]⟩
    have := Finite.card_le_one_iff_subsingleton.mpr hsub
    omega
  · exact h1

theorem le_centralizer_of_isPGroup_two_of_no_kleinFour {S : Subgroup X} (hS : IsPGroup 2 S)
    (hS4 : ∀ T : Subgroup X, T ≤ S → ¬ IsKleinFour T) {u : X} (hu : u ∈ S) (hu2 : orderOf u = 2) :
    S ≤ Subgroup.centralizer {u} := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hu1 : u ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hu2
    omega
  have hSnt : Nontrivial S := ⟨⟨⟨u, hu⟩, 1, fun h => hu1 (congrArg Subtype.val h)⟩⟩
  have hZnt : Nontrivial (Subgroup.center S) := hS.center_nontrivial
  have hZp : IsPGroup 2 (Subgroup.center S) := hS.to_subgroup _
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hZp
  have hk1 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    have := Finite.one_lt_card_iff_nontrivial.mpr hZnt
    omega
  have h2 : 2 ∣ Nat.card (Subgroup.center S) := by
    rw [hk]
    exact dvd_pow_self 2 hk1
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 h2
  set z' : X := ((z : S) : X) with hz'
  have hz'2 : orderOf z' = 2 := by
    rw [hz', Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz]
  have hz'c : ∀ g ∈ S, g * z' = z' * g := by
    intro g hg
    have := (Subgroup.mem_center_iff.mp z.2) ⟨g, hg⟩
    exact congrArg Subtype.val this
  by_cases hzu : z' = u
  · intro g hg
    rw [Subgroup.mem_centralizer_singleton_iff, ← hzu]
    exact hz'c g hg
  · exfalso
    apply hS4 (Subgroup.zpowers u ⊔ Subgroup.zpowers z')
      (sup_le (Subgroup.zpowers_le.mpr hu) (Subgroup.zpowers_le.mpr (z : S).2))
    exact isKleinFour_sup_zpowers hu2 hz'2 (Ne.symm hzu) (hz'c u hu)

theorem conj_eq_inv_of_inf_centralizer_eq_bot {Q : Subgroup X} (hQ : Odd (Nat.card Q)) {u : X}
    (hu2 : u * u = 1) (huQ : u ∈ Subgroup.normalizer (Q : Set X))
    (hfree : Q ⊓ Subgroup.centralizer {u} = ⊥) :
    (∀ x ∈ Q, u * x * u⁻¹ = x⁻¹) ∧ ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x := by
  have _ := hQ.pos
  have huinv : u⁻¹ = u := (eq_inv_of_mul_eq_one_left hu2).symm
  have hconj : ∀ x ∈ Q, u * x * u⁻¹ ∈ Q := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp huQ x).mp hx
  let φ : Q → Q := fun x => ⟨(x : X)⁻¹ * (u * x * u⁻¹), Q.mul_mem (Q.inv_mem x.2) (hconj x x.2)⟩
  have hinj : Function.Injective φ := by
    intro x y hxy
    have h1 : (x : X)⁻¹ * (u * x * u⁻¹) = (y : X)⁻¹ * (u * y * u⁻¹) := congrArg Subtype.val hxy
    have h1' : (x : X)⁻¹ * u * x = (y : X)⁻¹ * u * y := by
      have := congrArg (· * u) h1
      simpa [mul_assoc] using this
    have h2 : (y : X) * (x : X)⁻¹ ∈ Q ⊓ Subgroup.centralizer {u} := by
      refine ⟨Q.mul_mem y.2 (Q.inv_mem x.2), ?_⟩
      show (y : X) * (x : X)⁻¹ ∈ Subgroup.centralizer {u}
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (y : X) * (x : X)⁻¹ * u = y * ((x : X)⁻¹ * u * x) * (x : X)⁻¹ := by group
        _ = y * ((y : X)⁻¹ * u * y) * (x : X)⁻¹ := by rw [h1']
        _ = u * ((y : X) * (x : X)⁻¹) := by group
    rw [hfree, Subgroup.mem_bot] at h2
    apply Subtype.ext
    exact (mul_inv_eq_one.mp h2).symm
  have hsurj := Finite.surjective_of_injective hinj
  have hinv : ∀ x ∈ Q, u * x * u⁻¹ = x⁻¹ := by
    intro x hx
    obtain ⟨y, hy⟩ := hsurj ⟨x, hx⟩
    have hy' : (y : X)⁻¹ * (u * y * u⁻¹) = x := congrArg Subtype.val hy
    rw [← hy', huinv]
    calc u * ((y : X)⁻¹ * (u * y * u)) * u = u * (y : X)⁻¹ * u * y * (u * u) := by group
      _ = u * (y : X)⁻¹ * u * y := by rw [hu2, mul_one]
      _ = ((y : X)⁻¹ * (u * y * u))⁻¹ := by
        simp only [mul_inv_rev, inv_inv, huinv, mul_assoc]
  refine ⟨hinv, fun x hx y hy => ?_⟩
  have h1 := hinv (x * y) (Q.mul_mem hx hy)
  have h2 : u * (x * y) * u⁻¹ = (u * x * u⁻¹) * (u * y * u⁻¹) := by group
  rw [h2, hinv x hx, hinv y hy, mul_inv_rev] at h1
  have := congrArg (fun w => w⁻¹) h1
  simpa using this.symm

theorem odd_mem_pPrimeCore_of_isCyclic_sylow {F : Subgroup X} (S : Sylow 2 F)
    (hS : IsCyclic (S : Subgroup F)) :
    IsPGroup 2 (F ⧸ CFSG.pPrimeCore 2 F) ∧
      ∀ x ∈ F, Odd (orderOf x) → x ∈ (CFSG.pPrimeCore 2 F).map F.subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, ⟨hN, -, hidx, -⟩, -⟩ := CFSG.cyclic_sylow_normal_odd_complement S hS
  obtain ⟨k, hk⟩ := S.isPGroup'.exists_card_eq
  have hq : IsPGroup 2 (F ⧸ CFSG.pPrimeCore 2 F) := by
    apply IsPGroup.of_card (n := k)
    rw [← Subgroup.index, hidx, hk]
  refine ⟨hq, fun x hx hodd => ?_⟩
  set x' : F := ⟨x, hx⟩
  have h1 : orderOf (QuotientGroup.mk x' : F ⧸ CFSG.pPrimeCore 2 F) ∣ orderOf x' :=
    orderOf_map_dvd (QuotientGroup.mk' _) x'
  obtain ⟨k, hk⟩ := hq (QuotientGroup.mk x')
  have hodd' : Odd (orderOf x') := by rwa [Subgroup.orderOf_mk]
  have hodd2 : Odd (orderOf (QuotientGroup.mk x' : F ⧸ CFSG.pPrimeCore 2 F)) :=
    hodd'.of_dvd_nat h1
  have h3 : orderOf (QuotientGroup.mk x' : F ⧸ CFSG.pPrimeCore 2 F) ∣ 2 ^ k :=
    orderOf_dvd_of_pow_eq_one hk
  have hcop : Nat.Coprime (orderOf (QuotientGroup.mk x' : F ⧸ CFSG.pPrimeCore 2 F)) (2 ^ k) :=
    Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hodd2)
  have h4 := Nat.Coprime.eq_one_of_dvd hcop h3
  rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h4
  exact ⟨x', h4, rfl⟩

end Generic

end CFSG.Semidihedral.FixedCoreNontrivial
