module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutBasic

public section

namespace CFSG.AGLEmbedding.LieOut

open CFSG.RankThree.PartOne (centerQuotientConj)

theorem exists_fixed_of_not_dvd_card {L : Type*} [Group L] (σ : MulAut L) {p : ℕ} (hp : p.Prime)
    (hσp : σ ^ p = 1) (S : Set L) (hS : ∀ g, σ g ∈ S ↔ g ∈ S) [Finite S]
    (hcard : ¬ p ∣ Nat.card S) : ∃ g ∈ S, σ g = g := by
  have : Fact p.Prime := ⟨hp⟩
  have hSz : ∀ (k : ℤ) (g : L), (σ ^ k) g ∈ S ↔ g ∈ S := by
    intro k
    induction k using Int.induction_on with
    | zero => intro g; simp
    | succ n ih =>
      intro g
      rw [zpow_add_one, MulAut.mul_apply]
      exact (ih (σ g)).trans (hS g)
    | pred n ih =>
      intro g
      rw [zpow_sub_one, MulAut.mul_apply]
      refine (ih (σ⁻¹ g)).trans ?_
      have := hS (σ⁻¹ g)
      rw [MulAut.apply_inv_self] at this
      exact this.symm
  let A : Subgroup (MulAut L) := Subgroup.zpowers σ
  let S' : SubMulAction A L :=
    { carrier := S
      smul_mem' := by
        rintro ⟨a, ha⟩ g hg
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
        exact (hSz k g).2 hg }
  have hA : IsPGroup p A := by
    have hord : orderOf σ ∣ p := orderOf_dvd_of_pow_eq_one hσp
    rcases (Nat.dvd_prime hp).1 hord with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h]; simp)
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h]; simp)
  have hcard' : ¬ p ∣ Nat.card S' := hcard
  obtain ⟨s, hs⟩ := hA.nonempty_fixed_point_of_prime_not_dvd_card S' hcard'
  refine ⟨s.1, s.2, ?_⟩
  have := MulAction.mem_fixedPoints.1 hs ⟨σ, Subgroup.mem_zpowers σ⟩
  exact congrArg Subtype.val this

@[expose] def centerTorsion (L : Type*) [Group L] (s : ℕ) : Subgroup L where
  carrier := {z | z ∈ Subgroup.center L ∧ z ^ s = 1}
  mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, by
    have hab : Commute a b := ((Subgroup.mem_center_iff.1 ha.1 b)).symm
    rw [hab.mul_pow, ha.2, hb.2, mul_one]⟩
  one_mem' := ⟨one_mem _, one_pow _⟩
  inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩

theorem not_dvd_card_centerTorsion {L : Type*} [Group L] [Finite L] {p s : ℕ} (hp : p.Prime)
    (hs : ¬ p ∣ s) : ¬ p ∣ Nat.card (centerTorsion L s) := by
  intro hd
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hd
  have hz1 : (z : L) ^ s = 1 := z.2.2
  have : orderOf (z : L) ∣ s := orderOf_dvd_of_pow_eq_one hz1
  rw [Subgroup.orderOf_coe, hz] at this
  exact hs this

theorem exists_centralizer_lift_of_coprime {Y : Type} [Group Y] [Finite Y] (L : Subgroup Y)
    {x : Y} (hx : x ∈ Subgroup.normalizer (L : Set Y)) {p : ℕ} (hp : p.Prime) (hxp : x ^ p = 1)
    {y : ↥L ⧸ Subgroup.center ↥L} (hfix : centerQuotientConj L ⟨x, hx⟩ y = y) {m : ℕ}
    (hm : Nat.Coprime m p) (hym : y ^ m = 1) :
    ∃ l : L, (QuotientGroup.mk l : ↥L ⧸ Subgroup.center ↥L) = y ∧ x * (l : Y) * x⁻¹ = l := by
  classical
  set σ : MulAut L := L.normalizerMonoidHom ⟨x, hx⟩ with hσ
  have hσp : σ ^ p = 1 := by
    have : (⟨x, hx⟩ : Subgroup.normalizer (L : Set Y)) ^ p = 1 := Subtype.ext (by simpa using hxp)
    rw [hσ, ← map_pow, this, map_one]
  set α := centerQuotientConj L ⟨x, hx⟩ with hα
  have hmk : ∀ g : L, (QuotientGroup.mk (σ g) : ↥L ⧸ Subgroup.center ↥L) =
      α (QuotientGroup.mk g) := fun g => (centerQuotientConj_mk L hx g).symm
  obtain ⟨ã, hã⟩ := QuotientGroup.mk_surjective y
  obtain ⟨e, s', hs', hs⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos ã).ne' p hp.ne_one
  have hr : Nat.Coprime (p ^ e) (orderOf y) :=
    (Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hym) hm).symm.pow_left e
  obtain ⟨k, hk0, hk1⟩ := Nat.chineseRemainder hr 0 1
  obtain ⟨u, hu⟩ : p ^ e ∣ k := (Nat.modEq_zero_iff_dvd).1 hk0
  have hyk : y ^ k = y := by
    rw [pow_eq_pow_mod k (pow_orderOf_eq_one y), hk1, ← pow_eq_pow_mod 1 (pow_orderOf_eq_one y),
      pow_one]
  set a : L := ã ^ k with ha
  have ha1 : (QuotientGroup.mk a : ↥L ⧸ Subgroup.center ↥L) = y := by
    rw [ha, QuotientGroup.mk_pow, hã, hyk]
  have has : a ^ s' = 1 := by
    rw [ha, ← pow_mul, hu, show p ^ e * u * s' = (p ^ e * s') * u by ring, ← hs, pow_mul,
      pow_orderOf_eq_one, one_pow]
  set S : Set L := {g | (QuotientGroup.mk g : ↥L ⧸ Subgroup.center ↥L) = y ∧ g ^ s' = 1}
    with hSdef
  have hS : ∀ g, σ g ∈ S ↔ g ∈ S := by
    intro g
    show ((QuotientGroup.mk (σ g) : ↥L ⧸ Subgroup.center ↥L) = y ∧ (σ g) ^ s' = 1) ↔
      ((QuotientGroup.mk g : ↥L ⧸ Subgroup.center ↥L) = y ∧ g ^ s' = 1)
    rw [hmk]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨α.injective (h1.trans hfix.symm), ?_⟩
      have : σ (g ^ s') = σ 1 := by rw [map_pow, h2, map_one]
      exact σ.injective this
    · rintro ⟨h1, h2⟩
      refine ⟨by rw [h1, hfix], ?_⟩
      rw [← map_pow, h2, map_one]
  have haS : a ∈ S := ⟨ha1, has⟩
  have : Finite S := inferInstance
  have hcardS : Nat.card S = Nat.card (centerTorsion L s') := by
    refine (Nat.card_congr (Equiv.ofBijective (fun z : centerTorsion L s' =>
      (⟨a * (z : L), ?_⟩ : S)) ⟨?_, ?_⟩)).symm
    · have hz1 : (QuotientGroup.mk (z : L) : ↥L ⧸ Subgroup.center ↥L) = 1 :=
        (QuotientGroup.eq_one_iff _).2 z.2.1
      refine ⟨by rw [QuotientGroup.mk_mul, ha1, hz1, mul_one], ?_⟩
      have hcomm : Commute a (z : L) := (Subgroup.mem_center_iff.1 z.2.1 a)
      rw [hcomm.mul_pow, has, z.2.2, mul_one]
    · intro z w hzw
      have := congrArg Subtype.val hzw
      exact Subtype.ext (mul_left_cancel this)
    · rintro ⟨g, hg1, hg2⟩
      have hz1 : (QuotientGroup.mk (a⁻¹ * g) : ↥L ⧸ Subgroup.center ↥L) = 1 := by
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, ha1, hg1, inv_mul_cancel]
      have hzc : a⁻¹ * g ∈ Subgroup.center L := (QuotientGroup.eq_one_iff _).1 hz1
      have hcomm : Commute a (a⁻¹ * g) := (Subgroup.mem_center_iff.1 hzc a)
      have hzs : (a⁻¹ * g) ^ s' = 1 := by
        have h3 : g = a * (a⁻¹ * g) := by group
        have h4 : g ^ s' = a ^ s' * (a⁻¹ * g) ^ s' := by
          conv_lhs => rw [h3]
          exact hcomm.mul_pow s'
        rw [hg2, has, one_mul] at h4
        exact h4.symm
      exact ⟨⟨a⁻¹ * g, hzc, hzs⟩, Subtype.ext (by simp)⟩
  have hnd : ¬ p ∣ Nat.card S := by
    rw [hcardS]
    exact not_dvd_card_centerTorsion hp hs'
  obtain ⟨g, hgS, hgσ⟩ := exists_fixed_of_not_dvd_card σ hp hσp S hS hnd
  refine ⟨g, hgS.1, ?_⟩
  have := congrArg (fun l : L => (l : Y)) hgσ
  simpa [hσ, Subgroup.normalizerMonoidHom_apply_apply_coe] using this

theorem mem_quotImage_of_coprime {Y : Type} [Group Y] [Finite Y] (L J : Subgroup Y) {x : Y}
    (hx : x ∈ Subgroup.normalizer (L : Set Y)) {p : ℕ} (hp : p.Prime) (hxp : x ^ p = 1)
    (hJ : ∀ l ∈ L, x * l * x⁻¹ = l → l ∈ J) {y : ↥L ⧸ Subgroup.center ↥L}
    (hfix : centerQuotientConj L ⟨x, hx⟩ y = y) {m : ℕ} (hm : Nat.Coprime m p) (hym : y ^ m = 1) :
    y ∈ quotImage L J := by
  obtain ⟨l, hl, hxl⟩ := exists_centralizer_lift_of_coprime L hx hp hxp hfix hm hym
  exact mem_quotImage.2 ⟨l, hJ l l.2 hxl, hl⟩

end CFSG.AGLEmbedding.LieOut
