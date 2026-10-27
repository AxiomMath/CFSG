module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open scoped commutatorElement

namespace JOut

variable {G : Type*} [Group G]

theorem sup_centralizer_le_normalizer (L : Subgroup G) :
    L ⊔ Subgroup.centralizer (L : Set G) ≤ Subgroup.normalizer (L : Set G) :=
  sup_le Subgroup.le_normalizer (Subgroup.centralizer_le_normalizer _)

theorem conj_mem_sup_centralizer {L : Subgroup G} {w : G}
    (hw : w ∈ Subgroup.normalizer (L : Set G)) {k : G}
    (hk : k ∈ L ⊔ Subgroup.centralizer (L : Set G)) :
    w * k * w⁻¹ ∈ L ⊔ Subgroup.centralizer (L : Set G) := by
  have key : L ⊔ Subgroup.centralizer (L : Set G) ≤
      (L ⊔ Subgroup.centralizer (L : Set G)).comap (MulAut.conj w).toMonoidHom := by
    refine sup_le (fun l hl => ?_) (fun c hc => ?_)
    · refine Subgroup.mem_sup_left ?_
      exact ((Subgroup.mem_normalizer_iff.1 hw l).1 hl)
    · refine Subgroup.mem_sup_right ?_
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have hl' : w⁻¹ * l * w ∈ L := by
        have := (Subgroup.mem_normalizer_iff.1 (inv_mem hw) l).1 hl
        simpa using this
      have h1 := Subgroup.mem_centralizer_iff.1 hc (w⁻¹ * l * w) hl'
      show l * (w * c * w⁻¹) = w * c * w⁻¹ * l
      calc l * (w * c * w⁻¹) = w * ((w⁻¹ * l * w) * c) * w⁻¹ := by group
        _ = w * (c * (w⁻¹ * l * w)) * w⁻¹ := by rw [h1]
        _ = w * c * w⁻¹ * l := by group
  have := key hk
  simpa [Subgroup.mem_comap, MulAut.conj_apply] using this

theorem commutator_mem_sup_centralizer_of_mem {L : Subgroup G} {w j : G}
    (hw : w ∈ Subgroup.normalizer (L : Set G)) (hj : j ∈ L ⊔ Subgroup.centralizer (L : Set G)) :
    ⁅w, j⁆ ∈ L ⊔ Subgroup.centralizer (L : Set G) := by
  rw [commutatorElement_def]
  exact mul_mem (conj_mem_sup_centralizer hw hj) (inv_mem hj)

@[expose] def commutesModInner (L : Subgroup G) (w : G) : Subgroup G where
  carrier := {j | j ∈ Subgroup.normalizer (L : Set G) ∧
    ⁅w, j⁆ ∈ L ⊔ Subgroup.centralizer (L : Set G)}
  one_mem' := ⟨one_mem _, by simpa using one_mem (L ⊔ Subgroup.centralizer (L : Set G))⟩
  mul_mem' := by
    rintro j j' ⟨hjN, hjK⟩ ⟨hj'N, hj'K⟩
    refine ⟨mul_mem hjN hj'N, ?_⟩
    have : ⁅w, j * j'⁆ = ⁅w, j⁆ * (j * ⁅w, j'⁆ * j⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [this]
    exact mul_mem hjK (conj_mem_sup_centralizer hjN hj'K)
  inv_mem' := by
    rintro j ⟨hjN, hjK⟩
    refine ⟨inv_mem hjN, ?_⟩
    have : ⁅w, j⁻¹⁆ = j⁻¹ * ⁅w, j⁆⁻¹ * (j⁻¹)⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [this]
    exact conj_mem_sup_centralizer (inv_mem hjN) (inv_mem hjK)

theorem sup_centralizer_le_commutesModInner {L : Subgroup G} {w : G}
    (hw : w ∈ Subgroup.normalizer (L : Set G)) :
    L ⊔ Subgroup.centralizer (L : Set G) ≤ commutesModInner L w := fun j hj =>
  ⟨sup_centralizer_le_normalizer L hj, commutator_mem_sup_centralizer_of_mem hw hj⟩

theorem inverted_commutator {a : G} (ha : a * a = 1) (w : G) :
    a * ⁅w, a⁆ * a⁻¹ = ⁅w, a⁆⁻¹ := by
  have h : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  simp only [commutatorElement_def, mul_inv_rev, inv_inv, h]
  calc a * (w * a * w⁻¹ * a) * a = a * w * a * w⁻¹ * (a * a) := by group
    _ = a * w * a * w⁻¹ := by rw [ha, mul_one]
    _ = _ := by simp [mul_assoc]

theorem exists_odd_order_pow_of_pow_mem [Finite G] {K : Subgroup G} {y : G} {m : ℕ} (hm : Odd m)
    (hy : y ^ m ∈ K) : ∃ c : ℕ, Odd (orderOf (y ^ c)) ∧ (y ^ c ∈ K → y ∈ K) := by
  by_cases hm1 : m = 1
  · subst hm1
    exact ⟨0, by simp, fun _ => by simpa using hy⟩
  obtain ⟨e, n', hn'odd, hn⟩ := Nat.exists_eq_two_pow_mul_odd (n := orderOf y) (orderOf_pos y).ne'
  have hcop : Nat.Coprime (2 ^ e) m := Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hm)
  obtain ⟨k, hk0, hk1⟩ := Nat.chineseRemainder hcop 0 1
  have hk0' : 2 ^ e ∣ k := (Nat.modEq_zero_iff_dvd).1 hk0
  refine ⟨k, ?_, ?_⟩
  · obtain ⟨t, ht⟩ := hk0'
    have hpow : (y ^ k) ^ n' = 1 := by
      rw [← pow_mul, ht, show 2 ^ e * t * n' = orderOf y * t by rw [hn]; ring, pow_mul,
        pow_orderOf_eq_one, one_pow]
    exact hn'odd.of_dvd_nat (orderOf_dvd_of_pow_eq_one hpow)
  · intro hyk
    have hm2 : 2 ≤ m := by
      rcases hm with ⟨j, rfl⟩
      omega
    have hk1' : 1 ≤ k := by
      by_contra h
      have : k = 0 := by omega
      subst this
      have := hk1
      unfold Nat.ModEq at this
      rw [Nat.zero_mod, Nat.mod_eq_of_lt (by omega : 1 < m)] at this
      omega
    obtain ⟨s, hs⟩ := (Nat.modEq_iff_dvd' hk1').1 hk1.symm
    have hks : k = 1 + m * s := by omega
    have : y = y ^ k * ((y ^ m) ^ s)⁻¹ := by
      rw [hks, ← pow_mul, pow_add, pow_one]
      group
    rw [this]
    exact mul_mem hyk (inv_mem (pow_mem hy s))

theorem mem_of_odd_primary_parts [Finite G] {K : Subgroup G} {P : G → Prop}
    (hP : ∀ (y : G) (c : ℕ), P y → P (y ^ c))
    (h : ∀ (z : G) (r e : ℕ), r.Prime → r ≠ 2 → P z → orderOf z = r ^ e → z ∈ K) :
    ∀ y : G, P y → Odd (orderOf y) → y ∈ K := by
  intro y
  induction hn : orderOf y using Nat.strong_induction_on generalizing y with
  | _ n ih =>
  intro hPy hodd
  by_cases hn1 : n = 1
  · have : y = 1 := orderOf_eq_one_iff.1 (hn.trans hn1)
    rw [this]
    exact one_mem K
  · obtain ⟨r, hr, hrn⟩ := Nat.exists_prime_and_dvd hn1
    have hn0 : n ≠ 0 := by rw [← hn]; exact (orderOf_pos y).ne'
    have hr2 : r ≠ 2 := by
      rintro rfl
      have : Odd n := hn ▸ hodd
      exact (Nat.not_even_iff_odd.2 this) (even_iff_two_dvd.2 hrn)
    obtain ⟨k, n1, hn1r, hnk⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 r hr.ne_one
    have hk : 1 ≤ k := by
      by_contra hk0
      have : k = 0 := by omega
      subst this
      rw [pow_zero, one_mul] at hnk
      exact hn1r (hnk ▸ hrn)
    have hcop : Nat.Coprime (r ^ k) n1 := Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hr).2 hn1r)
    obtain ⟨c, hc1, hc0⟩ := Nat.chineseRemainder hcop 1 0
    obtain ⟨c', hc'0, hc'1⟩ := Nat.chineseRemainder hcop 0 1
    have hn1pos : 0 < n1 := by
      rcases Nat.eq_zero_or_pos n1 with h0 | h0
      · exfalso; subst h0; simp at hnk; exact hn0 hnk
      · exact h0
    have hn1lt : n1 < n := by
      rw [hnk]
      calc n1 = 1 * n1 := (one_mul n1).symm
        _ < r ^ k * n1 := by
          apply Nat.mul_lt_mul_of_pos_right _ hn1pos
          exact Nat.one_lt_pow (by omega) hr.one_lt
    have hdc : n1 ∣ c := (Nat.modEq_zero_iff_dvd).1 hc0
    have hdc' : r ^ k ∣ c' := (Nat.modEq_zero_iff_dvd).1 hc'0
    have hyr : (y ^ c) ^ (r ^ k) = 1 := by
      obtain ⟨t, ht⟩ := hdc
      rw [← pow_mul, ht, show n1 * t * r ^ k = orderOf y * t by rw [hn, hnk]; ring, pow_mul,
        pow_orderOf_eq_one, one_pow]
    have hord_r : orderOf (y ^ c) ∣ r ^ k := orderOf_dvd_of_pow_eq_one hyr
    obtain ⟨j, hj, hjeq⟩ := (Nat.dvd_prime_pow hr).1 hord_r
    have hyrK : y ^ c ∈ K := h (y ^ c) r j hr hr2 (hP y c hPy) hjeq
    have hy1 : (y ^ c') ^ n1 = 1 := by
      obtain ⟨t, ht⟩ := hdc'
      rw [← pow_mul, ht, show r ^ k * t * n1 = orderOf y * t by rw [hn, hnk]; ring, pow_mul,
        pow_orderOf_eq_one, one_pow]
    have hord_1 : orderOf (y ^ c') ∣ n1 := orderOf_dvd_of_pow_eq_one hy1
    have hodd1 : Odd (orderOf (y ^ c')) := by
      have : Odd n1 := by
        have : Odd n := hn ▸ hodd
        rw [hnk] at this
        exact (Nat.odd_mul.1 this).2
      exact this.of_dvd_nat hord_1
    have hy1K : y ^ c' ∈ K :=
      ih (orderOf (y ^ c')) (lt_of_le_of_lt (Nat.le_of_dvd hn1pos hord_1) hn1lt) (y ^ c') rfl
        (hP y c' hPy) hodd1
    have hsum : y = y ^ c * y ^ c' := by
      have hmod : c + c' ≡ 1 [MOD n] := by
        rw [hnk]
        have h1 : c + c' ≡ 1 [MOD r ^ k] := by
          calc c + c' ≡ 1 + 0 [MOD r ^ k] := Nat.ModEq.add hc1 hc'0
            _ = 1 := by simp
        have h2 : c + c' ≡ 1 [MOD n1] := by
          calc c + c' ≡ 0 + 1 [MOD n1] := Nat.ModEq.add hc0 hc'1
            _ = 1 := by simp
        exact (Nat.modEq_and_modEq_iff_modEq_mul hcop).1 ⟨h1, h2⟩
      have := (pow_eq_pow_iff_modEq (x := y)).2 (hn ▸ hmod)
      rw [pow_add] at this
      simpa using this.symm
    rw [hsum]
    exact mul_mem hyrK hy1K

@[expose] noncomputable def outerHom (L : Subgroup G) : Subgroup.normalizer (L : Set G) →* Outer ↥L :=
  (QuotientGroup.mk' (inner ↥L)).comp L.normalizerMonoidHom

theorem mem_sup_centralizer_of_outerHom_eq_one {L : Subgroup G} {w : Subgroup.normalizer (L : Set G)}
    (h : outerHom L w = 1) : (w : G) ∈ L ⊔ Subgroup.centralizer (L : Set G) := by
  have hin : L.normalizerMonoidHom w ∈ inner ↥L := (QuotientGroup.eq_one_iff _).1 h
  obtain ⟨c, hc⟩ := hin
  have hx : ∀ x : L, ((w : G) * x * (w : G)⁻¹ : G) = (c : G) * x * (c : G)⁻¹ := by
    intro x
    have h1 := congrArg (fun f : MulAut ↥L => ((f x : L) : G)) hc
    exact h1.symm
  have hcent : (c : G)⁻¹ * (w : G) ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hxL
    have : (w : G) * x * (w : G)⁻¹ = (c : G) * x * (c : G)⁻¹ := hx ⟨x, hxL⟩
    calc x * ((c : G)⁻¹ * (w : G))
        = (c : G)⁻¹ * ((c : G) * x * (c : G)⁻¹) * (w : G) := by group
      _ = (c : G)⁻¹ * ((w : G) * x * (w : G)⁻¹) * (w : G) := by rw [this]
      _ = ((c : G)⁻¹ * (w : G)) * x := by group
  have : (w : G) = (c : G) * ((c : G)⁻¹ * (w : G)) := by group
  rw [this]
  exact Subgroup.mul_mem_sup c.2 hcent

theorem outerHom_eq_one_of_mem_sup_centralizer {L : Subgroup G}
    {w : Subgroup.normalizer (L : Set G)}
    (h : (w : G) ∈ L ⊔ Subgroup.centralizer (L : Set G)) : outerHom L w = 1 := by
  have hmul := Subgroup.coe_mul_of_left_le_normalizer_right L (Subgroup.centralizer (L : Set G))
    (Subgroup.le_centralizer_iff.mpr le_rfl |>.trans (Subgroup.centralizer_le_normalizer _))
  have h' : (w : G) ∈ ((L ⊔ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) := h
  rw [hmul] at h'
  obtain ⟨l, hl, c, hc, hwlc⟩ := h'
  rw [outerHom, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  refine ⟨⟨l, hl⟩, ?_⟩
  ext x
  have h1 := Subgroup.mem_centralizer_iff.1 hc (x : G) x.2
  change l * x * l⁻¹ = (w : G) * x * (w : G)⁻¹
  rw [← hwlc]
  calc l * (x : G) * l⁻¹ = l * (c * x * c⁻¹) * l⁻¹ := by
        rw [show c * (x : G) * c⁻¹ = x by rw [← h1]; group]
    _ = l * c * x * (l * c)⁻¹ := by group

theorem exists_odd_pow_mem_of_commutator {L : Subgroup G}
    (hodd : Odd (Nat.card (commutator (Outer ↥L)))) {w a : G}
    (hw : w ∈ Subgroup.normalizer (L : Set G)) (ha : a ∈ Subgroup.normalizer (L : Set G)) :
    ∃ m : ℕ, Odd m ∧ ⁅w, a⁆ ^ m ∈ L ⊔ Subgroup.centralizer (L : Set G) := by
  have hwa : ⁅w, a⁆ ∈ Subgroup.normalizer (L : Set G) := by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hw ha) (inv_mem hw)) (inv_mem ha)
  have hmem : outerHom L ⟨⁅w, a⁆, hwa⟩ ∈ commutator (Outer ↥L) := by
    have : (⟨⁅w, a⁆, hwa⟩ : Subgroup.normalizer (L : Set G)) =
        ⁅(⟨w, hw⟩ : Subgroup.normalizer (L : Set G)), ⟨a, ha⟩⁆ := rfl
    rw [this, map_commutatorElement, commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  refine ⟨Nat.card (commutator (Outer ↥L)), hodd, ?_⟩
  have hpow : (outerHom L ⟨⁅w, a⁆, hwa⟩) ^ Nat.card (commutator (Outer ↥L)) = 1 := by
    have := pow_card_eq_one' (G := commutator (Outer ↥L)) (x := ⟨_, hmem⟩)
    exact congrArg Subtype.val this
  rw [← map_pow] at hpow
  have := mem_sup_centralizer_of_outerHom_eq_one hpow
  simpa using this

end JOut

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15
