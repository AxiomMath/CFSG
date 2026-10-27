module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingCentralCase
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.ComponentClassification.AschbacherStrongEmbedding

namespace Lemma34

open CFSG.Open

variable {G : Type*} [Group G] [Finite G]

theorem four_le_card_of_two_le_pRank {A : Subgroup G} (h : 2 ≤ CFSG.Open.pRank 2 A) :
    4 ≤ Nat.card A := by
  obtain ⟨E, hE, -, hEcard⟩ := CFSG.SectionRank.exists_pRank (p := 2) (by norm_num) A
  have h4 : 4 ≤ Nat.card E := by
    rw [hEcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ CFSG.Open.pRank 2 A := Nat.pow_le_pow_right (by norm_num) h
  exact h4.trans (Subgroup.card_le_of_le hE)

theorem exists_central_involution {A : Subgroup G} (hA : IsPGroup 2 A) (hne : A ≠ ⊥) :
    ∃ w ∈ A, orderOf w = 2 ∧ ∀ b ∈ A, Commute w b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial A := (Subgroup.bot_or_nontrivial A).resolve_left hne
  have hZ : Nontrivial (Subgroup.center A) := hA.center_nontrivial
  have hZp : IsPGroup 2 (Subgroup.center A) := hA.to_subgroup _
  obtain ⟨k, hk⟩ := hZp.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    exact (Finite.one_lt_card_iff_nontrivial.mpr hZ).ne' hk
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center A) 2
    (by rw [hk]; exact dvd_pow_self 2 hk0)
  refine ⟨((w : A) : G), (w : A).property, ?_, fun b hb => ?_⟩
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    exact hw
  · have h := Subgroup.mem_center_iff.mp w.property ⟨b, hb⟩
    exact (congrArg Subtype.val h).symm

theorem two_le_pRank_inf_centralizer {A : Subgroup G} (hA : IsPGroup 2 A)
    (hr : 2 ≤ CFSG.Open.pRank 2 A) {a : G} (ha : a ∈ A) (ha2 : orderOf a = 2) :
    2 ≤ CFSG.Open.pRank 2 (A ⊓ Subgroup.centralizer ({a} : Set G)) := by
  by_cases hc : ∀ b ∈ A, Commute a b
  · have heq : A ⊓ Subgroup.centralizer ({a} : Set G) = A := by
      refine inf_eq_left.mpr fun b hb => ?_
      exact Subgroup.mem_centralizer_singleton_iff.mpr (hc b hb).eq.symm
    rw [heq]
    exact hr
  · obtain ⟨b, hb, hab⟩ : ∃ b ∈ A, ¬ Commute a b := by
      by_contra h
      exact hc fun b hb => not_not.mp fun hn => h ⟨b, hb, hn⟩
    have hne : A ≠ ⊥ := fun h => by rw [h] at ha; exact hab (by
      rw [Subgroup.mem_bot.mp ha]; exact Commute.one_left b)
    obtain ⟨w, hwA, hw2, hwc⟩ := exists_central_involution hA hne
    have hwa : a ≠ w := fun h => hab (h ▸ hwc b hb)
    have haa : a * a = 1 := by simpa only [pow_two] using (orderOf_eq_prime_iff.mp ha2).1
    have hww : w * w = 1 := by simpa only [pow_two] using (orderOf_eq_prime_iff.mp hw2).1
    have ha1 : a ≠ 1 := (orderOf_eq_prime_iff.mp ha2).2
    have hw1 : w ≠ 1 := (orderOf_eq_prime_iff.mp hw2).2
    let E := commutingPairSubgroup a w haa hww (hwc a ha).symm
    refine CFSG.SectionRank.le_pRank (by norm_num) (E := E) ?_ ?_
      (commutingPairSubgroup_card ha1 hw1 hwa)
    · intro x hx
      have hwa' : Commute a w := (hwc a ha).symm
      rcases mem_commutingPairSubgroup.mp hx with rfl | rfl | rfl | rfl
      · exact (A ⊓ _).one_mem
      · exact ⟨ha, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
      · exact ⟨hwA, Subgroup.mem_centralizer_singleton_iff.mpr hwa'.eq.symm⟩
      · exact ⟨A.mul_mem ha hwA, Subgroup.mem_centralizer_singleton_iff.mpr
          ((Commute.refl a).mul_left hwa'.symm).eq⟩
    · exact ⟨isMulCommutative_of_sq_eq_one fun k hk => commutingPairSubgroup_sq hk,
        fun k hk => commutingPairSubgroup_sq hk⟩

theorem four_le_card_inf_centralizer {A : Subgroup G} (hA : IsPGroup 2 A)
    (hr : 2 ≤ CFSG.Open.pRank 2 A) {a : G} (ha : a ∈ A) (ha2 : orderOf a = 2) :
    4 ≤ Nat.card (A ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) :=
  four_le_card_of_two_le_pRank (two_le_pRank_inf_centralizer hA hr ha ha2)

section Twisted

variable {P : Subgroup G} {t : G}

omit [Finite G] in
theorem exists_twisted_range (hP : ∀ x ∈ P, ∀ y ∈ P, Commute x y) (ht : t * t = 1)
    (hnorm : ∀ p ∈ P, t * p * t ∈ P) :
    ∃ R : Subgroup G, R ≤ P ∧
      Nat.card (P ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) * Nat.card R =
        Nat.card P ∧
      (∀ j ∈ R, t * j * t = j⁻¹) ∧ ∀ j ∈ R, ∃ y ∈ P, j = y⁻¹ * (t * y * t) := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_left ht
  have key : ∀ p q : G, t * (p * q) * t = (t * p * t) * (t * q * t) := by
    intro p q
    calc t * (p * q) * t = t * p * (t * t) * q * t := by rw [ht]; group
      _ = (t * p * t) * (t * q * t) := by group
  let ψ : P →* P :=
    { toFun := fun p => ⟨(p : G)⁻¹ * (t * p * t), P.mul_mem (P.inv_mem p.2) (hnorm _ p.2)⟩
      map_one' := by
        apply Subtype.ext
        simp only [Subgroup.coe_one, inv_one, mul_one, ht]
      map_mul' := by
        intro p q
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        rw [key, mul_inv_rev]
        have h1 : Commute ((q : G)⁻¹) ((p : G)⁻¹ * (t * p * t)) :=
          (hP _ (P.inv_mem q.2) _ (P.mul_mem (P.inv_mem p.2) (hnorm _ p.2)))
        calc (q : G)⁻¹ * (p : G)⁻¹ * ((t * p * t) * (t * q * t))
            = (q : G)⁻¹ * ((p : G)⁻¹ * (t * p * t)) * (t * q * t) := by group
          _ = ((p : G)⁻¹ * (t * p * t)) * (q : G)⁻¹ * (t * q * t) := by rw [h1.eq]
          _ = (p : G)⁻¹ * (t * p * t) * ((q : G)⁻¹ * (t * q * t)) := by group }
  refine ⟨ψ.range.map P.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
  · have hker : Nat.card ψ.ker =
        Nat.card (P ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) := by
      have heq : ψ.ker.map P.subtype = P ⊓ Subgroup.centralizer ({t} : Set G) := by
        ext x
        constructor
        · rintro ⟨p, hp, rfl⟩
          have h1 : (p : G)⁻¹ * (t * p * t) = 1 := congrArg Subtype.val hp
          have h2 : t * p * t = p := by
            have := congrArg ((p : G) * ·) h1
            simpa only [mul_inv_cancel_left, mul_one] using this
          refine ⟨p.property, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
          calc (p : G) * t = t * p * t * t := by rw [h2]
            _ = t * p := by rw [mul_assoc, ht, mul_one]
        · rintro ⟨hxP, hxC⟩
          refine ⟨⟨x, hxP⟩, ?_, rfl⟩
          apply Subtype.ext
          change x⁻¹ * (t * x * t) = 1
          have hxC' : x * t = t * x := Subgroup.mem_centralizer_singleton_iff.mp hxC
          rw [← hxC', mul_assoc, ht, mul_one, inv_mul_cancel]
      rw [← heq, Subgroup.card_map_of_injective P.subtype_injective]
    rw [← hker, Subgroup.card_map_of_injective P.subtype_injective]
    exact Subgroup.card_ker_mul_card_range ψ
  · rintro _ ⟨j, ⟨p, rfl⟩, rfl⟩
    change t * ((p : G)⁻¹ * (t * p * t)) * t = ((p : G)⁻¹ * (t * p * t))⁻¹
    have hrhs : ((p : G)⁻¹ * (t * p * t))⁻¹ = t * (p : G)⁻¹ * t * p := by
      rw [mul_inv_rev, mul_inv_rev, mul_inv_rev, htinv, inv_inv]
      group
    rw [hrhs]
    calc t * ((p : G)⁻¹ * (t * p * t)) * t = t * (p : G)⁻¹ * t * p * (t * t) := by group
      _ = t * (p : G)⁻¹ * t * p := by rw [ht, mul_one]
  · rintro _ ⟨j, ⟨p, rfl⟩, rfl⟩
    exact ⟨p, p.property, rfl⟩

omit [Finite G] in
theorem eq_of_mem_twisted {R : Subgroup G} (hRP : R ≤ P)
    (hinv : ∀ j ∈ R, t * j * t = j⁻¹) {z : G}
    (hfix : ∀ p ∈ P, t * p * t = p → p = 1 ∨ p = z) {j : G} (hj : j ∈ R)
    (hj2 : orderOf j = 2) : j = z := by
  have hjj : j⁻¹ = j := inv_eq_of_mul_eq_one_left (by
    simpa only [pow_two] using (orderOf_eq_prime_iff.mp hj2).1)
  rcases hfix j (hRP hj) (by rw [hinv j hj, hjj]) with h | h
  · exact absurd h (orderOf_eq_prime_iff.mp hj2).2
  · exact h

omit [Finite G] in
theorem card_inf_centralizer_eq_two (ht : t * t = 1) {z : G} (hz : z ∈ P) (hz1 : z ≠ 1)
    (hzt : t * z * t = z) (hfix : ∀ p ∈ P, t * p * t = p → p = 1 ∨ p = z) :
    Nat.card (P ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) = 2 := by
  have htz : z * t = t * z := by
    calc z * t = t * z * t * t := by rw [hzt]
      _ = t * z := by rw [mul_assoc, ht, mul_one]
  have hfix' : ∀ p ∈ P, p * t = t * p → p = 1 ∨ p = z := fun p hp hpt =>
    hfix p hp (by rw [← hpt, mul_assoc, ht, mul_one])
  have hz2 : z * z = 1 := by
    rcases hfix' (z * z) (P.mul_mem hz hz) (by
      rw [mul_assoc, htz, ← mul_assoc, htz, mul_assoc]) with h | h
    · exact h
    · exact absurd (mul_left_cancel (h.trans (mul_one z).symm)) hz1
  have heq : P ⊓ Subgroup.centralizer ({t} : Set G) = Subgroup.zpowers z := by
    apply le_antisymm
    · rintro p ⟨hp, hpc⟩
      rcases hfix' p hp (Subgroup.mem_centralizer_singleton_iff.mp hpc) with rfl | rfl
      · exact Subgroup.one_mem _
      · exact Subgroup.mem_zpowers _
    · rw [Subgroup.zpowers_le]
      exact ⟨hz, Subgroup.mem_centralizer_singleton_iff.mpr htz⟩
  rw [heq, Nat.card_zpowers]
  exact orderOf_eq_prime (by rw [pow_two]; exact hz2) hz1

theorem exists_conj_eq_mul_of_card (hP2 : IsPGroup 2 P)
    (hP : ∀ x ∈ P, ∀ y ∈ P, Commute x y) (ht : t * t = 1) (hnorm : ∀ p ∈ P, t * p * t ∈ P)
    {z : G} (hz : z ∈ P) (hz1 : z ≠ 1) (hzt : t * z * t = z)
    (hfix : ∀ p ∈ P, t * p * t = p → p = 1 ∨ p = z) (hcard : 4 ≤ Nat.card P) :
    ∃ y ∈ P, y⁻¹ * t * y = t * z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R, hRP, hcardR, hRinv, hRform⟩ := exists_twisted_range hP ht hnorm
  rw [card_inf_centralizer_eq_two ht hz hz1 hzt hfix] at hcardR
  have hR2 : IsPGroup 2 R := hP2.to_le hRP
  obtain ⟨k, hk⟩ := hR2.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    omega
  obtain ⟨j, hj⟩ := exists_prime_orderOf_dvd_card' (G := R) 2 (by rw [hk]; exact dvd_pow_self 2 hk0)
  have hjz : (j : G) = z :=
    eq_of_mem_twisted hRP hRinv hfix j.property ((Subgroup.orderOf_coe j).trans hj)
  obtain ⟨y, hyP, hyj⟩ := hRform j j.property
  refine ⟨y, hyP, ?_⟩
  have htz : z * t = t * z := by
    calc z * t = t * z * t * t := by rw [hzt]
      _ = t * z := by rw [mul_assoc, ht, mul_one]
  have h1 : y⁻¹ * (t * y * t) = z := hyj.symm.trans hjz
  calc y⁻¹ * t * y = y⁻¹ * (t * y * t) * t := by
        rw [show y⁻¹ * (t * y * t) * t = y⁻¹ * t * y * (t * t) by group, ht, mul_one]
    _ = z * t := by rw [h1]
    _ = t * z := htz

theorem card_eq_four_of_fixed_two (hP2 : IsPGroup 2 P)
    (hP : ∀ x ∈ P, ∀ y ∈ P, Commute x y) (ht : t * t = 1) (hnorm : ∀ p ∈ P, t * p * t ∈ P)
    {z : G} (hz : z ∈ P) (hz1 : z ≠ 1) (hzt : t * z * t = z)
    (hfix : ∀ p ∈ P, t * p * t = p → p = 1 ∨ p = z) (hr : 2 ≤ CFSG.Open.pRank 2 P) :
    Nat.card P = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h4 := four_le_card_of_two_le_pRank hr
  obtain ⟨E, hEP, ⟨-, hEsq⟩, hEcard⟩ :=
    CFSG.SectionRank.exists_pRank (p := 2) (by norm_num) P
  have hE4 : 4 ≤ Nat.card E := by
    rw [hEcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ CFSG.Open.pRank 2 P := Nat.pow_le_pow_right (by norm_num) hr
  obtain ⟨e, heE, he⟩ : ∃ e ∈ E, e ∉ ({1, z} : Set G) := by
    by_contra hcon
    have hsub : (E : Set G) ⊆ {1, z} := fun x hx => by
      by_contra h
      exact hcon ⟨x, hx, h⟩
    have h1 : Nat.card E ≤ ({1, z} : Set G).ncard := by
      rw [← Nat.card_coe_set_eq]
      exact Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 : ({1, z} : Set G).ncard ≤ 2 := (Set.ncard_insert_le _ _).trans (by simp)
    omega
  have he1 : e ≠ 1 := fun h => he (by simp [h])
  have hez : e ≠ z := fun h => he (by simp [h])
  have hee : e * e = 1 := by rw [← pow_two]; exact hEsq e heE
  have heinv : e⁻¹ = e := inv_eq_of_mul_eq_one_left hee
  have heP : e ∈ P := hEP heE
  have hte : t * e * t = e * z := by
    have hf : t * (e * (t * e * t)) * t = e * (t * e * t) := by
      calc t * (e * (t * e * t)) * t = (t * e * t) * e * (t * t) := by group
        _ = (t * e * t) * e := by rw [ht, mul_one]
        _ = e * (t * e * t) := ((hP _ (hnorm e heP) _ heP).eq)
    rcases hfix _ (P.mul_mem heP (hnorm e heP)) hf with h | h
    · exfalso
      have h' : t * e * t = e := by
        have := eq_inv_of_mul_eq_one_right h
        rwa [heinv] at this
      rcases hfix e heP h' with h'' | h''
      · exact he1 h''
      · exact hez h''
    · have := congrArg (e⁻¹ * ·) h
      simp only [inv_mul_cancel_left] at this
      rw [heinv] at this
      exact this
  by_contra hne
  have h8 : 8 ≤ Nat.card P := by
    obtain ⟨k, hk⟩ := hP2.exists_card_eq
    rw [hk] at h4 hne ⊢
    rcases Nat.lt_or_ge k 3 with hk3 | hk3
    · interval_cases k <;> simp_all
    · calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk3
  obtain ⟨R, hRP, hcardR, hRinv, -⟩ := exists_twisted_range hP ht hnorm
  rw [card_inf_centralizer_eq_two ht hz hz1 hzt hfix] at hcardR
  have hR2 : IsPGroup 2 R := hP2.to_le hRP
  obtain ⟨j, hjR, hj⟩ : ∃ j ∈ R, j ^ 2 ≠ 1 := by
    by_contra hcon
    have hsub : (R : Set G) ⊆ {1, z} := by
      intro x hx
      by_cases hx1 : x = 1
      · simp [hx1]
      · have hx2 : x ^ 2 = 1 := by
          by_contra h
          exact hcon ⟨x, hx, h⟩
        have := eq_of_mem_twisted hRP hRinv hfix hx (orderOf_eq_prime hx2 hx1)
        simp [this]
    have h1 : Nat.card R ≤ ({1, z} : Set G).ncard := by
      rw [← Nat.card_coe_set_eq]
      exact Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 : ({1, z} : Set G).ncard ≤ 2 := (Set.ncard_insert_le _ _).trans (by simp)
    omega
  obtain ⟨n, hn⟩ := hR2 ⟨j, hjR⟩
  have hdvd : orderOf j ∣ 2 ^ n := by
    rw [← Subgroup.orderOf_mk j hjR]
    exact orderOf_dvd_of_pow_eq_one hn
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hm2 : 2 ≤ m := by
    by_contra hlt
    apply hj
    rw [← orderOf_dvd_iff_pow_eq_one, hm]
    have : 2 ^ m ∣ 2 ^ 1 := Nat.pow_dvd_pow 2 (by omega)
    simpa using this
  set r := j ^ (2 ^ (m - 2)) with hr_def
  have hrR : r ∈ R := R.pow_mem hjR _
  have hdvd' : 2 ^ (m - 2) ∣ orderOf j := by
    rw [hm]; exact Nat.pow_dvd_pow 2 (by omega)
  have hr4 : orderOf r = 4 := by
    rw [hr_def, orderOf_pow_of_dvd (by positivity) hdvd', hm]
    have : 2 ^ m = 2 ^ (m - 2) * 4 := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
      congr 1
      omega
    rw [this, Nat.mul_div_cancel_left _ (by positivity)]
  have hr2 : orderOf (r ^ 2) = 2 := by
    rw [orderOf_pow_of_dvd (by norm_num) (by rw [hr4]; norm_num), hr4]
  have hrz : r ^ 2 = z := eq_of_mem_twisted hRP hRinv hfix (R.pow_mem hrR 2) hr2
  have hrP : r ∈ P := hRP hrR
  have htr : t * r * t = r⁻¹ := hRinv r hrR
  have hp : t * (r * e) * t = r * e := by
    calc t * (r * e) * t = (t * r * t) * (t * e * t) := by
          calc t * (r * e) * t = t * r * (t * t) * e * t := by rw [ht]; group
            _ = (t * r * t) * (t * e * t) := by group
      _ = r⁻¹ * (e * r ^ 2) := by rw [htr, hte, hrz]
      _ = e * (r⁻¹ * r ^ 2) := by
          rw [← mul_assoc, (hP _ (P.inv_mem hrP) _ heP).eq, mul_assoc]
      _ = r * e := by rw [pow_two, inv_mul_cancel_left, (hP _ heP _ hrP).eq]
  rcases hfix _ (P.mul_mem hrP heP) hp with h | h
  · have he' : e = r⁻¹ := eq_inv_of_mul_eq_one_right h
    have : orderOf e = 4 := by rw [he', orderOf_inv, hr4]
    have h2 : orderOf e ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hee)
    rw [this] at h2
    norm_num at h2
  · have he' : e = r := by
      have h' : r * e = r * r := by rw [h, ← hrz, pow_two]
      exact mul_left_cancel h'
    have : orderOf e = 4 := by rw [he', hr4]
    have h2 : orderOf e ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hee)
    rw [this] at h2
    norm_num at h2

end Twisted

end Lemma34

end CFSG.ComponentClassification.AschbacherStrongEmbedding
