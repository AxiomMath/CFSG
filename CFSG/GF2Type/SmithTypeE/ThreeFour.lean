module

public import CFSG.LargeExtraspecial.S14C12SmHolt
public import CFSG.LargeExtraspecial.S14C12SmGraph
public import CFSG.LargeExtraspecial.FS77PSU

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S14
  CFSG.Timmesfeld.Connectivity CFSG.RankThree.PartTwo.Sec21

variable {G : Type} [Group G] [Finite G]

theorem exists_isConj_orderOf_mul_eq_four_of_two_part [IsSimpleGroup G]
    (hAS : AschbacherSmithWideInput) (hDW : DW.DW37Statement) (S : Setting G)
    (hw : 5 ≤ S.width)
    (h2 : (Nat.card G).factorization 2 ≠ (S.width + 2) * (S.width + 2 - 1) / 2) :
    ∃ a b : G, IsConj S.z a ∧ IsConj S.z b ∧ orderOf (a * b) = 4 := by
  by_cases hW : ∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ = S.z
  · exfalso
    obtain ⟨e⟩ := hAS G S hw hW
    have h := FS77.factorization_card_timmesfeldPSU (m := S.width + 2) (by omega)
    rw [← Nat.card_congr e.toEquiv] at h
    exact h2 h
  · push Not at hW
    obtain ⟨g, hgQ, hne⟩ := hW
    by_contra hno
    have hcomm : ∀ x y : G, IsConj S.z x → x ∈ S.QG → IsConj S.z y → y ∈ S.QG →
        x * y = y * x := by
      intro x y hx hxQ hy hyQ
      by_contra hxy
      exact hno ⟨x, y, hx, hy, SmithQ.orderOf_mul_eq_four S hxQ hyQ
        (SmithQ.mul_self_eq_one_of_isConj S hx) (SmithQ.mul_self_eq_one_of_isConj S hy) hxy⟩
    obtain ⟨e⟩ := hDW G S g hw hgQ hne
      (SmithQ.isReducible_of_commute S (by omega) (isConj_iff.mpr ⟨g, rfl⟩) hgQ hne hcomm)
    have h := SmithQ.factorization_card_psl (S.width + 2)
    rw [← Nat.card_congr e.toEquiv] at h
    exact h2 h

theorem prime_dvd_card_centralizer_perm {p m : ℕ} (hp : p.Prime) (hm : 3 * p - 2 ≤ m)
    {g : Perm (Fin m)} (hg : orderOf g = 2) : p ∣ Nat.card (centralizer {g}) := by
  have hp2 : (orderOf g).Prime := hg ▸ Nat.prime_two
  obtain ⟨k, hk⟩ := Perm.cycleType_prime_order hp2
  rw [hg] at hk
  have hle := Perm.sum_cycleType_le g
  rw [hk, Multiset.sum_replicate, Fintype.card_fin, smul_eq_mul] at hle
  rw [Perm.nat_card_centralizer, hk]
  simp only [Multiset.sum_replicate, Multiset.prod_replicate, Fintype.card_fin, smul_eq_mul,
    Multiset.toFinset_replicate, Nat.add_one_ne_zero, ↓reduceIte, Finset.prod_singleton,
    Multiset.count_replicate_self]
  by_cases hkp : p ≤ k + 1
  · exact dvd_mul_of_dvd_right ((hp.dvd_factorial).mpr hkp) _
  · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left ((hp.dvd_factorial).mpr (by omega)) _) _

theorem sign_eq_one_of_orderOf_prime {m p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {h : Perm (Fin m)}
    (hh : orderOf h = p) : Perm.sign h = 1 := by
  have h1 : Perm.sign h ^ p = 1 := by rw [← map_pow, ← hh, pow_orderOf_eq_one, map_one]
  obtain ⟨c, hc⟩ := hp.odd_of_ne_two hp2
  rw [hc, pow_succ, pow_mul, Int.units_sq, one_pow, one_mul] at h1
  exact h1

theorem false_of_mulEquiv_alternatingGroup (S : Setting G) {p c : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (h2 : (Nat.card G).factorization 2 = c)
    (hbig : ¬ 2 ^ c ∣ Nat.factorial (3 * p - 3)) (hpM : ¬ p ∣ Nat.card S.M) {m : ℕ}
    (e : G ≃* alternatingGroup (Fin m)) : False := by
  have hc : 2 ^ c ∣ Nat.card G :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mpr (by omega)
  by_cases hm : m ≤ 3 * p - 3
  · have h1 : Nat.card G ∣ Nat.factorial (3 * p - 3) := by
      rw [Nat.card_congr e.toEquiv]
      refine (Subgroup.card_subgroup_dvd_card _).trans ?_
      rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
      exact Nat.factorial_dvd_factorial hm
    exact hbig (hc.trans h1)
  · push Not at hm
    have hσ : orderOf ((e S.z : alternatingGroup (Fin m)) : Perm (Fin m)) = 2 := by
      rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, S.orderOf_z]
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨h, hh⟩ := exists_prime_orderOf_dvd_card' p
      (prime_dvd_card_centralizer_perm hp (by omega) hσ)
    have hh' : orderOf (h : Perm (Fin m)) = p := by rw [Subgroup.orderOf_coe, hh]
    set h₁ : alternatingGroup (Fin m) :=
      ⟨h, Perm.mem_alternatingGroup.mpr (sign_eq_one_of_orderOf_prime hp hp2 hh')⟩ with hh₁
    have hcomm : h₁ * e S.z = e S.z * h₁ :=
      Subtype.ext (mem_centralizer_singleton_iff.mp h.2)
    have hy : e.symm h₁ ∈ S.M := by
      rw [mem_centralizer_singleton_iff]
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hcomm]
    have hord : orderOf (⟨e.symm h₁, hy⟩ : S.M) = p := by
      rw [Subgroup.orderOf_mk, MulEquiv.orderOf_eq, hh₁, Subgroup.orderOf_mk, hh']
    exact hpM (hord ▸ orderOf_dvd_natCard _)

theorem reach_conjugatesOf_of [IsSimpleGroup G]
    (hHolt : HoltUniqueFixedPointSimple) (S : Setting G)
    (hAlt : ∀ m : ℕ, ¬ Nonempty (G ≃* alternatingGroup (Fin m)))
    {d e : G} (hd : IsConj S.z d) (he : IsConj S.z e) (h4 : orderOf (d * e) = 4)
    {t : G} (ht : IsConj S.z t) : Reach (conjugatesOf S.z) S.z t := by
  by_contra hnt
  have hd2 := SmithQ.mul_self_eq_one_of_isConj S hd
  have he2 := SmithQ.mul_self_eq_one_of_isConj S he
  have hnonab : ∃ a b : G, a * b ≠ b * a := by
    refine ⟨d, e, fun hc => ?_⟩
    have h1 : (d * e) ^ 2 = 1 := by
      rw [_root_.sq, show d * e * (d * e) = d * (e * d) * e by group, ← hc,
        show d * (d * e) * e = (d * d) * (e * e) by group, hd2, he2, one_mul]
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [h4] at h2
    norm_num at h2
  rcases RankThree.Holt.holt_commutingComponent hHolt hnonab S.orderOf_z
      (SmithHolt.exists_sylow_twoCentral S) ⟨t, ht, hnt⟩ with ⟨H, hH⟩ | ⟨m, -, ⟨φ⟩⟩
  · exact SmithHolt.false_of_isStronglyEmbedded hH (S.orderOf_of_isConj hd)
      (S.orderOf_of_isConj he) h4
  · exact hAlt m ⟨φ⟩

theorem local_of_local_input [IsSimpleGroup G] (S : Setting G)
    (hLoc : ∀ x y : G, IsConj S.z x → IsConj S.z y → x ∈ S.M → y ∈ S.M → x ∉ S.QG →
      orderOf (x * y) ∈ ({1, 2, 3, 4} : Set ℕ) ∧
        (orderOf (x * y) = 4 → IsConj S.z ((x * y) ^ 2)))
    (x y : G) (hx : IsConj S.z x) (hy : IsConj S.z y) (hxM : x ∈ S.M) (hyM : y ∈ S.M) :
    orderOf (x * y) ∈ ({1, 2, 3, 4} : Set ℕ) ∧
      (orderOf (x * y) = 4 → IsConj S.z ((x * y) ^ 2)) := by
  by_cases hxQ : x ∈ S.QG
  · by_cases hyQ : y ∈ S.QG
    · exact SmithQ.orderOf_mul_mem_of_mem_QG S hxQ hyQ
    · obtain ⟨h1, h2⟩ := hLoc y x hy hx hyM hxM hyQ
      have hord : orderOf (y * x) = orderOf (x * y) := by
        rw [show y * x = MulAut.conj y (x * y) by rw [MulAut.conj_apply]; group,
          MulEquiv.orderOf_eq]
      rw [hord] at h1 h2
      refine ⟨h1, fun h4 => ?_⟩
      rw [show (x * y) ^ 2 = x * (y * x) ^ 2 * x⁻¹ by rw [_root_.sq, _root_.sq]; group]
      exact (h2 h4).trans (isConj_iff.mpr ⟨x, rfl⟩)
  · exact hLoc x y hx hy hxM hyM hxQ

theorem threeFour_of_local_path [IsSimpleGroup G]
    (hHolt : HoltUniqueFixedPointSimple) (S : Setting G)
    (hAlt : ∀ m : ℕ, ¬ Nonempty (G ≃* alternatingGroup (Fin m)))
    (hLoc : ∀ x y : G, IsConj S.z x → IsConj S.z y → x ∈ S.M → y ∈ S.M → x ∉ S.QG →
      orderOf (x * y) ∈ ({1, 2, 3, 4} : Set ℕ) ∧
        (orderOf (x * y) = 4 → IsConj S.z ((x * y) ^ 2)))
    (hPath : ∀ x w y : G, IsConj S.z x → IsConj S.z w → IsConj S.z y →
      Commute x S.z → Commute S.z w → Commute w y →
        ¬ Commute x w → ¬ Commute S.z y → ¬ Commute x y →
          ∃ v : G, IsConj S.z v ∧ Commute x v ∧ Commute v y)
    {d e : G} (hd : IsConj S.z d) (he : IsConj S.z e) (h4 : orderOf (d * e) = 4)
    (a b : G) (ha : IsConj S.z a) (hb : IsConj S.z b) :
    orderOf (a * b) ∈ ({1, 2, 3, 4} : Set ℕ) ∧
      (orderOf (a * b) = 4 → IsConj S.z ((a * b) ^ 2)) := by
  have hra := reach_conjugatesOf_of hHolt S hAlt hd he h4 ha
  have hrb := reach_conjugatesOf_of hHolt S hAlt hd he h4 hb
  obtain ⟨v, hv, hav, hvb⟩ :=
    SmithGraph.exists_common_of_reach hPath ha (reach_trans (reach_symm hra) hrb)
  exact SmithGraph.threeFour_of_common S (local_of_local_input S hLoc) ha hb hv hav hvb

end CFSG.GF2Type.SmithTypeE
