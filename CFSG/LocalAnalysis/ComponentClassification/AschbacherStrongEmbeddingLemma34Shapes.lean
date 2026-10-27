module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingLemma34TwoGroup
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3Shapes
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitTwoGroupCentralizer
public import CFSG.CharacterTheory.Semidihedral.CenterAndOrders

public section

namespace CFSG.ComponentClassification.AschbacherStrongEmbedding

namespace Lemma34

open CFSG.Open CFSG.ComponentClassification.AschbacherToolkit
open CFSG.ComponentClassification.AschbacherTheorem3
  (IsDihedralTwoGroup IsSemidihedralTwoGroup IsQuaternionTwoGroup
    isCyclic_or_isDihedral_of_hasDihedralGenerators isCyclic_or_isQuaternion_of_atMostOneInvolution)

variable {G : Type} [Group G]

section Models

theorem dihedral_sq_eq_one_of_mem_center {m : ℕ} {x : DihedralGroup m}
    (hx : x ∈ Subgroup.center (DihedralGroup m)) : x ^ 2 = 1 := by
  rcases x with i | i
  · have h := Subgroup.mem_center_iff.mp hx (DihedralGroup.sr 0)
    rw [DihedralGroup.sr_mul_r, DihedralGroup.r_mul_sr, zero_add, zero_sub] at h
    have hi : i = -i := DihedralGroup.sr.inj h
    rw [sq, DihedralGroup.r_mul_r, DihedralGroup.one_def]
    congr 1
    calc i + i = i + -i := by rw [← hi]
      _ = 0 := add_neg_cancel i
  · rw [sq, DihedralGroup.sr_mul_sr, sub_self, DihedralGroup.one_def]

theorem quaternion_sq_eq_one_of_mem_center {m : ℕ} (hm : 2 ≤ m) {x : QuaternionGroup m}
    (hx : x ∈ Subgroup.center (QuaternionGroup m)) : x ^ 2 = 1 := by
  rcases x with i | i
  · have h := Subgroup.mem_center_iff.mp hx (QuaternionGroup.xa 0)
    rw [QuaternionGroup.xa_mul_a, QuaternionGroup.a_mul_xa, zero_add, zero_sub] at h
    have hi : i = -i := QuaternionGroup.xa.inj h
    rw [sq, QuaternionGroup.a_mul_a, QuaternionGroup.one_def]
    congr 1
    calc i + i = i + -i := by rw [← hi]
      _ = 0 := add_neg_cancel i
  · exfalso
    have h := Subgroup.mem_center_iff.mp hx (QuaternionGroup.a 1)
    rw [QuaternionGroup.a_mul_xa, QuaternionGroup.xa_mul_a] at h
    have hi : i - 1 = i + 1 := QuaternionGroup.xa.inj h
    have h2 : (2 : ZMod (2 * m)) = 0 := by linear_combination -hi
    have h2' : ((2 : ℕ) : ZMod (2 * m)) = 0 := by exact_mod_cast h2
    rw [ZMod.natCast_eq_zero_iff] at h2'
    have := Nat.le_of_dvd (by norm_num) h2'
    omega

theorem semidihedral_sq_eq_one_of_mem_center {n : ℕ} (hn : 4 ≤ n) {x : SemidihedralGroup n}
    (hx : x ∈ Subgroup.center (SemidihedralGroup n)) : x ^ 2 = 1 := by
  rw [CFSG.Semidihedral.center_eq_zpowers n hn] at hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
    CFSG.Semidihedral.z_sq n (by omega), one_zpow]

theorem sq_eq_one_of_commute_of_mulEquiv {M : Type*} [Group M] {P : Subgroup G} (e : P ≃* M)
    (hM : ∀ x ∈ Subgroup.center M, x ^ 2 = 1) {w : G} (hw : w ∈ P)
    (hc : ∀ b ∈ P, Commute w b) : w ^ 2 = 1 := by
  have hcen : e ⟨w, hw⟩ ∈ Subgroup.center M := by
    rw [Subgroup.mem_center_iff]
    intro m
    obtain ⟨p, rfl⟩ := e.surjective m
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hc p p.2).eq.symm
  have h : (⟨w, hw⟩ : P) ^ 2 = 1 := e.injective (by rw [map_pow, hM _ hcen, map_one])
  simpa using congrArg Subtype.val h

theorem sq_eq_one_of_commute_of_dihedral {P : Subgroup G}
    (hP : IsDihedralTwoGroup P ∨ IsSemidihedralTwoGroup P) {w : G} (hw : w ∈ P)
    (hc : ∀ b ∈ P, Commute w b) : w ^ 2 = 1 := by
  rcases hP with ⟨n, -, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
  · exact sq_eq_one_of_commute_of_mulEquiv e (fun _ hx => dihedral_sq_eq_one_of_mem_center hx)
      hw hc
  · exact sq_eq_one_of_commute_of_mulEquiv e
      (fun _ hx => semidihedral_sq_eq_one_of_mem_center hn hx) hw hc

theorem sq_eq_one_of_commute_of_quaternion {P : Subgroup G} (hP : IsQuaternionTwoGroup P)
    {w : G} (hw : w ∈ P) (hc : ∀ b ∈ P, Commute w b) : w ^ 2 = 1 := by
  obtain ⟨n, hn, ⟨e⟩⟩ := hP
  have hm : 2 ≤ 2 ^ (n - 2) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (n - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  exact sq_eq_one_of_commute_of_mulEquiv e
    (fun _ hx => quaternion_sq_eq_one_of_mem_center hm hx) hw hc

end Models

variable [Finite G]

theorem card_le_two_of_lt_four {P : Subgroup G} (hP : IsPGroup 2 P) (h : Nat.card P < 4) :
    Nat.card P ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  rw [hk] at h ⊢
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · interval_cases k <;> norm_num
  · have : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
    omega

theorem exists_two_involutions {E : Subgroup G} (hE : 4 ≤ Nat.card E)
    (hsq : ∀ x ∈ E, x ^ 2 = 1) :
    ∃ u ∈ E, ∃ v ∈ E, orderOf u = 2 ∧ orderOf v = 2 ∧ u ≠ v := by
  have hcard : 2 < (E : Set G).ncard := by
    have : Nat.card E = (E : Set G).ncard := Nat.card_coe_set_eq _
    omega
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := (Set.two_lt_ncard_iff (Set.toFinite _)).mp hcard
  have hord : ∀ x ∈ E, x ≠ 1 → orderOf x = 2 := fun x hx hx1 => orderOf_eq_prime (hsq x hx) hx1
  by_cases ha1 : a = 1
  · subst ha1
    exact ⟨b, hb, c, hc, hord b hb (Ne.symm hab), hord c hc (Ne.symm hac), hbc⟩
  · by_cases hb1 : b = 1
    · subst hb1
      exact ⟨a, ha, c, hc, hord a ha ha1, hord c hc (Ne.symm hbc), hac⟩
    · exact ⟨a, ha, b, hb, hord a ha ha1, hord b hb hb1, hab⟩

theorem not_atMostOneInvolution_of_two_le_pRank {P : Subgroup G}
    (hr : 2 ≤ CFSG.Open.pRank 2 P) : ¬ AtMostOneInvolution P := by
  obtain ⟨E, hEP, ⟨-, hEsq⟩, hEcard⟩ :=
    CFSG.SectionRank.exists_pRank (p := 2) (by norm_num) P
  have hE4 : 4 ≤ Nat.card E := by
    rw [hEcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ CFSG.Open.pRank 2 P := Nat.pow_le_pow_right (by norm_num) hr
  obtain ⟨u, hu, v, hv, hu2, hv2, huv⟩ := exists_two_involutions hE4 hEsq
  intro h
  have := h ⟨u, hEP hu⟩ ⟨v, hEP hv⟩ (by rw [Subgroup.orderOf_mk]; exact hu2)
    (by rw [Subgroup.orderOf_mk]; exact hv2)
  exact huv (congrArg Subtype.val this)

theorem not_isCyclic_of_two_le_pRank {P : Subgroup G} (hr : 2 ≤ CFSG.Open.pRank 2 P) :
    ¬ IsCyclic P := fun _ =>
  not_atMostOneInvolution_of_two_le_pRank hr (atMostOneInvolution_of_isCyclic (P := P))

theorem isDihedral_of_card_four {P : Subgroup G} (hP : IsPGroup 2 P) (hcard : Nat.card P = 4)
    (hr : 2 ≤ CFSG.Open.pRank 2 P) : IsDihedralTwoGroup P := by
  obtain ⟨E, hEP, ⟨-, hEsq⟩, hEcard⟩ :=
    CFSG.SectionRank.exists_pRank (p := 2) (by norm_num) P
  have hE4 : 4 ≤ Nat.card E := by
    rw [hEcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ CFSG.Open.pRank 2 P := Nat.pow_le_pow_right (by norm_num) hr
  have hEeq : E = P := Subgroup.eq_of_le_of_card_ge hEP (by omega)
  have hsq : ∀ g : P, g ^ 2 = 1 := fun g =>
    Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hEsq g (hEeq ▸ g.2))
  obtain ⟨u, hu, v, hv, hu2, hv2, huv⟩ := exists_two_involutions hE4 hEsq
  set x : P := ⟨u, hEP hu⟩ with hx
  set y : P := ⟨v, hEP hv⟩ with hy
  have hx2 : orderOf x = 2 := by rw [hx, Subgroup.orderOf_mk]; exact hu2
  have hy2 : orderOf y = 2 := by rw [hy, Subgroup.orderOf_mk]; exact hv2
  have hxy : x ≠ y := fun h => huv (congrArg Subtype.val h)
  have hy1 : y ≠ 1 := fun h => by rw [h, orderOf_one] at hy2; omega
  have hyx : y ∉ Subgroup.zpowers x := by
    intro hmem
    rcases CFSG.RankTwoShapes.eq_one_or_eq_of_mem_zpowers hx2 hmem with h | h
    · exact hy1 h
    · exact hxy h.symm
  have hdih : HasDihedralGenerators P := by
    refine ⟨x, y, ?_, hsq y, ?_, hyx⟩
    · have hlt : Subgroup.zpowers x < Subgroup.zpowers x ⊔ Subgroup.zpowers y :=
        lt_of_le_of_ne le_sup_left fun h => hyx (h ▸ Subgroup.mem_sup_right
          (Subgroup.mem_zpowers y))
      have hcard_lt := Subgroup.card_lt_of_lt hlt
      rw [Nat.card_zpowers, hx2] at hcard_lt
      have hdvd := Subgroup.card_subgroup_dvd_card (Subgroup.zpowers x ⊔ Subgroup.zpowers y)
      rw [hcard] at hdvd
      have hle : Nat.card (Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup P) ≤ 4 :=
        Nat.le_of_dvd (by norm_num) hdvd
      have h4 : Nat.card (Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup P) = 4 := by
        interval_cases h : Nat.card (Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup P)
        · norm_num at hdvd
        · rfl
      exact Subgroup.eq_top_of_card_eq _ (h4.trans hcard.symm)
    · have hcomm := commute_of_sq_eq_one hsq y x
      have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hsq x)
      have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hsq y)
      rw [hyinv, hcomm, mul_assoc, ← sq, hsq y, mul_one, hxinv]
  rcases isCyclic_or_isDihedral_of_hasDihedralGenerators hP hdih with hc | hd
  · exact absurd hc (not_isCyclic_of_two_le_pRank hr)
  · exact hd

omit [Finite G] in
theorem exists_pow_not_mem_sq_mem {W : Subgroup G} {g : G} {n : ℕ} (hn : g ^ (2 ^ n) = 1)
    (hg : g ∉ W) : ∃ k : ℕ, g ^ (2 ^ k) ∉ W ∧ g ^ (2 ^ k) * g ^ (2 ^ k) ∈ W := by
  classical
  have hex : ∃ m, g ^ (2 ^ m) ∈ W := ⟨n, by rw [hn]; exact W.one_mem⟩
  set m₀ := Nat.find hex with hm₀
  have hm₀W : g ^ (2 ^ m₀) ∈ W := Nat.find_spec hex
  have hm₀0 : m₀ ≠ 0 := by
    intro h0
    rw [h0, pow_zero, pow_one] at hm₀W
    exact hg hm₀W
  refine ⟨m₀ - 1, Nat.find_min hex (by omega), ?_⟩
  rw [← pow_add, ← two_mul, ← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hm₀0)]
  exact hm₀W

omit [Finite G] in
theorem exists_pow_two_pow_eq_one {P : Subgroup G} (hP : IsPGroup 2 P) {g : G} (hg : g ∈ P) :
    ∃ n : ℕ, g ^ (2 ^ n) = 1 := by
  obtain ⟨n, hn⟩ := hP ⟨g, hg⟩
  exact ⟨n, by simpa using congrArg Subtype.val hn⟩

omit [Finite G] in
theorem exists_mem_sq_mem_of_not_le {A B : Subgroup G} (hA : IsPGroup 2 A) (h : ¬ A ≤ B) :
    ∃ v ∈ A, v ∉ B ∧ v * v ∈ B := by
  obtain ⟨g, hgA, hgB⟩ := Set.not_subset.mp h
  obtain ⟨n, hn⟩ := exists_pow_two_pow_eq_one hA hgA
  obtain ⟨k, hk, hk2⟩ := exists_pow_not_mem_sq_mem hn hgB
  exact ⟨g ^ (2 ^ k), A.pow_mem hgA _, hk, hk2⟩

theorem exists_involution_commute_of_not_sq {P : Subgroup G} (hP : IsPGroup 2 P) {x : G}
    (hxP : x ∈ P) (hx2 : orderOf x = 2) (hsq : ∀ r ∈ P, r * r ≠ x) (hcard : 4 ≤ Nat.card P) :
    ∃ y ∈ P, orderOf y = 2 ∧ y ≠ x ∧ Commute x y := by
  have hxx : x * x = 1 := by rw [← sq]; exact (orderOf_eq_prime_iff.mp hx2).1
  have hx1 : x ≠ 1 := (orderOf_eq_prime_iff.mp hx2).2
  let Q := P ⊓ Subgroup.centralizer ({x} : Set G)
  have hmemW : ∀ {w : G}, w ∈ Subgroup.zpowers x → w = 1 ∨ w = x := fun hw =>
    CFSG.RankTwoShapes.eq_one_or_eq_of_mem_zpowers hx2 hw
  obtain ⟨q₀, hq₀Q, hq₀W⟩ : ∃ q ∈ Q, q ∉ Subgroup.zpowers x := by
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    have hne : P ≠ ⊥ := by
      rintro rfl
      rw [Subgroup.card_bot] at hcard
      omega
    obtain ⟨c, hcP, hc2, hcc⟩ := exists_central_involution hP hne
    have hcQ : c ∈ Q := ⟨hcP, Subgroup.mem_centralizer_singleton_iff.mpr (hcc x hxP).eq⟩
    have hcx : c = x := by
      rcases hmemW (hcon c hcQ) with h | h
      · exact absurd h (orderOf_eq_prime_iff.mp hc2).2
      · exact h
    have hPW : P ≤ Subgroup.zpowers x := fun p hp => hcon p ⟨hp,
      Subgroup.mem_centralizer_singleton_iff.mpr (by rw [← hcx]; exact (hcc p hp).eq.symm)⟩
    have := Subgroup.card_le_of_le hPW
    rw [Nat.card_zpowers, hx2] at this
    omega
  obtain ⟨n, hn⟩ := exists_pow_two_pow_eq_one hP hq₀Q.1
  obtain ⟨k, hk, hk2⟩ := exists_pow_not_mem_sq_mem hn hq₀W
  set q := q₀ ^ (2 ^ k) with hq
  have hqQ : q ∈ Q := Q.pow_mem hq₀Q _
  have hqq : q * q = 1 := by
    rcases hmemW hk2 with h | h
    · exact h
    · exact absurd h (hsq q hqQ.1)
  have hq1 : q ≠ 1 := fun h => hk (h ▸ Subgroup.one_mem _)
  have hqx : q ≠ x := fun h => hk (h ▸ Subgroup.mem_zpowers x)
  refine ⟨q, hqQ.1, orderOf_eq_prime (by rw [sq]; exact hqq) hq1, hqx, ?_⟩
  exact (Subgroup.mem_centralizer_singleton_iff.mp hqQ.2).symm

theorem exists_commute_of_mem_normalizer {S I : Subgroup G} (hS : IsPGroup 2 S) (hIS : I ≤ S)
    (hI : I ≠ ⊥) {t : G} (htS : t ∈ S) (hnorm : t ∈ Subgroup.normalizer (I : Set G)) :
    ∃ z ∈ I, z ≠ 1 ∧ Commute t z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Q := S ⊓ Subgroup.normalizer (I : Set G)
  have hQ : IsPGroup 2 Q := hS.to_le inf_le_left
  have : Group.IsNilpotent Q := hQ.isNilpotent
  have hIQ : I ≤ Q := le_inf hIS Subgroup.le_normalizer
  have hnormal : (I.subgroupOf Q).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer inf_le_right
  have hne : I.subgroupOf Q ≠ ⊥ := by
    intro hbot
    apply hI
    rw [eq_bot_iff]
    intro x hx
    have hmem : (⟨x, hIQ hx⟩ : Q) ∈ I.subgroupOf Q := hx
    rw [hbot, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  have h := Group.IsNilpotent.inf_center_ne_bot_of_normal hne
  obtain ⟨q, hq, hq1⟩ := (Subgroup.bot_or_exists_ne_one _).resolve_left h
  refine ⟨q, hq.1, fun h1 => hq1 (Subtype.ext h1), ?_⟩
  have := Subgroup.mem_center_iff.mp hq.2 ⟨t, htS, hnorm⟩
  exact congrArg Subtype.val this

noncomputable def centralizerEquivInf (A : Subgroup G) {u : G} (hu : u ∈ A) :
    Subgroup.centralizer ({(⟨u, hu⟩ : A)} : Set A) ≃*
      (A ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G) where
  toFun p := ⟨((p : A) : G), (p : A).2, Subgroup.mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp p.2))⟩
  invFun q := ⟨⟨q, q.2.1⟩, Subgroup.mem_centralizer_singleton_iff.mpr
    (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp q.2.2))⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem two_le_pRank_inf_centralizer_of_orderOf_four {A : Subgroup G} (hA : IsPGroup 2 A)
    (hr : 2 ≤ CFSG.Open.pRank 2 A)
    (hnd : ¬ (IsDihedralTwoGroup A ∨ IsSemidihedralTwoGroup A)) {u : G} (hu : u ∈ A)
    (hu4 : orderOf u = 4) :
    2 ≤ CFSG.Open.pRank 2 (A ⊓ Subgroup.centralizer ({u} : Set G)) := by
  set Q := A ⊓ Subgroup.centralizer ({u} : Set G) with hQ
  have hQ2 : IsPGroup 2 Q := hA.to_le inf_le_left
  have huQ : u ∈ Q := ⟨hu, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hucen : ∀ b ∈ Q, Commute u b := fun b hb =>
    (Subgroup.mem_centralizer_singleton_iff.mp hb.2).symm
  have hz2 : orderOf (u ^ 2) = 2 := by
    rw [orderOf_pow' u (by norm_num), hu4]
    norm_num
  have hzQ : u ^ 2 ∈ Q := Q.pow_mem huQ 2
  by_cases hone : AtMostOneInvolution Q
  · exfalso
    rcases isCyclic_or_isQuaternion_of_atMostOneInvolution hQ2 hone with hc | hq
    ·
      have hcyc : IsCyclic (Subgroup.centralizer ({(⟨u, hu⟩ : A)} : Set A)) :=
        isCyclic_of_surjective (centralizerEquivInf A hu).symm.toMonoidHom
          (centralizerEquivInf A hu).symm.surjective
      have hinv : ¬ AtMostOneInvolution A := not_atMostOneInvolution_of_two_le_pRank hr
      have hu4' : orderOf (⟨u, hu⟩ : A) = 4 := by rw [Subgroup.orderOf_mk]; exact hu4
      exact hnd (cyclic_centralizer_order_four_shape hA hinv hu4' hcyc)
    · have := sq_eq_one_of_commute_of_quaternion hq huQ hucen
      rw [← orderOf_dvd_iff_pow_eq_one, hu4] at this
      norm_num at this
  ·
    obtain ⟨e, heQ, he2, hez⟩ : ∃ e ∈ Q, orderOf e = 2 ∧ e ≠ u ^ 2 := by
      by_contra hcon
      simp only [not_exists, not_and, not_not] at hcon
      apply hone
      intro s s' hs hs'
      have h1 := hcon s s.2 (by rw [Subgroup.orderOf_coe]; exact hs)
      have h2 := hcon s' s'.2 (by rw [Subgroup.orderOf_coe]; exact hs')
      exact Subtype.ext (h1.trans h2.symm)
    have hee : e * e = 1 := by rw [← sq]; exact (orderOf_eq_prime_iff.mp he2).1
    have hzz : u ^ 2 * u ^ 2 = 1 := by rw [← sq]; exact (orderOf_eq_prime_iff.mp hz2).1
    have hez' : Commute e (u ^ 2) := ((hucen e heQ).pow_left 2).symm
    let E := commutingPairSubgroup e (u ^ 2) hee hzz hez'
    refine CFSG.SectionRank.le_pRank (by norm_num) (E := E) ?_ ?_
      (commutingPairSubgroup_card (orderOf_eq_prime_iff.mp he2).2
        (orderOf_eq_prime_iff.mp hz2).2 hez)
    · intro x hx
      rcases mem_commutingPairSubgroup.mp hx with rfl | rfl | rfl | rfl
      · exact Q.one_mem
      · exact heQ
      · exact hzQ
      · exact Q.mul_mem heQ hzQ
    · exact ⟨isMulCommutative_of_sq_eq_one fun k hk => commutingPairSubgroup_sq hk,
        fun k hk => commutingPairSubgroup_sq hk⟩

noncomputable def conjAutOfMemNormalizer (B : Subgroup G) {y : G}
    (hy : y ∈ Subgroup.normalizer (B : Set G)) : MulAut B where
  toFun b := ⟨y * b * y⁻¹, (Subgroup.mem_normalizer_iff.mp hy b).mp b.2⟩
  invFun b := ⟨y⁻¹ * b * y, by
    have h := (Subgroup.mem_normalizer_iff.mp hy (y⁻¹ * b * y)).mpr
    apply h
    simpa only [mul_assoc, mul_inv_cancel, mul_one, mul_inv_cancel_left] using b.2⟩
  left_inv b := Subtype.ext (by simp only [mul_assoc, inv_mul_cancel, mul_one,
    inv_mul_cancel_left])
  right_inv b := Subtype.ext (by simp only [mul_assoc, mul_inv_cancel, mul_one,
    mul_inv_cancel_left])
  map_mul' a b := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem isDihedral_of_involution_small_centralizer {B : Subgroup G} (hB : IsPGroup 2 B)
    (hr : 2 ≤ CFSG.Open.pRank 2 B) {y : G} (hyy : y * y = 1)
    (hyN : y ∈ Subgroup.normalizer (B : Set G))
    (hC : Nat.card (B ⊓ Subgroup.centralizer ({y} : Set G) : Subgroup G) ≤ 2) :
    IsDihedralTwoGroup B := by
  set β := conjAutOfMemNormalizer B hyN with hβ
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_left hyy
  have hβ2 : β ^ 2 = 1 := by
    ext b
    change y * (y * b * y⁻¹) * y⁻¹ = b
    rw [hyinv]
    calc y * (y * b * y) * y = (y * y) * b * (y * y) := by group
      _ = b := by rw [hyy, one_mul, mul_one]
  have hfix : Nat.card (fixedSubgroup β) ≤ 2 := by
    refine le_trans ?_ hC
    rw [← Subgroup.card_map_of_injective B.subtype_injective]
    apply Subgroup.card_le_of_le
    rintro _ ⟨b, hb, rfl⟩
    have hb' : y * b * y⁻¹ = b := congrArg Subtype.val (mem_fixedSubgroup.mp hb)
    refine ⟨b.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    calc (b : G) * y = y * b * y⁻¹ * y := by rw [hb']
      _ = y * b := by group
  rcases involutory_automorphism_shape hB β hβ2 hfix with h | h
  · exact absurd h (not_atMostOneInvolution_of_two_le_pRank hr)
  · rcases isCyclic_or_isDihedral_of_hasDihedralGenerators hB h with hc | hd
    · exact absurd hc (not_isCyclic_of_two_le_pRank hr)
    · exact hd

end Lemma34

end CFSG.ComponentClassification.AschbacherStrongEmbedding
