module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitTwoGroupShapes

public section

namespace CFSG.ComponentClassification.AschbacherToolkit

namespace CyclicCentralizer

open CFSG.RankTwoShapes

variable {G : Type*} [Group G]

theorem exists_eq_zpowers_of_isCyclic {H : Subgroup G} (hH : IsCyclic H) :
    ∃ g : G, H = Subgroup.zpowers g := by
  obtain ⟨⟨g, hg⟩, hgen⟩ := (isCyclic_iff_exists_zpowers_eq_top (α := H)).mp hH
  refine ⟨g, ?_⟩
  have h1 := congrArg (Subgroup.map H.subtype) hgen
  rw [MonoidHom.map_zpowers, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h1
  exact h1.symm

theorem exists_orderOf_eq_two_pow (hG : IsPGroup 2 G) (g : G) : ∃ m : ℕ, orderOf g = 2 ^ m := by
  obtain ⟨k, hk⟩ := hG g
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk)
  exact ⟨m, hm⟩

theorem conj_eq_of_principal {m : ℕ} {r w a : G}
    (hwr : w * r * w⁻¹ = r ^ (1 + 2 ^ (m - 1))) (ha : a ∈ Subgroup.zpowers r)
    (ha2 : a ^ 2 ^ (m - 1) = 1) : w * a * w⁻¹ = a := by
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  rw [← conj_zpow, hwr, pow_add, pow_one, (Commute.self_pow r _).mul_zpow, ← zpow_natCast,
    ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha2, mul_one]

theorem conj_cases {m : ℕ} (hm : 3 ≤ m) {r w : G} (hr : orderOf r = 2 ^ m)
    (hw : w * r * w⁻¹ ∈ Subgroup.zpowers r) (hw2 : w ^ 2 * r = r * w ^ 2) :
    w * r * w⁻¹ = r ∨ w * r * w⁻¹ = r⁻¹ ∨ w * r * w⁻¹ = r ^ (1 + 2 ^ (m - 1)) ∨
      w * r * w⁻¹ = r ^ (2 ^ (m - 1) - 1) := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hw
  have hsq : r ^ (k ^ 2) = r := by
    have h1 : w ^ 2 * r * (w ^ 2)⁻¹ = r := by rw [hw2]; group
    calc r ^ (k ^ 2) = (r ^ k) ^ k := by rw [← zpow_mul, sq]
      _ = (w * r * w⁻¹) ^ k := by rw [hk]
      _ = w * r ^ k * w⁻¹ := by rw [conj_zpow]
      _ = w * (w * r * w⁻¹) * w⁻¹ := by rw [hk]
      _ = w ^ 2 * r * (w ^ 2)⁻¹ := by rw [sq]; group
      _ = r := h1
  have hmod : k ^ 2 ≡ 1 [ZMOD 2 ^ m] := by
    have := (zpow_eq_zpow_iff_modEq (x := r) (m := k ^ 2) (n := 1)).mp (by rw [hsq, zpow_one])
    rwa [hr, Nat.cast_pow, Nat.cast_ofNat] at this
  have hcast : ∀ j : ℤ, k ≡ j [ZMOD 2 ^ m] → w * r * w⁻¹ = r ^ j := by
    intro j hj
    rw [← hk]
    apply zpow_eq_zpow_iff_modEq.mpr
    rwa [hr, Nat.cast_pow, Nat.cast_ofNat]
  have hpos : 1 ≤ 2 ^ (m - 1) := Nat.one_le_two_pow
  rcases sq_eq_one_mod_two_pow hm hmod with h | h | h | h
  · left
    simpa using hcast 1 h
  · right; left
    simpa using hcast (-1) h
  · right; right; left
    rw [hcast _ h, ← zpow_natCast]
    push_cast
    rfl
  · right; right; right
    rw [hcast _ h, ← zpow_natCast]
    congr 1
    push_cast [Nat.cast_sub hpos]
    ring

theorem fixed_cases {m : ℕ} (hm : 3 ≤ m) {r w : G} (hr : orderOf r = 2 ^ m)
    (hw : w * r * w⁻¹ = r⁻¹ ∨ w * r * w⁻¹ = r ^ (2 ^ (m - 1) - 1)) {g : G}
    (hg : g ∈ Subgroup.zpowers r) (hgw : w * g * w⁻¹ = g) : g = 1 ∨ g = r ^ 2 ^ (m - 1) := by
  have hfin : IsOfFinOrder r := orderOf_pos_iff.mp (by rw [hr]; positivity)
  obtain ⟨j, rfl⟩ := (Submonoid.mem_powers_iff g r).mp ((hfin.mem_powers_iff_mem_zpowers).mpr hg)
  apply pow_eq_one_or_of_two_pow_dvd (by omega) hr
  have hconj : w * r ^ j * w⁻¹ = (w * r * w⁻¹) ^ j := conj_pow.symm
  rw [hconj] at hgw
  have e1 : 2 ^ m = 2 * 2 ^ (m - 1) := by rw [← pow_succ']; congr 1; omega
  rcases hw with hw | hw
  ·
    rw [hw, inv_pow] at hgw
    have h2 : r ^ (2 * j) = 1 := by
      rw [mul_comm, pow_mul, sq]
      nth_rewrite 2 [← hgw]
      exact mul_inv_cancel _
    have := orderOf_dvd_of_pow_eq_one h2
    rw [hr, e1] at this
    exact Nat.dvd_of_mul_dvd_mul_left two_pos this
  ·
    rw [hw, ← pow_mul] at hgw
    have e2 : (2 ^ (m - 1) - 1) * j = (2 ^ (m - 1) - 2) * j + j := by
      have : 2 ≤ 2 ^ (m - 1) := by
        calc 2 = 2 ^ 1 := rfl
          _ ≤ 2 ^ (m - 1) := Nat.pow_le_pow_right two_pos (by omega)
      rw [← Nat.succ_mul]
      congr 1
      omega
    rw [e2, pow_add] at hgw
    have h2 : r ^ ((2 ^ (m - 1) - 2) * j) = 1 := mul_eq_right.mp hgw
    have hdvd := orderOf_dvd_of_pow_eq_one h2
    rw [hr] at hdvd
    have e3 : 2 ^ (m - 1) - 2 = 2 * (2 ^ (m - 2) - 1) := by
      have : 2 ^ (m - 1) = 2 * 2 ^ (m - 2) := by rw [← pow_succ']; congr 1; omega
      have h1 : 1 ≤ 2 ^ (m - 2) := Nat.one_le_two_pow
      omega
    rw [e3, e1, mul_assoc] at hdvd
    have hdvd' := Nat.dvd_of_mul_dvd_mul_left two_pos hdvd
    have hodd : Odd (2 ^ (m - 2) - 1) := by
      have h4 : 2 ≤ 2 ^ (m - 2) := by
        calc 2 = 2 ^ 1 := rfl
          _ ≤ 2 ^ (m - 2) := Nat.pow_le_pow_right two_pos (by omega)
      have heven : Even (2 ^ (m - 2)) := (Nat.even_pow.mpr ⟨even_two, by omega⟩)
      obtain ⟨t, ht⟩ := heven
      exact ⟨t - 1, by omega⟩
    have hcop : Nat.Coprime (2 ^ (m - 1)) (2 ^ (m - 2) - 1) :=
      Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hodd)
    exact hcop.dvd_of_dvd_mul_left hdvd'

theorem eq_of_sq_eq_one_of_mem_zpowers {m : ℕ} (hm : 1 ≤ m) {r g : G} (hr : orderOf r = 2 ^ m)
    (hg : g ∈ Subgroup.zpowers r) (hg2 : g ^ 2 = 1) : g = 1 ∨ g = r ^ 2 ^ (m - 1) := by
  have hfin : IsOfFinOrder r := orderOf_pos_iff.mp (by rw [hr]; positivity)
  obtain ⟨j, rfl⟩ := (Submonoid.mem_powers_iff g r).mp ((hfin.mem_powers_iff_mem_zpowers).mpr hg)
  apply pow_eq_one_or_of_two_pow_dvd hm hr
  rw [← pow_mul, mul_comm] at hg2
  have := orderOf_dvd_of_pow_eq_one hg2
  have e1 : 2 ^ m = 2 * 2 ^ (m - 1) := by rw [← pow_succ']; congr 1; omega
  rw [hr, e1] at this
  exact Nat.dvd_of_mul_dvd_mul_left two_pos this

theorem card_normalizer_le [Finite G] {m : ℕ} (hm : 3 ≤ m) {r a : G} (hr : orderOf r = 2 ^ m)
    (hcent : Subgroup.centralizer ({a} : Set G) = Subgroup.zpowers r)
    (ha2 : a ^ 2 ^ (m - 1) = 1) :
    Nat.card (Subgroup.normalizer ((Subgroup.zpowers r : Subgroup G) : Set G)) ≤ 2 * 2 ^ m := by
  have haR : a ∈ Subgroup.zpowers r := by
    rw [← hcent]
    exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hcentR : Subgroup.centralizer ((Subgroup.zpowers r : Subgroup G) : Set G) =
      Subgroup.zpowers r := by
    apply le_antisymm
    · intro g hg
      rw [← hcent]
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hg a haR).symm
    · intro g hg
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
      rw [← zpow_add, ← zpow_add, add_comm]
  let φ := (Subgroup.zpowers r).normalizerMonoidHom
  have hker : φ.ker = (Subgroup.zpowers r).subgroupOf
      (Subgroup.normalizer ((Subgroup.zpowers r : Subgroup G) : Set G)) := by
    rw [Subgroup.normalizerMonoidHom_ker, hcentR]
  have hgen : Subgroup.zpowers (⟨r, Subgroup.mem_zpowers r⟩ : Subgroup.zpowers r) = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨x, hx⟩ -
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact ⟨k, Subtype.ext (by simp)⟩
  have hord : orderOf (⟨r, Subgroup.mem_zpowers r⟩ : Subgroup.zpowers r) = 2 ^ m := by
    rw [Subgroup.orderOf_mk]
    exact hr
  have hrange : Nat.card φ.range ≤ 2 := by
    by_contra hlt
    push Not at hlt
    obtain ⟨σ, hσ, hσr, -⟩ := cyclic_two_large_automorphism_subgroup hm _ hgen hord φ.range hlt
    obtain ⟨y, rfl⟩ := hσ
    have hyr : (y : G) * r * (y : G)⁻¹ = r ^ (1 + 2 ^ (m - 1)) := congrArg Subtype.val hσr
    have hya := conj_eq_of_principal hyr haR ha2
    have hyR : (y : G) ∈ Subgroup.zpowers r := by
      have hyC : (y : G) ∈ Subgroup.centralizer ({a} : Set G) :=
        Subgroup.mem_centralizer_singleton_iff.mpr (by
          calc (y : G) * a = (y : G) * a * (y : G)⁻¹ * y := by group
            _ = a * y := by rw [hya])
      rwa [hcent] at hyC
    have hy1 : φ y = 1 := by
      rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
      exact hyR
    rw [hy1] at hσr
    have h1 : r = r ^ (1 + 2 ^ (m - 1)) := congrArg Subtype.val hσr
    rw [pow_add, pow_one] at h1
    have h2 : r ^ 2 ^ (m - 1) = 1 := mul_eq_left.mp h1.symm
    have h3 := Nat.le_of_dvd (by positivity) (hr ▸ orderOf_dvd_of_pow_eq_one h2)
    have h4 : 2 ^ (m - 1) < 2 ^ m := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  have h := Subgroup.card_ker_mul_card_range φ
  rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer).toEquiv,
    Nat.card_zpowers, hr] at h
  calc Nat.card (Subgroup.normalizer ((Subgroup.zpowers r : Subgroup G) : Set G))
      = 2 ^ m * Nat.card φ.range := h.symm
    _ ≤ 2 ^ m * 2 := Nat.mul_le_mul_left _ hrange
    _ = 2 * 2 ^ m := mul_comm _ _

end CyclicCentralizer

open CyclicCentralizer CFSG.Open CFSG.RankTwoShapes

theorem cyclic_centralizer_shape {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hinv : ¬ AtMostOneInvolution P) {a : P} (ha : 2 < orderOf a)
    (hcyc : IsCyclic (Subgroup.centralizer ({a} : Set P))) :
    (∃ n : ℕ, 2 ≤ n ∧ Nonempty (P ≃* DihedralGroup (2 ^ (n - 1)))) ∨
      (∃ n : ℕ, 4 ≤ n ∧ Nonempty (P ≃* SemidihedralGroup n)) ∨
      Subgroup.centralizer ({a} : Set P) = Subgroup.zpowers a := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hRa : Subgroup.centralizer ({a} : Set P) = Subgroup.zpowers a
  · exact Or.inr (Or.inr hRa)
  obtain ⟨r, hRr⟩ := exists_eq_zpowers_of_isCyclic hcyc
  obtain ⟨m, hr⟩ := exists_orderOf_eq_two_pow hP r
  obtain ⟨e, he⟩ := exists_orderOf_eq_two_pow hP a
  have haC : a ∈ Subgroup.centralizer ({a} : Set P) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have haR : a ∈ Subgroup.zpowers r := hRr ▸ haC
  have hdvd : orderOf a ∣ orderOf r := orderOf_dvd_of_mem_zpowers haR
  have hne : orderOf a ≠ orderOf r := by
    intro heq
    apply hRa
    rw [hRr]
    symm
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr haR)
    rw [Nat.card_zpowers, Nat.card_zpowers, heq]
  rw [he, hr] at hdvd hne
  have hem : e < m := by
    have hle := Nat.pow_dvd_pow_iff_le_right'.mp hdvd
    rcases hle.lt_or_eq with h | h
    · exact h
    · exact absurd (by rw [h]) hne
  have he2 : 2 ≤ e := by
    rw [he] at ha
    by_contra h
    push Not at h
    interval_cases e <;> simp at ha
  have hm : 3 ≤ m := by omega
  have ha2 : a ^ 2 ^ (m - 1) = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, he]
    exact Nat.pow_dvd_pow 2 (by omega)
  have hRtop : Subgroup.zpowers r ≠ ⊤ := by
    intro htop
    have : IsCyclic P := isCyclic_iff_exists_zpowers_eq_top.mpr ⟨r, htop⟩
    exact hinv atMostOneInvolution_of_isCyclic
  have hnil : Group.IsNilpotent P := hP.isNilpotent
  have hRN : Subgroup.zpowers r < Subgroup.normalizer ((Subgroup.zpowers r : Subgroup P) : Set P) :=
    Group.normalizerCondition_of_isNilpotent _ (lt_top_iff_ne_top.mpr hRtop)
  have hRcard : Nat.card (Subgroup.zpowers r) = 2 ^ m := by rw [Nat.card_zpowers, hr]
  have hNcard : Nat.card (Subgroup.normalizer ((Subgroup.zpowers r : Subgroup P) : Set P)) =
      2 * 2 ^ m := by
    have hNle := card_normalizer_le hm hr hRr ha2
    obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hRN.le
    have hneq : Nat.card (Subgroup.normalizer ((Subgroup.zpowers r : Subgroup P) : Set P)) ≠
        Nat.card (Subgroup.zpowers r) := fun h =>
      hRN.ne (Subgroup.eq_of_le_of_card_ge hRN.le h.le)
    rw [hRcard] at hk hneq
    have hpos : 0 < 2 ^ m := by positivity
    have hk2 : k ≤ 2 := Nat.le_of_mul_le_mul_left (by rw [← hk, mul_comm]; exact hNle) hpos
    have hNpos : 0 < Nat.card (Subgroup.normalizer ((Subgroup.zpowers r : Subgroup P) : Set P)) :=
      Nat.card_pos
    interval_cases k
    · omega
    · omega
    · omega
  have hidxN : ((Subgroup.zpowers r).subgroupOf
      (Subgroup.normalizer ((Subgroup.zpowers r : Subgroup P) : Set P))).index = 2 := by
    have h1 := Subgroup.index_mul_card ((Subgroup.zpowers r).subgroupOf
      (Subgroup.normalizer ((Subgroup.zpowers r : Subgroup P) : Set P)))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRN.le).toEquiv, hRcard, hNcard] at h1
    exact Nat.eq_of_mul_eq_mul_right (by positivity) h1
  have hsqN : ∀ w ∈ Subgroup.normalizer ((Subgroup.zpowers r : Subgroup P) : Set P),
      w ^ 2 ∈ Subgroup.zpowers r := by
    intro w hw
    have := Subgroup.sq_mem_of_index_two hidxN ⟨w, hw⟩
    rwa [Subgroup.mem_subgroupOf] at this
  have hcr : ∀ g : P, g * r = r * g → g ∈ Subgroup.zpowers r := by
    intro g hg
    have hgC : g ∈ Subgroup.centralizer ({a} : Set P) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp haR
      exact (Commute.zpow_right hg j)
    rwa [hRr] at hgC
  have hout : ∀ w ∈ Subgroup.normalizer ((Subgroup.zpowers r : Subgroup P) : Set P),
      w ∉ Subgroup.zpowers r →
        (w * r * w⁻¹ = r⁻¹ ∨ w * r * w⁻¹ = r ^ (2 ^ (m - 1) - 1)) ∧
          (w ^ 2 = 1 ∨ w ^ 2 = r ^ 2 ^ (m - 1)) := by
    intro w hwN hwR
    have hwr : w * r * w⁻¹ ∈ Subgroup.zpowers r :=
      (Subgroup.mem_normalizer_iff.mp hwN r).mp (Subgroup.mem_zpowers r)
    have hw2 : w ^ 2 * r = r * w ^ 2 := by
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hsqN w hwN)
      rw [← hj]
      exact Commute.zpow_left (Commute.refl r) j
    have hact : w * r * w⁻¹ = r⁻¹ ∨ w * r * w⁻¹ = r ^ (2 ^ (m - 1) - 1) := by
      rcases conj_cases hm hr hwr hw2 with h1 | h1 | h1 | h1
      · exfalso
        apply hwR
        apply hcr
        calc w * r = w * r * w⁻¹ * w := by group
          _ = r * w := by rw [h1]
      · exact Or.inl h1
      · exfalso
        apply hwR
        have hwa := conj_eq_of_principal h1 haR ha2
        have hwC : w ∈ Subgroup.centralizer ({a} : Set P) :=
          Subgroup.mem_centralizer_singleton_iff.mpr (by
            calc w * a = w * a * w⁻¹ * w := by group
              _ = a * w := by rw [hwa])
        rwa [hRr] at hwC
      · exact Or.inr h1
    exact ⟨hact, fixed_cases hm hr hact (hsqN w hwN) (by group)⟩
  have hNN : Subgroup.normalizer
      ((Subgroup.normalizer ((Subgroup.zpowers r : Subgroup P) : Set P) : Subgroup P) : Set P) ≤
        Subgroup.normalizer ((Subgroup.zpowers r : Subgroup P) : Set P) := by
    intro g hg
    have hgr : g * r * g⁻¹ ∈ Subgroup.normalizer ((Subgroup.zpowers r : Subgroup P) : Set P) :=
      (Subgroup.mem_normalizer_iff.mp hg r).mp (hRN.le (Subgroup.mem_zpowers r))
    have hgrR : g * r * g⁻¹ ∈ Subgroup.zpowers r := by
      by_contra hgrR
      obtain ⟨-, h2⟩ := hout _ hgr hgrR
      have h4 : (g * r * g⁻¹) ^ 4 = 1 := by
        rw [show 4 = 2 * 2 from rfl, pow_mul]
        rcases h2 with h2 | h2
        · rw [h2, one_pow]
        · rw [h2, ← pow_mul, ← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ m), ← hr,
            pow_orderOf_eq_one]
      rw [conj_pow, conj_eq_one_iff] at h4
      have h5 := Nat.le_of_dvd (by norm_num) (hr ▸ orderOf_dvd_of_pow_eq_one h4)
      have h6 : 2 ^ 3 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
      omega
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    apply Subgroup.eq_of_le_of_card_ge
    · rw [MonoidHom.map_zpowers]
      exact Subgroup.zpowers_le.mpr hgrR
    · exact (Subgroup.card_map_of_injective (MulAut.conj g).injective).ge
  have hNtop : Subgroup.normalizer ((Subgroup.zpowers r : Subgroup P) : Set P) = ⊤ := by
    by_contra hNtop
    have := Group.normalizerCondition_of_isNilpotent _ (lt_top_iff_ne_top.mpr hNtop)
    exact lt_irrefl _ (lt_of_lt_of_le this hNN)
  have hPcard : Nat.card P = 2 ^ (m + 1) := by
    rw [← Subgroup.card_top (G := P), ← hNtop, hNcard, pow_succ, mul_comm]
  have hidx : (Subgroup.zpowers r).index = 2 := by
    have h1 := Subgroup.index_mul_card (Subgroup.zpowers r)
    rw [hRcard, hPcard, pow_succ, mul_comm (2 ^ m)] at h1
    exact Nat.eq_of_mul_eq_mul_right (by positivity) h1
  have hgen : ∀ y : P, y ∉ Subgroup.zpowers r →
      ⊤ = Subgroup.zpowers r ⊔ Subgroup.zpowers y := by
    intro y hyR
    refine (eq_top_iff.mpr ?_).symm
    intro g _
    by_cases hg : g ∈ Subgroup.zpowers r
    · exact Subgroup.mem_sup_left hg
    · have hyg : y⁻¹ * g ∈ Subgroup.zpowers r :=
        (Subgroup.mul_mem_iff_of_index_two hidx).mpr (by simp [hyR, hg])
      have hgeq : g = y * (y⁻¹ * g) := by group
      rw [hgeq]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers y))
        (Subgroup.mem_sup_left hyg)
  obtain ⟨y, hyN, hyR⟩ := IsConcreteLE.exists_of_lt hRN
  obtain ⟨hact, hsq⟩ := hout y hyN hyR
  rcases hact with hinvr | hsd
  · rcases hsq with hy2 | hy2
    ·
      left
      obtain ⟨φ⟩ := CFSG.GorensteinWalter.dihedral_of_generators_of_not_mem r y (hgen y hyR) hy2
        hinvr hyR
      rw [hr] at φ
      refine ⟨m + 1, by omega, ?_⟩
      rw [Nat.add_sub_cancel]
      exact ⟨φ⟩
    ·
      exfalso
      apply hinv
      have hinR : ∀ x : P, orderOf x = 2 → x ∈ Subgroup.zpowers r := by
        intro x hx
        by_contra hxR
        have hyx : y⁻¹ * x ∈ Subgroup.zpowers r :=
          (Subgroup.mul_mem_iff_of_index_two hidx).mpr (by simp [hyR, hxR])
        obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hyx
        have hxeq : x = y * r ^ j := by rw [hj]; group
        have hconj : y * r ^ j * y⁻¹ = (r ^ j)⁻¹ := by rw [← conj_zpow, hinvr, inv_zpow]
        have hx2 : x ^ 2 = r ^ 2 ^ (m - 1) := by
          rw [hxeq]
          calc (y * r ^ j) ^ 2 = (y * r ^ j * y⁻¹) * y ^ 2 * r ^ j := by rw [sq, sq]; group
            _ = (r ^ j)⁻¹ * r ^ 2 ^ (m - 1) * r ^ j := by rw [hconj, hy2]
            _ = r ^ 2 ^ (m - 1) := by group
        have hx1 : x ^ 2 = 1 := by rw [← hx, pow_orderOf_eq_one]
        rw [hx2] at hx1
        have h5 := Nat.le_of_dvd (by positivity) (hr ▸ orderOf_dvd_of_pow_eq_one hx1)
        have h6 : 2 ^ (m - 1) < 2 ^ m := Nat.pow_lt_pow_right (by norm_num) (by omega)
        omega
      intro s t hs ht
      have hs2 : s ^ 2 = 1 := by rw [← hs, pow_orderOf_eq_one]
      have ht2 : t ^ 2 = 1 := by rw [← ht, pow_orderOf_eq_one]
      have hs1 : s ≠ 1 := by rintro rfl; rw [orderOf_one] at hs; omega
      have ht1 : t ≠ 1 := by rintro rfl; rw [orderOf_one] at ht; omega
      rcases eq_of_sq_eq_one_of_mem_zpowers (by omega) hr (hinR s hs) hs2 with h | h
      · exact absurd h hs1
      rcases eq_of_sq_eq_one_of_mem_zpowers (by omega) hr (hinR t ht) ht2 with h' | h'
      · exact absurd h' ht1
      rw [h, h']
  ·
    right; left
    have hpow : 2 ^ m = 2 * 2 ^ (m - 1) := by rw [← pow_succ']; congr 1; omega
    have hpos : 1 ≤ 2 ^ (m - 1) := Nat.one_le_two_pow
    obtain ⟨y', hy'R, hy'2, hy'r⟩ : ∃ y' : P, y' ∉ Subgroup.zpowers r ∧ y' ^ 2 = 1 ∧
        y' * r * y'⁻¹ = r ^ (2 ^ (m - 1) - 1) := by
      rcases hsq with hy2 | hy2
      · exact ⟨y, hyR, hy2, hsd⟩
      · refine ⟨y * r, ?_, ?_, ?_⟩
        · intro h
          apply hyR
          have := Subgroup.mul_mem _ h (Subgroup.inv_mem _ (Subgroup.mem_zpowers r))
          rwa [mul_inv_cancel_right] at this
        · calc (y * r) ^ 2 = (y * r * y⁻¹) * y ^ 2 * r := by rw [sq, sq]; group
            _ = r ^ (2 ^ (m - 1) - 1) * r ^ 2 ^ (m - 1) * r := by rw [hsd, hy2]
            _ = r ^ (2 ^ (m - 1) - 1 + 2 ^ (m - 1) + 1) := by rw [pow_add, pow_add, pow_one]
            _ = r ^ 2 ^ m := by congr 1; omega
            _ = 1 := by rw [← hr, pow_orderOf_eq_one]
        · calc y * r * r * (y * r)⁻¹ = y * r * y⁻¹ := by group
            _ = r ^ (2 ^ (m - 1) - 1) := hsd
    exact ⟨m + 1, by omega,
      semidihedral_of_generators hm r y' hr hy'2 hy'r (hgen y' hy'R) hPcard⟩


namespace CyclicCentralizer

variable {G : Type*} [Group G]

theorem isCyclic_zpowers (x : G) : IsCyclic (Subgroup.zpowers x) := by
  refine isCyclic_iff_exists_zpowers_eq_top.mpr ⟨⟨x, Subgroup.mem_zpowers x⟩, ?_⟩
  rw [eq_top_iff]
  rintro ⟨y, hy⟩ -
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  exact ⟨k, Subtype.ext (by simp)⟩

theorem exists_involution_ne [Finite G] (hG : IsPGroup 2 G) {B : Subgroup G}
    (hBab : IsMulCommutative B) (hBc : ¬ IsCyclic B) (z : G) :
    ∃ e ∈ B, e ^ 2 = 1 ∧ e ≠ 1 ∧ e ≠ z := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : CommGroup B :=
    { (inferInstance : Group B) with mul_comm := fun a b => hBab.is_comm.comm a b }
  have hB2 : IsPGroup 2 B := hG.to_subgroup B
  have hnot : ¬ ∀ C₁ C₂ : Subgroup B, Nat.card C₁ = 2 → Nat.card C₂ = 2 → C₁ = C₂ :=
    fun h => hBc ((CFSG.RankTwoShapes.isCyclic_iff_subgroup_card_prime_unique hB2).mpr h)
  push Not at hnot
  obtain ⟨C₁, C₂, hC₁, hC₂, hne⟩ := hnot
  have hgen : ∀ C : Subgroup B, Nat.card C = 2 →
      ∃ c : B, c ≠ 1 ∧ c ^ 2 = 1 ∧ C = Subgroup.zpowers c := by
    intro C hC
    have hCne : C ≠ ⊥ := fun h => by rw [h, Subgroup.card_bot] at hC; omega
    obtain ⟨⟨c, hc⟩, hc1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hCne
    have hc1' : c ≠ 1 := fun h => hc1 (Subtype.ext h)
    have hc2 : c ^ 2 = 1 := by
      have h := orderOf_dvd_natCard (⟨c, hc⟩ : C)
      rw [hC] at h
      exact congrArg Subtype.val (orderOf_dvd_iff_pow_eq_one.mp h)
    refine ⟨c, hc1', hc2, ?_⟩
    symm
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hc)
    rw [hC, Nat.card_zpowers, orderOf_eq_prime hc2 hc1']
  obtain ⟨c₁, hc₁1, hc₁2, rfl⟩ := hgen C₁ hC₁
  obtain ⟨c₂, hc₂1, hc₂2, rfl⟩ := hgen C₂ hC₂
  have hc : (c₁ : G) ≠ c₂ := fun h => hne (by rw [Subtype.ext h])
  have hc₁1' : (c₁ : G) ≠ 1 := fun h => hc₁1 (Subtype.ext h)
  have hc₂1' : (c₂ : G) ≠ 1 := fun h => hc₂1 (Subtype.ext h)
  have hc₁2' : (c₁ : G) ^ 2 = 1 := congrArg Subtype.val hc₁2
  have hc₂2' : (c₂ : G) ^ 2 = 1 := congrArg Subtype.val hc₂2
  by_cases hz : (c₁ : G) = z
  · exact ⟨c₂, c₂.2, hc₂2', hc₂1', fun h => hc (hz.trans h.symm)⟩
  · exact ⟨c₁, c₁.2, hc₁2', hc₁1', hz⟩

theorem eq_or_eq_inv_of_orderOf_eq_four {u g : G} (hu : orderOf u = 4)
    (hg : g ∈ Subgroup.zpowers u) (hg4 : orderOf g = 4) : g = u ∨ g = u⁻¹ := by
  have hfin : IsOfFinOrder u := orderOf_pos_iff.mp (by rw [hu]; norm_num)
  obtain ⟨k, rfl⟩ := (Submonoid.mem_powers_iff g u).mp ((hfin.mem_powers_iff_mem_zpowers).mpr hg)
  rw [← pow_mod_orderOf, hu] at hg4 ⊢
  have hu4 : u ^ 4 = 1 := by rw [← hu, pow_orderOf_eq_one]
  obtain h | h | h | h : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by omega
  · rw [h, pow_zero, orderOf_one] at hg4
    omega
  · left
    rw [h, pow_one]
  · exfalso
    rw [h] at hg4
    have h2 : (u ^ 2) ^ 2 = 1 := by rw [← pow_mul, hu4]
    have := orderOf_dvd_of_pow_eq_one h2
    rw [hg4] at this
    omega
  · right
    rw [h]
    exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ, hu4])

end CyclicCentralizer

open CyclicCentralizer in
theorem cyclic_centralizer_order_four_shape {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hinv : ¬ AtMostOneInvolution P) {u : P} (hu : orderOf u = 4)
    (hcyc : IsCyclic (Subgroup.centralizer ({u} : Set P))) :
    (∃ n : ℕ, 2 ≤ n ∧ Nonempty (P ≃* DihedralGroup (2 ^ (n - 1)))) ∨
      (∃ n : ℕ, 4 ≤ n ∧ Nonempty (P ≃* SemidihedralGroup n)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases cyclic_centralizer_shape hP hinv (by omega : 2 < orderOf u) hcyc with h | h | hCu
  · exact Or.inl h
  · exact Or.inr h
  have hu4 : orderOf u = 2 ^ 2 := hu
  have hCu' : ∀ g : P, g * u = u * g → g ∈ Subgroup.zpowers u := fun g hg => by
    have hgC : g ∈ Subgroup.centralizer ({u} : Set P) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hg
    rwa [hCu] at hgC
  have hsq1 : ∀ g ∈ Subgroup.zpowers u, g ^ 2 = 1 → g = 1 ∨ g = u ^ 2 := fun g hg hg2 =>
    eq_of_sq_eq_one_of_mem_zpowers (by norm_num) hu4 hg hg2
  have hnotcyc : ¬ IsCyclic P := fun h => hinv (@atMostOneInvolution_of_isCyclic P _ h)
  have hutop : Subgroup.zpowers u ≠ ⊤ := fun h =>
    hnotcyc (isCyclic_iff_exists_zpowers_eq_top.mpr ⟨u, h⟩)
  have hnil : Group.IsNilpotent P := hP.isNilpotent
  have hconjU : ∀ g : P, g * u * g⁻¹ ∈ Subgroup.zpowers u →
      g * u * g⁻¹ = u ∨ g * u * g⁻¹ = u⁻¹ := fun g hg =>
    eq_or_eq_inv_of_orderOf_eq_four hu hg (by rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hu])
  by_cases hD : ∃ e : P, e ^ 2 = 1 ∧ e ∉ Subgroup.zpowers u ∧ e * u * e⁻¹ = u⁻¹
  ·
    left
    obtain ⟨e, he2, heu, hinvu⟩ := hD
    have heinv : e⁻¹ = e := inv_eq_of_mul_eq_one_left (by rw [← sq, he2])
    have hN : ∀ g : P, g * u * g⁻¹ ∈ Subgroup.zpowers u →
        g ∈ Subgroup.zpowers u ∨ e⁻¹ * g ∈ Subgroup.zpowers u := by
      intro g hg
      rcases hconjU g hg with h1 | h1
      · left
        apply hCu'
        calc g * u = g * u * g⁻¹ * g := by group
          _ = u * g := by rw [h1]
      · right
        apply hCu'
        have he' : e⁻¹ * u * e = u⁻¹ := by
          have h' := hinvu
          rw [heinv] at h' ⊢
          exact h'
        calc e⁻¹ * g * u = e⁻¹ * (g * u * g⁻¹) * g := by group
          _ = (e⁻¹ * u * e)⁻¹ * (e⁻¹ * g) := by rw [h1]; group
          _ = u * (e⁻¹ * g) := by rw [he', inv_inv]
    have hinvol : ∀ t ∈ Subgroup.zpowers u, (e * t) ^ 2 = 1 := by
      intro t ht
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht
      have hej : e * u ^ j * e⁻¹ = (u ^ j)⁻¹ := by rw [← conj_zpow, hinvu, inv_zpow]
      calc (e * u ^ j) ^ 2 = (e * u ^ j * e⁻¹) * (e * e) * u ^ j := by rw [sq]; group
        _ = 1 := by rw [hej, ← sq, he2]; group
    have hNN : Subgroup.normalizer
        ((Subgroup.normalizer ((Subgroup.zpowers u : Subgroup P) : Set P) : Subgroup P) : Set P)
          ≤ Subgroup.normalizer ((Subgroup.zpowers u : Subgroup P) : Set P) := by
      intro g hg
      have hw : g * u * g⁻¹ ∈ Subgroup.normalizer ((Subgroup.zpowers u : Subgroup P) : Set P) :=
        (Subgroup.mem_normalizer_iff.mp hg u).mp
          (Subgroup.le_normalizer (Subgroup.mem_zpowers u))
      have hwu : (g * u * g⁻¹) * u * (g * u * g⁻¹)⁻¹ ∈ Subgroup.zpowers u :=
        (Subgroup.mem_normalizer_iff.mp hw u).mp (Subgroup.mem_zpowers u)
      have hgu : g * u * g⁻¹ ∈ Subgroup.zpowers u := by
        rcases hN _ hwu with h1 | h1
        · exact h1
        · exfalso
          have h2 := hinvol _ h1
          rw [mul_inv_cancel_left, conj_pow, conj_eq_one_iff] at h2
          have := orderOf_dvd_of_pow_eq_one h2
          rw [hu] at this
          omega
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      apply Subgroup.eq_of_le_of_card_ge
      · rw [MonoidHom.map_zpowers]
        exact Subgroup.zpowers_le.mpr hgu
      · exact (Subgroup.card_map_of_injective (MulAut.conj g).injective).ge
    have hNtop : Subgroup.normalizer ((Subgroup.zpowers u : Subgroup P) : Set P) = ⊤ := by
      by_contra hNtop
      have := Group.normalizerCondition_of_isNilpotent _ (lt_top_iff_ne_top.mpr hNtop)
      exact lt_irrefl _ (lt_of_lt_of_le this hNN)
    have hgen : ⊤ = Subgroup.zpowers u ⊔ Subgroup.zpowers e := by
      refine (eq_top_iff.mpr ?_).symm
      intro g _
      have hgN : g ∈ Subgroup.normalizer ((Subgroup.zpowers u : Subgroup P) : Set P) := by
        rw [hNtop]
        exact Subgroup.mem_top g
      rcases hN g ((Subgroup.mem_normalizer_iff.mp hgN u).mp (Subgroup.mem_zpowers u)) with
        h1 | h1
      · exact Subgroup.mem_sup_left h1
      · have hgeq : g = e * (e⁻¹ * g) := by group
        rw [hgeq]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers e))
          (Subgroup.mem_sup_left h1)
    obtain ⟨φ⟩ := CFSG.GorensteinWalter.dihedral_of_generators_of_not_mem u e hgen he2 hinvu heu
    rw [hu] at φ
    exact ⟨3, by norm_num, ⟨φ⟩⟩
  push Not at hD
  have hcenter : ∀ c ∈ Subgroup.center P, c ∈ Subgroup.zpowers u := fun c hc =>
    hCu' c (Subgroup.mem_center_iff.mp hc u).symm
  have hz : u ^ 2 ∈ Subgroup.center P := by
    have : Nontrivial P := ⟨⟨u, 1, fun h => by rw [h, orderOf_one] at hu; omega⟩⟩
    have := hP.center_nontrivial
    obtain ⟨c, hc1⟩ := exists_ne (1 : Subgroup.center P)
    have hcu := hcenter c c.2
    by_cases hc2 : (c : P) ^ 2 = 1
    · rcases hsq1 _ hcu hc2 with h | h
      · exact absurd (Subtype.ext h) hc1
      · rw [← h]
        exact c.2
    · have hc4 : ((c : P) ^ 2) ^ 2 = 1 := by
        rw [← pow_mul]
        exact orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_of_mem_zpowers hcu).trans (by rw [hu]))
      rcases hsq1 _ (Subgroup.pow_mem _ hcu 2) hc4 with h | h
      · exact absurd h hc2
      · rw [← h]
        exact Subgroup.pow_mem _ c.2 2
  have hzc : ∀ g : P, g * u ^ 2 = u ^ 2 * g := Subgroup.mem_center_iff.mp hz
  have habn : ∀ B : Subgroup P, B.Normal → IsMulCommutative B → IsCyclic B := by
    intro B hBn hBab
    by_contra hBc
    obtain ⟨e, heB, he2, he1, hez⟩ := exists_involution_ne hP hBab hBc (u ^ 2)
    have heu : e ∉ Subgroup.zpowers u := fun h => by
      rcases hsq1 e h he2 with h' | h'
      · exact he1 h'
      · exact hez h'
    have hueu : u * e * u⁻¹ ∈ B := hBn.conj_mem e heB u
    have hcomm : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := fun a ha b hb =>
      congrArg Subtype.val (hBab.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    have heinv : e⁻¹ = e := inv_eq_of_mul_eq_one_left (by rw [← sq, he2])
    have h1 : u * (e * (u * e * u⁻¹)) * u⁻¹ = e * (u * e * u⁻¹) := by
      calc u * (e * (u * e * u⁻¹)) * u⁻¹ = (u * e * u⁻¹) * (u ^ 2 * e * (u ^ 2)⁻¹) := by
            rw [sq]; group
        _ = (u * e * u⁻¹) * e := by rw [← hzc e]; group
        _ = e * (u * e * u⁻¹) := hcomm _ hueu _ heB
    have hfZ : e * (u * e * u⁻¹) ∈ Subgroup.zpowers u :=
      hCu' _ (mul_inv_eq_iff_eq_mul.mp h1).symm
    have hf2 : (e * (u * e * u⁻¹)) ^ 2 = 1 := by
      have hc : Commute e (u * e * u⁻¹) := hcomm e heB _ hueu
      rw [hc.mul_pow, he2, conj_pow, he2]
      group
    rcases hsq1 _ hfZ hf2 with hf1 | hfz
    · apply heu
      apply hCu'
      have h2 : u * e * u⁻¹ = e := by
        have := eq_inv_of_mul_eq_one_right hf1
        rwa [heinv] at this
      exact (mul_inv_eq_iff_eq_mul.mp h2).symm
    · apply hD e he2 heu
      have h2 : u * e * u⁻¹ = e * u ^ 2 := by
        calc u * e * u⁻¹ = e⁻¹ * (e * (u * e * u⁻¹)) := by group
          _ = e * u ^ 2 := by rw [hfz, heinv]
      have hu4' : u ^ 4 = 1 := by rw [← hu, pow_orderOf_eq_one]
      calc e * u * e⁻¹ = e * (u * e * u⁻¹) * u := by rw [heinv]; group
        _ = e * (e * u ^ 2) * u := by rw [h2]
        _ = u ^ 3 := by rw [← mul_assoc, ← sq, he2, one_mul, ← pow_succ]
        _ = u⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_succ, hu4'])
  obtain ⟨X, -, hXc, hXidx⟩ := cyclic_abelian_normal_index_two hP habn
  obtain ⟨x, rfl⟩ := exists_eq_zpowers_of_isCyclic hXc
  have hidx2 : (Subgroup.zpowers x).index = 2 := by
    have h1 := Subgroup.index_mul_card (Subgroup.zpowers x)
    have hPpos : 0 < Nat.card P := Nat.card_pos
    have hpos : 0 < (Subgroup.zpowers x).index := by
      rcases Nat.eq_zero_or_pos (Subgroup.zpowers x).index with h | h
      · rw [h, zero_mul] at h1
        omega
      · exact h
    have hne1 : (Subgroup.zpowers x).index ≠ 1 := fun h =>
      hnotcyc (isCyclic_iff_exists_zpowers_eq_top.mpr ⟨x, Subgroup.index_eq_one.mp h⟩)
    omega
  have hPx : Nat.card P = 2 * orderOf x := by
    have h1 := Subgroup.index_mul_card (Subgroup.zpowers x)
    rw [hidx2, Nat.card_zpowers] at h1
    exact h1.symm
  have hle_of : u ∈ Subgroup.zpowers x → orderOf x ≤ 4 := by
    intro hux
    have hle : Subgroup.zpowers x ≤ Subgroup.zpowers u := by
      intro g hg
      apply hCu'
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hux
      rw [← hj, ← zpow_add, ← zpow_add, add_comm]
    have := Subgroup.card_le_of_le hle
    rwa [Nat.card_zpowers, Nat.card_zpowers, hu] at this
  have hx8 : 8 ≤ orderOf x := by
    by_contra hlt
    push Not at hlt
    have hx4 : orderOf x ≤ 4 := by
      obtain ⟨k, hk⟩ := exists_orderOf_eq_two_pow hP x
      rw [hk] at hlt ⊢
      by_contra h4
      push Not at h4
      have hk3 : 3 ≤ k := by
        by_contra hk3
        push Not at hk3
        interval_cases k <;> norm_num at h4
      have : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk3
      omega
    have hUcard : Nat.card (Subgroup.zpowers u) = 4 := by rw [Nat.card_zpowers, hu]
    have hUidx : (Subgroup.zpowers u).index = 2 := by
      have h1 := Subgroup.index_mul_card (Subgroup.zpowers u)
      rw [hUcard] at h1
      have hne1 : (Subgroup.zpowers u).index ≠ 1 := fun h => hutop (Subgroup.index_eq_one.mp h)
      have hne0 : (Subgroup.zpowers u).index ≠ 0 := fun h => by
        rw [h, zero_mul] at h1
        have : 0 < Nat.card P := Nat.card_pos
        omega
      omega
    have hUn : (Subgroup.zpowers u).Normal := Subgroup.normal_of_index_eq_two hUidx
    have hinv' := hinv
    rw [AtMostOneInvolution] at hinv'
    push Not at hinv'
    obtain ⟨s, t, hs, ht, hst⟩ := hinv'
    have hs2 : s ^ 2 = 1 := by rw [← hs, pow_orderOf_eq_one]
    have ht2 : t ^ 2 = 1 := by rw [← ht, pow_orderOf_eq_one]
    have hs1 : s ≠ 1 := by rintro rfl; rw [orderOf_one] at hs; omega
    have ht1 : t ≠ 1 := by rintro rfl; rw [orderOf_one] at ht; omega
    obtain ⟨e, he2, heu⟩ : ∃ e : P, e ^ 2 = 1 ∧ e ∉ Subgroup.zpowers u := by
      by_cases hsu : s ∈ Subgroup.zpowers u
      · refine ⟨t, ht2, fun htu => hst ?_⟩
        rcases hsq1 s hsu hs2 with h | h
        · exact absurd h hs1
        rcases hsq1 t htu ht2 with h' | h'
        · exact absurd h' ht1
        rw [h, h']
      · exact ⟨s, hs2, hsu⟩
    have heuu : e * u * e⁻¹ ∈ Subgroup.zpowers u := hUn.conj_mem u (Subgroup.mem_zpowers u) e
    rcases hconjU e heuu with h1 | h1
    · apply heu
      apply hCu'
      calc e * u = e * u * e⁻¹ * e := by group
        _ = u * e := by rw [h1]
    · exact hD e he2 heu h1
  have hux : u ∉ Subgroup.zpowers x := fun h => by
    have := hle_of h
    omega
  have hx2ord : orderOf (x ^ 2) = orderOf x / 2 := by
    rw [orderOf_pow' x two_ne_zero, Nat.gcd_eq_right]
    obtain ⟨k, hk⟩ := exists_orderOf_eq_two_pow hP x
    rw [hk]
    have : k ≠ 0 := by
      rintro rfl
      rw [hk] at hx8
      norm_num at hx8
    exact dvd_pow_self 2 this
  have hC : Subgroup.centralizer ({x ^ 2} : Set P) = Subgroup.zpowers x := by
    apply le_antisymm
    · intro g hg
      by_contra hgx
      have hgc : g * x ^ 2 = x ^ 2 * g := Subgroup.mem_centralizer_singleton_iff.mp hg
      have hall : x ^ 2 ∈ Subgroup.center P := by
        rw [Subgroup.mem_center_iff]
        intro h
        by_cases hh : h ∈ Subgroup.zpowers x
        · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
          rw [← zpow_natCast, ← zpow_add, ← zpow_add, add_comm]
        · have hgh : g⁻¹ * h ∈ Subgroup.zpowers x :=
            (Subgroup.mul_mem_iff_of_index_two hidx2).mpr (by simp [hgx, hh])
          obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hgh
          have hheq : h = g * x ^ i := by rw [hi]; group
          have hxi : x ^ i * x ^ 2 = x ^ 2 * x ^ i := by
            rw [← zpow_natCast, ← zpow_add, ← zpow_add, add_comm]
          rw [hheq, mul_assoc, hxi, ← mul_assoc, hgc, mul_assoc]
      have hx2u := hcenter _ hall
      have heq : Subgroup.zpowers (x ^ 2) = Subgroup.zpowers u := by
        apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hx2u)
        rw [Nat.card_zpowers, Nat.card_zpowers, hu, hx2ord]
        omega
      apply hux
      have hu2 : u ∈ Subgroup.zpowers (x ^ 2) := heq ▸ Subgroup.mem_zpowers u
      exact Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) 2) hu2
    · intro g hg
      rw [Subgroup.mem_centralizer_singleton_iff]
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      rw [← zpow_natCast, ← zpow_add, ← zpow_add, add_comm]
  have hx2 : 2 < orderOf (x ^ 2) := by
    rw [hx2ord]
    omega
  have hcyc2 : IsCyclic (Subgroup.centralizer ({x ^ 2} : Set P)) := by
    rw [hC]
    exact isCyclic_zpowers x
  rcases cyclic_centralizer_shape hP hinv hx2 hcyc2 with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exfalso
    rw [hC] at h
    have := congrArg (fun H : Subgroup P => Nat.card H) h
    simp only [Nat.card_zpowers, hx2ord] at this
    omega

end CFSG.ComponentClassification.AschbacherToolkit
