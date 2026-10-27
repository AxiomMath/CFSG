module

public import CFSG.LocalAnalysis.EvenBN.Tits.I21Red

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.I21.Toolbox

open Subgroup CFSG.Open

section NormalForms

variable {G : Type*} [Group G] {t u x : G}

theorem nf_eq_iff (h : CRel t u x) {a i j a' i' j' : ℕ} :
    t ^ a * x ^ i * u ^ j = t ^ a' * x ^ i' * u ^ j' ↔
      a % 2 = a' % 2 ∧ x ^ i = x ^ i' ∧ j % 4 = j' % 4 := by
  constructor
  · intro heq
    have h1 : (t ^ a' * x ^ (4 * i' * 2 ^ (3 * j')) * u ^ (3 * j')) *
        (t ^ a * x ^ i * u ^ j) = 1 := by
      rw [← h.nf_inv a' i' j', heq, inv_mul_cancel]
    rw [h.nf_mul, h.nf_eq_one_iff] at h1
    obtain ⟨ha, hx, hj⟩ := h1
    refine ⟨by omega, ?_, by omega⟩
    have hm : Nat.Coprime 5 (2 ^ (3 * j')) := Nat.Coprime.pow_right _ (by norm_num)
    have hord : orderOf x ∣ 5 := orderOf_dvd_of_pow_eq_one h.x_five
    have hdvd : orderOf x ∣ (4 * i' + i) * 2 ^ (3 * j') := by
      apply orderOf_dvd_of_pow_eq_one
      rw [show (4 * i' + i) * 2 ^ (3 * j') = 4 * i' * 2 ^ (3 * j') + i * 2 ^ (3 * j') by ring]
      exact hx
    have hdvd' : orderOf x ∣ 4 * i' + i :=
      (Nat.Coprime.coprime_dvd_left hord hm).dvd_of_dvd_mul_right hdvd
    have hx1 : x ^ (4 * i' + i) = 1 := orderOf_dvd_iff_pow_eq_one.mp hdvd'
    have hx2 : x ^ (i' + 4 * i') = 1 := by
      rw [show i' + 4 * i' = 5 * i' by ring, pow_mul, h.x_five, one_pow]
    apply mul_right_cancel (b := x ^ (4 * i'))
    rw [← pow_add, ← pow_add, add_comm i (4 * i'), hx1, hx2]
  · rintro ⟨ha, hx, hj⟩
    rw [pow_mod_of_pow_eq_one h.t_sq a, pow_mod_of_pow_eq_one h.u_four j,
      pow_mod_of_pow_eq_one h.t_sq a', pow_mod_of_pow_eq_one h.u_four j', ha, hj, hx]

theorem card_eq_mul (h : CRel t u x) {N : Subgroup G} (hNC : N ≤ closure ({t, u, x} : Set G))
    (cond : ℕ → ℕ → Prop) [DecidablePred fun p : ℕ × ℕ => cond p.1 p.2]
    (hper : ∀ a j, cond a j ↔ cond (a % 2) (j % 4))
    (hmem : ∀ a i j, t ^ a * x ^ i * u ^ j ∈ N ↔ cond a j) :
    Nat.card N = orderOf x *
      ((Finset.range 2 ×ˢ Finset.range 4).filter fun p : ℕ × ℕ => cond p.1 p.2).card := by
  have hx0 : 0 < orderOf x :=
    orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨5, by norm_num, h.x_five⟩)
  set T := (Finset.range 2 ×ˢ Finset.range 4).filter fun p : ℕ × ℕ => cond p.1 p.2
  let F : ℕ × ℕ × ℕ → G := fun q => t ^ q.2.1 * x ^ q.1 * u ^ q.2.2
  let S : Finset (ℕ × ℕ × ℕ) := Finset.range (orderOf x) ×ˢ T
  have hF : (N : Set G) = F '' (S : Set (ℕ × ℕ × ℕ)) := by
    ext g
    constructor
    · intro hg
      obtain ⟨a, i, j, rfl⟩ := h.mem_closure_iff.mp (hNC hg)
      have hc := (hmem a i j).mp hg
      refine ⟨(i % orderOf x, a % 2, j % 4), ?_, ?_⟩
      · simp only [S, T, Set.mem_prod, Finset.mem_coe, Finset.mem_range, Finset.mem_filter,
          Finset.mem_product]
        exact ⟨Nat.mod_lt _ hx0, ⟨Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num)⟩,
          (hper a j).mp hc⟩
      · simp only [F]
        rw [← pow_mod_of_pow_eq_one h.t_sq a, pow_mod_orderOf x i, ←
          pow_mod_of_pow_eq_one h.u_four j]
    · rintro ⟨q, hq, rfl⟩
      simp only [S, T, Set.mem_prod, Finset.mem_coe, Finset.mem_range, Finset.mem_filter,
        Finset.mem_product] at hq
      exact (hmem _ _ _).mpr hq.2.2
  have hinj : Set.InjOn F (S : Set (ℕ × ℕ × ℕ)) := by
    rintro ⟨i, a, j⟩ hq ⟨i', a', j'⟩ hq' hEq
    simp only [S, T, Set.mem_prod, Finset.mem_coe, Finset.mem_range, Finset.mem_filter,
      Finset.mem_product] at hq hq'
    obtain ⟨ha, hx, hj⟩ := (nf_eq_iff h).mp hEq
    have hi : i % orderOf x = i' % orderOf x := pow_eq_pow_iff_modEq.mp hx
    rw [Nat.mod_eq_of_lt hq.1, Nat.mod_eq_of_lt hq'.1] at hi
    rw [Nat.mod_eq_of_lt hq.2.1.1, Nat.mod_eq_of_lt hq'.2.1.1] at ha
    rw [Nat.mod_eq_of_lt hq.2.1.2, Nat.mod_eq_of_lt hq'.2.1.2] at hj
    rw [hi, ha, hj]
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, hF, hinj.ncard_image, Set.ncard_coe_finset,
    Finset.card_product, Finset.card_range]

theorem closure_one_pair (w : G) : closure ({1, w} : Set G) = zpowers w := by
  rw [Subgroup.closure_insert_one, ← Subgroup.zpowers_eq_closure]

end NormalForms

section Card

variable {G : Type} [Group G] {t u x : G}

theorem card_centralizer_eq (h : Sec622Bar G t u x) :
    Nat.card (centralizer ({t} : Set G)) = orderOf x * 8 := by
  have hc := h.crel
  have := card_eq_mul hc (N := centralizer ({t} : Set G)) h.cent.le (fun _ _ => True)
    (fun _ _ => Iff.rfl) fun a i j =>
      ⟨fun _ => trivial, fun _ => h.cent ▸ hc.mem_closure_iff.mpr ⟨a, i, j, rfl⟩⟩
  rw [this]
  rfl

end Card

section Zj

variable {G : Type*} [Group G] {t u x : G}

theorem zj_mul (h : CRel t u x) (j k : ℕ) :
    (x ^ j * u ^ 2) * (x ^ k * u ^ 2) = x ^ (j + 4 * k) := by
  have h1 : u ^ 2 * x ^ k = x ^ (k * 2 ^ 2) * u ^ 2 := h.pow_u_mul_x_pow 2 k
  calc (x ^ j * u ^ 2) * (x ^ k * u ^ 2) = x ^ j * (u ^ 2 * x ^ k) * u ^ 2 := by
        simp only [mul_assoc]
    _ = x ^ j * (x ^ (k * 2 ^ 2) * u ^ 2) * u ^ 2 := by rw [h1]
    _ = x ^ (j + k * 2 ^ 2) * u ^ (2 + 2) := by
        rw [pow_add, pow_add]
        simp only [mul_assoc]
    _ = x ^ (j + 4 * k) := by
        rw [show 2 + 2 = 4 from rfl, h.u_four, mul_one, show j + k * 2 ^ 2 = j + 4 * k by ring]

theorem zj_mul_zpow (h : CRel t u x) (j k : ℕ) :
    (x ^ j * u ^ 2) * (x ^ k * u ^ 2) = x ^ ((j : ℤ) - k) := by
  rw [zj_mul h]
  have h1 : x ^ ((j : ℤ) - k) * x ^ k = x ^ j := by
    rw [← zpow_natCast x k, ← zpow_add, sub_add_cancel, zpow_natCast]
  have h2 : x ^ (j + 4 * k) * x ^ k = x ^ j := by
    rw [← pow_add, show j + 4 * k + k = j + 5 * k by ring, pow_add, pow_mul, h.x_five, one_pow,
      mul_one]
  exact mul_right_cancel (h2.trans h1.symm)

theorem zj_sq (h : CRel t u x) (j : ℕ) : (x ^ j * u ^ 2) ^ 2 = 1 := by
  rw [sq, zj_mul_zpow h, sub_self, zpow_zero]

theorem zj_ne_one (h : CRel t u x) (j : ℕ) : x ^ j * u ^ 2 ≠ 1 := by
  intro h1
  have h2 := (h.nf_eq_one_iff (a := 0) (i := j) (j := 2)).mp (by simpa using h1)
  have h3 := h2.2.2
  omega

theorem zj_conj (h : CRel t u x) (j : ℕ) : (x ^ j * u ^ 2) * x * (x ^ j * u ^ 2)⁻¹ = x⁻¹ := by
  have h1 : u ^ 2 * x = x ^ 4 * u ^ 2 := by simpa using h.pow_u_mul_x_pow 2 1
  have h4 : x ^ 4 = x⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_succ, h.x_five]
  calc (x ^ j * u ^ 2) * x * (x ^ j * u ^ 2)⁻¹
      = x ^ j * (u ^ 2 * x) * (u ^ 2)⁻¹ * (x ^ j)⁻¹ := by group
    _ = x ^ j * (x ^ 4 * u ^ 2) * (u ^ 2)⁻¹ * (x ^ j)⁻¹ := by rw [h1]
    _ = x ^ j * x ^ 4 * (x ^ j)⁻¹ := by group
    _ = x ^ 4 := by group
    _ = x⁻¹ := h4

theorem conj_mem_zpowers [Finite G] (h : CRel t u x) {g : G}
    (hg : g ∈ closure ({t, u, x} : Set G)) {n : G} (hn : n ∈ zpowers x) :
    g * n * g⁻¹ ∈ zpowers x := by
  have hnorm : closure ({t, u, x} : Set G) ≤ normalizer (zpowers x : Set G) := by
    rw [closure_le]
    intro g hg
    rcases hg with rfl | rfl | rfl
    · refine mem_normalizer_fintype fun n hn => ?_
      obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp hn
      rw [(Commute.zpow_right (show Commute g x from h.tx) m).eq, mul_inv_cancel_right]
      exact hn
    · refine mem_normalizer_fintype fun n hn => ?_
      obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp hn
      rw [← conj_zpow, h.ux]
      exact zpow_mem (pow_mem (mem_zpowers x) 2) m
    · refine mem_normalizer_fintype fun n hn => ?_
      obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp hn
      rw [(Commute.zpow_right (Commute.refl g) m).eq, mul_inv_cancel_right]
      exact hn
  exact (mem_normalizer_iff.mp (hnorm hg) n).mp hn

end Zj

section FourOne

variable {G : Type*} [Group G] {t u x : G}

theorem four_one_core (h : CRel t u x) {N : Subgroup G}
    (hNC : N ≤ closure ({t, u, x} : Set G)) (hxN : x ∈ N) (hzN : u ^ 2 ∈ N) (htN : t ∉ N) :
    (N = closure {x, u ^ 2} ∧ Nat.card N = orderOf x * 2) ∨
      (N = closure {x, u} ∧ Nat.card N = orderOf x * 4) ∨
      (N = closure {x, t * u} ∧ Nat.card N = orderOf x * 4) := by
  have hnf : ∀ a i j : ℕ, t ^ a * x ^ i * u ^ j ∈ N ↔ t ^ (a % 2) * u ^ (j % 2) ∈ N := by
    intro a i j
    have e1 : t ^ a * x ^ i * u ^ j =
        x ^ i * (t ^ (a % 2) * u ^ (j % 2)) * (u ^ 2) ^ (j / 2) := by
      have hc : t ^ a * x ^ i = x ^ i * t ^ a :=
        (Commute.pow_pow (show Commute t x from h.tx) a i).eq
      have hu : u ^ j = u ^ (j % 2) * (u ^ 2) ^ (j / 2) := by
        rw [← pow_mul, ← pow_add, Nat.mod_add_div]
      rw [hc, pow_mod_of_pow_eq_one h.t_sq a]
      conv_lhs => rw [hu]
      simp only [mul_assoc]
    rw [e1, Subgroup.mul_mem_cancel_right N (pow_mem hzN _),
      Subgroup.mul_mem_cancel_left N (pow_mem hxN _)]
  by_cases hu : u ∈ N
  ·
    have htu : t * u ∉ N := fun htu => htN ((Subgroup.mul_mem_cancel_right N hu).mp htu)
    have hmem : ∀ a i j : ℕ, t ^ a * x ^ i * u ^ j ∈ N ↔ a % 2 = 0 := by
      intro a i j
      rw [hnf]
      rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
        rcases Nat.mod_two_eq_zero_or_one j with hj | hj <;>
          simp [ha, hj, htN, htu, hu]
    right; left
    refine ⟨le_antisymm ?_ ?_, ?_⟩
    · intro g hg
      obtain ⟨a, i, j, rfl⟩ := h.mem_closure_iff.mp (hNC hg)
      have hta : t ^ a = 1 := by
        rw [pow_mod_of_pow_eq_one h.t_sq a, (hmem a i j).mp hg, pow_zero]
      rw [hta, one_mul]
      exact mul_mem (pow_mem (subset_closure (by simp)) _) (pow_mem (subset_closure (by simp)) _)
    · rw [closure_le]
      intro g hg
      rcases hg with rfl | rfl
      exacts [hxN, hu]
    · rw [card_eq_mul h hNC (fun a _ => a % 2 = 0) (fun a j => by simp) hmem]
      rfl
  · by_cases htu : t * u ∈ N
    ·
      have hmem : ∀ a i j : ℕ, t ^ a * x ^ i * u ^ j ∈ N ↔ a % 2 = j % 2 := by
        intro a i j
        rw [hnf]
        rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
          rcases Nat.mod_two_eq_zero_or_one j with hj | hj <;>
            simp [ha, hj, htN, htu, hu]
      right; right
      refine ⟨le_antisymm ?_ ?_, ?_⟩
      · intro g hg
        obtain ⟨a, i, j, rfl⟩ := h.mem_closure_iff.mp (hNC hg)
        have ha := (hmem a i j).mp hg
        have hta : t ^ a = t ^ j := by
          rw [pow_mod_of_pow_eq_one h.t_sq a, pow_mod_of_pow_eq_one h.t_sq j, ha]
        have hc : t ^ a * x ^ i = x ^ i * t ^ a :=
          (Commute.pow_pow (show Commute t x from h.tx) a i).eq
        have e : t ^ a * x ^ i * u ^ j = x ^ i * (t * u) ^ j := by
          rw [hc, hta, (show Commute t u from h.tu).mul_pow, mul_assoc]
        rw [e]
        exact mul_mem (pow_mem (subset_closure (by simp)) _) (pow_mem (subset_closure (by simp)) _)
      · rw [closure_le]
        intro g hg
        rcases hg with rfl | rfl
        exacts [hxN, htu]
      · rw [card_eq_mul h hNC (fun a j => a % 2 = j % 2) (fun a j => by omega) hmem]
        rfl
    ·
      have hmem : ∀ a i j : ℕ, t ^ a * x ^ i * u ^ j ∈ N ↔ a % 2 = 0 ∧ j % 2 = 0 := by
        intro a i j
        rw [hnf]
        rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
          rcases Nat.mod_two_eq_zero_or_one j with hj | hj <;>
            simp [ha, hj, htN, htu, hu]
      left
      refine ⟨le_antisymm ?_ ?_, ?_⟩
      · intro g hg
        obtain ⟨a, i, j, rfl⟩ := h.mem_closure_iff.mp (hNC hg)
        obtain ⟨ha, hj⟩ := (hmem a i j).mp hg
        have hta : t ^ a = 1 := by rw [pow_mod_of_pow_eq_one h.t_sq a, ha, pow_zero]
        have huj : u ^ j = (u ^ 2) ^ (j / 2) := by
          rw [← pow_mul]
          congr 1
          omega
        rw [hta, one_mul, huj]
        exact mul_mem (pow_mem (subset_closure (by simp)) _) (pow_mem (subset_closure (by simp)) _)
      · rw [closure_le]
        intro g hg
        rcases hg with rfl | rfl
        exacts [hxN, hzN]
      · rw [card_eq_mul h hNC (fun a j => a % 2 = 0 ∧ j % 2 = 0) (fun a j => by omega) hmem]
        rfl

end FourOne

end CFSG.LocalAnalysis.EvenBN.Tits.I21.Toolbox

namespace CFSG.LocalAnalysis.EvenBN.Tits

open Subgroup CFSG.Open

theorem sec622_centralizer_solvable {G : Type} [Group G] [Finite G] {t u x : G}
    (h : Sec622Bar G t u x) : Group.IsSolvable (centralizer ({t} : Set G)) := by
  have hc := h.crel
  have hxC : x ∈ centralizer ({t} : Set G) := h.cent ▸ subset_closure (by simp)
  have hcardC : Nat.card (centralizer ({t} : Set G)) = orderOf x * 8 :=
    I21.Toolbox.card_centralizer_eq h
  set C := centralizer ({t} : Set G)
  have hle : zpowers x ≤ C := zpowers_le.mpr hxC
  set H : Subgroup C := (zpowers x).subgroupOf C
  have hHn : H.Normal := (normal_subgroupOf_iff hle).mpr fun a k ha hk =>
    I21.Toolbox.conj_mem_zpowers hc (h.cent ▸ hk) ha
  haveI := hHn
  have hHs : Group.IsSolvable H := by
    refine Group.isSolvable_of_comm fun a b => ?_
    obtain ⟨m, hm⟩ := mem_zpowers_iff.mp (mem_subgroupOf.mp a.2)
    obtain ⟨n, hn⟩ := mem_zpowers_iff.mp (mem_subgroupOf.mp b.2)
    apply Subtype.ext
    apply Subtype.ext
    change (a.1 : G) * b.1 = b.1 * a.1
    rw [← hm, ← hn]
    exact ((Commute.refl x).zpow_zpow m n).eq
  have hQs : Group.IsSolvable (C ⧸ H) := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hcard : Nat.card (C ⧸ H) = 2 ^ 3 := by
      have h1 := H.card_eq_card_quotient_mul_card_subgroup
      have h2 : Nat.card H = orderOf x := by
        rw [Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv, Nat.card_zpowers]
      rw [h2, hcardC] at h1
      exact (Nat.eq_of_mul_eq_mul_right (orderOf_pos x) (by rw [← h1]; ring)).symm
    haveI : Group.IsNilpotent (C ⧸ H) := (IsPGroup.of_card hcard).isNilpotent
    exact IsNilpotent.to_isSolvable
  exact Group.isSolvable_of_subgroup_quotient H

theorem sec622_involutions_centralizer {G : Type} [Group G] [Finite G] {t u x : G}
    (h : Sec622Bar G t u x) {g : G} (hg : g ∈ centralizer ({t} : Set G)) (hg1 : g ≠ 1)
    (hg2 : g ^ 2 = 1) :
    g = t ∨ (∃ j : ℕ, g = x ^ j * u ^ 2) ∨ ∃ j : ℕ, g = t * (x ^ j * u ^ 2) :=
  h.crel.eq_of_sq_eq_one (h.cent ▸ hg) hg2 hg1

theorem sec622_zj_facts {G : Type} [Group G] [Finite G] {t u x : G} (h : Sec622Bar G t u x)
    (hx : x ≠ 1) (j k : ℕ) :
    (x ^ j * u ^ 2) ^ 2 = 1 ∧ x ^ j * u ^ 2 ≠ 1 ∧
      (x ^ j * u ^ 2) * x * (x ^ j * u ^ 2)⁻¹ = x⁻¹ ∧
      (x ^ j * u ^ 2) * (x ^ k * u ^ 2) = x ^ ((j : ℤ) - k) ∧
      (x ^ j * u ^ 2 = x ^ k * u ^ 2 ↔ x ^ j = x ^ k) := by
  have hc := h.crel
  have _ := hx
  exact ⟨I21.Toolbox.zj_sq hc j, I21.Toolbox.zj_ne_one hc j, I21.Toolbox.zj_conj hc j,
    I21.Toolbox.zj_mul_zpow hc j k, mul_left_inj _⟩

theorem sec622_four_one {G : Type} [Group G] [Finite G] {t u x : G} (h : Sec622Bar G t u x)
    {N : Subgroup G} (hNC : N ≤ centralizer ({t} : Set G))
    (hNn : ∀ c ∈ centralizer ({t} : Set G), ∀ n ∈ N, c * n * c⁻¹ ∈ N) (hN2 : 2 ∣ Nat.card N)
    (htN : t ∉ N) (htzN : ∀ j : ℕ, t * (x ^ j * u ^ 2) ∉ N) :
    (x ≠ 1 ∧ ((N = closure {x, u ^ 2} ∧ Nat.card N = 10) ∨
      (N = closure {x, u} ∧ Nat.card N = 20) ∨ (N = closure {x, t * u} ∧ Nat.card N = 20))) ∨
    (x = 1 ∧ ((N = zpowers (u ^ 2) ∧ Nat.card N = 2) ∨
      (N = zpowers u ∧ Nat.card N = 4) ∨ (N = zpowers (t * u) ∧ Nat.card N = 4))) := by
  have hc := h.crel
  have hNC' : N ≤ closure ({t, u, x} : Set G) := h.cent ▸ hNC
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' (G := N) 2 hN2
  have hs' : orderOf (s : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hs
  have hs2 : (s : G) ^ 2 = 1 := by rw [← hs']; exact pow_orderOf_eq_one _
  have hs1 : (s : G) ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hs'
    omega
  obtain ⟨i, hi⟩ : ∃ i : ℕ, x ^ i * u ^ 2 ∈ N := by
    rcases hc.eq_of_sq_eq_one (hNC' s.2) hs2 hs1 with h1 | ⟨i, hi⟩ | ⟨i, hi⟩
    · exact absurd (by rw [← h1]; exact s.2) htN
    · exact ⟨i, by rw [← hi]; exact s.2⟩
    · exact absurd (by rw [← hi]; exact s.2) (htzN i)
  have hxC : x ∈ centralizer ({t} : Set G) := h.cent ▸ subset_closure (by simp)
  have hxN : x ∈ N := by
    have key : ∀ s : G, s * x * s⁻¹ = x⁻¹ → x * s * x⁻¹ * s⁻¹ = x ^ 2 := by
      intro s hs
      calc x * s * x⁻¹ * s⁻¹ = x * (s * x * s⁻¹)⁻¹ := by group
        _ = x * x := by rw [hs, inv_inv]
        _ = x ^ 2 := (sq x).symm
    have h2 : x ^ 2 ∈ N := by
      rw [← key _ (I21.Toolbox.zj_conj hc i)]
      exact N.mul_mem (hNn x hxC _ hi) (N.inv_mem hi)
    have h6 : x = (x ^ 2) ^ 3 := by
      rw [← pow_mul]
      calc x = x ^ 5 * x := by rw [hc.x_five, one_mul]
        _ = x ^ 6 := by rw [← pow_succ]
    rw [h6]
    exact pow_mem h2 3
  have hzN : u ^ 2 ∈ N := by
    have : u ^ 2 = (x ^ i)⁻¹ * (x ^ i * u ^ 2) := by group
    rw [this]
    exact N.mul_mem (N.inv_mem (pow_mem hxN i)) hi
  have core := I21.Toolbox.four_one_core hc hNC' hxN hzN htN
  rcases h.x_cases with hx1 | hx5
  · right
    refine ⟨hx1, ?_⟩
    subst hx1
    simpa only [I21.Toolbox.closure_one_pair, orderOf_one, one_mul] using core
  · left
    have hx1 : x ≠ 1 := fun h1 => by
      rw [h1, orderOf_one] at hx5
      omega
    refine ⟨hx1, ?_⟩
    rw [hx5] at core
    rcases core with ⟨e, c⟩ | ⟨e, c⟩ | ⟨e, c⟩
    · exact Or.inl ⟨e, by omega⟩
    · exact Or.inr (Or.inl ⟨e, by omega⟩)
    · exact Or.inr (Or.inr ⟨e, by omega⟩)

theorem sec622_le_of_perfect {G : Type} [Group G] [Finite G] {N E : Subgroup G} (hN : N.Normal)
    (hNi : N.index = 2) (hE : Group.IsPerfect E) : E ≤ N := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := hN
  have hcard : Nat.card (G ⧸ N) = 2 := by rw [← Subgroup.index_eq_card]; exact hNi
  haveI : IsCyclic (G ⧸ N) := isCyclic_of_prime_card hcard
  have h1 : commutator G ≤ N := by
    have := Abelianization.commutator_subset_ker (QuotientGroup.mk' N)
    rwa [QuotientGroup.ker_mk'] at this
  calc E = ⁅E, E⁆ := (Subgroup.isPerfect_iff.mp hE).symm
    _ ≤ ⁅(⊤ : Subgroup G), ⊤⁆ := Subgroup.commutator_mono le_top le_top
    _ ≤ N := h1

end CFSG.LocalAnalysis.EvenBN.Tits
