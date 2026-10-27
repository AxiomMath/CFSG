module

public import CFSG.LocalAnalysis.EvenBN.Tits.I21Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralGenerators
public import CFSG.CharacterTheory.Semidihedral.NormalForm
public import CFSG.LocalAnalysis.EvenBN.Tits.Prelim.SecTwoTwoGroup

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.I21.SixTwoB

open Subgroup CFSG.Open

section Generic

variable {G : Type*} [Group G]

theorem mem_or_mul_mem_of_closure_insert {H : Subgroup G} {s : G} (hs : s * s ∈ H)
    (hn : ∀ h ∈ H, s * h * s⁻¹ ∈ H) {g : G} (hg : g ∈ closure (insert s (H : Set G))) :
    g ∈ H ∨ ∃ h ∈ H, g = s * h := by
  have hn' : ∀ h ∈ H, s⁻¹ * h * s ∈ H := fun h hh => by
    have : s⁻¹ * h * s = (s * s)⁻¹ * (s * h * s⁻¹) * (s * s) := by group
    rw [this]
    exact mul_mem (mul_mem (inv_mem hs) (hn h hh)) hs
  induction hg using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with rfl | hy
    · exact Or.inr ⟨1, one_mem H, (mul_one _).symm⟩
    · exact Or.inl hy
  | one => exact Or.inl (one_mem H)
  | mul a b _ _ ha hb =>
    rcases ha with ha | ⟨h, hh, rfl⟩ <;> rcases hb with hb | ⟨h', hh', rfl⟩
    · exact Or.inl (mul_mem ha hb)
    · refine Or.inr ⟨(s⁻¹ * a * s) * h', mul_mem (hn' a ha) hh', ?_⟩
      group
    · exact Or.inr ⟨h * b, mul_mem hh hb, by group⟩
    · refine Or.inl ?_
      have : s * h * (s * h') = (s * s) * (s⁻¹ * h * s) * h' := by group
      rw [this]
      exact mul_mem (mul_mem hs (hn' h hh)) hh'
  | inv a _ ha =>
    rcases ha with ha | ⟨h, hh, rfl⟩
    · exact Or.inl (inv_mem ha)
    · refine Or.inr ⟨(s⁻¹ * h⁻¹ * s) * (s * s)⁻¹, mul_mem (hn' _ (inv_mem hh)) (inv_mem hs), ?_⟩
      group

theorem conj_mem_of_forall_mem {S : Set G} {K : Subgroup G} (s : G)
    (hS : ∀ g ∈ S, s * g * s⁻¹ ∈ K) {h : G} (hh : h ∈ closure S) : s * h * s⁻¹ ∈ K := by
  induction hh using Subgroup.closure_induction with
  | mem y hy => exact hS y hy
  | one => simpa using one_mem K
  | mul a b _ _ ha hb =>
    have : s * (a * b) * s⁻¹ = (s * a * s⁻¹) * (s * b * s⁻¹) := by group
    rw [this]
    exact mul_mem ha hb
  | inv a _ ha =>
    have : s * a⁻¹ * s⁻¹ = (s * a * s⁻¹)⁻¹ := by group
    rw [this]
    exact inv_mem ha

theorem exists_zpow_mul_zpow_of_mem_closure {x y : G} (hxy : x * y = y * x) {g : G}
    (hg : g ∈ closure ({x, y} : Set G)) : ∃ i j : ℤ, g = x ^ i * y ^ j := by
  have hc : Commute x y := hxy
  induction hg using Subgroup.closure_induction with
  | mem a ha =>
    rcases ha with rfl | ha
    · exact ⟨1, 0, by simp⟩
    · rw [Set.mem_singleton_iff] at ha
      subst ha
      exact ⟨0, 1, by simp⟩
  | one => exact ⟨0, 0, by simp⟩
  | mul a b _ _ ha hb =>
    obtain ⟨i, j, rfl⟩ := ha
    obtain ⟨k, l, rfl⟩ := hb
    refine ⟨i + k, j + l, ?_⟩
    have h1 : y ^ j * x ^ k = x ^ k * y ^ j := (hc.symm.zpow_zpow j k).eq
    calc x ^ i * y ^ j * (x ^ k * y ^ l) = x ^ i * (y ^ j * x ^ k) * y ^ l := by group
      _ = x ^ i * (x ^ k * y ^ j) * y ^ l := by rw [h1]
      _ = x ^ (i + k) * y ^ (j + l) := by rw [zpow_add, zpow_add]; group
  | inv a _ ha =>
    obtain ⟨i, j, rfl⟩ := ha
    refine ⟨-i, -j, ?_⟩
    rw [mul_inv_rev, ← zpow_neg, ← zpow_neg]
    exact (hc.symm.zpow_zpow (-j) (-i)).eq

theorem exists_normal_form_dihedral {t x : G} (ht2 : t * t = 1) (htx : t * x * t⁻¹ = x⁻¹)
    {g : G} (hg : g ∈ closure ({t, x} : Set G)) : ∃ i : ℤ, g = x ^ i ∨ g = t * x ^ i := by
  have hn : ∀ h ∈ zpowers x, t * h * t⁻¹ ∈ zpowers x := by
    intro h hh
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hh
    rw [← conj_zpow, htx]
    exact zpow_mem (inv_mem (mem_zpowers x)) i
  have hsub : closure ({t, x} : Set G) ≤ closure (insert t ((zpowers x : Subgroup G) : Set G)) := by
    rw [closure_le]
    intro y hy
    rcases hy with rfl | hy
    · exact subset_closure (Set.mem_insert _ _)
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact subset_closure (Set.mem_insert_of_mem _ (mem_zpowers y))
  rcases mem_or_mul_mem_of_closure_insert (by rw [ht2]; exact one_mem _) hn (hsub hg) with
    h | ⟨h, hh, rfl⟩
  · obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp h
    exact ⟨i, Or.inl rfl⟩
  · obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hh
    exact ⟨i, Or.inr rfl⟩

theorem exists_normal_form_triple {t x u₀ : G} (ht2 : t * t = 1) (htx : t * x * t⁻¹ = x⁻¹)
    (htu : u₀ * t = t * u₀) (hxu : u₀ * x = x * u₀) {g : G}
    (hg : g ∈ closure ({t, x, u₀} : Set G)) :
    ∃ i j : ℤ, g = x ^ i * u₀ ^ j ∨ g = t * (x ^ i * u₀ ^ j) := by
  have hn : ∀ h ∈ closure ({x, u₀} : Set G), t * h * t⁻¹ ∈ closure ({x, u₀} : Set G) := by
    intro h hh
    refine conj_mem_of_forall_mem t ?_ hh
    intro y hy
    rcases hy with rfl | hy
    · rw [htx]
      exact inv_mem (subset_closure (by simp))
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      have : t * y * t⁻¹ = y := by
        rw [mul_inv_eq_iff_eq_mul, ← htu]
      rw [this]
      exact subset_closure (by simp)
  have hsub : closure ({t, x, u₀} : Set G) ≤
      closure (insert t ((closure ({x, u₀} : Set G) : Subgroup G) : Set G)) := by
    rw [closure_le]
    intro y hy
    rcases hy with rfl | hy
    · exact subset_closure (Set.mem_insert _ _)
    · refine subset_closure (Set.mem_insert_of_mem _ (subset_closure ?_))
      rcases hy with rfl | hy
      · simp
      · simp [Set.mem_singleton_iff.mp hy]
  rcases mem_or_mul_mem_of_closure_insert (by rw [ht2]; exact one_mem _) hn (hsub hg) with
    h | ⟨h, hh, rfl⟩
  · obtain ⟨i, j, rfl⟩ := exists_zpow_mul_zpow_of_mem_closure hxu.symm h
    exact ⟨i, j, Or.inl rfl⟩
  · obtain ⟨i, j, rfl⟩ := exists_zpow_mul_zpow_of_mem_closure hxu.symm hh
    exact ⟨i, j, Or.inr rfl⟩

theorem two_mul_card_le {A B : Subgroup G} [Finite G] (hAB : A ≤ B) {a : G} (haB : a ∈ B)
    (haA : a ∉ A) : 2 * Nat.card A ≤ Nat.card B := by
  obtain ⟨c, hc⟩ := Subgroup.card_dvd_of_le hAB
  have hpos : 0 < Nat.card B := Nat.card_pos
  have hApos : 0 < Nat.card A := Nat.card_pos
  rcases Nat.lt_or_ge c 2 with hc2 | hc2
  · exfalso
    interval_cases c
    · omega
    · have : A = B := Subgroup.eq_of_le_of_card_ge hAB (by omega)
      exact haA (this ▸ haB)
  · calc 2 * Nat.card A ≤ c * Nat.card A := Nat.mul_le_mul_right _ hc2
      _ = Nat.card B := by rw [hc, mul_comm]

end Generic

section Cyclic

variable {G : Type*} [Group G]

theorem zpow_two_mul_eq (x : G) (c : ℤ) : x ^ (2 * c) = (x ^ 2) ^ c := by
  rw [zpow_mul]
  simp

theorem two_pow_dvd_of_zpow_two_mul {x : G} {e : ℕ} (hx : orderOf x = 2 ^ (e + 1)) {i : ℤ}
    (h : x ^ (2 * i) = 1) : (2 : ℤ) ^ e ∣ i := by
  have h1 : ((2 ^ (e + 1) : ℕ) : ℤ) ∣ 2 * i := by
    rw [← hx]
    exact orderOf_dvd_iff_zpow_eq_one.mpr h
  rw [pow_succ] at h1
  push_cast at h1
  rw [mul_comm ((2 : ℤ) ^ e) 2] at h1
  exact (mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0)).mp h1

theorem eq_pow_of_mem_zpowers_of_mul_self {x y : G} {e : ℕ} (hx : orderOf x = 2 ^ (e + 1))
    (hy : y ∈ zpowers x) (hy2 : y * y = 1) (hy1 : y ≠ 1) : y = x ^ (2 ^ e) := by
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hy
  have hi : x ^ (2 * i) = 1 := by rw [two_mul, zpow_add]; exact hy2
  obtain ⟨m, hm⟩ := two_pow_dvd_of_zpow_two_mul hx hi
  have hw2 : x ^ (2 ^ e) * x ^ (2 ^ e) = 1 := by
    rw [← pow_add, ← two_mul, ← pow_succ', ← hx]
    exact pow_orderOf_eq_one x
  have hxi : x ^ i = (x ^ (2 ^ e)) ^ m := by
    rw [hm, zpow_mul]
    congr 1
    rw [← zpow_natCast]
    norm_cast
  rcases Int.even_or_odd' m with ⟨c, rfl | rfl⟩
  · exfalso
    apply hy1
    rw [hxi, zpow_mul, zpow_two, hw2, one_zpow]
  · rw [hxi, zpow_add_one, zpow_mul, zpow_two, hw2, one_zpow, one_mul]

theorem t_not_mem_zpowers {t x : G} (htx : t * x * t⁻¹ = x⁻¹) {e : ℕ} (he : 1 ≤ e)
    (hx : orderOf x = 2 ^ (e + 1)) : t ∉ zpowers x := by
  intro htm
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp htm
  have hcomm : t * x = x * t := by
    rw [← hk]
    exact ((Commute.refl x).zpow_left k).eq
  have h5 : x⁻¹ = x := by
    rw [← htx, hcomm]
    exact mul_inv_cancel_right x t
  have h6 : x ^ 2 = 1 := by
    rw [sq]
    have := mul_inv_cancel x
    rwa [h5] at this
  have h7 := orderOf_dvd_of_pow_eq_one h6
  rw [hx] at h7
  have h8 : 2 ^ (e + 1) ≤ 2 := Nat.le_of_dvd (by norm_num) h7
  have h9 : 2 ^ 2 ≤ 2 ^ (e + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem not_mem_zpowers_sq {u : G} (hu : orderOf u = 4) : u ∉ zpowers (u ^ 2) := by
  intro h
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp h
  have h1 : u ^ (2 * k - 1) = 1 := by
    rw [zpow_sub_one, zpow_two_mul_eq, hk, mul_inv_cancel]
  have h2 : ((4 : ℕ) : ℤ) ∣ 2 * k - 1 := by
    rw [← hu]
    exact orderOf_dvd_iff_zpow_eq_one.mpr h1
  obtain ⟨c, hc⟩ := h2
  push_cast at hc
  omega

theorem x_not_mem_closure_sq {t x : G} (ht2 : t * t = 1) (htx : t * x * t⁻¹ = x⁻¹) {e : ℕ}
    (he : 1 ≤ e) (hx : orderOf x = 2 ^ (e + 1)) : x ∉ closure ({t, x ^ 2} : Set G) := by
  intro hmem
  have htx2 : t * x ^ 2 * t⁻¹ = (x ^ 2)⁻¹ := by rw [← conj_pow, htx, inv_pow]
  obtain ⟨i, hi | hi⟩ := exists_normal_form_dihedral ht2 htx2 hmem
  · have h1 : x ^ (2 * i) = x := by
      rw [zpow_mul]
      simpa using hi.symm
    have h2 : x ^ (2 * i - 1) = 1 := by rw [zpow_sub_one, h1, mul_inv_cancel]
    have h3 : ((2 ^ (e + 1) : ℕ) : ℤ) ∣ 2 * i - 1 := by
      rw [← hx]
      exact orderOf_dvd_iff_zpow_eq_one.mpr h2
    obtain ⟨c, hc⟩ := h3
    have h4 : 2 * i - 1 = 2 * (2 ^ e * c) := by
      rw [hc]
      push_cast
      ring
    omega
  · have htm : t ∈ zpowers x := by
      have h1 : t = x * ((x ^ 2) ^ i)⁻¹ := by
        calc t = (t * (x ^ 2) ^ i) * ((x ^ 2) ^ i)⁻¹ := by group
          _ = x * ((x ^ 2) ^ i)⁻¹ := by rw [← hi]
      rw [h1]
      refine mul_mem (mem_zpowers x) (inv_mem ?_)
      rw [← zpow_natCast, ← zpow_mul]
      exact mem_zpowers_iff.mpr ⟨_, rfl⟩
    exact t_not_mem_zpowers htx he hx htm

end Cyclic

section Shape

variable {G : Type*} [Group G] {P T L : Subgroup G} {t z x u₀ : G} {n : ℕ}

theorem t_mem_T (hsh : TwoGroupShape P t z n x u₀ T) : t ∈ T := by
  rw [hsh.T_eq]
  exact subset_closure (by simp)

theorem x_mem_T (hsh : TwoGroupShape P t z n x u₀ T) : x ∈ T := by
  rw [hsh.T_eq]
  exact subset_closure (by simp)

theorem u_mem_T (hsh : TwoGroupShape P t z n x u₀ T) : u₀ ∈ T := by
  rw [hsh.T_eq]
  exact subset_closure (by simp)

theorem orderOf_x_eq (hsh : TwoGroupShape P t z n x u₀ T) : orderOf x = 2 ^ (n - 2 + 1) := by
  rw [hsh.ord_x]
  congr 1
  have := hsh.three_le
  omega

theorem z_ne_one (hsh : TwoGroupShape P t z n x u₀ T) : z ≠ 1 := by
  rw [← hsh.sq_u]
  intro h
  have := orderOf_dvd_of_pow_eq_one h
  rw [hsh.ord_u] at this
  omega

theorem mul_mem_iff_of_relIndex_two {a b : G} (hPL : (P ⊓ L).relIndex P = 2) (ha : a ∈ P)
    (hb : b ∈ P) : a * b ∈ L ↔ (a ∈ L ↔ b ∈ L) := by
  have h := mul_mem_iff_of_index_two (H := (P ⊓ L).subgroupOf P) hPL (a := ⟨a, ha⟩)
    (b := ⟨b, hb⟩)
  simpa [mem_subgroupOf, ha, hb] using h

theorem inf_L_eq_zpowers (hsh : TwoGroupShape P t z n x u₀ T) (ht2 : t * t = 1)
    (hLn : L.Normal) (htL : t ∉ L) (hPL : (P ⊓ L).relIndex P = 2) :
    closure ({t, x} : Set G) ⊓ L = zpowers x := by
  have htP : t ∈ P := hsh.T_le (t_mem_T hsh)
  have hxP : x ∈ P := hsh.T_le (x_mem_T hsh)
  by_cases hxL : x ∈ L
  · refine le_antisymm ?_ ?_
    · rintro g ⟨hgD, hgL⟩
      obtain ⟨i, hi | hi⟩ := exists_normal_form_dihedral ht2 hsh.inv_x hgD
      · rw [hi]
        exact zpow_mem (mem_zpowers x) i
      · exfalso
        apply htL
        have h1 : t = g * (x ^ i)⁻¹ := by rw [hi]; group
        rw [h1]
        exact mul_mem hgL (inv_mem (zpow_mem hxL i))
    · intro g hg
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hg
      exact ⟨zpow_mem (subset_closure (by simp)) i, zpow_mem hxL i⟩
  · exfalso
    obtain ⟨e, he1, hxe⟩ : ∃ e : ℕ, 1 ≤ e ∧ orderOf x = 2 ^ (e + 1) :=
      ⟨n - 2, by have := hsh.three_le; omega, orderOf_x_eq hsh⟩
    have hx2L : x ^ 2 ∈ L := by
      have := (mul_mem_iff_of_relIndex_two hPL hxP hxP).mpr Iff.rfl
      rwa [← sq] at this
    have hxL' : ∀ k : ℤ, x ^ (2 * k) ∈ L := fun k => by
      rw [zpow_two_mul_eq]
      exact zpow_mem hx2L k
    have hQ : closure {s : G | s ∈ P ∧ ∃ g : G, g * t * g⁻¹ = s} ≤
        closure ({t, x ^ 2} : Set G) := by
      rw [closure_le]
      rintro s ⟨hsP, g, rfl⟩
      have hsD := hsh.class_le_D g hsP
      have hsL : g * t * g⁻¹ ∉ L := fun hs => htL (by
        have := hLn.conj_mem _ hs g⁻¹
        simpa [mul_assoc] using this)
      have hs2 : (g * t * g⁻¹) * (g * t * g⁻¹) = 1 := by
        calc (g * t * g⁻¹) * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
          _ = 1 := by rw [ht2]; group
      obtain ⟨i, hi | hi⟩ := exists_normal_form_dihedral ht2 hsh.inv_x hsD
      · have h1 : x ^ (2 * i) = 1 := by
          rw [two_mul, zpow_add]
          rwa [hi] at hs2
        obtain ⟨m, hm⟩ := two_pow_dvd_of_zpow_two_mul hxe h1
        have h2 : (2 : ℤ) ∣ i := by
          rw [hm]
          exact Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) m
        obtain ⟨c, hc⟩ := h2
        rw [hi, hc, zpow_two_mul_eq]
        exact zpow_mem (subset_closure (by simp)) c
      · rcases Int.even_or_odd' i with ⟨c, rfl | rfl⟩
        · rw [hi, zpow_two_mul_eq]
          exact mul_mem (subset_closure (by simp)) (zpow_mem (subset_closure (by simp)) c)
        · exfalso
          apply hsL
          rw [hi]
          refine (mul_mem_iff_of_relIndex_two hPL htP (zpow_mem hxP _)).mpr (iff_of_false htL ?_)
          intro h
          rw [zpow_add_one] at h
          exact hxL ((Subgroup.mul_mem_cancel_left L (hxL' c)).mp h)
    have hDQ : closure ({t, x} : Set G) ≤ closure ({t, x ^ 2} : Set G) := by
      rw [← hsh.D_eq]
      exact hQ
    exact x_not_mem_closure_sq ht2 hsh.inv_x he1 hxe (hDQ (subset_closure (by simp)))

theorem inf_L_eq_of_u_mem (hsh : TwoGroupShape P t z n x u₀ T) (ht2 : t * t = 1) (htL : t ∉ L)
    (hxL : x ∈ L) (huL : u₀ ∈ L) :
    T ⊓ L = closure ({x, u₀} : Set G) ∧ IsMulCommutative (T ⊓ L : Subgroup G) := by
  have hH : closure ({x, u₀} : Set G) ≤ L := by
    rw [closure_le]
    intro y hy
    rcases hy with rfl | hy
    · exact hxL
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact huL
  have heq : T ⊓ L = closure ({x, u₀} : Set G) := by
    apply le_antisymm
    · rintro g ⟨hgT, hgL⟩
      rw [hsh.T_eq] at hgT
      obtain ⟨i, j, hij | hij⟩ :=
        exists_normal_form_triple ht2 hsh.inv_x hsh.comm_ut hsh.comm_ux hgT
      · rw [hij]
        exact mul_mem (zpow_mem (subset_closure (by simp)) i)
          (zpow_mem (subset_closure (by simp)) j)
      · exfalso
        apply htL
        have h1 : t = g * (x ^ i * u₀ ^ j)⁻¹ := by rw [hij]; group
        rw [h1]
        exact mul_mem hgL (inv_mem (mul_mem (zpow_mem hxL i) (zpow_mem huL j)))
    · refine le_inf ?_ hH
      rw [closure_le]
      intro y hy
      rcases hy with rfl | hy
      · exact x_mem_T hsh
      · rw [Set.mem_singleton_iff] at hy
        subst hy
        exact u_mem_T hsh
  refine ⟨heq, ?_⟩
  rw [heq]
  refine Subgroup.isMulCommutative_closure ?_
  intro a ha b hb _
  rcases ha with rfl | ha <;> rcases hb with rfl | hb
  · exact Commute.refl _
  · rw [Set.mem_singleton_iff] at hb
    subst hb
    exact hsh.comm_ux.symm
  · rw [Set.mem_singleton_iff] at ha
    subst ha
    exact hsh.comm_ux
  · rw [Set.mem_singleton_iff] at ha hb
    subst ha
    subst hb
    exact Commute.refl _

theorem inf_L_eq_of_u_not_mem (hsh : TwoGroupShape P t z n x u₀ T) (ht2 : t * t = 1)
    (htL : t ∉ L) (hPL : (P ⊓ L).relIndex P = 2) (hxL : x ∈ L) (huL : u₀ ∉ L) :
    T ⊓ L = closure ({x, t * u₀} : Set G) ∧ Sec622UniqueInv (T ⊓ L) := by
  have htP : t ∈ P := hsh.T_le (t_mem_T hsh)
  have huP : u₀ ∈ P := hsh.T_le (u_mem_T hsh)
  have hqL : t * u₀ ∈ L := (mul_mem_iff_of_relIndex_two hPL htP huP).mpr (iff_of_false htL huL)
  have hqT : t * u₀ ∈ T := mul_mem (t_mem_T hsh) (u_mem_T hsh)
  have hxu : u₀ * x * u₀⁻¹ = x := by rw [mul_inv_eq_iff_eq_mul, hsh.comm_ux]
  have hqx : t * u₀ * x * (t * u₀)⁻¹ = x⁻¹ := by
    have : t * u₀ * x * (t * u₀)⁻¹ = t * (u₀ * x * u₀⁻¹) * t⁻¹ := by group
    rw [this, hxu, hsh.inv_x]
  have hqq : t * u₀ * (t * u₀) = z := by
    calc t * u₀ * (t * u₀) = t * (u₀ * t) * u₀ := by group
      _ = t * (t * u₀) * u₀ := by rw [hsh.comm_ut]
      _ = (t * t) * (u₀ * u₀) := by group
      _ = z := by rw [ht2, one_mul, ← sq, hsh.sq_u]
  have hzx : z ∈ zpowers x := by
    rw [← hsh.z_eq]
    exact pow_mem (mem_zpowers x) _
  have hH' : closure ({x, t * u₀} : Set G) ≤ L := by
    rw [closure_le]
    intro y hy
    rcases hy with rfl | hy
    · exact hxL
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hqL
  have hHT : closure ({x, t * u₀} : Set G) ≤ T := by
    rw [closure_le]
    intro y hy
    rcases hy with rfl | hy
    · exact x_mem_T hsh
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hqT
  have heq : T ⊓ L = closure ({x, t * u₀} : Set G) := by
    apply le_antisymm
    · rintro g ⟨hgT, hgL⟩
      have hn : ∀ h ∈ closure ({x, t * u₀} : Set G),
          t * h * t⁻¹ ∈ closure ({x, t * u₀} : Set G) := by
        intro h hh
        refine conj_mem_of_forall_mem t ?_ hh
        intro y hy
        rcases hy with rfl | hy
        · rw [hsh.inv_x]
          exact inv_mem (subset_closure (by simp))
        · rw [Set.mem_singleton_iff] at hy
          subst hy
          have : t * (t * u₀) * t⁻¹ = t * u₀ := by
            calc t * (t * u₀) * t⁻¹ = (t * t) * u₀ * t⁻¹ := by group
              _ = u₀ * t⁻¹ := by rw [ht2, one_mul]
              _ = t * u₀ := by
                rw [mul_inv_eq_iff_eq_mul, mul_assoc, hsh.comm_ut, ← mul_assoc, ht2, one_mul]
          rw [this]
          exact subset_closure (by simp)
      have hsub : T ≤
          closure (insert t ((closure ({x, t * u₀} : Set G) : Subgroup G) : Set G)) := by
        rw [hsh.T_eq, closure_le]
        intro y hy
        rcases hy with rfl | hy
        · exact subset_closure (Set.mem_insert _ _)
        · rcases hy with rfl | hy
          · exact subset_closure (Set.mem_insert_of_mem _ (subset_closure (by simp)))
          · rw [Set.mem_singleton_iff] at hy
            subst hy
            have hy' : t * (t * y) ∈ closure (insert t ((closure ({x, t * y} : Set G) :
                Subgroup G) : Set G)) :=
              mul_mem (subset_closure (Set.mem_insert _ _))
                (subset_closure (Set.mem_insert_of_mem _ (subset_closure (by simp))))
            rwa [← mul_assoc, ht2, one_mul] at hy'
      rcases mem_or_mul_mem_of_closure_insert (by rw [ht2]; exact one_mem _) hn (hsub hgT) with
        h | ⟨h, hh, rfl⟩
      · exact h
      · exfalso
        apply htL
        have h1 : t = (t * h) * h⁻¹ := by group
        rw [h1]
        exact mul_mem hgL (inv_mem (hH' hh))
    · exact le_inf hHT hH'
  refine ⟨heq, ?_⟩
  have hHn : ∀ h ∈ zpowers x, t * u₀ * h * (t * u₀)⁻¹ ∈ zpowers x := by
    intro h hh
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hh
    rw [← conj_zpow, hqx]
    exact zpow_mem (inv_mem (mem_zpowers x)) i
  have hsub2 : closure ({x, t * u₀} : Set G) ≤
      closure (insert (t * u₀) ((zpowers x : Subgroup G) : Set G)) := by
    rw [closure_le]
    intro y hy
    rcases hy with rfl | hy
    · exact subset_closure (Set.mem_insert_of_mem _ (mem_zpowers y))
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact subset_closure (Set.mem_insert _ _)
  have hz1 := z_ne_one hsh
  have key : ∀ a ∈ closure ({x, t * u₀} : Set G), orderOf a = 2 → a = z := by
    intro a ha ha2
    have hmul : a * a = 1 := by rw [← sq]; rw [← ha2]; exact pow_orderOf_eq_one a
    have ha1 : a ≠ 1 := by
      intro h
      rw [h, orderOf_one] at ha2
      omega
    rcases mem_or_mul_mem_of_closure_insert (by rw [hqq]; exact hzx) hHn (hsub2 ha) with
      h | ⟨h, hh, rfl⟩
    · rw [← hsh.z_eq]
      exact eq_pow_of_mem_zpowers_of_mul_self (orderOf_x_eq hsh) h hmul ha1
    · exfalso
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hh
      have hzc : Commute z (x ^ j) := by
        rw [← hsh.z_eq]
        exact ((Commute.refl x).pow_left _).zpow_right j
      have h1 : t * u₀ * x ^ j * (t * u₀ * x ^ j) = z := by
        calc t * u₀ * x ^ j * (t * u₀ * x ^ j)
            = (t * u₀ * x ^ j * (t * u₀)⁻¹) * (t * u₀ * (t * u₀)) * x ^ j := by group
          _ = (x⁻¹) ^ j * z * x ^ j := by rw [← conj_zpow, hqx, hqq]
          _ = (x⁻¹) ^ j * (z * x ^ j) := by rw [mul_assoc]
          _ = (x⁻¹) ^ j * (x ^ j * z) := by rw [hzc.eq]
          _ = z := by rw [← mul_assoc, inv_zpow', ← zpow_add, neg_add_cancel, zpow_zero, one_mul]
      exact hz1 (h1.symm.trans hmul)
  intro a ha b hb ha2 hb2
  rw [heq] at ha hb
  exact (key a ha ha2).trans (key b hb hb2).symm

theorem relIndex_inf_eq_two {K : Subgroup G} (hKP : K ≤ P) (hPL : (P ⊓ L).relIndex P = 2)
    {a : G} (haK : a ∈ K) (haL : a ∉ L) : (K ⊓ L).relIndex K = 2 := by
  rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
  refine ⟨⟨a, haK⟩, fun b => ?_⟩
  have h := mul_mem_iff_of_relIndex_two hPL (hKP b.2) (hKP haK)
  by_cases hbL : (b : G) ∈ L
  · exact Or.inr ⟨⟨b.2, hbL⟩, fun hA => haL ((h.mp hA.2).mp hbL)⟩
  · exact Or.inl ⟨⟨mul_mem b.2 haK, h.mpr (iff_of_false hbL haL)⟩, fun hB => hbL hB.2⟩

theorem relIndex_T_eq_two (hsh : TwoGroupShape P t z n x u₀ T) (hTP : T ≠ P) :
    T.relIndex P = 2 := by
  rcases (Nat.dvd_prime Nat.prime_two).mp hsh.T_idx with h1 | h2
  · exact absurd (le_antisymm hsh.T_le (Subgroup.relIndex_eq_one.mp h1)) hTP
  · exact h2

theorem relIndex_inf_eq_two_of_ne (hsh : TwoGroupShape P t z n x u₀ T) (htL : t ∉ L)
    (hPL : (P ⊓ L).relIndex P = 2) (hTP : T ≠ P) : (T ⊓ L).relIndex (P ⊓ L) = 2 := by
  have hT2 := relIndex_T_eq_two hsh hTP
  have h1 : (T ⊓ L).relIndex T = 2 := relIndex_inf_eq_two hsh.T_le hPL (t_mem_T hsh) htL
  have e1 := Subgroup.relIndex_mul_relIndex (T ⊓ L) (P ⊓ L) P (inf_le_inf_right L hsh.T_le)
    inf_le_left
  have e2 := Subgroup.relIndex_mul_relIndex (T ⊓ L) T P inf_le_left hsh.T_le
  rw [hPL] at e1
  rw [h1, hT2] at e2
  omega

theorem n_le_four (hsh : TwoGroupShape P t z n x u₀ T)
    (hexp : ∀ g : G, (∃ k : ℕ, orderOf g = 2 ^ k) → g ^ 8 = 1) : n ≤ 4 := by
  have h8 := hexp x ⟨n - 1, hsh.ord_x⟩
  have h1 : 2 ^ (n - 1) ∣ 2 ^ 3 := by
    rw [← hsh.ord_x]
    exact orderOf_dvd_of_pow_eq_one (by simpa using h8)
  have := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp h1
  omega

theorem sixty_four_le_card [Finite G] (hsh : TwoGroupShape P t z n x u₀ T) (hn4 : n = 4)
    (hTP : T ≠ P) : 64 ≤ Nat.card P := by
  have hx8 : orderOf x = 8 := by
    rw [hsh.ord_x, hn4]
    norm_num
  have hxcard : Nat.card (zpowers x) = 8 := by rw [Nat.card_zpowers, hx8]
  have htx : t ∉ zpowers x :=
    t_not_mem_zpowers hsh.inv_x (e := 2) (by norm_num) (by rw [hx8]; norm_num)
  have hxD : x ∈ closure ({t, x} : Set G) := subset_closure (by simp)
  have htD : t ∈ closure ({t, x} : Set G) := subset_closure (by simp)
  have hZD : zpowers x ≤ closure ({t, x} : Set G) := (zpowers_le).mpr hxD
  have h1 := two_mul_card_le hZD htD htx
  have hDT : closure ({t, x} : Set G) ≤ T := by
    rw [closure_le]
    intro y hy
    rcases hy with rfl | hy
    · exact t_mem_T hsh
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact x_mem_T hsh
  have huD : u₀ ∉ closure ({t, x} : Set G) := by
    intro hu
    have h : u₀ ∈ zpowers u₀ ⊓ closure ({t, x} : Set G) := ⟨mem_zpowers u₀, hu⟩
    rw [hsh.inf_eq, ← hsh.sq_u] at h
    exact not_mem_zpowers_sq hsh.ord_u h
  have h2 := two_mul_card_le hDT (u_mem_T hsh) huD
  obtain ⟨a, haP, haT⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hsh.T_le hTP)
  have h3 := two_mul_card_le hsh.T_le haP haT
  omega

theorem exists_pow_eight_of_orderOf {Q : Type*} [Group Q] {a : Q} {e : ℕ} (he : 3 ≤ e)
    (ha : orderOf a = 2 ^ e) : ∃ y : Q, y ^ 8 = 1 ∧ y ^ 4 ≠ 1 := by
  have h8 : 8 ∣ orderOf a := by
    rw [ha]
    exact (Nat.pow_dvd_pow 2 he : 2 ^ 3 ∣ 2 ^ e)
  have hord : orderOf (a ^ (orderOf a / 8)) = 8 :=
    orderOf_pow_orderOf_div (by rw [ha]; positivity) h8
  refine ⟨a ^ (orderOf a / 8), ?_, ?_⟩
  · have := pow_orderOf_eq_one (a ^ (orderOf a / 8))
    rwa [hord] at this
  · exact pow_ne_one_of_lt_orderOf (by norm_num) (by rw [hord]; norm_num)

theorem exists_pow_eight_eq_one {Q : Type*} [Group Q] (hQ : 16 ≤ Nat.card Q)
    (h : (∃ m : ℕ, 1 ≤ m ∧ Nonempty (Q ≃* DihedralGroup (2 ^ m))) ∨
      ∃ k : ℕ, 4 ≤ k ∧ Nonempty (Q ≃* SemidihedralGroup k)) :
    ∃ y : Q, y ^ 8 = 1 ∧ y ^ 4 ≠ 1 := by
  rcases h with ⟨m, hm, ⟨e⟩⟩ | ⟨k, hk, ⟨e⟩⟩
  · have hm3 : 3 ≤ m := by
      by_contra hlt
      have h1 : m ≤ 2 := by omega
      have h2 : 2 ^ m ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) h1
      have h3 : Nat.card Q = 2 * 2 ^ m := by
        rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
      omega
    refine exists_pow_eight_of_orderOf hm3 (a := e.symm (DihedralGroup.r 1)) ?_
    rw [MulEquiv.orderOf_eq, DihedralGroup.orderOf_r_one]
  · refine exists_pow_eight_of_orderOf (e := k - 1) (by omega)
      (a := e.symm (CFSG.Semidihedral.r k)) ?_
    rw [MulEquiv.orderOf_eq, CFSG.Semidihedral.orderOf_r k (by omega)]
    rfl

theorem prod_zpow_pow_eq {x y : G} (hxy : x * y = y * x) (i j : ℤ) (k : ℕ) :
    (x ^ i * y ^ j) ^ k = x ^ (i * k) * y ^ (j * k) := by
  have hc : Commute (x ^ i) (y ^ j) := Commute.zpow_zpow hxy i j
  rw [hc.mul_pow, ← zpow_natCast (x ^ i) k, ← zpow_natCast (y ^ j) k, ← zpow_mul, ← zpow_mul]

theorem pow_eight_eq_z (hsh : TwoGroupShape P t z n x u₀ T) (ht2 : t * t = 1) (hn4 : n = 4)
    {g : G} (hg2 : g ^ 2 ∈ T) (hg4 : g ^ 4 ∉ zpowers u₀) : g ^ 8 = z := by
  have hx4 : x ^ 4 = z := by
    have := hsh.z_eq
    rw [hn4] at this
    simpa using this
  have hu4 : u₀ ^ 4 = 1 := by
    rw [← hsh.ord_u]
    exact pow_orderOf_eq_one u₀
  have hz2 : z ^ 2 = 1 := by
    rw [← hsh.sq_u, ← pow_mul]
    exact hu4
  rw [hsh.T_eq] at hg2
  obtain ⟨i, j, h | h⟩ := exists_normal_form_triple ht2 hsh.inv_x hsh.comm_ut hsh.comm_ux hg2
  · have h4 : g ^ 4 = x ^ (i * 2) * u₀ ^ (j * 2) := by
      have := prod_zpow_pow_eq hsh.comm_ux.symm i j 2
      push_cast at this
      rw [show g ^ 4 = (g ^ 2) ^ 2 by rw [← pow_mul], h]
      exact this
    have h8 : g ^ 8 = x ^ (i * 4) * u₀ ^ (j * 4) := by
      have := prod_zpow_pow_eq hsh.comm_ux.symm i j 4
      push_cast at this
      rw [show g ^ 8 = (g ^ 2) ^ 4 by rw [← pow_mul], h]
      exact this
    rcases Int.even_or_odd' i with ⟨c, rfl | rfl⟩
    · exfalso
      apply hg4
      rw [h4]
      have h5 : x ^ (2 * c * 2) = u₀ ^ (2 * c) := by
        have : x ^ (2 * c * 2) = (x ^ 4) ^ c := by
          rw [show (2 * c * 2 : ℤ) = 4 * c by ring, zpow_mul]
          simp
        rw [this, hx4, ← hsh.sq_u, ← zpow_two_mul_eq]
      rw [h5]
      exact mul_mem (zpow_mem (mem_zpowers u₀) _) (zpow_mem (mem_zpowers u₀) _)
    · rw [h8]
      have h6 : x ^ ((2 * c + 1) * 4) = z := by
        have : x ^ ((2 * c + 1) * 4) = (x ^ 4) ^ (2 * c + 1) := by
          rw [mul_comm, zpow_mul]
          simp
        rw [this, hx4, zpow_add_one, zpow_two_mul_eq, hz2, one_zpow, one_mul]
      have h7 : u₀ ^ (j * 4) = 1 := by
        rw [mul_comm, zpow_mul]
        simp [hu4]
      rw [h6, h7, mul_one]
  · exfalso
    apply hg4
    have hconj : t * (x ^ i * u₀ ^ j) * t⁻¹ = (x ^ i)⁻¹ * u₀ ^ j := by
      have h1 : t * (x ^ i * u₀ ^ j) * t⁻¹ = (t * x ^ i * t⁻¹) * (t * u₀ ^ j * t⁻¹) := by group
      have h2 : t * u₀ * t⁻¹ = u₀ := mul_inv_eq_iff_eq_mul.mpr hsh.comm_ut.symm
      rw [h1, ← conj_zpow, ← conj_zpow, hsh.inv_x, h2, inv_zpow]
    have hcomm : u₀ ^ j * x ^ i = x ^ i * u₀ ^ j :=
      (Commute.zpow_zpow (hsh.comm_ux : u₀ * x = x * u₀) j i).eq
    have h1 : g ^ 4 = u₀ ^ (j + j) := by
      rw [show g ^ 4 = (g ^ 2) ^ 2 by rw [← pow_mul], h, sq]
      calc t * (x ^ i * u₀ ^ j) * (t * (x ^ i * u₀ ^ j))
          = (t * (x ^ i * u₀ ^ j) * t⁻¹) * (t * t) * (x ^ i * u₀ ^ j) := by group
        _ = (x ^ i)⁻¹ * u₀ ^ j * (x ^ i * u₀ ^ j) := by rw [hconj, ht2, mul_one]
        _ = (x ^ i)⁻¹ * (u₀ ^ j * x ^ i) * u₀ ^ j := by group
        _ = (x ^ i)⁻¹ * (x ^ i * u₀ ^ j) * u₀ ^ j := by rw [hcomm]
        _ = u₀ ^ (j + j) := by rw [zpow_add]; group
    rw [h1]
    exact zpow_mem (mem_zpowers u₀) _

theorem n_eq_three [Finite G] (hsh : TwoGroupShape P t z n x u₀ T) (ht2 : t * t = 1)
    (hexp : ∀ g : G, (∃ k : ℕ, orderOf g = 2 ^ k) → g ^ 8 = 1) (hP : IsPGroup 2 P)
    (hTP : T ≠ P) : n = 3 := by
  have hn4 := n_le_four hsh hexp
  by_contra hne
  have hn4' : n = 4 := by
    have := hsh.three_le
    omega
  have hcard := sixty_four_le_card hsh hn4' hTP
  obtain ⟨hnorm, hq⟩ := hsh.quot
  have huP : u₀ ∈ P := hsh.T_le (u_mem_T hsh)
  have hU : Nat.card ((zpowers u₀).subgroupOf P) = 4 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe ((zpowers_le).mpr huP)).toEquiv, Nat.card_zpowers,
      hsh.ord_u]
  have hQcard : 16 ≤ Nat.card (P ⧸ (zpowers u₀).subgroupOf P) := by
    have h := card_eq_card_quotient_mul_card_subgroup ((zpowers u₀).subgroupOf P)
    rw [hU] at h
    omega
  obtain ⟨y, hy8, hy4⟩ := exists_pow_eight_eq_one hQcard hq
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
  have hg4 : (g : G) ^ 4 ∉ zpowers u₀ := by
    intro h
    apply hy4
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact h
  have hT2 : T.relIndex P = 2 := relIndex_T_eq_two hsh hTP
  have hg2 : (g : G) ^ 2 ∈ T := by
    haveI : (T.subgroupOf P).Normal := normal_of_index_eq_two hT2
    have h := pow_index_mem (T.subgroupOf P) g
    have h2 : (T.subgroupOf P).index = 2 := hT2
    rw [h2] at h
    exact h
  have hg2el : ∃ k : ℕ, orderOf (g : G) = 2 ^ k := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hP g
    exact ⟨k, by rw [Subgroup.orderOf_coe]; exact hk⟩
  exact z_ne_one hsh ((pow_eight_eq_z hsh ht2 hn4' hg2 hg4).symm.trans (hexp _ hg2el))

end Shape

section OrderEight

variable {H : Type*} [Group H]

theorem order_eight_cases [Finite H] (h8 : Nat.card H = 8) {w : H} (hw4 : orderOf w = 4) :
    IsMulCommutative H ∨ Nonempty (H ≃* DihedralGroup 4) ∨
      ∀ a b : H, orderOf a = 2 → orderOf b = 2 → a = b := by
  set W : Subgroup H := zpowers w with hW
  have hw4' : w ^ 4 = 1 := by
    rw [← hw4]
    exact pow_orderOf_eq_one w
  have hWcard : Nat.card W = 4 := by rw [hW, Nat.card_zpowers, hw4]
  have hWidx : W.index = 2 := by
    have h := W.card_mul_index
    rw [hWcard, h8] at h
    omega
  have hmul : ∀ {a b : H}, a * b ∈ W ↔ (a ∈ W ↔ b ∈ W) := fun {a b} =>
    mul_mem_iff_of_index_two hWidx
  have hWtop : W ≠ ⊤ := fun h => by
    rw [h, index_top] at hWidx
    omega
  obtain ⟨a, haW⟩ : ∃ a : H, a ∉ W := by
    by_contra hcon
    push Not at hcon
    exact hWtop (eq_top_iff.mpr fun x _ => hcon x)
  have hcos : ∀ b : H, b ∉ W → ∀ c : H, c ∈ W ∨ ∃ i : ℤ, c = b * w ^ i := by
    intro b hb c
    by_cases hc : c ∈ W
    · exact Or.inl hc
    · right
      have h1 : b⁻¹ * c ∈ W :=
        hmul.mpr (iff_of_false (fun h => hb (inv_mem_iff.mp h)) hc)
      obtain ⟨i, hi⟩ := mem_zpowers_iff.mp h1
      exact ⟨i, by rw [hi]; group⟩
  have hconj : ∀ b : H, b ∉ W → b * w * b⁻¹ = w ∨ b * w * b⁻¹ = w⁻¹ := by
    intro b hb
    have hWn : W.Normal := normal_of_index_eq_two hWidx
    have hmem : b * w * b⁻¹ ∈ W := hWn.conj_mem w (mem_zpowers w) b
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hmem
    have hk4 : w ^ (k % 4) = b * w * b⁻¹ := by
      have h1 := zpow_mod_orderOf w k
      rw [hw4] at h1
      push_cast at h1
      rw [h1, hk]
    rcases (by omega : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3) with h0 | h1 | h2 | h3
    · exfalso
      rw [h0, zpow_zero] at hk4
      have hw1 : w = 1 := by
        calc w = b⁻¹ * (b * w * b⁻¹) * b := by group
          _ = 1 := by rw [← hk4]; group
      rw [hw1, orderOf_one] at hw4
      omega
    · rw [h1, zpow_one] at hk4
      exact Or.inl hk4.symm
    · exfalso
      have hk4' : w ^ 2 = b * w * b⁻¹ := by
        rw [← hk4, h2]
        simp
      have hsq : (b * w * b⁻¹) ^ 2 = 1 := by
        rw [← hk4', ← pow_mul]
        exact hw4'
      have hw2 : w ^ 2 ≠ 1 := pow_ne_one_of_lt_orderOf (by norm_num) (by rw [hw4]; norm_num)
      apply hw2
      calc w ^ 2 = b⁻¹ * (b * w ^ 2 * b⁻¹) * b := by group
        _ = b⁻¹ * (b * w * b⁻¹) ^ 2 * b := by rw [conj_pow]
        _ = 1 := by rw [hsq]; group
    · rw [h3] at hk4
      have h33 : w ^ (3 : ℤ) = w⁻¹ := by
        have : w ^ 3 = w⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact hw4')
        simpa using this
      exact Or.inr (hk4.symm.trans h33)
  have hw2' : orderOf w = 2 ^ (1 + 1) := by rw [hw4]; norm_num
  rcases hconj a haW with ha | ha
  ·
    left
    have hc : Commute a w := mul_inv_eq_iff_eq_mul.mp ha
    have hcw : ∀ i : ℤ, Commute (w ^ i) a := fun i => hc.symm.zpow_left i
    have hww : ∀ i j : ℤ, Commute (w ^ i) (w ^ j) := fun i j => (Commute.refl w).zpow_zpow i j
    have hforms : ∀ c : H, ∃ i : ℤ, c = w ^ i ∨ c = a * w ^ i := by
      intro c
      rcases hcos a haW c with hc' | ⟨i, hi⟩
      · obtain ⟨i, hi⟩ := mem_zpowers_iff.mp hc'
        exact ⟨i, Or.inl hi.symm⟩
      · exact ⟨i, Or.inr hi⟩
    refine IsMulCommutative.of_comm fun b c => ?_
    obtain ⟨i, rfl | rfl⟩ := hforms b <;> obtain ⟨j, rfl | rfl⟩ := hforms c
    · exact (hww i j).eq
    · exact ((hcw i).mul_right (hww i j)).eq
    · exact (((hcw j).symm).mul_left (hww i j)).eq
    · exact (((Commute.refl a).mul_left (hcw i)).mul_right
        (((hcw j).symm).mul_left (hww i j))).eq
  ·
    right
    have hinv : ∀ b : H, b ∉ W → b * w * b⁻¹ = w⁻¹ := by
      intro b hb
      rcases hcos a haW b with hbW | ⟨i, rfl⟩
      · exact absurd hbW hb
      · calc a * w ^ i * w * (a * w ^ i)⁻¹ = a * (w ^ i * w * (w ^ i)⁻¹) * a⁻¹ := by group
          _ = a * w * a⁻¹ := by group
          _ = w⁻¹ := ha
    by_cases hinvol : ∃ b : H, b ∉ W ∧ b ^ 2 = 1
    · left
      obtain ⟨b, hbW, hb2⟩ := hinvol
      have hgen : (⊤ : Subgroup H) = zpowers w ⊔ zpowers b := by
        apply le_antisymm
        · intro c _
          rcases hcos b hbW c with hc | ⟨i, rfl⟩
          · exact mem_sup_left hc
          · exact mul_mem (mem_sup_right (mem_zpowers b))
              (mem_sup_left (zpow_mem (mem_zpowers w) i))
        · exact le_top
      have := CFSG.GorensteinWalter.dihedral_of_generators_of_not_mem w b hgen hb2 (hinv b hbW)
        hbW
      rwa [hw4] at this
    · right
      push Not at hinvol
      have key : ∀ c : H, orderOf c = 2 → c = w ^ 2 := by
        intro c hc
        have hc2 : c * c = 1 := by
          rw [← sq, ← hc]
          exact pow_orderOf_eq_one c
        have hc1 : c ≠ 1 := by
          intro h
          rw [h, orderOf_one] at hc
          omega
        have hcW : c ∈ W := by
          by_contra hcW
          exact hinvol c hcW (by rw [sq]; exact hc2)
        have := eq_pow_of_mem_zpowers_of_mul_self hw2' hcW hc2 hc1
        simpa using this
      intro c d hc hd
      rw [key c hc, key d hd]

end OrderEight

section Extension

variable {G : Type*} [Group G]

theorem extension_facts {M L : Subgroup G} {t : G} (ht2 : t * t = 1) (hML : M ≤ L)
    (htL : t ∉ L) (hMt : ∀ m ∈ M, t * m * t⁻¹ ∈ M) :
    ∃ P : Subgroup G, M ≤ P ∧ t ∈ P ∧ P ⊓ L = M ∧ (P ⊓ L).relIndex P = 2 ∧
      Nat.card P = 2 * Nat.card M := by
  set P : Subgroup G := closure (insert t (M : Set G)) with hP
  have hnf : ∀ g ∈ P, g ∈ M ∨ ∃ m ∈ M, g = t * m := fun g hg =>
    mem_or_mul_mem_of_closure_insert (by rw [ht2]; exact one_mem M) hMt hg
  have hMP : M ≤ P := fun m hm => subset_closure (Set.mem_insert_of_mem _ hm)
  have htP : t ∈ P := subset_closure (Set.mem_insert _ _)
  have htM : t ∉ M := fun h => htL (hML h)
  have hPL : P ⊓ L = M := by
    apply le_antisymm
    · rintro g ⟨hgP, hgL⟩
      rcases hnf g hgP with h | ⟨m, hm, rfl⟩
      · exact h
      · exfalso
        apply htL
        have : t = (t * m) * m⁻¹ := by group
        rw [this]
        exact mul_mem hgL (inv_mem (hML hm))
    · exact le_inf hMP hML
  have hidx : M.relIndex P = 2 := by
    rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
    refine ⟨⟨t, htP⟩, fun b => ?_⟩
    rcases hnf b b.2 with hbM | ⟨m, hm, hbm⟩
    · exact Or.inr ⟨hbM, fun hA => htM ((Subgroup.mul_mem_cancel_left M hbM).mp hA)⟩
    · refine Or.inl ⟨?_, fun hB => htM ?_⟩
      · show (b : G) * t ∈ M
        rw [hbm]
        have := hMt m hm
        rwa [inv_eq_of_mul_eq_one_right ht2] at this
      · have hB' : (b : G) ∈ M := hB
        rw [hbm] at hB'
        have : t = (t * m) * m⁻¹ := by group
        rw [this]
        exact mul_mem hB' (inv_mem hm)
  refine ⟨P, hMP, htP, hPL, ?_, ?_⟩
  · rw [hPL]
    exact hidx
  · have h1 := Subgroup.card_mul_index (M.subgroupOf P)
    have h2 : Nat.card (M.subgroupOf P) = Nat.card M :=
      Nat.card_congr (subgroupOfEquivOfLe hMP).toEquiv
    have h3 : (M.subgroupOf P).index = 2 := hidx
    rw [h2, h3] at h1
    omega

end Extension

end CFSG.LocalAnalysis.EvenBN.Tits.I21.SixTwoB

namespace CFSG.LocalAnalysis.EvenBN.Tits

open Subgroup CFSG.Open

variable {G : Type} [Group G] [Finite G] {t u x : G}

theorem sec622_order_eight {M : Subgroup G} (hM : IsPGroup 2 M) (h8 : Nat.card M = 8) {w : G}
    (hw : w ∈ M) (hw4 : orderOf w = 4) :
    IsMulCommutative M ∨ Nonempty (M ≃* DihedralGroup 4) ∨ Sec622UniqueInv M := by
  have hw4' : orderOf (⟨w, hw⟩ : M) = 4 := by
    rw [Subgroup.orderOf_mk]
    exact hw4
  rcases I21.SixTwoB.order_eight_cases h8 hw4' with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · refine Or.inr (Or.inr fun a ha b hb ha2 hb2 => ?_)
    have := h ⟨a, ha⟩ ⟨b, hb⟩ (by rw [Subgroup.orderOf_mk]; exact ha2)
      (by rw [Subgroup.orderOf_mk]; exact hb2)
    exact congrArg Subtype.val this

theorem sec622_six_two_b (h : SecTwoHyp G t u)
    (hexp : ∀ g : G, (∃ k : ℕ, orderOf g = 2 ^ k) → g ^ 8 = 1) {L : Subgroup G}
    (hLn : L.Normal) (htL : t ∉ L) {P : Subgroup G} (hP : IsPGroup 2 P)
    (hRP : secTwoR t u ≤ P) (hPL : (P ⊓ L).relIndex P = 2) {T : Subgroup G} {n : ℕ} {x u₀ : G}
    (hsh : TwoGroupShape P t (u ^ 2) n x u₀ T) :
    closure {t, x} ⊓ L = zpowers x ∧ n ≤ 4 ∧
      ((T ⊓ L = closure {x, u₀} ∧ IsMulCommutative (T ⊓ L : Subgroup G)) ∨
        (T ⊓ L = closure {x, t * u₀} ∧ Sec622UniqueInv (T ⊓ L))) ∧
      (T = P → P ⊓ L = T ⊓ L) ∧ (T ≠ P → (T ⊓ L).relIndex (P ⊓ L) = 2 ∧ n = 3) := by
  have ht2 : t * t = 1 := h.t_mul_t
  have hD := I21.SixTwoB.inf_L_eq_zpowers hsh ht2 hLn htL hPL
  have hxL : x ∈ L := (hD ▸ mem_zpowers x : x ∈ closure {t, x} ⊓ L).2
  refine ⟨hD, I21.SixTwoB.n_le_four hsh hexp, ?_, fun hTP => by rw [hTP], fun hTP => ⟨?_, ?_⟩⟩
  · by_cases huL : u₀ ∈ L
    · exact Or.inl (I21.SixTwoB.inf_L_eq_of_u_mem hsh ht2 htL hxL huL)
    · exact Or.inr (I21.SixTwoB.inf_L_eq_of_u_not_mem hsh ht2 htL hPL hxL huL)
  · exact I21.SixTwoB.relIndex_inf_eq_two_of_ne hsh htL hPL hTP
  · exact I21.SixTwoB.n_eq_three hsh ht2 hexp hP hTP

theorem sec622_six_two_of (h : SecTwoHyp G t u)
    (hexp : ∀ g : G, (∃ k : ℕ, orderOf g = 2 ^ k) → g ^ 8 = 1) {L M : Subgroup G}
    (hLn : L.Normal) (htL : t ∉ L) (hM2 : IsPGroup 2 M) (hML : M ≤ L)
    (hMt : ∀ m ∈ M, t * m * t⁻¹ ∈ M) {w : G} (hw : w = u ∨ w = t * u)
    (hCM : M ⊓ centralizer ({t} : Set G) = zpowers w)
    (h6a : ∀ {P : Subgroup G}, IsPGroup 2 P → secTwoR t u ≤ P →
      (((∃ V : Subgroup G, V ≤ P ∧ (∀ p ∈ P, ∀ v ∈ V, p * v * p⁻¹ ∈ V) ∧ IsElemAbelian 2 V ∧
          Nat.card V = 4 ∧ ∃ v ∈ V, ∃ g : G, g * t * g⁻¹ = v) ∧ Nat.card P ≤ 16) ∨
        ∃ (T : Subgroup G) (n : ℕ) (x u₀ : G), TwoGroupShape P t (u ^ 2) n x u₀ T))
    (h6c : ∀ {L' : Subgroup G}, L'.Normal → t ∉ L' → ∀ {P : Subgroup G}, IsPGroup 2 P →
      secTwoR t u ≤ P → (P ⊓ L').relIndex P = 2 → ∀ {T : Subgroup G} {x u₀ : G},
      TwoGroupShape P t (u ^ 2) 3 x u₀ T → T ≠ P →
      (T ⊓ L' = closure {x, u₀} ∨ T ⊓ L' = closure {x, t * u₀}) →
      IsMulCommutative (P ⊓ L' : Subgroup G) ∨ Sec622ProdDihedral (P ⊓ L') 3 ∨
        Sec622CentralInv (P ⊓ L') ∨ Sec622Order16 (P ⊓ L') ∨
        Nonempty (↥(P ⊓ L') ≃* SemidihedralGroup 4) ∨ Sec622UniqueInv (P ⊓ L')) :
    Sec622UniqueInv M ∨ IsMulCommutative M ∨ Nonempty (M ≃* SemidihedralGroup 4) ∨
      Nonempty (M ≃* DihedralGroup 4) ∨ Sec622Order16 M ∨ Sec622CentralInv M ∨
      Sec622ProdDihedral M 3 := by
  have ht2 : t * t = 1 := h.t_mul_t
  have hwM : w ∈ M := by
    have : w ∈ M ⊓ centralizer ({t} : Set G) := by
      rw [hCM]
      exact mem_zpowers w
    exact this.1
  have hw4 : orderOf w = 4 := by
    rcases hw with hw | hw
    · rw [hw]
      exact h.orderOf_u
    · have hc : Commute t u := h.commute
      have h2 : (t * u) ^ 2 = u ^ 2 := by rw [hc.mul_pow, h.t_sq, one_mul]
      have h4 : (t * u) ^ 2 ^ (1 + 1) = 1 := by
        rw [show 2 ^ (1 + 1) = 2 * 2 by norm_num, pow_mul, h2, ← pow_mul]
        exact h.u_pow_four
      have := orderOf_eq_prime_pow (p := 2) (n := 1) (x := t * u)
        (by rw [pow_one, h2]; exact h.z_ne_one) h4
      rw [hw]
      simpa using this
  obtain ⟨P, hMP, htP, hPLM, hPL, hPcard⟩ := I21.SixTwoB.extension_facts ht2 hML htL hMt
  have hP2 : IsPGroup 2 P := by
    obtain ⟨a, ha⟩ := hM2.exists_card_eq
    exact IsPGroup.of_card (n := a + 1) (by rw [hPcard, ha, pow_succ]; ring)
  have huP : u ∈ P := by
    rcases hw with hw | hw
    · rw [← hw]
      exact hMP hwM
    · have : u = t * w := by rw [hw, ← mul_assoc, ht2, one_mul]
      rw [this]
      exact mul_mem htP (hMP hwM)
  have hRP : secTwoR t u ≤ P := by
    unfold secTwoR
    rw [closure_le]
    intro y hy
    rcases hy with hy | hy
    · rw [hy]
      exact htP
    · rw [Set.mem_singleton_iff.mp hy]
      exact huP
  rcases h6a hP2 hRP with ⟨_, hcard16⟩ | ⟨T, n, x, u₀, hsh⟩
  ·
    have hM8 : Nat.card M ≤ 8 := by omega
    have hdvd : 4 ∣ Nat.card M := by
      have := Subgroup.orderOf_dvd_natCard M hwM
      rwa [hw4] at this
    have hpos : 0 < Nat.card M := Nat.card_pos
    have hcases : Nat.card M = 4 ∨ Nat.card M = 8 := by omega
    rcases hcases with h4 | h8
    · refine Or.inr (Or.inl (IsMulCommutative.of_comm ?_))
      exact IsPGroup.commutative_of_card_eq_prime_sq (p := 2) (by rw [h4]; norm_num)
    · rcases sec622_order_eight hM2 h8 hwM hw4 with h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inl h
  ·
    obtain ⟨_, _, h3, h4, h5⟩ := sec622_six_two_b h hexp hLn htL hP2 hRP hPL hsh
    by_cases hTP : T = P
    · have hMT : M = T ⊓ L := hPLM.symm.trans (h4 hTP)
      rcases h3 with ⟨_, hc⟩ | ⟨_, hu⟩
      · refine Or.inr (Or.inl ?_)
        rw [hMT]
        exact hc
      · refine Or.inl ?_
        rw [hMT]
        exact hu
    · obtain ⟨_, hn3⟩ := h5 hTP
      subst hn3
      have hTL : T ⊓ L = closure {x, u₀} ∨ T ⊓ L = closure {x, t * u₀} :=
        h3.imp And.left And.left
      have := h6c hLn htL hP2 hRP hPL hsh hTP hTL
      rw [hPLM] at this
      rcases this with h | h | h | h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inl h

end CFSG.LocalAnalysis.EvenBN.Tits
