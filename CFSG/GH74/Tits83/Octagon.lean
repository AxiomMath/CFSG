module

public import CFSG.GH74.Tits83.Nu

public section

namespace CFSG.GH74.Tits83

open CFSG.GH74.BNPair

open scoped commutatorElement Pointwise

universe u

variable {G : Type u} [Group G] {n : ℕ}

namespace TitsSystem

variable (T : TitsSystem G n)

theorem nu_mem {i : ℤ} {u : G} (hu : u ∈ T.U i) (hu1 : u ≠ 1) :
    T.nu i u ∈ T.U (i + n) :=
  (T.isMu_nu hu hu1).1

theorem nu'_mem {i : ℤ} {u : G} (hu : u ∈ T.U i) (hu1 : u ≠ 1) :
    T.nu' i u ∈ T.U (i + n) :=
  (T.isMu_nu hu hu1).2.1

theorem nu'_shift (hn : 3 ≤ n) (s i : ℤ) (u : G) :
    (T.shift s).nu' i u = T.nu' (i + s) u := by
  by_cases h : u ∈ T.U (i + s) ∧ u ≠ 1
  · have h' : u ∈ (T.shift s).U i ∧ u ≠ 1 := by
      refine ⟨?_, h.2⟩
      simpa [shift_U] using h.1
    have htrans : T.IsMu (i + s) u (T.nu (i + s) u) ((T.shift s).nu' i u) := by
      have hIs := (T.shift s).isMu_nu h'.1 h'.2
      have hh := (T.isMu_shift_iff s i u _ _).1 hIs
      rwa [T.nu_shift hn s i u] at hh
    exact (T.isMu_unique hn h.1 h.2 htrans (T.isMu_nu h.1 h.2)).2
  · have h' : ¬(u ∈ (T.shift s).U i ∧ u ≠ 1) := by
      simpa [shift_U] using h
    rw [(T.shift s).nu'_of_not_mem h', T.nu'_of_not_mem h]

theorem mu_shift (hn : 3 ≤ n) (s i : ℤ) (u : G) :
    (T.shift s).mu i u = T.mu (i + s) u := by
  by_cases h : u ∈ T.U (i + s) ∧ u ≠ 1
  · simp only [mu]
    rw [T.nu_shift hn s i u, T.nu'_shift hn s i u]
  · have h' : ¬(u ∈ (T.shift s).U i ∧ u ≠ 1) := by
      simpa [shift_U] using h
    simp only [mu]
    rw [(T.shift s).nu_of_not_mem h', (T.shift s).nu'_of_not_mem h',
      T.nu_of_not_mem h, T.nu'_of_not_mem h]

theorem nu'_refl (hn : 3 ≤ n) (c i : ℤ) (u : G) :
    (T.refl c).nu' i u = T.nu' (c - i) u := by
  by_cases h : u ∈ T.U (c - i) ∧ u ≠ 1
  · have h' : u ∈ (T.refl c).U i ∧ u ≠ 1 := by
      refine ⟨?_, h.2⟩
      simpa [refl_U] using h.1
    have htrans : T.IsMu (c - i) u (T.nu (c - i) u) ((T.refl c).nu' i u) := by
      have hIs := (T.refl c).isMu_nu h'.1 h'.2
      have hh := (T.isMu_refl_iff c i u _ _).1 hIs
      rwa [T.nu_refl hn c i u] at hh
    exact (T.isMu_unique hn h.1 h.2 htrans (T.isMu_nu h.1 h.2)).2
  · have h' : ¬(u ∈ (T.refl c).U i ∧ u ≠ 1) := by
      simpa [refl_U] using h
    rw [(T.refl c).nu'_of_not_mem h', T.nu'_of_not_mem h]

theorem mu_refl (hn : 3 ≤ n) (c i : ℤ) (u : G) :
    (T.refl c).mu i u = T.mu (c - i) u := by
  by_cases h : u ∈ T.U (c - i) ∧ u ≠ 1
  · simp only [mu]
    rw [T.nu_refl hn c i u, T.nu'_refl hn c i u]
  · have h' : ¬(u ∈ (T.refl c).U i ∧ u ≠ 1) := by
      simpa [refl_U] using h
    simp only [mu]
    rw [(T.refl c).nu_of_not_mem h', (T.refl c).nu'_of_not_mem h',
      T.nu_of_not_mem h, T.nu'_of_not_mem h]

theorem isMu_add_two_mul_iff (i k : ℤ) (u v w : G) :
    T.IsMu (i + 2 * n * k) u v w ↔ T.IsMu i u v w := by
  have h1 : (i + 2 * n * k) + n = (i + n) + 2 * n * k := by ring
  have h2 : ∀ j : ℤ,
      2 * (i + 2 * n * k) + n - j = (2 * i + n - j) + 2 * n * (2 * k) := by
    intro j
    ring
  constructor
  · rintro ⟨hv, hw, hm⟩
    refine ⟨?_, ?_, fun j => ?_⟩
    · rw [h1] at hv
      rwa [U_add_two_mul T (i + n) k] at hv
    · rw [h1] at hw
      rwa [U_add_two_mul T (i + n) k] at hw
    · have hj := hm j
      rw [h2 j] at hj
      rwa [U_add_two_mul T (2 * i + n - j) (2 * k)] at hj
  · rintro ⟨hv, hw, hm⟩
    refine ⟨?_, ?_, fun j => ?_⟩
    · rw [h1, U_add_two_mul T (i + n) k]
      exact hv
    · rw [h1, U_add_two_mul T (i + n) k]
      exact hw
    · rw [h2 j, U_add_two_mul T (2 * i + n - j) (2 * k)]
      exact hm j

theorem nu_add_two_mul (hn : 3 ≤ n) (i k : ℤ) (u : G) :
    T.nu (i + 2 * n * k) u = T.nu i u := by
  by_cases h : u ∈ T.U i ∧ u ≠ 1
  · have hu' : u ∈ T.U (i + 2 * n * k) := by
      rw [U_add_two_mul T i k]
      exact h.1
    have htrans : T.IsMu i u (T.nu (i + 2 * n * k) u) (T.nu' (i + 2 * n * k) u) :=
      (T.isMu_add_two_mul_iff i k u _ _).1 (T.isMu_nu hu' h.2)
    exact (T.isMu_unique hn h.1 h.2 htrans (T.isMu_nu h.1 h.2)).1
  · have h' : ¬(u ∈ T.U (i + 2 * n * k) ∧ u ≠ 1) := by
      rintro ⟨hu, hu1⟩
      exact h ⟨by rwa [U_add_two_mul T i k] at hu, hu1⟩
    rw [T.nu_of_not_mem h', T.nu_of_not_mem h]

theorem nu'_add_two_mul (hn : 3 ≤ n) (i k : ℤ) (u : G) :
    T.nu' (i + 2 * n * k) u = T.nu' i u := by
  by_cases h : u ∈ T.U i ∧ u ≠ 1
  · have hu' : u ∈ T.U (i + 2 * n * k) := by
      rw [U_add_two_mul T i k]
      exact h.1
    have htrans : T.IsMu i u (T.nu (i + 2 * n * k) u) (T.nu' (i + 2 * n * k) u) :=
      (T.isMu_add_two_mul_iff i k u _ _).1 (T.isMu_nu hu' h.2)
    exact (T.isMu_unique hn h.1 h.2 htrans (T.isMu_nu h.1 h.2)).2
  · have h' : ¬(u ∈ T.U (i + 2 * n * k) ∧ u ≠ 1) := by
      rintro ⟨hu, hu1⟩
      exact h ⟨by rwa [U_add_two_mul T i k] at hu, hu1⟩
    rw [T.nu'_of_not_mem h', T.nu'_of_not_mem h]

theorem mu_add_two_mul (hn : 3 ≤ n) (i k : ℤ) (u : G) :
    T.mu (i + 2 * n * k) u = T.mu i u := by
  by_cases h : u ∈ T.U i ∧ u ≠ 1
  · simp only [mu]
    rw [T.nu_add_two_mul hn i k u, T.nu'_add_two_mul hn i k u]
  · have h' : ¬(u ∈ T.U (i + 2 * n * k) ∧ u ≠ 1) := by
      rintro ⟨hu, hu1⟩
      exact h ⟨by rwa [U_add_two_mul T i k] at hu, hu1⟩
    simp only [mu]
    rw [T.nu_of_not_mem h', T.nu'_of_not_mem h',
      T.nu_of_not_mem h, T.nu'_of_not_mem h]

theorem nu_nu (hn : 3 ≤ n) {i : ℤ} {u : G} (hu : u ∈ T.U i) (hu1 : u ≠ 1) :
    T.nu (i + n) (T.nu i u) = T.mu i u * T.nu' i u * (T.mu i u)⁻¹ := by
  have hv : T.nu i u ∈ T.U (i + n) := T.nu_mem hu hu1
  have hv1 : T.nu i u ≠ 1 := T.nu_ne_one hn hu hu1
  have hdecomp : T.mu i u * T.nu' i u * (T.mu i u)⁻¹ * T.nu i u * u =
      T.mu i u := by
    simp only [mu]
    group
  have hbar : T.mu i u * T.nu' i u * (T.mu i u)⁻¹ ∈ T.U i := by
    have hmov : (T.U (i + n)).map (MulAut.conj (T.mu i u)).toMonoidHom = T.U i := by
      have h := (T.moves_mu hu hu1) (i + n)
      change (T.U (i + n)).map (MulAut.conj (T.mu i u)).toMonoidHom =
        T.U (2 * i + n - (i + n)) at h
      rwa [show 2 * i + n - (i + n) = i by ring] at h
    have hmem := CFSG.LieType.Steinberg.conj_mem_map_conj
      (g := T.mu i u) (T.nu'_mem hu hu1)
    rwa [hmov] at hmem
  have hIs : T.IsMu (i + n) (T.nu i u)
      (T.mu i u * T.nu' i u * (T.mu i u)⁻¹) u := by
    refine ⟨?_, ?_, ?_⟩
    · rw [show (i + n) + n = i + 2 * (n : ℤ) by ring, T.periodic i]
      exact hbar
    · rw [show (i + n) + n = i + 2 * (n : ℤ) by ring, T.periodic i]
      exact hu
    · intro j
      rw [hdecomp, (T.moves_mu hu hu1) j]
      change T.U (2 * i + n - j) = T.U (2 * (i + n) + n - j)
      rw [show 2 * (i + n) + n - j =
        (2 * i + n - j) + 2 * (n : ℤ) * 1 by ring,
        U_add_two_mul T (2 * i + n - j) 1]
  exact (T.isMu_unique hn hv hv1 hIs (T.isMu_nu hv hv1)).1.symm

theorem mu_eq_nu_nu (hn : 3 ≤ n) {i : ℤ} {u : G} (hu : u ∈ T.U i) (hu1 : u ≠ 1) :
    T.mu i u = T.nu (i + n) (T.nu i u) * T.nu i u * u := by
  rw [T.nu_nu hn hu hu1]
  simp only [mu]
  group

theorem mu_conj_self (hn : 3 ≤ n) {i : ℤ} {u : G} (hu : u ∈ T.U i) (hu1 : u ≠ 1) :
    T.mu (i + n) (T.mu i u * u * (T.mu i u)⁻¹) = T.mu i u := by
  have hg : T.Moves (T.mu i u) (fun j : ℤ => (-1 : ℤ) * j + (2 * i + n)) := by
    simpa [sub_eq_add_neg, neg_one_mul, add_comm, add_left_comm, add_assoc] using
      (T.moves_mu hu hu1)
  have h := (T.mu_conj hn (Or.inr rfl) hg hu hu1).1
  rw [show (-1 : ℤ) * i + (2 * i + n) = i + n by ring] at h
  calc
    T.mu (i + n) (T.mu i u * u * (T.mu i u)⁻¹) =
        T.mu i u * T.mu i u * (T.mu i u)⁻¹ := h
    _ = T.mu i u := by group

theorem win_eq_bot {a b : ℤ} (h : b < a) : win T.U a b = ⊥ := by
  simp [win, show ¬ a ≤ b by omega]

theorem U_le_win {a b k : ℤ} (ha : a ≤ k) (hb : k ≤ b) : T.U k ≤ win T.U a b :=
  le_iSup₂_of_le k ⟨ha, hb⟩ le_rfl

theorem win_mono {a b c d : ℤ} (hca : c ≤ a) (hbd : b ≤ d) :
    win T.U a b ≤ win T.U c d := by
  refine iSup₂_le fun k hk => ?_
  exact le_iSup₂_of_le k ⟨le_trans hca hk.1, le_trans hk.2 hbd⟩ le_rfl

theorem win_add_two_mul (a b k : ℤ) :
    win T.U (a + 2 * n * k) (b + 2 * n * k) = win T.U a b := by
  apply le_antisymm
  · refine iSup₂_le fun t ht => ?_
    refine le_iSup₂_of_le (t - 2 * (n : ℤ) * k) ?_ ?_
    · simp only [Set.mem_Icc] at ht ⊢
      omega
    · have h := U_add_two_mul T (t - 2 * (n : ℤ) * k) k
      rw [show t - 2 * (n : ℤ) * k + 2 * (n : ℤ) * k = t by ring] at h
      exact le_of_eq h
  · refine iSup₂_le fun t ht => ?_
    refine le_iSup₂_of_le (t + 2 * (n : ℤ) * k) ?_ ?_
    · simp only [Set.mem_Icc] at ht ⊢
      omega
    · exact le_of_eq (U_add_two_mul T t k).symm

theorem win_self (i : ℤ) : win T.U i i = T.U i := by
  simp [win]

theorem exists_mul_of_mem_win {a c b : ℤ} (h1 : a ≤ c + 1) (h2 : c ≤ b)
    (h3 : b < a + n) {x : G} (hx : x ∈ win T.U a b) :
    ∃ y ∈ win T.U a c, ∃ z ∈ win T.U (c + 1) b, x = y * z := by
  obtain ⟨f, hf, rfl⟩ := (T.mem_win_iff_prod h3).1 hx
  have hsplit : intList a b = intList a c ++ intList (c + 1) b := by
    apply List.ext_getElem
    · simp only [intList, List.length_append, List.length_map, List.length_range]
      omega
    · intro t ht1 ht2
      simp only [intList, List.length_map, List.length_range] at ht1 ht2 ⊢
      by_cases ht : t < (c + 1 - a).toNat
      · rw [List.getElem_append_left (by simpa using ht)]
        simp
      · rw [List.getElem_append_right (by simp; omega)]
        simp only [List.getElem_map, List.getElem_range, List.length_map,
          List.length_range]
        omega
  refine ⟨((intList a c).map f).prod, ?_, ((intList (c + 1) b).map f).prod, ?_, ?_⟩
  · refine (T.mem_win_iff_prod (a := a) (b := c) (by omega)).2 ⟨f, ?_, rfl⟩
    intro k hk
    exact hf k (by rw [hsplit]; exact List.mem_append_left _ hk)
  · refine (T.mem_win_iff_prod (a := c + 1) (b := b) (by omega)).2 ⟨f, ?_, rfl⟩
    intro k hk
    exact hf k (by rw [hsplit]; exact List.mem_append_right _ hk)
  · rw [hsplit, List.map_append, List.prod_append]

theorem eq_of_mul_eq_mul {a c b : ℤ} (h1 : a ≤ c + 1) (h2 : c ≤ b) (h3 : b < a + n)
    {x x' y y' : G} (hx : x ∈ win T.U a c) (hx' : x' ∈ win T.U a c)
    (hy : y ∈ win T.U (c + 1) b) (hy' : y' ∈ win T.U (c + 1) b)
    (h : x * y = x' * y') : x = x' ∧ y = y' := by
  have hxinv : x'⁻¹ * x ∈ win T.U a c :=
    (win T.U a c).mul_mem ((win T.U a c).inv_mem hx') hx
  have hyinv : y' * y⁻¹ ∈ win T.U (c + 1) b :=
    (win T.U (c + 1) b).mul_mem hy' ((win T.U (c + 1) b).inv_mem hy)
  have heq : x'⁻¹ * x = y' * y⁻¹ := by
    calc
      x'⁻¹ * x = x'⁻¹ * (x * y) * y⁻¹ := by group
      _ = x'⁻¹ * (x' * y') * y⁻¹ := by rw [h]
      _ = y' * y⁻¹ := by group
  have hmem : x'⁻¹ * x ∈ win T.U a c ⊓ win T.U (c + 1) b := by
    refine ⟨hxinv, ?_⟩
    rw [heq]
    exact hyinv
  have hwin : win T.U a c ⊓ win T.U (c + 1) b = win T.U (c + 1) c := by
    rw [T.win_inf_win (a := a) (b := c) (c := c + 1) (d := b) (by omega)]
    rw [show max a (c + 1) = c + 1 by omega, show min c b = c by omega]
  have hbot : win T.U (c + 1) c = ⊥ := T.win_eq_bot (by omega)
  have hone : x'⁻¹ * x = 1 := by
    have hmem' : x'⁻¹ * x ∈ win T.U (c + 1) c := by
      rwa [hwin] at hmem
    rw [hbot] at hmem'
    simpa using hmem'
  have hyone : y' * y⁻¹ = 1 := by
    have hmem' : y' * y⁻¹ ∈ win T.U (c + 1) c := by
      rw [← heq]
      rwa [hwin] at hmem
    rw [hbot] at hmem'
    simpa using hmem'
  exact ⟨(inv_mul_eq_one.mp hone).symm, (mul_inv_eq_one.mp hyone).symm⟩

theorem mem_centralizer_win_iff {a b : ℤ} {x : G} :
    x ∈ Subgroup.centralizer (win T.U a b : Set G) ↔
      ∀ k, a ≤ k → k ≤ b → ∀ y ∈ T.U k, y * x = x * y := by
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro h k hk1 hk2 y hy
    exact h y (T.U_le_win hk1 hk2 hy)
  · intro h y hy
    have hle : win T.U a b ≤ Subgroup.centralizer ({x} : Set G) := by
      refine iSup₂_le fun k hk => ?_
      intro z hz
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact h k hk.1 hk.2 z hz
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hy)

end TitsSystem

@[expose] def TitsSystem.Uprime (T : TitsSystem G 8) (j : ℤ) : Subgroup G :=
  Subgroup.centralizer (win T.U (j - 4) (j + 4) : Set G) ⊓ T.U j

@[expose] def TitsSystem.Normalized (T : TitsSystem G 8) : Prop :=
  Subgroup.centralizer (win T.U 0 8 : Set G) ⊓ T.U 4 ≠ ⊥

@[expose] def TitsSystem.Usec (T : TitsSystem G 8) (j : ℤ) : Set G :=
  {x | x = 1 ∨ ∃ u ∈ T.Uprime (j - 8), u ≠ 1 ∧ x = T.nu' (j - 8) u}

namespace TitsSystem

variable (T : TitsSystem G 8)

theorem comm_add_one {j : ℤ} {x y : G} (hx : x ∈ T.U j) (hy : y ∈ T.U (j + 1)) :
    x * y = y * x := by
  have h := T.commutator_mem_win (j := j) (a := j + 1) (b := j + 1) (by omega) le_rfl
    (by omega) hx (T.U_le_win le_rfl le_rfl hy)
  rw [show j + 1 - 1 = j by ring] at h
  rw [T.win_eq_bot (by omega), Subgroup.mem_bot] at h
  exact commutatorElement_eq_one_iff_mul_comm.mp h

theorem normalized_iff : T.Normalized ↔ T.Uprime 4 ≠ ⊥ :=
  Iff.rfl

theorem Uprime_le (j : ℤ) : T.Uprime j ≤ T.U j :=
  inf_le_right

theorem mem_Uprime_iff {j : ℤ} {x : G} :
    x ∈ T.Uprime j ↔ x ∈ T.U j ∧
      ∀ k, j - 4 ≤ k → k ≤ j + 4 → ∀ y ∈ T.U k, y * x = x * y := by
  rw [Uprime, Subgroup.mem_inf, mem_centralizer_win_iff]
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

theorem Uprime_comm {j k : ℤ} (hk1 : j - 4 ≤ k) (hk2 : k ≤ j + 4) {x y : G}
    (hx : x ∈ T.Uprime j) (hy : y ∈ T.U k) : x * y = y * x :=
  ((T.mem_Uprime_iff (j := j) (x := x)).1 hx).2 k hk1 hk2 y hy |>.symm

theorem Uprime_comm_win {j a b : ℤ} (ha : j - 4 ≤ a) (hb : b ≤ j + 4) {x y : G}
    (hx : x ∈ T.Uprime j) (hy : y ∈ win T.U a b) : x * y = y * x := by
  have hle : win T.U a b ≤ win T.U (j - 4) (j + 4) := T.win_mono ha hb
  have hcent : x ∈ Subgroup.centralizer (win T.U (j - 4) (j + 4) : Set G) := hx.1
  have hxcent : x ∈ Subgroup.centralizer (win T.U a b : Set G) :=
    Subgroup.centralizer_le hle hcent
  exact (Subgroup.mem_centralizer_iff.mp hxcent y hy).symm

theorem Uprime_mul_comm {j : ℤ} {x y : G} (hx : x ∈ T.Uprime j)
    (hy : y ∈ T.Uprime j) : x * y = y * x :=
  T.Uprime_comm (j := j) (k := j) (by omega) (by omega) hx (T.Uprime_le j hy)

theorem Uprime_shift (s j : ℤ) : (T.shift s).Uprime j = T.Uprime (j + s) := by
  simp only [Uprime, win_shift, shift_U]
  rw [show j - 4 + s = j + s - 4 by ring, show j + 4 + s = j + s + 4 by ring]

theorem Uprime_refl (c j : ℤ) : (T.refl c).Uprime j = T.Uprime (c - j) := by
  simp only [Uprime, win_refl, refl_U]
  rw [show c - (j + 4) = c - j - 4 by ring,
    show c - (j - 4) = c - j + 4 by ring]

theorem Uprime_add_two_mul (j k : ℤ) : T.Uprime (j + 16 * k) = T.Uprime j := by
  have hwin : win T.U (j + 16 * k - 4) (j + 16 * k + 4) =
      win T.U (j - 4) (j + 4) := by
    convert T.win_add_two_mul (a := j - 4) (b := j + 4) (k := k) using 2 <;> ring_nf
  have hU : T.U (j + 16 * k) = T.U j := by
    convert U_add_two_mul T j k using 1 <;> ring_nf
  simp only [Uprime, hwin, hU]

theorem Moves.conj_mem_Uprime_shift {g : G} {c : ℤ} (hg : T.Moves g (· + c))
    {j : ℤ} {x : G} (hx : x ∈ T.Uprime j) :
    g * x * g⁻¹ ∈ T.Uprime (j + c) := by
  have hxU : x ∈ T.U j := T.Uprime_le j hx
  have hmem : g * x * g⁻¹ ∈ T.U (j + c) := Moves.conj_mem T hg hxU
  refine (T.mem_Uprime_iff (j := j + c) (x := g * x * g⁻¹)).2 ⟨hmem, ?_⟩
  intro k hk1 hk2 y hy
  have hg' : T.Moves g⁻¹ (· - c) := Moves.inv_shift T hg
  have hz : g⁻¹ * y * g ∈ T.U (k - c) := by
    simpa using Moves.conj_mem T hg' hy
  have hcomm : x * (g⁻¹ * y * g) = (g⁻¹ * y * g) * x :=
    T.Uprime_comm (j := j) (k := k - c) (by omega) (by omega) hx hz
  calc
    y * (g * x * g⁻¹) = g * (g⁻¹ * y * g * x) * g⁻¹ := by group
    _ = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by rw [← hcomm]
    _ = (g * x * g⁻¹) * y := by group

theorem Moves.conj_mem_Uprime_refl {g : G} {c : ℤ} (hg : T.Moves g (c - ·))
    {j : ℤ} {x : G} (hx : x ∈ T.Uprime j) :
    g * x * g⁻¹ ∈ T.Uprime (c - j) := by
  have hxU : x ∈ T.U j := T.Uprime_le j hx
  have hmem : g * x * g⁻¹ ∈ T.U (c - j) := Moves.conj_mem T hg hxU
  refine (T.mem_Uprime_iff (j := c - j) (x := g * x * g⁻¹)).2 ⟨hmem, ?_⟩
  intro k hk1 hk2 y hy
  have hg' : T.Moves g⁻¹ (c - ·) := Moves.inv_refl T hg
  have hz : g⁻¹ * y * g ∈ T.U (c - k) := by
    simpa using Moves.conj_mem T hg' hy
  have hcomm : x * (g⁻¹ * y * g) = (g⁻¹ * y * g) * x :=
    T.Uprime_comm (j := j) (k := c - k) (by omega) (by omega) hx hz
  calc
    y * (g * x * g⁻¹) = g * (g⁻¹ * y * g * x) * g⁻¹ := by group
    _ = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by rw [← hcomm]
    _ = (g * x * g⁻¹) * y := by group

theorem Moves.conj_mem_Uprime {g : G} {ε c : ℤ} (hε : ε = 1 ∨ ε = -1)
    (hg : T.Moves g (fun j => ε * j + c)) {j : ℤ} {x : G}
    (hx : x ∈ T.Uprime j) : g * x * g⁻¹ ∈ T.Uprime (ε * j + c) := by
  rcases hε with rfl | rfl
  · have hg' : T.Moves g (· + c) := by simpa [one_mul] using hg
    simpa [one_mul] using Moves.conj_mem_Uprime_shift T hg' hx
  · have hg' : T.Moves g (c - ·) := by
      simpa [sub_eq_add_neg, neg_one_mul, add_comm] using hg
    simpa [sub_eq_add_neg, neg_one_mul, add_comm] using
      Moves.conj_mem_Uprime_refl T hg' hx

theorem Moves.map_Uprime_shift {g : G} {c : ℤ} (hg : T.Moves g (· + c)) (j : ℤ) :
    (T.Uprime j).map (MulAut.conj g).toMonoidHom = T.Uprime (j + c) := by
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    exact Moves.conj_mem_Uprime_shift T hg hy
  · intro x hx
    have hg' : T.Moves g⁻¹ (· + (-c)) := Moves.inv_shift T hg
    have hy : g⁻¹ * x * g ∈ T.Uprime j := by
      have h := Moves.conj_mem_Uprime_shift T hg' hx
      rw [inv_inv, show (j + c) + -c = j by ring] at h
      exact h
    refine ⟨g⁻¹ * x * g, hy, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem Moves.map_Uprime_refl {g : G} {c : ℤ} (hg : T.Moves g (c - ·)) (j : ℤ) :
    (T.Uprime j).map (MulAut.conj g).toMonoidHom = T.Uprime (c - j) := by
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    exact Moves.conj_mem_Uprime_refl T hg hy
  · intro x hx
    have hg' : T.Moves g⁻¹ (c - ·) := Moves.inv_refl T hg
    have hy : g⁻¹ * x * g ∈ T.Uprime j := by
      have h := Moves.conj_mem_Uprime_refl T hg' hx
      rw [inv_inv, show c - (c - j) = j by ring] at h
      exact h
    refine ⟨g⁻¹ * x * g, hy, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem Usec_shift (s j : ℤ) : (T.shift s).Usec j = T.Usec (j + s) := by
  ext x
  constructor
  · rintro (rfl | ⟨u, hu, hu1, rfl⟩)
    · exact Or.inl rfl
    · right
      have hu' : u ∈ T.Uprime ((j - 8) + s) := by
        rwa [Uprime_shift] at hu
      have hindex : (j - 8) + s = (j + s) - 8 := by ring
      refine ⟨u, ?_, hu1, ?_⟩
      · rwa [hindex] at hu'
      · rw [T.nu'_shift (by norm_num) s (j - 8) u, hindex]
  · rintro (rfl | ⟨u, hu, hu1, rfl⟩)
    · exact Or.inl rfl
    · right
      have hindex : (j + s) - 8 = (j - 8) + s := by ring
      have hu' : u ∈ T.Uprime ((j - 8) + s) := by
        rwa [hindex] at hu
      refine ⟨u, ?_, hu1, ?_⟩
      · rw [Uprime_shift]; exact hu'
      · rw [T.nu'_shift (by norm_num) s (j - 8) u, hindex]

theorem Normalized.shift {T : TitsSystem G 8} (hT : T.Normalized) {s : ℤ} (hs : Even s) :
    (T.shift s).Normalized := by
  have h4 : T.Uprime 4 ≠ ⊥ := T.normalized_iff.mp hT
  rcases hs with ⟨t, rfl⟩
  obtain ⟨g, hg⟩ := T.exists_moves_shift t
  have hmap : (T.Uprime 4).map (MulAut.conj g).toMonoidHom =
      (T.shift (t + t)).Uprime 4 := by
    rw [Moves.map_Uprime_shift T hg, Uprime_shift]
    rw [show 4 + 2 * t = 4 + (t + t) by ring]
  rw [Normalized]
  change (T.shift (t + t)).Uprime 4 ≠ ⊥
  rw [← hmap]
  intro hbot
  exact h4 ((Subgroup.map_eq_bot_iff_of_injective (T.Uprime 4)
    (MulAut.conj g).injective).mp hbot)

theorem Normalized.refl {T : TitsSystem G 8} (hT : T.Normalized) {c : ℤ} (hc : Even c) :
    (T.refl c).Normalized := by
  have h4 : T.Uprime 4 ≠ ⊥ := T.normalized_iff.mp hT
  obtain ⟨g, hg⟩ := T.exists_moves_refl_of_even c hc (⟨4, by norm_num⟩ : Even (8 : ℤ))
  have hmap : (T.Uprime 4).map (MulAut.conj g).toMonoidHom =
      (T.refl c).Uprime 4 := by
    rw [Moves.map_Uprime_refl T hg, Uprime_refl]
  rw [Normalized]
  change (T.refl c).Uprime 4 ≠ ⊥
  rw [← hmap]
  intro hbot
  exact h4 ((Subgroup.map_eq_bot_iff_of_injective (T.Uprime 4)
    (MulAut.conj g).injective).mp hbot)

theorem Uprime_ne_bot (hT : T.Normalized) {j : ℤ} (hj : Even j) : T.Uprime j ≠ ⊥ := by
  have h4 : T.Uprime 4 ≠ ⊥ := T.normalized_iff.mp hT
  rcases hj with ⟨k, hk⟩
  have hc : Even (j + 4) := ⟨k + 2, by rw [hk]; ring⟩
  obtain ⟨g, hg⟩ := T.exists_moves_refl_of_even (j + 4) hc (⟨4, by norm_num⟩ : Even (8 : ℤ))
  have hmap : (T.Uprime 4).map (MulAut.conj g).toMonoidHom = T.Uprime j := by
    rw [Moves.map_Uprime_refl T hg]
    rw [show (j + 4) - 4 = j by ring]
  rw [← hmap]
  intro hbot
  exact h4 ((Subgroup.map_eq_bot_iff_of_injective (T.Uprime 4)
    (MulAut.conj g).injective).mp hbot)

theorem exists_Uprime (hT : T.Normalized) {j : ℤ} (hj : Even j) :
    ∃ x ∈ T.Uprime j, x ≠ 1 :=
  Subgroup.exists_mem_ne_one_of_ne_bot (T.Uprime_ne_bot hT hj)

theorem mu_conj_mem_Uprime {i j : ℤ} {u x : G} (hu : u ∈ T.U i) (hu1 : u ≠ 1)
    (hx : x ∈ T.Uprime j) :
    T.mu i u * x * (T.mu i u)⁻¹ ∈ T.Uprime (2 * i + 8 - j) := by
  exact Moves.conj_mem_Uprime_refl T (T.moves_mu hu hu1) hx

end TitsSystem

end CFSG.GH74.Tits83
