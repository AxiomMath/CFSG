module

public import CFSG.ClassicalInvolution.WeakCT.B2Intrinsic

public section

namespace CFSG.ClassicalInvolution.WeakCT

structure B2Sys (F : Type) [Field F] where
  eS : ℤ × ℤ → F
  eL : ℤ × ℤ → F
  Cc : ℤ × ℤ → ℤ × ℤ → ℕ × ℕ → F
  sq_S : ∀ z ∈ zB2, eS z * eS z = 1
  sq_L : ∀ z ∈ zB2, eL z * eL z = 1
  trans_S : ∀ z ∈ zB2, ∀ w ∈ zB2, z + w ≠ 0 → ∀ p ∈ eList z w,
    Cc (bS z) (bS w) p * eS z ^ p.1 * eS w ^ p.2 = eS (p.1 • z + p.2 • w) * Cc z w p
  trans_L : ∀ z ∈ zB2, ∀ w ∈ zB2, z + w ≠ 0 → ∀ p ∈ eList z w,
    Cc (bL z) (bL w) p * eL z ^ p.1 * eL w ^ p.2 = eL (p.1 • z + p.2 • w) * Cc z w p
  swap : ∀ z ∈ zB2, ∀ w ∈ zB2, z + w ≠ 0 → ∀ p ∈ eList z w, Cc w z p.swap = -Cc z w p
  s_a : eS (1, 0) = -1
  s_na : eS (-1, 0) = -1
  l_b : eL (0, 1) = -1
  l_nb : eL (0, -1) = -1
  l_d : eL (2, 1) = 1
  l_nd : eL (-2, -1) = 1
  s_c : eS (1, 1) = -1
  s_nc : eS (-1, -1) = -1
  s_par : eS (2, 1) = eS (0, 1)
  s_npar : eS (-2, -1) = eS (0, -1)
  l_par : eL (1, 1) = -eL (1, 0)
  l_npar : eL (-1, -1) = -eL (-1, 0)
  base3 : Cc (1, 0) (0, 1) (2, 1) = eS (2, 1)
  base1 : Cc (1, 0) (0, 1) (1, 1) = -eL (1, 0)
  base2 : Cc (1, 0) (0, 1) (1, 1) * Cc (1, 0) (1, 1) (1, 1) = 2 * eS (2, 1)

abbrev Tr : Type := (ℤ × ℤ) × (ℤ × ℤ) × (ℕ × ℕ)

def nbrs (t : Tr) : List Tr :=
  [(bS t.1, bS t.2.1, t.2.2), (bL t.1, bL t.2.1, t.2.2), (t.2.1, t.1, t.2.2.swap)]

def stepL (L : List Tr) : List Tr := (L ++ L.flatMap nbrs).dedup

def reachL : ℕ → List Tr → List Tr
  | 0, L => L
  | n + 1, L => reachL n (stepL L)

def baseL : List Tr :=
  [((1, 0), (0, 1), (1, 1)), ((1, 0), (0, 1), (2, 1)), ((1, 0), (1, 1), (1, 1))]

set_option maxRecDepth 100000 in
theorem reach_all : ∀ z ∈ zB2, ∀ w ∈ zB2, z + w ≠ 0 → ∀ p ∈ eList z w,
    (z, w, p) ∈ reachL 6 baseL := by decide

theorem mem_stepL {L : List Tr} {t : Tr} (h : t ∈ L) : t ∈ stepL L := by
  unfold stepL
  rw [List.mem_dedup]
  exact List.mem_append_left _ h

theorem mem_stepL_nbrs {L : List Tr} {t t' : Tr} (h : t ∈ L) (h' : t' ∈ nbrs t) :
    t' ∈ stepL L := by
  unfold stepL
  rw [List.mem_dedup]
  exact List.mem_append_right _ (List.mem_flatMap.2 ⟨t, h, h'⟩)

theorem mem_reachL_induction {Q : Tr → Prop} (hnbr : ∀ t, Q t → ∀ t' ∈ nbrs t, Q t') :
    ∀ n (L : List Tr), (∀ t ∈ L, Q t) → ∀ t ∈ reachL n L, Q t := by
  intro n
  induction n with
  | zero => intro L hL t ht; exact hL t ht
  | succ n ih =>
    intro L hL t ht
    refine ih (stepL L) (fun t' ht' => ?_) t ht
    unfold stepL at ht'
    rw [List.mem_dedup, List.mem_append] at ht'
    rcases ht' with ht' | ht'
    · exact hL t' ht'
    · obtain ⟨t₀, ht₀, ht'⟩ := List.mem_flatMap.1 ht'
      exact hnbr t₀ (hL t₀ ht₀) t' ht'

theorem alg_step {R : Type*} [CommRing R] {Cs Cs' Ct Ct' u v y a a' b b' c c' : R} {i j : ℕ}
    (ha' : a' * a' = 1) (hb' : b' * b' = 1) (hc' : c' * c' = 1)
    (h1 : Cs' * a ^ i * b ^ j = c * Cs) (h2 : Ct' * a' ^ i * b' ^ j = c' * Ct)
    (h3 : Cs * u ^ i * v ^ j = y * Ct) :
    Cs' * (u * (a * a')) ^ i * (v * (b * b')) ^ j = (y * (c * c')) * Ct' := by
  have hQ : (a' ^ i * b' ^ j) * (a' ^ i * b' ^ j) = 1 := by
    rw [mul_mul_mul_comm, ← mul_pow, ← mul_pow, ha', hb', one_pow, one_pow, mul_one]
  rw [mul_pow, mul_pow, mul_pow, mul_pow]
  linear_combination (u ^ i * v ^ j * (a' ^ i * b' ^ j)) * h1 + (c * (a' ^ i * b' ^ j)) * h3 +
    (-(y * c * c' * (a' ^ i * b' ^ j))) * h2 + (-(y * c * (a' ^ i * b' ^ j) * Ct)) * hc' +
    (y * c * c' * Ct') * hQ

section Match

variable {F : Type} [Field F] (S T : B2Sys F)

def B2Sys.gS (z : ℤ × ℤ) : F := S.eS z * T.eS z

def B2Sys.gL (z : ℤ × ℤ) : F := S.eL z * T.eL z

def B2Sys.twist (z : ℤ × ℤ) : F :=
  if z = (0, 1) then 1
  else if z = (2, 1) then S.gS T (0, 1)
  else if z = (0, -1) then S.gL T (0, 1)
  else if z = (-2, -1) then S.gL T (0, 1) * S.gS T (0, -1)
  else if z = (1, 0) then 1
  else if z = (1, 1) then S.gL T (1, 0)
  else if z = (-1, 0) then S.gS T (1, 0)
  else if z = (-1, -1) then S.gS T (1, 0) * S.gL T (-1, 0)
  else 1

theorem B2Sys.gS_sq (z : ℤ × ℤ) (hz : z ∈ zB2) : S.gS T z * S.gS T z = 1 := by
  unfold B2Sys.gS
  calc S.eS z * T.eS z * (S.eS z * T.eS z) = (S.eS z * S.eS z) * (T.eS z * T.eS z) := by ring
    _ = 1 := by rw [S.sq_S z hz, T.sq_S z hz, one_mul]

theorem B2Sys.gL_sq (z : ℤ × ℤ) (hz : z ∈ zB2) : S.gL T z * S.gL T z = 1 := by
  unfold B2Sys.gL
  calc S.eL z * T.eL z * (S.eL z * T.eL z) = (S.eL z * S.eL z) * (T.eL z * T.eL z) := by ring
    _ = 1 := by rw [S.sq_L z hz, T.sq_L z hz, one_mul]

theorem B2Sys.gS_a : S.gS T (1, 0) = 1 := by
  simp [B2Sys.gS, S.s_a, T.s_a]

theorem B2Sys.gS_na : S.gS T (-1, 0) = 1 := by
  simp [B2Sys.gS, S.s_na, T.s_na]

theorem B2Sys.gS_c : S.gS T (1, 1) = 1 := by
  simp [B2Sys.gS, S.s_c, T.s_c]

theorem B2Sys.gS_nc : S.gS T (-1, -1) = 1 := by
  simp [B2Sys.gS, S.s_nc, T.s_nc]

theorem B2Sys.gS_par : S.gS T (2, 1) = S.gS T (0, 1) := by
  simp only [B2Sys.gS, S.s_par, T.s_par]

theorem B2Sys.gS_npar : S.gS T (-2, -1) = S.gS T (0, -1) := by
  simp only [B2Sys.gS, S.s_npar, T.s_npar]

theorem B2Sys.gL_b : S.gL T (0, 1) = 1 := by
  simp [B2Sys.gL, S.l_b, T.l_b]

theorem B2Sys.gL_nb : S.gL T (0, -1) = 1 := by
  simp [B2Sys.gL, S.l_nb, T.l_nb]

theorem B2Sys.gL_d : S.gL T (2, 1) = 1 := by
  simp [B2Sys.gL, S.l_d, T.l_d]

theorem B2Sys.gL_nd : S.gL T (-2, -1) = 1 := by
  simp [B2Sys.gL, S.l_nd, T.l_nd]

theorem B2Sys.gL_par : S.gL T (1, 1) = S.gL T (1, 0) := by
  simp only [B2Sys.gL, S.l_par, T.l_par]
  ring

theorem B2Sys.gL_npar : S.gL T (-1, -1) = S.gL T (-1, 0) := by
  simp only [B2Sys.gL, S.l_npar, T.l_npar]
  ring

theorem B2Sys.twist_edge_S (ζ : ℤ × ℤ) (hζ : ζ ∈ zB2) :
    S.twist T (bS ζ) = S.twist T ζ * S.gS T ζ := by
  have h1 := S.gS_sq T (0, 1) (by decide)
  have h2 := S.gS_sq T (0, -1) (by decide)
  simp only [zB2, Finset.mem_insert, Finset.mem_singleton] at hζ
  rcases hζ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp [B2Sys.twist, bS, S.gS_a T]
  · simp [B2Sys.twist, bS, S.gS_na T, S.gS_a T]
  · simp [B2Sys.twist, bS]
  · simp [B2Sys.twist, bS]
  · simp [B2Sys.twist, bS, S.gS_c T]
  · simp [B2Sys.twist, bS, S.gS_nc T]
  · simp [B2Sys.twist, bS, S.gS_par T, h1]
  · simp [B2Sys.twist, bS, S.gS_npar T, h2, mul_assoc]

theorem B2Sys.twist_edge_L (ζ : ℤ × ℤ) (hζ : ζ ∈ zB2) :
    S.twist T (bL ζ) = S.twist T ζ * S.gL T ζ := by
  have h1 := S.gL_sq T (1, 0) (by decide)
  have h2 := S.gL_sq T (-1, 0) (by decide)
  simp only [zB2, Finset.mem_insert, Finset.mem_singleton] at hζ
  rcases hζ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp [B2Sys.twist, bL]
  · simp [B2Sys.twist, bL, S.gS_a T]
  · simp [B2Sys.twist, bL, S.gL_b T]
  · simp [B2Sys.twist, bL, S.gL_nb T, S.gL_b T]
  · simp [B2Sys.twist, bL, S.gL_par T, h1]
  · simp [B2Sys.twist, bL, S.gL_npar T, S.gS_a T, h2]
  · simp [B2Sys.twist, bL, S.gL_d T]
  · simp [B2Sys.twist, bL, S.gL_nd T]

def trip (t : Tr) : Prop :=
  t.1 ∈ zB2 ∧ t.2.1 ∈ zB2 ∧ t.1 + t.2.1 ≠ 0 ∧ t.2.2 ∈ eList t.1 t.2.1

def PQ (e : ℤ × ℤ → F) (t : Tr) : Prop :=
  S.Cc t.1 t.2.1 t.2.2 * e t.1 ^ t.2.2.1 * e t.2.1 ^ t.2.2.2 =
    e (t.2.2.1 • t.1 + t.2.2.2 • t.2.1) * T.Cc t.1 t.2.1 t.2.2

theorem step_gen (e : ℤ × ℤ → F) (r : ℤ × ℤ →+ ℤ × ℤ) (hrmem : ∀ z ∈ zB2, r z ∈ zB2)
    (hrinv : ∀ z, r (r z) = z) (εS εT : ℤ × ℤ → F) (hεT : ∀ z ∈ zB2, εT z * εT z = 1)
    (hS : ∀ z ∈ zB2, ∀ w ∈ zB2, z + w ≠ 0 → ∀ p ∈ eList z w,
      S.Cc (r z) (r w) p * εS z ^ p.1 * εS w ^ p.2 = εS (p.1 • z + p.2 • w) * S.Cc z w p)
    (hT : ∀ z ∈ zB2, ∀ w ∈ zB2, z + w ≠ 0 → ∀ p ∈ eList z w,
      T.Cc (r z) (r w) p * εT z ^ p.1 * εT w ^ p.2 = εT (p.1 • z + p.2 • w) * T.Cc z w p)
    (hedge : ∀ ζ ∈ zB2, e (r ζ) = e ζ * (εS ζ * εT ζ)) {t : Tr} (ht : trip t)
    (hP : PQ S T e t) : trip (r t.1, r t.2.1, t.2.2) ∧ PQ S T e (r t.1, r t.2.1, t.2.2) := by
  obtain ⟨z, w, p⟩ := t
  obtain ⟨hz, hw, hzw, hp⟩ := ht
  simp only at hz hw hzw hp
  have hrzw : r z + r w ≠ 0 := by
    rw [← map_add]
    intro h
    apply hzw
    have := congrArg r h
    rwa [hrinv, map_zero] at this
  have hγm : p.1 • z + p.2 • w ∈ zB2 := ((mem_eList hz hw hzw p).1 hp).2.2
  have hγ : p.1 • r z + p.2 • r w = r (p.1 • z + p.2 • w) := by
    rw [map_add, map_nsmul, map_nsmul]
  refine ⟨⟨hrmem z hz, hrmem w hw, hrzw, ?_⟩, ?_⟩
  · simp only
    rw [eList_map hrmem hrinv]
    exact hp
  · unfold PQ at hP ⊢
    simp only at hP ⊢
    rw [hγ, hedge z hz, hedge w hw, hedge _ hγm]
    exact alg_step (hεT z hz) (hεT w hw) (hεT _ hγm) (hS z hz w hw hzw p hp)
      (hT z hz w hw hzw p hp) hP

theorem step_swap (e : ℤ × ℤ → F) {t : Tr} (ht : trip t) (hP : PQ S T e t) :
    trip (t.2.1, t.1, t.2.2.swap) ∧ PQ S T e (t.2.1, t.1, t.2.2.swap) := by
  obtain ⟨z, w, p⟩ := t
  obtain ⟨hz, hw, hzw, hp⟩ := ht
  simp only at hz hw hzw hp
  have hwz : w + z ≠ 0 := by rwa [add_comm]
  refine ⟨⟨hw, hz, hwz, ?_⟩, ?_⟩
  · simp only
    exact (eList_swap_perm hz hw hzw).mem_iff.2 (List.mem_map.2 ⟨p, hp, rfl⟩)
  · unfold PQ at hP ⊢
    simp only at hP ⊢
    rw [S.swap z hz w hw hzw p hp, T.swap z hz w hw hzw p hp]
    simp only [Prod.fst_swap, Prod.snd_swap]
    rw [add_comm (p.2 • w) (p.1 • z)]
    linear_combination (-1 : F) * hP

theorem B2Sys.twist_sq (ζ : ℤ × ℤ) (hζ : ζ ∈ zB2) : S.twist T ζ * S.twist T ζ = 1 := by
  have h1 := S.gS_sq T (0, 1) (by decide)
  have h2 := S.gS_sq T (0, -1) (by decide)
  have h3 := S.gL_sq T (1, 0) (by decide)
  have h4 := S.gL_sq T (-1, 0) (by decide)
  simp only [zB2, Finset.mem_insert, Finset.mem_singleton] at hζ
  rcases hζ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp [B2Sys.twist]
  · simp [B2Sys.twist, S.gS_a T]
  · simp [B2Sys.twist]
  · simp [B2Sys.twist, S.gL_b T]
  · simp [B2Sys.twist, h3]
  · simp [B2Sys.twist, S.gS_a T, h4]
  · simp [B2Sys.twist, h1]
  · simp [B2Sys.twist, S.gL_b T, h2]

theorem B2Sys.exists_match : ∃ e : ℤ × ℤ → F, e (1, 0) = 1 ∧ e (-1, 0) = 1 ∧ e (0, 1) = 1 ∧
    e (0, -1) = 1 ∧ (∀ z ∈ zB2, e z * e z = 1) ∧
    ∀ z ∈ zB2, ∀ w ∈ zB2, z + w ≠ 0 → ∀ p ∈ eList z w,
      S.Cc z w p * e z ^ p.1 * e w ^ p.2 = e (p.1 • z + p.2 • w) * T.Cc z w p := by
  have h1a : S.twist T (1, 0) = 1 := by simp [B2Sys.twist]
  have h1b : S.twist T (-1, 0) = 1 := by simp [B2Sys.twist, S.gS_a T]
  have h1c : S.twist T (0, 1) = 1 := by simp [B2Sys.twist]
  have h1d : S.twist T (0, -1) = 1 := by simp [B2Sys.twist, S.gL_b T]
  refine ⟨S.twist T, h1a, h1b, h1c, h1d, S.twist_sq T, ?_⟩
  have hκ₂S : S.Cc (1, 0) (1, 1) (1, 1) = -2 * S.eL (1, 0) * S.eS (2, 1) := by
    have h := S.base2
    rw [S.base1] at h
    linear_combination (-(S.eL (1, 0))) * h + (-(S.Cc (1, 0) (1, 1) (1, 1))) *
      S.sq_L (1, 0) (by decide)
  have hκ₂T : T.Cc (1, 0) (1, 1) (1, 1) = -2 * T.eL (1, 0) * T.eS (2, 1) := by
    have h := T.base2
    rw [T.base1] at h
    linear_combination (-(T.eL (1, 0))) * h + (-(T.Cc (1, 0) (1, 1) (1, 1))) *
      T.sq_L (1, 0) (by decide)
  have tw11 : S.twist T (1, 1) = S.gL T (1, 0) := by simp [B2Sys.twist]
  have tw21 : S.twist T (2, 1) = S.gS T (0, 1) := by simp [B2Sys.twist]
  have e1 : (1 : ℕ) • ((1 : ℤ), (0 : ℤ)) + (1 : ℕ) • ((0 : ℤ), (1 : ℤ)) = (1, 1) := by decide
  have e2 : (2 : ℕ) • ((1 : ℤ), (0 : ℤ)) + (1 : ℕ) • ((0 : ℤ), (1 : ℤ)) = (2, 1) := by decide
  have e3 : (1 : ℕ) • ((1 : ℤ), (0 : ℤ)) + (1 : ℕ) • ((1 : ℤ), (1 : ℤ)) = (2, 1) := by decide
  have hbase : ∀ t ∈ baseL, trip t ∧ PQ S T (S.twist T) t := by
    intro t ht
    simp only [baseL, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · refine ⟨by unfold trip; decide, ?_⟩
      unfold PQ
      show S.Cc (1, 0) (0, 1) (1, 1) * S.twist T (1, 0) ^ 1 * S.twist T (0, 1) ^ 1 =
        S.twist T ((1 : ℕ) • (1, 0) + (1 : ℕ) • (0, 1)) * T.Cc (1, 0) (0, 1) (1, 1)
      rw [e1, tw11, h1a, h1c, S.base1, T.base1]
      unfold B2Sys.gL
      linear_combination (S.eL (1, 0)) * T.sq_L (1, 0) (by decide)
    · refine ⟨by unfold trip; decide, ?_⟩
      unfold PQ
      show S.Cc (1, 0) (0, 1) (2, 1) * S.twist T (1, 0) ^ 2 * S.twist T (0, 1) ^ 1 =
        S.twist T ((2 : ℕ) • (1, 0) + (1 : ℕ) • (0, 1)) * T.Cc (1, 0) (0, 1) (2, 1)
      rw [e2, tw21, h1a, h1c, S.base3, T.base3, T.s_par, S.s_par]
      unfold B2Sys.gS
      linear_combination (-(S.eS (0, 1))) * T.sq_S (0, 1) (by decide)
    · refine ⟨by unfold trip; decide, ?_⟩
      unfold PQ
      show S.Cc (1, 0) (1, 1) (1, 1) * S.twist T (1, 0) ^ 1 * S.twist T (1, 1) ^ 1 =
        S.twist T ((1 : ℕ) • (1, 0) + (1 : ℕ) • (1, 1)) * T.Cc (1, 0) (1, 1) (1, 1)
      rw [e3, tw21, tw11, h1a, hκ₂S, hκ₂T, S.s_par, T.s_par]
      unfold B2Sys.gS B2Sys.gL
      linear_combination (2 * T.eL (1, 0) * S.eS (0, 1)) * T.sq_S (0, 1) (by decide) +
        (-2 * S.eS (0, 1) * T.eL (1, 0)) * S.sq_L (1, 0) (by decide)
  have hnbr : ∀ t, (trip t ∧ PQ S T (S.twist T) t) → ∀ t' ∈ nbrs t,
      (trip t' ∧ PQ S T (S.twist T) t') := by
    intro t ht t' ht'
    simp only [nbrs, List.mem_cons, List.not_mem_nil, or_false] at ht'
    rcases ht' with rfl | rfl | rfl
    · exact step_gen S T (S.twist T) bSh (fun z hz => bS_mem z hz) bS_bS S.eS T.eS T.sq_S
        (fun z hz w hw hzw p hp => S.trans_S z hz w hw hzw p hp)
        (fun z hz w hw hzw p hp => T.trans_S z hz w hw hzw p hp)
        (fun ζ hζ => S.twist_edge_S T ζ hζ) ht.1 ht.2
    · exact step_gen S T (S.twist T) bLh (fun z hz => bL_mem z hz) bL_bL S.eL T.eL T.sq_L
        (fun z hz w hw hzw p hp => S.trans_L z hz w hw hzw p hp)
        (fun z hz w hw hzw p hp => T.trans_L z hz w hw hzw p hp)
        (fun ζ hζ => S.twist_edge_L T ζ hζ) ht.1 ht.2
    · exact step_swap S T (S.twist T) ht.1 ht.2
  intro z hz w hw hzw p hp
  exact (mem_reachL_induction hnbr 6 baseL hbase _ (reach_all z hz w hw hzw p hp)).2

end Match

section OfHE

open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.Timmesfeld
  CFSG.Timmesfeld.LevisExtras

variable {K : Type} [Group K] {D : UniversalRootDatum K} {F : Type} [Field F]
  {x : (Fin D.rank → ℤ) → F → K}
  {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
  {O : Steinberg.CommOrder (Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible)}

theorem b2_V_pos (hE : Steinberg.ChevalleyExtras D F x C O) {s l : Fin D.rank}
    (hdiv : D.divisible = ∅) (hcsl : D.cartan s l = -2) (hcls : D.cartan l s = -1) :
    Cz F C s l (1, 0) (0, 1) (2, 1) = wsign hE s (pair s l (2, 1)) ∧
      Cz F C s l (1, 0) (0, 1) (1, 1) * Cz F C s l (1, 0) (1, 1) (1, 1) =
        2 * wsign hE s (pair s l (2, 1)) ∧ wsign hE s (pair s l (1, 1)) = -1 := by
  obtain ⟨h1, h2, h3, -⟩ := b2_V hE hdiv hcsl hcls (σ := 1) (Or.inl rfl) 1 (Or.inl rfl)
    (by simp [Steinberg.weylElement, pair_one_zero, pair_neg_one_zero])
  rw [show ((2 * 1 : ℤ), (1 : ℤ)) = (2, 1) by norm_num] at h1 h2
  exact ⟨h1, h2, h3⟩

@[expose] noncomputable def B2Sys.ofHE (hE : Steinberg.ChevalleyExtras D F x C O) (s l : Fin D.rank)
    (hdiv : D.divisible = ∅) (hcsl : D.cartan s l = -2) (hcls : D.cartan l s = -1) :
    B2Sys F where
  eS z := wsign hE s (pair s l z)
  eL z := wsign hE l (pair s l z)
  Cc z w p := Cz F C s l z w p
  sq_S := fun z hz => wsign_mul_self hE (pair_mem_roots_zB2 hcsl hcls z hz)
  sq_L := fun z hz => wsign_mul_self hE (pair_mem_roots_zB2 hcsl hcls z hz)
  trans_S := fun z hz w hw hzw p hp => const_transfer_s hE hdiv hcsl hcls hz hw hzw hp
  trans_L := fun z hz w hw hzw p hp => const_transfer_l hE hdiv hcsl hcls hz hw hzw hp
  swap := fun z hz w hw hzw p hp => const_swap hE hdiv hcsl hcls hz hw hzw hp
  s_a := b2_wsign_s_one_zero hE
  s_na := b2_wsign_s_neg_one_zero hE
  l_b := b2_wsign_l_zero_one hE
  l_nb := b2_wsign_l_zero_neg_one hE
  l_d := b2_wsign_l_two_one hE hdiv hcsl hcls
  l_nd := b2_wsign_l_neg_two_neg_one hE hdiv hcsl hcls
  s_c := (b2_V_pos hE hdiv hcsl hcls).2.2
  s_nc := (b2_V hE hdiv hcsl hcls (σ := -1) (Or.inr rfl) (-1) (Or.inr rfl)
    (by simpa [pair_one_zero, pair_neg_one_zero] using weylElement_neg_one_eq hE s)).2.2.1
  s_par := b2_wsign_s_two_one hE hcsl hcls
  s_npar := b2_wsign_s_neg_two_neg_one hE hcsl hcls
  l_par := b2_wsign_l_one_one hE hcsl hcls
  l_npar := b2_wsign_l_neg_one_neg_one hE hcsl hcls
  base3 := (b2_V_pos hE hdiv hcsl hcls).1
  base1 := by
    have h := (b2_H hE hdiv hcsl hcls).1
    have h' := const_swap hE hdiv hcsl hcls (z := (1, 0)) (w := (0, 1)) (p := (1, 1))
      (by decide) (by decide) (by decide) (by decide)
    simp only [Prod.swap_prod_mk] at h'
    linear_combination h' - h
  base2 := (b2_V_pos hE hdiv hcsl hcls).2.1

section W0

variable (hE : Steinberg.ChevalleyExtras D F x C O) {s l : Fin D.rank}
  (hdiv : D.divisible = ∅) (hcsl : D.cartan s l = -2) (hcls : D.cartan l s = -1)
include hE hdiv hcsl hcls

theorem weylS_conj {z : ℤ × ℤ} (hz : z ∈ zB2) (u : F) :
    Steinberg.weylElement x s 1 * x (pair s l z) u * (Steinberg.weylElement x s 1)⁻¹ =
      x (pair s l (bS z)) ((B2Sys.ofHE hE s l hdiv hcsl hcls).eS z * u) := by
  rw [weyl_conj_one hE (pair_mem_roots_zB2 hcsl hcls z hz), reflection_pair_bS hcsl]
  rfl

theorem weylL_conj {z : ℤ × ℤ} (hz : z ∈ zB2) (u : F) :
    Steinberg.weylElement x l 1 * x (pair s l z) u * (Steinberg.weylElement x l 1)⁻¹ =
      x (pair s l (bL z)) ((B2Sys.ofHE hE s l hdiv hcsl hcls).eL z * u) := by
  rw [weyl_conj_one hE (pair_mem_roots_zB2 hcsl hcls z hz), reflection_pair_bL hcls]
  rfl

theorem w0_chain {z₀ z₁ z₂ z₃ z₄ : ℤ × ℤ} (h0 : z₀ ∈ zB2) (h1 : bL z₀ = z₁) (h2 : bS z₁ = z₂)
    (h3 : bL z₂ = z₃) (h4 : bS z₃ = z₄) (c : F) :
    (Steinberg.weylElement x s 1 * Steinberg.weylElement x l 1 * Steinberg.weylElement x s 1 *
      Steinberg.weylElement x l 1) * x (pair s l z₀) c * (Steinberg.weylElement x s 1 *
        Steinberg.weylElement x l 1 * Steinberg.weylElement x s 1 *
          Steinberg.weylElement x l 1)⁻¹ =
      x (pair s l z₄) ((B2Sys.ofHE hE s l hdiv hcsl hcls).eS z₃ *
        ((B2Sys.ofHE hE s l hdiv hcsl hcls).eL z₂ * ((B2Sys.ofHE hE s l hdiv hcsl hcls).eS z₁ *
          ((B2Sys.ofHE hE s l hdiv hcsl hcls).eL z₀ * c)))) := by
  have e : ∀ (W V y : K), (W * V * W * V) * y * (W * V * W * V)⁻¹ =
      W * (V * (W * (V * y * V⁻¹) * W⁻¹) * V⁻¹) * W⁻¹ := fun W V y => by group
  have m1 : z₁ ∈ zB2 := h1 ▸ bL_mem z₀ h0
  have m2 : z₂ ∈ zB2 := h2 ▸ bS_mem z₁ m1
  have m3 : z₃ ∈ zB2 := h3 ▸ bL_mem z₂ m2
  rw [e, weylL_conj hE hdiv hcsl hcls h0, h1, weylS_conj hE hdiv hcsl hcls m1, h2,
    weylL_conj hE hdiv hcsl hcls m2, h3, weylS_conj hE hdiv hcsl hcls m3, h4]

theorem w0_conj_simple (c : F) :
    (Steinberg.weylElement x s 1 * Steinberg.weylElement x l 1 * Steinberg.weylElement x s 1 *
      Steinberg.weylElement x l 1) * x (pair s l (1, 0)) c * (Steinberg.weylElement x s 1 *
        Steinberg.weylElement x l 1 * Steinberg.weylElement x s 1 *
          Steinberg.weylElement x l 1)⁻¹ = x (pair s l (-1, 0)) (-c) ∧
    (Steinberg.weylElement x s 1 * Steinberg.weylElement x l 1 * Steinberg.weylElement x s 1 *
      Steinberg.weylElement x l 1) * x (pair s l (-1, 0)) c * (Steinberg.weylElement x s 1 *
        Steinberg.weylElement x l 1 * Steinberg.weylElement x s 1 *
          Steinberg.weylElement x l 1)⁻¹ = x (pair s l (1, 0)) (-c) ∧
    (Steinberg.weylElement x s 1 * Steinberg.weylElement x l 1 * Steinberg.weylElement x s 1 *
      Steinberg.weylElement x l 1) * x (pair s l (0, 1)) c * (Steinberg.weylElement x s 1 *
        Steinberg.weylElement x l 1 * Steinberg.weylElement x s 1 *
          Steinberg.weylElement x l 1)⁻¹ = x (pair s l (0, -1)) (-c) ∧
    (Steinberg.weylElement x s 1 * Steinberg.weylElement x l 1 * Steinberg.weylElement x s 1 *
      Steinberg.weylElement x l 1) * x (pair s l (0, -1)) c * (Steinberg.weylElement x s 1 *
        Steinberg.weylElement x l 1 * Steinberg.weylElement x s 1 *
          Steinberg.weylElement x l 1)⁻¹ = x (pair s l (0, 1)) (-c) := by
  set S := B2Sys.ofHE hE s l hdiv hcsl hcls with hS
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [w0_chain hE hdiv hcsl hcls (z₁ := (1, 1)) (z₂ := (1, 1)) (z₃ := (1, 0)) (z₄ := (-1, 0))
      (by decide) (by decide) (by decide) (by decide) (by decide) c]
    congr 1
    have h1 := S.l_par
    have h2 := S.sq_L (1, 0) (by decide)
    rw [S.s_a, h1, S.s_c]
    linear_combination (-c) * h2
  · rw [w0_chain hE hdiv hcsl hcls (z₁ := (-1, -1)) (z₂ := (-1, -1)) (z₃ := (-1, 0))
      (z₄ := (1, 0)) (by decide) (by decide) (by decide) (by decide) (by decide) c]
    congr 1
    have h1 := S.l_npar
    have h2 := S.sq_L (-1, 0) (by decide)
    rw [S.s_na, h1, S.s_nc]
    linear_combination (-c) * h2
  · rw [w0_chain hE hdiv hcsl hcls (z₁ := (0, -1)) (z₂ := (-2, -1)) (z₃ := (-2, -1))
      (z₄ := (0, -1)) (by decide) (by decide) (by decide) (by decide) (by decide) c]
    congr 1
    have h2 := S.sq_S (0, -1) (by decide)
    rw [S.s_npar, S.l_nd, S.l_b]
    linear_combination (-c) * h2
  · rw [w0_chain hE hdiv hcsl hcls (z₁ := (0, 1)) (z₂ := (2, 1)) (z₃ := (2, 1))
      (z₄ := (0, 1)) (by decide) (by decide) (by decide) (by decide) (by decide) c]
    congr 1
    have h2 := S.sq_S (0, 1) (by decide)
    rw [S.s_par, S.l_d, S.l_nb]
    linear_combination (-c) * h2

end W0
end OfHE

end CFSG.ClassicalInvolution.WeakCT
