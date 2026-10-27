module

public import CFSG.GH74.Tits83.Windows
public import CFSG.ThirdParty.BrauerInduction.Background.Group.Basic

public section

namespace CFSG.GH74.Tits83

open CFSG.GH74.BNPair
open scoped commutatorElement Pointwise

universe u

variable {G : Type u} [Group G] {n : ℕ}

namespace TitsSystem

variable (T : TitsSystem G n)

@[expose] def IsMu (i : ℤ) (u v w : G) : Prop :=
  v ∈ T.U (i + n) ∧ w ∈ T.U (i + n) ∧
    ∀ j : ℤ, (T.U j).map (MulAut.conj (v * u * w)).toMonoidHom = T.U (2 * i + n - j)

theorem IsMu.inv {i : ℤ} {u v w : G} (h : T.IsMu i u v w) :
    T.IsMu i u⁻¹ w⁻¹ v⁻¹ := by
  refine ⟨(T.U (i + n)).inv_mem h.2.1, (T.U (i + n)).inv_mem h.1, fun j => ?_⟩
  have hm : (T.U (2 * i + n - j)).map
      (MulAut.conj (v * u * w)).toMonoidHom = T.U j := by
    simpa [show 2 * i + n - (2 * i + n - j) = j by ring] using h.2.2 (2 * i + n - j)
  have hinv := CFSG.LieType.Steinberg.map_conj_inv_of_map_conj hm
  have hprod : (v * u * w)⁻¹ = w⁻¹ * u⁻¹ * v⁻¹ := by group
  rwa [hprod] at hinv

theorem isMu_choose (S : TitsSystem G n) {i : ℤ} {u : G} (hu : u ∈ S.U i) (hu1 : u ≠ 1) :
    S.IsMu i u (Classical.choose (S.moufang i u hu hu1))
      (Classical.choose (Classical.choose_spec (S.moufang i u hu hu1)).2) := by
  exact ⟨(Classical.choose_spec (S.moufang i u hu hu1)).1,
    (Classical.choose_spec (Classical.choose_spec (S.moufang i u hu hu1)).2).1,
    (Classical.choose_spec (Classical.choose_spec (S.moufang i u hu hu1)).2).2⟩

theorem IsMu.shift {g : G} {c : ℤ} (hg : T.Moves g (· + c)) {i : ℤ} {u v w : G}
    (h : T.IsMu i u v w) :
    T.IsMu (i + c) (g * u * g⁻¹) (g * v * g⁻¹) (g * w * g⁻¹) := by
  refine ⟨?_, ?_, ?_⟩
  · have hp : g * v * g⁻¹ ∈ T.U (i + n + c) := Moves.conj_mem T hg h.1
    have e : i + n + c = (i + c) + n := by ring
    rwa [e] at hp
  · have hp : g * w * g⁻¹ ∈ T.U (i + n + c) := Moves.conj_mem T hg h.2.1
    have e : i + n + c = (i + c) + n := by ring
    rwa [e] at hp
  · intro j
    have h1 : (T.U j).map (MulAut.conj g⁻¹).toMonoidHom = T.U (j - c) := by
      have := CFSG.LieType.Steinberg.map_conj_inv_of_map_conj (hg (j - c))
      simpa [sub_add_cancel] using this
    have h2 : (T.U (j - c)).map (MulAut.conj (v * u * w)).toMonoidHom =
        T.U (2 * i + n - (j - c)) := h.2.2 (j - c)
    have h3 : (T.U (2 * i + n - (j - c))).map (MulAut.conj g).toMonoidHom =
        T.U (2 * i + n - (j - c) + c) := hg _
    have hmaps : (T.U j).map
        (MulAut.conj (g * v * g⁻¹ * (g * u * g⁻¹) * (g * w * g⁻¹))).toMonoidHom =
        (((T.U j).map (MulAut.conj g⁻¹).toMonoidHom).map
          (MulAut.conj (v * u * w)).toMonoidHom).map
          (MulAut.conj g).toMonoidHom := by
      rw [show g * v * g⁻¹ * (g * u * g⁻¹) * (g * w * g⁻¹) =
        g * ((v * u * w) * g⁻¹) by group]
      rw [CFSG.LieType.Steinberg.map_conj_mul g ((v * u * w) * g⁻¹),
        CFSG.LieType.Steinberg.map_conj_mul (v * u * w) g⁻¹]
    rw [hmaps, h1, h2, h3]
    congr 1
    ring

theorem IsMu.refl {g : G} {c : ℤ} (hg : T.Moves g (c - ·)) {i : ℤ} {u v w : G}
    (h : T.IsMu i u v w) :
    T.IsMu (c - i) (g * u * g⁻¹) (g * v * g⁻¹) (g * w * g⁻¹) := by
  refine ⟨?_, ?_, ?_⟩
  · have hp : g * v * g⁻¹ ∈ T.U (c - (i + n)) := Moves.conj_mem T hg h.1
    have e : c - (i + n) + 2 * (n : ℤ) * 1 = (c - i) + n := by ring
    rw [← e, U_add_two_mul T (c - (i + n)) 1]
    exact hp
  · have hp : g * w * g⁻¹ ∈ T.U (c - (i + n)) := Moves.conj_mem T hg h.2.1
    have e : c - (i + n) + 2 * (n : ℤ) * 1 = (c - i) + n := by ring
    rw [← e, U_add_two_mul T (c - (i + n)) 1]
    exact hp
  · intro j
    have h1 : (T.U j).map (MulAut.conj g⁻¹).toMonoidHom = T.U (c - j) := by
      have := CFSG.LieType.Steinberg.map_conj_inv_of_map_conj (hg (c - j))
      simpa [sub_sub_cancel] using this
    have h2 : (T.U (c - j)).map (MulAut.conj (v * u * w)).toMonoidHom =
        T.U (2 * i + n - (c - j)) := h.2.2 (c - j)
    have h3 : (T.U (2 * i + n - (c - j))).map (MulAut.conj g).toMonoidHom =
        T.U (c - (2 * i + n - (c - j))) := hg _
    have hmaps : (T.U j).map
        (MulAut.conj (g * v * g⁻¹ * (g * u * g⁻¹) * (g * w * g⁻¹))).toMonoidHom =
        (((T.U j).map (MulAut.conj g⁻¹).toMonoidHom).map
          (MulAut.conj (v * u * w)).toMonoidHom).map
          (MulAut.conj g).toMonoidHom := by
      rw [show g * v * g⁻¹ * (g * u * g⁻¹) * (g * w * g⁻¹) =
        g * ((v * u * w) * g⁻¹) by group]
      rw [CFSG.LieType.Steinberg.map_conj_mul g ((v * u * w) * g⁻¹),
        CFSG.LieType.Steinberg.map_conj_mul (v * u * w) g⁻¹]
    rw [hmaps, h1, h2, h3]
    have e : 2 * (c - i) + n - j =
        (c - (2 * i + n - (c - j))) + 2 * (n : ℤ) * 1 := by ring
    rw [e, U_add_two_mul T (c - (2 * i + n - (c - j))) 1]

theorem isMu_shift_iff (s i : ℤ) (u v w : G) :
    (T.shift s).IsMu i u v w ↔ T.IsMu (i + s) u v w := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · have hv : v ∈ (T.shift s).U (i + n) := h.1
      rw [shift_U] at hv
      have e : i + n + s = (i + s) + n := by ring
      rwa [e] at hv
    · have hw : w ∈ (T.shift s).U (i + n) := h.2.1
      rw [shift_U] at hw
      have e : i + n + s = (i + s) + n := by ring
      rwa [e] at hw
    · intro j
      have hp := h.2.2 (j - s)
      rw [shift_U, shift_U] at hp
      have e1 : j - s + s = j := by ring
      have e2 : 2 * i + n - (j - s) + s = 2 * (i + s) + n - j := by ring
      rw [e2, e1] at hp
      exact hp
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · have hv : v ∈ T.U ((i + s) + n) := h.1
      have e : (i + s) + n = i + n + s := by ring
      rw [e] at hv
      rw [shift_U]
      exact hv
    · have hw : w ∈ T.U ((i + s) + n) := h.2.1
      have e : (i + s) + n = i + n + s := by ring
      rw [e] at hw
      rw [shift_U]
      exact hw
    · intro j
      have hp := h.2.2 (j + s)
      rw [shift_U, shift_U]
      rw [hp]
      congr 1
      ring

theorem isMu_refl_iff (c i : ℤ) (u v w : G) :
    (T.refl c).IsMu i u v w ↔ T.IsMu (c - i) u v w := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · have hv : v ∈ (T.refl c).U (i + n) := h.1
      rw [refl_U] at hv
      have e : c - (i + n) + 2 * (n : ℤ) * 1 = (c - i) + n := by ring
      rw [← e, U_add_two_mul T (c - (i + n)) 1]
      exact hv
    · have hw : w ∈ (T.refl c).U (i + n) := h.2.1
      rw [refl_U] at hw
      have e : c - (i + n) + 2 * (n : ℤ) * 1 = (c - i) + n := by ring
      rw [← e, U_add_two_mul T (c - (i + n)) 1]
      exact hw
    · intro j
      have hp := h.2.2 (c - j)
      rw [refl_U, refl_U] at hp
      have e1 : c - (c - j) = j := by ring
      have e2 : 2 * (c - i) + n - j =
          (c - (2 * i + n - (c - j))) + 2 * (n : ℤ) * 1 := by ring
      rw [e1] at hp
      rw [hp]
      rw [e2, U_add_two_mul T (c - (2 * i + n - (c - j))) 1]
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · have hv : v ∈ T.U ((c - i) + n) := h.1
      have e : c - (i + n) + 2 * (n : ℤ) * 1 = (c - i) + n := by ring
      rw [← e, U_add_two_mul T (c - (i + n)) 1] at hv
      rw [refl_U]
      exact hv
    · have hw : w ∈ T.U ((c - i) + n) := h.2.1
      have e : c - (i + n) + 2 * (n : ℤ) * 1 = (c - i) + n := by ring
      rw [← e, U_add_two_mul T (c - (i + n)) 1] at hw
      rw [refl_U]
      exact hw
    · intro j
      have hp := h.2.2 (c - j)
      rw [refl_U, refl_U]
      rw [hp]
      have e : 2 * (c - i) + n - (c - j) =
          c - (2 * i + n - j) + 2 * (n : ℤ) * 1 := by ring
      rw [e, U_add_two_mul T (c - (2 * i + n - j)) 1]

noncomputable def nu (i : ℤ) (u : G) : G := by
  classical
  exact if h : u ∈ T.U i ∧ u ≠ 1 then Classical.choose (T.moufang i u h.1 h.2) else 1

noncomputable def nu' (i : ℤ) (u : G) : G := by
  classical
  exact if h : u ∈ T.U i ∧ u ≠ 1 then
    Classical.choose (Classical.choose_spec (T.moufang i u h.1 h.2)).2 else 1

theorem nu_of_not_mem {i : ℤ} {u : G} (h : ¬(u ∈ T.U i ∧ u ≠ 1)) : T.nu i u = 1 := by
  classical
  simp only [nu]
  rw [dif_neg h]

theorem nu'_of_not_mem {i : ℤ} {u : G} (h : ¬(u ∈ T.U i ∧ u ≠ 1)) : T.nu' i u = 1 := by
  classical
  simp only [nu']
  rw [dif_neg h]

@[expose] noncomputable def mu (i : ℤ) (u : G) : G := T.nu i u * u * T.nu' i u

theorem isMu_nu {i : ℤ} {u : G} (hu : u ∈ T.U i) (hu1 : u ≠ 1) :
    T.IsMu i u (T.nu i u) (T.nu' i u) := by
  classical
  have h : u ∈ T.U i ∧ u ≠ 1 := ⟨hu, hu1⟩
  simp only [nu, nu']
  rw [dif_pos h, dif_pos h]
  exact ⟨(Classical.choose_spec (T.moufang i u hu hu1)).1,
    (Classical.choose_spec (Classical.choose_spec (T.moufang i u hu hu1)).2).1,
    (Classical.choose_spec (Classical.choose_spec (T.moufang i u hu hu1)).2).2⟩

theorem moves_mu {i : ℤ} {u : G} (hu : u ∈ T.U i) (hu1 : u ≠ 1) :
    T.Moves (T.mu i u) (fun j => 2 * i + n - j) := by
  intro j
  exact (T.isMu_nu hu hu1).2.2 j

theorem eq_one_of_mem_normalizer (hn : 3 ≤ n) {i : ℤ} {u : G} (hu : u ∈ T.U i)
    (hN : u ∈ Subgroup.normalizer (T.U (i + n) : Set G)) : u = 1 := by
  by_contra hu1
  have hIs := T.isMu_nu hu hu1
  have hv : T.nu i u ∈ T.U (i + n) := hIs.1
  have hw : T.nu' i u ∈ T.U (i + n) := hIs.2.1
  have hmN : T.mu i u ∈ Subgroup.normalizer (T.U (i + n) : Set G) := by
    have hvN : T.nu i u ∈ Subgroup.normalizer (T.U (i + n) : Set G) :=
      Subgroup.le_normalizer hv
    have hwN : T.nu' i u ∈ Subgroup.normalizer (T.U (i + n) : Set G) :=
      Subgroup.le_normalizer hw
    rw [mu]
    exact (Subgroup.normalizer (T.U (i + n) : Set G)).mul_mem
      ((Subgroup.normalizer (T.U (i + n) : Set G)).mul_mem hvN hN) hwN
  have hmaps := CFSG.LieType.Steinberg.mem_normalizer_iff_map_conj.1 hmN
  have hmov : (T.U (i + n)).map (MulAut.conj (T.mu i u)).toMonoidHom = T.U i := by
    have h := (T.moves_mu hu hu1) (i + n)
    change (T.U (i + n)).map (MulAut.conj (T.mu i u)).toMonoidHom =
      T.U (2 * i + n - (i + n)) at h
    rwa [show 2 * i + n - (i + n) = i by ring] at h
  have hUi : T.U i = T.U (i + n) := by
    rw [hmaps] at hmov
    exact hmov.symm
  have hm_ui : T.mu i u ∈ T.U i := by
    rw [hUi, mu]
    exact (T.U (i + n)).mul_mem
      ((T.U (i + n)).mul_mem hv (hUi ▸ hu)) hw
  have hnorm : T.U i ≤ Subgroup.normalizer (T.U (i + 1) : Set G) := by
    have h := (T.le_normalizer_win (a := i + 1) (b := i + 1) (by omega)).1
    have e : i + 1 - 1 = i := by ring
    rw [e] at h
    simpa [win] using h
  have hconj1 := CFSG.LieType.Steinberg.mem_normalizer_iff_map_conj.1 (hnorm hm_ui)
  have hmov1 : T.U (i + 1) = T.U (2 * i + n - (i + 1)) := by
    have h := (T.moves_mu hu hu1) (i + 1)
    rw [hconj1] at h
    exact h
  rw [show 2 * i + n - (i + 1) = i + n - 1 by ring] at hmov1
  have hUn : T.U (i + n - 1) = T.U (i + 1) := hmov1.symm
  have hne : i + 1 ≠ i + n - 1 := by omega
  have hdist : |(i + 1) - (i + n - 1)| < (n : ℤ) := by
    have h1 : (i + 1) - (i + n - 1) = -((n : ℤ) - 2) := by ring
    rw [h1, abs_neg, abs_of_nonneg (by omega)]
    omega
  have hbot : T.U (i + 1) = ⊥ := by
    have h := T.U_inf_U hne hdist
    rw [hUn] at h
    simpa using h
  exact T.ne_bot (i + 1) hbot

theorem nu_ne_one (hn : 3 ≤ n) {i : ℤ} {u : G} (hu : u ∈ T.U i) (hu1 : u ≠ 1) :
    T.nu i u ≠ 1 := by
  intro hv
  have hIs := T.isMu_nu hu hu1
  have hw : T.nu' i u ∈ T.U (i + n) := hIs.2.1
  have hmov : (T.U (i + n)).map (MulAut.conj (T.mu i u)).toMonoidHom = T.U i := by
    have h := (T.moves_mu hu hu1) (i + n)
    change (T.U (i + n)).map (MulAut.conj (T.mu i u)).toMonoidHom =
      T.U (2 * i + n - (i + n)) at h
    rwa [show 2 * i + n - (i + n) = i by ring] at h
  have hmu : T.mu i u = u * T.nu' i u := by
    simp only [mu, hv]
    rw [one_mul]
  rw [hmu] at hmov
  rw [CFSG.LieType.Steinberg.map_conj_mul] at hmov
  rw [CFSG.LieType.Steinberg.map_conj_of_mem hw] at hmov
  have hUi : T.U i = T.U (i + n) := by
    have hinv := CFSG.LieType.Steinberg.map_conj_inv_of_map_conj hmov
    have hu_norm : (T.U i).map (MulAut.conj u⁻¹).toMonoidHom = T.U i :=
      CFSG.LieType.Steinberg.map_conj_of_mem ((T.U i).inv_mem hu)
    rw [hu_norm] at hinv
    exact hinv
  exact hu1 (T.eq_one_of_mem_normalizer hn hu (by
    simpa [hUi] using Subgroup.le_normalizer hu))

theorem isMu_fst_eq (hn : 3 ≤ n) {i : ℤ} {u v w v' w' : G} (hu : u ∈ T.U i)
    (h : T.IsMu i u v w) (h' : T.IsMu i u v' w') : v = v' := by
  have hmap : ((T.U (i + n)).map (MulAut.conj u).toMonoidHom).map
      (MulAut.conj v).toMonoidHom = T.U i := by
    have h0 := h.2.2 (i + n)
    change (T.U (i + n)).map (MulAut.conj (v * u * w)).toMonoidHom =
      T.U (2 * i + n - (i + n)) at h0
    rw [show 2 * i + n - (i + n) = i by ring] at h0
    rw [mul_assoc] at h0
    rw [CFSG.LieType.Steinberg.map_conj_mul v (u * w)] at h0
    rw [CFSG.LieType.Steinberg.map_conj_mul u w] at h0
    rwa [CFSG.LieType.Steinberg.map_conj_of_mem h.2.1] at h0
  have hmap' : ((T.U (i + n)).map (MulAut.conj u).toMonoidHom).map
      (MulAut.conj v').toMonoidHom = T.U i := by
    have h0 := h'.2.2 (i + n)
    change (T.U (i + n)).map (MulAut.conj (v' * u * w')).toMonoidHom =
      T.U (2 * i + n - (i + n)) at h0
    rw [show 2 * i + n - (i + n) = i by ring] at h0
    rw [mul_assoc] at h0
    rw [CFSG.LieType.Steinberg.map_conj_mul v' (u * w')] at h0
    rw [CFSG.LieType.Steinberg.map_conj_mul u w'] at h0
    rwa [CFSG.LieType.Steinberg.map_conj_of_mem h'.2.1] at h0
  have hA : (T.U i).map (MulAut.conj v⁻¹).toMonoidHom =
      (T.U (i + n)).map (MulAut.conj u).toMonoidHom :=
    CFSG.LieType.Steinberg.map_conj_inv_of_map_conj hmap
  have hA' : (T.U i).map (MulAut.conj v'⁻¹).toMonoidHom =
      (T.U (i + n)).map (MulAut.conj u).toMonoidHom :=
    CFSG.LieType.Steinberg.map_conj_inv_of_map_conj hmap'
  have hAB : (T.U i).map (MulAut.conj v⁻¹).toMonoidHom =
      (T.U i).map (MulAut.conj v'⁻¹).toMonoidHom := hA.trans hA'.symm
  have hnorm : v' * v⁻¹ ∈ Subgroup.normalizer (T.U i : Set G) := by
    rw [CFSG.LieType.Steinberg.mem_normalizer_iff_map_conj]
    rw [CFSG.LieType.Steinberg.map_conj_mul]
    rw [hAB]
    rw [← CFSG.LieType.Steinberg.map_conj_mul v' v'⁻¹, mul_inv_cancel,
      CFSG.LieType.Steinberg.map_conj_one]
  have hmem : v' * v⁻¹ ∈ T.U (i + n) :=
    (T.U (i + n)).mul_mem h'.1 ((T.U (i + n)).inv_mem h.1)
  have hidx : i + n + n = i + 2 * (n : ℤ) := by ring
  have hN : v' * v⁻¹ ∈ Subgroup.normalizer (T.U (i + n + n) : Set G) := by
    rw [hidx, T.periodic i]
    exact hnorm
  have hone := T.eq_one_of_mem_normalizer hn hmem hN
  exact (mul_inv_eq_one.mp hone).symm

theorem isMu_unique (hn : 3 ≤ n) {i : ℤ} {u v w v' w' : G} (hu : u ∈ T.U i)
    (hu1 : u ≠ 1) (h : T.IsMu i u v w) (h' : T.IsMu i u v' w') : v = v' ∧ w = w' := by
  refine ⟨T.isMu_fst_eq hn hu h h', ?_⟩
  have h1 := h.inv
  have h2 := h'.inv
  have hw := T.isMu_fst_eq hn ((T.U i).inv_mem hu) h1 h2
  exact inv_injective hw

theorem nu_inv (hn : 3 ≤ n) {i : ℤ} {u : G} (hu : u ∈ T.U i) (hu1 : u ≠ 1) :
    T.nu i u⁻¹ = (T.nu' i u)⁻¹ := by
  have hu' : u⁻¹ ∈ T.U i := (T.U i).inv_mem hu
  have hu1' : u⁻¹ ≠ 1 := inv_ne_one.mpr hu1
  exact (T.isMu_unique hn hu' hu1' (T.isMu_nu hu' hu1') (T.isMu_nu hu hu1).inv).1

theorem nu'_inv (hn : 3 ≤ n) {i : ℤ} {u : G} (hu : u ∈ T.U i) (hu1 : u ≠ 1) :
    T.nu' i u⁻¹ = (T.nu i u)⁻¹ := by
  have hu' : u⁻¹ ∈ T.U i := (T.U i).inv_mem hu
  have hu1' : u⁻¹ ≠ 1 := inv_ne_one.mpr hu1
  exact (T.isMu_unique hn hu' hu1' (T.isMu_nu hu' hu1') (T.isMu_nu hu hu1).inv).2

theorem nu'_ne_one (hn : 3 ≤ n) {i : ℤ} {u : G} (hu : u ∈ T.U i) (hu1 : u ≠ 1) :
    T.nu' i u ≠ 1 := by
  intro hw
  have hu' : u⁻¹ ∈ T.U i := (T.U i).inv_mem hu
  have hu1' : u⁻¹ ≠ 1 := inv_ne_one.mpr hu1
  have h := T.nu_ne_one hn hu' hu1'
  rw [T.nu_inv hn hu hu1, hw, inv_one] at h
  exact h rfl

theorem mu_inv (hn : 3 ≤ n) {i : ℤ} {u : G} (hu : u ∈ T.U i) (hu1 : u ≠ 1) :
    T.mu i u⁻¹ = (T.mu i u)⁻¹ := by
  simp only [mu, T.nu_inv hn hu hu1, T.nu'_inv hn hu hu1]
  group

theorem mu_nu (hn : 3 ≤ n) {i : ℤ} {u : G} (hu : u ∈ T.U i) (hu1 : u ≠ 1) :
    T.mu (i + n) (T.nu i u) = T.mu i u ∧ T.nu' (i + n) (T.nu i u) = u := by
  have hv : T.nu i u ∈ T.U (i + n) := (T.isMu_nu hu hu1).1
  have hw : T.nu' i u ∈ T.U (i + n) := (T.isMu_nu hu hu1).2.1
  have hv1 : T.nu i u ≠ 1 := T.nu_ne_one hn hu hu1
  have hdecomp : T.mu i u * T.nu' i u * (T.mu i u)⁻¹ * T.nu i u * u = T.mu i u := by
    simp only [mu]
    group
  have hbar : T.mu i u * T.nu' i u * (T.mu i u)⁻¹ ∈ T.U i := by
    have hmov : (T.U (i + n)).map (MulAut.conj (T.mu i u)).toMonoidHom = T.U i := by
      have h := (T.moves_mu hu hu1) (i + n)
      change (T.U (i + n)).map (MulAut.conj (T.mu i u)).toMonoidHom =
        T.U (2 * i + n - (i + n)) at h
      rwa [show 2 * i + n - (i + n) = i by ring] at h
    have hmem := CFSG.LieType.Steinberg.conj_mem_map_conj
      (g := T.mu i u) hw
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
  have huniq := T.isMu_unique hn hv hv1 hIs (T.isMu_nu hv hv1)
  refine ⟨?_, huniq.2.symm⟩
  simp only [mu]
  rw [← huniq.1, ← huniq.2, hdecomp]
  rfl

theorem mu_nu' (hn : 3 ≤ n) {i : ℤ} {u : G} (hu : u ∈ T.U i) (hu1 : u ≠ 1) :
    T.mu (i + n) (T.nu' i u) = T.mu i u ∧ T.nu (i + n) (T.nu' i u) = u := by
  have hw : T.nu' i u ∈ T.U (i + n) := (T.isMu_nu hu hu1).2.1
  have hw1 : T.nu' i u ≠ 1 := T.nu'_ne_one hn hu hu1
  have hu' : u⁻¹ ∈ T.U i := (T.U i).inv_mem hu
  have hu1' : u⁻¹ ≠ 1 := inv_ne_one.mpr hu1
  have h := T.mu_nu hn hu' hu1'
  rw [T.nu_inv hn hu hu1] at h
  have h1 : T.mu (i + n) (T.nu' i u) = T.mu i u := by
    rw [T.mu_inv hn hw hw1, T.mu_inv hn hu hu1] at h
    exact inv_injective h.1
  have h2 : T.nu (i + n) (T.nu' i u) = u := by
    rw [T.nu'_inv hn hw hw1] at h
    exact inv_injective h.2
  exact ⟨h1, h2⟩

theorem mu_conj (hn : 3 ≤ n) {g : G} {ε c : ℤ} (hε : ε = 1 ∨ ε = -1)
    (hg : T.Moves g (fun j => ε * j + c)) {i : ℤ} {u : G} (hu : u ∈ T.U i)
    (hu1 : u ≠ 1) :
    T.mu (ε * i + c) (g * u * g⁻¹) = g * T.mu i u * g⁻¹ ∧
      T.nu (ε * i + c) (g * u * g⁻¹) = g * T.nu i u * g⁻¹ ∧
      T.nu' (ε * i + c) (g * u * g⁻¹) = g * T.nu' i u * g⁻¹ := by
  have hmem : g * u * g⁻¹ ∈ T.U (ε * i + c) := by
    simpa using Moves.conj_mem T hg (j := i) hu
  have hne : g * u * g⁻¹ ≠ 1 := by
    intro h
    exact hu1 ((MulAut.conj g).injective (by simpa using h))
  rcases hε with rfl | rfl
  · have hg' : T.Moves g (· + c) := by simpa [one_mul] using hg
    have hmem' : g * u * g⁻¹ ∈ T.U (i + c) := by simpa [one_mul] using hmem
    have htrans := IsMu.shift T hg' (T.isMu_nu hu hu1)
    have huniq := T.isMu_unique hn hmem' hne htrans (T.isMu_nu hmem' hne)
    have hgoal : T.mu (i + c) (g * u * g⁻¹) = g * T.mu i u * g⁻¹ ∧
        T.nu (i + c) (g * u * g⁻¹) = g * T.nu i u * g⁻¹ ∧
        T.nu' (i + c) (g * u * g⁻¹) = g * T.nu' i u * g⁻¹ := by
      refine ⟨?_, huniq.1.symm, huniq.2.symm⟩
      simp only [mu]
      rw [← huniq.1, ← huniq.2]
      group
    simpa [one_mul] using hgoal
  · have hg' : T.Moves g (c - ·) := by
      simpa [sub_eq_add_neg, neg_one_mul, add_comm] using hg
    have hmem' : g * u * g⁻¹ ∈ T.U (c - i) := by
      simpa [sub_eq_add_neg, neg_one_mul, add_comm] using hmem
    have htrans := IsMu.refl T hg' (T.isMu_nu hu hu1)
    have huniq := T.isMu_unique hn hmem' hne htrans (T.isMu_nu hmem' hne)
    have hgoal : T.mu (c - i) (g * u * g⁻¹) = g * T.mu i u * g⁻¹ ∧
        T.nu (c - i) (g * u * g⁻¹) = g * T.nu i u * g⁻¹ ∧
        T.nu' (c - i) (g * u * g⁻¹) = g * T.nu' i u * g⁻¹ := by
      refine ⟨?_, huniq.1.symm, huniq.2.symm⟩
      simp only [mu]
      rw [← huniq.1, ← huniq.2]
      group
    simpa [sub_eq_add_neg, neg_one_mul, add_comm] using hgoal

theorem nu_shift (hn : 3 ≤ n) (s i : ℤ) (u : G) :
    (T.shift s).nu i u = T.nu (i + s) u := by
  by_cases h : u ∈ T.U (i + s) ∧ u ≠ 1
  · have h' : u ∈ (T.shift s).U i ∧ u ≠ 1 := by
      simpa [shift_U] using h
    simp only [nu]
    rw [dif_pos h', dif_pos h]
    have htrans : T.IsMu (i + s) u
        (Classical.choose ((T.shift s).moufang i u h'.1 h'.2))
        (Classical.choose
          (Classical.choose_spec ((T.shift s).moufang i u h'.1 h'.2)).2) :=
      (T.isMu_shift_iff s i u _ _).1 (isMu_choose (T.shift s) h'.1 h'.2)
    simpa [nu, dif_pos h] using
      (T.isMu_unique hn h.1 h.2 htrans (T.isMu_nu h.1 h.2)).1
  · have h' : ¬(u ∈ (T.shift s).U i ∧ u ≠ 1) := by
      simpa [shift_U] using h
    simp only [nu, dif_neg h', dif_neg h]

theorem nu_refl (hn : 3 ≤ n) (c i : ℤ) (u : G) :
    (T.refl c).nu i u = T.nu (c - i) u := by
  by_cases h : u ∈ T.U (c - i) ∧ u ≠ 1
  · have h' : u ∈ (T.refl c).U i ∧ u ≠ 1 := by
      simpa [refl_U] using h
    simp only [nu]
    rw [dif_pos h', dif_pos h]
    have htrans : T.IsMu (c - i) u
        (Classical.choose ((T.refl c).moufang i u h'.1 h'.2))
        (Classical.choose
          (Classical.choose_spec ((T.refl c).moufang i u h'.1 h'.2)).2) :=
      (T.isMu_refl_iff c i u _ _).1 (isMu_choose (T.refl c) h'.1 h'.2)
    simpa [nu, dif_pos h] using
      (T.isMu_unique hn h.1 h.2 htrans (T.isMu_nu h.1 h.2)).1
  · have h' : ¬(u ∈ (T.refl c).U i ∧ u ≠ 1) := by
      simpa [refl_U] using h
    simp only [nu, dif_neg h', dif_neg h]

theorem exists_moves_shift (s : ℤ) : ∃ g : G, T.Moves g (· + 2 * s) := by
  obtain ⟨u, hu, hu1⟩ := Subgroup.exists_mem_ne_one_of_ne_bot (T.ne_bot s)
  obtain ⟨v, hv, hv1⟩ := Subgroup.exists_mem_ne_one_of_ne_bot (T.ne_bot 0)
  refine ⟨T.mu s u * T.mu 0 v, ?_⟩
  have h := Moves.mul T (T.moves_mu hu hu1) (T.moves_mu hv hv1)
  have hcomp : (fun j : ℤ => 2 * s + n - j) ∘ (fun j : ℤ => 2 * 0 + n - j) =
      (fun j : ℤ => j + 2 * s) := by
    funext j
    simp only [Function.comp_apply]
    ring
  rwa [hcomp] at h

theorem exists_moves_refl (c : ℤ) (hc : Even (c - n)) : ∃ g : G, T.Moves g (c - ·) := by
  obtain ⟨k, hk⟩ := hc
  have hc' : c = 2 * k + n := by
    rw [show c = (c - n) + n by ring, hk]
    ring
  obtain ⟨u, hu, hu1⟩ := Subgroup.exists_mem_ne_one_of_ne_bot (T.ne_bot k)
  refine ⟨T.mu k u, ?_⟩
  rw [hc']
  exact T.moves_mu hu hu1

theorem exists_moves_refl_of_even (c : ℤ) (hc : Even c) (hn : Even (n : ℤ)) :
    ∃ g : G, T.Moves g (c - ·) := by
  obtain ⟨a, ha⟩ := hc
  obtain ⟨b, hb⟩ := hn
  exact T.exists_moves_refl c ⟨a - b, by rw [ha, hb]; ring⟩

end TitsSystem

end CFSG.GH74.Tits83
