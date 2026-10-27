module

public import CFSG.CGT.PushingUpLit.Orth.OrthDef
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.CGT.PushingUpLit.Orth

open Equiv

variable {G : Type*} [Group G] {M Q : Subgroup G}

theorem conj_inv_mem_of_conj_mem [Finite G] {H : Subgroup G} {n : G}
    (h : ∀ x ∈ H, n * x * n⁻¹ ∈ H) {x : G} (hx : x ∈ H) : n⁻¹ * x * n ∈ H := by
  let f : ↥H → ↥H := fun y => ⟨n * y * n⁻¹, h y y.2⟩
  have hf : Function.Injective f := by
    intro a b hab
    have h1 : n * (a : G) * n⁻¹ = n * (b : G) * n⁻¹ := congrArg Subtype.val hab
    apply Subtype.ext
    calc (a : G) = n⁻¹ * (n * (a : G) * n⁻¹) * n := by group
      _ = n⁻¹ * (n * (b : G) * n⁻¹) * n := by rw [h1]
      _ = b := by group
  obtain ⟨y, hy⟩ := Finite.injective_iff_surjective.1 hf ⟨x, hx⟩
  have h1 : n * (y : G) * n⁻¹ = x := congrArg Subtype.val hy
  have h2 : n⁻¹ * x * n = y := by
    rw [← h1]; group
  rw [h2]
  exact y.2

theorem mem_centralizer_of_conj_eq {x y : G} (h : x * y * x⁻¹ = y) :
    x ∈ Subgroup.centralizer ({y} : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  rw [Set.mem_singleton_iff.1 ht]
  calc y * x = (x * y * x⁻¹) * x := by rw [h]
    _ = x * y := by group

theorem card_centralizer_conj {y z : G} (g : G) (h : g * y * g⁻¹ = z) :
    Nat.card (Subgroup.centralizer ({y} : Set G)) =
      Nat.card (Subgroup.centralizer ({z} : Set G)) := by
  refine Nat.card_congr
    { toFun := fun x => ⟨g * x * g⁻¹, ?_⟩
      invFun := fun x => ⟨g⁻¹ * x * g, ?_⟩
      left_inv := fun x => ?_
      right_inv := fun x => ?_ }
  · have hx := Subgroup.mem_centralizer_iff.1 x.2 y (Set.mem_singleton y)
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    rw [Set.mem_singleton_iff.1 ht, ← h]
    calc g * y * g⁻¹ * (g * (x : G) * g⁻¹) = g * (y * x) * g⁻¹ := by group
      _ = g * (x * y) * g⁻¹ := by rw [hx]
      _ = g * (x : G) * g⁻¹ * (g * y * g⁻¹) := by group
  · have hx := Subgroup.mem_centralizer_iff.1 x.2 z (Set.mem_singleton z)
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    rw [Set.mem_singleton_iff.1 ht]
    have hy : y = g⁻¹ * z * g := by rw [← h]; group
    rw [hy]
    calc g⁻¹ * z * g * (g⁻¹ * (x : G) * g) = g⁻¹ * (z * x) * g := by group
      _ = g⁻¹ * (x * z) * g := by rw [hx]
      _ = g⁻¹ * (x : G) * g * (g⁻¹ * z * g) := by group
  · exact Subtype.ext (by group)
  · exact Subtype.ext (by group)

namespace OrthCfg

variable (C : OrthCfg G M Q)

include C

theorem S_isPGroup : IsPGroup 2 (C.pre D8) := C.isPGroup_pre isPGroup_D8

theorem relIndex_S : (C.pre D8).relIndex M = 15 := by rw [C.relindex_pre, index_D8]

theorem S_fixes {w : Vec5} (hw : ∀ σ, isD8 σ → permAct σ w = w) {s : G} (hs : s ∈ C.pre D8) :
    s * C.elt w * s⁻¹ = C.elt w := by
  rw [C.conj_elt (C.pre_le_M D8 hs), hw _ (C.th_mem_of_mem_pre hs)]

theorem elt_mem_centralizer_S {w : Vec5} (hw : ∀ σ, isD8 σ → permAct σ w = w) :
    C.elt w ∈ Subgroup.centralizer ((C.pre D8 : Subgroup G) : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  have := C.S_fixes hw hs
  calc s * C.elt w = (s * C.elt w * s⁻¹) * s := by group
    _ = C.elt w * s := by rw [this]

theorem fixed_of_mem_centralizer_S {c : G}
    (hc : c ∈ Subgroup.centralizer ((C.pre D8 : Subgroup G) : Set G)) :
    c ∈ Q ∧ ∀ σ, isD8 σ → permAct σ (C.vec c) = C.vec c := by
  have hcQ : c ∈ Q := by
    apply C.centralizer_Q
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact Subgroup.mem_centralizer_iff.1 hc q (C.Q_le_pre D8 hq)
  refine ⟨hcQ, fun σ hσ => ?_⟩
  obtain ⟨s, hs, hsσ⟩ := C.pre_surj (A := D8) hσ
  have h1 : s * c * s⁻¹ = c := by
    have := Subgroup.mem_centralizer_iff.1 hc s hs
    calc s * c * s⁻¹ = c * s * s⁻¹ := by rw [this]
      _ = c := by group
  have h2 := C.conj_vec (C.pre_le_M D8 hs) hcQ
  rw [h1, hsσ] at h2
  exact h2.symm

variable (hrig : ∀ v : Vec5, Rigid v → Subgroup.centralizer ({C.elt v} : Set G) ≤ M)

include hrig

theorem exists_sylow_eq [Finite G] : ∃ T : Sylow 2 G, (T : Subgroup G) = C.pre D8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hST⟩ := C.S_isPGroup.exists_le_sylow
  refine ⟨T, ?_⟩
  have hz4 : C.elt z4 ∈ (T : Subgroup G) := hST (C.Q_le_pre D8 (C.elt_mem z4))
  have : Nontrivial ↥(T : Subgroup G) :=
    ⟨⟨1, ⟨C.elt z4, hz4⟩, fun h => C.elt_ne_one z4_ne_zero (congrArg Subtype.val h).symm⟩⟩
  have := T.isPGroup'.center_nontrivial
  obtain ⟨c, hc1⟩ := exists_ne (1 : ↥(Subgroup.center ↥(T : Subgroup G)))
  have hcT : ∀ t ∈ (T : Subgroup G), t * ((c : ↥(T : Subgroup G)) : G) =
      ((c : ↥(T : Subgroup G)) : G) * t := by
    intro t ht
    have := Subgroup.mem_center_iff.1 c.2 ⟨t, ht⟩
    exact congrArg Subtype.val this
  set c0 : G := ((c : ↥(T : Subgroup G)) : G) with hc0
  have hc0ne : c0 ≠ 1 := fun h => hc1 (Subtype.ext (Subtype.ext h))
  have hcent : c0 ∈ Subgroup.centralizer ((C.pre D8 : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact hcT s (hST hs)
  obtain ⟨hcQ, hfix⟩ := C.fixed_of_mem_centralizer_S hcent
  have hw := D8_fixed (C.vec c0) hfix
  have hw0 : C.vec c0 ≠ 0 := fun h => hc0ne ((C.vec_eq_zero_iff hcQ).1 h)
  have hrw : Rigid (C.vec c0) := by
    rcases hw with h | h | h | h
    · exact absurd h hw0
    · rw [h]; exact rigid_z4
    · rw [h]; exact rigid_z1
    · rw [h]; exact rigid_ones
  have hTM : (T : Subgroup G) ≤ M := by
    intro t ht
    apply hrig _ hrw
    rw [C.elt_vec hcQ, Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff.1 hy]
    exact (hcT t ht).symm
  have hST' : (C.pre D8) ≤ (T : Subgroup G) := hST
  have h1 : (C.pre D8).relIndex (T : Subgroup G) * (T : Subgroup G).relIndex M =
      (C.pre D8).relIndex M := Subgroup.relIndex_mul_relIndex _ _ _ hST' hTM
  rw [C.relIndex_S] at h1
  have h2 : ∃ n, (C.pre D8).relIndex (T : Subgroup G) = 2 ^ n := by
    have := T.isPGroup'.index ((C.pre D8).subgroupOf (T : Subgroup G))
    exact this
  obtain ⟨n, hn⟩ := h2
  rw [hn] at h1
  have h3 : 2 ^ n ∣ 15 := ⟨_, h1.symm⟩
  have hn0 : n = 0 := by
    by_contra hne
    have h4 : 2 ∣ 2 ^ n := dvd_pow_self 2 hne
    have := h4.trans h3
    omega
  rw [hn0, pow_zero, Subgroup.relIndex_eq_one] at hn
  exact le_antisymm hn hST'

theorem mem_of_mem_normalizer_S [Finite G] {n : G}
    (hn : n ∈ Subgroup.normalizer ((C.pre D8 : Subgroup G) : Set G)) : n ∈ C.pre D8 := by
  have hnS : ∀ s ∈ C.pre D8, n * s * n⁻¹ ∈ C.pre D8 := fun s hs =>
    (Subgroup.mem_normalizer_iff.1 hn s).1 hs
  have hnS' : ∀ s ∈ C.pre D8, n⁻¹ * s * n ∈ C.pre D8 := fun s hs => by
    have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hn) s).1 hs
    simpa using this
  set r := C.elt ones with hr
  have hrM : ∀ m ∈ M, m * r * m⁻¹ = r := fun m hm => by
    rw [hr, C.conj_elt hm, permAct_ones]
  have hr1 : r ≠ 1 := C.elt_ne_one ones_ne_zero
  have hcent : n * r * n⁻¹ ∈ Subgroup.centralizer ((C.pre D8 : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have h1 := hrM (n⁻¹ * s * n) (C.pre_le_M D8 (hnS' s hs))
    calc s * (n * r * n⁻¹) = n * ((n⁻¹ * s * n) * r * (n⁻¹ * s * n)⁻¹) * n⁻¹ * s := by group
      _ = n * r * n⁻¹ * s := by rw [h1]
  obtain ⟨hzQ, hfix⟩ := C.fixed_of_mem_centralizer_S hcent
  have hw := D8_fixed _ hfix
  have hw0 : C.vec (n * r * n⁻¹) ≠ 0 := fun h => by
    have h1 := (C.vec_eq_zero_iff hzQ).1 h
    apply hr1
    calc r = n⁻¹ * (n * r * n⁻¹) * n := by group
      _ = 1 := by rw [h1]; group
  have hnr : n * r * n⁻¹ = r := by
    by_cases hones : C.vec (n * r * n⁻¹) = ones
    · rw [← C.elt_vec hzQ, hones]
    · exfalso
      have hrg : Rigid (C.vec (n * r * n⁻¹)) := by
        rcases hw with h | h | h | h
        · exact absurd h hw0
        · rw [h]; exact rigid_z4
        · rw [h]; exact rigid_z1
        · exact absurd h hones
      have hle : Subgroup.centralizer ({n * r * n⁻¹} : Set G) ≤ M := by
        have := hrig _ hrg
        rwa [C.elt_vec hzQ] at this
      have h2 : ∀ m ∈ M, n * m * n⁻¹ ∈ M := fun m hm => by
        apply hle
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff.1 hy]
        have h3 : m * r * m⁻¹ = r := hrM m hm
        have h4 : r * m = m * r := by
          calc r * m = (m * r * m⁻¹) * m := by rw [h3]
            _ = m * r := by group
        calc n * r * n⁻¹ * (n * m * n⁻¹) = n * (r * m) * n⁻¹ := by group
          _ = n * (m * r) * n⁻¹ := by rw [h4]
          _ = n * m * n⁻¹ * (n * r * n⁻¹) := by group
      have h3 : ∀ m ∈ M, n⁻¹ * m * n ∈ M := fun m hm => conj_inv_mem_of_conj_mem h2 hm
      have h4 : ∀ m ∈ M, permAct (C.th m) (C.vec (n * r * n⁻¹)) = C.vec (n * r * n⁻¹) := by
        intro m hm
        have h5 := hrM (n⁻¹ * m * n) (h3 m hm)
        have h6 : m * (n * r * n⁻¹) * m⁻¹ = n * r * n⁻¹ := by
          calc m * (n * r * n⁻¹) * m⁻¹
              = n * ((n⁻¹ * m * n) * r * (n⁻¹ * m * n)⁻¹) * n⁻¹ := by group
            _ = n * r * n⁻¹ := by rw [h5]
        have := C.conj_vec hm hzQ
        rw [h6] at this
        exact this.symm
      have h7 : ∀ σ : Perm (Fin 5), permAct σ (C.vec (n * r * n⁻¹)) = C.vec (n * r * n⁻¹) := by
        intro σ
        obtain ⟨m, hm, hmσ⟩ := C.th_surj σ
        rw [← hmσ]
        exact h4 m hm
      rcases fixed_all _ h7 with h8 | h8
      · exact hw0 h8
      · exact hones h8
  have hnM : n ∈ M := by
    apply hrig ones rigid_ones
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff.1 hy]
    calc r * n = (n * r * n⁻¹) * n := by rw [hnr]
      _ = n * r := by group
  have hD : isD8 (C.th n) := by
    apply D8_normalizer
    intro d hd
    obtain ⟨s, hs, hsd⟩ := C.pre_surj (A := D8) hd
    have h1 := hnS s hs
    have h2 := C.th_mem_of_mem_pre h1
    have hsM := C.pre_le_M D8 hs
    rwa [C.th_mul (M.mul_mem hnM hsM) (M.inv_mem hnM), C.th_mul hnM hsM, C.th_inv hnM, hsd] at h2
  exact C.mem_pre.2 ⟨hnM, hD⟩

theorem not_conj_z4_z1 [Finite G] (g : G) : g * C.elt z4 * g⁻¹ ≠ C.elt z1 := by
  intro h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT⟩ := C.exists_sylow_eq hrig
  have hx : C.elt z4 ∈ Subgroup.centralizer ((T : Subgroup G) : Set G) := by
    rw [hT]; exact C.elt_mem_centralizer_S D8_fixes_z4
  have hy : g⁻¹⁻¹ * C.elt z4 * g⁻¹ ∈ Subgroup.centralizer ((T : Subgroup G) : Set G) := by
    rw [hT, inv_inv, h]; exact C.elt_mem_centralizer_S D8_fixes_z1
  obtain ⟨n, hn, hn'⟩ := T.conj_eq_normalizer_conj_of_mem_centralizer (C.elt z4) g⁻¹ hx hy
  have hn2 : n ∈ Subgroup.normalizer ((C.pre D8 : Subgroup G) : Set G) := by
    rw [← hT]; exact hn
  have hnS := C.mem_of_mem_normalizer_S hrig hn2
  have h1 : n * C.elt z4 * n⁻¹ = C.elt z4 := C.S_fixes D8_fixes_z4 hnS
  have h2 : n⁻¹ * C.elt z4 * n = C.elt z4 := by
    have := C.S_fixes D8_fixes_z4 (Subgroup.inv_mem _ hnS)
    simpa using this
  rw [inv_inv, h, h2] at hn'
  exact z4_ne_z1 (C.elt_inj hn'.symm)

omit hrig in
theorem centralizer_eq_pre {v : Vec5} (hc : Subgroup.centralizer ({C.elt v} : Set G) ≤ M) :
    Subgroup.centralizer ({C.elt v} : Set G) = C.pre (stab v) := by
  ext x
  constructor
  · intro hx
    exact C.mem_pre.2 ⟨hc hx, mem_stab.2 ((C.mem_centralizer_elt_iff (hc hx) v).1 hx)⟩
  · intro hx
    exact (C.mem_centralizer_elt_iff (C.pre_le_M _ hx) v).2 (mem_stab.1 (C.th_mem_of_mem_pre hx))

omit hrig in
theorem not_conj_ones [Finite G] {w : Vec5} (hw0 : w ≠ 0) (hw5 : wt w ≠ 5)
    (hcw : Subgroup.centralizer ({C.elt w} : Set G) ≤ M) (g : G) :
    g * C.elt ones * g⁻¹ ≠ C.elt w := by
  intro h
  set r := C.elt ones with hr
  have hrM : ∀ m ∈ M, m * r * m⁻¹ = r := fun m hm => by
    rw [hr, C.conj_elt hm, permAct_ones]
  have h2 : ∀ m ∈ M, g * m * g⁻¹ ∈ M := fun m hm => by
    apply hcw
    apply mem_centralizer_of_conj_eq
    have h3 := hrM m hm
    calc g * m * g⁻¹ * C.elt w * (g * m * g⁻¹)⁻¹
        = g * (m * r * m⁻¹) * g⁻¹ := by rw [← h]; group
      _ = C.elt w := by rw [h3, h]
  have h3 : ∀ m ∈ M, g⁻¹ * m * g ∈ M := fun m hm => conj_inv_mem_of_conj_mem h2 hm
  have h4 : ∀ σ : Perm (Fin 5), permAct σ w = w := by
    intro σ
    obtain ⟨m, hm, hmσ⟩ := C.th_surj σ
    rw [← hmσ, ← C.mem_centralizer_elt_iff hm]
    apply mem_centralizer_of_conj_eq
    have h5 := hrM (g⁻¹ * m * g) (h3 m hm)
    calc m * C.elt w * m⁻¹ = g * ((g⁻¹ * m * g) * r * (g⁻¹ * m * g)⁻¹) * g⁻¹ := by
          rw [← h]; group
      _ = C.elt w := by rw [h5, h]
  rcases fixed_all w h4 with h5 | h5
  · exact hw0 h5
  · exact hw5 (by rw [h5]; exact wt_ones)

theorem fusion_ctrl [Finite G] {v w : Vec5}
    (hv : wt v = 1 ∨ wt v = 2 ∨ wt v = 4 ∨ wt v = 5)
    (hw : wt w = 1 ∨ wt w = 2 ∨ wt w = 4 ∨ wt w = 5)
    (hcv : Subgroup.centralizer ({C.elt v} : Set G) ≤ M)
    (hcw : Subgroup.centralizer ({C.elt w} : Set G) ≤ M) {g : G}
    (h : g * C.elt v * g⁻¹ = C.elt w) : g ∈ M := by
  have h0 : wt (0 : Vec5) = 0 := by decide
  have hv0 : v ≠ 0 := fun h0' => by rw [h0'] at hv; omega
  have hw0 : w ≠ 0 := fun h0' => by rw [h0'] at hw; omega
  by_cases hwt : wt v = wt w
  · obtain ⟨m, hm, hmv⟩ := C.exists_conj_of_wt_eq hwt
    have h1 : m⁻¹ * g ∈ Subgroup.centralizer ({C.elt v} : Set G) := by
      apply mem_centralizer_of_conj_eq
      calc m⁻¹ * g * C.elt v * (m⁻¹ * g)⁻¹ = m⁻¹ * (g * C.elt v * g⁻¹) * m := by group
        _ = C.elt v := by rw [h, ← hmv]; group
    have := M.mul_mem hm (hcv h1)
    simpa using this
  · by_cases h5v : wt v = 5
    · exfalso
      have hvo := eq_ones_of_wt_five v h5v
      subst hvo
      exact C.not_conj_ones hw0 (fun h5 => hwt (by omega)) hcw g h
    · by_cases h5w : wt w = 5
      · exfalso
        have hwo := eq_ones_of_wt_five w h5w
        subst hwo
        have h' : g⁻¹ * C.elt ones * g⁻¹⁻¹ = C.elt v := by
          rw [← h]; group
        exact C.not_conj_ones hv0 h5v hcv g⁻¹ h'
      · exfalso
        have hcases : (wt v = 1 ∧ wt w = 4) ∨ (wt v = 4 ∧ wt w = 1) ∨
            (wt v = 2 ∧ (wt w = 1 ∨ wt w = 4)) ∨ ((wt v = 1 ∨ wt v = 4) ∧ wt w = 2) := by
          omega
        rcases hcases with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩
        · obtain ⟨m₁, hm₁, h₁⟩ := C.exists_conj_of_wt_eq (v := z1) (w := v) (by rw [wt_z1, a])
          obtain ⟨m₂, hm₂, h₂⟩ := C.exists_conj_of_wt_eq (v := z4) (w := w) (by rw [wt_z4, b])
          have hx : (m₂⁻¹ * g * m₁) * C.elt z1 * (m₂⁻¹ * g * m₁)⁻¹ = C.elt z4 := by
            calc (m₂⁻¹ * g * m₁) * C.elt z1 * (m₂⁻¹ * g * m₁)⁻¹
                = m₂⁻¹ * (g * (m₁ * C.elt z1 * m₁⁻¹) * g⁻¹) * m₂ := by group
              _ = C.elt z4 := by rw [h₁, h, ← h₂]; group
          apply C.not_conj_z4_z1 hrig (m₂⁻¹ * g * m₁)⁻¹
          rw [← hx]
          group
        · obtain ⟨m₁, hm₁, h₁⟩ := C.exists_conj_of_wt_eq (v := z4) (w := v) (by rw [wt_z4, a])
          obtain ⟨m₂, hm₂, h₂⟩ := C.exists_conj_of_wt_eq (v := z1) (w := w) (by rw [wt_z1, b])
          apply C.not_conj_z4_z1 hrig (m₂⁻¹ * g * m₁)
          calc (m₂⁻¹ * g * m₁) * C.elt z4 * (m₂⁻¹ * g * m₁)⁻¹
              = m₂⁻¹ * (g * (m₁ * C.elt z4 * m₁⁻¹) * g⁻¹) * m₂ := by group
            _ = C.elt z1 := by rw [h₁, h, ← h₂]; group
        · have hcard : Nat.card (C.pre (stab v)) = Nat.card (C.pre (stab w)) := by
            rw [← C.centralizer_eq_pre hcv, ← C.centralizer_eq_pre hcw]
            exact card_centralizer_conj g h
          rw [C.card_pre, C.card_pre] at hcard
          have h12 : Nat.card (stab v) = 12 := card_stab_wt2 v a
          rcases b with b | b
          · have := card_stab_wt1 w b
            omega
          · have := card_stab_wt4 w b
            omega
        · have hcard : Nat.card (C.pre (stab v)) = Nat.card (C.pre (stab w)) := by
            rw [← C.centralizer_eq_pre hcv, ← C.centralizer_eq_pre hcw]
            exact card_centralizer_conj g h
          rw [C.card_pre, C.card_pre] at hcard
          have h12 : Nat.card (stab w) = 12 := card_stab_wt2 w b
          rcases a with a | a
          · have := card_stab_wt1 v a
            omega
          · have := card_stab_wt4 v a
            omega

theorem rig_fusion [Finite G] {v w : Vec5} (hv : Rigid v) (hw : Rigid w) {g : G}
    (h : g * C.elt v * g⁻¹ = C.elt w) : g ∈ M :=
  C.fusion_ctrl hrig (by rcases hv.2 with a | a | a <;> omega)
    (by rcases hw.2 with a | a | a <;> omega) (hrig v hv) (hrig w hw) h

end OrthCfg

end CFSG.CGT.PushingUpLit.Orth
