module

public import CFSG.CGT.Foote81L6.Basic

public section

namespace CFSG.CGT.Foote81L6

open Subgroup DihedralGroup

@[expose] def zpar (m : ℕ) (hm : 1 ≤ m) : ZMod (2 ^ m) →+* ZMod 2 :=
  ZMod.castHom (dvd_pow_self 2 (by omega)) (ZMod 2)

theorem zpar_natCast (m : ℕ) (hm : 1 ≤ m) (k : ℕ) : zpar m hm k = k := map_natCast _ k

theorem zpar_eq_zero_iff {m : ℕ} (hm : 1 ≤ m) {i : ZMod (2 ^ m)} :
    zpar m hm i = 0 ↔ ∃ c : ZMod (2 ^ m), i = c + c := by
  haveI : NeZero (2 ^ m) := ⟨by positivity⟩
  constructor
  · intro h
    have hv : zpar m hm (i.val : ZMod (2 ^ m)) = 0 := by rwa [ZMod.natCast_zmod_val]
    rw [zpar_natCast, ZMod.natCast_eq_zero_iff] at hv
    obtain ⟨c, hc⟩ := hv
    refine ⟨(c : ZMod (2 ^ m)), ?_⟩
    rw [← ZMod.natCast_zmod_val i, hc]
    push_cast
    ring
  · rintro ⟨c, rfl⟩
    rw [map_add]
    generalize zpar m hm c = u
    revert u
    decide

theorem zpar_eq_zero_of_mul_half {m : ℕ} (hm : 1 ≤ m) {i : ZMod (2 ^ m)}
    (h : i * ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) = 0) : zpar m hm i = 0 := by
  haveI : NeZero (2 ^ m) := ⟨by positivity⟩
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [Nat.add_sub_cancel] at h
  have h' : ((i.val * 2 ^ k : ℕ) : ZMod (2 ^ (k + 1))) = 0 := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val]
    exact h
  rw [ZMod.natCast_eq_zero_iff] at h'
  have h'' : 2 * 2 ^ k ∣ i.val * 2 ^ k := by rw [← pow_succ']; exact h'
  have h2 : 2 ∣ i.val := Nat.dvd_of_mul_dvd_mul_right (by positivity) h''
  rw [← ZMod.natCast_zmod_val i, zpar_natCast]
  exact (ZMod.natCast_eq_zero_iff _ _).2 h2

@[expose] def twistChar (m : ℕ) (hm : 1 ≤ m) (j₀ : ZMod (2 ^ m)) :
    DihedralGroup (2 ^ m) →* Multiplicative (ZMod 2) where
  toFun g := match g with
    | r i => Multiplicative.ofAdd (zpar m hm i)
    | sr i => Multiplicative.ofAdd (zpar m hm (i - j₀))
  map_one' := by
    rw [one_def]
    simp
  map_mul' g h := by
    rcases g with i | i <;> rcases h with j | j
    · rw [r_mul_r]
      show Multiplicative.ofAdd (zpar m hm (i + j)) =
        Multiplicative.ofAdd (zpar m hm i) * Multiplicative.ofAdd (zpar m hm j)
      rw [← ofAdd_add, map_add]
    · rw [r_mul_sr]
      show Multiplicative.ofAdd (zpar m hm (j - i - j₀)) =
        Multiplicative.ofAdd (zpar m hm i) * Multiplicative.ofAdd (zpar m hm (j - j₀))
      rw [← ofAdd_add, map_sub, map_sub, map_sub]
      congr 1
      generalize zpar m hm i = u
      generalize zpar m hm j = v
      generalize zpar m hm j₀ = w
      revert u v w
      decide
    · rw [sr_mul_r]
      show Multiplicative.ofAdd (zpar m hm (i + j - j₀)) =
        Multiplicative.ofAdd (zpar m hm (i - j₀)) * Multiplicative.ofAdd (zpar m hm j)
      rw [← ofAdd_add, map_sub, map_sub, map_add]
      congr 1
      generalize zpar m hm i = u
      generalize zpar m hm j = v
      generalize zpar m hm j₀ = w
      revert u v w
      decide
    · rw [sr_mul_sr]
      show Multiplicative.ofAdd (zpar m hm (j - i)) =
        Multiplicative.ofAdd (zpar m hm (i - j₀)) * Multiplicative.ofAdd (zpar m hm (j - j₀))
      rw [← ofAdd_add, map_sub, map_sub, map_sub]
      congr 1
      generalize zpar m hm i = u
      generalize zpar m hm j = v
      generalize zpar m hm j₀ = w
      revert u v w
      decide

@[simp] theorem twistChar_r (m : ℕ) (hm : 1 ≤ m) (j₀ i : ZMod (2 ^ m)) :
    twistChar m hm j₀ (r i) = Multiplicative.ofAdd (zpar m hm i) := rfl

@[simp] theorem twistChar_sr (m : ℕ) (hm : 1 ≤ m) (j₀ i : ZMod (2 ^ m)) :
    twistChar m hm j₀ (sr i) = Multiplicative.ofAdd (zpar m hm (i - j₀)) := rfl

namespace FooteCore

variable {G : Type*} [Group G] {T : Subgroup G} {m n : ℕ} (D : FooteCore G T m n)

noncomputable def eAt : ↥(D.A ⊔ zpowers D.t) ≃* DihedralGroup (2 ^ m) := D.At_iso.some

noncomputable def jt : ZMod (2 ^ m) := (D.At_iso_apply_t D.eAt).choose

theorem eAt_t : D.eAt ⟨D.t, mem_sup_right (mem_zpowers _)⟩ = sr D.jt :=
  (D.At_iso_apply_t D.eAt).choose_spec

theorem eAt_a : D.eAt ⟨D.a, mem_sup_left D.a_mem⟩ = zc m := D.At_iso_apply_a D.eAt

theorem eAt_a_eq : D.eAt ⟨D.a, mem_sup_left D.a_mem⟩ = r ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) := by
  rw [D.eAt_a]
  obtain ⟨k, hk⟩ : ∃ k, m = k + 1 := ⟨m - 1, by have := D.one_le_m; omega⟩
  subst hk
  rw [Nat.add_sub_cancel, ← rho_pow (by omega : 1 ≤ k + 1), r_pow, one_mul, Nat.add_sub_cancel]

theorem zpar_of_eAt_r {x : ↥(D.A ⊔ zpowers D.t)} (hx : (x : G) ∈ D.A) {i : ZMod (2 ^ m)}
    (hi : D.eAt x = r i) : zpar m D.one_le_m i = 0 := by
  obtain ⟨eA⟩ := D.A_iso
  have h1 : (x : G) ^ (2 ^ (m - 1)) = 1 := by
    have := pow_two_pow_eq_one (a := m - 1) (b := m - 1) (by have := D.two_le_m; omega) le_rfl
      (eA ⟨x, hx⟩)
    rw [← map_pow, ← eA.map_one] at this
    have := congrArg Subtype.val (eA.injective this)
    simpa using this
  have h2 : x ^ (2 ^ (m - 1)) = 1 := Subtype.ext (by simpa using h1)
  have h3 : (r i : DihedralGroup (2 ^ m)) ^ (2 ^ (m - 1)) = 1 := by
    rw [← hi, ← map_pow, h2, map_one]
  rw [r_pow, ← r_zero] at h3
  exact zpar_eq_zero_of_mul_half D.one_le_m (by exact_mod_cast r.inj h3)

theorem eAt_symm_r_double_mem (c : ZMod (2 ^ m)) : ((D.eAt.symm (r (c + c)) : G)) ∈ D.A := by
  have h : D.eAt.symm (r (c + c)) = D.eAt.symm (r c) * D.eAt.symm (r c) := by
    rw [← map_mul, r_mul_r]
  rw [h, Subgroup.coe_mul]
  exact D.mul_self_mem_A_of_mem_At (D.eAt.symm (r c)).2

theorem zpar_of_eAt_sr {x : ↥(D.A ⊔ zpowers D.t)} (hx : (x : G) ∈ D.A) {i : ZMod (2 ^ m)}
    (hi : D.eAt x = sr i) : zpar m D.one_le_m (i - D.jt) = 1 := by
  have h01 : ∀ u : ZMod 2, u = 0 ∨ u = 1 := by decide
  rcases h01 (zpar m D.one_le_m (i - D.jt)) with h0 | h1
  · exfalso
    have h0' : zpar m D.one_le_m (D.jt - i) = 0 := by
      rw [show D.jt - i = -(i - D.jt) by ring, map_neg, h0]
      decide
    obtain ⟨c, hc⟩ := (zpar_eq_zero_iff D.one_le_m).1 h0'
    have hy := D.eAt_symm_r_double_mem c
    apply D.t_not_mem_A
    have he : D.eAt (x * D.eAt.symm (r (c + c))) = D.eAt ⟨D.t, mem_sup_right (mem_zpowers _)⟩ := by
      rw [map_mul, MulEquiv.apply_symm_apply, hi, sr_mul_r, D.eAt_t, ← hc]
      congr 1
      ring
    have := congrArg Subtype.val (D.eAt.injective he)
    simp only [Subgroup.coe_mul] at this
    rw [← this]
    exact mul_mem hx hy
  · exact h1

theorem mem_A_iff_eAt (g : ↥(D.A ⊔ zpowers D.t)) :
    (g : G) ∈ D.A ↔ (∃ i, D.eAt g = r i ∧ zpar m D.one_le_m i = 0) ∨
      (∃ i, D.eAt g = sr i ∧ zpar m D.one_le_m (i - D.jt) = 1) := by
  constructor
  · intro hg
    rcases h : D.eAt g with i | i
    · exact Or.inl ⟨i, rfl, D.zpar_of_eAt_r hg h⟩
    · exact Or.inr ⟨i, rfl, D.zpar_of_eAt_sr hg h⟩
  · rintro (⟨i, hi, hpar⟩ | ⟨i, hi, hpar⟩)
    · obtain ⟨c, rfl⟩ := (zpar_eq_zero_iff D.one_le_m).1 hpar
      have : g = D.eAt.symm (r (c + c)) := by rw [← hi, MulEquiv.symm_apply_apply]
      rw [this]
      exact D.eAt_symm_r_double_mem c
    · rcases D.mem_At_iff.1 g.2 with h | h
      · exact h
      · exfalso
        have hgt : (g : G) * D.t = ((g * ⟨D.t, mem_sup_right (mem_zpowers _)⟩ :
            ↥(D.A ⊔ zpowers D.t)) : G) := rfl
        rw [hgt] at h
        have hr : D.eAt (g * ⟨D.t, mem_sup_right (mem_zpowers _)⟩) = r (D.jt - i) := by
          rw [map_mul, hi, D.eAt_t, sr_mul_sr]
        have := D.zpar_of_eAt_r h hr
        rw [show D.jt - i = -(i - D.jt) by ring, map_neg, hpar] at this
        exact absurd this (by decide)

@[expose] def bHom : Multiplicative (ZMod 2) →* G where
  toFun u := if Multiplicative.toAdd u = 0 then 1 else D.b
  map_one' := by simp
  map_mul' u v := by
    have h01 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
    rcases h01 (Multiplicative.toAdd u) with hu | hu <;>
      rcases h01 (Multiplicative.toAdd v) with hv | hv <;>
      simp [hu, hv, D.b_mul_b, show (1 : ZMod 2) + 1 = 0 by decide]

theorem bHom_comm_T (u : Multiplicative (ZMod 2)) {x : G} (hx : x ∈ T) :
    x * D.bHom u = D.bHom u * x := by
  simp only [bHom, MonoidHom.coe_mk, OneHom.coe_mk]
  split_ifs
  · rw [mul_one, one_mul]
  · exact D.b_comm_T hx

theorem bHom_ofAdd_zero : D.bHom (Multiplicative.ofAdd 0) = 1 := by simp [bHom]

theorem bHom_ofAdd_one : D.bHom (Multiplicative.ofAdd 1) = D.b := by simp [bHom]

theorem bHom_mem (u : Multiplicative (ZMod 2)) : D.bHom u = 1 ∨ D.bHom u = D.b := by
  simp only [bHom, MonoidHom.coe_mk, OneHom.coe_mk]
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

@[expose] noncomputable def delta : ↥(D.A ⊔ zpowers D.t) →* Multiplicative (ZMod 2) :=
  (twistChar m D.one_le_m D.jt).comp D.eAt.toMonoidHom

theorem At_le_T : D.A ⊔ zpowers D.t ≤ T := sup_le D.A_le_T (zpowers_le.2 D.t_mem_T)

@[expose] noncomputable def starHom : ↥(D.A ⊔ zpowers D.t) →* G where
  toFun g := (g : G) * D.bHom (D.delta g)
  map_one' := by simp
  map_mul' g h := by
    simp only [Subgroup.coe_mul, map_mul]
    have hc := D.bHom_comm_T (D.delta g) (D.At_le_T h.2)
    calc (g : G) * h * (D.bHom (D.delta g) * D.bHom (D.delta h))
        = (g : G) * (h * D.bHom (D.delta g)) * D.bHom (D.delta h) := by group
      _ = (g : G) * (D.bHom (D.delta g) * h) * D.bHom (D.delta h) := by rw [hc]
      _ = (g : G) * D.bHom (D.delta g) * ((h : G) * D.bHom (D.delta h)) := by group

theorem starHom_apply (g : ↥(D.A ⊔ zpowers D.t)) :
    D.starHom g = (g : G) * D.bHom (D.delta g) := rfl

theorem starHom_t : D.starHom ⟨D.t, mem_sup_right (mem_zpowers _)⟩ = D.t := by
  rw [starHom_apply, delta, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, D.eAt_t,
    twistChar_sr, sub_self, map_zero, D.bHom_ofAdd_zero, mul_one]

theorem starHom_of_rot {g : ↥(D.A ⊔ zpowers D.t)} {i : ZMod (2 ^ m)} (hi : D.eAt g = r i)
    (hpar : zpar m D.one_le_m i = 0) : D.starHom g = g := by
  rw [starHom_apply, delta, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hi, twistChar_r, hpar,
    D.bHom_ofAdd_zero, mul_one]

theorem starHom_of_refl {g : ↥(D.A ⊔ zpowers D.t)} {i : ZMod (2 ^ m)} (hi : D.eAt g = sr i)
    (hpar : zpar m D.one_le_m (i - D.jt) = 1) : D.starHom g = g * D.b := by
  rw [starHom_apply, delta, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hi, twistChar_sr, hpar,
    D.bHom_ofAdd_one]

theorem b_not_mem_At : D.b ∉ D.A ⊔ zpowers D.t := by
  intro h
  rcases D.mem_At_iff.1 h with h | h
  · have : D.b ∈ D.A ⊓ D.B := mem_inf.2 ⟨h, D.b_mem_B⟩
    rw [D.A_inf_B, mem_bot] at this
    exact D.b_ne_one this
  · apply D.t_not_mem_T₀
    have : D.t = D.b⁻¹ * (D.b * D.t) := by group
    rw [this]
    exact mul_mem (mem_sup_right (inv_mem D.b_mem_B)) (mem_sup_left h)

theorem starHom_injective : Function.Injective D.starHom := by
  rw [injective_iff_map_eq_one]
  intro g hg
  rw [starHom_apply] at hg
  have hg' : (g : G) = (D.bHom (D.delta g))⁻¹ := eq_inv_of_mul_eq_one_left hg
  rcases D.bHom_mem (D.delta g) with h | h
  · rw [h, inv_one] at hg'
    exact Subtype.ext hg'
  · exfalso
    rw [h, inv_eq_of_mul_eq_one_right D.b_mul_b] at hg'
    exact D.b_not_mem_At (hg' ▸ g.2)

theorem eAt_sr_of_involution {x : ↥(D.A ⊔ zpowers D.t)} (hx : (x : G) ∈ D.A)
    (hx2 : orderOf (x : G) = 2) (hxa : (x : G) ≠ D.a) : ∃ i, D.eAt x = sr i := by
  rcases h : D.eAt x with i | i
  · exfalso
    obtain ⟨k, hk⟩ : ∃ k, m = k + 1 := ⟨m - 1, by have := D.one_le_m; omega⟩
    have hxx : (x : G) * x = 1 := by rw [← sq, ← hx2]; exact pow_orderOf_eq_one _
    have hxx' : x * x = 1 := Subtype.ext hxx
    have : (r i : DihedralGroup (2 ^ m)) * r i = 1 := by rw [← h, ← map_mul, hxx', map_one]
    rw [r_mul_r, ← r_zero] at this
    have hii : i + i = 0 := r.inj this
    subst hk
    rcases eq_zero_or_half hii with h0 | hh
    · have : x = 1 := D.eAt.injective (by rw [h, h0, r_zero, map_one])
      rw [this, OneMemClass.coe_one, orderOf_one] at hx2
      omega
    · apply hxa
      have : x = ⟨D.a, mem_sup_left D.a_mem⟩ :=
        D.eAt.injective (by rw [h, hh, D.eAt_a_eq, Nat.add_sub_cancel])
      rw [this]
  · exact ⟨i, rfl⟩

noncomputable abbrev Apart : Subgroup ↥(D.A ⊔ zpowers D.t) := D.A.subgroupOf (D.A ⊔ zpowers D.t)

theorem eAt_symm_sr_mem {v : ZMod (2 ^ m)} (hv : zpar m D.one_le_m (v - D.jt) = 1) :
    ((D.eAt.symm (sr v) : G)) ∈ D.A :=
  (D.mem_A_iff_eAt _).2 (Or.inr ⟨v, MulEquiv.apply_symm_apply _ _, hv⟩)

theorem orderOf_eAt_symm_sr (v : ZMod (2 ^ m)) : orderOf ((D.eAt.symm (sr v) : G)) = 2 := by
  rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, orderOf_sr]

theorem eAt_symm_sr_ne_a (v : ZMod (2 ^ m)) : ((D.eAt.symm (sr v) : G)) ≠ D.a := by
  intro h
  have : D.eAt.symm (sr v) = ⟨D.a, mem_sup_left D.a_mem⟩ := Subtype.ext h
  have h2 := congrArg D.eAt this
  rw [MulEquiv.apply_symm_apply, D.eAt_a_eq] at h2
  exact absurd h2 (by simp)

theorem Astar_eq_map : D.Astar = D.Apart.map D.starHom := by
  apply le_antisymm
  · rw [Astar, closure_le]
    rintro g ⟨x, hx, hx2, hxa, rfl⟩
    obtain ⟨i, hi⟩ := D.eAt_sr_of_involution (x := ⟨x, mem_sup_left hx⟩) hx hx2 hxa
    have hpar := D.zpar_of_eAt_sr (x := ⟨x, mem_sup_left hx⟩) hx hi
    exact ⟨⟨x, mem_sup_left hx⟩, mem_subgroupOf.2 hx, D.starHom_of_refl hi hpar⟩
  · rintro _ ⟨g, hg, rfl⟩
    replace hg : (g : G) ∈ D.A := mem_subgroupOf.1 hg
    have hgen : ∀ {v : ZMod (2 ^ m)}, zpar m D.one_le_m (v - D.jt) = 1 →
        ((D.eAt.symm (sr v) : G)) * D.b ∈ D.Astar := fun hv =>
      subset_closure ⟨_, D.eAt_symm_sr_mem hv, D.orderOf_eAt_symm_sr _, D.eAt_symm_sr_ne_a _, rfl⟩
    rcases (D.mem_A_iff_eAt g).1 hg with ⟨i, hi, hpar⟩ | ⟨i, hi, hpar⟩
    · rw [D.starHom_of_rot hi hpar]
      have hu : zpar m D.one_le_m ((D.jt + 1) - D.jt) = 1 := by
        rw [add_sub_cancel_left, map_one]
      have hu' : zpar m D.one_le_m ((D.jt + 1 + i) - D.jt) = 1 := by
        rw [show D.jt + 1 + i - D.jt = 1 + i by ring, map_add, map_one, hpar, add_zero]
      have hprod : g = D.eAt.symm (sr (D.jt + 1)) * D.eAt.symm (sr (D.jt + 1 + i)) := by
        apply D.eAt.injective
        rw [map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, sr_mul_sr, hi]
        congr 1
        ring
      have hmul := mul_mem (hgen hu) (hgen hu')
      have hy2T : ((D.eAt.symm (sr (D.jt + 1 + i)) : G)) ∈ T := D.At_le_T (D.eAt.symm _).2
      have hc := D.b_comm_T hy2T
      have e : ((D.eAt.symm (sr (D.jt + 1)) : G) * D.b) *
          ((D.eAt.symm (sr (D.jt + 1 + i)) : G) * D.b) = (g : G) := by
        rw [hprod, Subgroup.coe_mul]
        calc (D.eAt.symm (sr (D.jt + 1)) : G) * D.b * ((D.eAt.symm (sr (D.jt + 1 + i)) : G) * D.b)
            = (D.eAt.symm (sr (D.jt + 1)) : G) * (D.b * (D.eAt.symm (sr (D.jt + 1 + i)) : G)) *
                D.b := by group
          _ = (D.eAt.symm (sr (D.jt + 1)) : G) * ((D.eAt.symm (sr (D.jt + 1 + i)) : G) * D.b) *
                D.b := by rw [hc]
          _ = (D.eAt.symm (sr (D.jt + 1)) : G) * (D.eAt.symm (sr (D.jt + 1 + i)) : G) *
                (D.b * D.b) := by group
          _ = _ := by rw [D.b_mul_b, mul_one]
      rw [← e]
      exact hmul
    · rw [D.starHom_of_refl hi hpar]
      have : (g : G) = D.eAt.symm (sr i) := by rw [← hi, MulEquiv.symm_apply_apply]
      rw [this]
      exact hgen hpar

theorem mem_Apart_iff {g : ↥(D.A ⊔ zpowers D.t)} : g ∈ D.Apart ↔ (g : G) ∈ D.A := mem_subgroupOf

theorem starHom_mem_T₀ {g : ↥(D.A ⊔ zpowers D.t)} (hg : g ∈ D.Apart) : D.starHom g ∈ D.T₀ := by
  rw [starHom_apply]
  refine mul_mem (mem_sup_left (D.mem_Apart_iff.1 hg)) (mem_sup_right ?_)
  rcases D.bHom_mem (D.delta g) with h | h <;> rw [h]
  · exact one_mem _
  · exact D.b_mem_B

theorem Astar_le_T₀ : D.Astar ≤ D.T₀ := by
  rw [D.Astar_eq_map]
  rintro _ ⟨g, hg, rfl⟩
  exact D.starHom_mem_T₀ hg

theorem Astar_le_T : D.Astar ≤ T := D.Astar_le_T₀.trans D.T₀_le_T

theorem Astar_sup_B : D.Astar ⊔ D.B = D.A ⊔ D.B := by
  refine le_antisymm (sup_le D.Astar_le_T₀ le_sup_right) (sup_le (fun x hx => ?_) le_sup_right)
  have hg : (⟨x, mem_sup_left hx⟩ : ↥(D.A ⊔ zpowers D.t)) ∈ D.Apart := D.mem_Apart_iff.2 hx
  have hmem : D.starHom ⟨x, mem_sup_left hx⟩ ∈ D.Astar := by
    rw [D.Astar_eq_map]
    exact ⟨_, hg, rfl⟩
  have e : x = D.starHom ⟨x, mem_sup_left hx⟩ * (D.bHom (D.delta ⟨x, mem_sup_left hx⟩))⁻¹ := by
    rw [starHom_apply, mul_inv_cancel_right]
  rw [e]
  refine mul_mem (mem_sup_left hmem) (mem_sup_right (inv_mem ?_))
  rcases D.bHom_mem (D.delta ⟨x, mem_sup_left hx⟩) with h | h <;> rw [h]
  · exact one_mem _
  · exact D.b_mem_B

theorem Astar_inf_B : D.Astar ⊓ D.B = ⊥ := by
  rw [eq_bot_iff]
  rintro y ⟨hy, hyB⟩
  rw [D.Astar_eq_map] at hy
  obtain ⟨g, hg, rfl⟩ := hy
  rw [mem_bot]
  have hgB : (g : G) ∈ D.B := by
    have e : (g : G) = D.starHom g * (D.bHom (D.delta g))⁻¹ := by
      rw [starHom_apply, mul_inv_cancel_right]
    rw [e]
    refine mul_mem hyB (inv_mem ?_)
    rcases D.bHom_mem (D.delta g) with h | h <;> rw [h]
    · exact one_mem _
    · exact D.b_mem_B
  have h1 : (g : G) ∈ D.A ⊓ D.B := mem_inf.2 ⟨D.mem_Apart_iff.1 hg, hgB⟩
  rw [D.A_inf_B, mem_bot] at h1
  have : g = 1 := Subtype.ext h1
  rw [this, map_one]

theorem Astar_comm_B : ∀ x ∈ D.Astar, ∀ y ∈ D.B, x * y = y * x := by
  intro x hx y hy
  rw [D.Astar_eq_map] at hx
  obtain ⟨g, hg, rfl⟩ := hx
  rw [starHom_apply]
  have h1 := D.A_comm_B _ (D.mem_Apart_iff.1 hg) y hy
  have h2 := D.bHom_comm_T (D.delta g) (D.B_le_T hy)
  calc (g : G) * D.bHom (D.delta g) * y = (g : G) * (y * D.bHom (D.delta g)) := by
        rw [mul_assoc, h2]
    _ = y * ((g : G) * D.bHom (D.delta g)) := by rw [← mul_assoc, h1, mul_assoc]

theorem conj_t_Astar : ∀ x ∈ D.Astar, D.t * x * D.t⁻¹ ∈ D.Astar := by
  intro x hx
  rw [D.Astar_eq_map] at hx ⊢
  obtain ⟨g, hg, rfl⟩ := hx
  set t' : ↥(D.A ⊔ zpowers D.t) := ⟨D.t, mem_sup_right (mem_zpowers _)⟩
  refine ⟨t' * g * t'⁻¹, D.mem_Apart_iff.2 (D.conj_t_A _ (D.mem_Apart_iff.1 hg)), ?_⟩
  rw [map_mul, map_mul, map_inv, D.starHom_t]

theorem starHom_a : D.starHom ⟨D.a, mem_sup_left D.a_mem⟩ = D.a := by
  refine D.starHom_of_rot D.eAt_a_eq ?_
  rw [zpar_natCast]
  exact (ZMod.natCast_eq_zero_iff _ _).2 (dvd_pow_self 2 (by have := D.two_le_m; omega))

theorem a_mem_Astar : D.a ∈ D.Astar := by
  rw [D.Astar_eq_map]
  exact ⟨_, D.mem_Apart_iff.2 D.a_mem, D.starHom_a⟩

theorem starHom_range : D.starHom.range = D.Astar ⊔ zpowers D.t := by
  set t' : ↥(D.A ⊔ zpowers D.t) := ⟨D.t, mem_sup_right (mem_zpowers _)⟩
  have htop : D.Apart ⊔ zpowers t' = ⊤ := by
    refine eq_top_iff.2 fun g _ => ?_
    rcases D.mem_At_iff.1 g.2 with h | h
    · exact mem_sup_left (D.mem_Apart_iff.2 h)
    · have hgt : g * t' ∈ D.Apart := D.mem_Apart_iff.2 h
      have e : g = (g * t') * t'⁻¹ := by group
      rw [e]
      exact mul_mem (mem_sup_left hgt) (mem_sup_right (inv_mem (mem_zpowers _)))
  rw [MonoidHom.range_eq_map, ← htop, Subgroup.map_sup, MonoidHom.map_zpowers, D.starHom_t,
    ← D.Astar_eq_map]

theorem AstarT_le_T : D.Astar ⊔ zpowers D.t ≤ T :=
  sup_le D.Astar_le_T (zpowers_le.2 D.t_mem_T)

@[expose] noncomputable def star : FooteCore G T m n where
  A := D.Astar
  B := D.B
  B₀ := D.B₀
  B₁ := D.B₁
  t := D.t
  s := D.s
  a := D.a
  b₀ := D.b₀
  b₁ := D.b₁
  T_eq := by rw [D.Astar_sup_B]; exact D.T_eq
  A_inf_B := D.Astar_inf_B
  A_comm_B := D.Astar_comm_B
  conj_t_A := D.conj_t_Astar
  conj_t_B := D.conj_t_B
  t_sq := D.t_sq
  two_le_m := D.two_le_m
  A_iso := ⟨(MulEquiv.subgroupCongr D.Astar_eq_map).trans
    ((D.Apart.equivMapOfInjective D.starHom D.starHom_injective).symm.trans
      ((Subgroup.subgroupOfEquivOfLe le_sup_left).trans D.A_iso.some))⟩
  At_iso := ⟨(MulEquiv.subgroupCongr D.starHom_range.symm).trans
    ((MonoidHom.ofInjective D.starHom_injective).symm.trans D.eAt)⟩
  B_eq := D.B_eq
  B₀_inf_B₁ := D.B₀_inf_B₁
  B₀_comm_B₁ := D.B₀_comm_B₁
  m_lt_n := D.m_lt_n
  B₀_iso := D.B₀_iso
  B₁_iso := D.B₁_iso
  s_sq := D.s_sq
  conj_s_B₀ := D.conj_s_B₀
  Bt_conj := D.Bt_conj
  CBt_iso := D.CBt_iso
  a_mem := D.a_mem_Astar
  a_order := D.a_order
  a_comm := fun _ hx => D.a_comm_T (D.AstarT_le_T hx)
  b₀_mem := D.b₀_mem
  b₀_order := D.b₀_order
  b₀_comm := D.b₀_comm
  b₁_mem := D.b₁_mem
  b₁_order := D.b₁_order
  b₁_comm := D.b₁_comm

@[simp] theorem star_A : D.star.A = D.Astar := rfl
@[simp] theorem star_B : D.star.B = D.B := rfl
@[simp] theorem star_B₀ : D.star.B₀ = D.B₀ := rfl
@[simp] theorem star_B₁ : D.star.B₁ = D.B₁ := rfl
@[simp] theorem star_t : D.star.t = D.t := rfl
@[simp] theorem star_s : D.star.s = D.s := rfl
@[simp] theorem star_a : D.star.a = D.a := rfl
@[simp] theorem star_b₀ : D.star.b₀ = D.b₀ := rfl
@[simp] theorem star_b₁ : D.star.b₁ = D.b₁ := rfl
@[simp] theorem star_b : D.star.b = D.b := rfl
theorem exists_of_involution_Astar {y : G} (hy : y ∈ D.Astar) (hy2 : orderOf y = 2)
    (hya : y ≠ D.a) : ∃ x ∈ D.A, orderOf x = 2 ∧ x ≠ D.a ∧ y = x * D.b := by
  rw [D.Astar_eq_map] at hy
  obtain ⟨g, hg, rfl⟩ := hy
  have hgA := D.mem_Apart_iff.1 hg
  have hg2 : orderOf (g : G) = 2 := by
    rw [← hy2, Subgroup.orderOf_coe, ← orderOf_injective D.starHom D.starHom_injective g]
  have hga : (g : G) ≠ D.a := by
    intro h
    apply hya
    have : g = ⟨D.a, mem_sup_left D.a_mem⟩ := Subtype.ext h
    rw [this, D.starHom_a]
  obtain ⟨i, hi⟩ := D.eAt_sr_of_involution hgA hg2 hga
  exact ⟨g, hgA, hg2, hga, D.starHom_of_refl hi (D.zpar_of_eAt_sr hgA hi)⟩

theorem star_Astar : D.star.Astar = D.A := by
  apply le_antisymm
  · rw [Astar, closure_le]
    rintro g ⟨y, hy, hy2, hya, rfl⟩
    obtain ⟨x, hx, -, -, rfl⟩ := D.exists_of_involution_Astar hy hy2 hya
    show x * D.b * D.b ∈ D.A
    rw [mul_assoc, D.b_mul_b, mul_one]
    exact hx
  · intro x hx
    have hrefl : ∀ {v : ZMod (2 ^ m)}, zpar m D.one_le_m (v - D.jt) = 1 →
        ((D.eAt.symm (sr v) : G)) ∈ D.star.Astar := by
      intro v hv
      set y : ↥(D.A ⊔ zpowers D.t) := D.eAt.symm (sr v)
      have hyA : (y : G) ∈ D.A := D.eAt_symm_sr_mem hv
      have hsy : D.starHom y = y * D.b :=
        D.starHom_of_refl (MulEquiv.apply_symm_apply _ _) hv
      have hmem : (y : G) * D.b ∈ D.Astar := by
        rw [← hsy, D.Astar_eq_map]
        exact ⟨y, D.mem_Apart_iff.2 hyA, rfl⟩
      have hord : orderOf ((y : G) * D.b) = 2 := by
        rw [← hsy, orderOf_injective D.starHom D.starHom_injective y, ← Subgroup.orderOf_coe]
        exact D.orderOf_eAt_symm_sr v
      have hne : (y : G) * D.b ≠ D.a := by
        intro h
        apply D.eAt_symm_sr_ne_a v
        have h1 : D.starHom y = D.starHom ⟨D.a, mem_sup_left D.a_mem⟩ := by
          rw [hsy, D.starHom_a, h]
        exact congrArg Subtype.val (D.starHom_injective h1)
      have : (y : G) * D.b * D.star.b ∈ D.star.Astar :=
        subset_closure (show (y : G) * D.b * D.star.b ∈
          {g | ∃ x ∈ D.star.A, orderOf x = 2 ∧ x ≠ D.star.a ∧ g = x * D.star.b} from
          ⟨(y : G) * D.b, hmem, hord, hne, rfl⟩)
      show (y : G) ∈ D.star.Astar
      have e : (y : G) = (y : G) * D.b * D.star.b := by
        rw [star_b, mul_assoc, D.b_mul_b, mul_one]
      rw [e]
      exact this
    set g : ↥(D.A ⊔ zpowers D.t) := ⟨x, mem_sup_left hx⟩
    rcases (D.mem_A_iff_eAt g).1 hx with ⟨i, hi, hpar⟩ | ⟨i, hi, hpar⟩
    · have hu : zpar m D.one_le_m ((D.jt + 1) - D.jt) = 1 := by
        rw [add_sub_cancel_left, map_one]
      have hu' : zpar m D.one_le_m ((D.jt + 1 + i) - D.jt) = 1 := by
        rw [show D.jt + 1 + i - D.jt = 1 + i by ring, map_add, map_one, hpar, add_zero]
      have hprod : g = D.eAt.symm (sr (D.jt + 1)) * D.eAt.symm (sr (D.jt + 1 + i)) := by
        apply D.eAt.injective
        rw [map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, sr_mul_sr, hi]
        congr 1
        ring
      have hx' : x = ((D.eAt.symm (sr (D.jt + 1)) : G)) * D.eAt.symm (sr (D.jt + 1 + i)) := by
        have := congrArg Subtype.val hprod
        simpa using this
      rw [hx']
      exact mul_mem (hrefl hu) (hrefl hu')
    · have hx' : x = ((D.eAt.symm (sr i) : G)) := by
        have : g = D.eAt.symm (sr i) := by rw [← hi, MulEquiv.symm_apply_apply]
        exact congrArg Subtype.val this
      rw [hx']
      exact hrefl hpar

end FooteCore

end CFSG.CGT.Foote81L6
