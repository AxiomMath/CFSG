module

import CFSG.Quasithin.Background.G11Bridge
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.Quasithin.Background.G11Defs
public import CFSG.RankThree.PartTwo.NotationBlocks

public section

namespace CFSG.CGT.Foote82.BranchAAux

open CFSG.Open CFSG.Quasithin.G11 CFSG.QuasithinUnique CFSG.RankThree.PartTwo

section Heart

variable {n : ℕ}

@[expose] def pt (hn : 4 ≤ n) (k : ℕ) (hk : k < 4 := by decide) : Fin n := ⟨k, by omega⟩

theorem pt_ne (hn : 4 ≤ n) {k l : ℕ} (hk : k < 4) (hl : l < 4) (hkl : k ≠ l) :
    pt hn k hk ≠ pt hn l hl := by
  simp [pt, Fin.ext_iff, hkl]

@[expose] def sigma0 (hn : 4 ≤ n) : Equiv.Perm (Fin n) :=
  Equiv.swap (pt hn 0) (pt hn 1) * Equiv.swap (pt hn 0) (pt hn 2)

theorem sigma0_isThreeCycle (hn : 4 ≤ n) : (sigma0 hn).IsThreeCycle :=
  Equiv.Perm.isThreeCycle_swap_mul_swap_same (pt_ne hn _ _ (by decide))
    (pt_ne hn _ _ (by decide)) (pt_ne hn _ _ (by decide))

@[expose] def vab (hn : 4 ≤ n) (a b : ZMod 2) : Fin n → ZMod 2 :=
  Pi.single (pt hn 0) a + Pi.single (pt hn 1) b + Pi.single (pt hn 2) (a + b)

private theorem zmod2_add_self : ∀ a : ZMod 2, a + a = 0 := by decide

theorem vab_apply_zero (hn : 4 ≤ n) (a b : ZMod 2) : vab hn a b (pt hn 0) = a := by
  simp [vab, Pi.single_apply, pt_ne hn (k := 0) (l := 1) (by decide) (by decide) (by decide),
    pt_ne hn (k := 0) (l := 2) (by decide) (by decide) (by decide)]

theorem vab_apply_one (hn : 4 ≤ n) (a b : ZMod 2) : vab hn a b (pt hn 1) = b := by
  simp [vab, Pi.single_apply, pt_ne hn (k := 1) (l := 0) (by decide) (by decide) (by decide),
    pt_ne hn (k := 1) (l := 2) (by decide) (by decide) (by decide)]

theorem vab_apply_two (hn : 4 ≤ n) (a b : ZMod 2) : vab hn a b (pt hn 2) = a + b := by
  simp [vab, Pi.single_apply, pt_ne hn (k := 2) (l := 0) (by decide) (by decide) (by decide),
    pt_ne hn (k := 2) (l := 1) (by decide) (by decide) (by decide)]

theorem vab_apply_of_ne (hn : 4 ≤ n) (a b : ZMod 2) {i : Fin n} (h0 : i ≠ pt hn 0)
    (h1 : i ≠ pt hn 1) (h2 : i ≠ pt hn 2) : vab hn a b i = 0 := by
  simp [vab, Pi.single_apply, h0, h1, h2]

theorem vab_mem (hn : 4 ≤ n) (a b : ZMod 2) : vab hn a b ∈ evenWeight n := by
  show ∑ i, vab hn a b i = 0
  simp only [vab, Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single', Finset.mem_univ,
    if_true]
  calc a + b + (a + b) = (a + a) + (b + b) := by ring
    _ = 0 := by rw [zmod2_add_self, zmod2_add_self, add_zero]

private theorem sigma0_inv (hn : 4 ≤ n) :
    (sigma0 hn)⁻¹ = Equiv.swap (pt hn 0) (pt hn 2) * Equiv.swap (pt hn 0) (pt hn 1) := by
  rw [sigma0, mul_inv_rev, Equiv.swap_inv, Equiv.swap_inv]

theorem evenWeightPerm_sigma0_sub (hn : 4 ≤ n) (y : evenWeight n) :
    ((evenWeightPerm (sigma0 hn) y - y : evenWeight n) : Fin n → ZMod 2) =
      vab hn ((y : Fin n → ZMod 2) (pt hn 0) + (y : Fin n → ZMod 2) (pt hn 1))
        ((y : Fin n → ZMod 2) (pt hn 1) + (y : Fin n → ZMod 2) (pt hn 2)) := by
  have h01 := pt_ne hn (k := 0) (l := 1) (by decide) (by decide) (by decide)
  have h02 := pt_ne hn (k := 0) (l := 2) (by decide) (by decide) (by decide)
  have h12 := pt_ne hn (k := 1) (l := 2) (by decide) (by decide) (by decide)
  have hsub : ∀ a b : ZMod 2, b - a = a + b := by decide
  have hsub' : ∀ a b c : ZMod 2, a - c = a + b + (b + c) := by decide
  funext i
  show (y : Fin n → ZMod 2) ((sigma0 hn)⁻¹ i) - (y : Fin n → ZMod 2) i = vab hn _ _ i
  rw [sigma0_inv, Equiv.Perm.mul_apply]
  by_cases hi0 : i = pt hn 0
  · subst hi0
    rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne h01.symm h12, vab_apply_zero]
    exact hsub _ _
  by_cases hi1 : i = pt hn 1
  · subst hi1
    rw [Equiv.swap_apply_right, Equiv.swap_apply_left, vab_apply_one]
    exact hsub _ _
  by_cases hi2 : i = pt hn 2
  · subst hi2
    rw [Equiv.swap_apply_of_ne_of_ne h02.symm h12.symm, Equiv.swap_apply_right, vab_apply_two]
    exact hsub' _ _ _
  rw [Equiv.swap_apply_of_ne_of_ne hi0 hi1, Equiv.swap_apply_of_ne_of_ne hi0 hi2,
    vab_apply_of_ne hn _ _ hi0 hi1 hi2, sub_self]

@[expose] def gab (hn : 4 ≤ n) (p : ZMod 2 × ZMod 2) : altHeart n :=
  ((⟨vab hn p.1 p.2, vab_mem hn p.1 p.2⟩ : evenWeight n) : altHeart n)

theorem gab_injective (hn : 4 ≤ n) : Function.Injective (gab hn) := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  have hmem := (QuotientAddGroup.eq).1 h
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.1 hmem
  have hk' : k • allOnes n = -vab hn a b + vab hn a' b' := hk
  have e3 := congrFun hk' (pt hn 3)
  have e0 := congrFun hk' (pt hn 0)
  have e1 := congrFun hk' (pt hn 1)
  have h30 := pt_ne hn (k := 3) (l := 0) (by decide) (by decide) (by decide)
  have h31 := pt_ne hn (k := 3) (l := 1) (by decide) (by decide) (by decide)
  have h32 := pt_ne hn (k := 3) (l := 2) (by decide) (by decide) (by decide)
  simp only [Pi.smul_apply, allOnes, Pi.add_apply, Pi.neg_apply] at e3 e0 e1
  rw [vab_apply_of_ne hn _ _ h30 h31 h32, vab_apply_of_ne hn _ _ h30 h31 h32] at e3
  rw [vab_apply_zero, vab_apply_zero] at e0
  rw [vab_apply_one, vab_apply_one] at e1
  have hk0 : k • (1 : ZMod 2) = 0 := e3.trans (by decide)
  rw [hk0] at e0 e1
  have ha : a = a' := neg_add_eq_zero.1 e0.symm
  have hb : b = b' := neg_add_eq_zero.1 e1.symm
  rw [ha, hb]

theorem range_sigma0_eq (hn : 4 ≤ n) :
    Set.range (fun y : evenWeight n =>
      ((evenWeightPerm (sigma0 hn) y - y : evenWeight n) : altHeart n)) =
      Set.range (gab hn) := by
  ext m
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨((y : Fin n → ZMod 2) (pt hn 0) + (y : Fin n → ZMod 2) (pt hn 1),
      (y : Fin n → ZMod 2) (pt hn 1) + (y : Fin n → ZMod 2) (pt hn 2)), ?_⟩
    show ((⟨_, _⟩ : evenWeight n) : altHeart n) = _
    congr 1
    exact Subtype.ext (evenWeightPerm_sigma0_sub hn y).symm
  · rintro ⟨⟨a, b⟩, rfl⟩
    let yv : Fin n → ZMod 2 :=
      Pi.single (pt hn 1) a + Pi.single (pt hn 2) (a + b) + Pi.single (pt hn 3) b
    have hy : yv ∈ evenWeight n := by
      show ∑ i, yv i = 0
      simp only [yv, Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single',
        Finset.mem_univ, if_true]
      calc a + (a + b) + b = (a + a) + (b + b) := by ring
        _ = 0 := by rw [zmod2_add_self, zmod2_add_self, add_zero]
    refine ⟨⟨yv, hy⟩, ?_⟩
    show ((⟨_, _⟩ : evenWeight n) : altHeart n) = gab hn (a, b)
    have h := evenWeightPerm_sigma0_sub hn ⟨yv, hy⟩
    dsimp only at h
    have h01 := pt_ne hn (k := 0) (l := 1) (by decide) (by decide) (by decide)
    have h02 := pt_ne hn (k := 0) (l := 2) (by decide) (by decide) (by decide)
    have h03 := pt_ne hn (k := 0) (l := 3) (by decide) (by decide) (by decide)
    have h12 := pt_ne hn (k := 1) (l := 2) (by decide) (by decide) (by decide)
    have h13 := pt_ne hn (k := 1) (l := 3) (by decide) (by decide) (by decide)
    have h23 := pt_ne hn (k := 2) (l := 3) (by decide) (by decide) (by decide)
    have y0 : yv (pt hn 0) = 0 := by
      simp [yv, Pi.single_apply, h01, h02, h03]
    have y1 : yv (pt hn 1) = a := by
      simp [yv, Pi.single_apply, h12, h13]
    have y2 : yv (pt hn 2) = a + b := by
      simp [yv, Pi.single_apply, h12.symm, h23]
    have hb2 : a + (a + b) = b := by
      rw [← add_assoc, zmod2_add_self, zero_add]
    rw [y0, y1, y2, zero_add, hb2] at h
    congr 1
    exact Subtype.ext h

theorem card_heart_range (hn : 4 ≤ n) :
    Nat.card (Set.range (fun y : evenWeight n =>
      ((evenWeightPerm (sigma0 hn) y - y : evenWeight n) : altHeart n))) = 4 := by
  rw [range_sigma0_eq hn, Nat.card_range_of_injective (gab_injective hn), Nat.card_prod,
    Nat.card_zmod]

end Heart

section Additivity

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

private theorem add_self_zero (w : V) : w + w = 0 := by
  rw [← two_smul (ZMod 2) w, show (2 : ZMod 2) = 0 from rfl, zero_smul]

theorem eq_zero_of_mem_range_of_fixed {x : GLV V} (hx3 : x ^ 3 = 1) {u : V}
    (hxv : x (x u - u) = x u - u) : x u - u = 0 := by
  have h3 : x (x (x u)) = u := by
    have := congrArg (fun f : GLV V => f u) hx3
    simpa [pow_succ, mul_assoc] using this
  have h2 : x (x u) = u := by
    rw [map_sub] at hxv
    have : x (x u) = x u + x u - u := by
      calc x (x u) = (x (x u) - x u) + x u := by abel
        _ = (x u - u) + x u := by rw [hxv]
        _ = x u + x u - u := by abel
    rw [this, add_self_zero, zero_sub]
    rw [← add_eq_zero_iff_neg_eq']
    exact add_self_zero u
  rw [h2] at h3
  rw [h3, sub_self]

theorem apply_mem_commSpace {L : Subgroup (GLV V)} {x : GLV V} (hx : x ∈ L) {w : V}
    (hw : w ∈ commSpace L ⊤) : x w ∈ commSpace L ⊤ := by
  have := (commSpace L ⊤).add_mem (sub_mem_commSpace hx (Submodule.mem_top (x := w))) hw
  rwa [sub_add_cancel] at this

@[expose] def actW {L : Subgroup (GLV V)} {x : GLV V} (hx : x ∈ L) (w : ↥(commSpace L ⊤)) :
    ↥(commSpace L ⊤) :=
  ⟨x w, apply_mem_commSpace hx w.2⟩

theorem card_commSpace_eq {L : Subgroup (GLV V)} {M : Type*} [AddGroup M]
    (β : ↥(commSpace L ⊤) →+ M)
    (hβk : β.ker = ((fixedSpace L).comap (commSpace L ⊤).subtype).toAddSubgroup)
    {x : GLV V} (hx : x ∈ L) (hx3 : x ^ 3 = 1) :
    Nat.card ↥(commSpace (Subgroup.zpowers x) ⊤) =
      Nat.card (Set.range (fun w : ↥(commSpace L ⊤) => β (actW hx w) - β w)) := by
  set D : V →ₗ[ZMod 2] V := (x : V →ₗ[ZMod 2] V) - LinearMap.id with hD
  have hDapp : ∀ v, D v = x v - v := fun v => by simp [hD]
  rw [commSpace_zpowers_top]
  have hRW : ∀ r ∈ LinearMap.range D, r ∈ commSpace L ⊤ := by
    rintro _ ⟨u, rfl⟩
    rw [hDapp]
    exact sub_mem_commSpace hx Submodule.mem_top
  have hinj : ∀ r ∈ LinearMap.range D, D r = 0 → r = 0 := by
    rintro _ ⟨u, rfl⟩ h0
    rw [hDapp] at h0 ⊢
    rw [hDapp, sub_eq_zero] at h0
    exact eq_zero_of_mem_range_of_fixed hx3 h0
  have hsurj : ∀ r ∈ LinearMap.range D, ∃ r' ∈ LinearMap.range D, D r' = r := by
    let f : ↥(LinearMap.range D) → ↥(LinearMap.range D) := fun r => ⟨D r, ⟨r, rfl⟩⟩
    have hf : Function.Injective f := by
      intro r₁ r₂ h
      have h' : D ((r₁ : V) - r₂) = 0 := by
        rw [map_sub, sub_eq_zero]
        exact congrArg Subtype.val h
      exact Subtype.ext (sub_eq_zero.1 (hinj _ (Submodule.sub_mem _ r₁.2 r₂.2) h'))
    intro r hr
    obtain ⟨r', hr'⟩ := (Finite.injective_iff_surjective.1 hf) ⟨r, hr⟩
    exact ⟨r', r'.2, congrArg Subtype.val hr'⟩
  let Φ : ↥(LinearMap.range D) → M := fun r => β ⟨r, hRW r r.2⟩
  have hΦ : Function.Injective Φ := by
    intro r₁ r₂ h
    have h0 : β (⟨r₁, hRW r₁ r₁.2⟩ - ⟨r₂, hRW r₂ r₂.2⟩) = 0 := by
      rw [map_sub, sub_eq_zero]
      exact h
    have hker : (⟨r₁, hRW r₁ r₁.2⟩ - ⟨r₂, hRW r₂ r₂.2⟩ : ↥(commSpace L ⊤)) ∈ β.ker := h0
    rw [hβk] at hker
    have hfix : ((r₁ : V) - r₂) ∈ fixedSpace L := hker
    have hD0 : D ((r₁ : V) - r₂) = 0 := by
      rw [hDapp, hfix x hx, sub_self]
    exact Subtype.ext (sub_eq_zero.1 (hinj _ (Submodule.sub_mem _ r₁.2 r₂.2) hD0))
  have hrange : Set.range Φ =
      Set.range (fun w : ↥(commSpace L ⊤) => β (actW hx w) - β w) := by
    ext m
    constructor
    · rintro ⟨r, rfl⟩
      obtain ⟨r', hr', hDr'⟩ := hsurj r r.2
      refine ⟨⟨r', hRW r' hr'⟩, ?_⟩
      show β (actW hx ⟨r', hRW r' hr'⟩) - β ⟨r', hRW r' hr'⟩ = β ⟨r, hRW r r.2⟩
      rw [← map_sub]
      refine congrArg β (Subtype.ext ?_)
      show x r' - r' = r
      rw [← hDapp, hDr']
    · rintro ⟨w, rfl⟩
      refine ⟨⟨D w, ⟨w, rfl⟩⟩, ?_⟩
      show β ⟨D w, _⟩ = β (actW hx w) - β w
      rw [← map_sub]
      exact congrArg β (Subtype.ext (hDapp w))
  rw [← hrange, Nat.card_range_of_injective hΦ]

theorem finrank_commSpace_eq_two {L : Subgroup (GLV V)} {n : ℕ} (hn : 4 ≤ n)
    (β : ↥(commSpace L ⊤) →+ altHeart n) (hβs : Function.Surjective β)
    (hβk : β.ker = ((fixedSpace L).comap (commSpace L ⊤).subtype).toAddSubgroup)
    {x : GLV V} (hx : x ∈ L) (hx3 : x ^ 3 = 1)
    (hxβ : ∀ w w' : ↥(commSpace L ⊤), (w' : V) = x w → ∀ y : evenWeight n,
      β w = (y : altHeart n) → β w' = (evenWeightPerm (sigma0 hn) y : altHeart n)) :
    Module.finrank (ZMod 2) ↥(commSpace (Subgroup.zpowers x) ⊤) = 2 := by
  have hcard := card_commSpace_eq (M := altHeart n) β hβk hx hx3
  have hT : Set.range (fun w : ↥(commSpace L ⊤) => β (actW hx w) - β w) =
      Set.range (fun y : evenWeight n =>
        ((evenWeightPerm (sigma0 hn) y - y : evenWeight n) : altHeart n)) := by
    ext m
    constructor
    · rintro ⟨w, rfl⟩
      obtain ⟨y, hy⟩ := QuotientAddGroup.mk_surjective (β w)
      refine ⟨y, ?_⟩
      show ((evenWeightPerm (sigma0 hn) y - y : evenWeight n) : altHeart n) =
        β (actW hx w) - β w
      rw [hxβ w (actW hx w) rfl y hy.symm, ← hy, QuotientAddGroup.mk_sub]
    · rintro ⟨y, rfl⟩
      obtain ⟨w, hw⟩ := hβs (y : altHeart n)
      refine ⟨w, ?_⟩
      show β (actW hx w) - β w =
        ((evenWeightPerm (sigma0 hn) y - y : evenWeight n) : altHeart n)
      rw [hxβ w (actW hx w) rfl y hw, hw, QuotientAddGroup.mk_sub]
  rw [hT, card_heart_range hn, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at hcard
  have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
  rw [h4] at hcard
  exact Nat.pow_right_injective (le_refl 2) hcard

end Additivity

end CFSG.CGT.Foote82.BranchAAux
