module

public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Tactic.IntervalCases

public section

namespace CFSG.OddStandard.SmallF3.FritzII

private theorem fzrAux_card_mod3 {X : Type} [CommGroup X] [Finite X] (ρ : X →* X)
    (hρ3 : ∀ x : X, ρ (ρ (ρ x)) = x) (hfpf : ∀ x : X, ρ x = x → x = 1)
    {K : Subgroup X} (hK : ∀ k ∈ K, ρ k ∈ K) : Nat.card K % 3 = 1 := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  let f : Function.End K := fun k => ⟨ρ k, hK k k.2⟩
  have hf3 : f ^ 3 = 1 := by
    funext k
    apply Subtype.ext
    show ρ (ρ (ρ (k : X))) = (k : X)
    exact hρ3 k
  have hcardfix : Fintype.card (Function.fixedPoints f) = 1 := by
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨1, ?_⟩, ?_⟩
    · rw [Function.mem_fixedPoints_iff]; apply Subtype.ext; simp [f]
    · intro b
      apply Subtype.ext
      apply Subtype.ext
      have hb : f b.1 = b.1 := b.2
      have hb' : ρ (b.1 : X) = (b.1 : X) := by simpa [f] using congrArg Subtype.val hb
      exact hfpf b.1 hb'
  have hmod := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 3) (n := 1) hf3
  rw [hcardfix] at hmod
  rw [Nat.ModEq] at hmod
  rw [Nat.card_eq_fintype_card]
  simpa using hmod

private theorem fzrAux_inv_subgroup {X : Type} [CommGroup X] [Finite X] {Z : Subgroup X}
    (hZ4 : Nat.card Z = 4) (hX16 : Nat.card X = 16) (ρ : X →* X)
    (hρ3 : ∀ x : X, ρ (ρ (ρ x)) = x) (hfpf : ∀ x : X, ρ x = x → x = 1)
    {K : Subgroup X} (hZK : Z ≤ K) (hK : ∀ k ∈ K, ρ k ∈ K) : K = Z ∨ K = ⊤ := by
  have hcard16 : Nat.card K ∣ 16 := by
    rw [← hX16]; exact Subgroup.card_subgroup_dvd_card K
  have hcard4 : 4 ∣ Nat.card K := by
    rw [← hZ4]; exact Subgroup.card_dvd_of_le hZK
  have hmod : Nat.card K % 3 = 1 := fzrAux_card_mod3 ρ hρ3 hfpf hK
  obtain ⟨k, hk⟩ := hcard4
  have hk4 : k ∣ 4 := by
    obtain ⟨m, hm⟩ := hcard16
    refine ⟨m, ?_⟩
    have hm' : 16 = 4 * (k * m) := by rw [hk] at hm; exact hm.trans (by ring)
    have h44 : 4 * 4 = 4 * (k * m) := by rw [← hm']
    exact Nat.mul_left_cancel (by norm_num) h44
  have hk_le : k ≤ 4 := Nat.le_of_dvd (by norm_num) hk4
  have hkpos : 0 < k := by
    have hge : 4 ≤ Nat.card K := hZ4.symm.trans_le (Subgroup.card_le_of_le hZK)
    rw [hk] at hge; omega
  have hKcard : Nat.card K = 4 ∨ Nat.card K = 16 := by
    interval_cases k
    · left; rw [hk]
    · exfalso; rw [hk] at hmod; omega
    · exfalso; exact absurd hk4 (by norm_num)
    · right; rw [hk]
  rcases hKcard with hc | hc
  · left
    exact (Subgroup.eq_of_le_of_card_ge hZK (by rw [hZ4, hc])).symm
  · right
    exact Subgroup.eq_top_of_card_eq K (by rw [hX16, hc])

private theorem fzrAux_closure_Z {X : Type} [CommGroup X] [Finite X] {Z : Subgroup X}
    (hZ4 : Nat.card Z = 4) (ρ : X →* X) (hρ3 : ∀ x : X, ρ (ρ (ρ x)) = x)
    (hfpf : ∀ x : X, ρ x = x → x = 1) (hρZ : ∀ z ∈ Z, ρ z ∈ Z)
    {z : X} (hz : z ∈ Z) (hz1 : z ≠ 1) :
    ∀ y ∈ Z, y = 1 ∨ y = z ∨ y = ρ z ∨ y = ρ (ρ z) := by
  classical
  haveI : Fintype X := Fintype.ofFinite X
  have hρzZ : ρ z ∈ Z := hρZ z hz
  have hρρzZ : ρ (ρ z) ∈ Z := hρZ (ρ z) hρzZ
  have h1rz : ρ z ≠ 1 := by
    intro h
    have h' := hρ3 z
    rw [h, map_one, map_one] at h'
    exact hz1 h'.symm
  have h1rrz : ρ (ρ z) ≠ 1 := by
    intro h
    have h' := hρ3 z
    rw [h, map_one] at h'
    exact hz1 h'.symm
  have hzρz : z ≠ ρ z := fun h => hz1 (hfpf z h.symm)
  have hzρρz : z ≠ ρ (ρ z) := by
    intro h
    have hρz : ρ z = z := (congrArg ρ h).trans (hρ3 z)
    exact hz1 (hfpf z hρz)
  have hρzρρz : ρ z ≠ ρ (ρ z) := by
    intro h
    have hz_eq : ρ z = z := h.trans ((congrArg ρ h).trans (hρ3 z))
    exact hz1 (hfpf z hz_eq)
  have hTcard : ({1, z, ρ z, ρ (ρ z)} : Finset X).card = 4 :=
    Finset.card_eq_four.mpr
      ⟨1, z, ρ z, ρ (ρ z), Ne.symm hz1, Ne.symm h1rz, Ne.symm h1rrz,
        hzρz, hzρρz, hρzρρz, rfl⟩
  have hZcard : (Z : Set X).toFinset.card = 4 := by
    rw [Set.toFinset_card, ← Nat.card_eq_fintype_card]
    exact hZ4
  have hTsub : ({1, z, ρ z, ρ (ρ z)} : Finset X) ⊆ (Z : Set X).toFinset := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rw [Set.mem_toFinset]
    rcases ha with rfl | rfl | rfl | rfl
    · exact Z.one_mem
    · exact hz
    · exact hρzZ
    · exact hρρzZ
  have hTZ : ({1, z, ρ z, ρ (ρ z)} : Finset X) = (Z : Set X).toFinset :=
    Finset.eq_of_subset_of_card_le hTsub (by rw [hZcard, hTcard])
  intro y hy
  have hyT : y ∈ ({1, z, ρ z, ρ (ρ z)} : Finset X) := by
    rw [hTZ, Set.mem_toFinset]; exact hy
  simpa only [Finset.mem_insert, Finset.mem_singleton] using hyT

theorem fzr_B_core {X : Type} [CommGroup X] [Finite X] (hX2 : ∀ x : X, x * x = 1)
    (hX16 : Nat.card X = 16) {Z : Subgroup X} (hZ4 : Nat.card Z = 4)
    (ρ lam : X →* X) (hρ3 : ∀ x : X, ρ (ρ (ρ x)) = x) (hl2 : ∀ x : X, lam (lam x) = x)
    (hlρ : ∀ x : X, lam (ρ (lam x)) = ρ (ρ x)) (hfpf : ∀ x : X, ρ x = x → x = 1)
    (hρZ : ∀ z ∈ Z, ρ z ∈ Z) (hlZ : ∀ z ∈ Z, lam z ∈ Z) (hlmove : ∃ z ∈ Z, lam z ≠ z)
    (c d : X →* X) (hcZ : ∀ x : X, c x ∈ Z) (hdZ : ∀ x : X, d x ∈ Z)
    (hc0 : ∀ z ∈ Z, c z = 1) (hd0 : ∀ z ∈ Z, d z = 1)
    (hcρ : ∀ x : X, c (ρ x) = ρ (c x)) (hdρ : ∀ x : X, d (ρ x) = ρ (d x))
    (hcl : ∀ x : X, c (lam x) = lam (c x)) (hdl : ∀ x : X, d (lam x) = lam (d x))
    (hc : ∃ x : X, c x ≠ 1) :
    (∀ x : X, d x = 1) ∨ (∀ x : X, d x = c x) := by
  classical
  have hcZker : Z ≤ c.ker := by
    intro y hy
    rw [MonoidHom.mem_ker]
    exact hc0 y hy
  have hcρker : ∀ k ∈ c.ker, ρ k ∈ c.ker := by
    intro k hk
    rw [MonoidHom.mem_ker] at hk ⊢
    rw [hcρ, hk, map_one]
  have hcker : c.ker = Z := by
    rcases fzrAux_inv_subgroup hZ4 hX16 ρ hρ3 hfpf hcZker hcρker with h | h
    · exact h
    · exfalso
      obtain ⟨x, hx⟩ := hc
      exact hx (by
        have hxker : x ∈ c.ker := by rw [h]; trivial
        rwa [MonoidHom.mem_ker] at hxker)
  have hdZker : Z ≤ d.ker := by
    intro y hy
    rw [MonoidHom.mem_ker]
    exact hd0 y hy
  have hdρker : ∀ k ∈ d.ker, ρ k ∈ d.ker := by
    intro k hk
    rw [MonoidHom.mem_ker] at hk ⊢
    rw [hdρ, hk, map_one]
  rcases fzrAux_inv_subgroup hZ4 hX16 ρ hρ3 hfpf hdZker hdρker with hdkerZ | hdkerTop
  ·
    right
    have hZ_ne_top : Z ≠ ⊤ := by
      intro h
      rw [h, Subgroup.card_top, hX16] at hZ4
      omega
    obtain ⟨x₀, hx₀⟩ : ∃ x : X, x ∉ Z := by
      by_contra hcon
      push Not at hcon
      exact hZ_ne_top (le_antisymm le_top fun x _ => hcon x)
    have hc_ne : c x₀ ≠ 1 := by
      intro h
      have hxker : x₀ ∈ c.ker := by rw [MonoidHom.mem_ker]; exact h
      rw [hcker] at hxker
      exact hx₀ hxker
    have hd_ne : d x₀ ≠ 1 := by
      intro h
      have hxker : x₀ ∈ d.ker := by rw [MonoidHom.mem_ker]; exact h
      rw [hdkerZ] at hxker
      exact hx₀ hxker
    have hmem := fzrAux_closure_Z hZ4 ρ hρ3 hfpf hρZ (hcZ x₀) hc_ne (d x₀) (hdZ x₀)
    let A0 : Subgroup X :=
      { carrier := {x | d x = c x}
        one_mem' := by simp
        mul_mem' := by
          intro a b ha hb
          simp only [Set.mem_setOf_eq] at ha hb ⊢
          rw [map_mul, map_mul, ha, hb]
        inv_mem' := by
          intro a ha
          simp only [Set.mem_setOf_eq] at ha ⊢
          rw [map_inv, map_inv, ha] }
    let A1 : Subgroup X :=
      { carrier := {x | d x = ρ (c x)}
        one_mem' := by simp
        mul_mem' := by
          intro a b ha hb
          simp only [Set.mem_setOf_eq] at ha hb ⊢
          rw [map_mul, map_mul, map_mul, ha, hb]
        inv_mem' := by
          intro a ha
          simp only [Set.mem_setOf_eq] at ha ⊢
          rw [map_inv, map_inv, map_inv, ha] }
    let A2 : Subgroup X :=
      { carrier := {x | d x = ρ (ρ (c x))}
        one_mem' := by simp
        mul_mem' := by
          intro a b ha hb
          simp only [Set.mem_setOf_eq] at ha hb ⊢
          rw [map_mul, map_mul, map_mul, map_mul, ha, hb]
        inv_mem' := by
          intro a ha
          simp only [Set.mem_setOf_eq] at ha ⊢
          rw [map_inv, map_inv, map_inv, map_inv, ha] }
    have hZA0 : Z ≤ A0 := by
      intro y hy
      change d y = c y
      rw [hd0 y hy, hc0 y hy]
    have hZA1 : Z ≤ A1 := by
      intro y hy
      change d y = ρ (c y)
      rw [hd0 y hy, hc0 y hy, map_one]
    have hZA2 : Z ≤ A2 := by
      intro y hy
      change d y = ρ (ρ (c y))
      rw [hd0 y hy, hc0 y hy, map_one, map_one]
    have hρA0 : ∀ x ∈ A0, ρ x ∈ A0 := by
      intro x hx
      change d (ρ x) = c (ρ x)
      rw [hdρ, hcρ]
      exact congrArg ρ hx
    have hρA1 : ∀ x ∈ A1, ρ x ∈ A1 := by
      intro x hx
      change d (ρ x) = ρ (c (ρ x))
      rw [hdρ, hcρ]
      exact congrArg ρ hx
    have hρA2 : ∀ x ∈ A2, ρ x ∈ A2 := by
      intro x hx
      change d (ρ x) = ρ (ρ (c (ρ x)))
      rw [hdρ, hcρ]
      exact congrArg ρ hx
    have htop_of_mem : ∀ {A : Subgroup X}, Z ≤ A → (∀ x ∈ A, ρ x ∈ A) → x₀ ∈ A → A = ⊤ := by
      intro A hZA hρA hxA
      rcases fzrAux_inv_subgroup hZ4 hX16 ρ hρ3 hfpf hZA hρA with h | h
      · exfalso; rw [h] at hxA; exact hx₀ hxA
      · exact h
    have hxA : x₀ ∈ A0 ∨ x₀ ∈ A1 ∨ x₀ ∈ A2 := by
      rcases hmem with h | h | h | h
      · exact absurd h hd_ne
      · exact Or.inl (show x₀ ∈ A0 from h)
      · exact Or.inr (Or.inl (show x₀ ∈ A1 from h))
      · exact Or.inr (Or.inr (show x₀ ∈ A2 from h))
    have hI1 : ∀ t : X, ρ (lam t) = lam (ρ (ρ t)) := by
      intro t
      have h := congrArg lam (hlρ t)
      rw [hl2] at h
      exact h
    have hI2 : ∀ t : X, ρ (ρ (lam t)) = lam (ρ t) := by
      intro t
      calc ρ (ρ (lam t)) = ρ (lam (ρ (ρ t))) := by rw [hI1 t]
        _ = lam (ρ (ρ (ρ (ρ t)))) := by rw [hI1 (ρ (ρ t))]
        _ = lam (ρ t) := by rw [hρ3 (ρ t)]
    rcases hxA with hxA0 | hxA1 | hxA2
    ·
      intro x
      have htop : A0 = ⊤ := htop_of_mem hZA0 hρA0 hxA0
      have hx : x ∈ A0 := by rw [htop]; trivial
      exact hx
    ·
      exfalso
      have htop : A1 = ⊤ := htop_of_mem hZA1 hρA1 hxA1
      have hdx : ∀ x, d x = ρ (c x) := by
        intro x
        have hx : x ∈ A1 := by rw [htop]; trivial
        exact hx
      have hcontra : lam (ρ (c x₀)) = lam (ρ (ρ (c x₀))) := by
        calc lam (ρ (c x₀)) = lam (d x₀) := by rw [hdx x₀]
          _ = d (lam x₀) := (hdl x₀).symm
          _ = ρ (c (lam x₀)) := hdx (lam x₀)
          _ = ρ (lam (c x₀)) := by rw [hcl x₀]
          _ = lam (ρ (ρ (c x₀))) := hI1 (c x₀)
      have hρeq : ρ (c x₀) = ρ (ρ (c x₀)) := by
        have h := congrArg lam hcontra
        rwa [hl2, hl2] at h
      have hy_eq : ρ (c x₀) = c x₀ := by
        have h : ρ (ρ (c x₀)) = c x₀ := by
          have h' := congrArg ρ hρeq
          rwa [hρ3 (c x₀)] at h'
        exact hρeq.trans h
      exact hc_ne (hfpf (c x₀) hy_eq)
    ·
      exfalso
      have htop : A2 = ⊤ := htop_of_mem hZA2 hρA2 hxA2
      have hdx : ∀ x, d x = ρ (ρ (c x)) := by
        intro x
        have hx : x ∈ A2 := by rw [htop]; trivial
        exact hx
      have hcontra : lam (ρ (ρ (c x₀))) = lam (ρ (c x₀)) := by
        calc lam (ρ (ρ (c x₀))) = lam (d x₀) := by rw [hdx x₀]
          _ = d (lam x₀) := (hdl x₀).symm
          _ = ρ (ρ (c (lam x₀))) := hdx (lam x₀)
          _ = ρ (ρ (lam (c x₀))) := by rw [hcl x₀]
          _ = lam (ρ (c x₀)) := hI2 (c x₀)
      have hρeq : ρ (ρ (c x₀)) = ρ (c x₀) := by
        have h := congrArg lam hcontra
        rwa [hl2, hl2] at h
      have hy_eq : ρ (c x₀) = c x₀ := by
        have h1 : c x₀ = ρ (ρ (c x₀)) := by
          have h := congrArg ρ hρeq
          rwa [hρ3 (c x₀)] at h
        exact (h1.trans hρeq).symm
      exact hc_ne (hfpf (c x₀) hy_eq)
  ·
    left
    intro x
    have hx : x ∈ d.ker := by rw [hdkerTop]; trivial
    rwa [MonoidHom.mem_ker] at hx

end CFSG.OddStandard.SmallF3.FritzII
