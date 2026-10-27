module

public import Certificates.Certificate4138

public section

set_option maxRecDepth 100000

namespace CFSG.QuasithinUnique.Setup.X3

open Equiv CFSG.QuasithinUnique

section Generic

theorem mem_relStab {n : ℕ} {b : Fin n → ℕ} {σ : Perm (Fin n)} :
    σ ∈ relStab b ↔ ∀ i j, b i = b j ↔ b (σ i) = b (σ j) := Iff.rfl

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem top_of_adjacent_swaps {m : ℕ} {G : Subgroup (Perm (Fin (m + 1)))}
    (h : ∀ i : Fin m, swap i.castSucc i.succ ∈ G) : G = ⊤ := by
  rw [eq_top_iff]
  intro σ _
  have hσ : σ ∈ Submonoid.closure (Set.range fun i : Fin m => swap i.castSucc i.succ) := by
    rw [Perm.mclosure_swap_castSucc_succ m]
    trivial
  refine (Submonoid.closure_le (S := G.toSubmonoid)).mpr ?_ hσ
  rintro _ ⟨i, rfl⟩
  exact h i

omit [Fintype α] in
theorem swap_apply_mem_of_mem {G : Subgroup (Perm α)} {σ : Perm α} (hσ : σ ∈ G) {a b : α}
    (h : swap a b ∈ G) : swap (σ a) (σ b) ∈ G := by
  rw [swap_apply_apply]
  exact G.mul_mem (G.mul_mem hσ h) (G.inv_mem hσ)

theorem card_eq_two_mul_card_inf_alt {K : Subgroup (Perm α)} {s : Perm α} (hsK : s ∈ K)
    (hs : Perm.sign s = -1) : Nat.card K = 2 * Nat.card ↥(K ⊓ alternatingGroup α) := by
  have h2 : (alternatingGroup α).relIndex K = 2 := by
    refine Subgroup.relIndex_eq_two_iff.mpr ⟨s, hsK, fun b hb => ?_⟩
    rcases Int.units_eq_one_or (Perm.sign b) with h1 | h1
    · refine Or.inr ⟨Perm.mem_alternatingGroup.mpr h1, fun hmem => ?_⟩
      rw [Perm.mem_alternatingGroup, map_mul, h1, hs] at hmem
      exact absurd hmem (by decide)
    · refine Or.inl ⟨?_, fun hmem => ?_⟩
      · rw [Perm.mem_alternatingGroup, map_mul, h1, hs]
        rfl
      · rw [Perm.mem_alternatingGroup, h1] at hmem
        exact absurd hmem (by decide)
  have h3 := Subgroup.relIndex_mul_card (alternatingGroup α) K
  rw [h2, inf_comm] at h3
  omega

end Generic

section Case

variable {n : ℕ}

theorem two_gen_perm_case (h5 : 5 ≤ n) (X Y : Subgroup (Perm (Fin n))) (a b c : Fin n)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hsX : swap a b ∈ X) (hsY : swap a b ∈ Y) (hcX : swap a b * swap a c ∈ X)
    (hXYtop : X ⊔ Y = ⊤)
    {xS yS xA yA : Perm (Fin n)} (hxS : xS ∉ X) (hyS : yS ∉ Y)
    (hxA : xA ∈ alternatingGroup (Fin n)) (hxA' : xA ∉ X)
    (hyA : yA ∈ alternatingGroup (Fin n)) (hyA' : yA ∉ Y)
    {m q : ℕ} (hcard : Nat.card ↥(X ⊓ Y) = m) (hfac : n.factorial = m * q) (hq : ¬ 2 ∣ q)
    {D R : Subgroup (Perm (Fin n))} (hD : D = ⊤ ∨ D = alternatingGroup (Fin n))
    (hR : IsSylowTwoOf R D) :
    ∃ X' Y' : Subgroup (Perm (Fin n)), R ≤ X' ∧ R ≤ Y' ∧ X' < D ∧ Y' < D ∧ X' ⊔ Y' = D := by
  have hsgn : Perm.sign (swap a b) = -1 := Perm.sign_swap hab
  have hcardn : Nat.card (Perm (Fin n)) = n.factorial := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hmpos : 0 < m := by
    rw [← hcard]
    exact Nat.card_pos
  rcases hD with rfl | rfl
  · refine hasTwoGen_of_odd_index ?_ ?_ hXYtop ?_ hR
    · exact lt_top_iff_ne_top.mpr fun h => hxS (h ▸ Subgroup.mem_top xS)
    · exact lt_top_iff_ne_top.mpr fun h => hyS (h ▸ Subgroup.mem_top yS)
    · rw [Subgroup.relIndex_top_right]
      have h1 := Subgroup.card_mul_index (X ⊓ Y)
      rw [hcard, hcardn, hfac] at h1
      have h2 : (X ⊓ Y).index = q := Nat.eq_of_mul_eq_mul_left hmpos h1
      rwa [h2]
  · have hα : 5 ≤ Nat.card (Fin n) := by simpa using h5
    have hf3 : (swap a b * swap a c).IsThreeCycle :=
      Perm.isThreeCycle_swap_mul_swap_same hab hac hbc
    have hgenA : (X ⊓ alternatingGroup (Fin n)) ⊔ (Y ⊓ alternatingGroup (Fin n)) =
        alternatingGroup (Fin n) :=
      le_antisymm (sup_le inf_le_right inf_le_right)
        (alt_le_sup_of_common_odd hsX hsY hsgn hXYtop hα hf3 hcX)
    refine hasTwoGen_of_odd_index ?_ ?_ hgenA ?_ hR
    · refine lt_of_le_of_ne inf_le_right fun h => hxA' ?_
      have : xA ∈ X ⊓ alternatingGroup (Fin n) := by rw [h]; exact hxA
      exact this.1
    · refine lt_of_le_of_ne inf_le_right fun h => hyA' ?_
      have : yA ∈ Y ⊓ alternatingGroup (Fin n) := by rw [h]; exact hyA
      exact this.1
    · have hK : (X ⊓ alternatingGroup (Fin n)) ⊓ (Y ⊓ alternatingGroup (Fin n)) =
          (X ⊓ Y) ⊓ alternatingGroup (Fin n) := by
        ext x
        simp only [Subgroup.mem_inf]
        tauto
      rw [hK]
      have hle : (X ⊓ Y) ⊓ alternatingGroup (Fin n) ≤ alternatingGroup (Fin n) := inf_le_right
      have hm2 := card_eq_two_mul_card_inf_alt (K := X ⊓ Y) (s := swap a b) ⟨hsX, hsY⟩ hsgn
      have hKpos : 0 < Nat.card ↥((X ⊓ Y) ⊓ alternatingGroup (Fin n)) := Nat.card_pos
      have h1 := Subgroup.relIndex_mul_card ((X ⊓ Y) ⊓ alternatingGroup (Fin n))
        (alternatingGroup (Fin n))
      rw [inf_eq_left.mpr hle] at h1
      have hnt : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
      have h2 := Subgroup.card_mul_index (alternatingGroup (Fin n))
      rw [hcardn, alternatingGroup.index_eq_two] at h2
      rw [hcard] at hm2
      have h3 : Nat.card ↥(alternatingGroup (Fin n)) =
          Nat.card ↥((X ⊓ Y) ⊓ alternatingGroup (Fin n)) * q := by
        have : 2 * Nat.card ↥(alternatingGroup (Fin n)) =
            2 * (Nat.card ↥((X ⊓ Y) ⊓ alternatingGroup (Fin n)) * q) := by
          rw [mul_comm, h2, hfac, hm2]
          ring
        omega
      rw [h3, mul_comm] at h1
      have h4 : ((X ⊓ Y) ⊓ alternatingGroup (Fin n)).relIndex (alternatingGroup (Fin n)) = q :=
        Nat.eq_of_mul_eq_mul_left hKpos h1
      rwa [h4]

end Case


theorem mem_alt_swap_mul_swap {α : Type*} [Fintype α] [DecidableEq α] {a b c d : α} (hab : a ≠ b)
    (hcd : c ≠ d) : swap a b * swap c d ∈ alternatingGroup α := by
  rw [Perm.mem_alternatingGroup, map_mul, Perm.sign_swap hab, Perm.sign_swap hcd]
  rfl


section Case6

@[expose] def blkX6 (i : Fin 6) : ℕ := if i.val < 4 then 0 else 1

@[expose] def blkY6 (i : Fin 6) : ℕ := i.val / 2

theorem sup6 : relStab blkX6 ⊔ relStab blkY6 = ⊤ := by
  refine top_of_adjacent_swaps (m := 5) fun i => ?_
  have h01 : swap (0 : Fin 6) 1 ∈ relStab blkX6 ⊔ relStab blkY6 :=
    Subgroup.mem_sup_left (by decide +kernel)
  have h12 : swap (1 : Fin 6) 2 ∈ relStab blkX6 ⊔ relStab blkY6 :=
    Subgroup.mem_sup_left (by decide +kernel)
  have h23 : swap (2 : Fin 6) 3 ∈ relStab blkX6 ⊔ relStab blkY6 :=
    Subgroup.mem_sup_left (by decide +kernel)
  have h45 : swap (4 : Fin 6) 5 ∈ relStab blkX6 ⊔ relStab blkY6 :=
    Subgroup.mem_sup_left (by decide +kernel)
  have h13 : swap (1 : Fin 6) 3 ∈ relStab blkX6 ⊔ relStab blkY6 :=
    Subgroup.mem_sup_left (by decide +kernel)
  have hy : (swap (2 : Fin 6) 4 * swap 3 5 : Perm (Fin 6)) ∈ relStab blkX6 ⊔ relStab blkY6 :=
    Subgroup.mem_sup_right (by decide +kernel)
  have h14 : swap (1 : Fin 6) 4 ∈ relStab blkX6 ⊔ relStab blkY6 := by
    have h := swap_apply_mem_of_mem hy h12
    have e1 : (swap (2 : Fin 6) 4 * swap 3 5 : Perm (Fin 6)) 1 = 1 := by decide
    have e2 : (swap (2 : Fin 6) 4 * swap 3 5 : Perm (Fin 6)) 2 = 4 := by decide
    rwa [e1, e2] at h
  have h34 : swap (3 : Fin 6) 4 ∈ relStab blkX6 ⊔ relStab blkY6 := by
    have h := swap_apply_mem_of_mem h13 h14
    have e1 : (swap (1 : Fin 6) 3 : Perm (Fin 6)) 1 = 3 := by decide
    have e2 : (swap (1 : Fin 6) 3 : Perm (Fin 6)) 4 = 4 := by decide
    rwa [e1, e2] at h
  fin_cases i
  exacts [h01, h12, h23, h34, h45]

theorem card6 : Nat.card ↥(relStab blkX6 ⊓ relStab blkY6) = 16 := by
  have h : Fintype.card
      {σ : Perm (Fin 6) // σ ∈ relStab blkX6 ∧ σ ∈ relStab blkY6} = 16 := by
    decide +kernel
  rw [Nat.card_congr (Equiv.subtypeEquivRight fun σ => Subgroup.mem_inf),
    Nat.card_eq_fintype_card]
  exact h

theorem two_gen_6 {D R : Subgroup (Perm (Fin 6))}
    (hD : D = ⊤ ∨ D = alternatingGroup (Fin 6)) (hR : IsSylowTwoOf R D) :
    ∃ X' Y' : Subgroup (Perm (Fin 6)), R ≤ X' ∧ R ≤ Y' ∧ X' < D ∧ Y' < D ∧ X' ⊔ Y' = D :=
  two_gen_perm_case (by norm_num) (relStab blkX6) (relStab blkY6) 0 1 2
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) sup6
    (xS := swap 0 4) (yS := swap 1 2) (xA := swap 0 4 * swap 1 5) (yA := swap 1 2 * swap 3 4)
    (by decide +kernel) (by decide +kernel)
    (mem_alt_swap_mul_swap (by decide) (by decide)) (by decide +kernel)
    (mem_alt_swap_mul_swap (by decide) (by decide)) (by decide +kernel) card6
    (q := 45) (by decide +kernel) (by decide +kernel) hD hR

end Case6

section Case7

theorem sup7 : relStab blkX7 ⊔ relStab blkY7 = ⊤ := by
  refine top_of_adjacent_swaps (m := 6) fun i => ?_
  have h01 : swap (0 : Fin 7) 1 ∈ relStab blkX7 ⊔ relStab blkY7 :=
    Subgroup.mem_sup_left (by decide +kernel)
  have h12 : swap (1 : Fin 7) 2 ∈ relStab blkX7 ⊔ relStab blkY7 :=
    Subgroup.mem_sup_left (by decide +kernel)
  have h23 : swap (2 : Fin 7) 3 ∈ relStab blkX7 ⊔ relStab blkY7 :=
    Subgroup.mem_sup_left (by decide +kernel)
  have h34 : swap (3 : Fin 7) 4 ∈ relStab blkX7 ⊔ relStab blkY7 :=
    Subgroup.mem_sup_left (by decide +kernel)
  have h45 : swap (4 : Fin 7) 5 ∈ relStab blkX7 ⊔ relStab blkY7 :=
    Subgroup.mem_sup_left (by decide +kernel)
  have h56 : swap (5 : Fin 7) 6 ∈ relStab blkX7 ⊔ relStab blkY7 :=
    Subgroup.mem_sup_right (by decide +kernel)
  fin_cases i
  exacts [h01, h12, h23, h34, h45, h56]

theorem card7_h :
    Fintype.card
      {σ : Perm (Fin 7) // σ ∈ relStab blkX7 ∧ σ ∈ relStab blkY7} = 48 :=
  Certificates.certificate4138.1

end Case7

section Case8

theorem sup8 : relStab blkX8 ⊔ relStab blkY8 = ⊤ := by
  refine top_of_adjacent_swaps (m := 7) fun i => ?_
  have h01 : swap (0 : Fin 8) 1 ∈ relStab blkX8 ⊔ relStab blkY8 :=
    Subgroup.mem_sup_left (by decide +kernel)
  have h12 : swap (1 : Fin 8) 2 ∈ relStab blkX8 ⊔ relStab blkY8 :=
    Subgroup.mem_sup_left (by decide +kernel)
  have h23 : swap (2 : Fin 8) 3 ∈ relStab blkX8 ⊔ relStab blkY8 :=
    Subgroup.mem_sup_left (by decide +kernel)
  have h45 : swap (4 : Fin 8) 5 ∈ relStab blkX8 ⊔ relStab blkY8 :=
    Subgroup.mem_sup_left (by decide +kernel)
  have h56 : swap (5 : Fin 8) 6 ∈ relStab blkX8 ⊔ relStab blkY8 :=
    Subgroup.mem_sup_left (by decide +kernel)
  have h67 : swap (6 : Fin 8) 7 ∈ relStab blkX8 ⊔ relStab blkY8 :=
    Subgroup.mem_sup_left (by decide +kernel)
  have h13 : swap (1 : Fin 8) 3 ∈ relStab blkX8 ⊔ relStab blkY8 :=
    Subgroup.mem_sup_left (by decide +kernel)
  have hy : (swap (2 : Fin 8) 4 * swap 3 5 : Perm (Fin 8)) ∈ relStab blkX8 ⊔ relStab blkY8 :=
    Subgroup.mem_sup_right (by decide +kernel)
  have h14 : swap (1 : Fin 8) 4 ∈ relStab blkX8 ⊔ relStab blkY8 := by
    have h := swap_apply_mem_of_mem hy h12
    have e1 : (swap (2 : Fin 8) 4 * swap 3 5 : Perm (Fin 8)) 1 = 1 := by decide
    have e2 : (swap (2 : Fin 8) 4 * swap 3 5 : Perm (Fin 8)) 2 = 4 := by decide
    rwa [e1, e2] at h
  have h34 : swap (3 : Fin 8) 4 ∈ relStab blkX8 ⊔ relStab blkY8 := by
    have h := swap_apply_mem_of_mem h13 h14
    have e1 : (swap (1 : Fin 8) 3 : Perm (Fin 8)) 1 = 3 := by decide
    have e2 : (swap (1 : Fin 8) 3 : Perm (Fin 8)) 4 = 4 := by decide
    rwa [e1, e2] at h
  fin_cases i
  exacts [h01, h12, h23, h34, h45, h56, h67]

theorem card8_h :
    Fintype.card
      {σ : Perm (Fin 8) // σ ∈ relStab blkX8 ∧ σ ∈ relStab blkY8} = 128 :=
  Certificates.certificate4138.2

end Case8

section Abstract

variable {Γ Γ' : Type*} [Group Γ] [Group Γ']

theorem two_gen_of_map_injective {φ : Γ →* Γ'} (hφ : Function.Injective φ) {T : Subgroup Γ}
    {X' Y' : Subgroup Γ'} (hTX : T.map φ ≤ X') (hTY : T.map φ ≤ Y') (hX : X' < φ.range)
    (hY : Y' < φ.range) (hgen : X' ⊔ Y' = φ.range) :
    ∃ X Y : Subgroup Γ, T ≤ X ∧ T ≤ Y ∧ X < ⊤ ∧ Y < ⊤ ∧ X ⊔ Y = ⊤ := by
  have hprop : ∀ Z : Subgroup Γ', Z < φ.range → Z.comap φ < ⊤ := by
    intro Z hZ
    refine lt_top_iff_ne_top.mpr fun h => ?_
    have : φ.range ≤ Z := by
      rintro _ ⟨g, rfl⟩
      have hg : g ∈ Z.comap φ := h ▸ Subgroup.mem_top g
      exact hg
    exact not_le_of_gt hZ this
  refine ⟨X'.comap φ, Y'.comap φ, Subgroup.map_le_iff_le_comap.mp hTX,
    Subgroup.map_le_iff_le_comap.mp hTY, hprop X' hX, hprop Y' hY, ?_⟩
  apply Subgroup.map_injective hφ
  rw [Subgroup.map_sup, Subgroup.map_comap_eq, Subgroup.map_comap_eq,
    inf_eq_right.mpr hX.le, inf_eq_right.mpr hY.le, hgen, ← MonoidHom.range_eq_map]

@[expose] def TwoGenPerm (n : ℕ) : Prop :=
  ∀ {D R : Subgroup (Perm (Fin n))}, (D = ⊤ ∨ D = alternatingGroup (Fin n)) →
    IsSylowTwoOf R D → ∃ X' Y' : Subgroup (Perm (Fin n)), R ≤ X' ∧ R ≤ Y' ∧ X' < D ∧ Y' < D ∧
      X' ⊔ Y' = D

theorem twoGenPerm_six : TwoGenPerm 6 := fun hD hR => two_gen_6 hD hR

theorem two_generating_overgroups_of_iso {n : ℕ} (h : TwoGenPerm n)
    (hΓ : Nonempty (Γ ≃* Perm (Fin n)) ∨ Nonempty (Γ ≃* alternatingGroup (Fin n)))
    {T : Subgroup Γ} (hT : IsSylowTwoOf T ⊤) :
    ∃ X Y : Subgroup Γ, T ≤ X ∧ T ≤ Y ∧ X < ⊤ ∧ Y < ⊤ ∧ X ⊔ Y = ⊤ := by
  obtain ⟨φ, hφ, hrange⟩ : ∃ φ : Γ →* Perm (Fin n), Function.Injective φ ∧
      (φ.range = ⊤ ∨ φ.range = alternatingGroup (Fin n)) := by
    rcases hΓ with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · exact ⟨e.toMonoidHom, e.injective, Or.inl (MonoidHom.range_eq_top.mpr e.surjective)⟩
    · refine ⟨(alternatingGroup (Fin n)).subtype.comp e.toMonoidHom,
        (alternatingGroup (Fin n)).subtype_injective.comp e.injective, Or.inr ?_⟩
      rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr e.surjective, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype]
  have : Finite Γ := Finite.of_injective φ hφ
  have hS := CFSG.QuasithinUnique.Setup.X35.isSylowTwoOf_map_of_injective hφ hT
  rw [← MonoidHom.range_eq_map] at hS
  obtain ⟨X', Y', hRX, hRY, hX, hY, hgen⟩ := h hrange hS
  exact two_gen_of_map_injective hφ hRX hRY hX hY hgen

theorem small_alternating_six_two_generating_overgroups
    (hΓ : Nonempty (Γ ≃* Perm (Fin 6)) ∨ Nonempty (Γ ≃* alternatingGroup (Fin 6)))
    {T : Subgroup Γ} (hT : IsSylowTwoOf T ⊤) :
    ∃ X Y : Subgroup Γ, T ≤ X ∧ T ≤ Y ∧ X < ⊤ ∧ Y < ⊤ ∧ X ⊔ Y = ⊤ :=
  two_generating_overgroups_of_iso twoGenPerm_six hΓ hT

end Abstract

end CFSG.QuasithinUnique.Setup.X3
