module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog516COdd
public import CFSG.LinearAlgebra.LinearGroups.Elementary
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.ComponentClassification.GSThmB.Cent516

open CFSG Subgroup Matrix

abbrev Concl516 (Y : Type*) [Group Y] (α : MulAut Y) (q : ℕ) : Prop :=
  ∃ N : Subgroup Y, (∀ y ∈ N, α y = y) ∧
    (⁅N, N⁆ = N ∨ (q = 3 ∧ N ≤ closure {y : Y | α y = y ∧ Odd (orderOf y)})) ∧
    (center Y ≤ N ∨
      (∃ A : Subgroup Y, A ≤ N ∧ (∀ u ∈ A, ∀ v ∈ A, u * v = v * u) ∧ Nat.card A = 8 ∧
        ∃ u ∈ A, ∃ v ∈ A, u ≠ v ∧ orderOf u = 2 ∧ orderOf v = 2) ∨
      ((∀ t : Y, α ≠ MulAut.conj t) ∧ 4 ∣ Nat.card N))

section Elementary

variable {K : Type*} [Field K] {n : ℕ}

theorem transvection_pow (i j : Fin n) (hij : i ≠ j) (c : K) (k : ℕ) :
    (SpecialLinearGroup.transvection hij c) ^ k = SpecialLinearGroup.transvection hij (k * c) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih]
    apply Subtype.ext
    change Matrix.transvection i j ((k : K) * c) * Matrix.transvection i j c =
      Matrix.transvection i j (((k + 1 : ℕ) : K) * c)
    rw [Matrix.transvection_mul_transvection_same i j hij]
    push_cast
    ring_nf

theorem transvection_pow_char {p : ℕ} [CharP K p] (i j : Fin n) (hij : i ≠ j) (c : K) :
    (SpecialLinearGroup.transvection hij c) ^ p = 1 := by
  rw [transvection_pow, CharP.cast_eq_zero, zero_mul, SpecialLinearGroup.transvection_coeff_zero]

theorem odd_orderOf_of_mem_elementarySet {p : ℕ} [CharP K p] (hp : p.Prime) (hp2 : p ≠ 2)
    {s : SpecialLinearGroup (Fin n) K} (hs : s ∈ LinearGroups.elementarySet n K) :
    Odd (orderOf s) := by
  obtain ⟨i, j, hij, c, rfl⟩ := hs
  exact Odd.of_dvd_nat (hp.odd_of_ne_two hp2)
    (orderOf_dvd_of_pow_eq_one (transvection_pow_char i j hij c))

theorem closure_prod_eq_top {G₁ G₂ : Type*} [Group G₁] [Group G₂] {S₁ : Set G₁} {S₂ : Set G₂}
    (h₁ : closure S₁ = ⊤) (h₂ : closure S₂ = ⊤) :
    closure ((fun s => (s, (1 : G₂))) '' S₁ ∪ (fun s => ((1 : G₁), s)) '' S₂) = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨a, b⟩ -
  have ha : (a, (1 : G₂)) ∈ closure ((fun s => (s, (1 : G₂))) '' S₁ ∪
      (fun s => ((1 : G₁), s)) '' S₂) := by
    have : a ∈ closure S₁ := h₁ ▸ mem_top a
    have h := Subgroup.mem_map_of_mem (MonoidHom.inl G₁ G₂) this
    rw [MonoidHom.map_closure] at h
    exact closure_mono (fun x hx => Or.inl (by simpa using hx)) h
  have hb : ((1 : G₁), b) ∈ closure ((fun s => (s, (1 : G₂))) '' S₁ ∪
      (fun s => ((1 : G₁), s)) '' S₂) := by
    have : b ∈ closure S₂ := h₂ ▸ mem_top b
    have h := Subgroup.mem_map_of_mem (MonoidHom.inr G₁ G₂) this
    rw [MonoidHom.map_closure] at h
    exact closure_mono (fun x hx => Or.inr (by simpa using hx)) h
  have := mul_mem ha hb
  simpa using this

theorem isPerfect_prod {G₁ G₂ : Type*} [Group G₁] [Group G₂] [Group.IsPerfect G₁]
    [Group.IsPerfect G₂] : Group.IsPerfect (G₁ × G₂) := by
  rw [Group.isPerfect_def, commutator_def, ← Subgroup.top_prod_top, Subgroup.commutator_prod_prod,
    ← commutator_def, ← commutator_def, Group.IsPerfect.commutator_eq_top,
    Group.IsPerfect.commutator_eq_top]

end Elementary

section Z4Z2

variable {G : Type*} [Group G]

theorem pow_val_add_four {x : G} (hx : x ^ 4 = 1) (a b : ZMod 4) :
    x ^ (a + b).val = x ^ a.val * x ^ b.val := by
  rw [← pow_add, ZMod.val_add, ← pow_mod_orderOf, ← pow_mod_orderOf (n := a.val + b.val)]
  have h4 : orderOf x ∣ 4 := orderOf_dvd_of_pow_eq_one hx
  rw [Nat.mod_mod_of_dvd _ h4]

theorem pow_val_add_two {x : G} (hx : x ^ 2 = 1) (a b : ZMod 2) :
    x ^ (a + b).val = x ^ a.val * x ^ b.val := by
  rw [← pow_add, ZMod.val_add, ← pow_mod_orderOf, ← pow_mod_orderOf (n := a.val + b.val)]
  have h2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hx
  rw [Nat.mod_mod_of_dvd _ h2]

@[expose] def z4z2Hom (x w : G) (hx : x ^ 4 = 1) (hw : w ^ 2 = 1) (hxw : Commute x w) :
    Multiplicative (ZMod 4 × ZMod 2) →* G where
  toFun v := x ^ (Multiplicative.toAdd v).1.val * w ^ (Multiplicative.toAdd v).2.val
  map_one' := by simp
  map_mul' v u := by
    simp only [toAdd_mul, Prod.fst_add, Prod.snd_add, pow_val_add_four hx, pow_val_add_two hw,
      mul_assoc]
    congr 1
    exact (hxw.pow_pow _ _).left_comm _

theorem exists_z4z2 [Finite G] {M : Subgroup G} {x w : G} (hxM : x ∈ M) (hwM : w ∈ M)
    (hx : orderOf x = 4) (hw : orderOf w = 2) (hxw : Commute x w) (hne : w ≠ x ^ 2) :
    ∃ B : Subgroup G, B ≤ M ∧ (∀ u ∈ B, ∀ v ∈ B, u * v = v * u) ∧ Nat.card B = 8 ∧
      ∃ u ∈ B, ∃ v ∈ B, u ≠ v ∧ orderOf u = 2 ∧ orderOf v = 2 := by
  have hx4 : x ^ 4 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hw2 : w ^ 2 = 1 := by rw [← hw]; exact pow_orderOf_eq_one w
  set φ := z4z2Hom x w hx4 hw2 hxw
  have hx2 : orderOf (x ^ 2) = 2 := by
    rw [orderOf_pow' x (by norm_num), hx]
    rfl
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro v hv
    obtain ⟨⟨a, b⟩, rfl⟩ := Multiplicative.ofAdd.surjective v
    change x ^ a.val * w ^ b.val = 1 at hv
    have hb : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide
    have ha : ∀ a : ZMod 4, a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 := by decide
    have hv0 : (0 : ZMod 4).val = 0 := rfl
    have hv1 : (1 : ZMod 4).val = 1 := rfl
    have hv2 : (2 : ZMod 4).val = 2 := rfl
    have hv3 : (3 : ZMod 4).val = 3 := rfl
    have hw0 : (0 : ZMod 2).val = 0 := rfl
    have hw1 : (1 : ZMod 2).val = 1 := rfl
    have hxk : ∀ k : ℕ, 0 < k → k < 4 → x ^ k ≠ 1 := fun k hk hk4 h => by
      have := orderOf_le_of_pow_eq_one hk h
      omega
    rcases hb b with rfl | rfl
    · rw [hw0, pow_zero, mul_one] at hv
      rcases ha a with rfl | rfl | rfl | rfl
      · rfl
      · exact absurd hv (hxk 1 (by norm_num) (by norm_num))
      · exact absurd hv (hxk 2 (by norm_num) (by norm_num))
      · exact absurd hv (hxk 3 (by norm_num) (by norm_num))
    · exfalso
      rw [hw1, pow_one] at hv
      have hwx : w = (x ^ a.val)⁻¹ := eq_inv_of_mul_eq_one_right hv
      rcases ha a with rfl | rfl | rfl | rfl
      · rw [hv0, pow_zero, inv_one] at hwx
        rw [hwx, orderOf_one] at hw
        omega
      · rw [hv1, pow_one] at hwx
        rw [hwx, orderOf_inv, hx] at hw
        omega
      · apply hne
        rw [hwx, hv2]
        have h22 : x ^ 2 * x ^ 2 = 1 := by rw [← pow_add]; exact hx4
        exact inv_eq_of_mul_eq_one_right h22
      · have h3 : (x ^ 3)⁻¹ = x := by
          rw [inv_eq_iff_mul_eq_one, ← pow_succ, hx4]
        rw [hv3, h3] at hwx
        rw [hwx, hx] at hw
        omega
  have hle : φ.range ≤ M := by
    rintro _ ⟨v, rfl⟩
    exact mul_mem (pow_mem hxM _) (pow_mem hwM _)
  have hcard : Nat.card φ.range = 8 := by
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hinj, Subgroup.card_top,
      Nat.card_congr Multiplicative.toAdd]
    simp
  refine ⟨φ.range, hle, ?_, hcard, x ^ 2, ⟨Multiplicative.ofAdd (2, 0), ?_⟩, w,
    ⟨Multiplicative.ofAdd (0, 1), ?_⟩, fun h => hne h.symm, hx2, hw⟩
  · rintro _ ⟨v, rfl⟩ _ ⟨u, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm]
  · change x ^ (2 : ZMod 4).val * w ^ (0 : ZMod 2).val = x ^ 2
    rw [show (2 : ZMod 4).val = 2 from rfl, show (0 : ZMod 2).val = 0 from rfl, pow_zero,
      mul_one]
  · change x ^ (0 : ZMod 4).val * w ^ (1 : ZMod 2).val = w
    rw [show (0 : ZMod 4).val = 0 from rfl, show (1 : ZMod 2).val = 1 from rfl, pow_zero,
      one_mul, pow_one]

end Z4Z2

variable {Y : Type*} [Group Y]

theorem exists_N_of_hom [Finite Y] (hZ : Nat.card (center Y) = 2) (α : MulAut Y) {q : ℕ}
    {G : Type*} [Group G] (ρ : G →* Y ⧸ center Y) (hfix : ∀ g, barAut α (ρ g) = ρ g)
    (hgood : Group.IsPerfect G ∨
      (q = 3 ∧ ∃ S : Set G, closure S = ⊤ ∧ ∀ s ∈ S, Odd (orderOf s))) :
    ∃ N : Subgroup Y, (∀ y ∈ N, α y = y) ∧
      (⁅N, N⁆ = N ∨ (q = 3 ∧ N ≤ closure {y : Y | α y = y ∧ Odd (orderOf y)})) ∧
      N.map piZ = ρ.range ∧
      ∀ σ : G →* Y, (∀ g, piZ (σ g) = ρ g) → σ.range ≤ N := by
  have hfixM : ∀ x ∈ ρ.range, barAut α x = x := by
    rintro _ ⟨g, rfl⟩
    exact hfix g
  rcases hgood with hG | ⟨hq, S, hS, hSodd⟩
  · have hM : ⁅ρ.range, ρ.range⁆ = ρ.range := by
      rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← commutator_def,
        Group.IsPerfect.commutator_eq_top]
    refine ⟨liftN piZ ρ.range, fixed_lift α hM hfixM,
      Or.inl (liftN_perfect (ker_piZ (Y := Y)) hM (le_range_piZ _)),
      map_liftN hM (le_range_piZ _), fun σ hσ => ?_⟩
    have hle : σ.range ≤ (ρ.range).comap piZ := by
      rintro _ ⟨g, rfl⟩
      exact ⟨g, (hσ g).symm⟩
    rw [MonoidHom.range_eq_map, ← Group.IsPerfect.commutator_eq_top (G := G), commutator_def,
      Subgroup.map_commutator, ← MonoidHom.range_eq_map]
    exact Subgroup.commutator_mono hle hle
  · set T : Set (Y ⧸ center Y) := ρ '' S
    have hT : ∀ t ∈ T, barAut α t = t := by
      rintro _ ⟨s, -, rfl⟩
      exact hfix s
    have hTo : ∀ t ∈ T, Odd (orderOf t) := by
      rintro _ ⟨s, hs, rfl⟩
      exact Odd.of_dvd_nat (hSodd s hs) (orderOf_map_dvd ρ s)
    have hclT : closure T = ρ.range := by
      rw [← MonoidHom.map_closure, hS, MonoidHom.range_eq_map]
    refine ⟨oddLift piZ T, oddLift_fixed hZ ker_piZ_eq α (barAut α) (piZ_comm α) hT,
      Or.inr ⟨hq, oddLift_le hZ ker_piZ_eq α (barAut α) (piZ_comm α) hT⟩, ?_, fun σ hσ => ?_⟩
    · rw [map_oddLift (QuotientGroup.mk'_surjective _) (ker_piZ (Y := Y)) (sq_ker_piZ hZ) hTo,
        hclT]
    · rw [MonoidHom.range_eq_map, ← hS, MonoidHom.map_closure, oddLift, closure_le]
      rintro _ ⟨s, hs, rfl⟩
      exact subset_closure ⟨⟨s, hs, (hσ s).symm⟩,
        Odd.of_dvd_nat (hSodd s hs) (orderOf_map_dvd σ s)⟩

theorem concl516_abelian [Finite Y] (hZ : Nat.card (center Y) = 2) (α : MulAut Y) {q : ℕ}
    {G : Type*} [Group G] (ρ : G →* Y ⧸ center Y) (hfix : ∀ g, barAut α (ρ g) = ρ g)
    (hgood : Group.IsPerfect G ∨
      (q = 3 ∧ ∃ S : Set G, closure S = ⊤ ∧ ∀ s ∈ S, Odd (orderOf s)))
    {B : Subgroup (Y ⧸ center Y)} (hBM : B ≤ ρ.range)
    (hBab : ∀ u ∈ B, ∀ v ∈ B, u * v = v * u) (hB8 : Nat.card B = 8)
    (hBinv : ∃ u ∈ B, ∃ v ∈ B, u ≠ v ∧ orderOf u = 2 ∧ orderOf v = 2) : Concl516 Y α q := by
  obtain ⟨N, hfixN, hgoodN, hmap, -⟩ := exists_N_of_hom hZ α ρ hfix hgood
  refine ⟨N, hfixN, hgoodN, ?_⟩
  rcases abelian_or_center_of_le_map hZ (ker_piZ (Y := Y)) (hmap ▸ hBM) hBab hB8 hBinv with
    h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

theorem concl516_center [Finite Y] (hZ : Nat.card (center Y) = 2) (α : MulAut Y) {q : ℕ}
    {G : Type*} [Group G] (ρ : G →* Y ⧸ center Y) (hfix : ∀ g, barAut α (ρ g) = ρ g)
    (hgood : Group.IsPerfect G ∨
      (q = 3 ∧ ∃ S : Set G, closure S = ⊤ ∧ ∀ s ∈ S, Odd (orderOf s)))
    (σ : G →* Y) (hσ : ∀ g, piZ (σ g) = ρ g) (g₀ : G)
    (hg₀ : σ g₀ ∈ center Y) (hg₀1 : σ g₀ ≠ 1) : Concl516 Y α q := by
  obtain ⟨N, hfixN, hgoodN, -, hσN⟩ := exists_N_of_hom hZ α ρ hfix hgood
  refine ⟨N, hfixN, hgoodN, Or.inl fun w hw => ?_⟩
  by_cases hw1 : w = 1
  · rw [hw1]; exact one_mem _
  rw [eq_of_card_two hZ hw hg₀ hw1 hg₀1]
  exact hσN σ hσ ⟨g₀, rfl⟩

theorem concl516_outer [Finite Y] (hZ : Nat.card (center Y) = 2) (α : MulAut Y) {q : ℕ}
    {G : Type*} [Group G] (ρ : G →* Y ⧸ center Y) (hfix : ∀ g, barAut α (ρ g) = ρ g)
    (hgood : Group.IsPerfect G ∨
      (q = 3 ∧ ∃ S : Set G, closure S = ⊤ ∧ ∀ s ∈ S, Odd (orderOf s)))
    (hout : ∀ x, barAut α ≠ MulAut.conj x)
    (h4 : 4 ∣ Nat.card ρ.range) : Concl516 Y α q := by
  obtain ⟨N, hfixN, hgoodN, hmap, -⟩ := exists_N_of_hom hZ α ρ hfix hgood
  refine ⟨N, hfixN, hgoodN, Or.inr (Or.inr ⟨not_inner_of_bar hout, h4.trans ?_⟩)⟩
  have := Subgroup.card_map_dvd (H := N) (piZ (Y := Y))
  rwa [hmap] at this

theorem concl516_one (hY : Group.IsPerfect Y) (α : MulAut Y) {q : ℕ} (h1 : barAut α = 1) :
    Concl516 Y α q := by
  have hM : ⁅(⊤ : Subgroup (Y ⧸ center Y)), (⊤ : Subgroup (Y ⧸ center Y))⁆ =
      (⊤ : Subgroup (Y ⧸ center Y)) := by
    rw [← range_piZ, MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← commutator_def,
      Group.IsPerfect.commutator_eq_top]
  have hN : liftN (piZ (Y := Y)) ⊤ = ⊤ := by
    rw [liftN, Subgroup.comap_top, ← commutator_def, Group.IsPerfect.commutator_eq_top]
  refine ⟨liftN (piZ (Y := Y)) ⊤, fixed_lift α hM (fun x _ => by rw [h1]; rfl),
    Or.inl (liftN_perfect (ker_piZ (Y := Y)) hM (le_range_piZ ⊤)), Or.inl ?_⟩
  rw [hN]
  exact le_top

end CFSG.ComponentClassification.GSThmB.Cent516
