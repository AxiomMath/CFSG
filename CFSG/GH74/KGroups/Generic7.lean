module

public import Mathlib
public import CFSG.GH74.KGroups.Generic3
import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Gaschutz

public section

namespace CFSG.GH74.KGroups

open scoped commutatorElement

theorem commutator_central_mul {C : Type*} [Group C] (N : Subgroup C)
    (hZc : ∀ z ∈ N, ∀ g : C, g * z = z * g) (n1 n2 d1 d2 : C) (h1 : n1 ∈ N) (h2 : n2 ∈ N) :
    ⁅n1 * d1, n2 * d2⁆ = ⁅d1, d2⁆ := by
  have hl : ∀ n ∈ N, ∀ g h : C, ⁅n * g, h⁆ = ⁅g, h⁆ := by
    intro n hn g h
    have hz : n * (g * h * g⁻¹) = (g * h * g⁻¹) * n := (hZc n hn _).symm
    calc ⁅n * g, h⁆ = n * (g * h * g⁻¹) * n⁻¹ * h⁻¹ := by
          simp only [commutatorElement_def]; group
      _ = (g * h * g⁻¹) * n * n⁻¹ * h⁻¹ := by rw [hz]
      _ = ⁅g, h⁆ := by simp only [commutatorElement_def]; group
  have hr : ∀ n ∈ N, ∀ g h : C, ⁅g, n * h⁆ = ⁅g, h⁆ := by
    intro n hn g h
    have hz : g * n = n * g := hZc n hn g
    calc ⁅g, n * h⁆ = (g * n) * h * g⁻¹ * h⁻¹ * n⁻¹ := by
          simp only [commutatorElement_def]; group
      _ = (n * g) * h * g⁻¹ * h⁻¹ * n⁻¹ := by rw [hz]
      _ = n * (g * h * g⁻¹ * h⁻¹) * n⁻¹ := by group
      _ = (g * h * g⁻¹ * h⁻¹) * n * n⁻¹ := by rw [← hZc n hn (g * h * g⁻¹ * h⁻¹)]
      _ = ⁅g, h⁆ := by simp only [commutatorElement_def]; group
  rw [hl n1 h1, hr n2 h2]

theorem eq_bot_of_central_complement_perfect {C : Type*} [Group C] (N D : Subgroup C)
    [N.Normal] (hperf : commutator C = ⊤) (hZc : ∀ z ∈ N, ∀ g : C, g * z = z * g)
    (hND : N ⊓ D = ⊥) (hNDtop : N ⊔ D = ⊤) : N = ⊥ := by
  have hcomm : commutator C ≤ D := by
    rw [commutator_def, Subgroup.commutator_le]
    intro g _ h _
    have hg : g ∈ (↑(N ⊔ D) : Set C) := by rw [hNDtop]; exact Subgroup.mem_top g
    have hh : h ∈ (↑(N ⊔ D) : Set C) := by rw [hNDtop]; exact Subgroup.mem_top h
    rw [Subgroup.normal_mul] at hg hh
    obtain ⟨n1, hn1, d1, hd1, rfl⟩ := Set.mem_mul.1 hg
    obtain ⟨n2, hn2, d2, hd2, rfl⟩ := Set.mem_mul.1 hh
    rw [commutator_central_mul N hZc n1 n2 d1 d2 hn1 hn2, commutatorElement_def]
    exact D.mul_mem (D.mul_mem (D.mul_mem hd1 hd2) (D.inv_mem hd1)) (D.inv_mem hd2)
  have hD : D = ⊤ := top_le_iff.1 (hperf ▸ hcomm)
  calc N = N ⊓ D := by rw [hD, inf_top_eq]
    _ = ⊥ := hND

section SD16

local macro "gp" : tactic => `(tactic| (simp only [pow_succ, pow_zero, one_mul]; group))

theorem sd16_lifts {C J : Type*} [Group C] [Group J] (π : C →* J) (hπ : Function.Surjective π)
    (hZc : ∀ z ∈ π.ker, ∀ g : C, g * z = z * g) (hZ2 : ∀ z ∈ π.ker, z ^ 2 = 1)
    (x y w g1 g2 : J) (hy2 : y ^ 2 = 1) (hyx : y * x * y⁻¹ = x ^ 3)
    (hw3 : w ^ 3 = 1) (hwx4 : w * x ^ 4 * w⁻¹ = x ^ 4) (hwx2 : w * x ^ 2 * w⁻¹ = y * x)
    (hg1 : g1 * y * g1⁻¹ = x ^ 4) (hg2 : g2 * y * g2⁻¹ = y * x ^ 2) :
    ∃ a b : C, π a = x ∧ π b = y ∧ a ^ 8 = 1 ∧ b ^ 2 = 1 ∧ b * a * b⁻¹ = a ^ 3 := by
  have key : ∀ u v : C, π u = π v → ∃ z ∈ π.ker, u = v * z := fun u v h =>
    ⟨v⁻¹ * u, by rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel], by group⟩
  obtain ⟨a, ha⟩ := hπ x
  obtain ⟨b, hb⟩ := hπ y
  obtain ⟨c, hc⟩ := hπ w
  obtain ⟨d1, hd1⟩ := hπ g1
  obtain ⟨d2, hd2⟩ := hπ g2
  have hsq : ∀ z ∈ π.ker, z * z = 1 := fun z hz => by rw [← pow_two]; exact hZ2 z hz
  have hconj : ∀ z ∈ π.ker, ∀ g : C, g * z * g⁻¹ = z := fun z hz g => by
    rw [hZc z hz g]; group
  have hb2 : b ^ 2 ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_pow, hb]; exact hy2
  obtain ⟨e, he, hE⟩ := key (b * a * b⁻¹) (a ^ 3)
    (by simp [map_mul, map_inv, map_pow, ha, hb, hyx])
  have hba2 : b * a ^ 2 * b⁻¹ = a ^ 6 := by
    have h1 : b * a ^ 2 * b⁻¹ = (b * a * b⁻¹) * (b * a * b⁻¹) := by gp
    rw [h1, hE]
    have hec : e * a ^ 3 = a ^ 3 * e := (hZc e he (a ^ 3)).symm
    calc a ^ 3 * e * (a ^ 3 * e) = a ^ 3 * (e * a ^ 3) * e := by gp
      _ = a ^ 3 * (a ^ 3 * e) * e := by rw [hec]
      _ = a ^ 6 * (e * e) := by gp
      _ = a ^ 6 := by rw [hsq e he, mul_one]
  obtain ⟨z2, hz2, hZ2eq⟩ := key (d2 * b * d2⁻¹) (b * a ^ 2)
    (by simp [map_mul, map_inv, map_pow, ha, hb, hd2, hg2])
  have hu2 : (b * a ^ 2) ^ 2 = a ^ 8 * b ^ 2 := by
    have h1 : (b * a ^ 2) ^ 2 = (b * a ^ 2 * b⁻¹) * b ^ 2 * a ^ 2 := by gp
    rw [h1, hba2]
    have hc2 : b ^ 2 * a ^ 2 = a ^ 2 * b ^ 2 := (hZc (b ^ 2) hb2 (a ^ 2)).symm
    calc a ^ 6 * b ^ 2 * a ^ 2 = a ^ 6 * (b ^ 2 * a ^ 2) := by gp
      _ = a ^ 6 * (a ^ 2 * b ^ 2) := by rw [hc2]
      _ = a ^ 8 * b ^ 2 := by gp
  have hsqz2 : (d2 * b * d2⁻¹) ^ 2 = b ^ 2 := by
    have : (d2 * b * d2⁻¹) ^ 2 = d2 * b ^ 2 * d2⁻¹ := by gp
    rw [this, hconj _ hb2]
  have h8 : a ^ 8 = 1 := by
    have h1 : b ^ 2 = (b * a ^ 2) ^ 2 := by
      rw [← hsqz2, hZ2eq]
      have : (b * a ^ 2 * z2) ^ 2 = (b * a ^ 2) ^ 2 * (z2 * z2) := by
        calc (b * a ^ 2 * z2) ^ 2 = (b * a ^ 2) * (z2 * (b * a ^ 2)) * z2 := by gp
          _ = (b * a ^ 2) * ((b * a ^ 2) * z2) * z2 := by rw [hZc z2 hz2 (b * a ^ 2)]
          _ = (b * a ^ 2) ^ 2 * (z2 * z2) := by gp
      rw [this, hsq z2 hz2, mul_one]
    rw [hu2] at h1
    have h2 : a ^ 8 * b ^ 2 = 1 * b ^ 2 := by rw [one_mul]; exact h1.symm
    exact mul_right_cancel h2
  obtain ⟨z1, hz1, hZ1eq⟩ := key (d1 * b * d1⁻¹) (a ^ 4)
    (by simp [map_mul, map_inv, map_pow, ha, hb, hd1, hg1])
  have hb2eq : b ^ 2 = 1 := by
    have h1 : (d1 * b * d1⁻¹) ^ 2 = b ^ 2 := by
      have : (d1 * b * d1⁻¹) ^ 2 = d1 * b ^ 2 * d1⁻¹ := by gp
      rw [this, hconj _ hb2]
    rw [hZ1eq] at h1
    have : (a ^ 4 * z1) ^ 2 = a ^ 8 * (z1 * z1) := by
      calc (a ^ 4 * z1) ^ 2 = a ^ 4 * (z1 * a ^ 4) * z1 := by gp
        _ = a ^ 4 * (a ^ 4 * z1) * z1 := by rw [hZc z1 hz1 (a ^ 4)]
        _ = a ^ 8 * (z1 * z1) := by gp
    rw [this, hsq z1 hz1, mul_one, h8] at h1
    exact h1.symm
  have hc3 : c ^ 3 ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_pow, hc]; exact hw3
  obtain ⟨z3, hz3, hZ3eq⟩ := key (c * a ^ 2 * c⁻¹) (b * a)
    (by simp [map_mul, map_inv, map_pow, ha, hb, hc, hwx2])
  obtain ⟨z4, hz4, hZ4eq⟩ := key (c * a ^ 4 * c⁻¹) (a ^ 4)
    (by simp [map_mul, map_inv, map_pow, ha, hc, hwx4])
  have hz4one : z4 = 1 := by
    have h1 : c * (a ^ 4 * z4) * c⁻¹ = a ^ 4 := by
      have : c * (a ^ 4 * z4) * c⁻¹ = (c * a ^ 4 * c⁻¹) * (c * z4 * c⁻¹) := by gp
      rw [this, hZ4eq, hconj _ hz4, mul_assoc, hsq z4 hz4, mul_one]
    have h2 : c ^ 3 * a ^ 4 * (c ^ 3)⁻¹ = a ^ 4 * z4 := by
      have : c ^ 3 * a ^ 4 * (c ^ 3)⁻¹ = c * (c * (c * a ^ 4 * c⁻¹) * c⁻¹) * c⁻¹ := by gp
      rw [this, hZ4eq, h1, hZ4eq]
    have h3 : c ^ 3 * a ^ 4 * (c ^ 3)⁻¹ = a ^ 4 := by
      rw [← hZc (c ^ 3) hc3 (a ^ 4)]; group
    rw [h3] at h2
    have h4 : a ^ 4 * 1 = a ^ 4 * z4 := by rw [mul_one]; exact h2
    exact (mul_left_cancel h4).symm
  have he1 : e = 1 := by
    have h1 : (c * a ^ 2 * c⁻¹) ^ 2 = c * a ^ 4 * c⁻¹ := by gp
    have h2 : (b * a) ^ 2 = a ^ 4 * e := by
      have : (b * a) ^ 2 = (b * a * b⁻¹) * b ^ 2 * a := by gp
      rw [this, hE, hb2eq, mul_one]
      have hea : e * a = a * e := (hZc e he a).symm
      calc a ^ 3 * e * a = a ^ 3 * (e * a) := by gp
        _ = a ^ 3 * (a * e) := by rw [hea]
        _ = a ^ 4 * e := by gp
    rw [hZ3eq] at h1
    have h5 : (b * a * z3) ^ 2 = (b * a) ^ 2 * (z3 * z3) := by
      calc (b * a * z3) ^ 2 = (b * a) * (z3 * (b * a)) * z3 := by gp
        _ = (b * a) * ((b * a) * z3) * z3 := by rw [hZc z3 hz3 (b * a)]
        _ = (b * a) ^ 2 * (z3 * z3) := by gp
    rw [h5, hsq z3 hz3, mul_one, h2, hZ4eq, hz4one, mul_one] at h1
    have h6 : a ^ 4 * e = a ^ 4 * 1 := by rw [mul_one]; exact h1
    exact mul_left_cancel h6
  refine ⟨a, b, ha, hb, h8, hb2eq, ?_⟩
  rw [hE, he1, mul_one]

end SD16

theorem card_closure_le_sixteen {C : Type*} [Group C] (a b : C) (ha : a ^ 8 = 1) (hb : b ^ 2 = 1)
    (hab : b * a * b⁻¹ = a ^ 3) : Nat.card (Subgroup.closure ({a, b} : Set C)) ≤ 16 := by
  have hbinv : b⁻¹ = b := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_two]; exact hb
  have hba : b * a = a ^ 3 * b := by
    have : b * a * b⁻¹ * b = a ^ 3 * b := by rw [hab]
    simpa using this
  have hbak : ∀ k : ℕ, b * a ^ k = a ^ (3 * k) * b := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc b * a ^ (k + 1) = (b * a ^ k) * a := by rw [pow_succ, mul_assoc]
        _ = a ^ (3 * k) * (b * a) := by rw [ih, mul_assoc]
        _ = a ^ (3 * k) * (a ^ 3 * b) := by rw [hba]
        _ = a ^ (3 * (k + 1)) * b := by
          rw [← mul_assoc, ← pow_add]
          have : 3 * k + 3 = 3 * (k + 1) := by ring
          rw [this]
  have hbjak : ∀ j k : ℕ, b ^ j * a ^ k = a ^ (3 ^ j * k) * b ^ j := by
    intro j
    induction j with
    | zero => intro k; simp
    | succ j ih =>
      intro k
      calc b ^ (j + 1) * a ^ k = b ^ j * (b * a ^ k) := by rw [pow_succ, mul_assoc]
        _ = b ^ j * (a ^ (3 * k) * b) := by rw [hbak]
        _ = (b ^ j * a ^ (3 * k)) * b := by rw [mul_assoc]
        _ = (a ^ (3 ^ j * (3 * k)) * b ^ j) * b := by rw [ih]
        _ = a ^ (3 ^ (j + 1) * k) * b ^ (j + 1) := by
          rw [mul_assoc, ← pow_succ]
          have : 3 ^ j * (3 * k) = 3 ^ (j + 1) * k := by ring
          rw [this]
  have hmem : ∀ x ∈ Subgroup.closure ({a, b} : Set C), ∃ i j : ℕ, x = a ^ i * b ^ j := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | hx
      · exact ⟨1, 0, by simp⟩
      · rw [Set.mem_singleton_iff] at hx
        subst hx
        exact ⟨0, 1, by simp⟩
    | one => exact ⟨0, 0, by simp⟩
    | mul x y _ _ hx hy =>
      obtain ⟨i, j, rfl⟩ := hx
      obtain ⟨k, l, rfl⟩ := hy
      refine ⟨i + 3 ^ j * k, j + l, ?_⟩
      calc a ^ i * b ^ j * (a ^ k * b ^ l) = a ^ i * (b ^ j * a ^ k) * b ^ l := by
            simp only [mul_assoc]
        _ = a ^ i * (a ^ (3 ^ j * k) * b ^ j) * b ^ l := by rw [hbjak]
        _ = a ^ (i + 3 ^ j * k) * b ^ (j + l) := by
          rw [pow_add, pow_add]; simp only [mul_assoc]
    | inv x _ hx =>
      obtain ⟨i, j, rfl⟩ := hx
      refine ⟨7 * i * 3 ^ j, j, ?_⟩
      have h1 : (a ^ i * b ^ j)⁻¹ = (b ^ j)⁻¹ * (a ^ i)⁻¹ := mul_inv_rev _ _
      have h2 : (b ^ j)⁻¹ = b ^ j := by
        rw [← inv_pow, hbinv]
      have h3 : (a ^ i)⁻¹ = a ^ (7 * i) := by
        rw [← inv_pow]
        have : a⁻¹ = a ^ 7 := by
          apply inv_eq_of_mul_eq_one_right
          rw [← pow_succ']; exact ha
        rw [this, ← pow_mul, mul_comm]
      rw [h1, h2, h3, hbjak]
      have : 3 ^ j * (7 * i) = 7 * i * 3 ^ j := by ring
      rw [this]
  have hfin : Nat.card (Fin 8 × Fin 2) = 16 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  set H : Subgroup C := Subgroup.closure ({a, b} : Set C) with hH
  have haH : a ∈ H := Subgroup.subset_closure (by simp)
  have hbH : b ∈ H := Subgroup.subset_closure (by simp)
  let f : Fin 8 × Fin 2 → H := fun p =>
    ⟨a ^ (p.1 : ℕ) * b ^ (p.2 : ℕ), H.mul_mem (H.pow_mem haH _) (H.pow_mem hbH _)⟩
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x, hx⟩ := y
    obtain ⟨i, j, hij⟩ := hmem x hx
    have hi : i % 8 < 8 := Nat.mod_lt i (by norm_num)
    have hj : j % 2 < 2 := Nat.mod_lt j (by norm_num)
    refine ⟨(⟨i % 8, hi⟩, ⟨j % 2, hj⟩), ?_⟩
    apply Subtype.ext
    show a ^ (i % 8) * b ^ (j % 2) = x
    rw [hij, ← pow_eq_pow_mod i ha, ← pow_eq_pow_mod j hb]
  have h := Nat.card_le_card_of_surjective f hf
  rw [hfin] at h
  exact h

theorem card_closure_pair_equiv {J G : Type*} [Group J] [Group G] (P : Subgroup G) (ε : J ≃* P)
    (j1 j2 : J) :
    Nat.card (Subgroup.closure ({j1, j2} : Set J)) =
      Nat.card (Subgroup.closure ({(ε j1 : G), (ε j2 : G)} : Set G)) := by
  let f : J →* G := P.subtype.comp ε.toMonoidHom
  have hf : Function.Injective f := Subtype.val_injective.comp ε.injective
  have h1 : (Subgroup.closure ({j1, j2} : Set J)).map f =
      Subgroup.closure ({(ε j1 : G), (ε j2 : G)} : Set G) := by
    rw [MonoidHom.map_closure]
    congr 1
    ext g
    simp [f]
  rw [← h1]
  exact (Subgroup.card_map_of_injective hf).symm

theorem ker_eq_bot_of_sd16 {C J : Type*} [Group C] [Finite C] [Group J] (π : C →* J)
    (hπ : Function.Surjective π) (hperf : commutator C = ⊤)
    (hZc : ∀ z ∈ π.ker, ∀ g : C, g * z = z * g) (hZ2 : ∀ z ∈ π.ker, z ^ 2 = 1)
    (x y w g1 g2 : J) (hy2 : y ^ 2 = 1) (hyx : y * x * y⁻¹ = x ^ 3)
    (hw3 : w ^ 3 = 1) (hwx4 : w * x ^ 4 * w⁻¹ = x ^ 4) (hwx2 : w * x ^ 2 * w⁻¹ = y * x)
    (hg1 : g1 * y * g1⁻¹ = x ^ 4) (hg2 : g2 * y * g2⁻¹ = y * x ^ 2)
    (hS : 16 ≤ Nat.card (Subgroup.closure ({x, y} : Set J))) (m : ℕ)
    (hJ : Nat.card J = 16 * m) (hm : Odd m) : π.ker = ⊥ := by
  classical
  obtain ⟨a, b, ha, hb, ha8, hb2, hab⟩ := sd16_lifts π hπ hZc hZ2 x y w g1 g2 hy2 hyx hw3 hwx4 hwx2
    hg1 hg2
  set N : Subgroup C := π.ker with hN
  set H : Subgroup C := Subgroup.closure ({a, b} : Set C) with hH
  have hHcard : Nat.card H ≤ 16 := card_closure_le_sixteen a b ha8 hb2 hab
  have hmap : H.map π = Subgroup.closure ({x, y} : Set J) := by
    rw [hH, MonoidHom.map_closure]
    congr 1
    ext g
    simp [ha, hb]
  let f : H →* J := π.comp H.subtype
  have hfrange : f.range = H.map π := by
    ext g
    constructor
    · rintro ⟨⟨h, hh⟩, rfl⟩
      exact ⟨h, hh, rfl⟩
    · rintro ⟨h, hh, rfl⟩
      exact ⟨⟨h, hh⟩, rfl⟩
  have hcardH := Subgroup.card_ker_mul_card_range f
  rw [hfrange] at hcardH
  have hrange : 16 ≤ Nat.card (H.map π) := by rw [hmap]; exact hS
  have hker1 : Nat.card f.ker = 1 := by
    have hpos : 0 < Nat.card f.ker := Nat.card_pos
    by_contra hne
    have h2 : 2 ≤ Nat.card f.ker := by omega
    have := Nat.mul_le_mul h2 hrange
    omega
  have hHmap : Nat.card (H.map π) = 16 := by
    rw [hker1, one_mul] at hcardH
    omega
  have hHN : N ⊓ H = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    obtain ⟨hgN, hgH⟩ := Subgroup.mem_inf.1 hg
    have : (⟨g, hgH⟩ : H) ∈ f.ker := hgN
    rw [Subgroup.eq_bot_of_card_eq _ hker1, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val this
  have hNp : IsPGroup 2 N := fun g => ⟨1, by
    have := hZ2 g.1 g.2
    apply Subtype.ext
    simpa using this⟩
  have hsup : N ⊔ H = (H.map π).comap π := by
    rw [Subgroup.comap_map_eq, sup_comm]
  have hNH : Nat.card (N ⊔ H : Subgroup C) = 16 * Nat.card N := by
    rw [hsup, card_comap_of_surjective π hπ, hHmap]
  have : Finite J := Finite.of_surjective π hπ
  obtain ⟨k, hk⟩ := hNp.exists_card_eq
  have hcardC : Nat.card C = Nat.card N * (16 * m) := by
    rw [← hJ]
    exact (Subgroup.card_ker_mul_card_of_surjective hπ).symm
  have hp2 : IsPGroup 2 (N ⊔ H : Subgroup C) := by
    refine IsPGroup.of_card (n := k + 4) ?_
    rw [hNH, hk]; ring
  have hidx : ¬ 2 ∣ (N ⊔ H : Subgroup C).index := by
    have h1 := Subgroup.card_mul_index (N ⊔ H : Subgroup C)
    rw [hNH, hcardC] at h1
    have hNpos : 0 < Nat.card N := Nat.card_pos
    have h2 : (N ⊔ H : Subgroup C).index = m := by
      have : 16 * Nat.card N * (N ⊔ H : Subgroup C).index = 16 * Nat.card N * m := by
        rw [h1]; ring
      exact Nat.eq_of_mul_eq_mul_left (by positivity) this
    rw [h2]
    exact Nat.not_even_iff_odd.2 hm |> fun h => by simpa [even_iff_two_dvd] using h
  let P : Sylow 2 C := hp2.toSylow hidx
  have : IsMulCommutative N := ⟨⟨fun a b => Subtype.ext (hZc a.1 a.2 b.1).symm⟩⟩
  obtain ⟨D, hND, hNDtop⟩ := CFSG.SignalizerFunctorTheorem.McBride.exists_complement_of_sylow_complement
    Nat.prime_two hNp P le_sup_left hHN rfl
  exact eq_bot_of_central_complement_perfect N D hperf hZc hND hNDtop

end CFSG.GH74.KGroups
