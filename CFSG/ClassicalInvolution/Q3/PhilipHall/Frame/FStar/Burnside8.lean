module

public import Mathlib.GroupTheory.Transfer

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FStar

open Subgroup

variable {F : Type*} [Group F]

theorem mem_four_of_card {Z : Subgroup F} (hZ4 : Nat.card Z = 4) (hZ2 : ∀ x ∈ Z, x * x = 1)
    {u b c : F} (hu : u ∈ Z) (hb : b ∈ Z) (hc : c ∈ Z) (hu1 : u ≠ 1) (hb1 : b ≠ 1)
    (hbu : b ≠ u) : c = 1 ∨ c = u ∨ c = b ∨ c = b * u := by
  classical
  by_contra hne
  push_neg at hne
  obtain ⟨hc1, hcu, hcb, hcbu⟩ := hne
  have huu := hZ2 u hu
  have hbu1 : b * u ≠ 1 := by
    intro h; apply hbu
    calc b = b * u * u := by rw [mul_assoc, huu, mul_one]
      _ = u := by rw [h, one_mul]
  have hbuu : b * u ≠ u := fun h => hb1 (by simpa using h)
  have hbub : b * u ≠ b := fun h => hu1 (by simpa using h)
  let S : Finset F := {c, 1, u, b, b * u}
  have hS : S.card = 5 := by
    simp only [S]
    rw [Finset.card_insert_of_notMem (by simp [hc1, hcu, hcb, hcbu]),
      Finset.card_insert_of_notMem (by simp [hu1.symm, hb1.symm, hbu1.symm]),
      Finset.card_insert_of_notMem (by simp [hbu.symm, hbuu.symm]),
      Finset.card_pair hbub.symm]
  have hsub : (S : Set F) ⊆ Z := by
    intro y hy
    simp only [S, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl
    · exact hc
    · exact Z.one_mem
    · exact hu
    · exact hb
    · exact Z.mul_mem hb hu
  have hn : (Z : Set F).ncard = 4 := by rw [← Nat.card_coe_set_eq]; exact hZ4
  have h := Set.ncard_le_ncard hsub (Set.finite_of_ncard_ne_zero (by omega))
  rw [Set.ncard_coe_finset, hS, hn] at h
  omega

theorem commute_of_sq_of_odd {g a : F} {m : ℕ} (h2 : Commute (g ^ 2) a)
    (hm : Commute (g ^ m) a) (hodd : Odd m) : Commute g a := by
  obtain ⟨k, rfl⟩ := hodd
  rw [pow_succ, pow_mul] at hm
  have := (h2.pow_left k).inv_left.mul_left hm
  rwa [inv_mul_cancel_left] at this

theorem commute_sq_of_conj {g a : F} (h : g * (g * a * g⁻¹) * g⁻¹ = a) : Commute (g ^ 2) a := by
  show g ^ 2 * a = a * g ^ 2
  rw [sq]
  calc g * g * a = (g * (g * a * g⁻¹) * g⁻¹) * (g * g) := by group
    _ = a * (g * g) := by rw [h]

theorem false_of_sylow_eight_omega_four [Finite F] [IsSimpleGroup F]
    (hnab : ∃ a b : F, a * b ≠ b * a) (P : Sylow 2 F) (h8 : Nat.card (P : Subgroup F) = 8)
    {Z : Subgroup F} (hZP : Z ≤ P) (hZ4 : Nat.card Z = 4) (hZ2 : ∀ x ∈ Z, x * x = 1)
    (hinv : ∀ x ∈ (P : Subgroup F), x * x = 1 → x ∈ Z) : False := by
  classical
  have hZc : ∀ a ∈ Z, ∀ d ∈ Z, Commute a d := by
    intro a ha d hd
    show a * d = d * a
    calc a * d = (a * d)⁻¹ := eq_inv_of_mul_eq_one_left (hZ2 _ (Z.mul_mem ha hd))
      _ = d⁻¹ * a⁻¹ := mul_inv_rev a d
      _ = d * a := by rw [inv_eq_of_mul_eq_one_left (hZ2 d hd),
          inv_eq_of_mul_eq_one_left (hZ2 a ha)]
  have hidx : (Z.subgroupOf (P : Subgroup F)).index = 2 := by
    have h := card_mul_index (Z.subgroupOf (P : Subgroup F))
    rw [Nat.card_congr (subgroupOfEquivOfLe hZP).toEquiv, hZ4, h8] at h
    omega
  have hmul : ∀ a ∈ (P : Subgroup F), ∀ d ∈ (P : Subgroup F), a * d ∈ Z ↔ (a ∈ Z ↔ d ∈ Z) := by
    intro a ha d hd
    have := mul_mem_iff_of_index_two hidx (a := ⟨a, ha⟩) (b := ⟨d, hd⟩)
    simpa [mem_subgroupOf] using this
  obtain ⟨x, hxP, hxZ⟩ : ∃ x ∈ (P : Subgroup F), x ∉ Z := by
    by_contra h
    push_neg at h
    have := Subgroup.card_le_of_le (show (P : Subgroup F) ≤ Z from h)
    omega
  set u := x * x with hu_def
  have huZ : u ∈ Z := (hmul x hxP x hxP).2 Iff.rfl
  have hu1 : u ≠ 1 := fun h => hxZ (hinv x hxP h)
  have hxu : Commute x u := by
    show x * (x * x) = x * x * x
    rw [mul_assoc]
  obtain ⟨b, hbZ, hb1, hbu⟩ : ∃ b ∈ Z, b ≠ 1 ∧ b ≠ u := by
    by_contra h
    push_neg at h
    have hsub : (Z : Set F) ⊆ {1, u} := fun y hy => by
      by_cases h1 : y = 1
      · simp [h1]
      · simp [h y hy h1]
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 : ({1, u} : Set F).ncard ≤ 2 := (Set.ncard_insert_le _ _).trans (by simp)
    rw [← Nat.card_coe_set_eq] at h1
    have : Nat.card (Z : Set F) = 4 := hZ4
    omega
  have hfour : ∀ c ∈ Z, c = 1 ∨ c = u ∨ c = b ∨ c = b * u := fun c hc =>
    mem_four_of_card hZ4 hZ2 huZ hbZ hc hu1 hb1 hbu
  have hxb : Commute x b := by
    have hb'P : x * b * x⁻¹ ∈ (P : Subgroup F) :=
      P.mul_mem (P.mul_mem hxP (hZP hbZ)) (P.inv_mem hxP)
    have hb'2 : x * b * x⁻¹ * (x * b * x⁻¹) = 1 := by
      calc x * b * x⁻¹ * (x * b * x⁻¹) = x * (b * b) * x⁻¹ := by group
        _ = 1 := by rw [hZ2 b hbZ, mul_one, mul_inv_cancel]
    have hback : b = x⁻¹ * (x * b * x⁻¹) * x := by group
    rcases hfour _ (hinv _ hb'P hb'2) with h | h | h | h
    · exact absurd (by rw [hback, h]; group) hb1
    · refine absurd ?_ hbu
      rw [hback, h, hu_def]
      group
    · show x * b = b * x
      calc x * b = x * b * x⁻¹ * x := by group
        _ = b * x := by rw [h]
    · exfalso
      have hw : x * b * (x * b) = 1 := by
        calc x * b * (x * b) = x * b * x⁻¹ * (x * x) * b := by group
          _ = b * (u * u) * b := by rw [h, ← hu_def]; group
          _ = 1 := by rw [hZ2 u huZ, mul_one, hZ2 b hbZ]
      have hwZ := hinv _ (P.mul_mem hxP (hZP hbZ)) hw
      exact hxZ (((hmul x hxP b (hZP hbZ)).1 hwZ).2 hbZ)
  have hxZc : ∀ c ∈ Z, Commute x c := by
    intro c hc
    rcases hfour c hc with rfl | rfl | rfl | rfl
    · exact Commute.one_right x
    · exact hxu
    · exact hxb
    · exact hxb.mul_right hxu
  have hrep : ∀ y ∈ (P : Subgroup F), y ∈ Z ∨ ∃ c ∈ Z, y = x * c := by
    intro y hy
    by_cases hyZ : y ∈ Z
    · exact Or.inl hyZ
    · refine Or.inr ⟨x⁻¹ * y, (hmul _ (P.inv_mem hxP) y hy).2 ⟨fun h => absurd
        ((Z.inv_mem_iff).1 h) hxZ, fun h => absurd h hyZ⟩, by group⟩
  have hPc : ∀ a ∈ (P : Subgroup F), ∀ d ∈ (P : Subgroup F), Commute a d := by
    intro a ha d hd
    rcases hrep a ha with haZ | ⟨c, hc, rfl⟩ <;> rcases hrep d hd with hdZ | ⟨e, he, rfl⟩
    · exact hZc a haZ d hdZ
    · exact ((hxZc a haZ).symm).mul_right (hZc a haZ e he)
    · exact ((hxZc d hdZ).symm.mul_right (hZc d hdZ c hc)).symm
    · exact ((Commute.refl x).mul_right (hxZc e he)).mul_left
        (((hxZc c hc).symm).mul_right (hZc c hc e he))
  have hsq : ∀ y ∈ (P : Subgroup F), y ∉ Z → y * y = u := by
    intro y hy hyZ
    rcases hrep y hy with h | ⟨c, hc, rfl⟩
    · exact absurd h hyZ
    · rw [((hxZc c hc).symm).mul_mul_mul_comm, hZ2 c hc, mul_one]
  set N := normalizer ((P : Subgroup F) : Set F) with hN
  let K : Subgroup N := (centralizer (P : Set F)).subgroupOf N
  have hKn : K.Normal := ⟨fun n hn g => by
    simp only [K, mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv, mem_centralizer_iff,
      SetLike.mem_coe] at hn ⊢
    intro p hp
    have hq : (g : F)⁻¹ * p * g ∈ (P : Subgroup F) := (mem_normalizer_iff''.mp g.2 p).1 hp
    have h := hn _ hq
    calc p * (g * n * (g : F)⁻¹) = g * ((g : F)⁻¹ * p * g * n) * (g : F)⁻¹ := by group
      _ = g * (n * ((g : F)⁻¹ * p * g)) * (g : F)⁻¹ := by rw [h]
      _ = g * n * (g : F)⁻¹ * p := by group⟩
  have hPK : (P : Subgroup F).subgroupOf N ≤ K := fun p hp => by
    simp only [K, mem_subgroupOf, mem_centralizer_iff, SetLike.mem_coe] at hp ⊢
    intro q hq
    exact hPc q hq p hp
  have hodd : Odd K.index := by
    have h1 : K.index ∣ (P : Subgroup F).relIndex N := index_dvd_of_le hPK
    have h2 := relIndex_dvd_index_of_le (le_normalizer (H := (P : Subgroup F)))
    have h3 : ¬ 2 ∣ (P : Subgroup F).index := P.not_dvd_index
    exact Nat.not_even_iff_odd.1 fun he => h3 ((even_iff_two_dvd.1 he).trans (h1.trans h2))
  have hNC : N ≤ centralizer (P : Set F) := by
    intro g hg
    have hgm : g ^ K.index ∈ centralizer (P : Set F) := by
      have := pow_index_mem K (⟨g, hg⟩ : N)
      simpa [K, mem_subgroupOf] using this
    have hcm : ∀ a ∈ (P : Subgroup F), Commute (g ^ K.index) a := fun a ha =>
      ((mem_centralizer_iff.mp hgm) a ha).symm
    have hφP : ∀ p ∈ (P : Subgroup F), g * p * g⁻¹ ∈ (P : Subgroup F) := fun p hp =>
      (mem_normalizer_iff.mp hg p).1 hp
    have hφ2 : ∀ c ∈ Z, g * c * g⁻¹ * (g * c * g⁻¹) = 1 := fun c hc => by
      calc g * c * g⁻¹ * (g * c * g⁻¹) = g * (c * c) * g⁻¹ := by group
        _ = 1 := by rw [hZ2 c hc, mul_one, mul_inv_cancel]
    have hφZ : ∀ c ∈ Z, g * c * g⁻¹ ∈ Z := fun c hc =>
      hinv _ (hφP c (hZP hc)) (hφ2 c hc)
    have hgxZ : g * x * g⁻¹ ∉ Z := by
      intro h
      apply hu1
      have h1 := hZ2 _ h
      calc u = g⁻¹ * (g * x * g⁻¹ * (g * x * g⁻¹)) * g := by rw [hu_def]; group
        _ = 1 := by rw [h1]; group
    have hgu : Commute g u := by
      have h1 := hsq _ (hφP x hxP) hgxZ
      show g * u = u * g
      calc g * u = (g * x * g⁻¹ * (g * x * g⁻¹)) * g := by rw [hu_def]; group
        _ = u * g := by rw [h1]
    have hconj : ∀ {a : F}, Commute g a → g * a * g⁻¹ = a := fun {a} h => by
      rw [h.eq, mul_inv_cancel_right]
    have hgb : Commute g b := by
      refine commute_of_sq_of_odd (commute_sq_of_conj ?_) (hcm b (hZP hbZ)) hodd
      have hφb1 : g * b * g⁻¹ ≠ 1 := fun h => hb1 (by
        calc b = g⁻¹ * (g * b * g⁻¹) * g := by group
          _ = 1 := by rw [h]; group)
      have hφbu : g * b * g⁻¹ ≠ u := fun h => hbu (by
        calc b = g⁻¹ * (g * b * g⁻¹) * g := by group
          _ = g⁻¹ * (g * u * g⁻¹) * g := by rw [h, hconj hgu]
          _ = u := by group)
      rcases hfour _ (hφZ b hbZ) with h | h | h | h
      · exact absurd h hφb1
      · exact absurd h hφbu
      · rw [h, h]
      · calc g * (g * b * g⁻¹) * g⁻¹ = g * (b * u) * g⁻¹ := by rw [h]
          _ = (g * b * g⁻¹) * (g * u * g⁻¹) := by group
          _ = b * u * u := by rw [h, hconj hgu]
          _ = b := by rw [mul_assoc, hZ2 u huZ, mul_one]
    have hgZ : ∀ c ∈ Z, Commute g c := by
      intro c hc
      rcases hfour c hc with rfl | rfl | rfl | rfl
      · exact Commute.one_right g
      · exact hgu
      · exact hgb
      · exact hgb.mul_right hgu
    have hgx : Commute g x := by
      obtain ⟨c, hc, hxc⟩ : ∃ c ∈ Z, g * x * g⁻¹ = x * c := by
        rcases hrep _ (hφP x hxP) with h | h
        · exact absurd h hgxZ
        · exact h
      refine commute_of_sq_of_odd (commute_sq_of_conj ?_) (hcm x hxP) hodd
      calc g * (g * x * g⁻¹) * g⁻¹ = g * (x * c) * g⁻¹ := by rw [hxc]
        _ = (g * x * g⁻¹) * (g * c * g⁻¹) := by group
        _ = x * c * c := by rw [hxc, hconj (hgZ c hc)]
        _ = x := by rw [mul_assoc, hZ2 c hc, mul_one]
    rw [mem_centralizer_iff]
    intro p hp
    rcases hrep p hp with hpZ | ⟨c, hc, rfl⟩
    · exact (hgZ p hpZ).eq.symm
    · exact (hgx.mul_right (hgZ c hc)).eq.symm
  have hcompl := MonoidHom.ker_transferSylow_isComplement' P hNC
  have hcard := hcompl.card_mul_card
  rcases (MonoidHom.normal_ker (MonoidHom.transferSylow P hNC)).eq_bot_or_eq_top with h | h
  · rw [h, Subgroup.card_bot, one_mul] at hcard
    have hPtop : (P : Subgroup F) = ⊤ := Subgroup.eq_top_of_card_eq _ hcard
    obtain ⟨a, d, had⟩ := hnab
    exact had (hPc a (hPtop ▸ mem_top a) d (hPtop ▸ mem_top d)).eq
  · rw [h, Subgroup.card_top, h8] at hcard
    have : 0 < Nat.card F := Nat.card_pos
    omega

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FStar
