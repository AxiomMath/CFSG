module

public import CFSG.GH74.GLS.Stage4.RestL92B

public section

namespace CFSG.GH74.GLS.Stage4.Rest.L92

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.Stage4.Hex
  CFSG.GH74.GLS.Stage4.Rest CFSG.GH74.GLS.Stage4.Rest.DodecA CFSG.GH74.BNPair
open scoped Pointwise

variable {G : Type} [Group G]

theorem chainProd_append (A : ℤ → Subgroup G) (l₁ l₂ : List ℤ) :
    chainProd A (l₁ ++ l₂) = chainProd A l₁ * chainProd A l₂ := by
  simp [chainProd, List.map_append, List.prod_append]

theorem one_mem_chainProd (A : ℤ → Subgroup G) : ∀ l : List ℤ, (1 : G) ∈ chainProd A l
  | [] => by simp [chainProd]
  | k :: l => by
    rw [chainProd_cons]
    exact ⟨1, (A k).one_mem, 1, one_mem_chainProd A l, by simp⟩

theorem chainProd_subset {A : ℤ → Subgroup G} {Z : Subgroup G} :
    ∀ l : List ℤ, (∀ i ∈ l, A i ≤ Z) → chainProd A l ⊆ (Z : Set G)
  | [], _ => by
    intro x hx
    simp only [chainProd, List.map_nil, List.prod_nil, Set.mem_one] at hx
    rw [hx]
    exact Z.one_mem
  | k :: l, h => by
    rw [chainProd_cons]
    rintro _ ⟨a, ha, b, hb, rfl⟩
    exact Z.mul_mem (h k (by simp) ha) (chainProd_subset l (fun i hi => h i (by simp [hi])) hb)

@[expose] def relCenter (Z N : Subgroup G) (hN : ∀ g ∈ Z, ∀ n ∈ N, g * n * g⁻¹ ∈ N) : Subgroup G where
  carrier := {x | x ∈ Z ∧ ∀ w ∈ Z, x * w * x⁻¹ * w⁻¹ ∈ N}
  one_mem' := ⟨Z.one_mem, fun w _ => by simp⟩
  mul_mem' := by
    rintro x y ⟨hx, hxc⟩ ⟨hy, hyc⟩
    refine ⟨Z.mul_mem hx hy, fun w hw => ?_⟩
    have e : x * y * w * (x * y)⁻¹ * w⁻¹ =
        (x * (y * w * y⁻¹ * w⁻¹) * x⁻¹) * (x * w * x⁻¹ * w⁻¹) := by group
    rw [e]
    exact N.mul_mem (hN x hx _ (hyc w hw)) (hxc w hw)
  inv_mem' := by
    rintro x ⟨hx, hxc⟩
    refine ⟨Z.inv_mem hx, fun w hw => ?_⟩
    have e : x⁻¹ * w * x⁻¹⁻¹ * w⁻¹ = x⁻¹ * (x * w * x⁻¹ * w⁻¹)⁻¹ * x⁻¹⁻¹ := by group
    rw [e]
    exact hN x⁻¹ (Z.inv_mem hx) _ (N.inv_mem (hxc w hw))

theorem relCenter_le {Z N : Subgroup G} {hN : ∀ g ∈ Z, ∀ n ∈ N, g * n * g⁻¹ ∈ N} :
    relCenter Z N hN ≤ Z := fun _ hx => hx.1

theorem le_relCenter {Z N : Subgroup G} (hNZ : N ≤ Z) {hN : ∀ g ∈ Z, ∀ n ∈ N, g * n * g⁻¹ ∈ N} :
    N ≤ relCenter Z N hN := by
  intro n hn
  refine ⟨hNZ hn, fun w hw => ?_⟩
  have e : n * w * n⁻¹ * w⁻¹ = n * (w * n⁻¹ * w⁻¹) := by group
  rw [e]
  exact N.mul_mem hn (hN w hw _ (N.inv_mem hn))

theorem hinv_relCenter {H Z N : Subgroup G} {hN : ∀ g ∈ Z, ∀ n ∈ N, g * n * g⁻¹ ∈ N}
    (hZ : HInv H Z) (hNH : HInv H N) : HInv H (relCenter Z N hN) := by
  rintro h hh x ⟨hx, hxc⟩
  refine ⟨hZ h hh x hx, fun w hw => ?_⟩
  have hw' : h⁻¹ * w * h⁻¹⁻¹ ∈ Z := hZ h⁻¹ (H.inv_mem hh) w hw
  have e : h * x * h⁻¹ * w * (h * x * h⁻¹)⁻¹ * w⁻¹ =
      h * (x * (h⁻¹ * w * h⁻¹⁻¹) * x⁻¹ * (h⁻¹ * w * h⁻¹⁻¹)⁻¹) * h⁻¹ := by group
  rw [e]
  exact hNH h hh _ (hxc _ hw')

theorem exists_mem_relCenter_not_mem {p : ℕ} [Fact p.Prime] [Finite G] {Z N : Subgroup G}
    (hZp : IsPGroup p ↥Z) (hNZ : N ≤ Z) (hN : ∀ g ∈ Z, ∀ n ∈ N, g * n * g⁻¹ ∈ N) (hlt : N ≠ Z) :
    ∃ x ∈ Z, x ∉ N ∧ ∀ w ∈ Z, x * w * x⁻¹ * w⁻¹ ∈ N := by
  have hnorm : (N.subgroupOf Z).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have := hN g g.2 n hn
    exact this
  have hQp : IsPGroup p (↥Z ⧸ N.subgroupOf Z) := hZp.to_quotient _
  have hQnt : Nontrivial (↥Z ⧸ N.subgroupOf Z) := by
    rw [QuotientGroup.nontrivial_iff]
    intro h
    apply hlt
    apply le_antisymm hNZ
    intro x hx
    have : (⟨x, hx⟩ : ↥Z) ∈ N.subgroupOf Z := by rw [h]; exact Subgroup.mem_top _
    exact this
  have hQfin : Finite (↥Z ⧸ N.subgroupOf Z) := inferInstance
  have hc := hQp.center_nontrivial
  obtain ⟨⟨c, hcC⟩, hc1⟩ := exists_ne (1 : ↥(Subgroup.center (↥Z ⧸ N.subgroupOf Z)))
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
  refine ⟨x, x.2, fun hxN => hc1 ?_, fun w hw => ?_⟩
  · apply Subtype.ext
    show (QuotientGroup.mk x : ↥Z ⧸ N.subgroupOf Z) = 1
    rw [QuotientGroup.eq_one_iff]
    exact hxN
  · have hcomm := Subgroup.mem_center_iff.1 hcC (QuotientGroup.mk ⟨w, hw⟩)
    have h1 : QuotientGroup.mk (x * ⟨w, hw⟩ * x⁻¹ * ⟨w, hw⟩⁻¹ : ↥Z) =
        (1 : ↥Z ⧸ N.subgroupOf Z) := by
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
      exact hcomm.symm
    rw [QuotientGroup.eq_one_iff] at h1
    exact h1

@[expose] def mulSub (N Y : Subgroup G) (hY : ∀ y ∈ Y, ∀ n ∈ N, y * n * y⁻¹ ∈ N) : Subgroup G where
  carrier := {x | ∃ n ∈ N, ∃ y ∈ Y, x = n * y}
  one_mem' := ⟨1, N.one_mem, 1, Y.one_mem, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨n, hn, y, hy, rfl⟩ ⟨n', hn', y', hy', rfl⟩
    refine ⟨n * (y * n' * y⁻¹), N.mul_mem hn (hY y hy n' hn'), y * y', Y.mul_mem hy hy', ?_⟩
    group
  inv_mem' := by
    rintro _ ⟨n, hn, y, hy, rfl⟩
    refine ⟨y⁻¹ * n⁻¹ * y⁻¹⁻¹, ?_, y⁻¹, Y.inv_mem hy, by group⟩
    exact hY y⁻¹ (Y.inv_mem hy) _ (N.inv_mem hn)

theorem le_mulSub_left {N Y : Subgroup G} {hY : ∀ y ∈ Y, ∀ n ∈ N, y * n * y⁻¹ ∈ N} :
    N ≤ mulSub N Y hY := fun n hn => ⟨n, hn, 1, Y.one_mem, by simp⟩

theorem le_mulSub_right {N Y : Subgroup G} {hY : ∀ y ∈ Y, ∀ n ∈ N, y * n * y⁻¹ ∈ N} :
    Y ≤ mulSub N Y hY := fun y hy => ⟨1, N.one_mem, y, hy, by simp⟩

theorem hinv_mulSub {H N Y : Subgroup G} {hY : ∀ y ∈ Y, ∀ n ∈ N, y * n * y⁻¹ ∈ N}
    (hNH : HInv H N) (hYH : HInv H Y) : HInv H (mulSub N Y hY) := by
  rintro h hh _ ⟨n, hn, y, hy, rfl⟩
  exact ⟨h * n * h⁻¹, hNH h hh n hn, h * y * h⁻¹, hYH h hh y hy, by group⟩

theorem card_mulSub {N Y : Subgroup G} {hY : ∀ y ∈ Y, ∀ n ∈ N, y * n * y⁻¹ ∈ N}
    (hNY : N ⊓ Y = ⊥) :
    Nat.card ↥(mulSub N Y hY) = Nat.card ↥N * Nat.card ↥Y := by
  rw [← Nat.card_prod]
  refine (Nat.card_congr (Equiv.ofBijective
    (fun p : ↥N × ↥Y => (⟨(p.1 : G) * (p.2 : G), p.1, p.1.2, p.2, p.2.2, rfl⟩ : ↥(mulSub N Y hY)))
    ⟨?_, ?_⟩)).symm
  · rintro ⟨⟨n, hn⟩, ⟨y, hy⟩⟩ ⟨⟨n', hn'⟩, ⟨y', hy'⟩⟩ h
    have h1 : n * y = n' * y' := congrArg Subtype.val h
    have h2 : n'⁻¹ * n = y' * y⁻¹ := by
      calc n'⁻¹ * n = n'⁻¹ * (n * y) * y⁻¹ := by group
        _ = n'⁻¹ * (n' * y') * y⁻¹ := by rw [h1]
        _ = y' * y⁻¹ := by group
    have h3 : n'⁻¹ * n ∈ N ⊓ Y :=
      ⟨N.mul_mem (N.inv_mem hn') hn, by rw [h2]; exact Y.mul_mem hy' (Y.inv_mem hy)⟩
    rw [hNY, Subgroup.mem_bot] at h3
    have hn2 : n' = n := inv_mul_eq_one.1 h3
    subst hn2
    have : y = y' := mul_left_cancel h1
    subst this
    rfl
  · rintro ⟨_, n, hn, y, hy, rfl⟩
    exact ⟨(⟨n, hn⟩, ⟨y, hy⟩), rfl⟩

section Main

variable {p : ℕ} {H P : Subgroup G} {z u : G} {R : ℤ → Subgroup G}

open Classical in
@[expose] noncomputable def Jset (R : ℤ → Subgroup G) (Z : Subgroup G) : Finset ℤ :=
  (Finset.Icc (1 : ℤ) 6).filter fun i => R i ≤ Z

theorem mem_Jset {R : ℤ → Subgroup G} {Z : Subgroup G} {i : ℤ} :
    i ∈ Jset R Z ↔ 1 ≤ i ∧ i ≤ 6 ∧ R i ≤ Z := by
  unfold Jset
  simp [Finset.mem_filter, Finset.mem_Icc, and_assoc]

theorem Jset_mono {R : ℤ → Subgroup G} {N Z : Subgroup G} (h : N ≤ Z) : Jset R N ⊆ Jset R Z := by
  intro i hi
  obtain ⟨a, b, c⟩ := mem_Jset.1 hi
  exact mem_Jset.2 ⟨a, b, c.trans h⟩

theorem L92Data.card_eq_prod [Finite G] (hd : L92Data p H P z u R) {Z : Subgroup G} (hZP : Z ≤ P)
    (hZ : HInv H Z) : Nat.card ↥Z = ∏ i ∈ Jset R Z, Nat.card ↥(R i) := by
  classical
  obtain ⟨hdich, hcard⟩ := hd.card_eq hZP hZ
  have hinf : ∀ i : ℤ, 1 ≤ i → i ≤ 6 →
      Nat.card ↥(Z ⊓ R i) = if R i ≤ Z then Nat.card ↥(R i) else 1 := by
    intro i h1 h6
    by_cases hle : R i ≤ Z
    · simp only [hle, ↓reduceIte]
      rw [inf_eq_right.2 hle]
    · simp only [hle, ↓reduceIte]
      rcases hdich i h1 h6 with h | h
      · rw [h]
        exact Subgroup.card_bot
      · exact absurd (h ▸ inf_le_left) hle
  have hprod : ∏ i ∈ Jset R Z, Nat.card ↥(R i) =
      ∏ i ∈ Finset.Icc (1 : ℤ) 6, if R i ≤ Z then Nat.card ↥(R i) else 1 := by
    unfold Jset
    rw [Finset.prod_filter]
  have hIcc : Finset.Icc (1 : ℤ) 6 = {1, 2, 3, 4, 5, 6} := by decide
  rw [hprod, hIcc, hcard, Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton, hinf 1 (by norm_num) (by norm_num), hinf 2 (by norm_num) (by norm_num),
    hinf 3 (by norm_num) (by norm_num), hinf 4 (by norm_num) (by norm_num),
    hinf 5 (by norm_num) (by norm_num), hinf 6 (by norm_num) (by norm_num)]
  ring

theorem L92Data.two_le_card [Finite G] (hd : L92Data p H P z u R) {i : ℤ} (h1 : 1 ≤ i) (h6 : i ≤ 6) :
    2 ≤ Nat.card ↥(R i) := by
  have := (Subgroup.one_lt_card_iff_ne_bot (R i)).2 (hd.ne_bot i h1 h6)
  omega

theorem L92Data.Jset_mulSub [Finite G] (hd : L92Data p H P z u R) {N : Subgroup G} (hNP : N ≤ P)
    (hN : HInv H N) {e : ℤ} (he1 : 1 ≤ e) (he6 : e ≤ 6) (heN : ¬ R e ≤ N)
    {hY : ∀ y ∈ R e, ∀ n ∈ N, y * n * y⁻¹ ∈ N} (hN'P : mulSub N (R e) hY ≤ P) :
    Jset R (mulSub N (R e) hY) = insert e (Jset R N) := by
  classical
  have heJ : e ∉ Jset R N := fun h => heN (mem_Jset.1 h).2.2
  have hN'H : HInv H (mulSub N (R e) hY) := hinv_mulSub hN (hd.inv e he1 he6)
  apply Finset.Subset.antisymm
  · intro i hi
    by_contra hcon
    have hie : i ≠ e := fun h => hcon (h ▸ Finset.mem_insert_self _ _)
    have hiJ : i ∉ Jset R N := fun h => hcon (Finset.mem_insert_of_mem h)
    obtain ⟨hi1, hi6, -⟩ := mem_Jset.1 hi
    have hNbot : N ⊓ R e = ⊥ := by
      rcases (hd.irr e he1 he6).inf (hd.inv e he1 he6) hN with h | h
      · exact h
      · exact absurd (h ▸ inf_le_left) heN
    have hcardN' := hd.card_eq_prod hN'P hN'H
    have hcardN := hd.card_eq_prod hNP hN
    have hcardMul := card_mulSub (hY := hY) hNbot
    have hsub : insert i (insert e (Jset R N)) ⊆ Jset R (mulSub N (R e) hY) := by
      intro j hj
      rcases Finset.mem_insert.1 hj with rfl | hj
      · exact hi
      rcases Finset.mem_insert.1 hj with rfl | hj
      · exact mem_Jset.2 ⟨he1, he6, le_mulSub_right⟩
      · exact Jset_mono le_mulSub_left hj
    have hle := Finset.prod_le_prod_of_subset_of_one_le (f := fun j => Nat.card ↥(R j)) hsub
      (fun j _ _ => Nat.card_pos)
    have hnot : i ∉ insert e (Jset R N) := by
      intro h
      rcases Finset.mem_insert.1 h with h | h
      · exact hie h
      · exact hiJ h
    rw [Finset.prod_insert hnot, Finset.prod_insert heJ, ← hcardN', hcardMul, hcardN] at hle
    have hA : 1 ≤ ∏ j ∈ Jset R N, Nat.card ↥(R j) :=
      Nat.one_le_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 (fun j _ => Nat.card_pos.ne'))
    have hi2 := hd.two_le_card hi1 hi6
    have he2 := hd.two_le_card he1 he6
    generalize (∏ j ∈ Jset R N, Nat.card ↥(R j)) = A at hle hA
    generalize Nat.card ↥(R i) = c at hle hi2
    generalize Nat.card ↥(R e) = b at hle he2
    nlinarith [Nat.mul_le_mul_right (b * A) hi2, Nat.mul_le_mul he2 hA]
  · intro i hi
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact mem_Jset.2 ⟨he1, he6, le_mulSub_right⟩
    · exact Jset_mono le_mulSub_left hi

theorem L92Data.subset_chainProd_mul [Finite G] (hd : L92Data p H P z u R) :
    ∀ (k : ℕ) (Z N : Subgroup G), Z ≤ P → HInv H Z → N ≤ Z → HInv H N →
      (∀ g ∈ Z, ∀ n ∈ N, g * n * g⁻¹ ∈ N) → Nat.card ↥Z - Nat.card ↥N = k →
      ∀ m : List ℤ, m.Nodup → (∀ i, i ∈ m ↔ 1 ≤ i ∧ i ≤ 6 ∧ R i ≤ Z ∧ ¬ R i ≤ N) →
      (Z : Set G) ⊆ chainProd R m * (N : Set G) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro Z N hZP hZ hNZ hN hNn hk m hmnd hm
    by_cases hZN : N = Z
    · subst hZN
      intro x hx
      exact ⟨1, one_mem_chainProd R m, x, hx, by simp⟩
    have hZp : IsPGroup p ↥Z := hd.P_pGroup.to_le hZP
    have := Fact.mk hd.prime
    obtain ⟨x, hxZ, hxN, hxc⟩ := exists_mem_relCenter_not_mem hZp hNZ hNn hZN
    have hÑH : HInv H (relCenter Z N hNn) := hinv_relCenter hZ hN
    have hNÑ : N ≤ relCenter Z N hNn := le_relCenter hNZ
    have hÑZ : relCenter Z N hNn ≤ Z := relCenter_le
    have hex : ∃ e ∈ Jset R (relCenter Z N hNn), e ∉ Jset R N := by
      by_contra hcon
      have heq : Jset R (relCenter Z N hNn) = Jset R N :=
        Finset.Subset.antisymm (fun i hi => by_contra fun h => hcon ⟨i, hi, h⟩) (Jset_mono hNÑ)
      have hc1 := hd.card_eq_prod (hÑZ.trans hZP) hÑH
      have hc2 := hd.card_eq_prod (hNZ.trans hZP) hN
      have hceq : Nat.card ↥(relCenter Z N hNn) = Nat.card ↥N := by rw [hc1, hc2, heq]
      have hNeq : N = relCenter Z N hNn := Subgroup.eq_of_le_of_card_ge hNÑ hceq.le
      exact hxN (hNeq ▸ ⟨hxZ, hxc⟩)
    obtain ⟨e, heÑ, heN⟩ := hex
    obtain ⟨he1, he6, heleÑ⟩ := mem_Jset.1 heÑ
    have heN' : ¬ R e ≤ N := fun h => heN (mem_Jset.2 ⟨he1, he6, h⟩)
    have hReZ : R e ≤ Z := heleÑ.trans hÑZ
    have hY : ∀ y ∈ R e, ∀ n ∈ N, y * n * y⁻¹ ∈ N := fun y hy n hn => hNn y (hReZ hy) n hn
    have hN'H : HInv H (mulSub N (R e) hY) := hinv_mulSub hN (hd.inv e he1 he6)
    have hN'Z : mulSub N (R e) hY ≤ Z := by
      rintro _ ⟨n, hn, y, hy, rfl⟩
      exact Z.mul_mem (hNZ hn) (hReZ hy)
    have hN'n : ∀ g ∈ Z, ∀ x ∈ mulSub N (R e) hY, g * x * g⁻¹ ∈ mulSub N (R e) hY := by
      rintro g hg _ ⟨n, hn, y, hy, rfl⟩
      have hyÑ : y ∈ relCenter Z N hNn := heleÑ hy
      have hc : g * y * g⁻¹ * y⁻¹ ∈ N := by
        have e : g * y * g⁻¹ * y⁻¹ = (y * g * y⁻¹ * g⁻¹)⁻¹ := by group
        rw [e]
        exact N.inv_mem (hyÑ.2 g hg)
      refine ⟨(g * n * g⁻¹) * (g * y * g⁻¹ * y⁻¹), N.mul_mem (hNn g hg n hn) hc, y, hy, ?_⟩
      group
    have hNbot : N ⊓ R e = ⊥ := by
      rcases (hd.irr e he1 he6).inf (hd.inv e he1 he6) hN with h | h
      · exact h
      · exact absurd (h ▸ inf_le_left) heN'
    have hcardMul := card_mulSub (hY := hY) hNbot
    have hJ' := hd.Jset_mulSub (hNZ.trans hZP) hN he1 he6 heN' (hY := hY) (hN'Z.trans hZP)
    have heme : e ∈ m := (hm e).2 ⟨he1, he6, hReZ, heN'⟩
    obtain ⟨m₁, m₂, hmeq⟩ := List.append_of_mem heme
    have hnd := hmnd
    rw [hmeq, List.nodup_append, List.nodup_cons] at hnd
    obtain ⟨hnd1, ⟨hem2, hnd2⟩, hdisj⟩ := hnd
    have hem1 : e ∉ m₁ := fun h => hdisj e h e (List.mem_cons_self) rfl
    have hm'nd : (m₁ ++ m₂).Nodup := by
      rw [List.nodup_append]
      exact ⟨hnd1, hnd2, fun a ha b hb => hdisj a ha b (List.mem_cons_of_mem e hb)⟩
    have hm' : ∀ i, i ∈ m₁ ++ m₂ ↔ 1 ≤ i ∧ i ≤ 6 ∧ R i ≤ Z ∧ ¬ R i ≤ mulSub N (R e) hY := by
      intro i
      have hmi := hm i
      rw [hmeq] at hmi
      simp only [List.mem_append, List.mem_cons] at hmi ⊢
      have hJi : (1 ≤ i ∧ i ≤ 6 ∧ R i ≤ mulSub N (R e) hY) ↔
          i = e ∨ (1 ≤ i ∧ i ≤ 6 ∧ R i ≤ N) := by
        have := Finset.ext_iff.1 hJ' i
        simpa [mem_Jset] using this
      constructor
      · intro hi
        have hne : i ≠ e := by
          rintro rfl
          rcases hi with hi | hi
          · exact hem1 hi
          · exact hem2 hi
        have hi' : i ∈ m₁ ∨ i = e ∨ i ∈ m₂ := by
          rcases hi with hi | hi
          · exact Or.inl hi
          · exact Or.inr (Or.inr hi)
        obtain ⟨h1, h6, hZi, hNi⟩ := hmi.1 (by
          rcases hi' with h | h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr h))
        refine ⟨h1, h6, hZi, fun hle => ?_⟩
        rcases hJi.1 ⟨h1, h6, hle⟩ with h | h
        · exact hne h
        · exact hNi h.2.2
      · rintro ⟨h1, h6, hZi, hNi'⟩
        have hNi : ¬ R i ≤ N := fun h => hNi' (h.trans le_mulSub_left)
        have hne : i ≠ e := fun h => hNi' (h ▸ le_mulSub_right)
        rcases hmi.2 ⟨h1, h6, hZi, hNi⟩ with h | h | h
        · exact Or.inl h
        · exact absurd h hne
        · exact Or.inr h
    have hcardlt : Nat.card ↥Z - Nat.card ↥(mulSub N (R e) hY) < k := by
      have h2 := hd.two_le_card he1 he6
      have hNpos : 0 < Nat.card ↥N := Nat.card_pos
      have hle : Nat.card ↥(mulSub N (R e) hY) ≤ Nat.card ↥Z := Subgroup.card_le_of_le hN'Z
      rw [hcardMul] at hle ⊢
      have : Nat.card ↥N < Nat.card ↥N * Nat.card ↥(R e) := by nlinarith
      omega
    have hIH := ih _ hcardlt Z (mulSub N (R e) hY) hZP hZ hN'Z hN'H hN'n rfl (m₁ ++ m₂) hm'nd hm'
    intro w hw
    obtain ⟨c, hc, n', hn', rfl⟩ := hIH hw
    rw [chainProd_append] at hc
    obtain ⟨a, ha, b, hb, rfl⟩ := hc
    obtain ⟨n, hn, y, hy, rfl⟩ := hn'
    have hbZ : b ∈ Z := by
      refine chainProd_subset m₂ (fun i hi => ?_) hb
      have := (hm i).1 (by rw [hmeq]; simp [hi])
      exact this.2.2.1
    have hyZ : y ∈ Z := hReZ hy
    have hyc : y * b * y⁻¹ * b⁻¹ ∈ N := (heleÑ hy).2 b hbZ
    have hg1 : b⁻¹ * y⁻¹ * b ∈ Z := Z.mul_mem (Z.mul_mem (Z.inv_mem hbZ) (Z.inv_mem hyZ)) hbZ
    have hn3 : (b⁻¹ * y⁻¹ * b) * n * (b⁻¹ * y⁻¹ * b)⁻¹ ∈ N := hNn _ hg1 n hn
    have hd' : (y * b)⁻¹ * (y * b * y⁻¹ * b⁻¹)⁻¹ * ((y * b)⁻¹)⁻¹ ∈ N :=
      hNn _ (Z.inv_mem (Z.mul_mem hyZ hbZ)) _ (N.inv_mem hyc)
    refine ⟨a * (y * b), ?_, ((b⁻¹ * y⁻¹ * b) * n * (b⁻¹ * y⁻¹ * b)⁻¹) *
      ((y * b)⁻¹ * (y * b * y⁻¹ * b⁻¹)⁻¹ * ((y * b)⁻¹)⁻¹), N.mul_mem hn3 hd', ?_⟩
    · rw [hmeq, chainProd_append, chainProd_cons]
      exact ⟨a, ha, y * b, ⟨y, hy, b, hb, rfl⟩, rfl⟩
    · group

theorem L92Data.eq_chainProd [Finite G] (hd : L92Data p H P z u R) {Z : Subgroup G} (hZP : Z ≤ P)
    (hZ : HInv H Z) (l : List ℤ) (hl : l.Nodup)
    (hlmem : ∀ i, i ∈ l ↔ 1 ≤ i ∧ i ≤ 6 ∧ R i ≤ Z) :
    (Z : Set G) = chainProd R l ∧ Nat.card ↥Z = (l.map fun i => Nat.card ↥(R i)).prod := by
  classical
  refine ⟨?_, ?_⟩
  · apply Set.Subset.antisymm
    · have h := hd.subset_chainProd_mul _ Z ⊥ hZP hZ bot_le (hinv_bot H)
        (fun g _ n hn => by
          rw [Subgroup.mem_bot] at hn ⊢
          simp [hn]) rfl l hl (fun i => by
          rw [hlmem i]
          constructor
          · rintro ⟨h1, h6, hle⟩
            exact ⟨h1, h6, hle, fun hb => hd.ne_bot i h1 h6 (le_bot_iff.1 hb)⟩
          · rintro ⟨h1, h6, hle, -⟩
            exact ⟨h1, h6, hle⟩)
      intro x hx
      obtain ⟨c, hc, b, hb, rfl⟩ := h hx
      have : b = 1 := by simpa using hb
      simpa [this] using hc
    · exact chainProd_subset l (fun i hi => ((hlmem i).1 hi).2.2)
  · rw [hd.card_eq_prod hZP hZ]
    have hJ : Jset R Z = l.toFinset := by
      ext i
      rw [mem_Jset, List.mem_toFinset, hlmem]
    rw [hJ, List.prod_toFinset _ hl]

end Main

end CFSG.GH74.GLS.Stage4.Rest.L92
