module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87AltOrb
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87AltPerm

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87.AltCore

open Equiv Equiv.Perm Subgroup CFSG.GH74.GLS.Stage2.Signalizer.Odd87.AltOrb
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87.AltPerm

variable {α : Type*} [Fintype α] [DecidableEq α]

@[expose] def Moved (y : Perm α) : Finset α := Finset.univ.filter fun c => y c ≠ c

theorem mem_Moved {y : Perm α} {c : α} : c ∈ Moved y ↔ y c ≠ c := by simp [Moved]

omit [Fintype α] [DecidableEq α] in
theorem Moved_stable {y : Perm α} (hy : y * y = 1) {c : α} (hc : y c ≠ c) : y (y c) ≠ y c := by
  rw [yy hy]; exact fun h => hc h.symm

omit [Fintype α] in
theorem exists_moved_in_support {y x : Perm α} (hy : y * y = 1) (hxy : x * y ≠ y * x) :
    ∃ a, y a ≠ a ∧ x a ≠ a := by
  by_contra h
  push Not at h
  apply hxy
  ext w
  rw [Perm.mul_apply, Perm.mul_apply]
  by_cases hw : y w = w
  · have hxw : y (x w) = x w := by
      by_contra hne
      have h1 := h (x w) hne
      have h2 : x w = w := x.injective (by rw [h1])
      apply hne
      rw [h2, hw]
    rw [hw, hxw]
  · have h1 : x w = w := h w hw
    have h2 : x (y w) = y w := h (y w) (Moved_stable hy hw)
    rw [h2, h1]

omit [Fintype α] [DecidableEq α] in
theorem odd_orderOf_of_pow_three {g : Perm α} (h : g ^ 3 = 1) : Odd (orderOf g) :=
  Odd.of_dvd_nat (by decide : Odd 3) (orderOf_dvd_of_pow_eq_one h)

section Members

variable {X : Subgroup (Perm α)} {y : Perm α}

theorem V_mem (hy : y * y = 1)
    (hD : ∀ v : Perm α, Odd (orderOf v) → v * y = y * v → v ∈ normalizer (X : Set (Perm α)))
    {a b e : α} (h : Trip y a b e) : V y a b e ∈ normalizer (X : Set (Perm α)) :=
  hD _ (odd_orderOf_of_pow_three (V_pow_three hy h)) (V_mul_comm hy h)

theorem U_mem (hy : y * y = 1)
    (hD : ∀ v : Perm α, Odd (orderOf v) → v * y = y * v → v ∈ normalizer (X : Set (Perm α)))
    {a b e : α} (h : Trip y a b e) : U y a b ∈ normalizer (X : Set (Perm α)) := by
  rw [U_eq_comm hy h]
  refine Subgroup.mul_mem _ ?_ (Subgroup.inv_mem _ (V_mem hy hD h))
  apply hD
  · refine odd_orderOf_of_pow_three ?_
    rw [conj_pow, V_pow_three hy h]
    group
  · have hc1 : Commute (swap a (y a)) y := swap_mul_comm hy
    have hc2 : Commute (V y a b e) y := V_mul_comm hy h
    exact (((hc1.mul_left hc2).mul_left hc1.inv_left)).eq

theorem c3_mem
    (hD : ∀ v : Perm α, Odd (orderOf v) → v * y = y * v → v ∈ normalizer (X : Set (Perm α)))
    {a b e : α} (hab : a ≠ b) (hbe : b ≠ e) (hae : a ≠ e) (ha : y a = a) (hb : y b = b)
    (he : y e = e) : c3 a b e ∈ normalizer (X : Set (Perm α)) :=
  hD _ (odd_orderOf_of_pow_three (c3_pow_three hab hbe hae)) (c3_mul_comm_of_fixed ha hb he)

end Members

section Exist

variable {y : Perm α}

theorem exists_second (h5 : 5 ≤ (Moved y).card) {a : α} :
    ∃ b, y b ≠ b ∧ b ≠ a ∧ b ≠ y a := by
  by_contra hcon
  push Not at hcon
  have hsub : Moved y ⊆ {a, y a} := fun c hc => by
    by_contra hne
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hne
    exact absurd (hcon c (mem_Moved.mp hc) hne.1) (by simpa using hne.2)
  have := Finset.card_le_card hsub
  have h2 := Finset.card_le_two (a := a) (b := y a)
  omega

theorem exists_third (h5 : 5 ≤ (Moved y).card) {a b : α} (ha : y a ≠ a) (hb : y b ≠ b)
    (hba : b ≠ a) (hbya : b ≠ y a) : ∃ e, Trip y a b e := by
  by_contra hcon
  push Not at hcon
  have hsub : Moved y ⊆ {a, y a, b, y b} := fun c hc => by
    by_contra hne
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hne
    exact hcon c ⟨ha, hb, mem_Moved.mp hc, hba, hbya, hne.1, hne.2.1, hne.2.2.1, hne.2.2.2⟩
  have := Finset.card_le_card hsub
  have h2 := Finset.card_le_four (a := a) (b := y a) (c := b) (d := y b)
  omega

end Exist

omit [Fintype α] [DecidableEq α] in
theorem p_dvd_four {p : ℕ} (hp : p.Prime) (h : p ∣ 4) : p = 2 :=
  (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
    (hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 by simpa using h))

section Small

variable {p : ℕ} [Fact p.Prime] {X : Subgroup (Perm α)} {y : Perm α}

theorem core_small (hα : 7 ≤ Fintype.card α) (hp : p ≠ 2) (hX : IsPGroup p ↥X) (hy : y * y = 1)
    (hyN : y ∈ normalizer (X : Set (Perm α)))
    (hD : ∀ v : Perm α, Odd (orderOf v) → v * y = y * v → v ∈ normalizer (X : Set (Perm α)))
    (hsmall : (Moved y).card ≤ 4) {a : α} (ha : y a ≠ a) {x : Perm α} (hxX : x ∈ X)
    (hxa : x a ≠ a) : False := by
  classical
  have hyy : ∀ b, y (y b) = b := yy hy
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp
  have hO3 : 3 ≤ (Orb X a).ncard := three_le_ncard_Orb hp hX hxX hxa
  obtain ⟨k, hk⟩ := ncard_Orb_pow hX a
  have hOodd : Odd (Orb X a).ncard := by rw [hk]; exact hpodd.pow
  by_cases hfixO : ∃ φ ∈ Orb X a, y φ = φ
  · obtain ⟨φ, hφO, hφ⟩ := hfixO
    have hyφ : y φ ∈ Orb X a := by rw [hφ]; exact hφO
    have himg : y '' Orb X a = Orb X a := image_Orb_eq_self hyN hφO hyφ
    have hmem : ∀ b ∈ Orb X a, y b ∈ Orb X a := fun b hb => by
      rw [← himg]; exact Set.mem_image_of_mem y hb
    have hya : y a ∈ Orb X a := hmem a (mem_Orb_self X a)
    obtain ⟨j, hj⟩ := ncard_fixed_Orb hp hX hy hyN hya
    set F : Set α := {b | b ∈ Orb X a ∧ y b = b} with hF
    have hFO : F ⊆ Orb X a := fun b hb => hb.1
    set M : Set α := Orb X a \ F with hM
    have hsum := Set.ncard_sdiff_add_ncard_of_subset hFO (Set.toFinite _)
    have hMmem : ∀ c ∈ M, y c ≠ c := fun c hc h => hc.2 ⟨hc.1, h⟩
    have hMstab : ∀ c ∈ M, y c ∈ M := fun c hc => by
      refine ⟨hmem c hc.1, fun h => ?_⟩
      apply hMmem c hc
      have := h.2
      rw [hyy] at this
      exact this.symm
    have heven : Even M.ncard := even_ncard_of_fixedpointfree (Set.toFinite _) hyy hMstab hMmem
    have haM : a ∈ M := ⟨mem_Orb_self X a, fun h => ha h.2⟩
    have hMpos : 1 ≤ M.ncard := by
      rw [Nat.one_le_iff_ne_zero]
      intro h0
      rw [Set.ncard_eq_zero (Set.toFinite _)] at h0
      rw [h0] at haM
      exact haM
    have hMsub : M ⊆ (Moved y : Set α) := fun c hc => by
      rw [Finset.mem_coe, mem_Moved]; exact hMmem c hc
    have hM4 : M.ncard ≤ 4 := by
      have := Set.ncard_le_ncard hMsub (Set.toFinite _)
      rw [Set.ncard_coe_finset] at this
      omega
    have heq : p ^ k = M.ncard + p ^ j := by
      rw [← hk, ← hj]; exact hsum.symm
    have hp3 : 3 ≤ p := by
      have := (Fact.out : p.Prime).two_le
      omega
    have hj0 : j = 0 := by
      by_contra hj0
      have hk0 : k ≠ 0 := by
        rintro rfl
        rw [pow_zero] at hk
        omega
      have h1 : p ∣ p ^ k := dvd_pow_self p hk0
      have h2 : p ∣ p ^ j := dvd_pow_self p hj0
      have h3 : p ∣ M.ncard := by
        have : p ∣ M.ncard + p ^ j := heq ▸ h1
        exact (Nat.dvd_add_left h2).mp this
      obtain ⟨r, hr⟩ := heven
      have hm : M.ncard = 2 ∨ M.ncard = 4 := by omega
      rcases hm with hm | hm
      · rw [hm] at h3
        have := Nat.le_of_dvd (by norm_num) h3
        omega
      · rw [hm] at h3
        exact hp (p_dvd_four (Fact.out) h3)
    rw [hj0, pow_zero] at hj
    obtain ⟨c, hFc⟩ := Set.ncard_eq_one.mp hj
    have hφF : φ ∈ F := ⟨hφO, hφ⟩
    have hFeq : F = {φ} := by
      rw [hFc] at hφF ⊢
      rw [Set.mem_singleton_iff] at hφF
      rw [hφF]
    have hΦ : 3 ≤ (Finset.univ.filter fun c : α => y c = c).card := by
      have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset α))
        (fun c : α => y c = c)
      simp only [Finset.card_univ] at this
      have hmv : (Finset.univ.filter fun c : α => ¬ y c = c) = Moved y := by simp [Moved]
      rw [hmv] at this
      omega
    set Φ := Finset.univ.filter fun c : α => y c = c with hΦdef
    have hφΦ : φ ∈ Φ := by simp [Φ, hφ]
    have hcard : 1 < (Φ.erase φ).card := by
      rw [Finset.card_erase_of_mem hφΦ]; omega
    obtain ⟨φ', hφ', φ'', hφ'', hne⟩ := Finset.one_lt_card.mp hcard
    simp only [Finset.mem_erase, Φ, Finset.mem_filter, Finset.mem_univ, true_and] at hφ' hφ''
    have hw := c3_mem hD (a := φ) (b := φ') (e := φ'') hφ'.1.symm hne hφ''.1.symm hφ hφ'.2
      hφ''.2
    have hnaφ : ∀ c, y c = c → a ≠ c := fun c hc h => ha (by rw [h]; exact hc)
    have hwa : c3 φ φ' φ'' a = a :=
      c3_apply_of_ne (hnaφ φ hφ) (hnaφ φ' hφ'.2) (hnaφ φ'' hφ''.2)
    have hwimg := image_Orb_eq_self hw (mem_Orb_self X a) (by rw [hwa]; exact mem_Orb_self X a)
    have hwφ : c3 φ φ' φ'' φ = φ' := c3_apply_left hφ'.1.symm hφ''.1.symm
    have hφ'O : φ' ∈ Orb X a := by
      have h1 : φ' ∈ (c3 φ φ' φ'') '' Orb X a := ⟨φ, hφO, hwφ⟩
      rw [hwimg] at h1
      exact h1
    have hφ'F : φ' ∈ F := ⟨hφ'O, hφ'.2⟩
    rw [hFeq] at hφ'F
    exact hφ'.1 (Set.mem_singleton_iff.mp hφ'F)
  · push Not at hfixO
    have hya : y a ∉ Orb X a := by
      intro hya
      have himg := image_Orb_eq_self hyN (mem_Orb_self X a) hya
      have hmem : ∀ b ∈ Orb X a, y b ∈ Orb X a := fun b hb => by
        rw [← himg]; exact Set.mem_image_of_mem y hb
      obtain ⟨φ, hφO, hφ⟩ := exists_fixed_of_odd (Set.toFinite _) hyy hmem hOodd
      exact hfixO φ hφO hφ
    have hdisj : Disjoint (Orb X a) (y '' Orb X a) := by
      rw [Set.disjoint_left]
      intro c hcO hcy
      rw [image_Orb hyN a] at hcy
      apply hya
      have := Orb_eq_of_mem_inter hcO hcy
      rw [this]
      exact mem_Orb_self X (y a)
    have hsub : Orb X a ∪ y '' Orb X a ⊆ (Moved y : Set α) := by
      intro c hc
      rcases hc with hc | ⟨d, hd, rfl⟩
      · exact mem_Moved.mpr (hfixO c hc)
      · rw [Finset.mem_coe, mem_Moved, hyy]
        exact fun h => hfixO d hd h.symm
    have h1 := Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)
    rw [Set.ncard_image_of_injective _ y.injective] at h1
    have h2 := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_coe_finset] at h2
    omega

end Small

section Big

variable {p : ℕ} [Fact p.Prime] {X : Subgroup (Perm α)} {y : Perm α}

theorem core_big (hp : p ≠ 2) (hX : IsPGroup p ↥X) (hy : y * y = 1)
    (hyN : y ∈ normalizer (X : Set (Perm α)))
    (hD : ∀ v : Perm α, Odd (orderOf v) → v * y = y * v → v ∈ normalizer (X : Set (Perm α)))
    (hbig : 5 ≤ (Moved y).card) {a : α} (ha : y a ≠ a) {x : Perm α} (hxX : x ∈ X)
    (hxa : x a ≠ a) : False := by
  classical
  have hyy : ∀ b, y (y b) = b := yy hy
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp
  have hO3 : 3 ≤ (Orb X a).ncard := three_le_ncard_Orb hp hX hxX hxa
  obtain ⟨k, hk⟩ := ncard_Orb_pow hX a
  have hOodd : Odd (Orb X a).ncard := by rw [hk]; exact hpodd.pow
  obtain ⟨b, hb, hba, hbya⟩ := exists_second hbig (a := a)
  obtain ⟨e, hT⟩ := exists_third hbig ha hb hba hbya
  have S := hT.six hy
  by_cases hfixO : ∃ φ ∈ Orb X a, y φ = φ
  · obtain ⟨φ, hφO, hφ⟩ := hfixO
    have hφS : ∀ c, y c ≠ c → φ ≠ c ∧ φ ≠ y c := fun c hc =>
      ⟨fun h => hc (by rw [← h]; exact hφ), fun h => hc (by
        have h1 := hφ
        rw [h, hyy] at h1
        exact h1.symm)⟩
    have hpres : ∀ d ∈ normalizer (X : Set (Perm α)), d φ = φ → d a ∈ Orb X a := by
      intro d hd hdφ
      have himg := image_Orb_eq_self hd hφO (by rw [hdφ]; exact hφO)
      rw [← himg]
      exact Set.mem_image_of_mem _ (mem_Orb_self X a)
    have hSig : ∀ s, y s ≠ s → s ∈ Orb X a := by
      intro s hs
      by_cases h1 : s = a
      · rw [h1]; exact mem_Orb_self X a
      by_cases h2 : s = y a
      · have hd := U_mem hy hD hT
        have hdφ : U y a b φ = φ :=
          U_apply_of_ne (hφS a ha).1 (hφS a ha).2 (hφS b hb).1 (hφS b hb).2
        have := hpres _ hd hdφ
        rw [U_apply_left hy hT] at this
        rw [h2]; exact this
      · obtain ⟨e', hT'⟩ := exists_third hbig ha hs h1 h2
        have hd := V_mem hy hD hT'
        have hdφ : V y a s e' φ = φ :=
          V_apply_of_ne (hφS a ha).1 (hφS a ha).2 (hφS s hs).1 (hφS s hs).2
            (hφS e' hT'.he).1 (hφS e' hT'.he).2
        have := hpres _ hd hdφ
        rw [V_apply_left hy hT'] at this
        exact this
    have hTr : Trip y b e a := hT.rot hy
    have hu := U_mem hy hD hTr
    have hua : U y b e a = a := U_apply_of_ne S.a_b S.a_yb S.a_e S.a_ye
    have hOmem : U y b e a ∈ Orb X a := by rw [hua]; exact mem_Orb_self X a
    obtain ⟨j, hj⟩ := ncard_fixed_Orb hp hX (U_mul_self hy hTr) hu hOmem
    set F : Set α := {c | c ∈ Orb X a ∧ U y b e c = c} with hF
    set M : Finset α := {b, y b, e, y e} with hMdef
    have hMmoved : ∀ c ∈ M, y c ≠ c := by
      intro c hc
      simp only [hMdef, Finset.mem_insert, Finset.mem_singleton] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact hb
      · exact Moved_stable hy hb
      · exact hT.he
      · exact Moved_stable hy hT.he
    have hMmoved' : ∀ c ∈ M, U y b e c ≠ c := by
      intro c hc
      simp only [hMdef, Finset.mem_insert, Finset.mem_singleton] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · rw [U_apply_left hy hTr]; exact hb
      · rw [U_apply_left' hy hTr]; exact fun h => hb h.symm
      · rw [U_apply_right hy hTr]; exact hT.he
      · rw [U_apply_right' hy hTr]; exact fun h => hT.he h.symm
    have hdecomp : Orb X a = F ∪ (M : Set α) := by
      ext c
      constructor
      · intro hc
        by_cases huc : U y b e c = c
        · exact Or.inl ⟨hc, huc⟩
        · right
          rw [Finset.mem_coe]
          by_contra hcM
          simp only [hMdef, Finset.mem_insert, Finset.mem_singleton, not_or] at hcM
          exact huc (U_apply_of_ne hcM.1 hcM.2.1 hcM.2.2.1 hcM.2.2.2)
      · rintro (hc | hc)
        · exact hc.1
        · exact hSig c (hMmoved c hc)
    have hdisj : Disjoint F (M : Set α) := by
      rw [Set.disjoint_left]
      intro c hcF hcM
      exact hMmoved' c hcM hcF.2
    have hM4 : M.card = 4 := by
      simp [hMdef, Finset.card_insert_of_notMem, S.b_yb, S.b_e, S.b_ye, S.yb_e, S.yb_ye, S.e_ye]
    have hcard : (Orb X a).ncard = F.ncard + 4 := by
      conv_lhs => rw [hdecomp]
      rw [Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _), Set.ncard_coe_finset, hM4]
    have hF3 : 2 < F.ncard := by
      rw [Set.two_lt_ncard_iff (Set.toFinite _)]
      refine ⟨a, y a, φ, ⟨mem_Orb_self X a, hua⟩,
        ⟨hSig _ (Moved_stable hy ha), U_apply_of_ne S.ya_b S.ya_yb S.ya_e S.ya_ye⟩,
        ⟨hφO, U_apply_of_ne (hφS b hb).1 (hφS b hb).2 (hφS e hT.he).1 (hφS e hT.he).2⟩,
        fun h => ha h.symm, (hφS a ha).1.symm, (hφS a ha).2.symm⟩
    have hj0 : j ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hj
      omega
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hk
      omega
    have h1 : p ∣ p ^ k := dvd_pow_self p hk0
    have h2 : p ∣ p ^ j := dvd_pow_self p hj0
    have hsum : p ^ j + 4 = p ^ k := by rw [← hj, ← hcard, hk]
    have h3 : p ∣ 4 := (Nat.dvd_add_right h2).mp (hsum ▸ h1)
    exact hp (p_dvd_four (Fact.out) h3)
  · push Not at hfixO
    have hya : y a ∉ Orb X a := by
      intro hya
      have himg := image_Orb_eq_self hyN (mem_Orb_self X a) hya
      have hmem : ∀ b ∈ Orb X a, y b ∈ Orb X a := fun b hb => by
        rw [← himg]; exact Set.mem_image_of_mem y hb
      obtain ⟨φ, hφO, hφ⟩ := exists_fixed_of_odd (Set.toFinite _) hyy hmem hOodd
      exact hfixO φ hφO hφ
    have hOsub : ∀ {c d : α}, Trip y a c d → ∀ w ∈ Orb X a, w = a ∨ w = y a ∨ w = c ∨ w = y c := by
      intro c d hd w hw
      by_contra hcon
      push Not at hcon
      have hu := U_mem hy hD hd
      have huw : U y a c w = w := U_apply_of_ne hcon.1 hcon.2.1 hcon.2.2.1 hcon.2.2.2
      have himg := image_Orb_eq_self hu hw (by rw [huw]; exact hw)
      have h1 : U y a c a ∈ Orb X a := by
        rw [← himg]; exact Set.mem_image_of_mem _ (mem_Orb_self X a)
      rw [U_apply_left hy hd] at h1
      exact hya h1
    have hsub : Orb X a ⊆ {a} := by
      intro w hw
      have h1 := hOsub hT w hw
      have h2 := hOsub (hT.swap23 hy) w hw
      rw [Set.mem_singleton_iff]
      rcases h1 with h1 | h1 | h1 | h1
      · exact h1
      · exact absurd (h1 ▸ hw) hya
      · rcases h2 with h2 | h2 | h2 | h2
        · exact h2
        · exact absurd (h2 ▸ hw) hya
        · exact absurd (h1.symm.trans h2) hT.heb.symm
        · exact absurd (h1.symm.trans h2) S.b_ye
      · rcases h2 with h2 | h2 | h2 | h2
        · exact h2
        · exact absurd (h2 ▸ hw) hya
        · exact absurd (h1.symm.trans h2) S.yb_e
        · exact absurd (h1.symm.trans h2) S.yb_ye
    have := Set.ncard_le_ncard hsub (Set.finite_singleton a)
    rw [Set.ncard_singleton] at this
    omega

end Big

section Main

variable {p : ℕ} [Fact p.Prime] {X : Subgroup (Perm α)} {y : Perm α}

theorem alt_core (hα : 7 ≤ Fintype.card α) (hp : p ≠ 2) (hX : IsPGroup p ↥X) (hy : y * y = 1)
    (hyN : y ∈ normalizer (X : Set (Perm α)))
    (hD : ∀ v : Perm α, Odd (orderOf v) → v * y = y * v → v ∈ normalizer (X : Set (Perm α)))
    (hnc : ∃ x ∈ X, x * y ≠ y * x) : False := by
  obtain ⟨x, hxX, hxy⟩ := hnc
  obtain ⟨a, ha, hxa⟩ := exists_moved_in_support hy hxy
  by_cases h5 : 5 ≤ (Moved y).card
  · exact core_big hp hX hy hyN hD h5 ha hxX hxa
  · exact core_small hα hp hX hy hyN hD (by omega) ha hxX hxa

end Main

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87.AltCore
