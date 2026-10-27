module

public import Certificates.Certificate450102
public import CFSG.Quasithin.Background.HMathieuO2Data

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeModelLattice

open CFSG.Monster.Code CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk
  CFSG.Quasithin.H.Coc24 CFSG.Quasithin.H.ZTrans
  CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeModelOrbitBits
  CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeModelLzMasks

theorem latRoots_lt : ∀ i < 7, latRoots.getD i 0 < 2 ^ 11 := by decide

theorem latOrb_iff {Y : Subgroup W11} (hY : img11 Lz ≤ stabSub Y) {i : ℕ} (hi : i < 7) {n : ℕ}
    (hn : (latOrb i).testBit n = true) :
    n < 2 ^ 11 ∧ (toW 11 n ∈ Y ↔ toW 11 (latRoots.getD i 0) ∈ Y) := by
  refine orbitBits_lz_spec (fun m => toW 11 m ∈ Y ↔ toW 11 (latRoots.getD i 0) ∈ Y) ?_
    (latRoots_lt i hi) Iff.rfl n hn
  intro m _ hm x hx k hxk _
  show toW 11 k ∈ Y ↔ _
  rw [← hxk]
  exact ((hY hx) (toW 11 m)).trans hm

theorem length_filter_eq_sum {α : Type*} (l : List α) (k : ℕ) (P : α → Bool) (Q : ℕ → α → Bool)
    (hQ : ∀ x ∈ l, ∃ i < k, Q i x = true ∧ ∀ j < k, Q j x = true → j = i) :
    (l.filter P).length = ∑ i ∈ Finset.range k, (l.filter fun x => P x && Q i x).length := by
  induction l with
  | nil => simp
  | cons x l ih =>
    obtain ⟨i0, hi0, hQi0, huniq⟩ := hQ x List.mem_cons_self
    have hl : ∀ y ∈ l, ∃ i < k, Q i y = true ∧ ∀ j < k, Q j y = true → j = i :=
      fun y hy => hQ y (List.mem_cons_of_mem x hy)
    have hsum : ∑ i ∈ Finset.range k, (if P x && Q i x then 1 else 0) = if P x then 1 else 0 := by
      rw [Finset.sum_eq_single i0]
      · simp [hQi0]
      · intro j hj hji
        have : Q j x = false := by
          by_contra h
          exact hji (huniq j (Finset.mem_range.1 hj) (by simpa using h))
        simp [this]
      · intro h
        exact absurd (Finset.mem_range.2 hi0) h
    have e1 : ((x :: l).filter P).length = (if P x then 1 else 0) + (l.filter P).length := by
      rw [List.filter_cons]
      split_ifs <;> simp [add_comm]
    have e2 : ∀ i, ((x :: l).filter fun y => P y && Q i y).length =
        (if P x && Q i x then 1 else 0) + (l.filter fun y => P y && Q i y).length := by
      intro i
      rw [List.filter_cons]
      split_ifs <;> simp [add_comm]
    rw [e1, Finset.sum_congr rfl fun i _ => e2 i, Finset.sum_add_distrib, hsum, ih hl]

open scoped Classical in
theorem card_eq_sum {Y : Subgroup W11}
    (hY : img11 Lz ≤ stabSub Y) :
    Nat.card Y = ∑ i ∈ Finset.range 7,
      if decide (toW 11 (latRoots.getD i 0) ∈ Y) = true then latSizes.getD i 0 else 0 := by
  classical
  obtain ⟨⟨hpart, hsize, -⟩, -⟩ := Certificates.certificate450102
  have h1 : Nat.card Y =
      ((List.range 2048).filter fun n => decide (toW 11 n ∈ Y)).length :=
    (MaskCoords.std 11).card_eq Y (fun n => decide (toW 11 n ∈ Y))
      (fun m _ => (decide_eq_true_iff).symm)
  rw [h1, length_filter_eq_sum (List.range 2048) 7 (fun n => decide (toW 11 n ∈ Y))
    (fun i n => (latOrb i).testBit n) (fun n hn => ?_)]
  · refine Finset.sum_congr rfl fun i hi => ?_
    have hi7 : i < 7 := Finset.mem_range.1 hi
    have hcongr : ((List.range 2048).filter fun n =>
          decide (toW 11 n ∈ Y) && (latOrb i).testBit n) =
        (List.range 2048).filter fun n =>
          decide (toW 11 (latRoots.getD i 0) ∈ Y) && (latOrb i).testBit n := by
      refine List.filter_congr fun n _ => ?_
      by_cases hb : (latOrb i).testBit n = true
      · have := (latOrb_iff hY hi7 hb).2
        simp [hb, this]
      · simp [hb]
    rw [hcongr]
    by_cases hr : toW 11 (latRoots.getD i 0) ∈ Y
    · simp only [hr, decide_true, Bool.true_and, if_true]
      exact hsize i hi7
    · rw [decide_eq_false hr]
      simp
  · have hn' : n < 2048 := List.mem_range.1 hn
    have := hpart n hn'
    obtain ⟨i, hi⟩ := List.length_eq_one_iff.1 this
    have hmem : i ∈ (List.range 7).filter fun i => (latOrb i).testBit n := by
      rw [hi]; exact List.mem_singleton_self i
    rw [List.mem_filter, List.mem_range] at hmem
    refine ⟨i, hmem.1, hmem.2, fun j hj hQj => ?_⟩
    have : j ∈ (List.range 7).filter fun i => (latOrb i).testBit n :=
      List.mem_filter.2 ⟨List.mem_range.2 hj, hQj⟩
    rw [hi] at this
    exact List.mem_singleton.1 this

theorem lat_z0_mul_self : z0 * z0 = 1 := by
  rw [← toW_xor, Nat.xor_self, toW_zero]

theorem lat_z0_ne_one : z0 ≠ 1 := by
  intro h
  have : (31 : ℕ) = 0 := toW_inj (by norm_num) (by norm_num) (h.trans (toW_zero 11).symm)
  omega

theorem lat_orderOf_z0 : orderOf z0 = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact lat_z0_mul_self) lat_z0_ne_one

theorem lat_card_zpowers_z0 : Nat.card ↥(Subgroup.zpowers z0) = 2 := by
  rw [Nat.card_zpowers, lat_orderOf_z0]

theorem arith_lattice (b0 b1 b2 b3 b4 b5 b6 : Bool) (k : ℕ) (hk : k < 12) (h0 : b0 = true)
    (h : (if b0 = true then 1 else 0) + (if b1 = true then 1 else 0) +
      (if b2 = true then 36 else 0) + (if b3 = true then 90 else 0) +
      (if b4 = true then 240 else 0) + (if b5 = true then 240 else 0) +
      (if b6 = true then 1440 else 0) = 2 ^ k) :
    [b1, b2, b3, b4, b5, b6] ∈ [[false, false, false, false, false, false],
      [true, false, false, false, false, false], [true, true, true, false, false, false],
      [true, true, true, true, true, true]] := by
  subst h0
  revert k
  cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> cases b6 <;> decide

open scoped Classical in
theorem card_eq_sum_seven {Y : Subgroup W11}
    (hY : img11 Lz ≤ stabSub Y) :
    Nat.card Y = (if decide (toW 11 0 ∈ Y) = true then 1 else 0) +
      (if decide (toW 11 31 ∈ Y) = true then 1 else 0) +
      (if decide (toW 11 32 ∈ Y) = true then 36 else 0) +
      (if decide (toW 11 160 ∈ Y) = true then 90 else 0) +
      (if decide (toW 11 1 ∈ Y) = true then 240 else 0) +
      (if decide (toW 11 7 ∈ Y) = true then 240 else 0) +
      (if decide (toW 11 34 ∈ Y) = true then 1440 else 0) := by
  have h := card_eq_sum hY
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at h
  exact h

open scoped Classical in
theorem eq_of_le_stabSub {Y : Subgroup W11}
    (hY : img11 Lz ≤ stabSub Y) :
    Y = ⊥ ∨ Y = Subgroup.zpowers z0 ∨ Y = W0 ∨ Y = ⊤ := by
  obtain ⟨⟨-, -, hbasis⟩, -⟩ := Certificates.certificate450102
  have hcard := card_eq_sum_seven hY
  have hdvd : Nat.card Y ∣ 2 ^ 11 := natCard_W11 ▸ Subgroup.card_subgroup_dvd_card Y
  obtain ⟨k, hk, hkY⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have h0 : toW 11 0 ∈ Y := by rw [toW_zero]; exact Y.one_mem
  have hmem := arith_lattice _ (decide (toW 11 31 ∈ Y)) (decide (toW 11 32 ∈ Y))
    (decide (toW 11 160 ∈ Y)) (decide (toW 11 1 ∈ Y)) (decide (toW 11 7 ∈ Y))
    (decide (toW 11 34 ∈ Y)) k (by omega) (decide_eq_true h0) (hcard.symm.trans hkY)
  simp only [List.mem_cons, List.cons.injEq, decide_eq_true_eq, decide_eq_false_iff_not,
    List.not_mem_nil, or_false, and_true] at hmem
  rcases hmem with ⟨h1, h2, h3, h4, h5, h6⟩ | ⟨h1, h2, h3, h4, h5, h6⟩ |
    ⟨h1, h2, h3, h4, h5, h6⟩ | ⟨h1, h2, h3, h4, h5, h6⟩
  · left
    refine Subgroup.eq_bot_of_card_eq Y ?_
    rw [hcard]
    simp [h0, h1, h2, h3, h4, h5, h6]
  · right; left
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 h1) ?_).symm
    rw [lat_card_zpowers_z0, hcard]
    simp [h0, h1, h2, h3, h4, h5, h6]
  · right; right; left
    have hroot : ∀ i < 4, toW 11 (latRoots.getD i 0) ∈ Y := by
      intro i hi
      interval_cases i
      · exact h0
      · exact h1
      · exact h2
      · exact h3
    have hle : W0 ≤ Y := by
      rintro _ ⟨m, hm, rfl⟩
      refine mem_of_combos (fun m => toW 11 m ∈ Y) h0 ?_ w0Basis ?_ m hm
      · intro a b ha hb
        rw [toW_xor]
        exact Y.mul_mem ha hb
      · intro a ha
        obtain ⟨i, hi, hia⟩ := hbasis a ha
        exact ((latOrb_iff hY (by omega) hia).2).2 (hroot i hi)
    refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    rw [card_W0, hcard]
    simp [h0, h1, h2, h3, h4, h5, h6]
  · right; right; right
    refine Subgroup.eq_top_of_card_eq Y ?_
    rw [natCard_W11, hcard]
    simp [h0, h1, h2, h3, h4, h5, h6]

theorem eq_of_forall_apply_mem {Y : Subgroup W11}
    (hY : ∀ g ∈ img11 Lz, ∀ v ∈ Y, g v ∈ Y) :
    Y = ⊥ ∨ Y = Subgroup.zpowers z0 ∨ Y = W0 ∨ Y = ⊤ := by
  refine eq_of_le_stabSub fun g hg u => ⟨fun hu => ?_, hY g hg u⟩
  have hg' : g⁻¹ ∈ img11 Lz := (img11 Lz).inv_mem hg
  have h2 : g⁻¹ (g u) ∈ Y := hY g⁻¹ hg' _ hu
  have e : g⁻¹ (g u) = u := MulAut.inv_apply_self _ _ u
  exact (congrArg (· ∈ Y) e).mp h2

@[expose] def r0 : Equiv.Perm (Fin 24) := wPerm [lzX, lzY] r0Word

theorem hasArr_r0 : HasArr r0 r0Arr :=
  hasArr_wPerm (hasArr_getD₂ hasArr_lzX hasArr_lzY) r0Word

theorem r0_mem_Lz : r0 ∈ Lz := by
  refine wPerm_mem (fun p hp => ?_) r0Word
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact lzX_mem_Lz
  · exact lzY_mem_Lz

theorem r0_mem_AutPerm : r0 ∈ AutPerm := Lz_le r0_mem_Lz

theorem r0_pow_three : r0 ^ 3 = 1 := by
  obtain ⟨⟨hcube, -⟩, -⟩ := (Certificates.certificate450102).2
  have h : HasArr (r0 * (r0 * r0)) (cArr r0Arr (cArr r0Arr r0Arr)) :=
    hasArr_mul hasArr_r0 (hasArr_mul hasArr_r0 hasArr_r0)
  rw [hcube] at h
  rw [pow_three]
  exact perm_eq_of_hasArr h hasArr_one

theorem r0_ne_one : r0 ≠ 1 := by
  obtain ⟨⟨-, i, hi, hne⟩, -⟩ := (Certificates.certificate450102).2
  intro h
  refine hne ?_
  have h1 := hasArr_r0 ⟨i, hi⟩
  rw [h] at h1
  exact h1.symm

theorem orderOf_r0 : orderOf r0 = 3 :=
  orderOf_eq_prime r0_pow_three r0_ne_one

theorem colLz_r0 : colLz ⟨r0, r0_mem_Lz⟩ = 1 := by
  obtain ⟨-, hcol, -⟩ := (Certificates.certificate450102).2
  show colHom ⟨r0, Lz_le_BP r0_mem_Lz⟩ = 1
  refine colHom_eq fun i => Fin.ext ?_
  show (r0 i : ℕ) / 4 = (i : ℕ) / 4
  rw [hasArr_r0 i]
  exact hcol i i.2

theorem wActM_lt (w : List ℕ) {c : ℕ} (hc : c < 64) : wActM w c < 64 := by
  induction w with
  | nil => exact hc
  | cons g w ih =>
    show actM (if g = 0 then mxCols else myCols) (wActM w c) < 64
    split_ifs
    · exact (actM_ks_lt _ ih).1
    · exact (actM_ks_lt _ ih).2

theorem wPerm_conj_ksP : ∀ (w : List ℕ), (∀ g ∈ w, g < 2) → ∀ c : Fin 64,
    wPerm [lzX, lzY] w * ksP c * (wPerm [lzX, lzY] w)⁻¹ = ksP ⟨wActM w c, wActM_lt w c.2⟩
  | [], _, c => by
    simp only [wPerm, inv_one, mul_one, one_mul]
    rfl
  | g :: w, hw, c => by
    have hg : g < 2 := hw g List.mem_cons_self
    have ih := wPerm_conj_ksP w (fun h hh => hw h (List.mem_cons_of_mem g hh)) c
    have e : wPerm [lzX, lzY] (g :: w) * ksP c * (wPerm [lzX, lzY] (g :: w))⁻¹ =
        [lzX, lzY].getD g 1 * (wPerm [lzX, lzY] w * ksP c * (wPerm [lzX, lzY] w)⁻¹) *
          ([lzX, lzY].getD g 1)⁻¹ := by
      simp only [wPerm, mul_inv_rev, mul_assoc]
    rw [e, ih]
    interval_cases g
    · exact conj_ksP_x _
    · exact conj_ksP_y _

theorem r0_fpf {k : Equiv.Perm (Fin 24)} (hk : k ∈ KSp)
    (hk1 : k ≠ 1) : r0 * k * r0⁻¹ ≠ k := by
  obtain ⟨-, -, -, hfpf, -⟩ := (Certificates.certificate450102).2
  obtain ⟨c, rfl⟩ := mem_KSp_iff.1 hk
  have hc0 : (c : ℕ) ≠ 0 := fun h => hk1 (by rw [show c = 0 from Fin.ext h]; exact ksP_zero)
  intro h
  have hword : ∀ g ∈ r0Word, g < 2 := by decide
  have e := wPerm_conj_ksP r0Word hword c
  have h2 : ksP ⟨wActM r0Word c, wActM_lt r0Word c.2⟩ = ksP c := e.symm.trans h
  exact hfpf c c.2 hc0 (congrArg Fin.val (ksP_injective h2))

@[expose] noncomputable def r0Aut : MulAut W11 := rho11 AutPerm le_rfl ⟨r0, r0_mem_AutPerm⟩

theorem r0Aut_mem_img11_Lz : r0Aut ∈ img11 Lz :=
  ⟨⟨r0, r0_mem_AutPerm⟩, Subgroup.mem_subgroupOf.2 r0_mem_Lz, rfl⟩

theorem r0Aut_pow_three : r0Aut ^ 3 = 1 := by
  have h : (⟨r0, r0_mem_AutPerm⟩ : ↥AutPerm) ^ 3 = 1 := Subtype.ext r0_pow_three
  rw [r0Aut, ← map_pow, h, map_one]

theorem orderOf_r0Aut :
    orderOf r0Aut = 3 := by
  rw [r0Aut, orderOf_injective _ (rho11_injective AutPerm le_rfl), Subgroup.orderOf_mk,
    orderOf_r0]

theorem r0Aut_fpf
    {k : MulAut W11} (hk : k ∈ img11 KSp) (hk1 : k ≠ 1) : r0Aut * k * r0Aut⁻¹ ≠ k := by
  obtain ⟨σ, hσ, rfl⟩ := hk
  intro h
  have hσ' : (σ : Equiv.Perm (Fin 24)) ∈ KSp := Subgroup.mem_subgroupOf.1 hσ
  refine r0_fpf hσ' (fun h1 => hk1 ?_) ?_
  · rw [show σ = 1 from Subtype.ext h1, map_one]
  · have h2 : rho11 AutPerm le_rfl (⟨r0, r0_mem_AutPerm⟩ * σ * ⟨r0, r0_mem_AutPerm⟩⁻¹) =
        rho11 AutPerm le_rfl σ := by
      rw [map_mul, map_mul, map_inv]
      exact h
    have h3 := rho11_injective AutPerm le_rfl h2
    have h4 := congrArg Subtype.val h3
    simpa using h4

theorem r0Aut_mem_moveSub : r0Aut ∈ moveSub W0 := by
  obtain ⟨-, -, -, -, hcomm⟩ := (Certificates.certificate450102).2
  intro v
  obtain ⟨m, hm, rfl⟩ := toW_surj 11 v
  show r0Aut (toW 11 m) * (toW 11 m)⁻¹ ∈ W0
  have e : r0Aut (toW 11 m) * (toW 11 m)⁻¹ = toW 11 (act11 r0Arr m ^^^ m) := by
    rw [r0Aut, rho11_toW AutPerm le_rfl ⟨r0, r0_mem_AutPerm⟩ hasArr_r0 m, toW_inv, toW_xor]
  rw [e]
  exact toW_mem_maskSub (mem_combos_of_xorLin (xorLin_comm r0Arr) hcomm m hm)

theorem img11_KSp_le_moveSub : img11 KSp ≤ moveSub W0 := img11_KSp_le_commSub

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeModelLattice
