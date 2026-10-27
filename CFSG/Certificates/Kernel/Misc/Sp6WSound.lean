module

public import CFSG.Certificates.Kernel.Misc.Sp6NSound
public import CFSG.Certificates.Kernel.Misc.G22RSound
public import CFSG.Quasithin.H13.L32NKGSp6Wit
public import Certificates.Data.Kernel.Misc.Sp6W

public section

namespace CFSG.KC.Sp6W

open CFSG.KGroups.Sp6 CFSG.Quasithin.H13 CFSG.Quasithin.H13.KGSp6 CFSG.KD.Sp6W CFSG.KC.Mat8P
  CFSG.KD.G22W CFSG.KC.G22W CFSG.KC.G22C

@[expose] def Five (M : Mat6) : Prop := M ^ 6 ≠ 1 ∧ (M ^ 6) ^ 5 = 1

theorem five_of_Five {z : List ℕ} (hz : KGCert.ValidC z) (h : Five (KGCert.decodeC z)) :
    five z = true := by
  simp only [five, mulC_eq, oneC_eq, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq]
  have hz2 := KGCert.validC_mulC hz hz
  have hz3 := KGCert.validC_mulC hz2 hz
  have hd6 : KGCert.decodeC (KGCert.mulC (KGCert.mulC (KGCert.mulC z z) z)
      (KGCert.mulC (KGCert.mulC z z) z)) = KGCert.decodeC z ^ 6 := by
    rw [KGCert.decodeC_mulC _ _ hz3.1, KGCert.decodeC_mulC _ _ hz.1, KGCert.decodeC_mulC _ _ hz.1]
    simp only [pow_succ, pow_zero, one_mul, Matrix.mul_assoc]
  set y := KGCert.mulC (KGCert.mulC (KGCert.mulC z z) z) (KGCert.mulC (KGCert.mulC z z) z)
    with hydef
  have hy : KGCert.ValidC y := KGCert.validC_mulC hz3 hz3
  have hyy := KGCert.validC_mulC hy hy
  have hy4 := KGCert.validC_mulC hyy hyy
  refine ⟨fun h1 => h.1 ?_, ?_⟩
  · rw [← hd6, h1, KGCert.decodeC_oneC]
  · apply KGCert.decodeC_injOn (KGCert.validC_mulC hy hy4) KGCert.validC_oneC
    rw [KGCert.decodeC_mulC _ _ hy4.1, KGCert.decodeC_mulC _ _ hyy.1,
      KGCert.decodeC_mulC _ _ hy.1, hd6, KGCert.decodeC_oneC, ← h.2]
    simp only [pow_succ, pow_zero, one_mul, Matrix.mul_assoc]

theorem cpow {H H' A : Mat6} (h1 : H' * H = 1) (h2 : H * H' = 1) (n : ℕ) :
    (H * A * H') ^ n = H * A ^ n * H' := by
  induction n with
  | zero => simp [h2]
  | succ n ih =>
    rw [pow_succ, ih, pow_succ]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc H' H, h1, Matrix.one_mul]

theorem Five_conj {H H' M : Mat6} (h1 : H' * H = 1) (h2 : H * H' = 1) (h : Five M) :
    Five (H * M * H') := by
  refine ⟨fun he => h.1 ?_, ?_⟩
  · rw [cpow h1 h2] at he
    calc M ^ 6 = H' * (H * M ^ 6 * H') * H := by
          simp only [Matrix.mul_assoc]
          rw [h1, Matrix.mul_one, ← Matrix.mul_assoc, h1, Matrix.one_mul]
      _ = 1 := by rw [he, Matrix.mul_one, h1]
  · rw [cpow h1 h2, cpow h1 h2, h.2, Matrix.mul_one, h2]

theorem beq_oneP {x : ℕ} (hx : GoodL x) : Nat.beq x oneP = (colsK x == oneC) := by
  apply Bool.eq_iff_iff.2
  rw [Nat.beq_eq, beq_iff_eq]
  constructor
  · rintro rfl
    exact colsK_oneP
  · intro h
    exact goodL_inj hx goodL_one (by rw [h, colsK_oneP]; rfl)

theorem fiveP_eq {x : ℕ} (hx : GoodL x) : fiveP x = five (colsK x) := by
  have g2 := goodL_mul hx hx
  have g3 := goodL_mul g2.1 hx
  have g6 := goodL_mul g3.1 g3.1
  have gyy := goodL_mul g6.1 g6.1
  have gy4 := goodL_mul gyy.1 gyy.1
  have g5 := goodL_mul g6.1 gy4.1
  rw [fiveP, fiveY, beq_oneP g6.1, beq_oneP g5.1, g5.2, gy4.2, gyy.2, g6.2, g3.2, g2.2]
  rfl

theorem mem_spLeaves_of_isoK {x : ℕ} (hx : GoodL x) (h : isoK x = true) :
    colsK x ∈ spLeaves 64 := by
  have he : isoK x = (cand1 (Nat.land x 255) (Nat.land (Nat.shiftRight x 8) 255) &&
      cand2 (Nat.land x 255) (Nat.land (Nat.shiftRight x 8) 255)
        (Nat.land (Nat.shiftRight x 16) 255) &&
      cand3 (Nat.land x 255) (Nat.land (Nat.shiftRight x 8) 255)
        (Nat.land (Nat.shiftRight x 16) 255) (Nat.land (Nat.shiftRight x 24) 255) &&
      cand4 (Nat.land x 255) (Nat.land (Nat.shiftRight x 8) 255)
        (Nat.land (Nat.shiftRight x 16) 255) (Nat.land (Nat.shiftRight x 24) 255)
        (Nat.land (Nat.shiftRight x 32) 255) &&
      cand5 (Nat.land x 255) (Nat.land (Nat.shiftRight x 8) 255)
        (Nat.land (Nat.shiftRight x 16) 255) (Nat.land (Nat.shiftRight x 24) 255)
        (Nat.land (Nat.shiftRight x 32) 255) (Nat.land (Nat.shiftRight x 40) 255)) := rfl
  rw [he] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact mem_spLeaves_cols.2 ⟨hx.2.2, cols_of_cands h1 h2 h3 h4 h5⟩

@[expose] def maskL (l : List ℕ) : ℕ := l.foldr (fun v acc => Nat.lor (Nat.shiftLeft 1 v) acc) 0

theorem testBit_maskL (l : List ℕ) (i : ℕ) : (maskL l).testBit i = decide (i ∈ l) := by
  induction l with
  | nil => simp [maskL]
  | cons v l ih =>
    have e : maskL (v :: l) = (1 <<< v) ||| maskL l := rfl
    rw [e, Nat.testBit_or, ih, Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow]
    by_cases hv : v = i
    · subst hv
      simp
    · simp [hv, Ne.symm hv]

theorem maskL_eq_of_iff {l l' : List ℕ} (h : ∀ i, i ∈ l ↔ i ∈ l') : maskL l = maskL l' := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_maskL, testBit_maskL]
  simp [h i]

theorem mem_iff_of_maskL_eq {l l' : List ℕ} (h : maskL l = maskL l') (i : ℕ) :
    i ∈ l ↔ i ∈ l' := by
  have := congrArg (fun n => n.testBit i) h
  simpa [testBit_maskL] using this

@[expose] def keyL (A : List ℕ) : ℕ := maskL (uL.map (mulVecC A))

theorem keyK_eq (x : ℕ) : keyK x = keyL (colsK x) := rfl

theorem mulVecC_mulC {A B : List ℕ} (hA : KGCert.ValidC A) (hB : KGCert.ValidC B) (u : ℕ) :
    mulVecC (mulC A B) u = mulVecC A (mulVecC B u) := by
  apply KGCert.vec6_inj (KGCert.mulVecC_lt (KGCert.validC_mulC hA hB) u)
    (KGCert.mulVecC_lt hA _)
  change KGCert.vec6 (KGCert.mulVecC (KGCert.mulC A B) u) =
    KGCert.vec6 (KGCert.mulVecC A (KGCert.mulVecC B u))
  simp only [← KGCert.decodeC_mulVec]
  rw [KGCert.decodeC_mulC _ _ hB.1, Matrix.mulVec_mulVec]

theorem keyL_mul {A M : List ℕ} (hA : KGCert.ValidC A) (hM : KGCert.ValidC M)
    (hU : ∀ v, v ∈ uL.map (mulVecC M) ↔ v ∈ uL) : keyL (mulC A M) = keyL A := by
  apply maskL_eq_of_iff
  intro i
  simp only [List.mem_map]
  constructor
  · rintro ⟨u, hu, rfl⟩
    have : mulVecC M u ∈ uL := (hU _).1 (List.mem_map.2 ⟨u, hu, rfl⟩)
    exact ⟨_, this, (mulVecC_mulC hA hM u).symm⟩
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨u', hu', he⟩ := List.mem_map.1 ((hU u).2 hu)
    exact ⟨u', hu', by rw [mulVecC_mulC hA hM, he]⟩

theorem conj_mem {u : Mat6ˣ} {k : ℕ} (h : (s0u : Mat6) * u = u * (s0u : Mat6) ^ k) :
    u⁻¹ * s0u * u = s0u ^ k := by
  apply Units.ext
  have h' : ((u⁻¹ : Mat6ˣ) : Mat6) * ((u : Mat6) * (s0u : Mat6) ^ k) =
      (s0u : Mat6) ^ k := by
    rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
  rw [Units.val_mul, Units.val_mul, Matrix.mul_assoc, h, h', Units.val_pow_eq_pow_val]

theorem n0_closed (h2 : normCheck 64 s0 n0List = true)
    (hiso : ∀ n ∈ n0List, IsIso (KGCert.decodeC n))
    (hNs : ∀ n ∈ n0List, ∃ k, mulC s0 n = mulC n (powC s0 k)) :
    ∀ a ∈ n0List, ∀ b ∈ n0List, ∃ c ∈ n0List,
      KGCert.decodeC a * KGCert.decodeC b * KGCert.decodeC c = 1 := by
  have hu : ∀ n ∈ n0List, ∃ u : Mat6ˣ, u ∈ SpU ∧ (u : Mat6) = KGCert.decodeC n ∧
      ∃ k : ℕ, u⁻¹ * s0u * u = s0u ^ k := by
    intro n hn
    obtain ⟨u, hu⟩ := isUnit_of_isIso (hiso n hn)
    refine ⟨u, by rw [mem_SpU, hu]; exact hiso n hn, hu, ?_⟩
    obtain ⟨k, hk⟩ := hNs n hn
    have hv := n0List_valid n hn
    have hk' : KGCert.mulC s0 n = KGCert.mulC n (powC s0 k) := hk
    have hm := congrArg KGCert.decodeC hk'
    rw [KGCert.decodeC_mulC _ _ hv.1, KGCert.decodeC_mulC _ _ (validC_powC validC_s0 k).1,
      decodeC_powC validC_s0] at hm
    refine ⟨k, conj_mem ?_⟩
    rw [coe_s0u, hu]
    exact hm
  intro a ha b hb
  obtain ⟨ua, haS, hae, ka, hka⟩ := hu a ha
  obtain ⟨ub, hbS, hbe, kb, hkb⟩ := hu b hb
  have hxS : (ua * ub)⁻¹ ∈ SpU := SpU.inv_mem (SpU.mul_mem haS hbS)
  have hxn : (ua * ub)⁻¹ * s0u * ((ua * ub)⁻¹)⁻¹ ∈ Subgroup.zpowers s0u := by
    have e : (ua * ub)⁻¹ * s0u * ((ua * ub)⁻¹)⁻¹ = (ub⁻¹ * s0u * ub) ^ ka := by
      rw [inv_inv, mul_inv_rev]
      have : ub⁻¹ * ua⁻¹ * s0u * (ua * ub) = ub⁻¹ * (ua⁻¹ * s0u * ua) * ub := by group
      have hc : ∀ k : ℕ, (ub⁻¹ * s0u * ub) ^ k = ub⁻¹ * s0u ^ k * ub := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
          rw [pow_succ, ih, pow_succ]
          group
      rw [this, hka]
      exact (hc ka).symm
    rw [e, hkb, ← pow_mul]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
  refine ⟨colsOf (((ua * ub)⁻¹ : Mat6ˣ) : Mat6), colsOf_mem_n0List h2 hxS hxn, ?_⟩
  rw [decodeC_colsOf, ← hae, ← hbe, ← Units.val_mul, ← Units.val_mul, mul_inv_cancel,
    Units.val_one]

theorem countP_add_le {L S : List (List ℕ)} {Q : List ℕ → Bool} (hL : L.Nodup) (hS : S.Nodup)
    (hSL : ∀ x ∈ S, x ∈ L) (hQ : ∀ x ∈ S, Q x = false) : L.countP Q + S.length ≤ L.length := by
  classical
  rw [List.countP_eq_length_filter]
  have h1 : (L.filter Q).toFinset ∪ S.toFinset ⊆ L.toFinset := by
    intro x hx
    simp only [Finset.mem_union, List.mem_toFinset, List.mem_filter] at hx ⊢
    rcases hx with ⟨h, -⟩ | h
    · exact h
    · exact hSL x h
  have h2 : Disjoint (L.filter Q).toFinset S.toFinset := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [List.mem_toFinset, List.mem_filter] at hx hx'
    rw [hQ x hx'] at hx
    exact absurd hx.2 (by simp)
  have := Finset.card_le_card h1
  rw [Finset.card_union_of_disjoint h2, List.toFinset_card_of_nodup (hL.filter _),
    List.toFinset_card_of_nodup hS, List.toFinset_card_of_nodup hL] at this
  exact this

theorem iso_of_mem_G {x : List ℕ} (hx : x ∈ KGCert.g22Elems) :
    IsIso (KGCert.decodeC x) :=
  KGCert.g22Mats_isometry _ ((KGCert.mem_g22Mats_iff _).2 ⟨x, hx, rfl⟩)

theorem letB_eq (y : ℕ) (k : ℕ → Bool) : letB y k = k y := by
  cases y <;> rfl

theorem wRec_facts {N Z W : ℕ → ℕ} {m nz t : ℕ} (h : wRec N Z W m nz t = true) :
    jW W t < nz ∧ hW W t < 42 ∧ keyK (mulP (N (hW W t)) (Z (jW W t))) = kW W t ∧
      (t + 1 < m → kW W t < kW W (t + 1)) := by
  simp only [wRec, letB_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, h2, h3, fun ht => ?_⟩
  have hb : Nat.blt (Nat.add t 1) m = true := by
    rw [Nat.blt_eq]
    exact ht
  rw [hb] at h4
  have h5 : Nat.blt (kW W t) (kW W (t + 1)) = true := h4
  simpa [Nat.blt_eq] using h5

theorem zRec_facts {Z : ℕ → ℕ} {j : ℕ} (h : zRec Z j = true) :
    GoodL (Z j) ∧ isoK (Z j) = true ∧ fiveP (Z j) = true := by
  simp only [zRec, Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨goodL_of h1 h2, h3, h4⟩

theorem witCheck_of {N Z W : ℕ → ℕ} {m nz : ℕ}
    (hN : ∀ i < 42, GoodL (N i) ∧ colsK (N i) = n0List.getD i [])
    (hZ : ∀ j < nz, zRec Z j = true) (hWr : ∀ t < m, wRec N Z W m nz t = true)
    (hm : m = 34146) (hNG : ∀ n ∈ n0List, n ∈ KGCert.g22Elems)
    (hU : ∀ n ∈ n0List, maskL (uL.map (mulVecC n)) = maskL uL)
    (hcl : ∀ a ∈ n0List, ∀ b ∈ n0List, ∃ c ∈ n0List,
      KGCert.decodeC a * KGCert.decodeC b * KGCert.decodeC c = 1) :
    witCheck 64 KGCert.g22Elems n0List 6047 = true := by
  classical
  have hNmem : ∀ i < 42, colsK (N i) ∈ n0List := by
    intro i hi
    rw [(hN i hi).2, List.getD_eq_getElem _ _ (by rw [n0List_length]; exact hi)]
    exact List.getElem_mem _
  have hNv : ∀ n ∈ n0List, KGCert.ValidC n := n0List_valid
  have hNiso : ∀ n ∈ n0List, IsIso (KGCert.decodeC n) := fun n hn =>
    KGCert.g22Mats_isometry _ ((KGCert.mem_g22Mats_iff _).2 ⟨n, hNG n hn, rfl⟩)
  have hUiff : ∀ n ∈ n0List, ∀ v, v ∈ uL.map (mulVecC n) ↔ v ∈ uL := fun n hn v =>
    mem_iff_of_maskL_eq (hU n hn) v
  let At : ℕ → List ℕ := fun t => mulC (colsK (N (hW W t))) (colsK (Z (jW W t)))
  let C : ℕ → List (List ℕ) := fun t => n0List.map (mulC (At t))
  have hf := fun t (h : t < m) => wRec_facts (hWr t h)
  have hZt : ∀ t < m, GoodL (Z (jW W t)) ∧ isoK (Z (jW W t)) = true ∧
      fiveP (Z (jW W t)) = true :=
    fun t h => zRec_facts (hZ _ (hf t h).1)
  have hNt : ∀ t < m, GoodL (N (hW W t)) ∧ colsK (N (hW W t)) ∈ n0List := fun t h =>
    ⟨(hN _ (hf t h).2.1).1, hNmem _ (hf t h).2.1⟩
  have hAv : ∀ t < m, KGCert.ValidC (At t) := fun t h =>
    KGCert.validC_mulC (hNt t h).1.2.2 (hZt t h).1.2.2
  have hAiso : ∀ t < m, IsIso (KGCert.decodeC (At t)) := by
    intro t h
    have hz := (mem_spLeaves_iff.1 (mem_spLeaves_of_isoK (hZt t h).1 (hZt t h).2.1)).2
    change IsIso (KGCert.decodeC (KGCert.mulC _ _))
    rw [KGCert.decodeC_mulC _ _ (hZt t h).1.2.2.1]
    exact IsIso.mul (hNiso _ (hNt t h).2) hz
  have hCv : ∀ t < m, ∀ x ∈ C t, KGCert.ValidC x ∧ ∃ n ∈ n0List, x = mulC (At t) n := by
    intro t h x hx
    obtain ⟨n, hn, rfl⟩ := List.mem_map.1 hx
    exact ⟨KGCert.validC_mulC (hAv t h) (hNv n hn), n, hn, rfl⟩
  have hkey : ∀ t < m, ∀ x ∈ C t, keyL x = kW W t := by
    intro t h x hx
    obtain ⟨n, hn, rfl⟩ := List.mem_map.1 hx
    rw [keyL_mul (hAv t h) (hNv n hn) (hUiff n hn), ← (hf t h).2.2.1, keyK_eq,
      (goodL_mul (hNt t h).1 (hZt t h).1).2]
    rfl
  have hmono : ∀ a b, a < b → b < m → kW W a < kW W b := by
    intro a b hab hb
    induction b with
    | zero => omega
    | succ b ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hab with hab' | rfl
      · exact lt_trans (ih hab' (by omega)) ((hf b (by omega)).2.2.2 hb)
      · exact (hf a (by omega)).2.2.2 hb
  have hwit : ∀ t < m, ∀ x ∈ C t, ∃ c ∈ n0List, five (mulC x c) = true := by
    intro t h x hx
    obtain ⟨n, hn, rfl⟩ := List.mem_map.1 hx
    obtain ⟨c, hc, hhc⟩ := hcl _ (hNt t h).2 n hn
    refine ⟨c, hc, five_of_Five (KGCert.validC_mulC (KGCert.validC_mulC (hAv t h) (hNv n hn))
      (hNv c hc)) ?_⟩
    have hz5 := pow_of_five (hZt t h).1.2.2 (by rw [← fiveP_eq (hZt t h).1]; exact (hZt t h).2.2)
    set H := KGCert.decodeC (colsK (N (hW W t)))
    set H' := KGCert.decodeC n * KGCert.decodeC c
    have h2 : H * H' = 1 := by rw [← Matrix.mul_assoc]; exact hhc
    have h1 : H' * H = 1 := mul_eq_one_comm.1 h2
    have e : KGCert.decodeC (mulC (mulC (At t) n) c) =
        H * KGCert.decodeC (colsK (Z (jW W t))) * H' := by
      change KGCert.decodeC (KGCert.mulC (KGCert.mulC (KGCert.mulC _ _) n) c) = _
      rw [KGCert.decodeC_mulC _ _ (hNv c hc).1, KGCert.decodeC_mulC _ _ (hNv n hn).1,
        KGCert.decodeC_mulC _ _ (hZt t h).1.2.2.1]
      simp only [H, H', Matrix.mul_assoc]
    rw [e]
    exact Five_conj h1 h2 hz5
  have hNsub : ∀ n ∈ n0List, ∃ u ∈ Gsub, (u : Mat6) = KGCert.decodeC n := by
    intro n hn
    obtain ⟨u, hu⟩ := isUnit_of_isIso (hNiso n hn)
    exact ⟨u, by rw [mem_Gsub, hu]; exact (KGCert.mem_g22Mats_iff _).2 ⟨n, hNG n hn, rfl⟩, hu⟩
  have hout : ∀ t < m, ∀ x ∈ C t, x ∉ KGCert.g22Elems := by
    intro t h x hx hxG
    obtain ⟨c, hc, hfive⟩ := hwit t h x hx
    have hyG : mulC x c ∈ KGCert.g22Elems := mulC_mem_G hxG (hNG c hc)
    have hyv : KGCert.ValidC (mulC x c) := KGCert.validC_of_mem hyG
    obtain ⟨u, hu⟩ := isUnit_of_isIso (iso_of_mem_G hyG)
    have huG : u ∈ Gsub := by
      rw [mem_Gsub, hu]
      exact (KGCert.mem_g22Mats_iff _).2 ⟨_, hyG, rfl⟩
    have hno := no_witness card_Gsub hNsub huG oneC (by decide)
    have hcols : mulC (colsOf (u : Mat6)) oneC = mulC x c := by
      rw [hu, colsOf_decodeC hyv]
      apply KGCert.decodeC_injOn (KGCert.validC_mulC hyv KGCert.validC_oneC) hyv
      rw [KGCert.decodeC_mulC _ _ rfl, KGCert.decodeC_oneC, Matrix.mul_one]
    rw [hcols, hfive] at hno
    exact absurd hno (by decide)
  let S : List (List ℕ) := KGCert.g22Elems ++ (List.range m).flatMap C
  have hCnd : ∀ t < m, (C t).Nodup := by
    intro t h
    refine n0List_nodup.map_on fun a ha b hb hab => ?_
    obtain ⟨U, hU'⟩ := isUnit_of_isIso (hAiso t h)
    apply KGCert.decodeC_injOn (hNv a ha) (hNv b hb)
    have e := congrArg KGCert.decodeC hab
    rw [mulC_eq, KGCert.decodeC_mulC _ _ (hNv a ha).1, KGCert.decodeC_mulC _ _ (hNv b hb).1,
      ← hU'] at e
    exact (Units.isUnit U).mul_left_cancel e
  have hSnd : S.Nodup := by
    refine List.Nodup.append KGCert.g22Elems_nodup ?_ ?_
    · rw [List.nodup_flatMap]
      refine ⟨fun t ht => hCnd t (List.mem_range.1 ht), ?_⟩
      refine List.Pairwise.imp_of_mem ?_ List.nodup_range
      intro a b ha hb hab x hxa hxb
      have ha' := List.mem_range.1 ha
      have hb' := List.mem_range.1 hb
      have e := (hkey a ha' x hxa).symm.trans (hkey b hb' x hxb)
      rcases Nat.lt_or_gt_of_ne hab with h | h
      · exact absurd e (ne_of_lt (hmono a b h hb'))
      · exact absurd e (ne_of_gt (hmono b a h ha'))
    · intro x hxG hxC
      obtain ⟨t, ht, hxt⟩ := List.mem_flatMap.1 hxC
      exact hout t (List.mem_range.1 ht) x hxt hxG
  have hSL : ∀ x ∈ S, x ∈ spLeaves 64 := by
    intro x hx
    rcases List.mem_append.1 hx with hxG | hxC
    · exact mem_spLeaves_iff.2 ⟨KGCert.validC_of_mem hxG, iso_of_mem_G hxG⟩
    · obtain ⟨t, ht, hxt⟩ := List.mem_flatMap.1 hxC
      have ht' := List.mem_range.1 ht
      obtain ⟨hv, n, hn, rfl⟩ := hCv t ht' x hxt
      refine mem_spLeaves_iff.2 ⟨hv, ?_⟩
      change IsIso (KGCert.decodeC (KGCert.mulC _ _))
      rw [KGCert.decodeC_mulC _ _ (hNv n hn).1]
      exact IsIso.mul (hAiso t ht') (hNiso n hn)
  have hSQ : ∀ x ∈ S, (!KGCert.g22Elems.contains x &&
      !n0List.any fun n => five (mulC x n)) = false := by
    intro x hx
    rcases List.mem_append.1 hx with hxG | hxC
    · simp [List.contains_iff_mem, hxG]
    · obtain ⟨t, ht, hxt⟩ := List.mem_flatMap.1 hxC
      obtain ⟨c, hc, hfc⟩ := hwit t (List.mem_range.1 ht) x hxt
      have : (n0List.any fun n => five (mulC x n)) = true := List.any_eq_true.2 ⟨c, hc, hfc⟩
      simp [this]
  have hSlen : S.length = 12096 + 42 * m := by
    have hC : ∀ t, (C t).length = 42 := fun t => by simp [C, n0List_length]
    simp only [S, List.length_append, List.length_flatMap, hC, Certificates.certificate7102.1]
    simp [List.sum_replicate, List.map_const', mul_comm]
  have hcount := countP_add_le (spLeaves_nodup 64) hSnd hSL hSQ
  rw [CFSG.KC.Sp6N.spLeaves_length, hSlen, hm] at hcount
  have key : (spLeaves 64).countP (fun x => !KGCert.g22Elems.contains x &&
      !n0List.any fun n => five (mulC x n)) ≤ 6047 := by
    generalize (spLeaves 64).countP (fun x => !KGCert.g22Elems.contains x &&
      !n0List.any fun n => five (mulC x n)) = c at hcount ⊢
    omega
  rw [witCheck.eq_1]
  apply decide_eq_true
  rw [spCount_eq]
  simpa [Std.HashSet.contains_ofList] using key

end CFSG.KC.Sp6W

end
