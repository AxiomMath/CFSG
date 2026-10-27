module

public import CFSG.Certificates.Kernel.G2Three.Sec1T3F13
public import CFSG.Certificates.Kernel.G2Three.Sec1T3CSound
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.TabRank

public section

namespace CFSG.KC.G2Three.Sec1T3

open CFSG.KD.G2Three.Sec1T3 CFSG.KC.Loop CFSG.OddStandard.HigherRank.G2Three.Sec1 Subgroup
open CFSG.OddStandard.HigherRank.G2Three.Sec1Proof (sGen sGen_zero sGen_one sGen_two sGen_three
  sGen_four)

theorem f14fg_E16_not_gen3 {Y : Type} [Group Y] [Finite Y] (hsq : ∀ y : Y, y * y = 1)
    (hc : Nat.card Y = 16) : ∀ s : Finset Y, s.card ≤ 3 → closure (s : Set Y) ≠ ⊤ := by
  classical
  have hinv : ∀ y : Y, y⁻¹ = y := fun y => inv_eq_of_mul_eq_one_right (hsq y)
  have hcomm : ∀ a b : Y, a * b = b * a := by
    intro a b
    have := hinv (a * b)
    rw [mul_inv_rev, hinv, hinv] at this
    exact this.symm
  have key : ∀ s : Finset Y, ((closure (s : Set Y) : Subgroup Y) : Set Y).ncard ≤ 2 ^ s.card := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      rw [Finset.coe_empty, Subgroup.closure_empty, Subgroup.coe_bot, Set.ncard_singleton,
        Finset.card_empty, pow_zero]
    | insert x s hx ih =>
      set Cs := closure (s : Set Y)
      let U : Subgroup Y :=
        { carrier := {y | y ∈ Cs ∨ x * y ∈ Cs}
          mul_mem' := by
            rintro a b (ha | ha) (hb | hb)
            · exact Or.inl (Cs.mul_mem ha hb)
            · right
              have e : a * (x * b) = x * (a * b) := by
                rw [← mul_assoc, hcomm a x, mul_assoc]
              rw [← e]
              exact Cs.mul_mem ha hb
            · right
              rw [← mul_assoc]
              exact Cs.mul_mem ha hb
            · left
              have e : x * a * (x * b) = a * b := by
                rw [hcomm x a, mul_assoc, ← mul_assoc x x b, hsq, one_mul]
              rw [← e]
              exact Cs.mul_mem ha hb
          one_mem' := Or.inl Cs.one_mem
          inv_mem' := by
            intro a ha
            rw [hinv a]
            exact ha }
      have hle : closure ((insert x s : Finset Y) : Set Y) ≤ U := by
        rw [closure_le]
        intro y hy
        rw [Finset.coe_insert, Set.mem_insert_iff] at hy
        rcases hy with rfl | hy
        · right
          change y * y ∈ Cs
          rw [hsq]
          exact Cs.one_mem
        · left
          exact subset_closure hy
      have hU : (U : Set Y) = (Cs : Set Y) ∪ (fun c => x⁻¹ * c) '' (Cs : Set Y) := by
        ext y
        change (y ∈ Cs ∨ x * y ∈ Cs) ↔ _
        simp only [Set.mem_union, Set.mem_image, SetLike.mem_coe]
        constructor
        · rintro (h | h)
          · exact Or.inl h
          · exact Or.inr ⟨x * y, h, by group⟩
        · rintro (h | ⟨c, hc, rfl⟩)
          · exact Or.inl h
          · right
            rwa [mul_inv_cancel_left]
      calc ((closure ((insert x s : Finset Y) : Set Y) : Subgroup Y) : Set Y).ncard
          ≤ (U : Set Y).ncard := Set.ncard_le_ncard (SetLike.coe_subset_coe.2 hle) (Set.toFinite _)
        _ ≤ (Cs : Set Y).ncard + ((fun c => x⁻¹ * c) '' (Cs : Set Y)).ncard := by
          rw [hU]
          exact Set.ncard_union_le _ _
        _ ≤ 2 ^ s.card + 2 ^ s.card :=
          add_le_add ih ((Set.ncard_image_le (Set.toFinite _)).trans ih)
        _ = 2 ^ (insert x s).card := by
          rw [Finset.card_insert_of_notMem hx, pow_succ]
          ring
  intro s hs htop
  have h1 := key s
  rw [htop, Subgroup.coe_top, Set.ncard_univ, hc] at h1
  have h2 : 2 ^ s.card ≤ 8 :=
    calc 2 ^ s.card ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hs
      _ = 8 := by norm_num
  omega

theorem f14fg_comm_closure {Γ : Type} [Group Γ] {s : Set Γ} {x : Γ}
    (h : ∀ g ∈ s, x * g = g * x) : ∀ y ∈ closure s, x * y = y * x := by
  intro y hy
  have hle : closure s ≤ centralizer ({x} : Set Γ) := by
    rw [closure_le]
    intro g hg
    rw [SetLike.mem_coe, mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact h g hg
  have := hle hy
  rw [mem_centralizer_iff] at this
  exact this x (Set.mem_singleton x)

theorem f14fg_nIf_bit (c : Bool) (k j : ℕ) :
    (nIf(c, Nat.shiftLeft 1 k, 0)).testBit j = true ↔ c = true ∧ j = k := by
  cases c
  · simp
  · change (1 <<< k).testBit j = true ↔ _
    rw [Nat.one_shiftLeft, Nat.testBit_two_pow, decide_eq_true_eq]
    exact ⟨fun h => ⟨rfl, h.symm⟩, fun h => h.2.symm⟩

theorem f14fg_orBelow_idx {m hi : ℕ} (f : ℕ → ℕ) (c : ℕ → Bool) (hm : m ≤ 64 * hi)
    (hf : ∀ k j, (f k).testBit j = true ↔ c k = true ∧ j = k) (j : ℕ) :
    (orBelow m hi f).testBit j = true ↔ j < m ∧ c j = true := by
  rw [orBelow_bit f j hm]
  constructor
  · rintro ⟨i, hi, hb⟩
    obtain ⟨hc, rfl⟩ := (hf i j).1 hb
    exact ⟨hi, hc⟩
  · rintro ⟨hj, hc⟩
    exact ⟨j, hj, (hf j j).2 ⟨hc, rfl⟩⟩

theorem f14fg_recSum (g : ℕ → ℕ) : ∀ n,
    Nat.rec (motive := fun _ => ℕ) 0 (fun t acc => Nat.add (g t) acc) n = ∑ t ∈ Finset.range n, g t
  | 0 => rfl
  | n + 1 => by
    rw [Finset.sum_range_succ, ← f14fg_recSum g n]
    exact Nat.add_comm (g n) _

theorem f14fg_sumBelow_count {m hi : ℕ} (c : ℕ → Bool) (hm : m ≤ 64 * hi) :
    sumBelow m hi (fun i => nIf(c i, 1, 0)) =
      ((Finset.range m).filter fun i => c i = true).card := by
  set F : ℕ → ℕ := fun i => nIf(Nat.blt i m, nIf(c i, 1, 0), 0) with hFdef
  have e : ∀ h l : ℕ, Nat.add (Nat.shiftLeft h 6) l = 64 * h + l := fun h l => by
    change h <<< 6 + l = _
    rw [Nat.shiftLeft_eq, (rfl : (2 : ℕ) ^ 6 = 64)]
    ring
  have eS : sumBelow m hi (fun i => nIf(c i, 1, 0)) =
      ∑ h ∈ Finset.range hi, ∑ l ∈ Finset.range 64, F (64 * h + l) := by
    unfold sumBelow
    rw [f14fg_recSum]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [f14fg_recSum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← e]
  have eD : ∀ n, ∑ h ∈ Finset.range n, ∑ l ∈ Finset.range 64, F (64 * h + l) =
      ∑ i ∈ Finset.range (64 * n), F i := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih, Nat.mul_succ, Finset.sum_range_add]
  have eM : ∑ i ∈ Finset.range (64 * hi), F i = ∑ i ∈ Finset.range m, nIf(c i, 1, 0) := by
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hm
    rw [hd, Finset.sum_range_add]
    have h0 : ∑ x ∈ Finset.range d, F (m + x) = 0 := by
      refine Finset.sum_eq_zero fun x _ => ?_
      have hc : Nat.blt (m + x) m = false := by
        cases hb : Nat.blt (m + x) m
        · rfl
        · have := Nat.le_of_ble_eq_true hb
          omega
      simp only [hFdef, hc]
    rw [h0, add_zero]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hc : Nat.blt i m = true := by rw [Nat.blt_eq]; exact Finset.mem_range.1 hi
    simp only [hFdef, hc]
  rw [eS]
  rw [eD]
  rw [eM]
  simp only [Finset.card_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  cases c i
  · simp
  · simp

theorem f14fg_M128 : M128 = 2 ^ 128 - 1 := by decide

theorem f14fg_latM_lt (L k i : ℕ) (hi : (latM L k).testBit i = true) : i < 128 := by
  change ((L >>> (128 * k)) &&& M128).testBit i = true at hi
  rw [Nat.testBit_and, f14fg_M128, Nat.testBit_two_pow_sub_one, Bool.and_eq_true,
    decide_eq_true_eq] at hi
  exact hi.2

theorem f14fg_subM_of {X Y : ℕ} (hX : ∀ i, X.testBit i = true → i < 128)
    (h : ∀ i < 128, hasB X i = true → hasB Y i = true) : subM X Y = true := by
  unfold subM
  rw [Nat.beq_eq]
  apply Nat.eq_of_testBit_eq
  intro i
  change (X &&& Y).testBit i = X.testBit i
  rw [Nat.testBit_and]
  cases hx : X.testBit i
  · rfl
  · have := h i (hX i hx) (by rw [hasB_eq]; exact hx)
    rw [hasB_eq] at this
    rw [this]
    rfl

theorem f14fg_subM_spec {X Y : ℕ} (h : subM X Y = true) :
    ∀ i, hasB X i = true → hasB Y i = true := by
  have e : Nat.land X Y = X := Nat.eq_of_beq_eq_true h
  intro i hi
  rw [hasB_eq] at hi ⊢
  rw [← e] at hi
  change (X &&& Y).testBit i = true at hi
  rw [Nat.testBit_and, Bool.and_eq_true] at hi
  exact hi.2

theorem f14fg_hasB_one (i : ℕ) : hasB 1 i = true ↔ i = 0 := by
  rw [hasB_eq, Nat.testBit_one_eq_true_iff_self_eq_zero]

theorem f14fg_wIdx_bit (k : ℕ) : ∀ ws : List ℕ,
    (wIdx ws).testBit k = true ↔ ∃ w ∈ ws, Nat.land w 511 = k
  | [] => by
    change (0 : ℕ).testBit k = true ↔ _
    simp
  | w :: ws => by
    change (1 <<< Nat.land w 511 ||| wIdx ws).testBit k = true ↔ _
    rw [Nat.testBit_or, Bool.or_eq_true, f14fg_wIdx_bit k ws, Nat.one_shiftLeft,
      Nat.testBit_two_pow, decide_eq_true_eq]
    simp only [List.mem_cons, exists_eq_or_imp]

theorem f14fg_ys14 (Y0 Y1 Y2 Y3 Y4 j : ℕ) :
    ys14 Y0 Y1 Y2 Y3 Y4 j = Y0 ∨ ys14 Y0 Y1 Y2 Y3 Y4 j = Y1 ∨ ys14 Y0 Y1 Y2 Y3 Y4 j = Y2 ∨
      ys14 Y0 Y1 Y2 Y3 Y4 j = Y3 ∨ ys14 Y0 Y1 Y2 Y3 Y4 j = Y4 := by
  unfold ys14
  cases Nat.beq j 0 <;> cases Nat.beq j 1 <;> cases Nat.beq j 2 <;> cases Nat.beq j 3 <;> simp

section Tables

variable {Γ : Type} [Group Γ] {elt : ℕ → Γ} {P C V Q : ℕ} (hR : RealT elt P C V Q)
include hR

theorem f14fg_isPGroup {K : Subgroup Γ} (hK : ∀ x ∈ K, ∃ i < 128, elt i = x) : IsPGroup 2 K := by
  let T : Subgroup Γ :=
    { carrier := {g | ∃ i < 128, elt i = g}
      mul_mem' := by
        rintro _ _ ⟨i, hi, rfl⟩ ⟨j, hj, rfl⟩
        exact ⟨_, atR_lt _ _, hR.mulP hi hj⟩
      one_mem' := ⟨0, by norm_num, hR.one⟩
      inv_mem' := by
        rintro _ ⟨i, hi, rfl⟩
        exact ⟨_, atR_lt _ _, hR.inv hi⟩ }
  have hT : (T : Set Γ) = elt '' ((Finset.range 128 : Finset ℕ) : Set ℕ) := by
    ext g
    simp only [Finset.coe_range, Set.mem_image, Set.mem_Iio]
    rfl
  have hcard : Nat.card T = 2 ^ 7 := by
    have h1 : Nat.card T = (T : Set Γ).ncard := rfl
    rw [h1, hT, Set.InjOn.ncard_image, Set.ncard_coe_finset, Finset.card_range]
    · rfl
    · intro i hi j hj he
      exact hR.inj i (by simpa using hi) j (by simpa using hj) he
  have hle : K ≤ T := fun x hx => hK x hx
  exact (IsPGroup.of_card hcard).to_le hle

theorem f14fg_conjM_mset (X : ℕ) {s : ℕ} (hs : s < 128) :
    mset elt (conjM P C V s X) = (fun g => elt s * g * (elt s)⁻¹) '' mset elt X := by
  have e : conjM P C V s X = Nat.rec (motive := fun _ => Nat) 0 (fun i acc =>
      nIf(hasB X i, Nat.lor acc (Nat.shiftLeft 1 (conjR (rowT P s) (rowT C (atR V s)) i)), acc))
      128 := by
    simp only [conjM, strictN_eq]
  rw [e, mset_recMask (hasB X) (fun i => conjR (rowT P s) (rowT C (atR V s)) i)
    fun _ _ => atR_lt _ _]
  ext g
  constructor
  · rintro ⟨i, hi, hb, rfl⟩
    exact ⟨elt i, ⟨i, hi, hb, rfl⟩, (conjR_elt hR hs hi).symm⟩
  · rintro ⟨_, ⟨i, hi, hb, rfl⟩, rfl⟩
    exact ⟨i, hi, hb, conjR_elt hR hs hi⟩

theorem f14fg_cenS_mset (X : ℕ) : ∀ gs : List ℕ, (∀ g ∈ gs, g < 128) →
    mset elt (cenS P C X gs) = {x | x ∈ mset elt X ∧ ∀ g ∈ gs, x * elt g = elt g * x}
  | [], _ => by
    change mset elt X = _
    ext x
    simp
  | g :: gs, h => by
    have e : cenS P C X (g :: gs) = cenE P C (cenS P C X gs) g := rfl
    rw [e, cenE_mset hR _ (h g (by simp)),
      f14fg_cenS_mset X gs (fun g' hg' => h g' (by simp [hg']))]
    ext x
    simp only [Set.mem_setOf_eq, List.mem_cons, forall_eq_or_imp]
    tauto

theorem f14fg_sq_one_iff (K : ℕ) :
    subM (imgR Q K) 1 = true ↔ ∀ x ∈ mset elt K, x * x = 1 := by
  constructor
  · intro h
    rintro _ ⟨i, hi, hb, rfl⟩
    have h1 := f14fg_subM_spec h (atR Q i) ((imgR_bit Q K _).2 ⟨i, hi, hb, rfl⟩)
    rw [f14fg_hasB_one] at h1
    rw [← hR.sq hi, h1, hR.one]
  · intro h
    refine f14fg_subM_of (fun i hi => testBit_imgR_lt hi) fun k _ hk => ?_
    obtain ⟨i, hi, hb, rfl⟩ := (imgR_bit Q K k).1 hk
    rw [f14fg_hasB_one]
    refine hR.inj _ (atR_lt _ _) _ (by norm_num) ?_
    rw [hR.sq hi, hR.one]
    exact h _ ⟨i, hi, hb, rfl⟩

end Tables

section Gen

variable {Γ : Type} [Group Γ] [Finite Γ] {elt : ℕ → Γ} {P C V Q : ℕ}

theorem f14fg_gen4 {L OR RG N : ℕ} {G₀ : Subgroup Γ} (hR : RealT elt P C V Q)
    (hlat : (∀ k < N, ∃ K : Subgroup Γ, K ≤ G₀ ∧ RepM elt (latM L k) (K : Set Γ)) ∧
      ∀ K ≤ G₀, ∃ k < N, RepM elt (latM L k) (K : Set Γ))
    (hN : N ≤ 448) (ho : ordK L OR 0 N = true) (hrg : rgK L RG N = true)
    (hall : ∀ k < N, ∃ lo w, lo ≤ k ∧ k < lo + w ∧ w ≤ 448 ∧ rgAllK L OR RG N lo w = true) :
    ∀ K : Subgroup Γ, K ≤ G₀ → ∃ s : Finset Γ, s.card ≤ 4 ∧ closure (s : Set Γ) = K := by
  classical
  intro K hK
  obtain ⟨k, hk, hKr⟩ := hlat.2 K hK
  obtain ⟨g, -, hG⟩ := hlat.2 G₀ le_rfl
  have hall' : ∀ k < N, ∀ h < N, 2 * ordAt OR h = ordAt OR k →
      subM (entL L h) (entL L k) = true → outB (entL L h) (rgAt RG k) = true := by
    intro k hk h hh
    obtain ⟨lo, w, hlo, hkw, hw, hra⟩ := hall k hk
    have e : lo + (k - lo) = k := by omega
    have := rgAllK_spec hra hN hw (k - lo) (by omega) h hh
    rw [e] at this
    exact this
  obtain ⟨h4, he⟩ := rg_closure hR.inj hlat (f14fg_isPGroup hR hG.2) hN hrg (ordK_spec ho hN)
    hall' hk hKr
  refine ⟨(Finset.range (Nat.land (rgAt RG k) 7)).image fun t => elt (genAt (rgAt RG k) t),
    Finset.card_image_le.trans (by simpa using h4), ?_⟩
  rw [he]
  congr 1
  ext x
  simp [rgSet]

end Gen

section Frame

variable {Γ : Type} [Group Γ] [Finite Γ] {fr : Frame Γ} {elt : ℕ → Γ} {P C V Q : ℕ}

theorem f14fg_gens (hg : ∀ s < 5, elt (s + 1) = sGen fr s) :
    elt 1 = fr.a₁ ∧ elt 2 = fr.b₁ ∧ elt 3 = fr.a₂ ∧ elt 4 = fr.b₂ ∧ elt 5 = fr.h₀ := by
  have h0 := hg 0 (by norm_num)
  have h1 := hg 1 (by norm_num)
  have h2 := hg 2 (by norm_num)
  have h3 := hg 3 (by norm_num)
  have h4 := hg 4 (by norm_num)
  rw [sGen_zero] at h0
  rw [sGen_one] at h1
  rw [sGen_two] at h2
  rw [sGen_three] at h3
  rw [sGen_four] at h4
  exact ⟨h0, h1, h2, h3, h4⟩

theorem f14fg_prods (hR : RealT elt P C V Q) (hg : ∀ s < 5, elt (s + 1) = sGen fr s) :
    elt (atR Q 2) = fr.z ∧ elt (mulE P 1 3) = fr.a₁ * fr.a₂ ∧
      elt (mulE P 2 4) = fr.b₁ * fr.b₂ ∧ elt (mulE P 1 4) = fr.a₁ * fr.b₂ ∧
      elt (mulE P 2 3) = fr.b₁ * fr.a₂ ∧
      elt (mulE P (mulE P 1 2) 3) = fr.a₁ * fr.b₁ * fr.a₂ := by
  obtain ⟨e1, e2, e3, e4, -⟩ := f14fg_gens hg
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hR.sq (i := 2) (by norm_num), e2]
    exact (pow_two _).symm
  · rw [mulE_elt hR (x := 1) (y := 3) (by norm_num) (by norm_num), e1, e3]
  · rw [mulE_elt hR (x := 2) (y := 4) (by norm_num) (by norm_num), e2, e4]
  · rw [mulE_elt hR (x := 1) (y := 4) (by norm_num) (by norm_num), e1, e4]
  · rw [mulE_elt hR (x := 2) (y := 3) (by norm_num) (by norm_num), e2, e3]
  · rw [mulE_elt hR (x := mulE P 1 2) (y := 3) (f13_mulE_lt _ _ _) (by norm_num),
      mulE_elt hR (x := 1) (y := 2) (by norm_num) (by norm_num), e1, e2, e3]

theorem f14fg_S_le : fr.S ≤ fr.Sσ := by
  unfold SFrame.S Frame.Sσ
  refine closure_mono fun x hx => ?_
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
  tauto

theorem f14fg_A_le : fr.A ≤ fr.S := by
  unfold SFrame.A SFrame.S
  refine closure_mono fun x hx => ?_
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
  tauto

theorem f14fg_lt3 {a b c : ℕ} (ha : a < 128) (hb : b < 128) (hc : c < 128) :
    ∀ g ∈ [a, b, c], g < 128 := by
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl
  exacts [ha, hb, hc]

theorem f14fg_clos3 (hR : RealT elt P C V Q) {a b c R : ℕ} (ha : a < 128) (hb : b < 128)
    (hc : c < 128) (h : closOK C [a, b, c] R = true) :
    mset elt (closK C [a, b, c] R) = (closure {elt a, elt b, elt c} : Set Γ) := by
  rw [closK_closure hR (f14fg_lt3 ha hb hc) h, f13_setOf_eq_map]
  simp only [List.map_cons, List.map_nil]
  rw [f13_setOf_three]

theorem f14fg_S (hR : RealT elt P C V Q) (hg : ∀ s < 5, elt (s + 1) = sGen fr s) {R : ℕ}
    (h : closOK C [1, 2, 3, 4, 5] R = true) :
    mset elt (closK C [1, 2, 3, 4, 5] R) = (fr.S : Set Γ) := by
  obtain ⟨e1, e2, e3, e4, e5⟩ := f14fg_gens hg
  rw [closK_closure hR (by decide) h, f13_setOf_eq_map]
  simp only [List.map_cons, List.map_nil, e1, e2, e3, e4, e5]
  rw [f13_setOf_five]
  rfl

theorem f14fg_rep_eq {m : ℕ} {X Y : Subgroup Γ} (hX : RepM elt m (X : Set Γ))
    (hY : RepM elt m (Y : Set Γ)) : X = Y :=
  SetLike.coe_injective (hX.eq_mset.trans hY.eq_mset.symm)

theorem f14fg_seven {L OR RG N R : ℕ} (hR : RealT elt P C V Q)
    (hg : ∀ s < 5, elt (s + 1) = sGen fr s)
    (hlat : (∀ k < N, ∃ K : Subgroup Γ, K ≤ fr.Sσ ∧ RepM elt (latM L k) (K : Set Γ)) ∧
      ∀ K ≤ fr.Sσ, ∃ k < N, RepM elt (latM L k) (K : Set Γ))
    (hN : N ≤ 448) (ho : ordK L OR 0 N = true) (hrg : rgK L RG N = true)
    (hall : ∀ k < N, ∃ lo w, lo ≤ k ∧ k < lo + w ∧ w ≤ 448 ∧ rgAllK L OR RG N lo w = true)
    (h : f14gK P C V Q L N 1 2 3 4 5 R = true) :
    CFSG.Open.pRank 2 fr.S = 3 ∧ GH74.sectionalTwoRank ↥fr.S = 4 := by
  classical
  have hinj := hR.inj
  obtain ⟨e1, e2, e3, e4, -⟩ := f14fg_gens hg
  obtain ⟨hz, -⟩ := f14fg_prods hR hg
  simp only [f14gK, bAnd_eq, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨hcS, hcA, hcZ, hpr, hsec⟩ := h
  have hS := f14fg_S hR hg hcS
  set Sm := closK C [1, 2, 3, 4, 5] R
  have hSσ : fr.S ≤ fr.Sσ := f14fg_S_le
  have hent : ∀ k < N, ∃ K : Subgroup Γ, RepM elt (latM L k) (K : Set Γ) := fun k hk =>
    (hlat.1 k hk).elim fun K hK => ⟨K, hK.2⟩
  constructor
  ·
    simp only [pRankK, strictN_eq] at hpr
    obtain ⟨hmax, hatt⟩ := maxBelow_spec (m := N) (hi := 7) (fun k => nIf(bAnd(subM (entL L k) Sm,
      Nat.beq (imgR Q (entL L k)) 1), pop (entL L k), 0)) (by omega)
    rw [hpr] at hmax hatt
    unfold CFSG.Open.pRank
    have hcond : ∀ k < N, ∀ K : Subgroup Γ, RepM elt (latM L k) (K : Set Γ) →
        (bAnd(subM (entL L k) Sm, Nat.beq (imgR Q (entL L k)) 1) = true ↔
          K ≤ fr.S ∧ ∀ x ∈ K, x * x = 1) := by
      intro k hk K hK
      rw [bAnd_eq, Bool.and_eq_true, Nat.beq_eq]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨fun x hx => ?_, fun x hx => ?_⟩
        · obtain ⟨i, hi, rfl⟩ := hK.2 x hx
          have := f14fg_subM_spec h1 i ((hK.1 i hi).2 hx)
          rw [← SetLike.mem_coe, ← hS]
          exact ⟨i, hi, this, rfl⟩
        · have hsq := (f14fg_sq_one_iff hR (entL L k)).1 (by
            rw [h2]
            exact f14fg_subM_of (fun i hi => by
              rw [Nat.testBit_one_eq_true_iff_self_eq_zero] at hi; omega) fun i _ hi => hi)
          have hx' : x ∈ mset elt (latM L k) := by
            rw [← hK.eq_mset]
            exact hx
          exact hsq x hx'
      · rintro ⟨h1, h2⟩
        refine ⟨f14fg_subM_of (fun i hi => f14fg_latM_lt L k i hi) fun i hi hb => ?_, ?_⟩
        · have hx := h1 ((hK.1 i hi).1 hb)
          rw [← SetLike.mem_coe, ← hS] at hx
          exact (mem_mset_iff hinj hi).1 hx
        · apply Nat.eq_of_testBit_eq
          intro j
          rw [← hasB_eq, ← hasB_eq, Bool.eq_iff_iff, imgR_bit, f14fg_hasB_one]
          constructor
          · rintro ⟨i, hi, hb, rfl⟩
            refine hR.inj _ (atR_lt _ _) _ (by norm_num) ?_
            rw [hR.sq hi, hR.one]
            exact h2 _ ((hK.1 i hi).1 hb)
          · rintro rfl
            refine ⟨0, by norm_num, (hK.1 0 (by norm_num)).2 (by rw [hR.one]; exact K.one_mem), ?_⟩
            refine hR.inj _ (atR_lt _ _) _ (by norm_num) ?_
            rw [hR.sq (by norm_num), hR.one, one_mul]
    have hval : ∀ k < N, ∀ K : Subgroup Γ, RepM elt (latM L k) (K : Set Γ) →
        K ≤ fr.S → (∀ x ∈ K, x * x = 1) → Nat.card K ≤ 8 := by
      intro k hk K hK h1 h2
      have := hmax k hk
      rw [(hcond k hk K hK).2 ⟨h1, h2⟩] at this
      have hc : Nat.card K = pop (latM L k) := pop_sound hinj hK
      rw [hc]
      exact this
    apply le_antisymm
    · apply csSup_le
      · rcases hatt with h0 | ⟨k, hk, he⟩
        · exact absurd h0 (by norm_num)
        · exact ⟨0, ⊥, bot_le, (isElemAbelian_iff_sq).2 fun x hx => by
            rw [Subgroup.mem_bot] at hx; rw [hx, one_mul], by simp⟩
      · rintro j ⟨E, hE, hEa, hEc⟩
        obtain ⟨k, hk, hKr⟩ := hlat.2 E (hE.trans hSσ)
        have := hval k hk E hKr hE ((isElemAbelian_iff_sq).1 hEa)
        rw [hEc] at this
        by_contra hj
        have : 2 ^ 4 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
    · apply le_csSup
      · refine ⟨Nat.card Γ, ?_⟩
        rintro j ⟨E, -, -, hEc⟩
        have hc : Nat.card E ≤ Nat.card Γ := Subgroup.card_le_card_group E
        rw [hEc] at hc
        exact (Nat.lt_two_pow_self).le.trans hc
      · rcases hatt with h0 | ⟨k, hk, he⟩
        · exact absurd h0 (by norm_num)
        · obtain ⟨K, hK⟩ := hent k hk
          have hne : bAnd(subM (entL L k) Sm, Nat.beq (imgR Q (entL L k)) 1) = true := by
            cases hb : bAnd(subM (entL L k) Sm, Nat.beq (imgR Q (entL L k)) 1)
            · rw [hb] at he
              exact absurd he (by norm_num)
            · rfl
          rw [hne] at he
          obtain ⟨h1, h2⟩ := (hcond k hk K hK).1 hne
          refine ⟨K, h1, (isElemAbelian_iff_sq).2 h2, ?_⟩
          have hc0 : Nat.card K = pop (latM L k) := pop_sound hinj hK
          rw [hc0]
          exact he
  ·
    have hgen := f14fg_gen4 hR hlat hN ho hrg hall
    have hSp : IsPGroup 2 fr.S := f14fg_isPGroup hR fun x hx => by
      rw [← SetLike.mem_coe, ← hS] at hx
      obtain ⟨i, hi, -, he⟩ := hx
      exact ⟨i, hi, he⟩
    simp only [secEK, bAnd_eq, Bool.and_eq_true, Nat.beq_eq] at hsec
    obtain ⟨hZA, hnM, hsqM, hpop⟩ := hsec
    have hA : mset elt (closK C [1, 2, 3, 4] R) = (fr.A : Set Γ) := by
      rw [closK_closure hR (by decide) hcA, f13_setOf_eq_map]
      simp only [List.map_cons, List.map_nil, e1, e2, e3, e4]
      have e : {x | x ∈ [fr.a₁, fr.b₁, fr.a₂, fr.b₂]} = ({fr.a₁, fr.b₁, fr.a₂, fr.b₂} : Set Γ) := by
        ext x
        simp
      rw [e]
      rfl
    have hZ : mset elt (closK C [atR Q 2] R) = (fr.Z : Set Γ) := by
      rw [closK_closure hR (fun g hg => by rw [List.mem_singleton.1 hg]; exact atR_lt _ _) hcZ,
        f13_setOf_eq_map]
      simp only [List.map_cons, List.map_nil, hz]
      rw [f13_setOf_one]
      unfold SFrame.Z
      rw [Subgroup.zpowers_eq_closure]
    set Am := closK C [1, 2, 3, 4] R
    set Zm := closK C [atR Q 2] R
    have hAr : RepM elt Am (fr.A : Set Γ) := hA ▸ repM_mset hinj Am
    have hZr : RepM elt Zm (fr.Z : Set Γ) := hZ ▸ repM_mset hinj Zm
    have hZleA : fr.Z ≤ fr.A := fun x hx => by
      obtain ⟨i, hi, he⟩ := hZr.2 x hx
      subst he
      exact (hAr.1 i hi).1 (f14fg_subM_spec hZA i ((hZr.1 i hi).2 hx))
    have hnorm : (fr.Z.subgroupOf fr.A).Normal := by
      constructor
      intro n hn g
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      obtain ⟨i, hi, he⟩ := hAr.2 g g.2
      simp only [normM, strictB_eq] at hnM
      have h1 := allBelow_spec hnM (by norm_num) i hi
      rw [(hAr.1 i hi).2 (he ▸ g.2)] at h1
      have h2 : Nat.beq (conjM P C V i Zm) Zm = true := h1
      have hc := congrArg (mset elt) (Nat.eq_of_beq_eq_true h2)
      rw [f14fg_conjM_mset hR _ hi, hZ] at hc
      have : elt i * (n : Γ) * (elt i)⁻¹ ∈ (fr.Z : Set Γ) := hc ▸ ⟨(n : Γ), hn, rfl⟩
      rw [he] at this
      simpa using this
    have hsqA : ∀ a ∈ fr.A, a * a ∈ fr.Z := fun a ha => by
      obtain ⟨i, hi, rfl⟩ := hAr.2 a ha
      rw [← hR.sq hi]
      exact (hZr.1 _ (atR_lt _ _)).1 (f14fg_subM_spec hsqM _
        ((imgR_bit Q Am _).2 ⟨i, hi, (hAr.1 i hi).2 ha, rfl⟩))
    let Y := ↥fr.A ⧸ fr.Z.subgroupOf fr.A
    have hYsq : ∀ y : Y, y * y = 1 := by
      intro y
      induction y using QuotientGroup.induction_on with
      | H a =>
        rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
        exact hsqA a a.2
    have hYc : Nat.card Y = 16 := by
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (fr.Z.subgroupOf fr.A)
      have h2 : Nat.card (fr.Z.subgroupOf fr.A) = Nat.card fr.Z :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZleA).toEquiv
      have hAc : Nat.card fr.A = pop Am := pop_sound hinj hAr
      have hZc : Nat.card fr.Z = pop Zm := pop_sound hinj hZr
      have hpos : 0 < Nat.card fr.Z := Nat.card_pos
      rw [h2, hAc, hpop, ← hZc] at h1
      exact (Nat.eq_of_mul_eq_mul_right hpos h1).symm
    exact CFSG.OddStandard.HigherRank.G2Three.Sec1Proof.Tab.sectionalTwoRank_eq_of_data hSp
      f14fg_A_le (k := 4) (by norm_num) (fun P hP => hgen P (hP.trans hSσ))
      (QuotientGroup.mk' (fr.Z.subgroupOf fr.A)) (QuotientGroup.mk'_surjective _)
      fun s hs => f14fg_E16_not_gen3 hYsq hYc s (by simpa using hs)

theorem f14fg_nIf2_bit (a b : Bool) (k j : ℕ) :
    (nIf(a, nIf(b, Nat.shiftLeft 1 k, 0), 0)).testBit j = true ↔ (a && b) = true ∧ j = k := by
  cases a
  · simp
  · exact f14fg_nIf_bit b k j

theorem f14fg_subM_le (hR : RealT elt P C V Q) {L k X : ℕ} {K T : Subgroup Γ}
    (hK : RepM elt (latM L k) (K : Set Γ)) (hX : mset elt X = (T : Set Γ)) :
    subM (entL L k) X = true ↔ K ≤ T := by
  constructor
  · intro h x hx
    obtain ⟨i, hi, rfl⟩ := hK.2 x hx
    rw [← SetLike.mem_coe, ← hX]
    exact ⟨i, hi, f14fg_subM_spec h i ((hK.1 i hi).2 hx), rfl⟩
  · intro h
    refine f14fg_subM_of (fun i hi => f14fg_latM_lt L k i hi) fun i hi hb => ?_
    have hx := h ((hK.1 i hi).1 hb)
    rw [← SetLike.mem_coe, ← hX] at hx
    exact (mem_mset_iff hR.inj hi).1 hx

theorem f14fg_six {L N R : ℕ} {ws : List ℕ} (hR : RealT elt P C V Q)
    (hg : ∀ s < 5, elt (s + 1) = sGen fr s)
    (hlat : (∀ k < N, ∃ K : Subgroup Γ, K ≤ fr.Sσ ∧ RepM elt (latM L k) (K : Set Γ)) ∧
      ∀ K ≤ fr.Sσ, ∃ k < N, RepM elt (latM L k) (K : Set Γ))
    (hdist : ∀ k < N, ∀ k' < N, latM L k = latM L k' → k = k') (hN : N ≤ 448)
    (h : f14fK P C V Q L N 1 2 3 4 5 R ws = true) :
    (maxElemAbelian fr.S).ncard = 8 ∧
    ∀ Y ∈ maxElemAbelian fr.S, ∃ s ∈ fr.S, ∃ Y₀ ∈ ({fr.E, fr.F, cen fr.B ⊔ closure {fr.h₀},
      closure {fr.a₁ * fr.b₂, fr.b₁ * fr.a₂, fr.z}, closure {fr.a₁ * fr.b₂, fr.a₁ * fr.b₁ * fr.a₂,
        fr.z}} : Set (Subgroup Γ)), Y = conjSub s Y₀ := by
  classical
  have hinj := hR.inj
  obtain ⟨e1, e2, e3, e4, e5⟩ := f14fg_gens hg
  obtain ⟨hz, h13, h24, h14, h23, h123⟩ := f14fg_prods hR hg
  simp only [f14fK, bAnd_eq, strictB_eq, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨hcS, hcB, hc0, hc1, hcH, hc3, hc4, hB, hperm, hcnt, hw, hlist⟩ := h
  have hS := f14fg_S hR hg hcS
  set Sm := closK C [1, 2, 3, 4, 5] R
  have hSσ : fr.S ≤ fr.Sσ := f14fg_S_le
  have hlt := f13_mulE_lt
  have hgB : ∀ g ∈ [mulE P 1 3, 2, 4, 5], g < 128 := by
    intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl
    exacts [hlt _ _ _, by norm_num, by norm_num, by norm_num]
  have hBm : mset elt (cenE P C Sm (mulE P 2 4)) = (fr.B : Set Γ) := by
    rw [cenE_mset hR _ (hlt _ _ _), hS, h24]
    ext x
    unfold SFrame.B centIn
    simp only [Set.mem_setOf_eq, SetLike.mem_coe, Subgroup.mem_inf, mem_centralizer_iff]
    constructor
    · rintro ⟨hx, hc⟩
      refine ⟨hx, fun y hy => (f14fg_comm_closure (s := {fr.b₁ * fr.b₂}) (x := x) ?_ y hy).symm⟩
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      subst hg
      exact hc
    · rintro ⟨hx, hc⟩
      exact ⟨hx, (hc _ (subset_closure (Set.mem_singleton _))).symm⟩
  have hBc : (fr.B : Set Γ) =
      (closure {x | ∃ g ∈ [mulE P 1 3, 2, 4, 5], elt g = x} : Set Γ) := by
    rw [← hBm, hB, closK_closure hR hgB hcB]
  have hZB : mset elt (cenS P C (cenE P C Sm (mulE P 2 4)) [mulE P 1 3, 2, 4, 5]) =
      (cen fr.B : Set Γ) := by
    rw [f14fg_cenS_mset hR _ _ hgB, hBm]
    ext x
    unfold cen
    simp only [Set.mem_setOf_eq, SetLike.mem_coe, Subgroup.mem_inf, mem_centralizer_iff]
    constructor
    · rintro ⟨hx, hc⟩
      refine ⟨hx, fun y hy => ?_⟩
      have hy' : y ∈ closure {x | ∃ g ∈ [mulE P 1 3, 2, 4, 5], elt g = x} := by
        rw [← SetLike.mem_coe, ← hBc]
        exact hy
      refine (f14fg_comm_closure ?_ y hy').symm
      rintro _ ⟨g, hg, rfl⟩
      exact hc g hg
    · rintro ⟨hx, hc⟩
      refine ⟨hx, fun g hg => (hc _ ?_).symm⟩
      rw [← SetLike.mem_coe, hBc]
      exact subset_closure ⟨g, hg, rfl⟩
  have hH0 : mset elt (closK C [5] R) = (closure {fr.h₀} : Set Γ) := by
    rw [closK_closure hR (by decide) hcH, f13_setOf_eq_map]
    simp only [List.map_cons, List.map_nil, e5]
    rw [f13_setOf_one]
  have hY2 : mset elt (prodM C (cenS P C (cenE P C Sm (mulE P 2 4)) [mulE P 1 3, 2, 4, 5])
      (closK C [5] R)) = ((cen fr.B ⊔ closure {fr.h₀} : Subgroup Γ) : Set Γ) := by
    have hp := permB_spec hR hperm
    rw [hZB, hH0] at hp
    rw [prodM_mset hR, hZB, hH0, f13_coe_sup hp]
  have hY0 := f14fg_clos3 hR (hlt _ _ _) (hlt _ _ _) (atR_lt _ _) hc0
  have hY1 := f14fg_clos3 hR (hlt _ _ _) (hlt _ _ _) (atR_lt _ _) hc1
  have hY3 := f14fg_clos3 hR (hlt _ _ _) (hlt _ _ _) (atR_lt _ _) hc3
  have hY4 := f14fg_clos3 hR (hlt _ _ _) (hlt _ _ _) (atR_lt _ _) hc4
  rw [h24, h123, hz] at hY0
  rw [h13, h24, hz] at hY1
  rw [h14, h23, hz] at hY3
  rw [h14, h123, hz] at hY4
  let ent : ℕ → Subgroup Γ := fun k => if hk : k < N then (hlat.1 k hk).choose else ⊥
  have hentR : ∀ k (hk : k < N), RepM elt (latM L k) (ent k : Set Γ) := fun k hk => by
    simp only [ent, dif_pos hk]
    exact (hlat.1 k hk).choose_spec.2
  have hent_of : ∀ k (hk : k < N) (K : Subgroup Γ), RepM elt (latM L k) (K : Set Γ) → K = ent k :=
    fun k hk K hK => f14fg_rep_eq hK (hentR k hk)
  have hea : ∀ k (hk : k < N), (subM 1 (entL L k) && (subM (entL L k) Sm &&
      subM (imgR Q (entL L k)) 1)) = true ↔ ent k ≤ fr.S ∧ CFSG.Open.IsElemAbelian 2 (ent k) := by
    intro k hk
    have hK := hentR k hk
    have h1 : subM 1 (entL L k) = true := by
      refine f14fg_subM_of (fun i hi => by
        rw [Nat.testBit_one_eq_true_iff_self_eq_zero] at hi; omega) fun i _ hi => ?_
      rw [f14fg_hasB_one] at hi
      subst hi
      exact (hK.1 0 (by norm_num)).2 (by rw [hR.one]; exact (ent k).one_mem)
    rw [h1, Bool.true_and, Bool.and_eq_true, f14fg_subM_le hR hK hS, f14fg_sq_one_iff hR,
      isElemAbelian_iff_sq]
    change _ ∧ (∀ x ∈ mset elt (latM L k), _) ↔ _
    rw [← hK.eq_mset]
    rfl
  set Cm := secC Q L N Sm 1
  have hCm : ∀ k, hasB Cm k = true ↔ k < N ∧ ent k ≤ fr.S ∧
      CFSG.Open.IsElemAbelian 2 (ent k) := by
    intro k
    rw [hasB_eq]
    simp only [Cm, secC, strictN_eq]
    rw [f14fg_orBelow_idx _ _ (by omega) (fun k j => f14fg_nIf_bit _ k j)]
    constructor
    · rintro ⟨hk, hc⟩
      exact ⟨hk, (hea k hk).1 (by simpa only [bAnd_eq] using hc)⟩
    · rintro ⟨hk, hc⟩
      exact ⟨hk, by simpa only [bAnd_eq] using (hea k hk).2 hc⟩
  set Mx := maxIdx L Cm N
  have hMx : ∀ k, hasB Mx k = true ↔ k < N ∧ ent k ∈ maxElemAbelian fr.S := by
    intro k
    rw [hasB_eq]
    simp only [Mx, maxIdx, strictN_eq, strictB_eq]
    rw [f14fg_orBelow_idx _ _ (by omega) (fun k j => f14fg_nIf2_bit _ _ k j)]
    refine and_congr_right fun hk => ?_
    rw [Bool.and_eq_true, allBelow_iff (by omega), hCm]
    have hrow : ∀ k' < N, bIf(hasB Cm k', bIf(subM (entL L k) (entL L k'),
        Nat.beq (entL L k) (entL L k'), true), true) = true ↔
        (ent k' ≤ fr.S → CFSG.Open.IsElemAbelian 2 (ent k') → ent k ≤ ent k' → ent k = ent k') := by
      intro k' hk'
      have hsub : subM (entL L k) (entL L k') = true ↔ ent k ≤ ent k' :=
        f14fg_subM_le hR (hentR k hk) (hentR k' hk').eq_mset.symm
      have heq : entL L k = entL L k' ↔ ent k = ent k' := by
        constructor
        · intro he
          have h' : RepM elt (latM L k) (ent k' : Set Γ) := by
            change RepM elt (entL L k) _
            rw [he]
            exact hentR k' hk'
          exact f14fg_rep_eq (hentR k hk) h'
        · intro he
          refine eq_of_mset_eq hinj (f14fg_latM_lt L k) (f14fg_latM_lt L k') ?_
          change mset elt (latM L k) = mset elt (latM L k')
          rw [← (hentR k hk).eq_mset, ← (hentR k' hk').eq_mset, he]
      cases hc : hasB Cm k'
      · have := (hCm k').not.1 (by rw [hc]; decide)
        simp only [hk', true_and, not_and] at this
        exact ⟨fun _ h1 h2 => absurd h2 (this h1), fun _ => rfl⟩
      · obtain ⟨-, h1, h2⟩ := (hCm k').1 hc
        cases hs : subM (entL L k) (entL L k')
        · have := hsub.not.1 (by rw [hs]; decide)
          exact ⟨fun _ _ _ h3 => absurd h3 this, fun _ => rfl⟩
        · change Nat.beq (entL L k) (entL L k') = true ↔ _
          rw [Nat.beq_eq, heq]
          exact ⟨fun he _ _ _ => he, fun hh => hh h1 h2 (hsub.1 hs)⟩
    constructor
    · rintro ⟨⟨-, h1, h2⟩, hall⟩
      refine ⟨h1, h2, fun Y' hY' hY'S hY'a => ?_⟩
      obtain ⟨k', hk', hr⟩ := hlat.2 Y' (hY'S.trans hSσ)
      have e' := hent_of k' hk' Y' hr
      subst e'
      exact ((hrow k' hk').1 (hall k' hk') hY'S hY'a hY').symm
    · rintro ⟨h1, h2, hmaxY⟩
      refine ⟨⟨hk, h1, h2⟩, fun k' hk' => (hrow k' hk').2 fun h3 h4 h5 =>
        (hmaxY _ h5 h3 h4).symm⟩
  have hset : maxElemAbelian fr.S = ent '' {k | k < N ∧ hasB Mx k = true} := by
    ext Y
    constructor
    · intro hY
      obtain ⟨k, hk, hr⟩ := hlat.2 Y (hY.1.trans hSσ)
      have e' := hent_of k hk Y hr
      refine ⟨k, ⟨hk, (hMx k).2 ⟨hk, e' ▸ hY⟩⟩, e'.symm⟩
    · rintro ⟨k, ⟨hk, hb⟩, rfl⟩
      exact ((hMx k).1 hb).2
  have hio : Set.InjOn ent {k | k < N ∧ hasB Mx k = true} := by
    rintro k ⟨hk, -⟩ k' ⟨hk', -⟩ he
    refine hdist k hk k' hk' (eq_of_mset_eq hinj (f14fg_latM_lt L k) (f14fg_latM_lt L k') ?_)
    rw [← (hentR k hk).eq_mset, ← (hentR k' hk').eq_mset, he]
  have hfs : {k | k < N ∧ hasB Mx k = true} =
      (((Finset.range N).filter fun i => hasB Mx i = true : Finset ℕ) : Set ℕ) := by
    ext k
    simp
  have hcard : ((Finset.range N).filter fun i => hasB Mx i = true).card = 8 := by
    rw [← f14fg_sumBelow_count (hi := 7) (fun i => hasB Mx i) (by omega)]
    exact hcnt
  constructor
  · rw [hset]
    rw [hio.ncard_image]
    rw [hfs]
    rw [Set.ncard_coe_finset]
    exact hcard
  · intro Y hY
    rw [hset] at hY
    obtain ⟨k, ⟨hk, hb⟩, rfl⟩ := hY
    have hb' : (wIdx ws).testBit k = true := by
      rw [hw, ← hasB_eq]
      exact hb
    obtain ⟨w, hwm, hwk⟩ := (f14fg_wIdx_bit k ws).1 hb'
    have hwf := (listRecAnd_iff _ ws).1 hlist w hwm
    simp only [Bool.and_eq_true, Nat.beq_eq] at hwf
    obtain ⟨hsS, hent⟩ := hwf
    have hs := fld127_lt w 9
    refine ⟨elt (fld(w, 9, 127)), ?_, ?_⟩
    · rw [← SetLike.mem_coe, ← hS]
      exact ⟨_, hs, hsS, rfl⟩
    have hk' : mset elt (latM L k) = (fun g => elt (fld(w, 9, 127)) * g * (elt (fld(w, 9, 127)))⁻¹) ''
        mset elt (ys14 (closK C [mulE P 2 4, mulE P (mulE P 1 2) 3, atR Q 2] R)
          (closK C [mulE P 1 3, mulE P 2 4, atR Q 2] R)
          (prodM C (cenS P C (cenE P C Sm (mulE P 2 4)) [mulE P 1 3, 2, 4, 5]) (closK C [5] R))
          (closK C [mulE P 1 4, mulE P 2 3, atR Q 2] R)
          (closK C [mulE P 1 4, mulE P (mulE P 1 2) 3, atR Q 2] R) (Nat.shiftRight w 16)) := by
      rw [← f14fg_conjM_mset hR _ hs]
      change mset elt (entL L k) = _
      rw [← hwk, hent]
    have hconj : ∀ Y₀ : Subgroup Γ, ((conjSub (elt (fld(w, 9, 127))) Y₀ : Subgroup Γ) : Set Γ) =
        (fun g => elt (fld(w, 9, 127)) * g * (elt (fld(w, 9, 127)))⁻¹) '' (Y₀ : Set Γ) := by
      intro Y₀
      unfold conjSub
      rw [Subgroup.coe_map]
      rfl
    have fin : ∀ Y₀ : Subgroup Γ, mset elt (ys14 (closK C [mulE P 2 4, mulE P (mulE P 1 2) 3,
        atR Q 2] R) (closK C [mulE P 1 3, mulE P 2 4, atR Q 2] R)
          (prodM C (cenS P C (cenE P C Sm (mulE P 2 4)) [mulE P 1 3, 2, 4, 5]) (closK C [5] R))
          (closK C [mulE P 1 4, mulE P 2 3, atR Q 2] R)
          (closK C [mulE P 1 4, mulE P (mulE P 1 2) 3, atR Q 2] R) (Nat.shiftRight w 16)) =
        (Y₀ : Set Γ) → ent k = conjSub (elt (fld(w, 9, 127))) Y₀ := by
      intro Y₀ hY₀
      apply SetLike.coe_injective
      rw [hconj, ← hY₀, ← hk', (hentR k hk).eq_mset]
    rcases f14fg_ys14 (closK C [mulE P 2 4, mulE P (mulE P 1 2) 3, atR Q 2] R)
        (closK C [mulE P 1 3, mulE P 2 4, atR Q 2] R)
        (prodM C (cenS P C (cenE P C Sm (mulE P 2 4)) [mulE P 1 3, 2, 4, 5]) (closK C [5] R))
        (closK C [mulE P 1 4, mulE P 2 3, atR Q 2] R)
        (closK C [mulE P 1 4, mulE P (mulE P 1 2) 3, atR Q 2] R) (Nat.shiftRight w 16) with
      e | e | e | e | e
    · exact ⟨fr.E, by simp, fin _ (by rw [e, hY0]; rfl)⟩
    · exact ⟨fr.F, by simp, fin _ (by rw [e, hY1]; rfl)⟩
    · exact ⟨cen fr.B ⊔ closure {fr.h₀}, by simp, fin _ (by rw [e, hY2])⟩
    · exact ⟨closure {fr.a₁ * fr.b₂, fr.b₁ * fr.a₂, fr.z}, by simp, fin _ (by rw [e, hY3])⟩
    · exact ⟨closure {fr.a₁ * fr.b₂, fr.a₁ * fr.b₁ * fr.a₂, fr.z}, by simp,
        fin _ (by rw [e, hY4])⟩

end Frame

theorem fact14_67_of_twin {Γ : Type} [Group Γ] [Finite Γ] {fr : Frame Γ} {elt : ℕ → Γ}
    {P C V Q L OR RG N R : ℕ} {ws : List ℕ}
    (hR : RealT elt P C V Q) (hg : ∀ s < 5, elt (s + 1) = sGen fr s)
    (hlat : (∀ k < N, ∃ K : Subgroup Γ, K ≤ fr.Sσ ∧ RepM elt (latM L k) (K : Set Γ)) ∧
      ∀ K ≤ fr.Sσ, ∃ k < N, RepM elt (latM L k) (K : Set Γ))
    (hdist : ∀ k < N, ∀ k' < N, latM L k = latM L k' → k = k') (hN : N ≤ 448)
    (ho : ordK L OR 0 N = true) (hrg : rgK L RG N = true)
    (hall : ∀ k < N, ∃ lo w, lo ≤ k ∧ k < lo + w ∧ w ≤ 448 ∧ rgAllK L OR RG N lo w = true)
    (hf : f14fK P C V Q L N 1 2 3 4 5 R ws = true) (hgk : f14gK P C V Q L N 1 2 3 4 5 R = true) :
    ((maxElemAbelian fr.S).ncard = 8 ∧
      ∀ Y ∈ maxElemAbelian fr.S, ∃ s ∈ fr.S, ∃ Y₀ ∈ ({fr.E, fr.F, cen fr.B ⊔ closure {fr.h₀},
        closure {fr.a₁ * fr.b₂, fr.b₁ * fr.a₂, fr.z}, closure {fr.a₁ * fr.b₂, fr.a₁ * fr.b₁ * fr.a₂,
          fr.z}} : Set (Subgroup Γ)), Y = conjSub s Y₀) ∧
    (CFSG.Open.pRank 2 fr.S = 3 ∧ GH74.sectionalTwoRank ↥fr.S = 4) :=
  ⟨f14fg_six hR hg hlat hdist hN hf, f14fg_seven hR hg hlat hN ho hrg hall hgk⟩

end CFSG.KC.G2Three.Sec1T3
