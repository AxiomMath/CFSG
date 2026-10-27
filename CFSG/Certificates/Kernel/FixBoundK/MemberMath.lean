module

public import CFSG.Certificates.Kernel.FixBoundK.FixSpan
public import CFSG.Certificates.Kernel.FixBoundK.MemberSound
public import CFSG.Monster.VisQuot.MonoFlag
public import CFSG.Certificates.Kernel.FixBoundK.FamSound
public import CFSG.Sporadic.Schreier.J4SSylowBase

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.KC.FixBoundK

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Lifts CFSG.Monster.VisQuot
  CFSG.Quasithin.H.Mathieu

theorem spanChk_iff (B : List Nat) : ∀ (F : List Nat) (j₀ : Nat), spanChk B F j₀ = true ↔
    j₀ + F.length = 2 ^ B.length ∧ ∀ j < F.length, F.getD j 0 = actS B (j₀ + j)
  | [], j₀ => by
    change Nat.beq j₀ (2 ^ lenS B) = true ↔ _
    rw [beqT, TrivSound.lenS_eq]
    simp
  | f :: F, j₀ => by
    change Bool.rec (motive := fun _ => Bool) false (spanChk B F (Nat.succ j₀))
      (Nat.beq f (actS B j₀)) = true ↔ _
    rw [TrivSound.bAnd_eq, Bool.and_eq_true, beqT, spanChk_iff B F]
    constructor
    · rintro ⟨h0, h1, h2⟩
      refine ⟨by simp only [List.length_cons]; omega, fun j hj => ?_⟩
      cases j with
      | zero => simpa using h0
      | succ j =>
        rw [List.getD_cons_succ, h2 j (by simpa using hj)]
        congr 1
        omega
    · rintro ⟨h1, h2⟩
      refine ⟨by simpa using h2 0 (by simp), by simp only [List.length_cons] at h1; omega,
        fun j hj => ?_⟩
      have := h2 (j + 1) (by simpa using hj)
      rw [List.getD_cons_succ] at this
      rw [this]
      congr 1
      omega

theorem popS_eq : ∀ (l : List Nat) (A : Nat),
    popS l A = ∑ j ∈ Finset.range l.length, (A.testBit j).toNat
  | [], _ => rfl
  | _ :: l, A => by
    change Bool.rec (motive := fun _ => Nat) (Nat.add (Nat.land A 1) (popS l (Nat.shiftRight A 1)))
      0 (Nat.beq A 0) = _
    rw [List.length_cons, Finset.sum_range_succ']
    cases hA : Nat.beq A 0
    · change Nat.land A 1 + popS l (Nat.shiftRight A 1) = _
      rw [popS_eq l, shiftRight_one, add_comm]
      congr 1
      · refine Finset.sum_congr rfl fun j _ => ?_
        rw [Nat.testBit_succ]
      · change A &&& 1 = _
        rw [Nat.and_one_is_mod, Nat.toNat_testBit, Nat.pow_zero, Nat.div_one]
    · have h0 : A = 0 := Nat.eq_of_beq_eq_true hA
      subst h0
      simp

theorem zS_testBit (k : Nat) : ∀ (bs : List Nat) (A acc : Nat), (zS bs A acc).testBit k = true ↔
    acc.testBit k = true ∧ ∀ j < bs.length, A.testBit j = true → (bs.getD j 0).testBit k = true
  | [], A, acc => by
    change acc.testBit k = true ↔ _
    simp
  | b :: bs, A, acc => by
    change (Bool.rec (motive := fun _ => Nat)
      (zS bs (Nat.shiftRight A 1) (Bool.rec (motive := fun _ => Nat) acc (Nat.land acc b)
        (Nat.beq (Nat.land A 1) 1))) acc (Nat.beq A 0)).testBit k = true ↔ _
    cases hA : Nat.beq A 0
    · change (zS bs (Nat.shiftRight A 1) (Bool.rec (motive := fun _ => Nat) acc (Nat.land acc b)
        (Nat.beq (Nat.land A 1) 1))).testBit k = true ↔ _
      rw [zS_testBit k bs, TrivSound.nIf_beq, shiftRight_one]
      have h1 : Nat.land A 1 = A % 2 := Nat.and_one_is_mod A
      rw [h1]
      constructor
      · rintro ⟨h2, h3⟩
        by_cases ha : A % 2 = 1
        · rw [if_pos ha] at h2
          change (acc &&& b).testBit k = true at h2
          rw [Nat.testBit_and, Bool.and_eq_true] at h2
          refine ⟨h2.1, fun j hj hAj => ?_⟩
          cases j with
          | zero => simpa using h2.2
          | succ j =>
            rw [List.getD_cons_succ]
            exact h3 j (by simpa using hj) (by rwa [← Nat.testBit_succ])
        · rw [if_neg ha] at h2
          refine ⟨h2, fun j hj hAj => ?_⟩
          cases j with
          | zero =>
            rw [Nat.testBit_zero] at hAj
            exact absurd (of_decide_eq_true hAj) ha
          | succ j =>
            rw [List.getD_cons_succ]
            exact h3 j (by simpa using hj) (by rwa [← Nat.testBit_succ])
      · rintro ⟨h2, h3⟩
        refine ⟨?_, fun j hj hAj => ?_⟩
        · by_cases ha : A % 2 = 1
          · rw [if_pos ha]
            change (acc &&& b).testBit k = true
            rw [Nat.testBit_and, Bool.and_eq_true]
            refine ⟨h2, ?_⟩
            have := h3 0 (by simp) (by rw [Nat.testBit_zero]; exact decide_eq_true ha)
            simpa using this
          · rw [if_neg ha]
            exact h2
        · have := h3 (j + 1) (by simpa using hj) (by rwa [Nat.testBit_succ])
          rwa [List.getD_cons_succ] at this
    · have h0 : A = 0 := Nat.eq_of_beq_eq_true hA
      subst h0
      change acc.testBit k = true ↔ _
      simp

theorem mem_selS {x : Nat} : ∀ {l : List Nat} {s : Nat}, x ∈ selS l s →
    ∃ j < l.length, s.testBit j = true ∧ x = l.getD j 0
  | [], _, h => absurd h List.not_mem_nil
  | y :: l, s, h => by
    change x ∈ Bool.rec (motive := fun _ => List Nat)
      (Bool.rec (motive := fun _ => List Nat) (selS l (Nat.shiftRight s 1))
        (y :: selS l (Nat.shiftRight s 1)) (Nat.beq (Nat.land s 1) 1)) [] (Nat.beq s 0) at h
    cases hs : Nat.beq s 0
    · rw [hs] at h
      have hrest : x ∈ selS l (Nat.shiftRight s 1) → ∃ j < (y :: l).length,
          s.testBit j = true ∧ x = (y :: l).getD j 0 := fun hx => by
        obtain ⟨j, hj, hsj, rfl⟩ := mem_selS hx
        refine ⟨j + 1, by simpa using hj, ?_, by rw [List.getD_cons_succ]⟩
        rw [Nat.testBit_succ, ← shiftRight_one]
        exact hsj
      cases hb : Nat.beq (Nat.land s 1) 1
      · rw [hb] at h
        exact hrest h
      · rw [hb] at h
        rcases List.mem_cons.1 h with rfl | hx
        · refine ⟨0, by simp, ?_, by simp⟩
          have h1 : Nat.land s 1 = 1 := Nat.eq_of_beq_eq_true hb
          rw [Nat.testBit_zero]
          change s &&& 1 = 1 at h1
          rw [Nat.and_one_is_mod] at h1
          exact decide_eq_true h1
        · exact hrest hx
    · rw [hs] at h
      exact absurd h List.not_mem_nil

theorem testBit_foldl_and (bs : Nat → Nat) (k : Nat) : ∀ (l : List Nat) (acc : Nat),
    (l.foldl (fun acc j => acc &&& bs j) acc).testBit k = true ↔
      acc.testBit k = true ∧ ∀ j ∈ l, (bs j).testBit k = true
  | [], acc => by simp
  | j :: l, acc => by
    rw [List.foldl_cons, testBit_foldl_and bs k l, Nat.testBit_and, Bool.and_eq_true,
      List.forall_mem_cons, and_assoc]

@[expose] def maskR (p : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => maskR p n ||| (if p n then 2 ^ n else 0)

theorem testBit_maskR (p : Nat → Bool) (k : Nat) : ∀ n,
    (maskR p n).testBit k = (decide (k < n) && p k)
  | 0 => by simp [maskR]
  | n + 1 => by
    rw [maskR, Nat.testBit_or, testBit_maskR p k n]
    by_cases hk : k = n
    · subst hk
      cases hp : p k <;> simp [hp]
    · have h1 : (if p n = true then 2 ^ n else 0 : Nat).testBit k = false := by
        split_ifs
        · rw [Nat.testBit_two_pow]
          exact decide_eq_false (Ne.symm hk)
        · exact Nat.zero_testBit k
      rw [h1, Bool.or_false]
      by_cases hkn : k < n
      · simp [hkn, Nat.lt_succ_of_lt hkn]
      · have : ¬ k < n + 1 := by omega
        simp [hkn, this]

theorem compat_pair (P : Subgroup AutPerm) {X : Submodule (ZMod 2) C} (hXF : X ≤ fixModΩ P) :
    X ≤ compatC (compatC X ⊓ fixModΩ P) ⊓ fixModΩ P ∧
      compatC (compatC (compatC X ⊓ fixModΩ P) ⊓ fixModΩ P) ⊓ fixModΩ P =
        compatC X ⊓ fixModΩ P := by
  have hX : X ≤ compatC (compatC X ⊓ fixModΩ P) ⊓ fixModΩ P := by
    intro x hx
    refine Submodule.mem_inf.2 ⟨mem_compatC.2 fun z hz => ?_, hXF hx⟩
    have hzx := mem_compatC.1 (Submodule.mem_inf.1 hz).1 x hx
    rwa [mul_comm] at hzx
  refine ⟨hX, le_antisymm ?_ ?_⟩
  · exact le_inf (le_trans inf_le_left (compatC_anti hX)) inf_le_right
  · intro z hz
    refine Submodule.mem_inf.2 ⟨mem_compatC.2 fun a ha => ?_, (Submodule.mem_inf.1 hz).2⟩
    have haz := mem_compatC.1 (Submodule.mem_inf.1 ha).1 z hz
    rwa [mul_comm] at haz

theorem natCard_sub (V : Submodule (ZMod 2) C) : Nat.card V = 2 ^ Module.finrank (ZMod 2) V := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V), Nat.card_zmod]

theorem fixBoundAt_of_members {gens : List (List Nat)} {B gs ys : List Nat}
    {yfT : List (List Nat)} {r : Nat} {F bs Mws : List Nat} {L : List Nat}
    (hgen : ∀ g ∈ gens, ∃ σ : AutPerm, ImgL (σ : Equiv.Perm (Fin 24)) g)
    (hlen : B.length + ys.length = 12) (hsyn : ∀ y ∈ appS B ys, synS y = 0)
    (hfix : ∀ g ∈ gens, ∀ b ∈ B, fixS g b = true) (hd : dualS B gs 0 = true)
    (hpar : ∀ l ∈ yfT, ∀ f ∈ l, par24 f = 0) (hys : ysChk gens yfT ys 0 = true)
    (hspan : spanChk B F 0 = true) (hmws : mwsRem gens Mws = [])
    (hbl : bs.length = F.length)
    (hbit : ∀ j < F.length, ∀ k, (bs.getD j 0).testBit k = true ↔
      k < F.length ∧ bvec 24 (F.getD k 0) * bvec 24 (F.getD j 0) ∈ C)
    (hcl : ∀ u < L.length, ∀ j < F.length, ∃ v < L.length, L.getD v 0 = L.getD u 0 &&& bs.getD j 0)
    (hfull : 2 ^ F.length - 1 ∈ L)
    (hmem : ∀ A ∈ L, ∃ sF fs, memberK r F bs Mws (2 ^ F.length - 1) A sF fs = true)
    (hr : Nat.card (Subgroup.closure (GenSet gens)) ≤ 2 ^ r) :
    FixBoundAt (Subgroup.closure (GenSet gens)) := by
  classical
  set P := Subgroup.closure (GenSet gens) with hPdef
  set m := F.length with hm
  obtain ⟨hFlen, hFeq⟩ := (spanChk_iff B F 0).1 hspan
  rw [Nat.zero_add] at hFlen
  have hFj : ∀ j < m, F.getD j 0 = actS B j := fun j hj => by rw [hFeq j hj, Nat.zero_add]
  have hB : ∀ b ∈ B, synS b = 0 := fun b hb => hsyn b (mem_appS.2 (Or.inl hb))
  have hFC : ∀ j < m, bvec 24 (F.getD j 0) ∈ C := fun j hj => by
    rw [hFj j hj]
    exact (actS_mem_fixModΩ hB hfix j).fst
  have hFP : ∀ (j) (hj : j < m), (⟨bvec 24 (F.getD j 0), hFC j hj⟩ : C) ∈ fixModΩ P := by
    intro j hj
    have h := (actS_mem_fixModΩ hB hfix j).snd
    have e : (⟨bvec 24 (F.getD j 0), hFC j hj⟩ : C) =
        ⟨bvec 24 (actS B j), (actS_mem_fixModΩ hB hfix j).fst⟩ :=
      Subtype.ext (congrArg (bvec 24) (hFj j hj))
    rw [e]
    exact h
  have hcov : ∀ c ∈ fixModΩ P, ∃ j < m, bvec 24 (F.getD j 0) = (c : Fin 24 → ZMod 2) := by
    intro c hc
    obtain ⟨j, hj, e⟩ := fixModΩ_cover hgen hlen hsyn hfix hd hpar hys hc
    refine ⟨j, by rw [hm, ← hFlen] at *; omega, ?_⟩
    rw [hFj j (by rw [hm, hFlen]; exact hj), e]
  have hinj : ∀ j < m, ∀ k < m, bvec 24 (F.getD j 0) = bvec 24 (F.getD k 0) → j = k := by
    intro j hj k hk h
    rw [hFj j hj, hFj k hk] at h
    exact actS_bvec_inj hd (by rw [← hFlen]; exact hj) (by rw [← hFlen]; exact hk) h
  let memY : Submodule (ZMod 2) C → Nat → Prop := fun Y j =>
    ∃ h : bvec 24 (F.getD j 0) ∈ C, (⟨bvec 24 (F.getD j 0), h⟩ : C) ∈ Y
  have hmemY : ∀ (Y : Submodule (ZMod 2) C) (j) (hj : j < m),
      memY Y j ↔ (⟨bvec 24 (F.getD j 0), hFC j hj⟩ : C) ∈ Y :=
    fun Y j hj => ⟨fun ⟨_, h⟩ => h, fun h => ⟨hFC j hj, h⟩⟩
  have hcard : ∀ Y : Submodule (ZMod 2) C, Y ≤ fixModΩ P →
      ∑ j ∈ Finset.range m, (decide (memY Y j)).toNat = Nat.card Y := by
    intro Y hY
    have e1 : ∑ j ∈ Finset.range m, (decide (memY Y j)).toNat =
        ((Finset.range m).filter (memY Y)).card := by
      rw [Finset.card_filter]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases h : memY Y j
      · rw [if_pos h, decide_eq_true h]
        rfl
      · rw [if_neg h, decide_eq_false h]
        rfl
    rw [e1, ← Nat.card_eq_finsetCard]
    have hf : ∀ x : ((Finset.range m).filter (memY Y)), (x : Nat) < m := fun x =>
      Finset.mem_range.1 (Finset.mem_filter.1 x.2).1
    let f : ((Finset.range m).filter (memY Y)) → Y := fun x =>
      ⟨⟨bvec 24 (F.getD x 0), hFC x (hf x)⟩,
        (hmemY Y x (hf x)).1 (Finset.mem_filter.1 x.2).2⟩
    refine Nat.card_congr (Equiv.ofBijective f ⟨fun a b hab => ?_, fun y => ?_⟩)
    · have h := congrArg (fun z : Y => ((z : C) : Fin 24 → ZMod 2)) hab
      exact Subtype.ext (hinj a (hf a) b (hf b) h)
    · obtain ⟨j, hj, e⟩ := hcov y (hY y.2)
      have hjY : memY Y j := ⟨hFC j hj, by
        have e' : (⟨bvec 24 (F.getD j 0), hFC j hj⟩ : C) = y := Subtype.ext e
        rw [e']
        exact y.2⟩
      refine ⟨⟨j, Finset.mem_filter.2 ⟨Finset.mem_range.2 hj, hjY⟩⟩, ?_⟩
      exact Subtype.ext (Subtype.ext e)
  have hcompat : ∀ (Y : Submodule (ZMod 2) C), Y ≤ fixModΩ P → ∀ k < m,
      (memY (compatC Y ⊓ fixModΩ P) k ↔
        ∀ j < m, memY Y j → bvec 24 (F.getD k 0) * bvec 24 (F.getD j 0) ∈ C) := by
    intro Y hY k hk
    rw [hmemY _ k hk, Submodule.mem_inf, mem_compatC]
    constructor
    · intro hkc j hj hjY
      have hb : (⟨bvec 24 (F.getD j 0), hFC j hj⟩ : C) ∈ Y := (hmemY Y j hj).1 hjY
      have h1 := hkc.1 _ hb
      exact h1
    · intro h
      refine ⟨fun y hy => ?_, hFP k hk⟩
      obtain ⟨j, hj, e⟩ := hcov y (hY hy)
      have hjY : memY Y j := ⟨hFC j hj, by
        have e' : (⟨bvec 24 (F.getD j 0), hFC j hj⟩ : C) = y := Subtype.ext e
        rw [e']
        exact hy⟩
      have := h j hj hjY
      rwa [e] at this
  intro X _ hXF
  set Z : Submodule (ZMod 2) C := compatC X ⊓ fixModΩ P with hZ
  set A' : Submodule (ZMod 2) C := compatC Z ⊓ fixModΩ P with hA'
  obtain ⟨hXA, hZeq⟩ := compat_pair P hXF
  have hZF : Z ≤ fixModΩ P := inf_le_right
  have hAF : A' ≤ fixModΩ P := inf_le_right
  let pm : Submodule (ZMod 2) C → Nat := fun Y => maskR (fun j => decide (memY Y j)) m
  have hpm : ∀ Y k, (pm Y).testBit k = true ↔ k < m ∧ memY Y k := by
    intro Y k
    change (maskR _ m).testBit k = true ↔ _
    rw [testBit_maskR, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
  set full := 2 ^ m - 1 with hfulldef
  obtain ⟨u₀, hu₀, hfu⟩ : ∃ u₀ < L.length, L.getD u₀ 0 = full := by
    obtain ⟨u, hu, e⟩ := List.mem_iff_getElem.1 hfull
    exact ⟨u, hu, by rw [List.getD_eq_getElem _ _ hu, e]⟩
  let lZ := (List.range m).filter fun j => decide (memY Z j)
  have hlZ : ∀ j ∈ lZ, j < m := fun j hj => List.mem_range.1 (List.mem_filter.1 hj).1
  obtain ⟨v, hv, hve⟩ := foldl_mem (bs := fun j => bs.getD j 0) hcl lZ hlZ u₀ hu₀
  have hAmem : pm A' ∈ L := by
    have e : pm A' = L.getD v 0 := by
      rw [hve, hfu]
      apply Nat.eq_of_testBit_eq
      intro k
      apply Bool.eq_iff_iff.2
      rw [hpm, testBit_foldl_and, hfulldef, Nat.testBit_two_pow_sub_one, decide_eq_true_eq]
      constructor
      · rintro ⟨hk, hkA⟩
        refine ⟨hk, fun j hj => ?_⟩
        obtain ⟨hjr, hjZ⟩ := List.mem_filter.1 hj
        have hjm := List.mem_range.1 hjr
        exact (hbit j hjm k).2 ⟨hk, (hcompat Z hZF k hk).1 hkA j hjm (of_decide_eq_true hjZ)⟩
      · rintro ⟨hk, hall⟩
        refine ⟨hk, (hcompat Z hZF k hk).2 fun j hj hjZ => ?_⟩
        exact ((hbit j hj k).1 (hall j (List.mem_filter.2 ⟨List.mem_range.2 hj,
          decide_eq_true hjZ⟩))).2
    rw [e, List.getD_eq_getElem _ _ hv]
    exact List.getElem_mem hv
  obtain ⟨sF, fs, hK⟩ := hmem _ hAmem
  obtain ⟨-, hsF, hdual, hineq⟩ := memberK_spec hK
  have hzS : ∀ k, (zS bs (pm A') full).testBit k = true ↔ k < m ∧ memY Z k := by
    intro k
    rw [zS_testBit, hfulldef, Nat.testBit_two_pow_sub_one, decide_eq_true_eq]
    constructor
    · rintro ⟨hk, hall⟩
      refine ⟨hk, ?_⟩
      have h := (hcompat A' hAF k hk).2 fun j hj hjA =>
        ((hbit j hj k).1 (hall j (by rw [hbl]; exact hj) ((hpm A' j).2 ⟨hj, hjA⟩))).2
      rwa [hZeq] at h
    · rintro ⟨hk, hkZ⟩
      refine ⟨hk, fun j hj hjA => ?_⟩
      rw [hbl] at hj
      have hkZ' : memY (compatC A' ⊓ fixModΩ P) k := by rwa [hZeq]
      exact (hbit j hj k).2 ⟨hk, (hcompat A' hAF k hk).1 hkZ' j hj ((hpm A' j).1 hjA).2⟩
  have hpopA : popS F (pm A') = Nat.card A' := by
    rw [popS_eq, ← hcard A' hAF]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := Finset.mem_range.1 hj
    congr 1
    apply Bool.eq_iff_iff.2
    rw [hpm, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨hj', h⟩⟩
  have hpopZ : popS F (zS bs (pm A') full) = Nat.card Z := by
    rw [popS_eq, ← hcard Z hZF]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := Finset.mem_range.1 hj
    congr 1
    apply Bool.eq_iff_iff.2
    rw [hzS, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨hj', h⟩⟩
  set V : Submodule (ZMod 2) C := commΩ P ⊔ A' ⊔ Z with hV
  have hgenP : ∀ g ∈ gens, ∃ σ ∈ P, ImgL (σ : Equiv.Perm (Fin 24)) g := fun g hg => by
    obtain ⟨σ, hσ⟩ := hgen g hg
    exact ⟨σ, Subgroup.subset_closure ⟨g, hg, hσ⟩, hσ⟩
  have hws : ∀ w ∈ appS Mws (selS F sF), ∃ hw : bvec 24 w ∈ C, (⟨bvec 24 w, hw⟩ : C) ∈ V := by
    intro w hw
    rcases mem_appS.1 hw with hM | hS
    · obtain ⟨hC, hMP⟩ := mws_mem_commΩ hgenP hmws w hM
      exact ⟨hC, Submodule.mem_sup_left (Submodule.mem_sup_left hMP)⟩
    · obtain ⟨j, hj, hsj, rfl⟩ := mem_selS hS
      refine ⟨hFC j hj, ?_⟩
      have hbitj : (sF &&& (pm A' ||| zS bs (pm A') full)).testBit j = true := by rw [hsF]; exact hsj
      rw [Nat.testBit_and, Nat.testBit_or, Bool.and_eq_true, Bool.or_eq_true] at hbitj
      rcases hbitj.2 with hA | hZb
      · exact Submodule.mem_sup_left (Submodule.mem_sup_right
          ((hmemY A' j hj).1 ((hpm A' j).1 hA).2))
      · exact Submodule.mem_sup_right ((hmemY Z j hj).1 ((hzS j).1 hZb).2)
  have hrank : lenS (appS Mws (selS F sF)) ≤ Module.finrank (ZMod 2) V := by
    rw [TrivSound.lenS_eq]
    exact length_le_finrank_of_dualS hdual (fun w hw => (hws w hw).fst)
      (fun w hw => (hws w hw).snd)
  have h7 : Nat.card A' * Nat.card P * 2 ^ 11 * Nat.card Z ≤ 2 ^ 14 * Nat.card V := by
    calc Nat.card A' * Nat.card P * 2 ^ 11 * Nat.card Z
        ≤ popS F (pm A') * 2 ^ r * 2048 * popS F (zS bs (pm A') full) := by
          rw [hpopA, hpopZ]
          exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul le_rfl hr) le_rfl) le_rfl
      _ ≤ 16384 * 2 ^ lenS (appS Mws (selS F sF)) := hineq
      _ ≤ 2 ^ 14 * Nat.card V := by
          rw [natCard_sub]
          exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hrank)
  set W : Submodule (ZMod 2) C := commΩ P ⊔ Z with hW
  have hVW : V = W ⊔ A' := sup_right_comm (commΩ P) A' Z
  have hmono := finrank_add_finrank_sup_le (X := X) (Y := A') hXA W
  have hcardmono : Nat.card X * Nat.card ↥(W ⊔ A') ≤ Nat.card A' * Nat.card ↥(W ⊔ X) := by
    rw [natCard_sub X, natCard_sub (W ⊔ A'), natCard_sub A', natCard_sub (W ⊔ X), ← pow_add,
      ← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) hmono
  have hmain : Nat.card A' * (Nat.card X * Nat.card P * 2 ^ 11 * Nat.card Z) ≤
      Nat.card A' * (2 ^ 14 * Nat.card ↥(W ⊔ X)) := by
    rw [hVW] at h7
    calc Nat.card A' * (Nat.card X * Nat.card P * 2 ^ 11 * Nat.card Z)
        = Nat.card X * (Nat.card A' * Nat.card P * 2 ^ 11 * Nat.card Z) := by ring
      _ ≤ Nat.card X * (2 ^ 14 * Nat.card ↥(W ⊔ A')) := Nat.mul_le_mul_left _ h7
      _ = 2 ^ 14 * (Nat.card X * Nat.card ↥(W ⊔ A')) := by ring
      _ ≤ 2 ^ 14 * (Nat.card A' * Nat.card ↥(W ⊔ X)) := Nat.mul_le_mul_left _ hcardmono
      _ = Nat.card A' * (2 ^ 14 * Nat.card ↥(W ⊔ X)) := by ring
  have hcancel := Nat.le_of_mul_le_mul_left hmain Nat.card_pos
  have hVX : (commΩ P ⊔ X ⊔ Z : Submodule (ZMod 2) C) = W ⊔ X := sup_right_comm (commΩ P) X Z
  rw [hVX]
  exact hcancel

end CFSG.KC.FixBoundK

end
