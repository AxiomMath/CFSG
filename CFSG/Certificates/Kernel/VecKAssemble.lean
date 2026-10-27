module

public import CFSG.Certificates.Kernel.VecKRegs
public import CFSG.Certificates.Kernel.VecKTrees
public import CFSG.Sporadic.HS.Chain
public import CFSG.Perm.SiftComplete

public section

namespace CFSG.KC.VecK

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.M1F2 CFSG.KC.Co1F2 CFSG.Sporadic.SmallF2.Native
  CFSG.Sporadic.Th.Native CFSG.Perm.Native CFSG.Sporadic.Th CFSG.Perm

private theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

private theorem andB_eq (a b : Bool) : andB a b = (a && b) := by
  cases a <;> rfl

private theorem allN_iff {n : Nat} {f : Nat → Bool} : allN n f = true ↔ ∀ i < n, f i = true := by
  induction n with
  | zero => exact ⟨fun _ i hi => absurd hi (Nat.not_lt_zero i), fun _ => rfl⟩
  | succ n ih =>
    change andB (f n) (allN n f) = true ↔ _
    rw [andB_eq, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | h
      · exact h2 i h
      · subst h
        exact h1
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun i hi => h i (by omega)⟩

private theorem getL_eq (x : Nat) : ∀ (L : List Nat) (i : Nat), getL x L i = L[i]?.getD x
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: L, i + 1 => by
    change getL x L i = _
    rw [getL_eq x L i]
    rfl

private theorem getL_array (A : Array Nat) {i : Nat} (hi : i < A.size) : getL 0 A.toList i = A[i]! := by
  rw [getL_eq, List.getElem?_eq_getElem (by simpa using hi), Option.getD_some, Array.getElem_toList,
    getElem!_pos A i hi]

private theorem parAll_of {n chunks : Nat} {p : Nat → Bool} (h : ∀ i < n, p i = true) :
    parAll n chunks p = true := by
  unfold parAll
  rw [List.all_eq_true]
  intro t ht
  simp only [List.mem_map, List.mem_range] at ht
  obtain ⟨j, -, rfl⟩ := ht
  change allStep j (chunks + 1) n p = true
  unfold allStep
  rw [Nat.all_eq_finRange_all, List.all_eq_true]
  intro ⟨k, hk⟩ _
  apply h
  have h1 : (k + 1) * (chunks + 1) ≤ n + (chunks + 1) - 1 - j :=
    (Nat.le_div_iff_mul_le (by omega)).1 hk
  rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm] at h1
  generalize (chunks + 1) * k = t at h1 ⊢
  omega

private theorem prod_map_list {f : Tree → Nat} :
    ∀ l : List Tree, (l.map f).prod = ∏ i ∈ Finset.range l.length, f l[i]!
  | [] => by simp
  | a :: l => by
    rw [List.map_cons, List.prod_cons, prod_map_list l, List.length_cons, Finset.prod_range_succ']
    simp only [List.getElem!_cons_succ, List.getElem!_cons_zero]
    rw [mul_comm]

theorem prod_orbitSizes (trees : Array Tree) :
    (orbitSizes trees).prod = ∏ i ∈ Finset.range trees.size, trees[i]!.pts.size := by
  unfold orbitSizes
  rw [prod_map_list, Array.length_toList]
  refine Finset.prod_congr rfl fun i hi => ?_
  have hi' : i < trees.size := Finset.mem_range.1 hi
  rw [getElem!_pos trees.toList i (by simpa using hi'), getElem!_pos trees i hi', Array.getElem_toList]

theorem chain_arith {m N : Nat} {f s o : Nat → Nat} (ho : ∀ i < m, 0 < o i)
    (hfs : ∀ i < m, f i = o i * s i) (hsf : ∀ i < m, f (i + 1) ≤ s i) (hm : 1 ≤ f m)
    (h0 : f 0 ≤ N) (hN : N ≤ ∏ i ∈ Finset.range m, o i) :
    N ≤ f 0 ∧ f m ≤ 1 ∧ ∀ i < m, s i ≤ f (i + 1) := by
  have hL : ∀ d j, m - j = d → j ≤ m → (∏ l ∈ Finset.Ico j m, o l) * f m ≤ f j := by
    intro d
    induction d with
    | zero =>
      intro j hd hj
      obtain rfl : j = m := by omega
      simp
    | succ d ih =>
      intro j hd hj
      have hjm : j < m := by omega
      rw [Finset.prod_eq_prod_Ico_succ_bot hjm, mul_assoc, hfs j hjm]
      exact Nat.mul_le_mul_left _ ((ih (j + 1) (by omega) hjm).trans (hsf j hjm))
  have hU : ∀ i ≤ m, (∏ l ∈ Finset.range i, o l) * f i ≤ f 0 := by
    intro i
    induction i with
    | zero => intro _; simp
    | succ i ih =>
      intro hi
      have him : i < m := by omega
      rw [Finset.prod_range_succ, mul_assoc]
      calc (∏ l ∈ Finset.range i, o l) * (o i * f (i + 1))
          ≤ (∏ l ∈ Finset.range i, o l) * (o i * s i) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (hsf i him))
        _ = (∏ l ∈ Finset.range i, o l) * f i := by rw [hfs i him]
        _ ≤ f 0 := ih (by omega)
  have hpos : ∀ i ≤ m, 0 < ∏ l ∈ Finset.range i, o l := fun i hi =>
    Finset.prod_pos fun l hl => ho l (by have := Finset.mem_range.1 hl; omega)
  have hP0 : (∏ l ∈ Finset.range m, o l) * f m ≤ f 0 := by
    have := hL (m - 0) 0 rfl (Nat.zero_le _)
    rwa [← Finset.range_eq_Ico] at this
  refine ⟨?_, ?_, fun i hi => ?_⟩
  · calc N ≤ ∏ l ∈ Finset.range m, o l := hN
      _ ≤ (∏ l ∈ Finset.range m, o l) * f m := Nat.le_mul_of_pos_right _ hm
      _ ≤ f 0 := hP0
  · have h1 : (∏ l ∈ Finset.range m, o l) * f m ≤ (∏ l ∈ Finset.range m, o l) * 1 := by
      rw [mul_one]
      exact hP0.trans (h0.trans hN)
    exact Nat.le_of_mul_le_mul_left h1 (hpos m le_rfl)
  · have hsplit := Finset.prod_range_mul_prod_Ico o (Nat.le_of_lt hi)
    rw [Finset.prod_eq_prod_Ico_succ_bot hi] at hsplit
    have hc : (∏ l ∈ Finset.range i, o l) * o i * s i ≤
        (∏ l ∈ Finset.range i, o l) * o i * f (i + 1) := by
      calc (∏ l ∈ Finset.range i, o l) * o i * s i = (∏ l ∈ Finset.range i, o l) * f i := by
            rw [hfs i hi, mul_assoc]
        _ ≤ f 0 := hU i hi.le
        _ ≤ ∏ l ∈ Finset.range m, o l := h0.trans hN
        _ = (∏ l ∈ Finset.range i, o l) * o i * ∏ l ∈ Finset.Ico (i + 1) m, o l := by
            rw [← hsplit, mul_assoc]
        _ ≤ (∏ l ∈ Finset.range i, o l) * o i * ((∏ l ∈ Finset.Ico (i + 1) m, o l) * f m) :=
            Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ hm)
        _ ≤ (∏ l ∈ Finset.range i, o l) * o i * f (i + 1) :=
            Nat.mul_le_mul_left _ (hL _ (i + 1) rfl hi)
    exact Nat.le_of_mul_le_mul_left hc (Nat.mul_pos (hpos i hi.le) (ho i hi))

section Chain

variable {G : Type*} [Group G] [Finite G] {n : Nat} [MulAction G (Fin n)]

theorem levels_of_card {letters : Array Table} {base : Array Nat} {trees : Array Tree}
    {lG : Nat → G} (hrep : ∀ l < letters.size, Rep n letters[l]! (lG l))
    (hTF : ∀ i < base.size, CFSG.Perm.TreeFacts n trees[i]! (levelLetters letters base i) lG base[i]!)
    (hcard : Nat.card G ≤ ∏ i ∈ Finset.range base.size, trees[i]!.pts.size) :
    levelGroup letters base lG 0 = ⊤ ∧ levelGroup letters base lG base.size = ⊥ ∧
      ∀ i < base.size, ∀ g ∈ levelGroup letters base lG i, idx n g base[i]! = base[i]! →
        g ∈ levelGroup letters base lG (i + 1) := by
  classical
  have hfixb : ∀ i < base.size, ∀ g ∈ levelGroup letters base lG (i + 1),
      idx n g base[i]! = base[i]! := by
    intro i hi g hg
    unfold levelGroup lettersGroup at hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨l, hl, rfl⟩ := hx
      obtain ⟨hl', hfix⟩ := mem_levelLetters_succ.1 hl
      rw [← hrep l (levelLetters_lt hl') _ (hTF i hi).r_lt, hfix]
    | one => exact idx_one _
    | mul x y _ _ hx hy => rw [idx_mul, hy, hx]
    | inv x _ hx => rw [← hx, idx_inv_idx, hx]
  have hle : ∀ i, levelGroup letters base lG (i + 1) ≤ levelGroup letters base lG i :=
    fun i => levelGroup_anti lG (Nat.le_succ i)
  have hstabK : ∀ i (hi : i < base.size),
      (levelGroup letters base lG (i + 1)).subgroupOf (levelGroup letters base lG i) ≤
        MulAction.stabilizer (levelGroup letters base lG i) (⟨base[i]!, (hTF i hi).r_lt⟩ : Fin n) := by
    intro i hi x hx
    rw [Subgroup.mem_subgroupOf] at hx
    rw [MulAction.mem_stabilizer_iff]
    apply Fin.ext
    rw [Subgroup.smul_def, smul_val_eq_idx]
    exact hfixb i hi x hx
  let s : Nat → Nat := fun i => if hi : i < base.size then
    Nat.card (MulAction.stabilizer (levelGroup letters base lG i) (⟨base[i]!, (hTF i hi).r_lt⟩ : Fin n))
    else 0
  have hs : ∀ i (hi : i < base.size), s i =
      Nat.card (MulAction.stabilizer (levelGroup letters base lG i) (⟨base[i]!, (hTF i hi).r_lt⟩ : Fin n)) :=
    fun i hi => dite_eq_left hi
  have hfs : ∀ i < base.size, Nat.card (levelGroup letters base lG i) = trees[i]!.pts.size * s i := by
    intro i hi
    have hc : Nat.card (MulAction.orbit (levelGroup letters base lG i)
        (⟨base[i]!, (hTF i hi).r_lt⟩ : Fin n)) = trees[i]!.pts.size := (hTF i hi).card_orbit
    have h1 := Subgroup.card_mul_index
      (MulAction.stabilizer (levelGroup letters base lG i) (⟨base[i]!, (hTF i hi).r_lt⟩ : Fin n))
    rw [MulAction.index_stabilizer, ← Nat.card_coe_set_eq, hc] at h1
    rw [hs i hi, ← h1, mul_comm]
  have hcardsub : ∀ i, Nat.card ((levelGroup letters base lG (i + 1)).subgroupOf
      (levelGroup letters base lG i)) = Nat.card (levelGroup letters base lG (i + 1)) :=
    fun i => Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hle i)).toEquiv
  have hsf : ∀ i < base.size, Nat.card (levelGroup letters base lG (i + 1)) ≤ s i := by
    intro i hi
    rw [hs i hi, ← hcardsub i]
    exact Subgroup.card_le_of_le (hstabK i hi)
  obtain ⟨hA, hB, hC⟩ := chain_arith (f := fun i => Nat.card (levelGroup letters base lG i))
    (fun i hi => (hTF i hi).size_pos) hfs hsf Nat.card_pos
    (Subgroup.card_le_card_group _) hcard
  refine ⟨Subgroup.eq_top_of_le_card _ hA, Subgroup.eq_bot_of_card_le _ hB, fun i hi g hg hfix => ?_⟩
  have heq := Subgroup.eq_of_le_of_card_ge (hstabK i hi) (by
    rw [hcardsub i, ← hs i hi]
    exact hC i hi)
  have hmem : (⟨g, hg⟩ : levelGroup letters base lG i) ∈
      MulAction.stabilizer (levelGroup letters base lG i) (⟨base[i]!, (hTF i hi).r_lt⟩ : Fin n) := by
    rw [MulAction.mem_stabilizer_iff]
    apply Fin.ext
    rw [Subgroup.smul_def, smul_val_eq_idx]
    exact hfix
  rw [← heq] at hmem
  exact Subgroup.mem_subgroupOf.1 hmem

theorem chain_sound {letters : Array Table} {base Q qb : Array Nat} {trees : Array Tree}
    {gs : Nat → G} (h2 : letters.size % 2 = 0)
    (hrepE : ∀ j < letters.size / 2, Rep n letters[2 * j]! (gs j))
    (hinv : ∀ j < letters.size / 2, invOK n letters[2 * j]! letters[2 * j + 1]! = true)
    (htrees : trees.size = base.size) (hqb : qb.size = base.size) (hQ : ∀ t < Q.size, Q[t]! < n)
    (hqbQ : ∀ i < base.size, qb[i]! < Q.size ∧ Q[qb[i]!]! = base[i]!)
    (hok : ∀ i < base.size,
      CFSG.Perm.Native.treeOK n base[i]! trees[i]! letters (levelLetters letters base i) = true)
    (hcard : Nat.card G ≤ ∏ i ∈ Finset.range base.size, trees[i]!.pts.size) :
    (∀ chunks, chainOK n letters base Q qb trees chunks = true) ∧
      ∀ (g : G) (img : Array Nat), img.size = Q.size → (∀ t < Q.size, img[t]! = idx n g Q[t]!) →
        sift trees letters qb Q 0 img = true := by
  have hrepAll := rep_pairG hrepE h2 hinv
  have hlvRep : ∀ i, ∀ l ∈ levelLetters letters base i, Rep n letters[l]! (CFSG.Perm.pairG gs l) :=
    fun i l hl => hrepAll l (levelLetters_lt hl)
  have hTF : ∀ i < base.size, CFSG.Perm.TreeFacts n trees[i]! (levelLetters letters base i) (CFSG.Perm.pairG gs) base[i]! :=
    fun i hi => treeOK_facts (hlvRep i) (hok i hi)
  have hWF : ∀ i < base.size, WalkFacts n trees[i]! letters (CFSG.Perm.pairG gs) := by
    intro i hi k hk hk0
    obtain ⟨hpar, hlab⟩ := (hTF i hi).par k hk hk0
    have hl := levelLetters_lt hlab
    refine ⟨hpar, hrepAll _ hl, ?_⟩
    rw [← CFSG.Perm.pairG_invL]
    exact hrepAll _ (invL_lt h2 hl)
  obtain ⟨htop, hbot, hstab⟩ := levels_of_card hrepAll hTF hcard
  have hsift : ∀ l ≤ trees.size, ∀ g ∈ levelGroup letters base (CFSG.Perm.pairG gs) l, ∀ img : Array Nat,
      img.size = Q.size → (∀ t < Q.size, img[t]! = idx n g Q[t]!) →
        sift trees letters qb Q l img = true := by
    intro l hl g hg img hsz himg
    refine sift_complete (lvs := levelLetters letters base) (levelGroup letters base (CFSG.Perm.pairG gs)) hQ
      (fun l' hl' => (hqbQ l' (htrees ▸ hl')).1)
      (fun l' hl' => hWF l' (htrees ▸ hl'))
      (fun l' hl' => by
        rw [(hqbQ l' (htrees ▸ hl')).2]
        exact hTF l' (htrees ▸ hl'))
      (fun _ _ => rfl)
      (fun l' hl' g' hg' hfix => by
        rw [(hqbQ l' (htrees ▸ hl')).2] at hfix
        exact hstab l' (htrees ▸ hl') g' hg' hfix)
      (by rw [htrees]; exact hbot)
      (trees.size - l) l rfl hl g hg img hsz himg
  refine ⟨fun chunks => ?_, fun g img hsz himg =>
    hsift 0 (Nat.zero_le _) g (by rw [htop]; trivial) img hsz himg⟩
  have hsch : ∀ i < base.size, ∀ l ∈ levelLetters letters base i, ∀ k < trees[i]!.pts.size,
      schreierAt trees letters qb Q i l k = true := by
    intro i hi l hl k hk
    have hTi := hTF i hi
    have hrl := hlvRep i l hl
    have hpk := hTi.pts_lt k hk
    obtain ⟨hky, hkq⟩ := hTi.closed k hk l hl
    unfold schreierAt
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    rw [hrl _ hpk]
    generalize hkyd : ap trees[i]!.pos (idx n (CFSG.Perm.pairG gs l) (ap trees[i]!.pts k)) = ky at hky hkq
    refine ⟨hky, ?_⟩
    obtain ⟨hs0, he0⟩ := walk_spec (lG := CFSG.Perm.pairG gs) (hWF i hi) hk Q hQ
    have hn0 : ∀ j < (walk trees[i]! letters k Q).size, (walk trees[i]! letters k Q)[j]! < n := by
      intro j hj
      rw [hs0] at hj
      rw [he0 j hj]
      exact idx_lt _ (hQ j hj)
    have hn1 : ∀ j < (apT letters[l]! (walk trees[i]! letters k Q)).size,
        (apT letters[l]! (walk trees[i]! letters k Q))[j]! < n := by
      intro j hj
      rw [apT_size] at hj
      rw [apT_get _ _ hj, hrl _ (hn0 j hj)]
      exact idx_lt _ (hn0 j hj)
    obtain ⟨hs2, he2⟩ := walkInv_spec (lG := CFSG.Perm.pairG gs) (hWF i hi) hky _ hn1
    have hmem : (treeG trees[i]! (CFSG.Perm.pairG gs) ky)⁻¹ * CFSG.Perm.pairG gs l * treeG trees[i]! (CFSG.Perm.pairG gs) k ∈
        levelGroup letters base (CFSG.Perm.pairG gs) i :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (hTi.treeG_mem hky)) (lG_mem hl))
        (hTi.treeG_mem hk)
    have hfix : idx n ((treeG trees[i]! (CFSG.Perm.pairG gs) ky)⁻¹ * CFSG.Perm.pairG gs l * treeG trees[i]! (CFSG.Perm.pairG gs) k)
        base[i]! = base[i]! := by
      rw [idx_mul, idx_mul, hTi.elt k hk, ← hkq, ← hTi.elt ky hky, idx_inv_idx]
    exact hsift (i + 1) (by rw [htrees]; omega) _ (hstab i hi _ hmem hfix) _
      (by rw [hs2, apT_size, hs0])
      (fun t ht => by
        rw [he2 t (by rwa [apT_size, hs0]), apT_get _ _ (by rwa [hs0]), hrl _ (hn0 t (by rwa [hs0])),
          he0 t ht, ← idx_mul, ← idx_mul])
  have hterm : ∀ l ∈ levelLetters letters base base.size, tupleEq (apT letters[l]! Q) Q = true := by
    intro l hl
    have h1 : CFSG.Perm.pairG gs l = 1 := by
      have := lG_mem (lG := CFSG.Perm.pairG gs) hl
      rw [← levelGroup, hbot] at this
      exact Subgroup.mem_bot.1 this
    rw [CFSG.KS.TW.tupleEq_iff, apT_size]
    refine ⟨rfl, fun t ht => ?_⟩
    rw [apT_get _ _ ht, hlvRep _ l hl _ (hQ t ht), h1, idx_one]
  simp only [chainOK, Bool.and_eq_true, beq_iff_eq, Array.all_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨h2, allIn_eq_true.2 fun j _ hj => hinv j hj⟩, htrees⟩, hqb⟩,
    allIn_eq_true.2 fun t _ ht => by simpa using hQ t ht⟩,
    allIn_eq_true.2 fun i _ hi => by simpa using hqbQ i hi⟩,
    allIn_eq_true.2 fun i _ hi => hok i hi⟩, allIn_eq_true.2 fun i _ hi => ?_⟩,
    fun j hj => hterm _ (Array.getElem_mem hj)⟩
  simp only [Array.all_eq_true]
  intro j hj
  exact parAll_of fun k hk => hsch i hi _ (Array.getElem_mem hj) k hk

end Chain

section Letters

open CFSG.Sporadic.SmallF2

variable {D : VecData} (hBF : BaseFacts D)
include hBF

private theorem n_lt32 : D.n < 2 ^ 32 := lt_trans hBF.n_lt (by norm_num)

private theorem rep_genT_of (z : Int) : Rep D.n (genT D.n (O D) z) (genG D z) := by
  unfold genT genG
  split_ifs
  · exact rep_a hBF
  · exact Rep.inv_of_invOK (rep_a hBF) hBF.invA
  · exact rep_b hBF
  · exact Rep.inv_of_invOK (rep_b hBF) hBF.invB

private theorem rep_regs0_of : ∀ r < (R0 D).size, Rep D.n (R0 D)[r]! (regsG D r) := by
  intro r hr
  rw [R0_size_eq] at hr
  rw [R0_get D hr]
  unfold regsG
  split_ifs
  · exact Rep.wordT (n_lt32 hBF) _ fun l _ => rep_genT_of hBF l
  · exact Rep.wordT (n_lt32 hBF) _ fun l _ => rep_genT_of hBF l
  · exact Rep.idT (n_lt32 hBF)

theorem rep_letters_of (hprog : ∀ ins ∈ D.prog, instrLt D.nregs ins = true)
    (hslp : (SLP D).2 = true) (hsel : ∀ j < D.sel.size, D.sel[j]! < D.nregs) :
    ∀ j < (L D).size / 2, Rep D.n (L D)[2 * j]! (gs D j) := by
  have hR := (runSLP_rep (n_lt32 hBF) D.prog (R0 D) (regsG D)
    (fun ins hins => by rw [R0_size_eq]; exact instrRegsLt_of_instrLt (hprog ins hins))
    (rep_regs0_of hBF) hslp).2
  intro j hj
  rw [L_size] at hj
  have hj' : j < D.sel.size := by omega
  have e2 : 2 * j / 2 = j := by omega
  have e : (L D)[2 * j]! = (SLP D).1[D.sel[j]!]! := by
    rw [getElem!_pos (L D) (2 * j) (by rw [L_size]; omega)]
    simp only [L, lettersOf, Array.getElem_ofFn]
    rw [ite_eq_left (by omega), e2]
  rw [e]
  exact hR _ (by rw [R0_size_eq]; exact hsel j hj')

theorem invOK_letters (hrep : ∀ j < (L D).size / 2, Rep D.n (L D)[2 * j]! (gs D j))
    (hsz : ∀ l < (L D).size, (L D)[l]!.size = D.n) :
    ∀ j < (L D).size / 2, invOK D.n (L D)[2 * j]! (L D)[2 * j + 1]! = true := by
  intro j hj
  have hj2 : 2 * j < (L D).size := by omega
  have hj' : j < D.sel.size := by rw [L_size] at hj; omega
  have e : (L D)[2 * j + 1]! = invT D.n (L D)[2 * j]! := by
    have e1 : (2 * j + 1) / 2 = j := by omega
    have e2 : 2 * j / 2 = j := by omega
    rw [getElem!_pos (L D) (2 * j + 1) (by omega), getElem!_pos (L D) (2 * j) hj2]
    simp only [L, lettersOf, Array.getElem_ofFn]
    rw [ite_eq_right (by omega), ite_eq_left (by omega), e1, e2]
  rw [e]
  have hTR : CFSG.KS.TW.TR D.n (L D)[2 * j]! (idx D.n (gs D j)) :=
    ⟨hsz _ hj2, fun i hi => ⟨hrep j hj i hi, idx_lt _ hi⟩⟩
  have hR := CFSG.KS.TW.invT_TR (n_lt32 hBF) hTR (g := idx D.n (gs D j)⁻¹)
    fun i hi => ⟨idx_lt _ hi, idx_idx_inv _ i, idx_inv_idx _ i⟩
  exact CFSG.KS.TW.invOK_of hTR hR fun i _ => idx_inv_idx _ i

end Letters

theorem vecCert_of_kernel (D : VecData) (c : Nat) {csA csB : List Char}
    {MA MB NA NB NAi NBi BI BM kL : Nat} {P AT BT FO S IP SP : Nat → Nat} {R V LM : List Nat}
    {LT Ot IX Op Ol : Nat → Nat → Nat} {STs SPs SLs : List (Nat → Nat)} {LB PS : Nat → Nat}
    (hA : D.seedA = String.ofList csA) (hB : D.seedB = String.ofList csB)
    (hseed : seedK csA csB D.d MA MB NA NB D.expA D.expB = true)
    (hAi : Nat.beq (mulF D.d NA NAi) (idF D.d) = true) (hBi : Nat.beq (mulF D.d NB NBi) (idF D.d) = true)
    (hn : andB (Nat.blt (nat_lit 0) D.n) (Nat.blt D.n (pw2 (nat_lit 30))) = true)
    (hP0 : Nat.beq (lk P (nat_lit 32) (nat_lit 0)) D.v0 = true)
    (horb : ∀ h < D.n, orbAt D.d D.n NA NB P AT BT h = true)
    (hbfs : ∀ h < D.n, bfsAt D.n AT BT FO h = true)
    (hsort : ∀ h < D.n, sortAt D.n P S IP SP h = true)
    (hregs : andB (Nat.ble (nat_lit 2) D.nregs) (andB (allL (instrLtK D.nregs) D.prog)
      (allL (fun s => Nat.blt s D.nregs) D.sel.toList)) = true)
    (hslp : slpOK D.d D.prog (regs0N D.d D.nregs (wordN D.d NA NAi NB NBi D.w0)
      (wordN D.d NA NAi NB NBi D.w1)) V R = true)
    (hkL : Nat.beq kL (Nat.mul (nat_lit 2) D.sel.size) = true)
    (hkL32 : Nat.blt kL (pw2 (nat_lit 32)) = true)
    (hlet : lettersK D.d R D.sel.toList LM = true)
    (hLT : ∀ j < kL, ∀ h < D.n, letAt D.d D.n (getL (nat_lit 0) LM j) P (LT j) h = true)
    (hchain : andB (Nat.beq D.base.size D.orbSizes.length) (andB (Nat.beq D.qb.size D.base.size)
      (andB (allL (fun s => Nat.blt (nat_lit 0) s) D.orbSizes)
      (andB (allN D.basis.size fun t => Nat.blt (getL (nat_lit 0) D.basis.toList t) D.n)
      (allN D.base.size fun i => strictB (getL (nat_lit 0) D.qb.toList i) fun x =>
        andB (Nat.blt x D.basis.size)
          (Nat.beq (getL (nat_lit 0) D.basis.toList x) (getL (nat_lit 0) D.base.toList i)))))) = true)
    (htree : ∀ i < D.base.size, ∀ t < getL (nat_lit 0) D.orbSizes i,
      treeAt D.n kL (getL (nat_lit 0) D.orbSizes i) i (getL (nat_lit 0) D.base.toList i) LT
        (getL (nat_lit 0) D.base.toList) (Ot i) (IX i) (Op i) (Ol i) t = true)
    (hsub0 : andB (Nat.blt (nat_lit 0) D.base.size) (andB (Nat.beq (getL (nat_lit 0) D.base.toList 0) 0)
      (andB (Nat.blt (nat_lit 0) D.subReps.size) (andB (Nat.beq (getL (nat_lit 0) D.subReps.toList 0) 0)
      (andB (Nat.beq D.subSizes.length D.subReps.size)
        (allL (fun s => Nat.blt (nat_lit 0) s) D.subSizes))))) = true)
    (hsub : ∀ j < D.subReps.size, ∀ t < getL (nat_lit 0) D.subSizes j,
      subAt D.n kL (getL (nat_lit 0) D.subSizes j) j (getL (nat_lit 0) D.subReps.toList j) LT
        (getL (nat_lit 0) D.base.toList) (getF STs j) LB PS (getF SPs j) (getF SLs j) t = true)
    (hlab : ∀ p < D.n, labAt D.subReps.size D.subSizes STs LB PS p = true)
    (hord : andB (ordK D.d (wordN D.d NA NAi NB NBi D.w0) D.basis.size P (getL (nat_lit 0) D.basis.toList)
        D.ord0.1 D.ord0.2)
      (andB (ordK D.d (wordN D.d NA NAi NB NBi D.w1) D.basis.size P (getL (nat_lit 0) D.basis.toList)
        D.ord1.1 D.ord1.2)
      (ordK D.d (mulF D.d (wordN D.d NA NAi NB NBi D.w1) (wordN D.d NA NAi NB NBi D.w0)) D.basis.size P
        (getL (nat_lit 0) D.basis.toList) D.ord01.1 D.ord01.2)) = true)
    (hbasis : andB (Nat.beq D.basis.size D.d) (andB (packB D.d D.basisInv.toList BI)
      (basisK D.d BI BM P (getL (nat_lit 0) D.basis.toList))) = true)
    (hcard : Nat.card (CFSG.Sporadic.SmallF2.J D) ≤ D.orbSizes.prod) :
    vecCert D c = true := by
  have hBF := baseFacts D hA hB hseed hAi hBi hn hP0 horb hbfs hsort hchain hbasis
  have hslpc := slpChecks_ok D hA hB hseed hAi hBi hn hP0 horb hbfs hsort hregs hslp
  have hLeq := letters_eq D hA hB hseed hAi hBi hn hP0 horb hbfs hsort hregs hslp hkL hlet hLT
  have hordc := ordChecks_ok D hA hB hseed hAi hBi hn hP0 horb hbfs hsort hregs hchain hord
  have hbase := baseChecks_ok D hA hB hseed hAi hBi hn hP0 horb hbfs hsort hchain hbasis
  have hsl := hslpc
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Array.all_eq_true] at hsl
  obtain ⟨⟨⟨-, hprog⟩, hok⟩, hsel⟩ := hsl
  have hsel' : ∀ j < D.sel.size, D.sel[j]! < D.nregs := fun j hj => by
    rw [getElem!_pos D.sel j hj]
    simpa using hsel j hj
  have hch := hchain
  simp only [andB_eq, Bool.and_eq_true] at hch
  obtain ⟨-, hqbs, -, hbl, hqbl⟩ := hch
  have hqbs := Nat.eq_of_beq_eq_true hqbs
  rw [allN_iff] at hbl hqbl
  have hQ : ∀ t < D.basis.size, D.basis[t]! < D.n := fun t ht => by
    have := hbl t ht
    rw [Nat.blt_eq, getL_array _ ht] at this
    exact this
  have hqbQ : ∀ i < D.base.size, D.qb[i]! < D.basis.size ∧ D.basis[D.qb[i]!]! = D.base[i]! := by
    intro i hi
    have := hqbl i hi
    simp only [strictB_eq, Bool.and_eq_true, Nat.blt_eq] at this
    rw [getL_array _ (by omega : i < D.qb.size)] at this
    obtain ⟨h1, h2⟩ := this
    rw [getL_array _ h1, getL_array _ hi] at h2
    exact ⟨h1, Nat.eq_of_beq_eq_true h2⟩
  have hLs : (CFSG.Sporadic.SmallF2.L D).size = kL := hLeq.1
  have hsz : ∀ l < (CFSG.Sporadic.SmallF2.L D).size, (CFSG.Sporadic.SmallF2.L D)[l]!.size = D.n :=
    fun l hl => (hLeq.2 l (hLs ▸ hl)).1
  have hrepE := rep_letters_of hBF hprog hok hsel'
  have hinv := invOK_letters hBF hrepE hsz
  have h2 : (CFSG.Sporadic.SmallF2.L D).size % 2 = 0 := by
    rw [CFSG.Sporadic.SmallF2.L_size]
    omega
  have hkE : kL % 2 = 0 := by
    rw [← hLs]
    exact h2
  obtain ⟨hos, hTs⟩ := chainTrees_spec D hn hkL32 hLeq hLT hkE hinv hchain htree
  have hsubc := subChecks_ok D hn hkL32 hLeq hLT hkE hinv hsub0 hsub hlab
  have hTsz : (CFSG.Sporadic.SmallF2.T D).size = D.base.size := CFSG.Sporadic.SmallF2.T_size D
  have hcard' : Nat.card (CFSG.Sporadic.SmallF2.J D) ≤
      ∏ i ∈ Finset.range D.base.size, (CFSG.Sporadic.SmallF2.T D)[i]!.pts.size := by
    rw [← hTsz, ← prod_orbitSizes]
    have hos' : orbitSizes (CFSG.Sporadic.SmallF2.T D) = D.orbSizes := hos
    rw [hos']
    exact hcard
  obtain ⟨hchainOK, hsift⟩ := chain_sound h2 hrepE hinv hTsz hqbs hQ hqbQ
    (fun i hi => (hTs i hi).2.ok) hcard'
  have hsA := hsift (CFSG.Sporadic.SmallF2.a D) (apT (CFSG.Sporadic.SmallF2.O D).alpha D.basis)
    (apT_size _ _) fun t ht => by
      rw [apT_get _ _ ht, CFSG.Sporadic.SmallF2.rep_a hBF _ (hQ t ht)]
  have hsB := hsift (CFSG.Sporadic.SmallF2.b D) (apT (CFSG.Sporadic.SmallF2.O D).beta D.basis)
    (apT_size _ _) fun t ht => by
      rw [apT_get _ _ ht, CFSG.Sporadic.SmallF2.rep_b hBF _ (hQ t ht)]
  unfold vecCert
  dsimp only
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨⟨hbase, ?_⟩, hsubc⟩, hordc⟩
  unfold chainChecks
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
  exact ⟨⟨⟨⟨hslpc, hchainOK c⟩, by rw [beq_iff_eq]; exact hos⟩, hsA⟩, hsB⟩

end CFSG.KC.VecK

end
