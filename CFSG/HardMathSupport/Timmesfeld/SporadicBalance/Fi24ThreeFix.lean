
module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24ThreeTables
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Sep
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24ThreeFacts

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Proving
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native
open CFSG.Sporadic.Fi24.Native CFSG.Sporadic.FischerOddCore
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three.Native
open CFSG.Sporadic.Fi24 (R J JR jR tR cls lvl gs letters)

attribute [local instance] CFSG.Sporadic.Fi24.rAction

section Level

theorem mem_lvl_of_fix {g : J} {i : ℕ} (hi : i ≤ 6)
    (h : ∀ t < i, idx 306936 g chainBase[t]! = chainBase[t]!) : g ∈ lvl i := by
  induction i with
  | zero => exact CFSG.Sporadic.Fi24.mem_lvl_zero g
  | succ i ih =>
    have hg := ih (by omega) fun t ht => h t (by omega)
    exact (CFSG.Sporadic.Fi24.chain_facts'.2.1 i
      (by rw [CFSG.Sporadic.Fi24.chainBase_size]; omega) g hg).1 (h i (by omega))

theorem card_lvl_three : Nat.card (lvl 3) = 68024448 := by
  rw [CFSG.Sporadic.Fi24.chain_facts'.2.2 3 (by rw [CFSG.Sporadic.Fi24.chainBase_size]; norm_num),
    CFSG.Sporadic.Fi24.chainBase_size]
  rw [show Finset.Ico 3 6 = {3, 4, 5} by decide]
  rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton,
    CFSG.Sporadic.Fi24.tree_size_of (l := 3) rfl, CFSG.Sporadic.Fi24.tree_size_of (l := 4) rfl,
    CFSG.Sporadic.Fi24.tree_size_of (l := 5) rfl]
  norm_num

theorem card_dvd_of_fix_lvl3_card {y : ℕ} (hy : y < 306936)
    (hsz : 128 ∣ Nat.card (MulAction.orbit (lvl 3) (⟨y, hy⟩ : Fin 306936))) (H : Subgroup J)
    (hH : ∀ g ∈ H, (∀ t < 3, idx 306936 g chainBase[t]! = chainBase[t]!) ∧ idx 306936 g y = y) :
    Nat.card H ∣ 3 ^ 12 := by
  have hHK : H ≤ lvl 3 := fun g hg => mem_lvl_of_fix (by norm_num) (hH g hg).1
  set y' : Fin 306936 := ⟨y, hy⟩ with hy'
  have hos : Nat.card (MulAction.orbit (lvl 3) y') *
      Nat.card (MulAction.stabilizer (lvl 3) y') = Nat.card (lvl 3) := by
    rw [← Nat.card_prod]
    exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (lvl 3) y')
  rw [card_lvl_three] at hos
  have hle : H.subgroupOf (lvl 3) ≤ MulAction.stabilizer (lvl 3) y' := by
    intro g hg
    rw [Subgroup.mem_subgroupOf] at hg
    rw [MulAction.mem_stabilizer_iff]
    apply Fin.ext
    show ((g : J) • y').val = y
    rw [← idx_of_lt (g : J) hy]
    exact (hH g hg).2
  have h1 : Nat.card H = Nat.card (H.subgroupOf (lvl 3)) :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHK).toEquiv).symm
  obtain ⟨q, hq⟩ := hsz
  have h3 : Nat.card (MulAction.stabilizer (lvl 3) y') ∣ 3 ^ 12 := by
    refine ⟨q, ?_⟩
    rw [hq] at hos
    have : 128 * (q * Nat.card (MulAction.stabilizer (lvl 3) y')) = 128 * 3 ^ 12 := by
      rw [← mul_assoc, hos]; norm_num
    have := Nat.eq_of_mul_eq_mul_left (by norm_num) this
    rw [← this]; ring
  rw [h1]
  exact (Subgroup.card_dvd_of_le hle).trans h3

theorem card_dvd_of_fix_lvl3 {y : ℕ} {T : Tree}
    (hT : TreeFacts 306936 T (levelLetters letters chainBase 3) (pairG gs) y)
    (hsz : 128 ∣ T.pts.size) (H : Subgroup J)
    (hH : ∀ g ∈ H, (∀ t < 3, idx 306936 g chainBase[t]! = chainBase[t]!) ∧ idx 306936 g y = y) :
    Nat.card H ∣ 3 ^ 12 := by
  have hHK : H ≤ lvl 3 := fun g hg => mem_lvl_of_fix (by norm_num) (hH g hg).1
  set y' : Fin 306936 := ⟨y, hT.r_lt⟩ with hy'
  have horb : Nat.card (MulAction.orbit (lvl 3) y') = T.pts.size := hT.card_orbit
  have hos : Nat.card (MulAction.orbit (lvl 3) y') *
      Nat.card (MulAction.stabilizer (lvl 3) y') = Nat.card (lvl 3) := by
    rw [← Nat.card_prod]
    exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (lvl 3) y')
  rw [horb, card_lvl_three] at hos
  have hle : H.subgroupOf (lvl 3) ≤ MulAction.stabilizer (lvl 3) y' := by
    intro g hg
    rw [Subgroup.mem_subgroupOf] at hg
    rw [MulAction.mem_stabilizer_iff]
    apply Fin.ext
    show ((g : J) • y').val = y
    rw [← idx_of_lt (g : J) hT.r_lt]
    exact (hH g hg).2
  have h1 : Nat.card H = Nat.card (H.subgroupOf (lvl 3)) :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHK).toEquiv).symm
  obtain ⟨q, hq⟩ := hsz
  have h3 : Nat.card (MulAction.stabilizer (lvl 3) y') ∣ 3 ^ 12 := by
    refine ⟨q, ?_⟩
    rw [hq] at hos
    have : 128 * (q * Nat.card (MulAction.stabilizer (lvl 3) y')) = 128 * 3 ^ 12 := by
      rw [← mul_assoc, hos]; norm_num
    have := Nat.eq_of_mul_eq_mul_left (by norm_num) this
    rw [← this]; ring
  rw [h1]
  exact (Subgroup.card_dvd_of_le hle).trans h3

end Level

theorem getElem!_map_lt {α β : Type} [Inhabited α] [Inhabited β] (a : Array α) (f : α → β)
    {i : ℕ} (hi : i < a.size) : (a.map f)[i]! = f a[i]! := by
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_map, getElem!_pos a i hi]

theorem mem_filter_fix {S : Table} {x : ℕ} :
    x ∈ (Array.range nPts).filter (fun i => ap S i == i) ↔ x < 306936 ∧ ap S x = x := by
  rw [Array.mem_filter, Array.mem_range, beq_iff_eq]
  rfl

section Facts

theorem vecOf_spec (T : Array ℕ) (hT : ∀ t ∈ T, t < 306936) (d : Fin 306936) :
    (vecOf ctx T d).size = T.size ∧ ∀ j < T.size,
      (vecOf ctx T d)[j]! = (idx 306936 (cls d) T[j]! == T[j]!) := by
  have hq : ∀ j < T.size, T[j]! < 306936 := fun j hj => by
    rw [getElem!_pos T j hj]
    exact hT _ (Array.getElem_mem hj)
  have hc := fo24Cls_spec d T hq
  refine ⟨by simp [vecOf], fun j hj => ?_⟩
  unfold vecOf
  rw [getElem!_map_lt _ _ (by simpa using hj)]
  rw [getElem!_pos (Array.range T.size) j (by simpa using hj), Array.getElem_range]
  rw [clsAtN_ctx, hc.2 j hj]

theorem commute_iff_idx (k t : Fin 306936) :
    cls t * cls k = cls k * cls t ↔ idx 306936 (cls k) t = t := by
  rw [idx_of_lt _ t.2, Fin.val_eq_val]
  exact ⟨fun h => (cls_smul_eq_iff k t).2 h.symm, fun h => ((cls_smul_eq_iff k t).1 h).symm⟩

theorem eq_one_of_idx {g : J} (h : ∀ i < 306936, idx 306936 g i = i) : g = 1 := by
  apply eq_of_smul_eq_smul (α := Fin 306936)
  intro p
  apply Fin.ext
  rw [one_smul, ← idx_of_lt g p.2]
  exact h p p.2

theorem fixFacts_of_check {w : List ℕ} {m y : ℕ} {T : Array ℕ} {gp : Array (ℕ × ℕ)}
    (h : fixCheck ctx w m y T gp = true) : FixFacts w y := by
  unfold fixCheck at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hw, h3⟩, hm⟩, hsm⟩, h0⟩, h1⟩, h2⟩, hy⟩, hsy⟩, hT⟩, hgp⟩, hsep⟩, hp1⟩,
    hB⟩ := h
  have hw' : ∀ l ∈ w, l < letters.size := fun l hl => by
    have := List.all_eq_true.1 hw l hl
    rw [decide_eq_true_eq, ctx_L] at this
    exact this
  have hS := rep_wordTab w hw'
  set s := wordElt w with hsdef
  have hsk : ∀ k : Fin 306936, (s • k).val = ap (wordTab ctx w) k := smul_val_of_rep hS
  have hfixF : ∀ k : Fin 306936, s • k = k ↔
      k.val ∈ (Array.range nPts).filter (fun i => ap (wordTab ctx w) i == i) := by
    intro k
    rw [mem_filter_fix, ← hsk, Fin.val_eq_val]
    exact ⟨fun h => ⟨k.2, h⟩, fun h => h.2⟩
  have hTall : ∀ t ∈ T, t < 306936 ∧ ap (wordTab ctx w) t = t := by
    intro t ht
    have := Array.all_eq_true.1 hT
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 ht
    have h' := this i hi
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h'
    exact h'
  have hT' : ∀ t ∈ T, t < 306936 := fun t ht => (hTall t ht).1
  set F := (Array.range nPts).filter (fun i => ap (wordTab ctx w) i == i) with hF
  have hFlt : ∀ i < F.size, F[i]! < 306936 := fun i hi => by
    rw [getElem!_pos F i hi]
    exact (mem_filter_fix.1 (Array.getElem_mem hi)).1
  have hVget : ∀ i < F.size, (F.map (vecOf ctx T))[i]! = vecOf ctx T F[i]! :=
    fun i hi => getElem!_map_lt F (vecOf ctx T) hi
  have hvec : ∀ (d : Fin 306936), ∀ j < T.size, ∀ t : Fin 306936, t.val = T[j]! →
      ((vecOf ctx T d)[j]! = true ↔ cls t * cls d = cls d * cls t) := by
    intro d j hj t ht
    rw [(vecOf_spec T hT' d).2 j hj, beq_iff_eq, commute_iff_idx, ht]
  have hidx : ∀ k : Fin 306936, s • k = k → ∃ i < F.size, F[i]! = k.val := by
    intro k hk
    obtain ⟨i, hi, hik⟩ := Array.mem_iff_getElem.1 ((hfixF k).1 hk)
    exact ⟨i, hi, by rw [getElem!_pos F i hi]; exact hik⟩
  have hdiff : ∀ (d d' : Fin 306936), vecOf ctx T d ≠ vecOf ctx T d' →
      ∃ j < T.size, (vecOf ctx T d)[j]! ≠ (vecOf ctx T d')[j]! := by
    intro d d' hne
    by_contra hall
    push Not at hall
    apply hne
    apply Array.ext
    · rw [(vecOf_spec T hT' d).1, (vecOf_spec T hT' d').1]
    · intro j h1 h2
      have hj : j < T.size := by rwa [(vecOf_spec T hT' d).1] at h1
      have := hall j hj
      rwa [getElem!_pos _ j h1, getElem!_pos _ j h2] at this
  refine ⟨hw', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    exact eq_one_of_idx (idx_cube_of_order3OK hS h3)
  ·
    intro h1'
    rw [decide_eq_true_eq] at hm
    rw [bne_iff_ne, ne_eq, hS m hm, hsdef, h1', idx_one] at hsm
    exact hsm rfl
  · intro t ht
    rw [← hS _ (CFSG.Sporadic.Fi24.chainBase_lt t (by omega))]
    rcases (show t = 0 ∨ t = 1 ∨ t = 2 by omega) with rfl | rfl | rfl
    · rw [beq_iff_eq] at h0; exact h0
    · rw [beq_iff_eq] at h1; exact h1
    · rw [beq_iff_eq] at h2; exact h2
  · rw [decide_eq_true_eq] at hy; exact hy
  · rw [decide_eq_true_eq] at hy
    rw [beq_iff_eq, hS y hy] at hsy
    exact hsy
  ·
    intro k k' hk hk' hne hc
    obtain ⟨i, hi, hik⟩ := hidx k hk
    obtain ⟨j, hj, hjk⟩ := hidx k' hk'
    have hij : i ≠ j := fun e => hne (Fin.ext (by rw [← hik, ← hjk, e]))
    have key : ∀ (a b : Fin 306936) (ia ib : ℕ), ia < ib → ib < F.size → F[ia]! = a.val →
        F[ib]! = b.val → cls a * cls b = cls b * cls a →
        ∃ j < T.size, (vecOf ctx T a)[j]! ≠ (vecOf ctx T b)[j]! := by
      intro a b ia ib hab hb ha' hb' hcab
      have := (allIn_eq_true.1 ((allIn_eq_true.1 hsep) ia (Nat.zero_le _) (by omega)))
        ib (by omega) hb
      rw [Bool.or_eq_true, bne_iff_ne, Bool.not_eq_true'] at this
      rcases this with hv | hcomm
      · rw [hVget ia (by omega), hVget ib hb] at hv
        rw [ha', hb'] at hv
        exact hdiff a b (by simpa using hv)
      · exfalso
        have h' : commB ctx a b = true := (commB_iff a b).2 hcab
        rw [ha', hb', h'] at hcomm
        exact absurd hcomm (by decide)
    have hjj : ∃ jj < T.size, (vecOf ctx T k)[jj]! ≠ (vecOf ctx T k')[jj]! := by
      rcases Nat.lt_or_gt_of_ne hij with hlt | hgt
      · exact key k k' i j hlt hj hik hjk hc
      · obtain ⟨jj, hjj, hd⟩ := key k' k j i hgt hi hjk hik hc.symm
        exact ⟨jj, hjj, fun e => hd e.symm⟩
    obtain ⟨jj, hjj, hd⟩ := hjj
    have htlt : T[jj]! < 306936 := by
      rw [getElem!_pos T jj hjj]; exact hT' _ (Array.getElem_mem hjj)
    refine ⟨⟨T[jj]!, htlt⟩, ?_, ?_⟩
    · apply Fin.ext
      rw [hsk]
      show ap (wordTab ctx w) T[jj]! = T[jj]!
      rw [getElem!_pos T jj hjj]
      exact (hTall _ (Array.getElem_mem hjj)).2
    · have e1 := hvec k jj hjj ⟨T[jj]!, htlt⟩ rfl
      have e2 := hvec k' jj hjj ⟨T[jj]!, htlt⟩ rfl
      by_cases h1' : (vecOf ctx T k)[jj]! = true
      · have h2' : (vecOf ctx T k')[jj]! = false := by
          cases h : (vecOf ctx T k')[jj]!
          · rfl
          · rw [h1', h] at hd; exact absurd rfl hd
        left
        refine ⟨e1.1 h1', fun hc' => ?_⟩
        rw [← e2] at hc'
        rw [hc'] at h2'
        exact absurd h2' (by decide)
      · have h1'' : (vecOf ctx T k)[jj]! = false := by simpa using h1'
        have h2' : (vecOf ctx T k')[jj]! = true := by
          cases h : (vecOf ctx T k')[jj]!
          · rw [h1'', h] at hd; exact absurd rfl hd
          · rfl
        right
        refine ⟨fun hc' => h1' (e1.2 hc'), e2.1 h2'⟩
  ·
    intro k hk
    obtain ⟨i, hi, hik⟩ := hidx k hk
    have hv := Array.all_eq_true.1 hp1 i (by simpa using hi)
    rw [Array.getElem_map] at hv
    rw [← getElem!_pos F i hi, hik] at hv
    obtain ⟨j, hj, hjf⟩ := Array.mem_iff_getElem.1 (Array.contains_iff_mem.1 hv)
    have hjT : j < T.size := by rwa [(vecOf_spec T hT' k).1] at hj
    have htlt : T[j]! < 306936 := by
      rw [getElem!_pos T j hjT]; exact hT' _ (Array.getElem_mem hjT)
    refine ⟨⟨T[j]!, htlt⟩, ?_, ?_⟩
    · apply Fin.ext
      rw [hsk]
      show ap (wordTab ctx w) T[j]! = T[j]!
      rw [getElem!_pos T j hjT]
      exact (hTall _ (Array.getElem_mem hjT)).2
    · intro hc
      have := (hvec k j hjT ⟨T[j]!, htlt⟩ rfl).2 hc.symm
      rw [getElem!_pos _ j hj, hjf] at this
      exact absurd this (by decide)
  ·
    intro k hk hc
    have hb := allIn_eq_true.1 hB k (Nat.zero_le _) k.2
    rw [Bool.or_eq_true, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true'] at hb
    have hsk' : ap (wordTab ctx w) k ≠ k := by
      intro e; apply hk; apply Fin.ext; rw [hsk, e]
    have hcomm' : commB ctx k (ap (wordTab ctx w) k) = true := by
      have := (commB_iff k (s • k)).2 hc
      rwa [hsk] at this
    rcases hb with (hb | hb) | hb
    · exact absurd hb hsk'
    · obtain ⟨t, ht, hoff⟩ := Array.any_eq_true'.1 hb
      obtain ⟨jj, hjj, rfl⟩ := Array.mem_iff_getElem.1 ht
      rw [Array.size_map] at hjj
      rw [Array.getElem_map] at hoff
      have hg := Array.all_eq_true.1 hgp jj hjj
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hg
      obtain ⟨⟨⟨hd, he⟩, hsd⟩, hse⟩ := hg
      refine ⟨⟨gp[jj].1, hd⟩, ⟨gp[jj].2, he⟩, ?_, ?_, ?_⟩
      · apply Fin.ext; rw [hsk]; exact hsd
      · apply Fin.ext; rw [hsk]; exact hse
      have hR : Rep 306936 (compT nPts (clsTab ctx gp[jj].1) (clsTab ctx gp[jj].2))
          (cls ⟨gp[jj].1, hd⟩ * cls ⟨gp[jj].2, he⟩) :=
        Rep.compT (rep_clsTab ⟨gp[jj].1, hd⟩) (rep_clsTab ⟨gp[jj].2, he⟩)
      have hS2 : Rep 306936 (compT nPts (wordTab ctx w) (wordTab ctx w)) (s * s) :=
        Rep.compT hS hS
      unfold offTriple at hoff
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hoff
      obtain ⟨⟨o1, o2⟩, o3⟩ := hoff
      have hRk := smul_val_of_rep_R hR k
      have hS2k := smul_val_of_rep hS2 k
      refine ⟨fun e => o1 ?_, fun e => o2 ?_, fun e => o3 ?_⟩
      · rw [← hRk, e]
      · rw [← hRk, e, hsk]
      · rw [← hRk, e, ← hS2k, mul_smul]
    · exact absurd hcomm' (by rw [hb]; decide)

end Facts

section Class

theorem cls_mul_self (k : Fin 306936) : cls k * cls k = 1 := by
  have h := pow_orderOf_eq_one (cls k)
  rwa [CFSG.Sporadic.Fi24.orderOf_mem_D24 (CFSG.Sporadic.Fi24.cls_mem k), pow_two] at h

theorem cls_cube {k l : Fin 306936}
    (h : cls k * cls l ≠ cls l * cls k) :
    cls k * cls l * (cls k * cls l) * (cls k * cls l) = 1 := by
  rcases CFSG.Sporadic.Fi24.orderOf_mul_mem_D24 (CFSG.Sporadic.Fi24.cls_mem k)
      (CFSG.Sporadic.Fi24.cls_mem l) with h1 | h1 | h1
  · exfalso
    apply h
    have h2 : cls k * cls l = 1 := orderOf_eq_one_iff.1 h1
    have h3 : cls l = (cls k)⁻¹ := eq_inv_of_mul_eq_one_right h2
    rw [h3, mul_inv_cancel, inv_mul_cancel]
  · exfalso
    apply h
    have h3 := pow_orderOf_eq_one (cls k * cls l)
    rw [h1, sq] at h3
    have E : cls k * cls l * (cls k * cls l) = 1 := h3
    have hkk := cls_mul_self k
    have hll := cls_mul_self l
    symm
    calc cls l * cls k = cls l * cls k * (cls k * cls l * (cls k * cls l)) := by rw [E, mul_one]
      _ = cls l * (cls k * cls k) * cls l * (cls k * cls l) := by simp only [mul_assoc]
      _ = cls l * cls l * (cls k * cls l) := by rw [hkk, mul_one]
      _ = cls k * cls l := by rw [hll, one_mul]
  · have h3 := pow_orderOf_eq_one (cls k * cls l)
    rw [h1, pow_three'] at h3
    exact h3

theorem cls_mul_cls_smul {k l : Fin 306936}
    (h : cls k * cls l ≠ cls l * cls k) : (cls k * cls l) • k = l := by
  apply CFSG.Sporadic.Fi24.cls_injective
  rw [CFSG.Sporadic.Fi24.cls_smul_R]
  have h3 := cls_cube h
  have hk := cls_mul_self k
  have hl := cls_mul_self l
  have hki : (cls k)⁻¹ = cls k := inv_eq_of_mul_eq_one_right hk
  have hli : (cls l)⁻¹ = cls l := inv_eq_of_mul_eq_one_right hl
  rw [mul_inv_rev, hki, hli]
  have e : cls k * cls l * cls k * cls l * cls k * cls l = 1 := by
    rw [← h3]; simp only [mul_assoc]
  calc cls k * cls l * cls k * (cls l * cls k)
      = cls k * cls l * cls k * cls l * cls k * cls l * cls l := by
        simp only [mul_assoc, hl, mul_one]
    _ = cls l := by rw [e, one_mul]

theorem cls_commute_of_fix {s : J} {k : Fin 306936} (h : s • k = k) :
    cls k * jR s = jR s * cls k :=
  ((smul_eq_iff_commute s k).1 h).symm

theorem exists_jR_cls_mul_cls {s : J} {k l : Fin 306936} (hk : s • k = k) (hl : s • l = l) :
    ∃ t : J, jR t = cls k * cls l ∧ t * s = s * t := by
  obtain ⟨t, ht⟩ := exists_jR_of_mem (cls_mul_cls_mem_JR k l)
  refine ⟨t, ht, CFSG.Sporadic.Fi24.jR_injective ?_⟩
  rw [map_mul, map_mul, ht]
  calc cls k * cls l * jR s = cls k * (cls l * jR s) := by rw [mul_assoc]
    _ = cls k * (jR s * cls l) := by rw [cls_commute_of_fix hl]
    _ = (cls k * jR s) * cls l := by rw [mul_assoc]
    _ = (jR s * cls k) * cls l := by rw [cls_commute_of_fix hk]
    _ = jR s * (cls k * cls l) := by rw [mul_assoc]

end Class

section Core

theorem gLAPPrimeCoreOf_fix_of_fixFacts {w : List ℕ} {y : ℕ} (hF : FixFacts w y) :
    ∀ n ∈ GLAPPrimeCoreOf 3 (Subgroup.centralizer ({wordElt w} : Set J)),
      ∀ k : Fin 306936, wordElt w • k = k → n • k = k := by
  have := finite_J
  set s := wordElt w with hsdef
  set N := GLAPPrimeCoreOf 3 (Subgroup.centralizer ({s} : Set J)) with hN
  have hcop : Nat.Coprime 3 (Nat.card N) := coprime_card_GLAPPrimeCoreOf Nat.prime_three _
  set D₀ : Set R := {x | ∃ k : Fin 306936, s • k = k ∧ x = cls k} with hD₀
  have key := @commute_of_sepThree J (inferInstance : Group J) R (inferInstance : Group R)
    this jR CFSG.Sporadic.Fi24.jR_injective N hcop D₀
    (by rintro _ ⟨k, -, rfl⟩; exact cls_mul_self k)
    (by
      rintro _ ⟨k, -, rfl⟩ _ ⟨l, -, rfl⟩ h
      exact cls_cube h)
    (by
      rintro _ ⟨k, hk, rfl⟩ n hn
      exact conj_mem_gLAPPrimeCoreOf (cls_commute_of_fix hk) hn)
    (by
      rintro _ ⟨k, hk, rfl⟩ n hn
      refine ⟨n⁻¹ • k, ?_, ?_⟩
      · have hnC : n⁻¹ ∈ Subgroup.centralizer ({s} : Set J) :=
          (Subgroup.centralizer _).inv_mem (GLAPPrimeCoreOf_le _ hn)
        have hc : n⁻¹ * s = s * n⁻¹ := CFSG.Sporadic.Fi24.mem_centralizer_J.1 hnC
        rw [← mul_smul, ← hc, mul_smul, hk]
      · rw [← CFSG.Sporadic.Fi24.jR_smul, map_inv, CFSG.Sporadic.Fi24.cls_smul_R, inv_inv])
    (by
      rintro _ ⟨k, hk, rfl⟩ _ ⟨k', hk', rfl⟩ hne hc
      have hkk : k ≠ k' := fun e => hne (by rw [e])
      obtain ⟨t, ht, hor⟩ := hF.sep k k' hk hk' hkk hc
      exact ⟨cls t, ⟨t, ht, rfl⟩, hor⟩)
  intro n hn k hk
  exact (smul_eq_iff_commute n k).2 (key n hn (cls k) ⟨k, hk, rfl⟩)

theorem gLAPPrimeCoreOf_eq_bot_of_fixFacts {w : List ℕ} {y : ℕ} (hF : FixFacts w y)
    (hbound : ∀ H : Subgroup J, (∀ g ∈ H, (∀ t < 3, idx 306936 g chainBase[t]! = chainBase[t]!) ∧
      idx 306936 g y = y) → Nat.card H ∣ 3 ^ 12) :
    GLAPPrimeCoreOf 3 (Subgroup.centralizer ({wordElt w} : Set J)) = ⊥ := by
  set N := GLAPPrimeCoreOf 3 (Subgroup.centralizer ({wordElt w} : Set J)) with hN
  have hfix := gLAPPrimeCoreOf_fix_of_fixFacts hF
  have hdvd : Nat.card N ∣ 3 ^ 12 := by
    refine hbound N fun g hg => ⟨fun t ht => ?_, ?_⟩
    · have hlt := CFSG.Sporadic.Fi24.chainBase_get_lt
        (show t < chainBase.size by rw [CFSG.Sporadic.Fi24.chainBase_size]; omega)
      have hs : wordElt w • (⟨chainBase[t]!, hlt⟩ : Fin 306936) = ⟨chainBase[t]!, hlt⟩ := by
        apply Fin.ext
        rw [← idx_of_lt _ hlt]
        exact hF.fix0 t ht
      have := hfix g hg _ hs
      rw [idx_of_lt _ hlt, this]
    · have hs : wordElt w • (⟨y, hF.y_lt⟩ : Fin 306936) = ⟨y, hF.y_lt⟩ := by
        apply Fin.ext
        rw [← idx_of_lt _ hF.y_lt]
        exact hF.fixy
      have := hfix g hg _ hs
      rw [idx_of_lt _ hF.y_lt, this]
  have hcop : Nat.Coprime (3 ^ 12) (Nat.card N) :=
    Nat.Coprime.pow_left 12 (coprime_card_GLAPPrimeCoreOf Nat.prime_three _)
  exact Subgroup.card_eq_one.1 (Nat.Coprime.eq_one_of_dvd hcop.symm hdvd)

end Core

section Triple

structure TripleOf (r : R) (K : Set (Fin 306936)) : Prop where
  three : ∃ k₁ k₂ k₃ : Fin 306936, K = {k₁, k₂, k₃}
  fix : ∀ k ∈ K, r • k = k
  comm : ∀ k ∈ K, ∀ l : Fin 306936, r • l = l → cls k * cls l = cls l * cls k
  char : ∀ k : Fin 306936, r • k = k →
    (∀ l : Fin 306936, r • l = l → cls k * cls l = cls l * cls k) → k ∈ K

theorem TripleOf.conj {r : R} {K : Set (Fin 306936)} (h : TripleOf r K) (c : R) :
    TripleOf (c * r * c⁻¹) ((c • ·) '' K) := by
  have hc : ∀ l : Fin 306936, (c * r * c⁻¹) • l = l ↔ r • (c⁻¹ • l) = c⁻¹ • l := by
    intro l
    rw [mul_smul, mul_smul]
    constructor
    · intro e
      have := congrArg (c⁻¹ • ·) e
      simpa using this
    · intro e
      rw [e, smul_inv_smul]
  have hcls : ∀ l : Fin 306936, cls l = c * cls (c⁻¹ • l) * c⁻¹ := by
    intro l
    rw [CFSG.Sporadic.Fi24.cls_smul_R]
    group
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨k₁, k₂, k₃, rfl⟩ := h.three
    exact ⟨c • k₁, c • k₂, c • k₃, by simp [Set.image_insert_eq]⟩
  · rintro _ ⟨k, hk, rfl⟩
    rw [hc, inv_smul_smul, h.fix k hk]
  · rintro _ ⟨k, hk, rfl⟩ l hl
    have h1 := h.comm k hk _ ((hc l).1 hl)
    rw [hcls l, hcls (c • k), inv_smul_smul]
    calc c * cls k * c⁻¹ * (c * cls (c⁻¹ • l) * c⁻¹) = c * (cls k * cls (c⁻¹ • l)) * c⁻¹ := by
          group
      _ = c * (cls (c⁻¹ • l) * cls k) * c⁻¹ := by rw [h1]
      _ = c * cls (c⁻¹ • l) * c⁻¹ * (c * cls k * c⁻¹) := by group
  · intro k hk hall
    refine ⟨c⁻¹ • k, h.char _ ((hc k).1 hk) fun l hl => ?_, smul_inv_smul c k⟩
    have h1 := hall (c • l) ((hc _).2 (by rw [inv_smul_smul]; exact hl))
    rw [hcls k, hcls (c • l), inv_smul_smul] at h1
    have h2 : c * (cls (c⁻¹ • k) * cls l) * c⁻¹ = c * (cls l * cls (c⁻¹ • k)) * c⁻¹ := by
      calc c * (cls (c⁻¹ • k) * cls l) * c⁻¹
          = c * cls (c⁻¹ • k) * c⁻¹ * (c * cls l * c⁻¹) := by group
        _ = c * cls l * c⁻¹ * (c * cls (c⁻¹ • k) * c⁻¹) := h1
        _ = c * (cls l * cls (c⁻¹ • k)) * c⁻¹ := by group
    have h3 := congrArg (fun x => c⁻¹ * x * c) h2
    simpa [mul_assoc] using h3

theorem mem_of_three {k₁ k₂ k₃ x y z : Fin 306936}
    (hx : x ∈ ({k₁, k₂, k₃} : Set (Fin 306936))) (hy : y ∈ ({k₁, k₂, k₃} : Set (Fin 306936)))
    (hz : z ∈ ({k₁, k₂, k₃} : Set (Fin 306936))) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {v : Fin 306936} (hv : v ∈ ({k₁, k₂, k₃} : Set (Fin 306936))) : v = x ∨ v = y ∨ v = z := by
  classical
  have hsub : ({x, y, z} : Finset (Fin 306936)) ⊆ {k₁, k₂, k₃} := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy hz
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases ha with rfl | rfl | rfl <;> tauto
  have h3 : ({x, y, z} : Finset (Fin 306936)).card = 3 :=
    Finset.card_eq_three.2 ⟨x, y, z, hxy, hxz, hyz, rfl⟩
  have hcard : ({k₁, k₂, k₃} : Finset (Fin 306936)).card ≤ ({x, y, z} : Finset _).card := by
    rw [h3]; exact Finset.card_le_three
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  have hv' : v ∈ ({k₁, k₂, k₃} : Finset (Fin 306936)) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact hv
  rw [← heq] at hv'
  simpa using hv'

end Triple

section Outer

theorem exists_noncomm_of_pair {s : J} {k e : Fin 306936} (hk : s • k = k) (he : s • e = e)
    (hne : cls k * cls e ≠ cls e * cls k) :
    ∃ t : J, jR t = cls k * cls e ∧ t * s = s * t ∧ jR t * cls k ≠ cls k * jR t := by
  obtain ⟨t, ht, hts⟩ := exists_jR_cls_mul_cls hk he
  refine ⟨t, ht, hts, ?_⟩
  rw [ht]
  intro h
  apply hne
  have hkk := cls_mul_self k
  calc cls k * cls e = cls k * cls e * (cls k * cls k) := by rw [hkk, mul_one]
    _ = (cls k * cls e * cls k) * cls k := by simp only [mul_assoc]
    _ = (cls k * (cls k * cls e)) * cls k := by rw [h]
    _ = cls e * cls k := by rw [← mul_assoc, hkk, one_mul]

theorem exists_noncomm_cls_of_fixFacts {w : List ℕ} {y : ℕ} (hF : FixFacts w y)
    (k : Fin 306936) : ∃ t : J, t * wordElt w = wordElt w * t ∧ jR t * cls k ≠ cls k * jR t := by
  by_cases hk : wordElt w • k = k
  · obtain ⟨e, he, hne⟩ := hF.p1 k hk
    obtain ⟨t, -, hts, h⟩ := exists_noncomm_of_pair hk he hne
    exact ⟨t, hts, h⟩
  · exact ⟨wordElt w, rfl, fun h => hk ((smul_eq_iff_commute _ k).2 h)⟩

theorem exists_noncomm_triple_of_fixFacts {w : List ℕ} {y : ℕ} (hF : FixFacts w y) {r : R}
    {K : Set (Fin 306936)} (hT : TripleOf r K) :
    ∃ t : J, t * wordElt w = wordElt w * t ∧ jR t * r ≠ r * jR t := by
  set s := wordElt w with hsdef
  by_contra hall
  push Not at hall
  have hperm : ∀ t : J, t * s = s * t → ∀ k ∈ K, jR t • k ∈ K := fun t ht k hk =>
    fo24_triple_perm hT.fix hT.comm hT.char (hall t ht) hk
  have hsK : ∀ k ∈ K, s • k ∈ K := fun k hk => by
    have := hperm s rfl k hk
    rwa [CFSG.Sporadic.Fi24.jR_smul] at this
  by_cases hfix : ∃ k ∈ K, s • k = k
  · obtain ⟨k, hk, hks⟩ := hfix
    obtain ⟨e, he, hne⟩ := hF.p1 k hks
    obtain ⟨t, ht, hts, -⟩ := exists_noncomm_of_pair hks he hne
    have h1 := hperm t hts k hk
    rw [ht, cls_mul_cls_smul hne] at h1
    exact hne (hT.comm e h1 k (hT.fix k hk)).symm
  · push Not at hfix
    obtain ⟨k₁, k₂, k₃, hK⟩ := hT.three
    have hk : k₁ ∈ K := by rw [hK]; simp
    have hsk := hsK k₁ hk
    have hssk := hsK _ hsk
    have hc : cls k₁ * cls (s • k₁) = cls (s • k₁) * cls k₁ :=
      hT.comm k₁ hk _ (hT.fix _ hsk)
    obtain ⟨d, e, hd, he, o1, o2, o3⟩ := hF.gens k₁ (hfix k₁ hk) hc
    obtain ⟨t, ht, hts⟩ := exists_jR_cls_mul_cls hd he
    have h1 := hperm t hts k₁ hk
    rw [ht] at h1
    have hne1 : k₁ ≠ s • k₁ := fun e' => hfix k₁ hk e'.symm
    have hne2 : s • k₁ ≠ s • (s • k₁) := fun e' => hfix _ hsk e'.symm
    have hne3 : k₁ ≠ s • (s • k₁) := by
      intro e'
      apply hfix k₁ hk
      have h3 : s ^ 3 = 1 := hF.pow3
      calc s • k₁ = s • (s • (s • k₁)) := by rw [← e']
        _ = (s ^ 3) • k₁ := by rw [pow_three, mul_smul, mul_smul]
        _ = k₁ := by rw [h3, one_smul]
    rw [hK] at hk hsk hssk h1
    rcases mem_of_three hk hsk hssk hne1 hne3 hne2 h1 with h | h | h
    · exact o1 h
    · exact o2 h
    · exact o3 h

end Outer

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three
