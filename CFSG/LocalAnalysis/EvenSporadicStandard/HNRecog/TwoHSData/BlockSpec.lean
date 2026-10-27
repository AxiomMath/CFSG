module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.BlockCheck
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.BlockHomList
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.CheckSpec

public section

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

@[expose] def blkF (k : ℕ) (b : Array ℕ) (p : Fin 1408) : Option (Fin k) :=
  if h : b[p.val]! < k then some ⟨b[p.val]!, h⟩ else none

private theorem ap_eq_val {T : Table} {g : Equiv.Perm (Fin 1408)} (hT : Rep 1408 T g)
    (p : Fin 1408) : ap T p.val = (g p).val := by
  rw [hT p.val p.2, idx_of_lt g p.2, Equiv.Perm.smul_def]

theorem blkMapOK_spec {k : ℕ} {b : Array ℕ} {T L : Table} {g : Equiv.Perm (Fin 1408)}
    {π : Equiv.Perm (Fin k)} (hT : Rep 1408 T g) (hL : Rep k L π)
    (h : blkMapOK k b T L = true) (p : Fin 1408) :
    blkF k b (g p) = (blkF k b p).map π := by
  have hp := allIn_eq_true.1 h p.val (Nat.zero_le _) p.2
  rw [ap_eq_val hT p] at hp
  by_cases hbp : b[p.val]! < k
  · rw [if_pos hbp, beq_iff_eq] at hp
    have hLp : ap L b[p.val]! = (π ⟨b[p.val]!, hbp⟩).val := by
      rw [hL _ hbp, idx_of_lt π hbp, Equiv.Perm.smul_def]
    rw [hLp] at hp
    have hlt : b[(g p).val]! < k := by rw [hp]; exact (π ⟨b[p.val]!, hbp⟩).isLt
    simp only [blkF, dif_pos hbp, dif_pos hlt, Option.map_some]
    exact congrArg some (Fin.ext hp)
  · rw [if_neg hbp] at hp
    have hnl : ¬ b[(g p).val]! < k := by
      have := of_decide_eq_true hp
      omega
    simp only [blkF, dif_neg hbp, dif_neg hnl, Option.map_none]

theorem blkTrivOK_spec {k : ℕ} {b : Array ℕ} {T : Table} {g : Equiv.Perm (Fin 1408)}
    (hT : Rep 1408 T g) (h : blkTrivOK b T = true) (p : Fin 1408) :
    blkF k b (g p) = blkF k b p := by
  have hp := allIn_eq_true.1 h p.val (Nat.zero_le _) p.2
  rw [ap_eq_val hT p, beq_iff_eq] at hp
  simp only [blkF, hp]

private theorem b_eq_of_blkF_eq {k : ℕ} {b : Array ℕ} (hbk : ∀ p : Fin 1408, b[p.val]! ≤ k)
    {p q : Fin 1408} (h : blkF k b p = blkF k b q) : b[p.val]! = b[q.val]! := by
  have hp := hbk p
  have hq := hbk q
  by_cases hA : b[p.val]! < k <;> by_cases hB : b[q.val]! < k
  · simp only [blkF, dif_pos hA, dif_pos hB, Option.some.injEq, Fin.mk.injEq] at h
    exact h
  · simp only [blkF, dif_pos hA, dif_neg hB, reduceCtorEq] at h
  · simp only [blkF, dif_neg hA, dif_pos hB, reduceCtorEq] at h
  · omega

theorem blkTrivOK_of_fix {k : ℕ} {b : Array ℕ} (hbk : ∀ p : Fin 1408, b[p.val]! ≤ k) {T : Table}
    {g : Equiv.Perm (Fin 1408)} (hT : Rep 1408 T g) (h : ∀ p, blkF k b (g p) = blkF k b p) :
    blkTrivOK b T = true := by
  rw [blkTrivOK, allIn_eq_true]
  intro p _ hp
  have h1 := ap_eq_val hT ⟨p, hp⟩
  have h2 := b_eq_of_blkF_eq hbk (h ⟨p, hp⟩)
  change (b[ap T p]! == b[p]!) = true
  rw [beq_iff_eq]
  change ap T (⟨p, hp⟩ : Fin 1408).val = (g ⟨p, hp⟩).val at h1
  simp only [h1]
  exact h2

theorem blkSurjOK_spec {k : ℕ} {b : Array ℕ} (hb : b.size = 1408) (h : blkSurjOK k b = true) :
    ∀ j : Fin k, ∃ p : Fin 1408, blkF k b p = some j := by
  intro j
  rw [blkSurjOK, List.all_eq_true] at h
  have hj := h j.val (List.mem_range.2 j.2)
  rw [Array.any_eq_true'] at hj
  obtain ⟨x, hx, hxj⟩ := hj
  obtain ⟨i, hi, hix⟩ := Array.getElem_of_mem hx
  have hxj' : x = j.val := beq_iff_eq.1 hxj
  refine ⟨⟨i, by omega⟩, ?_⟩
  have hbi : b[i]! = j.val := by rw [getElem!_pos b i hi, hix, hxj']
  simp only [blkF]
  rw [dif_pos (by rw [hbi]; exact j.2)]
  exact congrArg some (Fin.ext hbi)

theorem mem_map_elemW_set (ws : List (List ℕ)) :
    {x | x ∈ ws.map elemW} = elemW '' {w | w ∈ ws} := by
  ext x
  simp only [Set.mem_setOf_eq, List.mem_map, Set.mem_image]

theorem genOf_eq_closure_map (n : ℕ) (gs : List Table) :
    genOf n gs = closure {x | x ∈ gs.map (tp n)} := by
  unfold genOf
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_setOf_eq, Array.mem_toArray, List.mem_map]

theorem blkData_spec {d : BlkData} (h : blkDataOK d = true) :
    ∃ φ : ↥(closure (elemW '' {w | w ∈ d.gens})) →* Equiv.Perm (Fin d.k),
      (∀ (x : ↥(closure (elemW '' {w | w ∈ d.gens}))) (p : Fin 1408),
        blkF d.k d.blk ((x : Equiv.Perm (Fin 1408)) p) = (blkF d.k d.blk p).map (φ x)) ∧
      φ.range = genOf d.k d.labs ∧
      (∀ x : ↥(closure (elemW '' {w | w ∈ d.gens})),
        φ x = 1 ↔
          ∀ p : Fin 1408, blkF d.k d.blk ((x : Equiv.Perm (Fin 1408)) p) = blkF d.k d.blk p) := by
  simp only [blkDataOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hg, hsz⟩, -⟩, hsurj⟩, hlen⟩, hw⟩, hp⟩, hmap⟩ := h
  have hF2 : List.Forall₂ (fun (g : Equiv.Perm (Fin 1408)) (π : Equiv.Perm (Fin d.k)) =>
      ∀ p, blkF d.k d.blk (g p) = (blkF d.k d.blk p).map π)
      (d.gens.map elemW) (d.labs.map (tp d.k)) := by
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_iff_zip]
    refine ⟨hlen, fun {w L} hmem => ?_⟩
    obtain ⟨hwm, hLm⟩ := List.of_mem_zip hmem
    have hwok : wordOK w = true := List.all_eq_true.1 hw w hwm
    have hLok : permOK d.k L = true := List.all_eq_true.1 hp L hLm
    exact fun q => blkMapOK_spec (rep_elemW_of_gensOK hg hwok) (rep_tp hLok)
      (List.all_eq_true.1 hmap (w, L) hmem) q
  have key := TwoHSData.exists_blockHom_list (d.gens.map elemW) (d.labs.map (tp d.k))
    (blkF d.k d.blk) (blkSurjOK_spec hsz hsurj) hF2
  rw [mem_map_elemW_set, ← genOf_eq_closure_map] at key
  obtain ⟨φ, hφ, hrange⟩ := key
  exact ⟨φ, hφ, hrange, fun x => TwoHSData.blockHom_eq_one_iff (blkF d.k d.blk)
    (blkSurjOK_spec hsz hsurj) φ hφ x⟩

theorem gensOK_of_blkDataOK {d : BlkData} (h : blkDataOK d = true) : gensOK = true := by
  simp only [blkDataOK, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1.1.1.1.1.1

theorem blkData_words_ok {d : BlkData} (h : blkDataOK d = true) : d.gens.all wordOK = true := by
  simp only [blkDataOK, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1.2

theorem blkData_labs_perm {d : BlkData} (h : blkDataOK d = true) :
    ∀ g ∈ d.labs, permOK d.k g = true := by
  simp only [blkDataOK, Bool.and_eq_true, beq_iff_eq] at h
  exact fun g hg => List.all_eq_true.1 h.1.2 g hg

theorem blkImage_spec {d : BlkData} {m : ℕ} (h : blkDataOK d = true) (hk : d.k < 2 ^ 32)
    (hi : blkImageOK d m = true) : Nat.card ↥(genOf d.k d.labs) = m :=
  (enumOK_spec hk (blkData_labs_perm h) hi).1

theorem blkData_blk_le {d : BlkData} (h : blkDataOK d = true) :
    ∀ p : Fin 1408, d.blk[p.val]! ≤ d.k := by
  simp only [blkDataOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hg, hsz⟩, hbk⟩, hsurj⟩, hlen⟩, hw⟩, hp⟩, hmap⟩ := h
  intro p
  have hlt : p.val < d.blk.size := by rw [hsz]; exact p.2
  have hmem : d.blk[p.val]! ∈ d.blk := by
    rw [getElem!_pos d.blk p.val hlt]
    exact Array.getElem_mem hlt
  exact of_decide_eq_true (Array.all_eq_true'.1 hbk _ hmem)

theorem blkTriv_closure_set {k : ℕ} {b : Array ℕ} {T : Set (Equiv.Perm (Fin 1408))}
    (h : ∀ t ∈ T, ∀ p : Fin 1408, blkF k b (t p) = blkF k b p) :
    ∀ x ∈ closure T, ∀ p : Fin 1408, blkF k b (x p) = blkF k b p := by
  let H : Subgroup (Equiv.Perm (Fin 1408)) :=
    { carrier := {x | ∀ p : Fin 1408, blkF k b (x p) = blkF k b p}
      one_mem' := fun p => rfl
      mul_mem' := fun {x y} hx hy p => by
        rw [Equiv.Perm.mul_apply, hx, hy]
      inv_mem' := fun {x} hx p => by
        have h1 := hx (x⁻¹ p)
        have e : x (x⁻¹ p) = p := by simp
        rw [e] at h1
        exact h1.symm }
  have hle : closure T ≤ H := by
    rw [closure_le]
    exact fun t ht => h t ht
  exact fun x hx => hle hx

theorem blkTriv_closure {k : ℕ} {b : Array ℕ} {ws : List (List ℕ)} (hg : gensOK = true)
    (hw : ws.all wordOK = true) (h : ws.all (fun w => blkTrivOK b (tabW w)) = true) :
    ∀ x ∈ closure (elemW '' {w | w ∈ ws}), ∀ p : Fin 1408, blkF k b (x p) = blkF k b p := by
  refine blkTriv_closure_set ?_
  rintro _ ⟨w, hwm, rfl⟩
  exact fun p => blkTrivOK_spec (rep_elemW_of_gensOK hg (List.all_eq_true.1 hw w hwm))
    (List.all_eq_true.1 h w hwm) p

theorem trivInjOK_iff {k : ℕ} {b : Array ℕ} (hbk : ∀ p : Fin 1408, b[p.val]! ≤ k) {L : Array Table}
    {S : Set (Equiv.Perm (Fin 1408))} (hL : IsEnumSet 1408 L S) :
    trivInjOK b (idT 1408) L = true ↔
      ∀ g ∈ S, (∀ p : Fin 1408, blkF k b (g p) = blkF k b p) → g = 1 := by
  refine hL.forall_iff _ (fun g => (∀ p : Fin 1408, blkF k b (g p) = blkF k b p) → g = 1) ?_
  intro x g hx
  have hid : tblEq 1408 x (idT 1408) = true ↔ g = 1 :=
    tblEq_iff_eq hx (Rep.idT (by norm_num))
  constructor
  · intro h hfix
    have htriv := blkTrivOK_of_fix hbk hx hfix
    simp only [Bool.or_eq_true, Bool.not_eq_true'] at h
    rcases h with h | h
    · rw [htriv] at h
      exact absurd h (by simp)
    · exact hid.1 h
  · intro H
    simp only [Bool.or_eq_true, Bool.not_eq_true']
    by_cases htriv : blkTrivOK b x = true
    · exact Or.inr (hid.2 (H (fun p => blkTrivOK_spec hx htriv p)))
    · exact Or.inl (by simpa using htriv)

theorem sqOneOK_iff {L : Array Table} {S : Set (Equiv.Perm (Fin 1408))} (hL : IsEnumSet 1408 L S) :
    sqOneOK (idT 1408) L = true ↔ ∀ g ∈ S, g * g = 1 := by
  refine hL.forall_iff _ (fun g => g * g = 1) ?_
  intro x g hx
  exact tblEq_iff_eq (Rep.compT hx hx) (Rep.idT (by norm_num))

theorem sqInOK_iff {L V : Array Table} {S T : Set (Equiv.Perm (Fin 1408))} (hL : IsEnumSet 1408 L S)
    (hV : IsEnumSet 1408 V T) : sqInOK L V = true ↔ ∀ g ∈ S, g * g ∈ T := by
  refine hL.forall_iff _ (fun g => g * g ∈ T) ?_
  intro x g hx
  exact hV.memT_iff (Rep.compT hx hx)

end CFSG.EvenSporadicStandard.HNRecog
