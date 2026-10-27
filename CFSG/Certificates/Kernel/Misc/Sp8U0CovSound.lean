module

public import Certificates.Data.Kernel.Misc.Sp8U0Cov
public import CFSG.Certificates.Kernel.Misc.Sp8U0Sound
public import CFSG.Certificates.Kernel.Misc.HashFoldSound

public section

namespace CFSG.KC.Sp8U0

open CFSG.KD.Sp8U0 CFSG.KD.BfsK CFSG.KC.BfsK CFSG.KC.Mat8P CFSG.KC.Sp8Syl3 CFSG.KD.Sp8Syl3
  CFSG.KC.Sp8Cz CFSG.Quasithin.H13.Mat8Cert CFSG.Quasithin.G2U
  CFSG.RankThree.PartTwo.Sec21.FF81.Sp8

theorem foldl_nested (O : Array (Array (List ℕ))) (ks : List ℕ) (m : Std.HashMap (List ℕ) ℕ) :
    ks.foldl (fun m k => (O.getD k #[]).foldl (fun m y => m.insert y k) m) m =
      (ks.flatMap fun k => (O.getD k #[]).toList.map fun y => (y, k)).foldl
        (fun m p => m.insert p.1 p.2) m := by
  induction ks generalizing m with
  | nil => rfl
  | cons a ks ih =>
    rw [List.foldl_cons, ih, List.flatMap_cons, List.foldl_append, List.foldl_map]
    congr 1
    rw [← Array.foldl_toList]

theorem get?_nested {O : Array (Array (List ℕ))} {x : List ℕ} {k : ℕ} (hk : k < O.size)
    (hx : x ∈ O.getD k #[]) :
    ∃ k', ((List.range O.size).foldl (fun m k => (O.getD k #[]).foldl (fun m y => m.insert y k) m)
      (∅ : Std.HashMap (List ℕ) ℕ)).get? x = some k' ∧ k' < O.size ∧ x ∈ O.getD k' #[] := by
  rw [foldl_nested]
  have hmem : (x, k) ∈ (List.range O.size).flatMap fun k =>
      (O.getD k #[]).toList.map fun y => (y, k) :=
    List.mem_flatMap.2 ⟨k, List.mem_range.2 hk, List.mem_map.2 ⟨x, Array.mem_toList_iff.2 hx, rfl⟩⟩
  cases hg : ((((List.range O.size).flatMap fun k =>
      (O.getD k #[]).toList.map fun y => (y, k)).foldl (fun m p => m.insert p.1 p.2)
      (∅ : Std.HashMap (List ℕ) ℕ)).get? x) with
  | none =>
    exact absurd rfl
      ((CFSG.KC.HashFold.get?_foldl_insert_eq_none (f := Prod.fst) (g := Prod.snd)).1 hg _ hmem)
  | some k' =>
    obtain ⟨p, hp, h1, h2⟩ :=
      CFSG.KC.HashFold.get?_foldl_insert_eq_some (f := Prod.fst) (g := Prod.snd) hg
    obtain ⟨k'', hk'', hp'⟩ := List.mem_flatMap.1 hp
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hp'
    simp only at h1 h2
    subst h1 h2
    exact ⟨k'', rfl, List.mem_range.1 hk'', Array.mem_toList_iff.1 hy⟩

variable {Q : ℕ → ℕ}

theorem gp_enc (hp : ∀ s < 5, EncS ((gpS.getD s []).take 8) (Q (2 * s)) ∧
    EncS ((gpS.getD s []).drop 8) (Q (2 * s + 1))) {s : ℕ} (hs : s < 5) (d : List ℕ) :
    EncS ((gpS.getD s d).take 8) (Q (2 * s)) ∧ EncS ((gpS.getD s d).drop 8) (Q (2 * s + 1)) := by
  have hl : gpS.length = 5 := rfl
  rw [CFSG.KC.G2Three.listGetD_irrel (by rw [hl]; exact hs) d []]
  exact hp s hs

theorem orb_facts (hp : ∀ s < 5, EncS ((gpS.getD s []).take 8) (Q (2 * s)) ∧
    EncS ((gpS.getD s []).drop 8) (Q (2 * s + 1))) {k o n : ℕ}
    (h0 : EncS (repS.getD k []) (recX Q o 0)) (h : orbAt Q k o n = true) :
    (orbS (repS.getD k []) gpS 256).size = n ∧
      ∀ j < n, EncS ((orbS (repS.getD k []) gpS 256).getD j []) (recX Q o j) := by
  unfold orbAt at h
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at h
  obtain ⟨⟨hn0, hn⟩, h⟩ := h
  obtain ⟨-, hsz, -, -, hrec⟩ := tableKk_ok (ok := validS) (num := code64) code_inj
    (start := repS.getD k []) (mul := conjStepS) (gens := gpS) (fuel := 256) (k := 5) rfl
    (by norm_num) hn0 (by omega)
    (fun x N hx s hs d => by
      obtain ⟨h1, h2⟩ := gp_enc hp hs d
      exact mulE (mulE h1 hx) h2)
    h0 h (by omega) (by omega) (by omega)
  exact ⟨hsz, hrec⟩

theorem getD_map_toArray {L : List (List ℕ)} {f : List ℕ → Array (List ℕ)} {k : ℕ}
    (hk : k < L.length) : (L.map f).toArray.getD k #[] = f (L.getD k []) := by
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map,
    List.getElem?_eq_getElem hk, List.getD_eq_getElem _ _ hk]
  rfl

theorem repS_length : repS.length = 133 := by decide +kernel

theorem getD_orbs {k : ℕ} (hk : k < 133) :
    (repS.map fun r => orbS r gpS 256).toArray.getD k #[] = orbS (repS.getD k []) gpS 256 :=
  getD_map_toArray (by rw [repS_length]; exact hk)

theorem covChk_of {R : ℕ → ℕ} (hz : ∀ s < 5, EncS (u0Gens.getD s []) (R s))
    (hT : u0TabK R 65536 = true)
    (hp : ∀ s < 5, EncS ((gpS.getD s []).take 8) (Q (2 * s)) ∧
      EncS ((gpS.getD s []).drop 8) (Q (2 * s + 1)))
    (h0 : ∀ k < 133, EncS (repS.getD k []) (recX Q (oK Q k) 0))
    (hpair : gpS.all (fun gg => mulS (gg.take 8) (gg.drop 8) == one8) = true)
    (hO : orbK Q = true) (hC : covK R Q = true) : covChk899106 = true := by
  obtain ⟨hsz, -, -, hrec⟩ := u0Tab_facts hz hT
  have horb := CFSG.KC.G2Three.allBelow_g2 hO (by norm_num)
  have hcov := CFSG.KC.G2Three.allBelow_g2 hC (by norm_num)
  have hsize : (repS.map fun r => orbS r gpS 256).toArray.size = 133 := by
    rw [List.size_toArray, List.length_map, repS_length]
  unfold covChk899106
  dsimp only
  rw [hpair, Bool.true_and]
  refine CFSG.KC.G2Three.allCheck_of fun t ht => ?_
  rw [hsz] at ht
  have hx := hrec t ht
  have e := hcov t ht
  generalize (tabS u0Gens 65536).getD t [] = x at hx ⊢
  generalize Q (Nat.add 4248 t) = w at e
  generalize recX R 9 t = X at hx e
  rw [beqE (mulE hx hx) one_enc, beqE hx one_enc]
  unfold covAt at e
  cases h2 : Nat.beq (mulP X X) oneP
  · rfl
  cases h1 : Nat.beq X oneP
  · rw [h2, h1] at e
    simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, Nat.blt_eq] at e
    obtain ⟨⟨hk, hj⟩, hX⟩ := e
    generalize Nat.shiftRight w 8 = k at hk hj hX
    generalize Nat.land w 255 = j at hj hX
    obtain ⟨osz, orec⟩ := orb_facts hp (h0 k hk) (horb k hk)
    have hxj : x = (orbS (repS.getD k []) gpS 256).getD j [] := by
      have hy := orec j hj
      rw [Nat.beq_eq] at hX
      rw [hX] at hy
      exact code_inj _ _ hx.1 hy.1 (hx.2.trans hy.2.symm)
    have hmem : x ∈ (repS.map fun r => orbS r gpS 256).toArray.getD k #[] := by
      rw [getD_orbs hk, hxj]
      exact getD_mem (by rw [osz]; exact hj)
    obtain ⟨k', hk', hk'lt, hmem'⟩ := get?_nested (by rw [hsize]; exact hk) hmem
    rw [hk']
    rw [hsize] at hk'lt
    simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨hk'lt, ?_⟩
    have hOM : (Array.map indexMap (repS.map fun r => orbS r gpS 256).toArray).getD k' {} =
        indexMap ((repS.map fun r => orbS r gpS 256).toArray.getD k' #[]) := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getD_eq_getD_getElem?,
        Array.getElem?_eq_getElem (by rw [hsize]; exact hk'lt)]
      rfl
    rw [hOM]
    exact CFSG.KC.HashFold.found_indexMap_iff_mem.2 hmem'
  · simp

end CFSG.KC.Sp8U0

end
