module

public import Certificates.Data.Kernel.AS91I43
public import CFSG.Certificates.Kernel.AS91S42Sound
import CFSG.Certificates.Kernel.AS91I43Sel7

public section

namespace Certificates.Kernel.AS91I43

open CFSG.KC.Mat12P CFSG.KC.Mat8P Certificates.Kernel.HJ12K Certificates.Kernel.AS91S42
open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA
open CFSG.GF2Type.Smith1979.IdxFour CFSG.GF2Type.Smith1979.IdxFour.Orb CFSG.Quasithin.H13.AS91.Two

theorem orbitListO_eq {gs : List (Array ℕ)} {fs : List (ℕ → ℕ)} (hfs : gs.map appN = fs)
    (v : ℕ) : orbitList gs v = closO fs 4096 [v] (Nat.shiftLeft 1 v) [] := by
  rw [orbitList, hfs, ← native_bfsClosure]
  refine bfsClosure_O _ 4096 [v] [] _ _ fun k => ?_
  rw [Std.HashSet.contains_insert, Std.HashSet.contains_empty, Bool.or_false]
  change _ = (1 <<< v).testBit k
  rw [Nat.one_shiftLeft, Nat.testBit_two_pow]
  by_cases h : v = k <;> simp [h]

theorem fold_stepO (S : List ℕ) : ∀ (L l : List ℕ) (m : ℕ),
    (∀ k, m.testBit k = true ↔ k ∈ l ∨ k ∈ S) →
    (∀ k, (L.foldl stepO (l, m)).2.testBit k = true ↔ k ∈ (L.foldl stepO (l, m)).1 ∨ k ∈ S) ∧
    (∀ t ∈ L, (L.foldl stepO (l, m)).2.testBit t = true) ∧
    (∀ k, m.testBit k = true → (L.foldl stepO (l, m)).2.testBit k = true)
  | [], _, _, h => ⟨h, by simp, fun _ hk => hk⟩
  | t :: L, l, m, h => by
    rw [List.foldl_cons]
    cases hb : bitQ m t
    · have e : stepO (l, m) t = (t :: l, Nat.lor m (Nat.shiftLeft 1 t)) := by
        simp only [stepO, hb, Bool.false_eq_true, if_false]
      rw [e]
      have h' : ∀ k, (Nat.lor m (Nat.shiftLeft 1 t)).testBit k = true ↔ k ∈ t :: l ∨ k ∈ S := by
        intro k
        rw [testBit_ins, Bool.or_eq_true, beq_iff_eq, h k, List.mem_cons]
        constructor
        · rintro (e | e | e)
          · exact Or.inl (Or.inl e.symm)
          · exact Or.inl (Or.inr e)
          · exact Or.inr e
        · rintro ((e | e) | e)
          · exact Or.inl e.symm
          · exact Or.inr (Or.inl e)
          · exact Or.inr (Or.inr e)
      obtain ⟨A, B, C⟩ := fold_stepO S L _ _ h'
      refine ⟨A, ?_, fun k hk => C k ?_⟩
      · intro x hx
        rcases List.mem_cons.1 hx with e | hx
        · subst e
          exact C _ (by rw [testBit_ins]; simp)
        · exact B x hx
      · rw [testBit_ins, hk, Bool.or_true]
    · have e : stepO (l, m) t = (l, m) := by simp only [stepO, hb, if_true]
      rw [e]
      obtain ⟨A, B, C⟩ := fold_stepO S L l m h
      refine ⟨A, ?_, C⟩
      intro x hx
      rcases List.mem_cons.1 hx with e | hx
      · subst e
        exact C _ (by rw [← bitQ_eq]; exact hb)
      · exact B x hx

theorem closed_foldl {fs : List (ℕ → ℕ)} {S : List ℕ} (hS : ∀ y ∈ S, ∀ f ∈ fs, f y ∈ S) :
    ∀ (l : List (ℕ → ℕ)), (∀ f ∈ l, f ∈ fs) → ∀ x ∈ S, l.foldl (fun y f => f y) x ∈ S
  | [], _, _, hx => hx
  | f :: l, hl, x, hx => by
    rw [List.foldl_cons]
    exact closed_foldl hS l (fun g hg => hl g (List.mem_cons_of_mem f hg)) _
      (hS x hx f (hl f List.mem_cons_self))

theorem closO_reach (fs : List (ℕ → ℕ)) : ∀ (fuel : ℕ) (fr : List ℕ) (m : ℕ) (vis : List ℕ),
    (∀ k, m.testBit k = true ↔ k ∈ fr ++ vis) → (∀ x ∈ vis, ∀ f ∈ fs, f x ∈ fr ++ vis) →
    ∀ x ∈ fr ++ vis, ∀ l : List (ℕ → ℕ), (∀ f ∈ l, f ∈ fs) → l.length ≤ fuel →
      l.foldl (fun y f => f y) x ∈ closO fs fuel fr m vis
  | 0, fr, m, vis, _, _, x, hx, l, _, hl => by
    rw [List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hl), closO]
    exact hx
  | fuel + 1, fr, m, vis, hI, hC, x, hx, l, hlf, hl => by
    have hR : roundO fs fr m = (fr.flatMap fun s => fs.map fun f => f s).foldl stepO ([], m) :=
      rfl
    obtain ⟨hJ, hT, -⟩ := fold_stepO (fr ++ vis) (fr.flatMap fun s => fs.map fun f => f s) [] m
      (fun k => by rw [hI k]; simp)
    rw [← hR] at hJ hT
    have himg : ∀ y ∈ fr ++ vis, ∀ f ∈ fs, f y ∈ (roundO fs fr m).1 ++ (fr ++ vis) := by
      intro y hy f hf
      rcases List.mem_append.1 hy with hy | hy
      · have hb := hT (f y) (List.mem_flatMap.2 ⟨y, hy, List.mem_map.2 ⟨f, hf, rfl⟩⟩)
        exact List.mem_append.2 ((hJ _).1 hb)
      · exact List.mem_append_right _ (hC y hy f hf)
    have hI' : ∀ k, (roundO fs fr m).2.testBit k = true ↔ k ∈ (roundO fs fr m).1 ++ (fr ++ vis) :=
      fun k => by simp only [hJ k, List.mem_append]
    rw [closO]
    split_ifs with he
    · have hcl : ∀ y ∈ fr ++ vis, ∀ f ∈ fs, f y ∈ fr ++ vis := by
        intro y hy f hf
        have h1 := himg y hy f hf
        rwa [List.isEmpty_iff.1 he, List.nil_append] at h1
      exact closed_foldl hcl l hlf x hx
    · cases l with
      | nil =>
        exact closO_reach fs fuel _ _ _ hI' himg x (List.mem_append_right _ hx) [] (by simp)
          (Nat.zero_le _)
      | cons f l' =>
        rw [List.foldl_cons]
        exact closO_reach fs fuel _ _ _ hI' himg (f x) (himg x hx f (hlf f List.mem_cons_self)) l'
          (fun g hg => hlf g (List.mem_cons_of_mem f hg)) (by simpa using hl)

theorem imgs_mem (fs fs3 : List (ℕ → ℕ)) (h3 : ∀ f ∈ fs3, f ∈ fs) (w x : ℕ)
    (hx : x ∈ imgs fs fs3 w) : x ∈ closO fs 4096 [w] (Nat.shiftLeft 1 w) [] := by
  have hI : ∀ k, (Nat.shiftLeft 1 w).testBit k = true ↔ k ∈ [w] ++ [] := by
    intro k
    change (1 <<< w).testBit k = true ↔ _
    rw [Nat.one_shiftLeft, Nat.testBit_two_pow]
    simp [eq_comm]
  have hw : w ∈ [w] ++ [] := by simp
  have go := closO_reach fs 4096 [w] _ [] hI (by simp) w hw
  simp only [imgs, imgsY, List.mem_cons, List.mem_append, List.mem_map, List.mem_flatMap] at hx
  rcases hx with (rfl | ⟨f, hf, rfl⟩) | ⟨g, hg, _, ⟨f, hf, rfl⟩, rfl⟩
  · exact go [] (by simp) (by simp)
  · exact go [f] (by simpa using hf) (by simp)
  · exact go [f, g] (by simp [hf, h3 g hg]) (by simp)

theorem sel7_sound (L T : List ℕ) (hT : ∀ t ∈ T, t ∈ L) (h : rk7 T = true) :
    ((sel7 L).size == 7 && (sel7 L).all (fun v => L.contains v) &&
      decide (((List.range 128).map (appN (sel7 L))).Nodup)) = true := by
  obtain ⟨⟨-, -, hindT, hmemT⟩, -, -, -⟩ :=
    s7fold insD s7insD T T ([], []) (s7Inv_nil T) (by simp) (fun x hx => hx)
  have h7T : (T.foldl (s7G insD) ([], [])).2.length = 7 := by
    rw [rk7, selT, s7selStep, Nat.beq_eq] at h
    exact h
  obtain ⟨⟨-, -, hindL, hmemL⟩, hlL, hcov, -⟩ :=
    s7fold s7mI s7mI_ok L L ([], []) (s7Inv_nil L) (by simp) (fun x hx => hx)
  generalize T.foldl (s7G insD) ([], []) = sT at hindT hmemT h7T
  rw [s7sel7]
  generalize L.foldl (s7G s7mI) ([], []) = sL at hindL hmemL hlL hcov
  have h7L : sL.2.length = 7 := by
    by_contra hne
    have hcov' : ∀ x ∈ L, s7spn sL.2 x := fun x hx => (hcov x hx).resolve_left (by omega)
    have := s7pigeon hindT (by rw [List.length_reverse, h7T])
      (fun q hq => hcov' q (hT q (hmemT q (List.mem_reverse.1 hq))))
    omega
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, hP⟩ := s7len7 h7L
  rw [hP] at hindL hmemL
  rw [hP, s7appN]
  have hsz : ([p0, p1, p2, p3, p4, p5, p6].toArray.size == 7) = true := rfl
  have hall : [p0, p1, p2, p3, p4, p5, p6].toArray.all (fun v => L.contains v) = true :=
    Array.all_eq_true'.2 fun v hv => List.contains_iff_mem.2 (hmemL v (List.mem_toArray.1 hv))
  have hnd : decide (s7E [p6, p5, p4, p3, p2, p1, p0]).Nodup = true :=
    decide_eq_true (s7E_nodup _ (by simpa using hindL))
  rw [hsz, hall, hnd]
  rfl

theorem iWit_of {gs : List (Array ℕ)} {fs fs3 : List (ℕ → ℕ)} (hfs : gs.map appN = fs)
    (h3 : ∀ f ∈ fs3, f ∈ fs) (w : ℕ) (h : (bitQ (maskOf 0 iList) w || rk7 (imgs fs fs3 w)) = true) :
    iWitOK1 gs w = true := by
  rw [iWitOK1, Bool.or_eq_true]
  rw [Bool.or_eq_true] at h
  rcases h with h | h
  · left
    rw [inIb, contains_bitQ]
    exact h
  · right
    refine sel7_sound (orbitList gs w) (imgs fs fs3 w) (fun v hv => ?_) h
    rw [orbitListO_eq hfs]
    exact imgs_mem fs fs3 h3 w v hv

theorem fs_eq : (stab1Gens ()).map appN = fsQ := by
  rw [stab1Gens_eq, fsQ, List.map_map]
  refine List.map_congr_left fun X _ => ?_
  funext n
  exact appN_uA X n

theorem iCountOK_of (h : cnt43 = true) : iCountOK () = true := by
  rw [cnt43, cntQ] at h
  rw [iCountOK]
  have e : (List.range 4096).filter inIb = bitsM (maskOf 0 iList) := by
    rw [bitsM]
    exact List.filter_congr fun n _ => by rw [inIb, contains_bitQ, bitQ_eq]
  rw [e, bitsM_length, nat_beq]
  exact h

theorem wit43_of {a : ℕ} (h : wit43 a = true) {i : ℕ} (hi : i < 512) :
    (bitQ (maskOf 0 iList) (a + i) || rk7 (imgs fsQ fs3Q (a + i))) = true := by
  rw [wit43, witC, List.all_eq_true] at h
  exact h i (List.mem_range.2 hi)

theorem iWitOK_of (h0 : wit43 0 = true) (h1 : wit43 512 = true) (h2 : wit43 1024 = true)
    (h3 : wit43 1536 = true) (h4 : wit43 2048 = true) (h5 : wit43 2560 = true)
    (h6 : wit43 3072 = true) (h7 : wit43 3584 = true) : iWitOK () = true := by
  have hs : ∀ f ∈ fs3Q, f ∈ fsQ := fun f hf => List.mem_of_mem_take hf
  rw [iWitOK]
  refine List.all_eq_true.2 fun w hw => iWit_of fs_eq hs w ?_
  have hw' := List.mem_range.1 hw
  have e : w = 512 * (w / 512) + w % 512 := (Nat.div_add_mod w 512).symm
  have hi : w % 512 < 512 := Nat.mod_lt _ (by norm_num)
  have hq : w / 512 < 8 := by omega
  rw [e]
  generalize w / 512 = q at hq ⊢
  generalize w % 512 = i at hi ⊢
  interval_cases q
  · simpa using wit43_of h0 hi
  · simpa using wit43_of h1 hi
  · simpa using wit43_of h2 hi
  · simpa using wit43_of h3 hi
  · simpa using wit43_of h4 hi
  · simpa using wit43_of h5 hi
  · simpa using wit43_of h6 hi
  · simpa using wit43_of h7 hi

theorem tInv_eq : wordRows nGensI tInvWord = unpackA (wordP nQ tInvWord) := by
  rw [nGensI_eq]
  exact wordRows_uA nQ tInvWord (by decide)

theorem iInterOK_of (h : inter43 = true) : iInterOK () = true := by
  rw [inter43, interQ] at h
  rw [iInterOK, tInv_eq]
  have e : (fun y => (inIb y && inIb (appN (unpackA (wordP nQ tInvWord)) y)) == inZb y) =
      fun y => (bitQ (maskOf 0 iList) y &&
        bitQ (maskOf 0 iList) (mvNR (unpackQ (wordP nQ tInvWord)) y)) == bitQ (maskOf 0 zList) y :=
    funext fun y => by rw [inIb, inIb, inZb, contains_bitQ, contains_bitQ, contains_bitQ, appN_uA]
  rw [e]
  exact h

theorem iOK43_of (hc : cnt43 = true) (h0 : wit43 0 = true) (h1 : wit43 512 = true)
    (h2 : wit43 1024 = true) (h3 : wit43 1536 = true) (h4 : wit43 2048 = true)
    (h5 : wit43 2560 = true) (h6 : wit43 3072 = true) (h7 : wit43 3584 = true)
    (hi : inter43 = true) : iOK43 () = true := by
  rw [iOK43, iCountOK_of hc, iWitOK_of h0 h1 h2 h3 h4 h5 h6 h7, iInterOK_of hi]
  rfl

end Certificates.Kernel.AS91I43
