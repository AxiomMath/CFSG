module

public import Certificates.Data.Kernel.Misc.YamakiA6
public import CFSG.Certificates.Kernel.Misc.YamakiCESound

public section

namespace CFSG.KC.YamakiA6

open CFSG.ClassicalInvolution.Solomon73.Yamaki CFSG.ClassicalInvolution.Sp62Rec CFSG.KD.YamakiCE
  CFSG.KD.YamakiA6 CFSG.KD.BfsK CFSG.KC.BfsEnum CFSG.KC.YamakiS0 CFSG.KC.YamakiCE
open CFSG.KD.Sp62 (MULF ONE)

theorem build_foldl {Q : Type} [Monoid Q] [Inhabited Q] (E : Enum) (hs : Array Q) :
    ∀ m : ℕ, (∀ i, 1 ≤ i → i ≤ m → E.parent[i]! < i) →
      let F := (List.range' 1 m).foldl (fun F i => F.push (F[E.parent[i]!]! * hs[E.gen[i]!]!))
        (#[1] : Array Q)
      F.size = m + 1 ∧ F[0]! = 1 ∧
        ∀ i, 1 ≤ i → i ≤ m → F[i]! = F[E.parent[i]!]! * hs[E.gen[i]!]!
  | 0, _ => by
    refine ⟨rfl, rfl, fun i h1 h2 => by omega⟩
  | m + 1, hp => by
    intro F
    obtain ⟨s, z, r⟩ := build_foldl E hs m fun i h1 h2 => hp i h1 (by omega)
    have hF : F = ((List.range' 1 m).foldl (fun F i => F.push (F[E.parent[i]!]! * hs[E.gen[i]!]!))
        (#[1] : Array Q)).push
        ((((List.range' 1 m).foldl (fun F i => F.push (F[E.parent[i]!]! * hs[E.gen[i]!]!))
          (#[1] : Array Q)))[E.parent[m + 1]!]! * hs[E.gen[m + 1]!]!) := by
      simp only [F, List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [Nat.one_mul, Nat.add_comm 1 m]
    generalize ((List.range' 1 m).foldl (fun F i => F.push (F[E.parent[i]!]! * hs[E.gen[i]!]!))
      (#[1] : Array Q)) = G at hF s z r
    rw [hF]
    have hpm := hp (m + 1) (by omega) le_rfl
    refine ⟨by simp [s], by rw [push_lt (by omega), z], fun i h1 h2 => ?_⟩
    rcases Nat.lt_or_eq_of_le h2 with h | h
    · have hpi := hp i h1 (by omega)
      have hi1 : i < G.size := by omega
      have hi2 : E.parent[i]! < G.size := by omega
      rw [push_lt hi1, push_lt hi2, r i h1 (by omega)]
    · subst h
      have hi2 : E.parent[m + 1]! < G.size := by omega
      have e : (G.push (G[E.parent[m + 1]!]! * hs[E.gen[m + 1]!]!))[m + 1]! =
          G[E.parent[m + 1]!]! * hs[E.gen[m + 1]!]! := by
        rw [← s]
        exact push_eq
      rw [e, push_lt hi2]

theorem buildHomTable_spec {Q : Type} [Monoid Q] [Inhabited Q] (E : Enum) (hs : Array Q) {n : ℕ}
    (hn : E.elems.size = n + 1) (hp : ∀ i, 1 ≤ i → i ≤ n → E.parent[i]! < i) :
    (buildHomTable E hs).size = n + 1 ∧ (buildHomTable E hs)[0]! = 1 ∧
      ∀ i, 1 ≤ i → i ≤ n →
        (buildHomTable E hs)[i]! = (buildHomTable E hs)[E.parent[i]!]! * hs[E.gen[i]!]! := by
  have e : buildHomTable E hs = (List.range' 1 n).foldl
      (fun F i => F.push (F[E.parent[i]!]! * hs[E.gen[i]!]!)) (#[1] : Array Q) := by
    unfold buildHomTable
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, hn,
      Nat.add_sub_cancel, Nat.div_one, bind_pure]
    exact forIn_foldl _ _ _ _ fun j b => rfl
  rw [e]
  exact build_foldl E hs n hp

@[expose] def permL (p : Equiv.Perm (Fin 6)) : List ℕ :=
  [(p 0).val, (p 1).val, (p 2).val, (p 3).val, (p 4).val, (p 5).val]

theorem permL_get (p : Equiv.Perm (Fin 6)) (k : Fin 6) : (permL p).getD k.val 0 = (p k).val := by
  fin_cases k <;> rfl

theorem permL_mul (p q : Equiv.Perm (Fin 6)) : permL (p * q) = compL (permL p) (permL q) := by
  unfold compL
  change permL (p * q) = [(permL p).getD (q 0).val 0, (permL p).getD (q 1).val 0,
    (permL p).getD (q 2).val 0, (permL p).getD (q 3).val 0, (permL p).getD (q 4).val 0,
    (permL p).getD (q 5).val 0]
  rw [permL_get, permL_get, permL_get, permL_get, permL_get, permL_get]
  rfl

theorem permL_inj {p q : Equiv.Perm (Fin 6)} (h : permL p = permL q) : p = q := by
  unfold permL at h
  simp only [List.cons.injEq, and_true] at h
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := h
  ext k
  fin_cases k
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5

theorem permL_one : permL 1 = [0, 1, 2, 3, 4, 5] := rfl

theorem permL_imgs {j : ℕ} (hj : j < 2) : permL a6Imgs[j]! = sigL j := by
  rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
  · rfl
  · rfl

theorem memK_of_isSome {R PA PB : ℕ → ℕ} {o n : ℕ} {E : Enum}
    (hE : BInvE (fun t => arrN (recX R o t)) PA PB n E) (hlt : ∀ t < n, recX R o t < 2 ^ 36)
    {x : ℕ} (hx : x < 2 ^ 36) (h : (E.lookup (arrN x)).isSome = true) : memK R o n x = true := by
  obtain ⟨e1, -, -, e4, -⟩ := hE
  unfold Enum.lookup at h
  split at h
  · split at h
    · rename_i hc
      obtain ⟨hk1, hk2⟩ := hc
      rw [e1] at hk1
      rw [e4 _ hk1] at hk2
      have he := arrN_inj (hlt _ hk1) hx hk2
      unfold memK
      exact List.any_eq_true.2 ⟨_, List.mem_range.2 hk1, Nat.beq_eq.mpr he⟩
    · simp at h
  · simp at h

theorem a6Check_of {RE RP RV PAV PBV : ℕ → ℕ}
    (hE : BInvE (fun t => arrN (recX RE 14 t)) (recF RE 14 0) (recF RE 14 1) 11520 (enumE ()))
    (hB : ∀ i < 11520 - 1, recF RE 14 0 i ≤ i ∧ recF RE 14 1 i < 2)
    (hlt : ∀ t < 11520, recX RE 14 t < 2 ^ 36)
    (hstep : ∀ i < 11520 * 2, recPOS RE 14 2 i < 11520 ∧
      recX RE 14 (recPOS RE 14 2 i) = MULF (recX RE 14 (i / 2)) (RE (12 + i % 2)))
    (hg : ∀ j < 2, (gE ())[j]! = arrN (RE (12 + j)))
    (hV : BInvE (fun t => arrN (recX RV 17 t)) PAV PBV 32 (enumV0 ()))
    (hVlt : ∀ t < 32, recX RV 17 t < 2 ^ 36)
    (hc : ∀ q < 23, a6Chunk RE RP RV 11520 512 q = true) : a6Check () = true := by
  have hE' := hE
  obtain ⟨e1, -, -, e4, e5, -, -⟩ := hE'
  have hat : ∀ t < 11520, a6At RE RP RV t = true := by
    intro t ht
    have hq : t / 512 < 23 := by omega
    have hcq := hc _ hq
    unfold a6Chunk at hcq
    have hlo : Nat.mul 512 (t / 512) ≤ t := Nat.mul_div_le t 512
    have hhi : t < Nat.mul 512 (t / 512) + 512 := by
      change t < 512 * (t / 512) + 512
      omega
    have e := (CFSG.KC.Misc.Clos.allR_iff _ _ _).1 hcq t hlo hhi
    rw [Nat.blt_eq.mpr ht, cond_true] at e
    exact e
  have hpar : ∀ i, 1 ≤ i → i ≤ 11519 → (enumE ()).parent[i]! < i := by
    intro i h1 h2
    rw [(e5 i (by omega) (by omega)).1]
    have := (hB (i - 1) (by omega)).1
    omega
  obtain ⟨fs, f0, fr⟩ := buildHomTable_spec (enumE ()) a6Imgs (n := 11519) (by rw [e1]) hpar
  have hF : ∀ t < 11520, permL (a6Table ())[t]! = decL (RP t) := by
    intro t
    induction t using Nat.strong_induction_on with
    | _ t ih =>
      intro ht
      have e := hat t ht
      unfold a6At at e
      rw [CFSG.KC.YamakiRepF.strictY_eq] at e
      simp only [Bool.and_eq_true] at e
      obtain ⟨⟨⟨e0, -⟩, -⟩, -⟩ := e
      cases t with
      | zero =>
        have hz : Nat.beq 0 0 = true := rfl
        rw [hz, cond_true, decide_eq_true_eq] at e0
        rw [e0]
        unfold a6Table
        rw [f0, permL_one]
      | succ t =>
        have hz : Nat.beq (t + 1) 0 = false := rfl
        rw [hz, cond_false, decide_eq_true_eq, Nat.pred_succ] at e0
        rw [e0]
        unfold a6Table
        obtain ⟨p1, p2⟩ := e5 (t + 1) ht (by omega)
        obtain ⟨b1, b2⟩ := hB t (by omega)
        rw [fr (t + 1) (by omega) (by omega), permL_mul, p1, p2, Nat.add_sub_cancel,
          permL_imgs b2]
        rw [← ih _ (by omega) (by omega)]
        rfl
  have hstep' : ∀ i < 11520, ∀ j < 2, (enumE ()).lookup (compA (enumE ()).elems[i]! (gE ())[j]!) =
      some (recPOS RE 14 2 (i * 2 + j)) := by
    intro i hi j hj
    obtain ⟨s1, s2⟩ := hstep (i * 2 + j) (by omega)
    have hd : (i * 2 + j) / 2 = i := by omega
    have hm : (i * 2 + j) % 2 = j := by omega
    rw [hd, hm] at s2
    rw [e4 i hi, hg j hj, arrN_mul, ← s2]
    exact lookup_of_inv hE s1
  unfold a6Check
  simp only [Bool.and_eq_true, allLt_iff]
  refine ⟨⟨⟨?_, ?_⟩, by decide⟩, by decide⟩
  · unfold homOK
    simp only [Bool.and_eq_true, decide_eq_true_eq, allLt_iff]
    refine ⟨⟨by unfold a6Table; rw [fs, e1], by unfold a6Table; exact f0⟩, fun i hi j hj => ?_⟩
    rw [e1] at hi
    have hj2 : j < 2 := by
      have : (gE ()).size = 2 := by simp [gE, wordsA, e0Words]
      omega
    rw [hstep' i hi j hj2]
    simp only [decide_eq_true_eq]
    apply permL_inj
    have e := hat i hi
    unfold a6At at e
    rw [CFSG.KC.YamakiRepF.strictY_eq] at e
    simp only [Bool.and_eq_true, decide_eq_true_eq] at e
    obtain ⟨⟨⟨-, ea⟩, eb⟩, -⟩ := e
    obtain ⟨s1, -⟩ := hstep (i * 2 + j) (by omega)
    rw [hF _ s1, permL_mul, hF i hi, permL_imgs hj2]
    rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
    · exact ea
    · exact eb
  · intro i hi
    rw [e1] at hi
    have e := hat i hi
    unfold a6At at e
    rw [CFSG.KC.YamakiRepF.strictY_eq] at e
    simp only [Bool.and_eq_true] at e
    obtain ⟨-, ec⟩ := e
    have hone : decide ((a6Table ())[i]! = 1) = decide (decL (RP i) = [0, 1, 2, 3, 4, 5]) := by
      apply Bool.eq_iff_iff.2
      rw [decide_eq_true_eq, decide_eq_true_eq, ← hF i hi, ← permL_one]
      exact ⟨fun h => by rw [h], permL_inj⟩
    have hmem : ((enumV0 ()).lookup (enumE ()).elems[i]!).isSome = memK RV 17 32 (recX RE 14 i) := by
      rw [e4 i hi]
      apply Bool.eq_iff_iff.2
      exact ⟨memK_of_isSome hV hVlt (hlt i hi), fun h => isSome_of_rec hV (memK_sound h)⟩
    rw [hone, hmem]
    exact ec

end CFSG.KC.YamakiA6

end
