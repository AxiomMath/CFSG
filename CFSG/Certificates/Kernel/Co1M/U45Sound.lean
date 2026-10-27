module

public import Certificates.Data.Kernel.Co1M.U45
public import CFSG.Certificates.Kernel.SortTreeSound

public section

namespace CFSG.KC.U45

open CFSG.KLie.CT CFSG.KC.M1F2 CFSG.KC.Co1F2 CFSG.KC.SortTree CFSG.KC.Odd73

theorem andB45 {a b : Bool} : andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> simp [andB]

theorem orB45 {a b : Bool} : orB a b = true ↔ a = true ∨ b = true := by
  cases a <;> simp [orB]

theorem notB45 {a : Bool} : notB a = true ↔ a = false := by
  cases a <;> simp [notB]

theorem beqF45 {a b : Nat} : Nat.beq a b = false ↔ a ≠ b := by
  rw [← Bool.not_eq_true, beq_iff]

theorem memK_iff (i : Nat) : ∀ L : List Nat, memK i L = true ↔ i ∈ L
  | [] => by simp [memK]
  | a :: L => by
    change orB (Nat.beq a i) (memK i L) = true ↔ _
    rw [orB45, beq_iff, memK_iff i L, List.mem_cons, eq_comm]

theorem allE_iff (f : List Nat → Bool) : ∀ L : List (List Nat), allE L f = true ↔ ∀ e ∈ L, f e = true
  | [] => by simp [allE]
  | e :: L => by
    change andB (f e) (allE L f) = true ↔ _
    rw [andB45, allE_iff f L, List.forall_mem_cons]

theorem headsE_eq : ∀ L : List (List Nat), headsE L = L.map fun e => getL 0 e 0
  | [] => rfl
  | e :: L => by
    change getL 0 e 0 :: headsE L = _
    rw [headsE_eq L, List.map_cons]

theorem lenE_eq : ∀ L : List (List Nat), lenE L = L.length
  | [] => rfl
  | _ :: L => by
    change Nat.succ (lenE L) = _
    rw [lenE_eq L, List.length_cons]

theorem eqL_iff : ∀ L M : List Nat, eqL L M = true ↔ L = M
  | [], [] => by simp [eqL]
  | [], _ :: _ => by simp [eqL]
  | _ :: _, [] => by simp [eqL]
  | a :: L, b :: M => by
    change andB (Nat.beq a b) (eqL L M) = true ↔ _
    rw [andB45, beq_iff, eqL_iff L M, List.cons.injEq]

theorem incE_spec : ∀ (L : List (List Nat)) (x : Nat), incE L x = true →
    (∀ h ∈ headsE L, x ≤ h) ∧ (headsE L).Nodup
  | [], _, _ => by simp [headsE]
  | e :: L, x, h => by
    change andB (Nat.ble x (getL 0 e 0)) (incE L (Nat.succ (getL 0 e 0))) = true at h
    rw [andB45, ble_iff] at h
    obtain ⟨h1, h2⟩ := incE_spec L _ h.2
    change (∀ k ∈ getL 0 e 0 :: headsE L, x ≤ k) ∧ (getL 0 e 0 :: headsE L).Nodup
    refine ⟨fun k hk => ?_, List.nodup_cons.2 ⟨fun hm => ?_, h2⟩⟩
    · rcases List.mem_cons.1 hk with rfl | hk
      · exact h.1
      · have := h1 k hk
        omega
    · have := h1 _ hm
      omega

theorem gapK_spec {rec : Nat → Nat} {n m g : Nat} (h : gapK rec n m g = true)
    (hs : ∀ i j, i < j → j < n → valF 576 (rec i) < valF 576 (rec j)) :
    ∀ k < n, valF 576 (rec k) ≠ m := by
  unfold gapK at h
  simp only [andB45, orB45, ble_iff, beq_iff, blt_iff, Nat.sub_eq] at h
  obtain ⟨hg, h1, h2⟩ := h
  intro k hk e
  rcases Nat.lt_or_ge k g with hkg | hkg
  · rcases h1 with h1 | h1
    · omega
    · have hle : valF 576 (rec k) ≤ valF 576 (rec (g - 1)) := by
        rcases Nat.lt_or_ge k (g - 1) with hk1 | hk1
        · exact (hs k (g - 1) hk1 (by omega)).le
        · have : k = g - 1 := by omega
          rw [this]
      omega
  · rcases h2 with h2 | h2
    · omega
    · have hle : valF 576 (rec g) ≤ valF 576 (rec k) := by
        rcases Nat.lt_or_ge g k with hk1 | hk1
        · exact (hs g k hk1 hk).le
        · have : k = g := by omega
          rw [this]
      omega

theorem witK_spec {TA TB TC o : Nat} {e : List Nat} (h : witK TA TB TC e o = true) :
    getL 0 e o < 2 ^ 24 ∧ opK TA (getL 0 e (o + 1)) = getL 0 e o ∧
      opK TB (getL 0 e (o + 2)) = getL 0 e o ∧ opK TC (getL 0 e (o + 3)) = getL 0 e o := by
  unfold witK at h
  have e24 : pw2 24 = 2 ^ 24 := Nat.one_shiftLeft 24
  simp only [andB45, beq_iff, blt_iff, e24] at h
  exact h

theorem wit2K_spec {nw TA TB TC : Nat} {e : List Nat} (h : wit2K nw TA TB TC e = true) :
    witK TA TB TC e 2 = true ∧ witK TA TB TC e (lastO nw) = true ∧
      (2 ≤ nw → getL 0 e 2 ≠ getL 0 e (lastO nw)) := by
  unfold wit2K at h
  simp only [andB45, orB45, notB45, blt_iff, beqF45] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, h2, fun hn => ?_⟩
  rcases h3 with h3 | h3
  · omega
  · exact h3

theorem stRec_spec {wl wp : Nat} {rec : Nat → Nat} {SI : List Nat} {i : Nat}
    (h : stRec wl wp rec SI i = true) :
    (levF 576 wl (rec i) ≠ 0 ∧ letF 576 wl wp (rec i) < 8) ∨ i ∈ SI := by
  unfold stRec at h
  simp only [orB45, andB45, notB45, blt_iff, beqF45, memK_iff] at h
  exact h

theorem stE_spec {nw R n : Nat} {rec : Nat → Nat} {e : List Nat} (h : stE nw R rec n e = true) :
    getL 0 e 0 < n ∧ (mulF 24 R (valF 576 (rec (getL 0 e 0))) ≠
        mulF 24 (valF 576 (rec (getL 0 e 0))) R ∨
      gapK rec n (mulF 24 R (valF 576 (rec (getL 0 e 0)))) (getL 0 e 1) = true ∨
      wit2K nw (trK 24 R) (trK 24 (valF 576 (rec (getL 0 e 0))))
        (trK 24 (mulF 24 R (valF 576 (rec (getL 0 e 0))))) e = true) := by
  unfold stE at h
  simp only [andB45, orB45, notB45, blt_iff, beqF45] at h
  exact h

theorem c5E_spec {nw R n : Nat} {rec aux : Nat → Nat} {e : List Nat}
    (h : c5E nw R rec aux n e = true) :
    getL 0 e 0 < n ∧ clsA (aux (getL 0 e 0)) = 5 ∧ (valF 576 (rec (getL 0 e 0)) = R ∨
      gapK rec n (mulF 24 R (valF 576 (rec (getL 0 e 0)))) (getL 0 e 1) = true ∨
      (getL 0 e 1 < n ∧ valF 576 (rec (getL 0 e 1)) = mulF 24 R (valF 576 (rec (getL 0 e 0))) ∧
        clsA (aux (getL 0 e 1)) ≠ 5) ∨
      wit2K nw (trK 24 R) (trK 24 (valF 576 (rec (getL 0 e 0))))
        (trK 24 (mulF 24 R (valF 576 (rec (getL 0 e 0))))) e = true) := by
  unfold c5E at h
  simp only [andB45, orB45, notB45, blt_iff, beq_iff, beqF45] at h
  exact h

end CFSG.KC.U45

end
