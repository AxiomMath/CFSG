module

public import CFSG.Certificates.Kernel.Fi22Snd.Rows
public import CFSG.Certificates.Kernel.Fi22Snd.AdjBfs

public section

namespace CFSG.KC.Fi22Snd

open CFSG.KC.Enum CFSG.KC.N3153 CFSG.KS CFSG.KS.Raw CFSG.Certificates.Native
open CFSG.Monster.B.Co2.Native

private theorem treeOK_facts {n ng : Nat} {G T : Nat → Nat} {x : Nat}
    (h : treeOK n ng G T x = true) (hx : x ≠ 0) :
    ∃ p g, p < n ∧ g < ng ∧
      Nat.land (Nat.shiftRight (T p) (nat_lit 24)) (nat_lit 65535) <
        Nat.land (Nat.shiftRight (T x) (nat_lit 24)) (nat_lit 65535) ∧
      pg (nat_lit 12) (nat_lit 4095) (G g) p = x := by
  unfold treeOK at h
  rw [CFSG.KS.Raw.Orb.bIf_eq] at h
  have h0 : ¬ Nat.beq x (nat_lit 0) = true := fun hb => hx (Nat.eq_of_beq_eq_true hb)
  rw [if_neg h0, CFSG.KC.Pack.strictB_eq, CFSG.KC.Pack.strictB_eq] at h
  obtain ⟨h1, h'⟩ := CFSG.KC.Pack.band_iff.1 h
  obtain ⟨h2, h''⟩ := CFSG.KC.Pack.band_iff.1 h'
  obtain ⟨h3, h4⟩ := CFSG.KC.Pack.band_iff.1 h''
  exact ⟨_, _, Nat.le_of_ble_eq_true h1, Nat.le_of_ble_eq_true h2, Nat.le_of_ble_eq_true h3,
    Nat.eq_of_beq_eq_true h4⟩

theorem graph_sound' {n d ng : Nat} {gens : Array (Array Nat)} {R M S G T : Nat → Nat}
    {root : List Nat} (hn0 : 0 < n) (hgs : gens.size = ng)
    (hG : ∀ k < ng, gens[k]! = unpack n 12 (G k))
    (hrow : ∀ x < n, rowOK n d R M S x = true)
    (himg : ∀ k < ng, ∀ x < n, imgOK n d (G k) R M x = true)
    (htree : ∀ x < n, treeOK n ng G T x = true) (hsym : ∀ i < d, sym0OK R M i = true)
    (hroot : root = decodeRow d (R 0)) :
    adjSearch n gens root = rowsArr n d R ∧ adjOK n gens (rowsArr n d R) root = true := by
  have hlt : ∀ k < gens.size, ∀ x < n, (gens[k]!)[x]! < n := by
    intro k hk x hx
    have hk' : k < ng := by omega
    rw [hG k hk', unpack12_get hx]
    exact (imgOK_facts (himg k hk' x hx)).1
  have himg' : ∀ k < gens.size, ∀ x < n,
      imgSorted gens[k]! (decodeRow d (R x)) = decodeRow d (R (gens[k]!)[x]!) := by
    intro k hk x hx
    have hk' : k < ng := by omega
    have h := (CFSG.Monster.B.Co2.allLt_iff.1 (img_sound' hrow (hG k hk') (himg k hk'))) x hx
    rw [beq_iff_eq, rowsArr_get (hlt k hk x hx), rowsArr_get hx] at h
    exact h.symm
  have hreach : ∀ P : Nat → Prop, P 0 → (∀ p < n, P p → ∀ k < gens.size, P (gens[k]!)[p]!) →
      ∀ x < n, P x := by
    intro P h0 hcl
    have key : ∀ D x, x < n → Nat.land (Nat.shiftRight (T x) (nat_lit 24)) (nat_lit 65535) = D →
        P x := by
      intro D
      induction D using Nat.strong_induction_on with
      | _ D ih =>
        intro x hx hD
        by_cases hx0 : x = 0
        · subst hx0
          exact h0
        · obtain ⟨p, g, hp, hg, hdep, hpg⟩ := treeOK_facts (htree x hx) hx0
          have hPp : P p := ih _ (hD ▸ hdep) p hp rfl
          have := hcl p hp hPp g (by omega)
          rwa [hG g hg, unpack12_get hp, hpg] at this
    exact fun x hx => key _ x hx rfl
  have h1 : adjSearch n gens root = rowsArr n d R := by
    rw [hroot]
    exact adjSearch_eq (Row := fun x => decodeRow d (R x)) hn0 hlt himg' hreach
  refine ⟨h1, ?_⟩
  unfold adjOK
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · simp [rowsArr]
  · rw [rowsArr_get hn0, hroot]
  · rw [CFSG.Monster.B.Co2.allLt_iff]
    intro x hx
    rw [rowsArr_get hx, Bool.and_eq_true, List.all_eq_true]
    exact ⟨fun y hy => decide_eq_true (row_entry_lt (hrow x hx) hy),
      strictIncr_of_pairwise (row_pairwise (hrow x hx))⟩
  · rw [rowsArr_get hn0, List.all_eq_true]
    intro y hy
    have hyn := row_entry_lt (hrow 0 hn0) hy
    rw [decodeRow_eq, List.mem_map] at hy
    obtain ⟨i, hi, rfl⟩ := hy
    have hs := hsym i (List.mem_range.1 hi)
    unfold sym0OK at hs
    have hb : (M (rg (R 0) i)).testBit 0 = true := by
      rw [← beq_bit]
      exact hs
    rw [row_mask (hrow _ hyn)] at hb
    rw [rowsArr_get hyn]
    simpa using hb
  · rw [CFSG.Monster.B.Co2.allLt_iff]
    intro k hk
    exact img_sound' hrow (hG k (by omega)) (himg k (by omega))

end CFSG.KC.Fi22Snd

end
