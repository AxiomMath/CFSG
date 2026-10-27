module

public import CFSG.Certificates.Kernel.Spor.Fi24PairPcSound
public import CFSG.Certificates.Kernel.Spor.Fi24NetPtSound
public import CFSG.Certificates.Kernel.Spor.Fi24FixPSound
public import CFSG.Sporadic.Schreier.J4SChain

public section

namespace CFSG.KS.Fi24PairK

open CFSG.KC CFSG.KC.Loop CFSG.KC.Benes CFSG.KC.Fi24Net CFSG.KC.Fi24NetPt CFSG.KC.Fi24PairK
  CFSG.KS.Fi24Net CFSG.KS.Fi24NetPt CFSG.KS.Fi24PairPc CFSG.Sporadic.Th

local notation "J" => CFSG.Sporadic.Fi24.J

section Chain

variable {G X : Type*} [Group G] [MulAction G X] [Finite G]

theorem card_chain_ge (H : ℕ → Subgroup G) (b : ℕ → X) (c : ℕ → ℕ) {m : ℕ}
    (hle : ∀ i, i + 1 < m → H (i + 1) ≤ H i)
    (hfix : ∀ i, i + 1 < m → ∀ g ∈ H (i + 1), g • b i = b i)
    (horb : ∀ i < m, c i ≤ (MulAction.orbit (H i) (b i)).ncard) :
    ∀ i < m, ∏ l ∈ Finset.Ico i m, c l ≤ Nat.card (H i) := by
  intro i hi
  induction h : m - i generalizing i with
  | zero => omega
  | succ d ih =>
    rw [Finset.prod_eq_prod_Ico_succ_bot hi,
      CFSG.Sporadic.J4Schreier.card_eq_orbit_mul_stabilizer (H i) (b i)]
    rcases Nat.lt_or_ge (i + 1) m with h1 | h1
    · exact Nat.mul_le_mul (horb i hi) ((ih (i + 1) h1 (by omega)).trans
        (CFSG.Sporadic.J4Schreier.card_le_card_stabilizer (hle i h1) (hfix i h1)))
    · have e : i + 1 = m := by omega
      rw [e, Finset.Ico_self, Finset.prod_empty, mul_one]
      exact (horb i hi).trans (Nat.le_mul_of_pos_right _ Nat.card_pos)

end Chain

theorem ptZ_eq_lP (NW : Nat → Nat → Nat) (z : Int) (x : Nat) : ptZ NW z x = lP NW z x := by
  cases z with
  | ofNat m =>
    by_cases hm : m = 0
    · subst hm
      have e : lP NW (Int.ofNat 0) = pR (NW (lidx 0)) := if_pos rfl
      rw [e, ← ptR_eq]
      rfl
    · have e : lP NW (Int.ofNat m) = pF (NW (lidx m)) := if_neg hm
      rw [e, ← ptF_eq]
      change nIf(Nat.beq m (nat_lit 0), ptR (NW (lidx m)) x, ptF (NW (lidx m)) x) = _
      rw [beq_false hm]
  | negSucc n =>
    by_cases hn : n = 0
    · subst hn
      have e : lP NW (Int.negSucc 0) = pF (NW 0) := if_pos rfl
      rw [e, ← ptF_eq]
      rfl
    · have e : lP NW (Int.negSucc n) = pR (NW (lidx (n + 1))) := if_neg hn
      rw [e, ← ptR_eq]
      change nIf(Nat.beq n (nat_lit 0), ptF (NW (nat_lit 0)) x, ptR (NW (lidx (Nat.succ n))) x) = _
      rw [beq_false hn]

theorem lP_cases (NW : Nat → Nat → Nat) (z : Int) :
    lP NW z = pF (NW (lidx z.natAbs)) ∨ lP NW z = pR (NW (lidx z.natAbs)) := by
  cases z with
  | ofNat m =>
    by_cases hm : m = 0
    · exact Or.inr (if_pos hm)
    · exact Or.inl (if_neg hm)
  | negSucc n =>
    by_cases hn : n = 0
    · subst hn
      exact Or.inl (if_pos rfl)
    · exact Or.inr (if_neg hn)

theorem foldr_lP_eq (NW : Nat → Nat → Nat) : ∀ (w : List Int) (q : Nat),
    w.foldr (lP NW) q = apZ NW w q
  | [], _ => rfl
  | z :: w, q => by rw [List.foldr_cons, apZ_cons, foldr_lP_eq NW w q, ptZ_eq_lP]

theorem dirOK_mem {net : Nat → Bool} : ∀ {w : List Int}, dirOK net w = true →
    ∀ z ∈ w, dirZ net z = true
  | [], _, _, hz => absurd hz List.not_mem_nil
  | y :: w, h, z, hz => by
    rw [dirOK_cons, Bool.and_eq_true] at h
    rcases List.mem_cons.1 hz with rfl | hz
    · exact h.1
    · exact dirOK_mem h.2 z hz

theorem net_lidx {net : Nat → Bool} (h0 : net 0 = true) (h1 : net 1 = true) {z : Int}
    (hz : dirZ net z = true) : net (lidx z.natAbs) = true := by
  unfold dirZ at hz
  rw [lidx_eq]
  by_cases h : z.natAbs ≤ 2
  · split_ifs <;> first | exact h0 | exact h1 | omega
  · rw [ble_false (by omega : 2 < z.natAbs)] at hz
    split_ifs <;> first | exact h0 | exact h1 | exact hz

section Nets

variable {NV : Nat → Nat → Nat} {net : Nat → Bool}
  (hV : ∀ j, net j = true → netOK (NV j) = true) (h0 : net 0 = true) (h1 : net 1 = true)
include hV h0 h1

theorem nv_dir {z : Int} (hz : dirZ net z = true) : CFSG.KS.Fi24Net.NV (NV (lidx z.natAbs)) :=
  (net_spec (hV _ (net_lidx h0 h1 hz))).1

theorem testBit_walkW' {w : List Int} (hw : dirOK net w = true) (v q : Nat) :
    (walkW NV w v).testBit q = v.testBit (apZ NV w q) := by
  rw [testBit_walkW w (fun z hz => nv_dir hV h0 h1 (dirOK_mem hw z hz)), foldr_lP_eq]

theorem lP_pts {z : Int} (hz : dirZ net z = true) {q : Nat} (hq : q < 524288) :
    lP NV z q < 524288 ∧ (lP NV z q < 306936 ↔ q < 306936) := by
  obtain ⟨hv, hpt⟩ := net_spec (hV _ (net_lidx h0 h1 hz))
  rcases lP_cases NV z with e | e
  · rw [e]
    exact ⟨pF_lt hv hq, hpt q hq⟩
  · rw [e]
    have hr := pR_lt hv hq
    refine ⟨hr, ?_⟩
    have := hpt _ hr
    rw [pF_pR hv] at this
    exact this.symm

theorem apZ_pts {w : List Int} (hw : dirOK net w = true) {q : Nat} (hq : q < 524288) :
    apZ NV w q < 524288 ∧ (apZ NV w q < 306936 ↔ q < 306936) := by
  induction w with
  | nil => exact ⟨hq, Iff.rfl⟩
  | cons z w ih =>
    rw [dirOK_cons, Bool.and_eq_true] at hw
    obtain ⟨h1', h2'⟩ := ih hw.2
    rw [apZ_cons, ptZ_eq_lP]
    obtain ⟨h3, h4⟩ := lP_pts hV h0 h1 hw.1 h1'
    exact ⟨h3, h4.trans h2'⟩

end Nets

theorem invW_eq (u : List Int) : invW u = (u.map Neg.neg).reverse := by
  induction u with
  | nil => rfl
  | cons z u ih => rw [invW_cons, ih, List.map_cons, List.reverse_cons]

theorem flatF_succ (W : Nat → List Int) (net : Nat → Bool) (d : Nat) (z : Int) :
    flatF W net (d + 1) z = Bool.rec (motive := fun _ => List Int)
      ((fun u => Bool.rec (motive := fun _ => List Int) (invW u) u (posZ z))
        (List.rec (motive := fun _ => List Int) List.nil (fun y _ r => flatF W net d y ++ r)
          (W (z.natAbs - 3))))
      [z] (dirZ net z) := rfl

theorem flatF_spec {L : ℤ → J} {net : Nat → Bool} {W : Nat → List Int}
    (hinv : ∀ z, z ≠ 0 → L (-z) = (L z)⁻¹)
    (hW : ∀ z : ℤ, 0 < z → dirZ net z = false →
      (∀ y ∈ W (z.natAbs - 3), y ≠ 0) ∧ wEl L (W (z.natAbs - 3)) = L z) :
    ∀ d z, z ≠ 0 → (∀ y ∈ flatF W net d z, y ≠ 0) ∧ wEl L (flatF W net d z) = L z := by
  intro d
  induction d with
  | zero =>
    intro z hz
    refine ⟨fun y hy => ?_, ?_⟩
    · have hy' : y ∈ [z] := hy
      rw [List.mem_singleton.1 hy']
      exact hz
    · change wEl L [z] = L z
      simp [wEl]
  | succ d ih =>
    intro z hz
    have hE : ∀ u : List Int, (∀ y ∈ u, y ≠ 0) →
        (∀ y ∈ List.rec (motive := fun _ => List Int) List.nil
          (fun y _ r => flatF W net d y ++ r) u, y ≠ 0) ∧
        wEl L (List.rec (motive := fun _ => List Int) List.nil
          (fun y _ r => flatF W net d y ++ r) u) = wEl L u := by
      intro u hu
      induction u with
      | nil => exact ⟨fun y hy => absurd hy List.not_mem_nil, rfl⟩
      | cons y u ihu =>
        obtain ⟨h1, h2⟩ := ihu fun y' hy' => hu y' (List.mem_cons_of_mem y hy')
        obtain ⟨h3, h4⟩ := ih y (hu y List.mem_cons_self)
        change (∀ y' ∈ flatF W net d y ++ _, y' ≠ 0) ∧ wEl L (flatF W net d y ++ _) = _
        refine ⟨fun y' hy' => ?_, ?_⟩
        · rcases List.mem_append.1 hy' with hy' | hy'
          · exact h3 y' hy'
          · exact h1 y' hy'
        · rw [wEl_append, h2, h4, wEl_cons]
    rw [flatF_succ]
    cases hd : dirZ net z
    · change (∀ y ∈ Bool.rec (motive := fun _ => List Int) (invW _) _ (posZ z), y ≠ 0) ∧
        wEl L (Bool.rec (motive := fun _ => List Int) (invW _) _ (posZ z)) = L z
      rcases lt_or_gt_of_ne hz with hneg | hpos
      · have hp : posZ z = false := by
          obtain ⟨n, rfl⟩ := Int.exists_eq_neg_ofNat (le_of_lt hneg)
          cases n with
          | zero => exact absurd rfl hz
          | succ n => rfl
        rw [hp]
        have hd' : dirZ net (-z) = false := by rw [dirZ_neg]; exact hd
        obtain ⟨hW1, hW2⟩ := hW (-z) (by omega) hd'
        rw [Int.natAbs_neg] at hW1 hW2
        obtain ⟨h1, h2⟩ := hE _ hW1
        refine ⟨fun y hy => ?_, ?_⟩
        · change y ∈ invW _ at hy
          rw [invW_eq, List.mem_reverse, List.mem_map] at hy
          obtain ⟨x, hx, rfl⟩ := hy
          exact neg_ne_zero.2 (h1 x hx)
        · change wEl L (invW _) = L z
          rw [wEl_invW L hinv _ h1, h2, hW2, hinv z hz, inv_inv]
      · have hp : posZ z = true := by
          obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (le_of_lt hpos)
          rfl
        rw [hp]
        obtain ⟨hW1, hW2⟩ := hW z hpos hd
        obtain ⟨h1, h2⟩ := hE _ hW1
        exact ⟨h1, h2.trans hW2⟩
    · change (∀ y ∈ [z], y ≠ 0) ∧ wEl L [z] = L z
      refine ⟨fun y hy => ?_, by simp [wEl]⟩
      rw [List.mem_singleton.1 hy]
      exact hz

theorem fixW_spec {NV : Nat → Nat → Nat} {w : List Int} :
    ∀ {B : List Nat}, fixW NV w B = true → ∀ b ∈ B, apZ NV w b = b
  | [], _, _, hb => absurd hb List.not_mem_nil
  | c :: B, h, b, hb => by
    change bAnd(Nat.beq (apZ NV w c) c, fixW NV w B) = true at h
    rw [bAnd_eq, Bool.and_eq_true] at h
    rcases List.mem_cons.1 hb with rfl | hb
    · exact Nat.eq_of_beq_eq_true h.1
    · exact fixW_spec h.2 b hb

@[expose] def Good (H : Subgroup J) (y S : Nat) : Prop :=
  ∀ q < 524288, S.testBit q = true → q < 306936 ∧ ∃ g ∈ H, idx 306936 g y = q

theorem testBit_stepW {NV : Nat → Nat → Nat} {S q : Nat} : ∀ {ws : List (List Int)},
    (stepW NV ws S).testBit q = true → S.testBit q = true ∨ ∃ w ∈ ws, (walkW NV w S).testBit q = true
  | [], h => Or.inl h
  | w :: ws, h => by
    change (Nat.lor (walkW NV w S) (stepW NV ws S)).testBit q = true at h
    rw [nlor, Nat.testBit_or, Bool.or_eq_true] at h
    rcases h with h | h
    · exact Or.inr ⟨w, List.mem_cons_self, h⟩
    · rcases testBit_stepW h with h' | ⟨w', hw', h'⟩
      · exact Or.inl h'
      · exact Or.inr ⟨w', List.mem_cons_of_mem w hw', h'⟩

section Orbit

variable {L : ℤ → J} {NV : Nat → Nat → Nat} {net : Nat → Bool}
  (hN : PtHyp L NV net) (hV : ∀ j, net j = true → netOK (NV j) = true) (h0 : net 0 = true)
  (h1 : net 1 = true)
include hN hV h0 h1

theorem good_stepW {ws : List (List Int)} (hws : ∀ w ∈ ws, dirOK net w = true) {H : Subgroup J}
    (hH : ∀ w ∈ ws, wEl L w ∈ H) {y S : Nat} (hS : Good H y S) : Good H y (stepW NV ws S) := by
  intro q hq h
  rcases testBit_stepW (NV := NV) h with h | ⟨w, hw, h⟩
  · exact hS q hq h
  · rw [testBit_walkW' hV h0 h1 (hws w hw)] at h
    obtain ⟨hlt, hpt⟩ := apZ_pts hV h0 h1 (hws w hw) hq
    obtain ⟨hp, g, hg, e⟩ := hS _ hlt h
    have hq' := hpt.1 hp
    refine ⟨hq', (wEl L w)⁻¹ * g, H.mul_mem (H.inv_mem (hH w hw)) hg, ?_⟩
    rw [idx_mul, e, apZ_eq hN w (hws w hw) q hq', idx_inv_idx]

theorem good_iterW {ws : List (List Int)} (hws : ∀ w ∈ ws, dirOK net w = true) {H : Subgroup J}
    (hH : ∀ w ∈ ws, wEl L w ∈ H) {y S : Nat} (hS : Good H y S) :
    ∀ d, Good H y (iterW NV ws d S)
  | 0 => hS
  | d + 1 => by
    have e : iterW NV ws (d + 1) S = stepW NV ws (iterW NV ws d S) := Fi24NetPt.strictN_eq _ _
    rw [e]
    exact good_stepW hN hV h0 h1 hws hH (good_iterW hws hH hS d)

theorem orbW_le {ws : List (List Int)} (hws : ∀ w ∈ ws, dirOK net w = true) (H : Subgroup J)
    (hH : ∀ w ∈ ws, wEl L w ∈ H) {d y c : Nat} (hy : y < 306936) (h : orbW NV ws d y c = true) :
    c ≤ (MulAction.orbit H (⟨y, hy⟩ : Fin 306936)).ncard := by
  classical
  unfold orbW at h
  rw [letB_eq', andB_eq, Bool.and_eq_true] at h
  set P := iterW NV ws d (Nat.shiftLeft 1 y) with hP
  have h1y : Good H y (Nat.shiftLeft 1 y) := by
    intro q _ hq
    change (1 <<< y).testBit q = true at hq
    rw [Nat.one_shiftLeft, Nat.testBit_two_pow] at hq
    have e : y = q := of_decide_eq_true hq
    subst e
    exact ⟨hy, 1, H.one_mem, idx_one y⟩
  have hG : Good H y P := good_iterW hN hV h0 h1 hws hH h1y d
  have hc : c = ((Finset.range 524288).filter (fun x => P.testBit x = true)).card := by
    rw [← CFSG.KS.Fi24FixP.sum_bits, ← CFSG.KS.Fi24FixP.popcount_19]
    exact (Nat.eq_of_beq_eq_true h.2).symm
  set T : Set (Fin 306936) := {x | P.testBit x.val = true} with hT
  have himg : (↑((Finset.range 524288).filter (fun x => P.testBit x = true)) : Set ℕ) =
      Fin.val '' T := by
    ext x
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq, Set.mem_image, hT]
    constructor
    · rintro ⟨hx, hb⟩
      exact ⟨⟨x, (hG x hx hb).1⟩, hb, rfl⟩
    · rintro ⟨x, hb, rfl⟩
      exact ⟨by omega, hb⟩
  have hsub : T ⊆ MulAction.orbit H (⟨y, hy⟩ : Fin 306936) := by
    intro x hx
    obtain ⟨-, g, hg, e⟩ := hG x.val (by omega) hx
    refine ⟨⟨g, hg⟩, Fin.ext ?_⟩
    change ((⟨g, hg⟩ : H) • (⟨y, hy⟩ : Fin 306936)).val = x.val
    rw [Subgroup.smul_def, ← e, idx_of_lt g hy]
  rw [hc, ← Set.ncard_coe_finset, himg, Set.ncard_image_of_injective _ Fin.val_injective]
  exact Set.ncard_le_ncard hsub (Set.toFinite _)

end Orbit

end CFSG.KS.Fi24PairK

end
