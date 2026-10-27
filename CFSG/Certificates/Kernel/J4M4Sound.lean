module

public import CFSG.Certificates.Kernel.J4Tree.CodeSound
public import CFSG.Certificates.Kernel.J4M4Bfs
public import CFSG.Certificates.Kernel.J4M4SetsSound
public import Certificates.Data.Kernel.J4M4Code
public import Certificates.Data.CFSGNative.J4Tree.M4Type

public section

namespace CFSG.KC.J4M4

open CFSG.J4Tree.Native CFSG.J4Tree.Native.Node CFSG.J4Tree.M4 CFSG.KC.J4Tree CFSG.KC.F2W
open CFSG.KC.Co1F2

theorem fieldsL_eq (a : ℕ) : fieldsL a = (unpackR 12 a).toList := by
  apply List.ext_getElem
  · simp [fieldsL, unpackR]
  · intro i h1 h2
    simp only [fieldsL, unpackR, List.getElem_map, List.getElem_range, Array.toList_ofFn,
      List.getElem_ofFn]

theorem rc_beq_eq {y y' : Code} {a b : ℕ} (ha : RC y a) (hb : RC y' b) :
    (y == y') = eqC a b := by
  rw [Bool.eq_iff_iff, beq_iff_eq, eqC, eqL_iff, fieldsL_eq, fieldsL_eq]
  constructor
  · rintro rfl
    rw [← ha, ← hb]
  · intro h
    cases y
    cases y'
    simp only [RC] at ha hb
    rw [Code.mk.injEq, ha, hb]
    exact Array.ext' h

theorem rc_unpack (k : ℕ) : RC ⟨unpackR 12 k⟩ k := rfl

theorem eq_of_fields : ∀ (n x y : ℕ), x < 2 ^ (12 * n) → y < 2 ^ (12 * n) →
    (∀ i < n, x / 2 ^ (12 * i) % 2 ^ 12 = y / 2 ^ (12 * i) % 2 ^ 12) → x = y
  | 0, x, y, hx, hy, _ => by
    simp at hx hy
    omega
  | n + 1, x, y, hx, hy, h => by
    have h0 := h 0 (by omega)
    simp only [Nat.mul_zero, Nat.pow_zero, Nat.div_one] at h0
    have hd : x / 2 ^ 12 = y / 2 ^ 12 := by
      refine eq_of_fields n _ _ ?_ ?_ fun i hi => ?_
      · rw [Nat.div_lt_iff_lt_mul (by positivity), ← Nat.pow_add]
        convert hx using 2
      · rw [Nat.div_lt_iff_lt_mul (by positivity), ← Nat.pow_add]
        convert hy using 2
      · have := h (i + 1) (by omega)
        rwa [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, ← Nat.pow_add,
          show 12 + 12 * i = 12 * (i + 1) by ring]
    rw [← Nat.div_add_mod x (2 ^ 12), ← Nat.div_add_mod y (2 ^ 12), hd, h0]

theorem key_unique {y : Code} {k k' : ℕ} (hk : k < 2 ^ 144) (hk' : k' < 2 ^ 144) (h : RC y k)
    (h' : RC y k') : k = k' := by
  have e : unpackR 12 k = unpackR 12 k' := h.symm.trans h'
  refine eq_of_fields 12 k k' hk hk' fun i hi => ?_
  have := congrArg (fun a : Array ℕ => a[i]?.getD 0) e
  simpa [unpackR, hi] using this

theorem rc_kel (hk : kCode.toList.all Code.wf = true) (e : ℕ) : RC (kelCode e) (kelK e) := by
  unfold kelCode kelK
  exact rc_foldl _ _ (fun _ _ i h => rc_mul h (rc_get hk i)) _ 1 oneK rc_one

theorem rc_cc (hu : uCode.toList.all Code.wf = true) (hk : kCode.toList.all Code.wf = true)
    (ce : ℕ × ℕ) : RC (cc ce) (ccK ce) := by
  unfold cc codeOfCoord ccK
  exact rc_mul (rc_etaCode hu _) (rc_kel hk _)

theorem rc_maskCodeL (hu : uCode.toList.all Code.wf = true) (hk : kCode.toList.all Code.wf = true)
    (w : List (ℕ × ℕ)) (m : ℕ) : RC (maskCodeL w m) (maskK w m) := by
  unfold maskCodeL maskK
  refine rc_foldl _ _ (fun a P l h => ?_) _ 1 oneK rc_one
  split
  · exact rc_mul h (rc_cc hu hk _)
  · exact h

theorem rc_map_getD (hu : uCode.toList.all Code.wf = true) (hk : kCode.toList.all Code.wf = true)
    (L : List (ℕ × ℕ)) {s : ℕ} (hs : s < L.length) :
    RC ((L.map cc).getD s 1) ((L.map ccK).getD s 0) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hs), List.getD_eq_getElem _ _ (by simpa using hs),
    List.getElem_map, List.getElem_map]
  exact rc_cc hu hk _

theorem reachLe_of_reachN {α : Type} {gs : List α} {step : α → Code → Code} {d : α}
    {act : ℕ → ℕ → ℕ}
    (hstep : ∀ s < gs.length, ∀ y k, RC y k → RC (step (gs.getD s d) y) (act s k))
    {x₀ : Code} {r : ℕ} (hr : RC x₀ r) :
    ∀ (n k : ℕ), ReachN act gs.length r n k → ∀ y, RC y k → ReachLe gs step x₀ n y
  | 0, k, hk, y, hy => by
    have e : k = r := hk
    subst e
    exact rc_eq hy hr
  | n + 1, k, hk, y, hy => by
    rcases hk with hk | ⟨s, hs, p, hp, rfl⟩
    · exact Or.inl (reachLe_of_reachN hstep hr n k hk y hy)
    · refine Or.inr ⟨⟨unpackR 12 p⟩, reachLe_of_reachN hstep hr n p hp _ (rc_unpack p),
        gs.getD s d, ?_, rc_eq (hstep s hs _ p (rc_unpack p)) hy⟩
      rw [List.getD_eq_getElem _ _ hs]
      exact List.getElem_mem hs

theorem mem_of_cert {α : Type} {gs : List α} {step : α → Code → Code} {d : α}
    {act : ℕ → ℕ → ℕ}
    (hstep : ∀ s < gs.length, ∀ y k, RC y k → RC (step (gs.getD s d) y) (act s k))
    {x₀ : Code} {r : ℕ} (hr : RC x₀ r) {L : List ℕ}
    (hT : r ∈ L ∧ (∀ k ∈ L, ReachN act gs.length r 64 k) ∧ L.Nodup) (hC : closeOK act gs.length L = true) (y : Code) :
    y ∈ bfsFrom gs step x₀ 64 ↔ ∃ k ∈ L, RC y k := by
  obtain ⟨hroot, hreach, -⟩ := hT
  have hcl := closeOK_sound hC
  refine bfsFrom_mem_iff gs step x₀ (fun y => ∃ k ∈ L, RC y k) ⟨r, hroot, hr⟩ ?_ ?_ y
  · rintro y ⟨k, hk, hy⟩ g hg
    obtain ⟨s, hs, rfl⟩ := List.mem_iff_getElem.mp hg
    refine ⟨act s k, hcl s hs k hk, ?_⟩
    have := hstep s hs y k hy
    rwa [List.getD_eq_getElem _ _ hs] at this
  · rintro y ⟨k, hk, hy⟩
    exact reachLe_of_reachN hstep hr 64 k (hreach k hk) y hy

theorem contains_of_cert {α : Type} {gs : List α} {step : α → Code → Code} {d : α}
    {act : ℕ → ℕ → ℕ}
    (hstep : ∀ s < gs.length, ∀ y k, RC y k → RC (step (gs.getD s d) y) (act s k))
    {x₀ : Code} {r : ℕ} (hr : RC x₀ r) {L : List ℕ}
    (hT : r ∈ L ∧ (∀ k ∈ L, ReachN act gs.length r 64 k) ∧ L.Nodup) (hC : closeOK act gs.length L = true) {y : Code}
    {k : ℕ} (hy : RC y k) (hk : k ∈ L) : (bfsFrom gs step x₀ 64).contains y = true :=
  Std.HashSet.contains_iff_mem.mpr ((mem_of_cert hstep hr hT hC y).mpr ⟨k, hk, hy⟩)

theorem not_contains_of_cert {α : Type} {gs : List α} {step : α → Code → Code} {d : α}
    {act : ℕ → ℕ → ℕ}
    (hstep : ∀ s < gs.length, ∀ y k, RC y k → RC (step (gs.getD s d) y) (act s k))
    {x₀ : Code} {r : ℕ} (hr : RC x₀ r) {L : List ℕ}
    (hT : r ∈ L ∧ (∀ k ∈ L, ReachN act gs.length r 64 k) ∧ L.Nodup) (hC : closeOK act gs.length L = true) {y : Code}
    {k : ℕ} (hy : RC y k) (hk : L.all (fun k' => !eqC k' k) = true) :
    (bfsFrom gs step x₀ 64).contains y = false := by
  rw [Bool.eq_false_iff]
  intro h
  obtain ⟨k', hk', hy'⟩ := (mem_of_cert hstep hr hT hC y).mp (Std.HashSet.contains_iff_mem.mp h)
  have h1 := List.all_eq_true.mp hk k' hk'
  rw [← rc_beq_eq hy' hy, beq_self_eq_true] at h1
  exact absurd h1 (by decide)

theorem closed_of_cert {α : Type} {gs : List α} {step : α → Code → Code} {d : α}
    {act : ℕ → ℕ → ℕ}
    (hstep : ∀ s < gs.length, ∀ y k, RC y k → RC (step (gs.getD s d) y) (act s k))
    {x₀ : Code} {r : ℕ} (hr : RC x₀ r) {L : List ℕ}
    (hT : r ∈ L ∧ (∀ k ∈ L, ReachN act gs.length r 64 k) ∧ L.Nodup) (hC : closeOK act gs.length L = true) :
    (bfsFrom gs step x₀ 64).contains x₀ = true ∧
      closedUnder gs step (bfsFrom gs step x₀ 64) = true := by
  have hm := mem_of_cert hstep hr hT hC
  refine ⟨contains_of_cert hstep hr hT hC hr (hT).1,
    closedUnder_of_mem_iff gs step _ hm ?_⟩
  rintro y ⟨k, hk, hy⟩ g hg
  obtain ⟨s, hs, rfl⟩ := List.mem_iff_getElem.mp hg
  refine ⟨act s k, closeOK_sound hC s hs k hk, ?_⟩
  have := hstep s hs y k hy
  rwa [List.getD_eq_getElem _ _ hs] at this

theorem size_of_cert {α : Type} {gs : List α} {step : α → Code → Code} {d : α}
    {act : ℕ → ℕ → ℕ}
    (hstep : ∀ s < gs.length, ∀ y k, RC y k → RC (step (gs.getD s d) y) (act s k))
    {x₀ : Code} {r : ℕ} (hr : RC x₀ r) {L : List ℕ}
    (hT : r ∈ L ∧ (∀ k ∈ L, ReachN act gs.length r 64 k) ∧ L.Nodup) (hC : closeOK act gs.length L = true)
    (hb : L.all (fun k => Nat.blt k (2 ^ 144)) = true) :
    (bfsFrom gs step x₀ 64).size = L.length := by
  have hb' : ∀ k ∈ L, k < 2 ^ 144 := fun k hk => Nat.blt_eq.mp (List.all_eq_true.mp hb k hk)
  exact size_of_mem_iff RC L (mem_of_cert hstep hr hT hC) (fun _ _ _ h1 h2 => rc_eq h1 h2)
    (fun _ _ _ hk hk' h1 h2 => key_unique (hb' _ hk) (hb' _ hk') h1 h2)
    (fun k _ => ⟨_, rc_unpack k⟩) (hT).2.2

theorem rmul_step {G : List Code} {GK : List ℕ} (hG : ∀ s < G.length, RC (G.getD s 1) (GK.getD s 0)) :
    ∀ s < G.length, ∀ y k, RC y k → RC (rmul (G.getD s 1) y) (actR GK s k) :=
  fun s hs _ _ hy => rc_mul hy (hG s hs)

theorem conj_step {G : List (Code × Code)} {GK GI : List ℕ}
    (hG : ∀ s < G.length, RC (G.getD s (1, 1)).1 (GK.getD s 0) ∧ RC (G.getD s (1, 1)).2 (GI.getD s 0)) :
    ∀ s < G.length, ∀ y k, RC y k → RC (conjP (G.getD s (1, 1)) y) (actC GK GI s k) :=
  fun s hs _ _ hy => rc_mul (rc_mul (hG s hs).1 hy) (hG s hs).2

end CFSG.KC.J4M4
