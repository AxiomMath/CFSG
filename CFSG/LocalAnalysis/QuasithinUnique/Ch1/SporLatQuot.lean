module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatO2

public section

namespace CFSG.QuasithinUnique.Ch1.SporLat

open CFSG.QuasithinUnique.K1.SporadicPerm

@[expose] def idTab (n : ℕ) : Array ℕ := Array.range n

@[expose] def powTab (n : ℕ) (t : Array ℕ) : ℕ → Array ℕ
  | 0 => idTab n
  | k + 1 => compArr t (powTab n t k)

structure QuotGen where
  w : List ℕ
  k : ℕ
  m : ℕ
  deriving Inhabited

@[expose] def quotGt (n : ℕ) (L : List (Array ℕ)) (x : QuotGen) : Array ℕ :=
  powTab n (wordTabA L.toArray n x.w) x.k

@[expose] def quotGi (n : ℕ) (L : List (Array ℕ)) (x : QuotGen) : Array ℕ :=
  powTab n (quotGt n L x) (x.m - 1)

@[expose] def QuotOK' (n : ℕ) (B : List ℕ) (L : List (Array ℕ)) (xs : List QuotGen)
    (Gt Gi : List (Array ℕ)) (Ts : Array (List ℕ)) (par cl : Array ℕ) (r : ℕ) : Prop :=
  (∀ x ∈ xs, (∀ l ∈ x.w, l < L.length) ∧ x.m % 2 = 1) ∧
  (∀ i < xs.length, ∀ b ∈ B, img (powTab n Gt[i]! xs[i]!.m) b = b) ∧
  BaseEnumOK n B Gt Gi Ts par cl ∧ Ts.size = r

instance (n : ℕ) (B : List ℕ) (L : List (Array ℕ)) (xs : List QuotGen) (Gt Gi : List (Array ℕ))
    (Ts : Array (List ℕ)) (par cl : Array ℕ) (r : ℕ) :
    Decidable (QuotOK' n B L xs Gt Gi Ts par cl r) := by
  unfold QuotOK'; infer_instance

@[expose] def QuotOK (n : ℕ) (B : List ℕ) (L : List (Array ℕ)) (xs : List QuotGen)
    (Ts : Array (List ℕ)) (par cl : Array ℕ) (r : ℕ) : Prop :=
  QuotOK' n B L xs (xs.map (quotGt n L)) (xs.map (quotGi n L)) Ts par cl r

instance (n : ℕ) (B : List ℕ) (L : List (Array ℕ)) (xs : List QuotGen) (Ts : Array (List ℕ))
    (par cl : Array ℕ) (r : ℕ) : Decidable (QuotOK n B L xs Ts par cl r) := by
  unfold QuotOK; infer_instance

section Pow

variable {Γ : Type} [Group Γ] {n : ℕ} [MulAction Γ (Fin n)]

theorem powTab_size (t : Array ℕ) : ∀ k, (powTab n t k).size = n := by
  intro k
  induction k with
  | zero => simp [powTab, idTab]
  | succ k ih => simp [powTab, compArr, ih]

theorem tab_one_toArray : (tab n (1 : Γ)).toArray = idTab n := by
  unfold tab idTab
  rw [← List.toArray_range]
  congr 1
  simp

theorem tab_pow (g : Γ) : ∀ k : ℕ, (tab n (g ^ k)).toArray = powTab n (tab n g).toArray k := by
  intro k
  induction k with
  | zero => rw [pow_zero]; exact tab_one_toArray
  | succ k ih =>
    rw [pow_succ', tab_mul, powTab, ← ih]
    apply Array.ext'
    rw [compArr_toList]

end Pow

section Odd

variable {Y : Type} [Group Y]

theorem mem_of_pow_eq_one_odd (N : Subgroup Y) [N.Normal] (hp : IsPGroup 2 (Y ⧸ N)) {g : Y}
    {m : ℕ} (hm : m % 2 = 1) (hg : g ^ m = 1) : g ∈ N := by
  have h1 : ((g : Y ⧸ N)) ^ m = 1 := by
    rw [← QuotientGroup.mk_pow, hg]; rfl
  have h2 : orderOf (g : Y ⧸ N) ∣ m := orderOf_dvd_of_pow_eq_one h1
  obtain ⟨a, ha⟩ := (IsPGroup.iff_orderOf.mp hp) (g : Y ⧸ N)
  have h3 : orderOf (g : Y ⧸ N) = 1 := by
    rcases Nat.eq_zero_or_pos a with rfl | hapos
    · simpa using ha
    · exfalso
      have : 2 ∣ m := by
        have h4 : 2 ∣ 2 ^ a := dvd_pow_self 2 hapos.ne'
        rw [← ha] at h4
        exact h4.trans h2
      omega
  have := orderOf_eq_one_iff.mp h3
  exact (QuotientGroup.eq_one_iff g).mp this

end Odd

namespace LatCtx

variable {Γ : Type} [Group Γ] [Finite Γ] {n : ℕ} [MulAction Γ (Fin n)]
  {Lab : Type} [DecidableEq Lab] [Hashable Lab] [Inhabited Lab] (C : LatCtx Γ n Lab)

theorem quot_bound {j : ℕ} (hj : j < C.J) (B : List ℕ) (hB : ∀ b ∈ B, b < n)
    (hbase : ∀ g : Γ, (∀ b ∈ B, act n g b = b) → g = 1) (xs : List QuotGen)
    (Ts : Array (List ℕ)) (par cl : Array ℕ) (r : ℕ)
    (hQ : QuotOK n B (C.D.sTabs ++ C.D.mt[j]!) xs Ts par cl r)
    (N : Subgroup (C.Y j)) [N.Normal] (hp : IsPGroup 2 (C.Y j ⧸ N)) :
    Nat.card (C.Y j ⧸ N) * r ≤ Nat.card (C.Y j) := by
  have hL : C.D.sTabs ++ C.D.mt[j]! = genTabs n (C.sg ++ C.gens j) := (C.Y_letters hj).symm
  obtain ⟨hxs, hpow, hEnum, hsize⟩ : QuotOK' n B (C.D.sTabs ++ C.D.mt[j]!) xs
      (xs.map (quotGt n (C.D.sTabs ++ C.D.mt[j]!)))
      (xs.map (quotGi n (C.D.sTabs ++ C.D.mt[j]!))) Ts par cl r := hQ
  generalize hLL : C.D.sTabs ++ C.D.mt[j]! = L at hL hxs hpow hEnum
  generalize hEE : C.sg ++ C.gens j = E at hL
  have hLlen : L.length = E.length := by rw [hL, genTabs_length]
  have hwl : ∀ x ∈ xs, ∀ l ∈ x.w, l < E.toArray.size := fun x hx l hl => by
    have := (hxs x hx).1 l hl
    simpa [hLlen] using this
  have hel : ∀ l < E.toArray.size, L.toArray.getD l #[] = (tab n (E.toArray.getD l 1)).toArray := by
    rw [hL]; exact genTabs_hel E
  have hGtx : ∀ x ∈ xs, quotGt n L x = (tab n ((evalElt E.toArray x.w) ^ x.k)).toArray := by
    intro x hx
    unfold quotGt
    rw [tab_pow, wordTabA_eq E.toArray L.toArray hel x.w (hwl x hx)]
  have hgm : ∀ x ∈ xs, ((evalElt E.toArray x.w) ^ x.k) ^ x.m = 1 := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    apply hbase
    intro b hb
    have h1 := hpow i hi b hb
    have h2 : (xs.map (quotGt n L))[i]! = quotGt n L xs[i] := by
      rw [getElem!_pos _ i (by simpa using hi)]; simp
    have h3 : xs[i]! = xs[i] := getElem!_pos xs i hi
    rw [h2, h3, hGtx _ (List.getElem_mem hi), ← tab_pow, img_tab] at h1
    exact h1
  have hm_pos : ∀ x ∈ xs, 1 ≤ x.m := fun x hx => by
    have := (hxs x hx).2
    omega
  let gl : List Γ := xs.map fun x => (evalElt E.toArray x.w) ^ x.k
  have hGt : xs.map (quotGt n L) = genTabs n gl := by
    simp only [genTabs, gl, List.map_map]
    apply List.map_congr_left
    intro x hx
    exact hGtx x hx
  have hGi : xs.map (quotGi n L) = genTabsInv n gl := by
    simp only [genTabsInv, gl, List.map_map]
    apply List.map_congr_left
    intro x hx
    simp only [Function.comp_apply]
    unfold quotGi
    rw [hGtx x hx, ← tab_pow]
    congr 2
    have h1 := hgm x hx
    have h2 : (evalElt E.toArray x.w ^ x.k) * (evalElt E.toArray x.w ^ x.k) ^ (x.m - 1) = 1 := by
      rw [← pow_succ', Nat.sub_add_cancel (hm_pos x hx)]; exact h1
    exact eq_inv_of_mul_eq_one_right h2
  have hcard : Nat.card (Subgroup.closure {x | x ∈ gl}) = r := by
    rw [benum_card hB hbase gl Ts par cl (by rw [← hGt, ← hGi]; exact hEnum), hsize]
  have hYmem : ∀ g ∈ gl, g ∈ C.Y j := by
    intro g hg
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hg
    apply Subgroup.pow_mem
    have hels : ∀ l < E.toArray.size, E.toArray.getD l 1 ∈ C.Y j := by
      intro l hl
      have := evalElt_getD_mem_closure E.toArray hl
      rw [toList_toArray_set] at this
      subst hEE
      exact this
    exact evalElt_mem E.toArray hels x.w (hwl x hx)
  have hNmem : ∀ g ∈ gl, ∀ h : g ∈ C.Y j, (⟨g, h⟩ : C.Y j) ∈ N := by
    intro g hg h
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hg
    refine mem_of_pow_eq_one_odd N hp (hxs x hx).2 ?_
    apply Subtype.ext
    simpa using hgm x hx
  have hR : ∀ g ∈ Subgroup.closure {x | x ∈ gl}, ∃ h : g ∈ C.Y j, (⟨g, h⟩ : C.Y j) ∈ N := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx => exact ⟨hYmem x hx, hNmem x hx (hYmem x hx)⟩
    | one => exact ⟨(C.Y j).one_mem, N.one_mem⟩
    | mul x y _ _ ihx ihy =>
      obtain ⟨hx, hxN⟩ := ihx
      obtain ⟨hy, hyN⟩ := ihy
      exact ⟨(C.Y j).mul_mem hx hy, N.mul_mem hxN hyN⟩
    | inv x _ ihx =>
      obtain ⟨hx, hxN⟩ := ihx
      exact ⟨(C.Y j).inv_mem hx, N.inv_mem hxN⟩
  have hle : Nat.card (Subgroup.closure {x | x ∈ gl}) ≤ Nat.card N := by
    refine Nat.card_le_card_of_injective
      (fun g => ⟨⟨g.1, (hR g.1 g.2).1⟩, (hR g.1 g.2).2⟩) ?_
    intro g1 g2 h
    apply Subtype.ext
    have := congrArg (fun z : N => ((z : C.Y j) : Γ)) h
    simpa using this
  have h5 := Subgroup.card_eq_card_quotient_mul_card_subgroup N
  rw [← hcard]
  calc Nat.card (C.Y j ⧸ N) * Nat.card (Subgroup.closure {x | x ∈ gl})
      ≤ Nat.card (C.Y j ⧸ N) * Nat.card N := Nat.mul_le_mul_left _ hle
    _ = Nat.card (C.Y j) := h5.symm

end LatCtx

end CFSG.QuasithinUnique.Ch1.SporLat
