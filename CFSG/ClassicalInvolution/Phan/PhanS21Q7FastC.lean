module

public import CFSG.ClassicalInvolution.Phan.PhanS21Q7FastA
public import CFSG.ClassicalInvolution.Phan.PhanS21Q7FastB
public import CFSG.ClassicalInvolution.Phan.PhanS21Q7Sound

public section

namespace CFSG.ClassicalInvolution.PhanB3.S.Std.Q7

open CFSG.ClassicalInvolution.PhanB3.S.Std

theorem anyFrom_eq_true {p : Nat → Bool} {i n : Nat} :
    anyFrom p i n = true ↔ ∃ k, k < n ∧ p (i + k) = true := by
  induction n generalizing i with
  | zero => simp [anyFrom]
  | succ n ih =>
    simp only [anyFrom, Bool.or_eq_true, ih]
    constructor
    · rintro (h | ⟨k, hk, h⟩)
      · exact ⟨0, by omega, h⟩
      · exact ⟨k + 1, by omega, by rwa [show i + (k + 1) = i + 1 + k by omega]⟩
    · rintro ⟨k, hk, h⟩
      rcases k with _ | k
      · exact Or.inl h
      · exact Or.inr ⟨k, by omega, by rwa [show i + 1 + k = i + (k + 1) by omega]⟩

theorem allFrom_eq_true {p : Nat → Bool} {i n : Nat} :
    allFrom p i n = true ↔ ∀ k, k < n → p (i + k) = true := by
  induction n generalizing i with
  | zero => simp [allFrom]
  | succ n ih =>
    simp only [allFrom, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h, h'⟩ k hk
      rcases k with _ | k
      · exact h
      · have := h' k (by omega)
        rwa [show i + 1 + k = i + (k + 1) by omega] at this
    · intro h
      refine ⟨h 0 (by omega), fun k hk => ?_⟩
      rw [show i + 1 + k = i + (k + 1) by omega]
      exact h _ (by omega)

theorem sameVec_eq {u v : N7} (h : sameVec u v = true) : u = v := by
  obtain ⟨u0, u1, u2, u3, u4, u5, u6⟩ := u
  obtain ⟨v0, v1, v2, v3, v4, v5, v6⟩ := v
  simp only [sameVec, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  subst h0 h1 h2 h3 h4 h5 h6
  rfl


theorem hubTable_get {c : N7} {γ β2 : Nat} {r : N7} {βr idx : Nat}
    (h : (hubTable c γ β2 r βr)[idx]!.1 = true) :
    idx < 2401 ∧ (hubTable c γ β2 r βr)[idx]! = hubEntry c γ β2 r βr idx := by
  by_cases hi : idx < 2401
  · refine ⟨hi, ?_⟩
    unfold hubTable
    rw [getElem!_pos _ _ (by simpa using hi)]
    simp
  · exfalso
    unfold hubTable at h
    rw [getElem!_neg _ _ (by simpa using hi)] at h
    exact Bool.noConfusion h

theorem hubEntry_sound {c : N7} (hc : Lt49 c) (hc3 : c.x3 = 1) {β2 : Nat} (hβ2 : β2 < 49)
    {r : N7} (hr : Lt49 r) {i : Nat} (hi : i < 2401)
    (h : (hubEntry c (herN c c) β2 r (hDiag r) i).1 = true) :
    Lt49 (hubEntry c (herN c c) β2 r (hDiag r) i).2.1 ∧
      (hubEntry c (herN c c) β2 r (hDiag r) i).2.1 ∈ q7Pts c ∧
      colN (hubEntry c (herN c c) β2 r (hDiag r) i).2.1 r = true ∧
      (hubEntry c (herN c c) β2 r (hDiag r) i).2.2 =
        hDiag (hubEntry c (herN c c) β2 r (hDiag r) i).2.1 := by
  have h5 : i / 49 < 49 := by omega
  have h6 : i % 49 < 49 := by omega
  have hvL : Lt49 (mkA c β2 (i / 49) (i % 49)) := lt49_mkA c hβ2 h5 h6
  simp only [hubEntry, Bool.and_eq_true] at h ⊢
  obtain ⟨hv, hadj⟩ := h
  refine ⟨hvL, (mkA_mem_iff hc hc3 hβ2 h5 h6).2 hv, ?_, trivial⟩
  rw [← adjF_eq_colN hvL hr]
  exact hadj

theorem hubNbr_sound {c : N7} (hc : Lt49 c) (hc3 : c.x3 = 1) {β2 : Nat} (hβ2 : β2 < 49)
    {r : N7} (hr : Lt49 r) {u : N7} (hu : Lt49 u)
    (h : hubNbr (hubTable c (herN c c) β2 r (hDiag r)) β2 u (hDiag u) = true) :
    ∃ v, v ∈ q7Pts c ∧ colN v r = true ∧ colN u v = true := by
  unfold hubNbr at h
  obtain ⟨t, _, h⟩ := anyFrom_eq_true.1 h
  unfold hubTryH at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨he, hadj⟩ := h
  obtain ⟨hidx, heq⟩ := hubTable_get he
  rw [heq] at he hadj
  obtain ⟨hvL, hvmem, hcol, hbv⟩ := hubEntry_sound hc hc3 hβ2 hr hidx he
  rw [hbv] at hadj
  refine ⟨_, hvmem, hcol, ?_⟩
  rw [← adjF_eq_colN hu hvL]
  exact hadj

theorem walk2_of_hubNbr {c : N7} (hc : Lt49 c) (hc3 : c.x3 = 1) {β2 : Nat} (hβ2 : β2 < 49)
    {r : N7} (hr : Lt49 r) {u : N7} (hu : Lt49 u) (huL : u ∈ q7Pts c)
    (h : hubNbr (hubTable c (herN c c) β2 r (hDiag r)) β2 u (hDiag u) = true) :
    Wk colN (· ∈ q7Pts c) 2 r u := by
  obtain ⟨v, hv, hvr, huv⟩ := hubNbr_sound hc hc3 hβ2 hr hu h
  exact Wk.cons (colN_symm hvr) hv (Wk.cons (colN_symm huv) huL (Wk.nil u))

@[expose] def GoodW (c r : N7) (wl : List (N7 × Nat)) : Prop :=
  ∀ p ∈ wl, Lt49 p.1 ∧ p.1 ∈ q7Pts c ∧ p.2 = hDiag p.1 ∧
    ∃ n, n ≤ 2 ∧ Wk colN (· ∈ q7Pts c) n r p.1

theorem fbA_sound {c : N7} (hc : Lt49 c) (hc3 : c.x3 = 1) {β2 : Nat} (hβ2 : β2 < 49) {r : N7}
    (hr : Lt49 r) {k : Nat} {p : N7 × Nat}
    (h : fbA c (herN c c) (hubTable c (herN c c) β2 r (hDiag r)) β2 k = some p) :
    Lt49 p.1 ∧ p.1 ∈ q7Pts c ∧ p.2 = hDiag p.1 ∧
      ∃ n, n ≤ 2 ∧ Wk colN (· ∈ q7Pts c) n r p.1 := by
  unfold fbA at h
  dsimp only at h
  split at h
  · rename_i hcond
    cases h
    simp only [Bool.and_eq_true] at hcond
    obtain ⟨hv, hn⟩ := hcond
    have h2 : k * 117 % 117649 / 2401 < 49 := by omega
    have h5 : k * 117 % 117649 / 49 % 49 < 49 := Nat.mod_lt _ (by norm_num)
    have h6 : k * 117 % 117649 % 49 < 49 := Nat.mod_lt _ (by norm_num)
    have hwL := lt49_mkA c h2 h5 h6
    have hwmem := (mkA_mem_iff hc hc3 h2 h5 h6).2 hv
    exact ⟨hwL, hwmem, rfl, 2, Nat.le_refl _, walk2_of_hubNbr hc hc3 hβ2 hr hwL hwmem hn⟩
  · cases h

theorem fbB_sound {c : N7} (hc : Lt49 c) (hc3 : c.x3 = 1) {β2 : Nat} (hβ2 : β2 < 49) {r : N7}
    (hr : Lt49 r) {k : Nat} (hk : k < 800) {p : N7 × Nat}
    (h : fbB c (herN c c) (hubTable c (herN c c) β2 r (hDiag r)) β2 k = some p) :
    Lt49 p.1 ∧ p.1 ∈ q7Pts c ∧ p.2 = hDiag p.1 ∧
      ∃ n, n ≤ 2 ∧ Wk colN (· ∈ q7Pts c) n r p.1 := by
  unfold fbB at h
  dsimp only at h
  split at h
  · rename_i hcond
    cases h
    simp only [Bool.and_eq_true] at hcond
    obtain ⟨hv, hn⟩ := hcond
    have h4 : k * 3 / 49 < 49 := by omega
    have h6 : k * 3 % 49 < 49 := Nat.mod_lt _ (by norm_num)
    have hwL := lt49_mkB c h4 h6
    have hwmem := (mkB_mem_iff hc hc3 h4 h6).2 hv
    exact ⟨hwL, hwmem, rfl, 2, Nat.le_refl _, walk2_of_hubNbr hc hc3 hβ2 hr hwL hwmem hn⟩
  · cases h

theorem fallback_good {c : N7} (hc : Lt49 c) (hc3 : c.x3 = 1) {β2 : Nat} (hβ2 : β2 < 49) {r : N7}
    (hr : Lt49 r) :
    GoodW c r (fallbackA c (herN c c) (hubTable c (herN c c) β2 r (hDiag r)) β2 ++
      fallbackB c (herN c c) (hubTable c (herN c c) β2 r (hDiag r)) β2) := by
  intro p hp
  rcases List.mem_append.1 hp with hp | hp
  · obtain ⟨k, _, hk⟩ := List.mem_filterMap.1 hp
    exact fbA_sound hc hc3 hβ2 hr hk
  · obtain ⟨k, hk, hk'⟩ := List.mem_filterMap.1 hp
    exact fbB_sound hc hc3 hβ2 hr (List.mem_range.1 hk) hk'


theorem allFrom_zero {p : Nat → Bool} {n : Nat} :
    allFrom p 0 n = true ↔ ∀ k, k < n → p k = true := by
  rw [allFrom_eq_true]
  simp

theorem reachOk_walk {c : N7} (hc : Lt49 c) (hc3 : c.x3 = 1) {β2 : Nat} (hβ2 : β2 < 49)
    {r : N7} (hr : Lt49 r) {wl : List (N7 × Nat)} (hwl : GoodW c r wl) {u : N7} (hu : Lt49 u)
    (huL : u ∈ q7Pts c) (hvtx : vtxF c (herN c c) u (hDiag u) = true)
    (h : reachOk c (herN c c) r (hDiag r) β2 (hubTable c (herN c c) β2 r (hDiag r)) wl u =
      true) :
    ∃ n, n ≤ 3 ∧ Wk colN (· ∈ q7Pts c) n r u := by
  unfold reachOk at h
  dsimp only at h
  rw [hvtx] at h
  simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true] at h
  rcases h with ((h | h) | h) | h
  · have := sameVec_eq h
    subst this
    exact ⟨0, by omega, Wk.nil _⟩
  · have hcol : colN u r = true := by
      rw [← adjF_eq_colN hu hr]
      exact h
    exact ⟨1, by omega, Wk.single (colN_symm hcol) huL⟩
  · exact ⟨2, by omega, walk2_of_hubNbr hc hc3 hβ2 hr hu huL h⟩
  · obtain ⟨p, hp, hadj⟩ := List.any_eq_true.1 h
    obtain ⟨hpL, _, hp2, n, hn, hw⟩ := hwl p hp
    have hcol : colN u p.1 = true := by
      rw [← adjF_eq_colN hu hpL, ← hp2]
      exact hadj
    exact ⟨n + 1, by omega, hw.snoc (colN_symm hcol) huL⟩

theorem mem_q7Cands_cases {c p : N7} (hc : Lt49 c) (hp : p ∈ q7Cands c) :
    (∃ x2, x2 < 49 ∧ ∃ x5, x5 < 49 ∧ ∃ x6, x6 < 49 ∧ p = mkA c x2 x5 x6) ∨
      (∃ x4, x4 < 49 ∧ ∃ x6, x6 < 49 ∧ p = mkB c x4 x6) ∨
      (∃ x5, x5 < 49 ∧ p = mkC c x5) ∨ p = mkD c := by
  simp only [q7Cands, candsA, candsB, candsC, candsD, List.mem_append, List.mem_flatMap,
    List.mem_map, List.mem_range, List.mem_singleton] at hp
  rcases hp with ((⟨x2, h2, x5, h5, x6, h6, e⟩ | ⟨x4, h4, x6, h6, e⟩) | ⟨x5, h5, e⟩) | e
  · exact Or.inl ⟨x2, h2, x5, h5, x6, h6, by rw [mkA_eq hc h2 h5 h6, e]⟩
  · exact Or.inr (Or.inl ⟨x4, h4, x6, h6, by rw [mkB_eq hc h4 h6, e]⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨x5, h5, by rw [mkC_eq hc h5, e]⟩))
  · exact Or.inr (Or.inr (Or.inr (by rw [mkD_eq hc, e])))

theorem rowLoops_sound {c : N7} (hc : Lt49 c) (hc3 : c.x3 = 1) {β2 : Nat} (hβ2 : β2 < 49)
    {r : N7} (hr : Lt49 r) {wl : List (N7 × Nat)} (hwl : GoodW c r wl)
    (h : rowLoops c (herN c c) r (hDiag r) β2 (hubTable c (herN c c) β2 r (hDiag r)) wl =
      true) :
    ∀ p ∈ q7Pts c, ∃ n, n ≤ 3 ∧ Wk colN (· ∈ q7Pts c) n r p := by
  intro p hp
  have hpC : p ∈ q7Cands c := (List.mem_filter.1 hp).1
  unfold rowLoops at h
  dsimp only at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨hA, hB⟩, hC⟩, hD⟩ := h
  rcases mem_q7Cands_cases hc hpC with ⟨x2, h2, x5, h5, x6, h6, e⟩ | ⟨x4, h4, x6, h6, e⟩ |
    ⟨x5, h5, e⟩ | e
  · subst e
    have hok := allFrom_zero.1 (allFrom_zero.1 (allFrom_zero.1 hA x2 h2) x5 h5) x6 h6
    exact reachOk_walk hc hc3 hβ2 hr hwl (lt49_mkA c h2 h5 h6) hp
      ((mkA_mem_iff hc hc3 h2 h5 h6).1 hp) hok
  · subst e
    have hok := allFrom_zero.1 (allFrom_zero.1 hB x4 h4) x6 h6
    exact reachOk_walk hc hc3 hβ2 hr hwl (lt49_mkB c h4 h6) hp
      ((mkB_mem_iff hc hc3 h4 h6).1 hp) hok
  · subst e
    have hok := allFrom_zero.1 hC x5 h5
    exact reachOk_walk hc hc3 hβ2 hr hwl (lt49_mkC c h5) hp
      ((mkC_mem_iff hc hc3 h5).1 hp) hok
  · subst e
    exact reachOk_walk hc hc3 hβ2 hr hwl (lt49_mkD c) hp ((mkD_mem_iff hc hc3).1 hp) hD

theorem rootIdx_spec {c : N7} {γ k : Nat} (h : rootIdx c γ = some k) :
    k < 48 ∧ vtxF c γ (mkC c (k + 1)) (hDiag (mkC c (k + 1))) = true := by
  unfold rootIdx at h
  have h1 := List.find?_some h
  have h2 := List.mem_of_find?_eq_some h
  exact ⟨List.mem_range.1 h2, h1⟩

theorem rowCore_sound {c : N7} (hc : Lt49 c) (hc3 : c.x3 = 1) {k : Nat} (hk : k < 48)
    (hr : vtxF c (herN c c) (mkC c (k + 1)) (hDiag (mkC c (k + 1))) = true)
    (h : rowCore c (herN c c) k = true) :
    ∃ r, r ∈ q7Pts c ∧ ∀ p ∈ q7Pts c, ∃ n, n ≤ 3 ∧ Wk colN (· ∈ q7Pts c) n r p := by
  have hk1 : k + 1 < 49 := by omega
  have hrL : mkC c (k + 1) ∈ q7Pts c := (mkC_mem_iff hc hc3 hk1).2 hr
  have hrlt := lt49_mkC c hk1
  have hβ2 : fNeg (fInv (k + 1)) < 49 := fNeg_lt _
  refine ⟨mkC c (k + 1), hrL, ?_⟩
  unfold rowCore at h
  dsimp only at h
  exact rowLoops_sound hc hc3 hβ2 hrlt (fallback_good hc hc3 hβ2 hrlt) h

theorem q7FastRow_sound {row : Array Nat} (h : q7FastRow row = true) :
    (rowN row).x3 = 1 ∧ isFFN (rowN row) = true ∧
      ∃ r, r ∈ q7Pts (rowN row) ∧ ∀ p ∈ q7Pts (rowN row),
        ∃ n, n ≤ 3 ∧ Wk colN (· ∈ q7Pts (rowN row)) n r p := by
  unfold q7FastRow at h
  dsimp only at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨hcl, hc3⟩, hff⟩, hm⟩ := h
  refine ⟨hc3, hff, ?_⟩
  have hc := (coordsLt_iff _).1 hcl
  rcases hroot : rootIdx (rowN row) (herN (rowN row) (rowN row)) with _ | k
  · rw [hroot] at hm
    exact absurd hm (by simp)
  · rw [hroot] at hm
    obtain ⟨hk, hr⟩ := rootIdx_spec hroot
    exact rowCore_sound hc hc3 hk hr hm


theorem nodup_flatMap_of_key {α : Type} {l : List Nat} {f : Nat → List α} {key : α → Nat}
    (hl : l.Nodup) (hf : ∀ x ∈ l, (f x).Nodup) (hk : ∀ x ∈ l, ∀ y ∈ f x, key y = x) :
    (l.flatMap f).Nodup := by
  rw [List.nodup_flatMap]
  refine ⟨hf, List.Pairwise.imp_of_mem ?_ hl⟩
  intro a b ha hb hab y h1 h2
  exact hab ((hk a ha y h1).symm.trans (hk b hb y h2))

theorem candsA_nodup (c : N7) : (candsA c).Nodup := by
  unfold candsA
  refine nodup_flatMap_of_key (key := N7.x2) List.nodup_range (fun x2 _ => ?_) ?_
  · refine nodup_flatMap_of_key (key := N7.x5) List.nodup_range (fun x5 _ => ?_) ?_
    · exact List.Nodup.map (fun a b h => congrArg N7.x6 h) List.nodup_range
    · intro x5 _ y hy
      obtain ⟨x6, _, rfl⟩ := List.mem_map.1 hy
      rfl
  · intro x2 _ y hy
    obtain ⟨x5, _, hy⟩ := List.mem_flatMap.1 hy
    obtain ⟨x6, _, rfl⟩ := List.mem_map.1 hy
    rfl

theorem candsB_nodup (c : N7) : (candsB c).Nodup := by
  unfold candsB
  refine nodup_flatMap_of_key (key := N7.x4) List.nodup_range (fun x4 _ => ?_) ?_
  · exact List.Nodup.map (fun a b h => congrArg N7.x6 h) List.nodup_range
  · intro x4 _ y hy
    obtain ⟨x6, _, rfl⟩ := List.mem_map.1 hy
    rfl

theorem candsC_nodup (c : N7) : (candsC c).Nodup := by
  unfold candsC
  exact List.Nodup.map (fun a b h => congrArg N7.x5 h) List.nodup_range

theorem mem_candsA_x1 {c y : N7} (h : y ∈ candsA c) : y.x1 = 1 := by
  simp only [candsA, List.mem_flatMap, List.mem_map, List.mem_range] at h
  obtain ⟨x2, _, x5, _, x6, _, rfl⟩ := h
  rfl

theorem mem_candsB_x {c y : N7} (h : y ∈ candsB c) : y.x1 = 0 ∧ y.x2 = 1 := by
  simp only [candsB, List.mem_flatMap, List.mem_map, List.mem_range] at h
  obtain ⟨x4, _, x6, _, rfl⟩ := h
  exact ⟨rfl, rfl⟩

theorem mem_candsC_x {c y : N7} (h : y ∈ candsC c) : y.x1 = 0 ∧ y.x2 = 0 ∧ y.x4 = 1 := by
  simp only [candsC, List.mem_map, List.mem_range] at h
  obtain ⟨x5, _, rfl⟩ := h
  exact ⟨rfl, rfl, rfl⟩

theorem mem_candsD_x {c y : N7} (h : y ∈ candsD c) : y.x1 = 0 ∧ y.x2 = 0 ∧ y.x4 = 0 := by
  simp only [candsD, List.mem_singleton] at h
  subst h
  exact ⟨rfl, rfl, rfl⟩

theorem q7Cands_nodup (c : N7) : (q7Cands c).Nodup := by
  unfold q7Cands
  refine List.nodup_append.2 ⟨List.nodup_append.2 ⟨List.nodup_append.2 ⟨candsA_nodup c,
    candsB_nodup c, ?_⟩, candsC_nodup c, ?_⟩, ?_, ?_⟩
  · intro a ha b hb hab
    have h1 := mem_candsA_x1 ha
    have h2 := (mem_candsB_x hb).1
    rw [hab] at h1
    omega
  · intro a ha b hb hab
    rcases List.mem_append.1 ha with ha | ha
    · have h1 := mem_candsA_x1 ha
      have h2 := (mem_candsC_x hb).1
      rw [hab] at h1
      omega
    · have h1 := (mem_candsB_x ha).2
      have h2 := (mem_candsC_x hb).2.1
      rw [hab] at h1
      omega
  · simp [candsD]
  · intro a ha b hb hab
    rcases List.mem_append.1 ha with ha | ha
    · rcases List.mem_append.1 ha with ha | ha
      · have h1 := mem_candsA_x1 ha
        have h2 := (mem_candsD_x hb).1
        rw [hab] at h1
        omega
      · have h1 := (mem_candsB_x ha).2
        have h2 := (mem_candsD_x hb).2.1
        rw [hab] at h1
        omega
    · have h1 := (mem_candsC_x ha).2.2
      have h2 := (mem_candsD_x hb).2.2
      rw [hab] at h1
      omega

theorem q7Pts_nodup (c : N7) : (q7Pts c).Nodup := (q7Cands_nodup c).filter _


theorem bfsOk_of_fast_row {row : Array Nat} (h : q7FastRow row = true) :
    bfsOk colN (q7Pts (rowN row)) = true := by
  obtain ⟨_, _, r, hrL, hwalk⟩ := q7FastRow_sound h
  rcases hL : q7Pts (rowN row) with _ | ⟨r₀, rest⟩
  · rfl
  · apply bfsOk_of_walks (r := r₀) (rest := rest)
    · have hnd := q7Pts_nodup (rowN row)
      rw [hL] at hnd
      exact (List.nodup_cons.1 hnd).1
    · intro u hu
      have hr₀L : r₀ ∈ q7Pts (rowN row) := by
        rw [hL]
        exact List.mem_cons_self
      have huL : u ∈ q7Pts (rowN row) := by
        rw [hL]
        exact List.mem_cons_of_mem _ hu
      obtain ⟨n1, hn1, w1⟩ := hwalk r₀ hr₀L
      obtain ⟨n2, hn2, w2⟩ := hwalk u huL
      have w1' := w1.symm (fun a b hab => colN_symm hab) hrL
      refine ⟨n1 + n2, by omega, ?_⟩
      rw [hL] at w1' w2
      exact w1'.trans w2

theorem q7RowCheck_of_fast {row : Array Nat} (h : q7FastRow row = true) :
    q7RowCheck row = true := by
  obtain ⟨hc3, hff, _⟩ := q7FastRow_sound h
  unfold q7RowCheck
  simp only [Bool.and_eq_true, beq_iff_eq]
  exact ⟨⟨hc3, hff⟩, bfsOk_of_fast_row h⟩

theorem q7MuCheck_of_fast (h : q7FastCheck = true) : q7MuCheck = true := by
  unfold q7FastCheck at h
  unfold q7MuCheck
  exact Array.all_eq_true.2 fun i hi => q7RowCheck_of_fast (Array.all_eq_true.1 h i hi)

end CFSG.ClassicalInvolution.PhanB3.S.Std.Q7
