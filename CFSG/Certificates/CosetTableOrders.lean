module

public import CFSG.Certificates.CosetTableAction
public import CFSG.Certificates.CosetTableColumns
public import Certificates.Data.CFSGNative.CosetTable.ActionNative

public section

namespace CFSG.CosetTable

open CFSG.Certificates.CosetEnumeration

variable {m : ℕ}

theorem invConsistentNative_eq : invConsistentNative = invConsistent := rfl

theorem relsClosedNative_eq : relsClosedNative = relsClosed := rfl

@[expose] def colOfCode (ws : List (List (Fin m × Bool))) (x : ℕ) : ℕ :=
  if h : x / 2 < m then colCode ws (⟨x / 2, h⟩, decide (x % 2 = 0)) else 0

theorem letterCode_div (x : Fin m × Bool) : letterCode x / 2 = x.1.val := by
  unfold letterCode
  split <;> omega

theorem letterCode_mod (x : Fin m × Bool) : decide (letterCode x % 2 = 0) = x.2 := by
  obtain ⟨i, b⟩ := x
  cases b <;> simp [letterCode]

theorem colOfCode_letterCode (ws : List (List (Fin m × Bool))) (x : Fin m × Bool) :
    colOfCode ws (letterCode x) = colCode ws x := by
  have hlt : letterCode x / 2 < m := by rw [letterCode_div]; exact x.1.isLt
  unfold colOfCode
  rw [dite_eq_left hlt]
  congr 1
  refine Prod.ext (Fin.ext (letterCode_div x)) (letterCode_mod x)

theorem exists_signed_letter {x : ℕ} (hx : x < 2 * m) :
    ∃ y : Fin m × Bool, letterCode y = x := by
  refine ⟨(⟨x / 2, by omega⟩, decide (x % 2 = 0)), ?_⟩
  unfold letterCode
  by_cases h : x % 2 = 0 <;> simp [h] <;> omega

theorem invCode_letterCode (x : Fin m × Bool) :
    invCode (letterCode x) = letterCode (x.1, !x.2) := by
  obtain ⟨i, b⟩ := x
  cases b
  · have h : Nat.beq (Nat.mod (letterCode (i, false)) 2) 0 = false := by
      have : letterCode (i, false) % 2 = 1 := by simp [letterCode]
      show Nat.beq (letterCode (i, false) % 2) 0 = false
      rw [this]; rfl
    unfold invCode
    rw [h]
    simp [letterCode]
  · have h : Nat.beq (Nat.mod (letterCode (i, true)) 2) 0 = true := by
      have : letterCode (i, true) % 2 = 0 := by simp [letterCode]
      show Nat.beq (letterCode (i, true) % 2) 0 = true
      rw [this]; rfl
    unfold invCode
    rw [h]
    simp [letterCode]

theorem colCode_flip (ws : List (List (Fin m × Bool))) (y : Fin m × Bool) :
    colCode ws ((colRep ws y).1, !(colRep ws y).2) = colCode ws (y.1, !y.2) := by
  by_cases h : isInvol ws y.1 = true
  · have h1 : colRep ws y = (y.1, true) := by simp [colRep, h]
    have h2 : colRep ws (y.1, false) = (y.1, true) := by simp [colRep, h]
    have h3 : colRep ws (y.1, !y.2) = (y.1, true) := by simp [colRep, h]
    rw [h1]
    unfold colCode
    simp only [Bool.not_true]
    rw [h2, h3]
  · have h1 : colRep ws y = y := by simp [colRep, h]
    rw [h1]

theorem colOfCode_lt (ws : List (List (Fin m × Bool))) {x : ℕ} (hx : x < 2 * m) :
    colOfCode ws x < (cols ws).length := by
  obtain ⟨y, rfl⟩ := exists_signed_letter hx
  rw [colOfCode_letterCode]
  exact colCode_lt ws y

theorem colOfCode_invCode (ws : List (List (Fin m × Bool))) {x : ℕ} (hx : x < 2 * m) :
    colOfCode ws (invCode x) = (colInv ws).getD (colOfCode ws x) 0 := by
  obtain ⟨y, rfl⟩ := exists_signed_letter hx
  rw [invCode_letterCode, colOfCode_letterCode, colOfCode_letterCode,
    colInv_getD (colCode_lt ws y)]
  have hget : (cols ws)[colCode ws y]'(colCode_lt ws y) = colRep ws y := getElem_colCode ws y
  rw [hget, colCode_flip]

theorem foldl_colOfCode (ws : List (List (Fin m × Bool))) (st : St) (Lc : ℕ)
    (u : List (Fin m × Bool)) (c : ℕ) :
    (u.map letterCode).foldl (fun c x => st.tab.getD (c * Lc + colOfCode ws x) 0) c =
      (u.map (colCode ws)).foldl (fun c x => st.tab.getD (c * Lc + x) 0) c := by
  induction u generalizing c with
  | nil => rfl
  | cons y u ih =>
    simp only [List.map_cons, List.foldl_cons, colOfCode_letterCode]
    exact ih _

theorem dvd_orderOf_of_walk {ws : List (List (Fin m × Bool))} {st : St}
    (hc : st.complete (cols ws).length = true)
    (hi : invConsistent (cols ws).length (colInv ws) st = true)
    (hrel : relsClosed (cols ws).length st (colCodes ws ws) = true)
    {u : List (Fin m × Bool)} {fuel ℓ : ℕ} (hℓ : 0 < ℓ)
    (hcyc : cycleLength (cols ws).length st.tab (u.map (colCode ws)) 1 fuel = ℓ) :
    ℓ ∣ orderOf (PresentedGroup.mk {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}
      (FreeGroup.mk u)) := by
  set Lc := (cols ws).length with hLc
  let δ : ℕ → ℕ → ℕ := fun c x => st.tab.getD (c * Lc + colOfCode ws x) 0
  have hlive : ∀ c, st.live c = true → ∀ x < 2 * m, st.live (δ c x) = true :=
    fun c hl x hx => St.complete_step hc hl (colOfCode_lt ws hx)
  have hinv : ∀ c, st.live c = true → ∀ x < 2 * m, δ (δ c x) (invCode x) = c := by
    intro c hl x hx
    have := invConsistent_spec hi hl (colOfCode_lt ws hx)
    simp only [δ, colOfCode_invCode ws hx]
    exact this
  have hrel' : ∀ c, st.live c = true → ∀ r ∈ codes ws, r.foldl δ c = c := by
    intro c hl r hr
    simp only [codes, List.mem_map] at hr
    obtain ⟨v, hv, rfl⟩ := hr
    show (v.map letterCode).foldl (fun c x => st.tab.getD (c * Lc + colOfCode ws x) 0) c = c
    rw [foldl_colOfCode]
    exact relsClosed_spec hrel hl (List.mem_map_of_mem hv)
  obtain ⟨ψ, hψ⟩ := exists_action_step ws (fun c => st.live c = true) δ hlive hinv hrel'
  rw [← evalWord_presLetter]
  have hw : ∀ y ∈ u.map letterCode, y < 2 * m := by
    intro y hy
    simp only [List.mem_map] at hy
    obtain ⟨x, -, rfl⟩ := hy
    unfold letterCode
    have := x.1.isLt
    split <;> omega
  have hfun : (fun c' => (u.map letterCode).foldl δ c') =
      (fun d => (u.map (colCode ws)).foldl (fun c x => st.tab.getD (c * Lc + x) 0) d) := by
    funext d
    exact foldl_colOfCode ws st Lc u d
  have hspec := cycleLength_spec Lc st.tab (u.map (colCode ws)) 1 fuel ℓ hcyc hℓ
  refine cycle_dvd_orderOf_step ψ hψ hw ⟨1, St.live_one hc⟩ hℓ ?_ ?_
  · rw [hfun]; exact hspec.1
  · intro j hj hjl
    rw [hfun]; exact hspec.2 j hj hjl

@[expose] def orderCheck (ws : List (List (Fin m × Bool))) (S : List ℕ) (k cap n : ℕ)
    (words : List (List (Fin m × Bool) × ℕ)) (fuel : ℕ) : Bool :=
  let P := colParamsShort ws ((subsetOf m S).map fun x => [(x, true)]) k
  let st := enumerateHLT P cap
  (!st.overflow && st.complete P.L && st.liveCount == n) &&
    invConsistentNative P.L (colInv ws) st && relsClosedNative P.L st (colCodes ws ws) &&
    words.all fun p => cycleLength P.L st.tab (p.1.map (colCode ws)) 1 fuel == p.2

theorem subsetCheckShortC_of_orderCheck {ws : List (List (Fin m × Bool))} {S : List ℕ}
    {k cap n : ℕ} {words : List (List (Fin m × Bool) × ℕ)} {fuel : ℕ}
    (h : orderCheck ws S k cap n words fuel = true) : subsetCheckShortC ws S k cap n = true := by
  unfold orderCheck at h
  unfold subsetCheckShortC checkHLT
  simp only [Bool.and_eq_true] at h ⊢
  obtain ⟨⟨⟨h1, -⟩, -⟩, -⟩ := h
  exact h1

theorem dvd_orderOf_of_orderCheck {ws : List (List (Fin m × Bool))} {S : List ℕ} {k cap n : ℕ}
    {words : List (List (Fin m × Bool) × ℕ)} {fuel : ℕ}
    (h : orderCheck ws S k cap n words fuel = true) {u : List (Fin m × Bool)} {ℓ : ℕ}
    (hmem : (u, ℓ) ∈ words) (hℓ : 0 < ℓ) :
    ℓ ∣ orderOf (PresentedGroup.mk {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}
      (FreeGroup.mk u)) := by
  unfold orderCheck at h
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨-, hc⟩, -⟩, hi⟩, hrel⟩, hwords⟩ := h
  exact dvd_orderOf_of_walk hc hi hrel hℓ (hwords _ hmem)

end CFSG.CosetTable
