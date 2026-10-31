
module

public import CFSG.LieType.Multipliers.U43Bridge
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43InvCheck

@[expose] public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43Inv

open CFSG.LieType.Multipliers.U43 CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

theorem rep_inv' {t : Array ℕ} {g : X₀} (h : Rep 820 t (psi g))
    (hi : isInvA 820 t (invCand 820 t) = true) : Rep 820 (invCand 820 t) (psi g⁻¹) := by
  have h1 := rep_permOfArr hi
  rw [map_inv, ← Rep.unique h1.1 h]
  exact h1.2

theorem rep_one : Rep 820 (idA 820) (psi (1 : X₀)) := by
  rw [map_one]
  exact rep_idA

noncomputable def letElt (l : ℕ) : X₀ :=
  if l = 0 then xElt else if l = 1 then yElt else if l = 2 then xElt⁻¹ else yElt⁻¹

theorem rep_letTab (l : ℕ) :
    Rep 820 (letTab l) (psi (letElt l)) := by
  unfold letTab letElt
  split_ifs
  · exact rep_tabA
  · exact rep_tabB
  · exact rep_inv' rep_tabA isInvA_tabA
  · exact rep_inv' rep_tabB isInvA_tabB

noncomputable def wordElt (w : List ℕ) : X₀ := w.foldl (fun g l => g * letElt l) 1

theorem rep_foldl (w : List ℕ) : ∀ (t : Array ℕ) (g : X₀),
    Rep 820 t (psi g) → Rep 820 (w.foldl (fun t l => compA 820 t (letTab l)) t)
      (psi (w.foldl (fun g l => g * letElt l) g)) := by
  induction w with
  | nil => intro t g h; exact h
  | cons l w ih =>
    intro t g h
    have h' : Rep 820 (compA 820 t (letTab l)) (psi (g * letElt l)) := by
      rw [map_mul]
      exact rep_compA h (rep_letTab l)
    rw [List.foldl_cons, List.foldl_cons]
    exact ih _ _ h'

theorem rep_wordTab (w : List ℕ) :
    Rep 820 (wordTab w) (psi (wordElt w)) :=
  rep_foldl w _ _ rep_one

noncomputable def treeG (root : X₀) (step : X₀ → ℕ → X₀) (par lab : Array ℕ) (nl : ℕ) :
    ℕ → ℕ → X₀
  | 0, _ => root
  | f + 1, k => if k = 0 then root else
      step (treeG root step par lab nl f par[k]!) (lab[k]! % nl)

theorem rep_treeG {rT : Array ℕ} {rG : X₀} (hr : Rep 820 rT (psi rG)) {sT : Array ℕ → ℕ → Array ℕ}
    {sG : X₀ → ℕ → X₀} {nl : ℕ} (hnl : 0 < nl)
    (hs : ∀ t g l, l < nl → Rep 820 t (psi g) → Rep 820 (sT t l) (psi (sG g l)))
    (par lab : Array ℕ) (f : ℕ) :
    ∀ k, Rep 820 (treeTab rT sT par lab nl f k) (psi (treeG rG sG par lab nl f k)) := by
  induction f with
  | zero => intro k; exact hr
  | succ f ih =>
    intro k
    simp only [treeTab, treeG]
    split_ifs
    · exact hr
    · exact hs _ _ _ (Nat.mod_lt _ hnl) (ih _)

theorem treeG_mem {Q : X₀ → Prop} {rG : X₀} (hr : Q rG) {sG : X₀ → ℕ → X₀} {nl : ℕ}
    (hnl : 0 < nl) (hs : ∀ g l, l < nl → Q g → Q (sG g l)) (par lab : Array ℕ) (f : ℕ) :
    ∀ k, Q (treeG rG sG par lab nl f k) := by
  induction f with
  | zero => intro k; exact hr
  | succ f ih =>
    intro k
    simp only [treeG]
    split_ifs
    · exact hr
    · exact hs _ _ (Nat.mod_lt _ hnl) (ih _)

theorem closedOK_spec {T : ℕ → Array ℕ} {tbl : Array ℕ} {n nl : ℕ}
    {step : Array ℕ → ℕ → Array ℕ} (h : closedOK T tbl n nl step = true) :
    ∀ k < n, ∀ l < nl, tbl[k * nl + l]! < n ∧
      eqA 820 (T tbl[k * nl + l]!) (step (T k) l) = true := by
  intro k hk l hl
  simp only [closedOK, List.all_eq_true, List.mem_range, Bool.and_eq_true,
    decide_eq_true_eq] at h
  exact h k hk l hl

theorem distinctOK_spec {T : ℕ → Array ℕ} {n : ℕ} (h : distinctOK T n = true) :
    ∀ i < n, ∀ j < n, fpKey (T i) = fpKey (T j) → i = j := by
  unfold distinctOK at h
  have := of_decide_eq_true h
  rw [List.nodup_map_iff_inj_on List.nodup_range] at this
  intro i hi j hj hij
  exact this i (List.mem_range.2 hi) j (List.mem_range.2 hj) hij

theorem getElem!_map_lt {α β : Type*} [Inhabited β] (f : α → β) (l : List α) {j : ℕ}
    (hj : j < l.length) : (l.map f)[j]! = f l[j] := by
  rw [getElem!_pos _ j (by simpa using hj)]
  simp

theorem getD_map_lt {α : Type*} (f : α → X₀) (l : List α) {j : ℕ} (hj : j < l.length) :
    (l.map f).getD j 1 = f l[j] := by
  rw [List.getD_eq_getElem _ _ (by simpa using hj)]
  simp

noncomputable def mulStepG (gs : List X₀) (g : X₀) (l : ℕ) : X₀ :=
  if l % 2 = 0 then g * gs.getD (l / 2) 1 else g * (gs.getD (l / 2) 1)⁻¹

theorem rep_mulStep {ts : List (Array ℕ)} {gs : List X₀} (_hlen : ts.length = gs.length)
    (hrep : ∀ j < gs.length, Rep 820 ts[j]! (psi (gs.getD j 1)))
    (hinv : ∀ j < gs.length, isInvA 820 ts[j]! (invCand 820 ts[j]!) = true)
    (t : Array ℕ) (g : X₀) (l : ℕ) (hl : l < 2 * gs.length) (h : Rep 820 t (psi g)) :
    Rep 820 (mulStep ts t l) (psi (mulStepG gs g l)) := by
  have hj : l / 2 < gs.length := by omega
  unfold mulStep mulStepG
  split_ifs
  · rw [map_mul]
    exact rep_compA h (hrep _ hj)
  · rw [map_mul]
    exact rep_compA h (rep_inv' (hrep _ hj) (hinv _ hj))

theorem enum_spec {ts : List (Array ℕ)} {gs : List X₀}
    (hlen : ts.length = gs.length)
    (hrep : ∀ j < gs.length, Rep 820 ts[j]! (psi (gs.getD j 1)))
    (hinv : ∀ j < gs.length, isInvA 820 ts[j]! (invCand 820 ts[j]!) = true)
    (hpos : 0 < gs.length) {par lab tbl : Array ℕ} {n : ℕ} (hn : 0 < n)
    (hcl : closedOK (fun k => treeTab (idA 820) (mulStep ts) par lab (2 * ts.length) fuel k) tbl n
      (2 * ts.length) (mulStep ts) = true)
    (hdist : distinctOK (fun k => treeTab (idA 820) (mulStep ts) par lab (2 * ts.length) fuel k)
      n = true) :
    (∀ k, treeG 1 (mulStepG gs) par lab (2 * gs.length) fuel k ∈
        Subgroup.closure {g | g ∈ gs}) ∧
    (∀ h ∈ Subgroup.closure {g | g ∈ gs}, ∃ k < n,
        treeG 1 (mulStepG gs) par lab (2 * gs.length) fuel k = h) ∧
    (∀ i < n, ∀ j < n, treeG 1 (mulStepG gs) par lab (2 * gs.length) fuel i =
        treeG 1 (mulStepG gs) par lab (2 * gs.length) fuel j → i = j) := by
  have hnl : 0 < 2 * gs.length := by omega
  rw [hlen] at hcl hdist
  have hmem : ∀ g l, l < 2 * gs.length → g ∈ Subgroup.closure {g | g ∈ gs} →
      mulStepG gs g l ∈ Subgroup.closure {g | g ∈ gs} := by
    intro g l hl hg
    have hj : l / 2 < gs.length := by omega
    have hy : gs.getD (l / 2) 1 ∈ Subgroup.closure {g | g ∈ gs} := by
      apply Subgroup.subset_closure
      rw [List.getD_eq_getElem _ _ hj]
      exact List.getElem_mem hj
    unfold mulStepG
    split_ifs
    · exact mul_mem hg hy
    · exact mul_mem hg (inv_mem hy)
  have hrepT : ∀ k, Rep 820 (treeTab (idA 820) (mulStep ts) par lab (2 * gs.length) fuel k)
      (psi (treeG 1 (mulStepG gs) par lab (2 * gs.length) fuel k)) :=
    rep_treeG rep_one hnl (fun t g l hl h => rep_mulStep hlen hrep hinv t g l hl h) par lab fuel
  have hdist' := distinctOK_spec hdist
  have hcl' := closedOK_spec hcl
  have hstep : ∀ k < n, ∀ l < 2 * gs.length, ∃ k' < n,
      treeG 1 (mulStepG gs) par lab (2 * gs.length) fuel k' =
        mulStepG gs (treeG 1 (mulStepG gs) par lab (2 * gs.length) fuel k) l := by
    intro k hk l hl
    obtain ⟨hk', heq⟩ := hcl' k hk l hl
    refine ⟨tbl[k * (2 * gs.length) + l]!, hk', ?_⟩
    have hr2 := rep_mulStep hlen hrep hinv _ _ l hl (hrepT k)
    have := (eqA_iff (hrepT _) hr2).1 heq
    exact psi_injective this
  refine ⟨treeG_mem (Q := (· ∈ Subgroup.closure {g | g ∈ gs})) (one_mem _) hnl hmem par lab fuel,
    ?_, ?_⟩
  · intro h hh
    induction hh using Subgroup.closure_induction_right with
    | one => exact ⟨0, hn, by simp [treeG, fuel]⟩
    | mul_right x hx y hy ih =>
      obtain ⟨k, hk, rfl⟩ := ih
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hy
      obtain ⟨k', hk', hk'e⟩ := hstep k hk (2 * j) (by omega)
      refine ⟨k', hk', ?_⟩
      rw [hk'e]
      have h1 : (2 * j) % 2 = 0 := by omega
      have h2 : (2 * j) / 2 = j := by omega
      simp [mulStepG, h1, h2, List.getElem?_eq_getElem hj]
    | mul_inv_cancel x hx y hy ih =>
      obtain ⟨k, hk, rfl⟩ := ih
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hy
      obtain ⟨k', hk', hk'e⟩ := hstep k hk (2 * j + 1) (by omega)
      refine ⟨k', hk', ?_⟩
      rw [hk'e]
      have h1 : (2 * j + 1) % 2 = 1 := by omega
      have h2 : (2 * j + 1) / 2 = j := by omega
      simp [mulStepG, h1, h2, List.getElem?_eq_getElem hj]
  · intro i hi j hj hij
    apply hdist' i hi j hj
    have key : ∀ (x : ℕ) (hx : x < 820),
        (treeTab (idA 820) (mulStep ts) par lab (2 * gs.length) fuel i)[x]! =
          (treeTab (idA 820) (mulStep ts) par lab (2 * gs.length) fuel j)[x]! := fun x hx => by
      rw [(hrepT i).apply hx, (hrepT j).apply hx, hij]
    simp [fpKey, key 0 (by norm_num), key 1 (by norm_num), key 9 (by norm_num)]

structure CheckFacts : Prop where
  gens : ∀ j < hGens.length, isInvA 820 hGens[j]! (invCand 820 hGens[j]!) = true ∧
    eqA 820 (compA 820 hGens[j]! tabA) (compA 820 tabA hGens[j]!) = true
  hpos : 0 < hGens.length
  hdist : distinctOK hTab 1152 = true
  hclosed : closedOK hTab hTbl 1152 (2 * hGens.length) (mulStep hGens) = true
  ppos : 0 < pGens.length
  pinv : ∀ j < pGens.length, isInvA 820 pGens[j]! (invCand 820 pGens[j]!) = true
  pdist : distinctOK pTab 128 = true
  pclosed : closedOK pTab pTbl 128 (2 * pGens.length) (mulStep pGens) = true
  cdist : distinctOK cTab 2835 = true
  fuse : ∀ k < 128, fuseOK k = true
  f2 : ∀ k < 1152, f2OK k = true
  g0 : g0OK = true

noncomputable def hGensG : List X₀ := hGenWords.map wordElt

noncomputable def hElt (k : ℕ) : X₀ :=
  treeG 1 (mulStepG hGensG) hPar hLab (2 * hGensG.length) fuel k

noncomputable def hSub : Subgroup X₀ := Subgroup.closure {g | g ∈ hGensG}

theorem hGens_length : hGens.length = hGensG.length := by simp [hGens, hGensG]

theorem rep_hGens :
    ∀ j < hGensG.length, Rep 820 hGens[j]! (psi (hGensG.getD j 1)) := by
  intro j hj
  have hj' : j < hGenWords.length := by simpa [hGensG] using hj
  rw [hGens, getElem!_map_lt _ _ hj', hGensG, getD_map_lt _ _ hj']
  exact rep_wordTab _

noncomputable def pGensG : List X₀ := pGenIdx.map hElt

noncomputable def pElt (k : ℕ) : X₀ :=
  treeG 1 (mulStepG pGensG) pPar pLab (2 * pGensG.length) fuel k

noncomputable def pSub : Subgroup X₀ := Subgroup.closure {g | g ∈ pGensG}

theorem pGens_length : pGens.length = pGensG.length := by simp [pGens, pGensG]

noncomputable def conjStepG (g : X₀) (l : ℕ) : X₀ := letElt l * g * letElt (l ^^^ 2)

noncomputable def cElt (k : ℕ) : X₀ := treeG xElt conjStepG cPar cLab 4 fuel k

theorem rep_cTab (k : ℕ) : Rep 820 (cTab k) (psi (cElt k)) := by
  unfold cTab cElt
  refine rep_treeG rep_tabA (by norm_num) (fun t g l hl h => ?_) cPar cLab fuel k
  unfold conjStep conjStepG
  rw [map_mul, map_mul]
  exact rep_compA (rep_compA (rep_letTab l) h) (rep_letTab _)

theorem letElt_xor {l : ℕ} (hl : l < 4) : letElt (l ^^^ 2) = (letElt l)⁻¹ := by
  interval_cases l <;> simp [letElt]

theorem cElt_conj : ∀ k, ∃ d : X₀, cElt k = d * xElt * d⁻¹ := by
  intro k
  refine treeG_mem (Q := fun g => ∃ d : X₀, g = d * xElt * d⁻¹) ⟨1, by simp⟩ (by norm_num)
    (fun g l hl => ?_) cPar cLab fuel k
  rintro ⟨d, rfl⟩
  refine ⟨letElt l * d, ?_⟩
  unfold conjStepG
  rw [letElt_xor hl]
  group

theorem eqA_one_iff {t : Array ℕ} {g : X₀}
    (h : Rep 820 t (psi g)) : eqA 820 t (idA 820) = true ↔ g = 1 := by
  rw [eqA_iff h rep_one]
  exact ⟨fun h' => psi_injective h', fun h' => by rw [h']⟩

theorem isInvol_iff {t : Array ℕ} {g : X₀}
    (h : Rep 820 t (psi g)) : isInvol t = true ↔ g * g = 1 ∧ g ≠ 1 := by
  have h2 : Rep 820 (compA 820 t t) (psi (g * g)) := by
    rw [map_mul]
    exact rep_compA h h
  have h3 : (!eqA 820 t (idA 820)) = true ↔ g ≠ 1 := by
    rw [Bool.not_eq_true', Bool.eq_false_iff, Ne, eqA_one_iff h]
  unfold isInvol
  rw [Bool.and_eq_true, eqA_one_iff h2, h3]

theorem rep_powTab {t : Array ℕ} {g : X₀}
    (h : Rep 820 t (psi g)) : ∀ k, Rep 820 (powTab t k) (psi (g ^ k))
  | 0 => by
    rw [pow_zero]
    exact rep_one
  | k + 1 => by
    rw [pow_succ', map_mul]
    exact rep_compA h (rep_powTab h k)

noncomputable def g0Elt : X₀ := wordElt g0Word

theorem conj_comm_iff {G : Type*} [Group G] (d x y : G) :
    d * x * d⁻¹ * (d * y * d⁻¹) = d * y * d⁻¹ * (d * x * d⁻¹) ↔ x * y = y * x := by
  have h1 : d * x * d⁻¹ * (d * y * d⁻¹) = d * (x * y) * d⁻¹ := by group
  have h2 : d * y * d⁻¹ * (d * x * d⁻¹) = d * (y * x) * d⁻¹ := by group
  rw [h1, h2]
  constructor
  · intro h
    have := mul_left_cancel (mul_right_cancel h)
    exact this
  · intro h
    rw [h]

theorem orderOf_conj' {G : Type*} [Group G] (d g : G) : orderOf (d * g * d⁻¹) = orderOf g := by
  rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43Inv
