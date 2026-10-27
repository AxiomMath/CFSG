
module

public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43Out
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43OutCheck
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43Interfaces
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43Inv

@[expose] public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43Out

open CFSG.LieType.Multipliers.U43 CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Certificates.Native CFSG.Certificates CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43Inv
  CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43Aut
  CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

@[expose] noncomputable def letP (l : ℕ) : Gp :=
  if l < 4 then psi (letElt l) else if l = 4 then dPerm else if l = 5 then sPerm
  else if l = 6 then dPerm⁻¹ else sPerm⁻¹

theorem rep_letTab8 (hf : AutFacts) (l : ℕ) :
    Rep 820 (letTab8 l) (letP l) := by
  unfold letTab8 letP
  split_ifs
  · exact rep_letTab l
  · exact rep_dTab hf
  · exact rep_sTab hf
  · exact rep_dTab_inv hf
  · exact rep_sTab_inv hf

@[expose] noncomputable def wordP (w : List ℕ) : Gp := w.foldl (fun g l => g * letP l) 1

theorem rep_foldl8 (hf : AutFacts) (w : List ℕ) : ∀ (t : Array ℕ) (g : Gp),
    Rep 820 t g → Rep 820 (w.foldl (fun t l => compA 820 t (letTab8 l)) t)
      (w.foldl (fun g l => g * letP l) g) := by
  induction w with
  | nil => intro t g h; exact h
  | cons l w ih =>
    intro t g h
    rw [List.foldl_cons, List.foldl_cons]
    exact ih _ _ (rep_compA h (rep_letTab8 hf l))

theorem rep_wordTab8 (hf : AutFacts) (w : List ℕ) :
    Rep 820 (wordTab8 w) (wordP w) := rep_foldl8 hf w _ _ rep_idA

theorem letP_mem (hf : AutFacts) (l : ℕ) : letP l ∈ Nrm := by
  unfold letP
  split_ifs
  · exact Nsub_le_Nrm ⟨_, rfl⟩
  · exact dPerm_mem hf
  · exact sPerm_mem hf
  · exact Nrm.inv_mem (dPerm_mem hf)
  · exact Nrm.inv_mem (sPerm_mem hf)

theorem wordP_mem (hf : AutFacts) (w : List ℕ) : wordP w ∈ Nrm := by
  unfold wordP
  have : ∀ (g : Gp), g ∈ Nrm → w.foldl (fun g l => g * letP l) g ∈ Nrm := by
    induction w with
    | nil => intro g hg; exact hg
    | cons l w ih =>
      intro g hg
      rw [List.foldl_cons]
      exact ih _ (Nrm.mul_mem hg (letP_mem hf l))
  exact this 1 Nrm.one_mem

@[expose] noncomputable def treeP (root : Gp) (step : Gp → ℕ → Gp) (par lab : Array ℕ) (nl : ℕ) :
    ℕ → ℕ → Gp
  | 0, _ => root
  | f + 1, k => if k = 0 then root else
      step (treeP root step par lab nl f par[k]!) (lab[k]! % nl)

theorem rep_treeP {rT : Array ℕ} {rG : Gp} (hr : Rep 820 rT rG) {sT : Array ℕ → ℕ → Array ℕ}
    {sG : Gp → ℕ → Gp} {nl : ℕ} (hnl : 0 < nl)
    (hs : ∀ t g l, l < nl → Rep 820 t g → Rep 820 (sT t l) (sG g l))
    (par lab : Array ℕ) (f : ℕ) :
    ∀ k, Rep 820 (treeTab rT sT par lab nl f k) (treeP rG sG par lab nl f k) := by
  induction f with
  | zero => intro k; exact hr
  | succ f ih =>
    intro k
    simp only [treeTab, treeP]
    split_ifs
    · exact hr
    · exact hs _ _ _ (Nat.mod_lt _ hnl) (ih _)

theorem treeP_mem {Q : Gp → Prop} {rG : Gp} (hr : Q rG) {sG : Gp → ℕ → Gp} {nl : ℕ}
    (hnl : 0 < nl) (hs : ∀ g l, l < nl → Q g → Q (sG g l)) (par lab : Array ℕ) (f : ℕ) :
    ∀ k, Q (treeP rG sG par lab nl f k) := by
  induction f with
  | zero => intro k; exact hr
  | succ f ih =>
    intro k
    simp only [treeP]
    split_ifs
    · exact hr
    · exact hs _ _ (Nat.mod_lt _ hnl) (ih _)

@[expose] noncomputable def mulStepP (gs : List Gp) (g : Gp) (l : ℕ) : Gp :=
  if l % 2 = 0 then g * gs.getD (l / 2) 1 else g * (gs.getD (l / 2) 1)⁻¹

theorem rep_mulStepP {ts : List (Array ℕ)} {gs : List Gp} (_hlen : ts.length = gs.length)
    (hrep : ∀ j < gs.length, Rep 820 ts[j]! (gs.getD j 1))
    (hinv : ∀ j < gs.length, isInvA 820 ts[j]! (invCand 820 ts[j]!) = true)
    (t : Array ℕ) (g : Gp) (l : ℕ) (hl : l < 2 * gs.length) (h : Rep 820 t g) :
    Rep 820 (mulStep ts t l) (mulStepP gs g l) := by
  have hj : l / 2 < gs.length := by omega
  unfold mulStep mulStepP
  split_ifs
  · exact rep_compA h (hrep _ hj)
  · exact rep_compA h (rep_inv_of_isInvA (hrep _ hj) (hinv _ hj))

theorem enum_specP {ts : List (Array ℕ)} {gs : List Gp}
    (hlen : ts.length = gs.length)
    (hrep : ∀ j < gs.length, Rep 820 ts[j]! (gs.getD j 1))
    (hinv : ∀ j < gs.length, isInvA 820 ts[j]! (invCand 820 ts[j]!) = true)
    (hpos : 0 < gs.length) {par lab tbl : Array ℕ} {n : ℕ} (hn : 0 < n)
    (hcl : closedOK (fun k => treeTab (idA 820) (mulStep ts) par lab (2 * ts.length) fuel k) tbl n
      (2 * ts.length) (mulStep ts) = true)
    (hdist : distinctOK (fun k => treeTab (idA 820) (mulStep ts) par lab (2 * ts.length) fuel k)
      n = true) :
    (∀ k, treeP 1 (mulStepP gs) par lab (2 * gs.length) fuel k ∈
        Subgroup.closure {g | g ∈ gs}) ∧
    (∀ h ∈ Subgroup.closure {g | g ∈ gs}, ∃ k < n,
        treeP 1 (mulStepP gs) par lab (2 * gs.length) fuel k = h) ∧
    (∀ i < n, ∀ j < n, treeP 1 (mulStepP gs) par lab (2 * gs.length) fuel i =
        treeP 1 (mulStepP gs) par lab (2 * gs.length) fuel j → i = j) := by
  have hnl : 0 < 2 * gs.length := by omega
  rw [hlen] at hcl hdist
  have hmem : ∀ g l, l < 2 * gs.length → g ∈ Subgroup.closure {g | g ∈ gs} →
      mulStepP gs g l ∈ Subgroup.closure {g | g ∈ gs} := by
    intro g l hl hg
    have hj : l / 2 < gs.length := by omega
    have hy : gs.getD (l / 2) 1 ∈ Subgroup.closure {g | g ∈ gs} := by
      apply Subgroup.subset_closure
      rw [List.getD_eq_getElem _ _ hj]
      exact List.getElem_mem hj
    unfold mulStepP
    split_ifs
    · exact mul_mem hg hy
    · exact mul_mem hg (inv_mem hy)
  have hrepT : ∀ k, Rep 820 (treeTab (idA 820) (mulStep ts) par lab (2 * gs.length) fuel k)
      (treeP 1 (mulStepP gs) par lab (2 * gs.length) fuel k) :=
    rep_treeP rep_idA hnl (fun t g l hl h => rep_mulStepP hlen hrep hinv t g l hl h) par lab fuel
  have hdist' := distinctOK_spec hdist
  have hcl' := closedOK_spec hcl
  have hstep : ∀ k < n, ∀ l < 2 * gs.length, ∃ k' < n,
      treeP 1 (mulStepP gs) par lab (2 * gs.length) fuel k' =
        mulStepP gs (treeP 1 (mulStepP gs) par lab (2 * gs.length) fuel k) l := by
    intro k hk l hl
    obtain ⟨hk', heq⟩ := hcl' k hk l hl
    refine ⟨tbl[k * (2 * gs.length) + l]!, hk', ?_⟩
    have hr2 := rep_mulStepP hlen hrep hinv _ _ l hl (hrepT k)
    exact (eqA_iff (hrepT _) hr2).1 heq
  refine ⟨treeP_mem (Q := (· ∈ Subgroup.closure {g | g ∈ gs})) (one_mem _) hnl hmem par lab fuel,
    ?_, ?_⟩
  · intro h hh
    induction hh using Subgroup.closure_induction_right with
    | one => exact ⟨0, hn, by simp [treeP, fuel]⟩
    | mul_right x hx y hy ih =>
      obtain ⟨k, hk, rfl⟩ := ih
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hy
      obtain ⟨k', hk', hk'e⟩ := hstep k hk (2 * j) (by omega)
      refine ⟨k', hk', ?_⟩
      rw [hk'e]
      have h1 : (2 * j) % 2 = 0 := by omega
      have h2 : (2 * j) / 2 = j := by omega
      simp [mulStepP, h1, h2, List.getElem?_eq_getElem hj]
    | mul_inv_cancel x hx y hy ih =>
      obtain ⟨k, hk, rfl⟩ := ih
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hy
      obtain ⟨k', hk', hk'e⟩ := hstep k hk (2 * j + 1) (by omega)
      refine ⟨k', hk', ?_⟩
      rw [hk'e]
      have h1 : (2 * j + 1) % 2 = 1 := by omega
      have h2 : (2 * j + 1) / 2 = j := by omega
      simp [mulStepP, h1, h2, List.getElem?_eq_getElem hj]
  · intro i hi j hj hij
    apply hdist' i hi j hj
    have key : ∀ (x : ℕ) (hx : x < 820),
        (treeTab (idA 820) (mulStep ts) par lab (2 * gs.length) fuel i)[x]! =
          (treeTab (idA 820) (mulStep ts) par lab (2 * gs.length) fuel j)[x]! := fun x hx => by
      rw [(hrepT i).apply hx, (hrepT j).apply hx, hij]
    simp [fpKey, key 0 (by norm_num), key 1 (by norm_num), key 9 (by norm_num)]

@[expose] def memNA (t : Array ℕ) : Bool := siftA 820 (rawLevels 820 chainS baseArr) baseArr 0 t

structure OutFacts : Prop where
  pos : 0 < tGens.length
  inv : ∀ j < tGens.length, isInvA 820 tGens[j]! (invCand 820 tGens[j]!) = true
  dist : distinctOK tTab 1024 = true
  closed : closedOK tTab tTbl 1024 (2 * tGens.length) (mulStep tGens) = true
  wit : ∀ w ∈ witWords, isInvA 820 (wordTab w) (invCand 820 (wordTab w)) = true
  pairs : ∀ k₁ < 1024, ∀ k₂ < 1024, isInvol (tTab k₁) = true → memNA (tTab k₁) = false →
    isInvol (tTab k₂) = true → memNA (tTab k₂) = false →
    pairOK memNA (tTab k₁) (tTab k₂) = true

@[expose] noncomputable def tGensG : List Gp := pGensG.map psi ++ tExtraWords.map wordP

theorem pGens_len : pGens.length = pGenIdx.length := by simp [pGens]

theorem pGensG_len : pGensG.length = pGenIdx.length := by simp [pGensG]

theorem tGensG_len : tGensG.length = pGenIdx.length + tExtraWords.length := by
  simp [tGensG, pGensG_len]

theorem tGens_len : tGens.length = pGenIdx.length + tExtraWords.length := by
  simp [tGens, pGens_len]

theorem tGens_length : tGens.length = tGensG.length := by rw [tGens_len, tGensG_len]

theorem rep_tGens (hf : AutFacts) :
    ∀ j < tGensG.length, Rep 820 tGens[j]! (tGensG.getD j 1) := by
  intro j hj
  have l1 := pGens_len
  have l2 := pGensG_len
  have l3 := tGensG_len
  have l4 := tGens_len
  by_cases hjp : j < pGensG.length
  · have hjp' : j < pGens.length := by omega
    have e1 : tGens[j]! = pGens[j]! := by
      rw [getElem!_pos _ j (by omega), getElem!_pos _ j hjp']
      simp [tGens, List.getElem_append_left hjp']
    have e2 : tGensG.getD j 1 = psi (pGensG.getD j 1) := by
      rw [List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ hjp]
      simp only [tGensG]
      rw [List.getElem_append_left (by simpa using hjp)]
      simp
    rw [e1, e2]
    exact rep_pGens j hjp
  · have hjp' : pGens.length ≤ j := by omega
    have hjq : j - pGens.length < tExtraWords.length := by omega
    have e1 : tGens[j]! = wordTab8 tExtraWords[j - pGens.length] := by
      rw [getElem!_pos _ j (by omega)]
      simp only [tGens, List.getElem_append_right hjp']
      simp
    have e2 : tGensG.getD j 1 = wordP tExtraWords[j - pGens.length] := by
      rw [List.getD_eq_getElem _ _ hj]
      simp only [tGensG]
      rw [List.getElem_append_right (by simpa [pGensG, l2, l1] using hjp')]
      simp [l1, l2]
    rw [e1, e2]
    exact rep_wordTab8 hf _

@[expose] noncomputable def tSub : Subgroup Gp := Subgroup.closure {g | g ∈ tGensG}

@[expose] noncomputable def tElt (k : ℕ) : Gp :=
  treeP 1 (mulStepP tGensG) tPar tLab (2 * tGensG.length) fuel k

theorem tSub_le_Nrm (hf : AutFacts) :
    tSub ≤ Nrm := by
  unfold tSub
  rw [Subgroup.closure_le]
  intro g hg
  have hmem : g ∈ pGensG.map psi ++ tExtraWords.map wordP := hg
  rw [List.mem_append, List.mem_map, List.mem_map] at hmem
  rcases hmem with ⟨x, -, rfl⟩ | ⟨w, -, rfl⟩
  · exact Nsub_le_Nrm ⟨x, rfl⟩
  · exact wordP_mem hf w

theorem factorization_two_Nrm : (26127360 : ℕ).factorization 2 = 10 := by
  rw [Nat.factorization_def _ Nat.prime_two]
  have : (26127360 : ℕ) = 2 ^ 10 * 25515 := by norm_num
  rw [this, padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (by norm_num)]

theorem isInvol_iff_P {t : Array ℕ} {g : Gp} (h : Rep 820 t g) :
    isInvol t = true ↔ g * g = 1 ∧ g ≠ 1 := by
  have h2 : Rep 820 (compA 820 t t) (g * g) := rep_compA h h
  have h3 : (!eqA 820 t (idA 820)) = true ↔ g ≠ 1 := by
    rw [Bool.not_eq_true', Bool.eq_false_iff, Ne, eqA_iff h rep_idA]
  unfold isInvol
  rw [Bool.and_eq_true, eqA_iff h2 rep_idA, h3]

theorem memNA_iff {t : Array ℕ} {g : Gp} (h : Rep 820 t g) :
    memNA t = true ↔ g ∈ Nsub := sift_iff h

@[expose] def SmallP (r : Gp) : Prop := ∀ n ∈ Nsub, orderOf (r * (n * r * n⁻¹)) ≤ 5

theorem conj_mem_Nsub {c : Gp} (hc : c ∈ Nrm) {x : Gp} (hx : x ∈ Nsub) : c * x * c⁻¹ ∈ Nsub :=
  ((Subgroup.mem_set_normalizer_iff.1 hc) x).1 hx

theorem smallN_conj {r : Gp} (c : (Nrm : Subgroup Gp)) (hs : SmallP r) :
    SmallP ((c : Gp) * r * (c : Gp)⁻¹) := by
  intro n hn
  have hn' : (c : Gp)⁻¹ * n * ((c : Gp)⁻¹)⁻¹ ∈ Nsub := conj_mem_Nsub (Nrm.inv_mem c.2) hn
  rw [inv_inv] at hn'
  have e : ((c : Gp) * r * (c : Gp)⁻¹) * (n * ((c : Gp) * r * (c : Gp)⁻¹) * n⁻¹) =
      (c : Gp) * (r * (((c : Gp)⁻¹ * n * (c : Gp)) * r * ((c : Gp)⁻¹ * n * (c : Gp))⁻¹)) *
        (c : Gp)⁻¹ := by group
  rw [e, orderOf_conj']
  exact hs _ hn'

theorem small_to_perm (e : (Nrm : Subgroup Gp) ≃* MulAut X₀)
    (he : ∀ (a : (Nrm : Subgroup Gp)) (x : X₀), psi (e a x) = (a : Gp) * psi x * (a : Gp)⁻¹)
    (ψ : MulAut X₀) (hs : IsSmallAut ψ) : SmallP ((e.symm ψ : (Nrm : Subgroup Gp)) : Gp) := by
  rintro _ ⟨g, rfl⟩
  have hg : psi g ∈ Nrm := Nsub_le_Nrm ⟨g, rfl⟩
  have hcg := e_psi e he g hg
  have h1 := hs g
  rw [← hcg] at h1
  have h2 : ψ * (e ⟨psi g, hg⟩ * ψ * (e ⟨psi g, hg⟩)⁻¹) =
      e (e.symm ψ * (⟨psi g, hg⟩ * e.symm ψ * ⟨psi g, hg⟩⁻¹)) := by
    simp
  rw [h2, MulEquiv.orderOf_eq] at h1
  have h3 := Subgroup.orderOf_coe (e.symm ψ * (⟨psi g, hg⟩ * e.symm ψ * ⟨psi g, hg⟩⁻¹) :
    (Nrm : Subgroup Gp))
  rw [← h3] at h1
  simpa using h1

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43Out
