module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Tables
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi24ThreeCoverMain
public import Certificates.Certificate450200

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model

open Equiv CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native
open CFSG.CosetTable CFSG.Sporadic.Recognition.PresentedWords
  CFSG.Sporadic.Recognition.Fi24PrimeMultiplier
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi24Three

abbrev Ω : Type := Fin 920808

@[expose] def x0 : Ω := ⟨0, by norm_num⟩

theorem x0_val : x0.val = 0 := rfl

@[expose] def litInt (l : Fin nG × Bool) : ℤ :=
  if l.2 then (l.1.val : ℤ) + 1 else -((l.1.val : ℤ) + 1)

@[expose] def wsQInt : List (List ℤ) := wsQ.map fun w => w.map litInt

theorem bridgeOK_wsQInt : bridgeOK wsQInt = true :=
  Certificates.certificate450200

structure BridgeFacts (gs ms : Array Table) (ws : List (List ℤ)) : Prop where
  gs_size : gs.size = 22
  ms_size : ms.size = 2
  gs_perm : tabsOK degree gs = true
  ms_perm : tabsOK degree ms = true
  rels : relatorsOK degree gs (gs.map (invT degree)) ws = true
  fix : fixOK gs = true
  move : moveOK gs = true
  slp : slpOK degree (gs.extract 0 11) ms = true
  tree : treeCheck degree ms[0]! ms[1]! = true

theorem BridgeFacts.of_bridgeOKAt {gs ms : Array Table} {ws : List (List ℤ)}
    (h : bridgeOKAt gs ms ws = true) : BridgeFacts gs ms ws := by
  unfold bridgeOKAt at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem bridgeFacts :
    BridgeFacts (genTabs ()) (mTabs ()) wsQInt :=
  BridgeFacts.of_bridgeOKAt bridgeOK_wsQInt

noncomputable def genPerm (i : ℕ) : Perm Ω := permOfTab 920808 (genTabs ())[i]!

theorem rep_genPerm {i : ℕ} (hi : i < 22) :
    Rep 920808 (genTabs ())[i]! (genPerm i) :=
  rep_permOfTab (permOK_of_tabsOK bridgeFacts.gs_perm (by rw [bridgeFacts.gs_size]; exact hi))

theorem invOK_genTabs {i : ℕ} (hi : i < 22) :
    invOK 920808 (genTabs ())[i]! (invT 920808 (genTabs ())[i]!) = true :=
  (permOK_spec (permOK_of_tabsOK bridgeFacts.gs_perm (by rw [bridgeFacts.gs_size]; exact hi))).2

theorem letterPerm_litInt {G : Type*} [Group G] (π : ℕ → G) (l : Fin nG × Bool) :
    letterPerm π 22 (litInt l) = if l.2 then π l.1.val else (π l.1.val)⁻¹ := by
  obtain ⟨i, b⟩ := l
  have hi : i.val < 22 := i.isLt
  rcases b with _ | _
  · have h0 : ¬(0 < -((i.val : ℤ) + 1)) := by omega
    have h1 : -((i.val : ℤ) + 1) < 0 := by omega
    have h2 : (-(-((i.val : ℤ) + 1)) - 1).toNat = i.val := by omega
    have h3 : (-(-((i.val : ℤ) + 1)) - 1).toNat < 22 := by rw [h2]; exact hi
    simp only [litInt, letterPerm, Bool.false_eq_true, if_false]
    rw [if_neg (fun h => h0 h.1), if_pos ⟨h1, h3⟩, h2]
  · have h1 : 0 < (i.val : ℤ) + 1 := by omega
    have h2 : ((i.val : ℤ) + 1 - 1).toNat = i.val := by omega
    have h3 : ((i.val : ℤ) + 1 - 1).toNat < 22 := by rw [h2]; exact hi
    simp only [litInt, letterPerm, if_true]
    rw [if_pos ⟨h1, h3⟩, h2]

theorem wprod_eq_wordG {G : Type*} [Group G] (π : ℕ → G) (w : List (Fin nG × Bool)) :
    wprod (fun i : Fin nG => π i.val) w = wordG (letterPerm π 22) (w.map litInt) := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    have e : wordG (letterPerm π 22) ((l :: w).map litInt) =
        letterPerm π 22 (litInt l) * wordG (letterPerm π 22) (w.map litInt) := by
      simp [wordG]
    rw [e, ← ih, letterPerm_litInt, wprod_cons]

theorem relators_hold :
    ∀ w ∈ wsQ, wprod (fun i : Fin nG => genPerm i.val) w = 1 := by
  intro w hw
  have hmem : w.map litInt ∈ wsQInt := List.mem_map_of_mem hw
  rw [wprod_eq_wordG]
  have := wordG_eq_one_of_relatorsOK (n := 920808) (by norm_num) (gs := genTabs ())
    (π := genPerm)
    (fun l hl => rep_genPerm (by rwa [bridgeFacts.gs_size] at hl))
    (fun l hl => invOK_genTabs (by rwa [bridgeFacts.gs_size] at hl)) bridgeFacts.rels hmem
  rwa [bridgeFacts.gs_size] at this

noncomputable def rho : Q3 →* Perm Ω :=
  pgHom (fun i : Fin nG => genPerm i.val) relators_hold

theorem rho_of (i : Fin nG) :
    rho (PresentedGroup.of i : Q3) = genPerm i.val :=
  pgHom_of _ _ i

noncomputable instance instMulAction : MulAction Q3 Ω :=
  MulAction.compHom Ω rho

theorem smul_def (g : Q3) (p : Ω) : g • p = rho g p := rfl

theorem idx_eq_rho (g : Q3) (j : ℕ) :
    idx 920808 g j = idx 920808 (rho g) j := by
  by_cases hj : j < 920808
  · rw [idx_of_lt _ hj, idx_of_lt _ hj]
    rfl
  · rw [idx_of_not_lt _ hj, idx_of_not_lt _ hj]

theorem rep_iff_rho {T : Table} {g : Q3} :
    Rep 920808 T g ↔ Rep 920808 T (rho g) := by
  unfold CFSG.Sporadic.Th.Rep
  simp only [idx_eq_rho]

noncomputable def genQ (i : ℕ) : Q3 := if h : i < nG then PresentedGroup.of ⟨i, h⟩ else 1

theorem genQ_of (i : Fin nG) : genQ i.val = (PresentedGroup.of i : Q3) := by
  simp [genQ, i.isLt]

theorem rep_genQ {i : ℕ} (hi : i < 22) :
    Rep 920808 (genTabs ())[i]! (genQ i) := by
  rw [rep_iff_rho]
  have e : rho (genQ i) = genPerm i := by
    have : i < nG := hi
    rw [genQ, dif_pos this, rho_of]
  rw [e]
  exact rep_genPerm hi

theorem rep_of (i : Fin nG) :
    Rep 920808 (genTabs ())[i.val]! (PresentedGroup.of i : Q3) := by
  rw [← genQ_of]
  exact rep_genQ i.isLt

theorem smul_val_of_rep {T : Table} {g : Q3}
    (h : Rep 920808 T g) (p : Ω) : (g • p).val = ap T p.val := by
  have := h p.val p.isLt
  rw [idx_of_lt _ p.isLt] at this
  exact this.symm

theorem smul_of (i : Fin nG) (p : Ω) :
    ((PresentedGroup.of i : Q3) • p).val = ap (genTabs ())[i.val]! p.val :=
  smul_val_of_rep (rep_of i) p

theorem rep_wordT (w : List ℤ) :
    Rep 920808 (wordT 920808 (letterTab 920808 (genTabs ()) ((genTabs ()).map (invT 920808))) w)
      (wordG (letterPerm genQ 22) w) := by
  have := rep_wordT_letters (G := Q3) (n := 920808) (by norm_num) (gs := genTabs ())
    (π := genQ) (fun l hl => rep_genQ (by rwa [bridgeFacts.gs_size] at hl))
    (fun l hl => invOK_genTabs (by rwa [bridgeFacts.gs_size] at hl)) w
  rwa [bridgeFacts.gs_size] at this

theorem rep_wordT_signed (w : List (Fin nG × Bool)) :
    Rep 920808 (wordT 920808 (letterTab 920808 (genTabs ()) ((genTabs ()).map (invT 920808)))
      (w.map litInt)) (wprod (fun i : Fin nG => (PresentedGroup.of i : Q3)) w) := by
  have e : wprod (fun i : Fin nG => (PresentedGroup.of i : Q3)) w =
      wordG (letterPerm genQ 22) (w.map litInt) := by
    rw [← wprod_eq_wordG genQ w]
    congr 1
    funext i
    exact (genQ_of i).symm
  rw [e]
  exact rep_wordT _

theorem rep_runSLP (prog : List Instr) (extra : ℕ)
    (hprog : ∀ ins ∈ prog, instrRegsLt (22 + extra) ins)
    (hok : (runSLP 920808 prog (genTabs () ++ Array.replicate extra (idT 920808))).2 = true) :
    ∀ r < 22 + extra, Rep 920808
      (runSLP 920808 prog (genTabs () ++ Array.replicate extra (idT 920808))).1[r]!
      (runSLPG prog genQ r) := by
  have hsz : (genTabs () ++ Array.replicate extra (idT 920808)).size = 22 + extra := by
    simp [bridgeFacts.gs_size]
  have hregs : ∀ r < (genTabs () ++ Array.replicate extra (idT 920808)).size,
      Rep 920808 (genTabs () ++ Array.replicate extra (idT 920808))[r]! (genQ r) := by
    intro r hr
    by_cases h22 : r < 22
    · rw [getElem!_pos _ r hr, Array.getElem_append_left (by rw [bridgeFacts.gs_size]; exact h22),
        ← getElem!_pos (genTabs ()) r (by rw [bridgeFacts.gs_size]; exact h22)]
      exact rep_genQ h22
    · have hq : genQ r = 1 := by
        have : ¬ r < nG := h22
        simp [genQ, this]
      rw [hq, getElem!_pos _ r hr, Array.getElem_append_right (by rw [bridgeFacts.gs_size]; omega)]
      simp only [Array.getElem_replicate]
      exact Rep.idT (by norm_num)
  have := runSLP_rep (n := 920808) (by norm_num) prog
    (genTabs () ++ Array.replicate extra (idT 920808)) genQ
    (by rwa [hsz]) hregs hok
  intro r hr
  exact this.2 r (by rwa [hsz])

noncomputable def regsM (r : ℕ) : Q3 := if r < 11 then genQ r else 1

noncomputable def m1Q : Q3 := runSLPG (compileSLP 11 (slpLines bridgeGensText)) regsM 13

noncomputable def m2Q : Q3 := runSLPG (compileSLP 11 (slpLines bridgeGensText)) regsM 14

theorem rep_m1Q_m2Q :
    Rep 920808 (mTabs ())[0]! m1Q ∧ Rep 920808 (mTabs ())[1]! m2Q := by
  have hx : ∀ i < 11, Rep 920808 ((genTabs ()).extract 0 11)[i]! (genQ i) := by
    intro i hi
    have hi' : i < ((genTabs ()).extract 0 11).size := by
      simp [Array.size_extract, bridgeFacts.gs_size]; omega
    have e : ((genTabs ()).extract 0 11)[i]! = (genTabs ())[i]! := by
      rw [getElem!_pos _ i hi', getElem!_pos (genTabs ()) i (by rw [bridgeFacts.gs_size]; omega)]
      simp [Array.getElem_extract]
    rw [e]
    exact rep_genQ (by omega)
  obtain ⟨-, -, h0, h1⟩ := slpOK_spec (G := Q3) (n := 920808) (by norm_num) hx bridgeFacts.slp
  exact ⟨h0, h1⟩

theorem rep_m1Q : Rep 920808 (mTabs ())[0]! m1Q :=
  rep_m1Q_m2Q.1

theorem rep_m2Q : Rep 920808 (mTabs ())[1]! m2Q :=
  rep_m1Q_m2Q.2

noncomputable def m1Perm : Perm Ω := permOfTab 920808 (mTabs ())[0]!

noncomputable def m2Perm : Perm Ω := permOfTab 920808 (mTabs ())[1]!

theorem rep_m1Perm : Rep 920808 (mTabs ())[0]! m1Perm :=
  rep_permOfTab (permOK_of_tabsOK bridgeFacts.ms_perm (by rw [bridgeFacts.ms_size]; norm_num))

theorem rep_m2Perm : Rep 920808 (mTabs ())[1]! m2Perm :=
  rep_permOfTab (permOK_of_tabsOK bridgeFacts.ms_perm (by rw [bridgeFacts.ms_size]; norm_num))

theorem rho_m1Q : rho m1Q = m1Perm :=
  rep_unique (rep_iff_rho.1 rep_m1Q) rep_m1Perm

theorem rho_m2Q : rho m2Q = m2Perm :=
  rep_unique (rep_iff_rho.1 rep_m2Q) rep_m2Perm

noncomputable def mQ (i : ℕ) : Q3 := if i = 0 then m1Q else if i = 1 then m2Q else 1

theorem rep_mQ {i : ℕ} (hi : i < 2) :
    Rep 920808 (mTabs ())[i]! (mQ i) := by
  interval_cases i
  · simpa [mQ] using rep_m1Q
  · simpa [mQ] using rep_m2Q

theorem invOK_mTabs {i : ℕ} (hi : i < 2) :
    invOK 920808 (mTabs ())[i]! (invT 920808 (mTabs ())[i]!) = true :=
  (permOK_spec (permOK_of_tabsOK bridgeFacts.ms_perm (by rw [bridgeFacts.ms_size]; exact hi))).2

theorem rep_wordT_m (w : List ℤ) :
    Rep 920808 (wordT 920808 (letterTab 920808 (mTabs ()) ((mTabs ()).map (invT 920808))) w)
      (wordG (letterPerm mQ 2) w) := by
  have := rep_wordT_letters (G := Q3) (n := 920808) (by norm_num) (gs := mTabs ())
    (π := mQ) (fun l hl => rep_mQ (by rwa [bridgeFacts.ms_size] at hl))
    (fun l hl => invOK_mTabs (by rwa [bridgeFacts.ms_size] at hl)) w
  rwa [bridgeFacts.ms_size] at this

theorem rep_runSLP_m (prog : List Instr) (extra : ℕ)
    (hprog : ∀ ins ∈ prog, instrRegsLt (2 + extra) ins)
    (hok : (runSLP 920808 prog (mTabs () ++ Array.replicate extra (idT 920808))).2 = true) :
    ∀ r < 2 + extra, Rep 920808
      (runSLP 920808 prog (mTabs () ++ Array.replicate extra (idT 920808))).1[r]!
      (runSLPG prog mQ r) := by
  have hsz : (mTabs () ++ Array.replicate extra (idT 920808)).size = 2 + extra := by
    simp [bridgeFacts.ms_size]
  have hregs : ∀ r < (mTabs () ++ Array.replicate extra (idT 920808)).size,
      Rep 920808 (mTabs () ++ Array.replicate extra (idT 920808))[r]! (mQ r) := by
    intro r hr
    by_cases h2 : r < 2
    · rw [getElem!_pos _ r hr, Array.getElem_append_left (by rw [bridgeFacts.ms_size]; exact h2),
        ← getElem!_pos (mTabs ()) r (by rw [bridgeFacts.ms_size]; exact h2)]
      exact rep_mQ h2
    · have hq : mQ r = 1 := by
        have h0 : r ≠ 0 := by omega
        have h1 : r ≠ 1 := by omega
        simp [mQ, h0, h1]
      rw [hq, getElem!_pos _ r hr,
        Array.getElem_append_right (by rw [bridgeFacts.ms_size]; omega)]
      simp only [Array.getElem_replicate]
      exact Rep.idT (by norm_num)
  have := runSLP_rep (n := 920808) (by norm_num) prog
    (mTabs () ++ Array.replicate extra (idT 920808)) mQ (by rwa [hsz]) hregs hok
  intro r hr
  exact this.2 r (by rwa [hsz])

theorem smul_x0_of_fix {i : Fin nG}
    (hi : i.val ∈ [0, 1, 2, 3, 4, 5, 6, 7, 9, 10]) : (PresentedGroup.of i : Q3) • x0 = x0 := by
  have h0 := ap_zero_of_fixOK bridgeFacts.fix hi
  have h1 := rep_genPerm (i := i.val) i.isLt 0 (by norm_num)
  rw [idx_of_lt _ (by norm_num)] at h1
  have h2 : genPerm i.val x0 = x0 := by
    apply Fin.ext
    exact h1.symm.trans h0
  rw [smul_def, rho_of]
  exact h2

theorem zeta_smul_x0_ne :
    (PresentedGroup.of (zeta 10) : Q3) • x0 ≠ x0 := by
  have h0 := ap_zero_of_moveOK bridgeFacts.move
  have hz : (zeta 10).val = 21 := by decide
  have h1 := rep_genPerm (i := (zeta 10).val) (by rw [hz]; norm_num) 0 (by norm_num)
  rw [idx_of_lt _ (by norm_num)] at h1
  rw [hz] at h1
  intro h
  apply h0
  have h2 := congrArg Fin.val h
  rw [smul_def, rho_of, hz] at h2
  rw [h1]
  simpa [x0] using h2

theorem exists_mem_closure_smul (p : Ω) :
    ∃ g ∈ Subgroup.closure ({m1Q, m2Q} : Set Q3), g • x0 = p :=
  treeCheck_spec rep_m1Q rep_m2Q bridgeFacts.tree (by norm_num) p

instance instIsPretransitive :
    MulAction.IsPretransitive Q3 Ω := by
  refine ⟨fun p q => ?_⟩
  obtain ⟨g, -, hg⟩ := exists_mem_closure_smul p
  obtain ⟨h, -, hh⟩ := exists_mem_closure_smul q
  refine ⟨h * g⁻¹, ?_⟩
  rw [mul_smul, ← hg, inv_smul_smul, hh]

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model
