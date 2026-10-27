module

public import CFSG.Sporadic.Th.TableSpec
public import Certificates.Data.RouteP.Objects

public section

namespace CFSG.KS.RouteP

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native

variable {G : Type*} [Group G] {n : ℕ} [MulAction G (Fin n)]

theorem toNat_ofNat_of_lt {k : ℕ} (hk : k < 2 ^ 32) : (UInt32.ofNat k).toNat = k := by
  rw [UInt32.toNat_ofNat']
  exact Nat.mod_eq_of_lt hk

theorem invT_eq_foldl (n : ℕ) (P : Table) :
    invT n P = (List.range' 0 n).foldl (fun r i => r.set! (P[i]!).toNat (UInt32.ofNat i))
      (Array.replicate n 0) := by
  unfold invT
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.forIn_pure_yield_eq_foldl, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    bind_pure]
  rfl

theorem invT_loop (P : Table) (hlt : ∀ i < n, (P[i]!).toNat < n)
    (hinj : ∀ i < n, ∀ j < n, (P[i]!).toNat = (P[j]!).toNat → i = j) :
    ∀ s ≤ n,
      ((List.range' 0 s).foldl (fun r i => r.set! (P[i]!).toNat (UInt32.ofNat i))
        (Array.replicate n 0)).size = n ∧
      ∀ i < s, ((List.range' 0 s).foldl (fun r i => r.set! (P[i]!).toNat (UInt32.ofNat i))
        (Array.replicate n 0))[(P[i]!).toNat]! = UInt32.ofNat i := by
  intro s
  induction s with
  | zero => intro _; exact ⟨by simp, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | succ s ih =>
    intro hs
    obtain ⟨hsz, hval⟩ := ih (by omega)
    rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil]
    simp only [Nat.one_mul, Nat.zero_add]
    refine ⟨by rw [Array.size_set!]; exact hsz, fun i hi => ?_⟩
    by_cases e : i = s
    · subst e
      exact Array.getElem!_set!_self _ _ _ (by rw [hsz]; exact hlt i (by omega))
    · have hne : (P[s]!).toNat ≠ (P[i]!).toNat := fun h =>
        e (hinj i (by omega) s (by omega) h.symm)
      rw [Array.getElem!_set!_ne _ _ _ _ hne]
      exact hval i (by omega)

theorem rep_invT (hn : n < 2 ^ 32) {T : Table} {g : G} (h : Rep n T g) : Rep n (invT n T) g⁻¹ := by
  have hT : ∀ i < n, (T[i]!).toNat = idx n g i := fun i hi => h i hi
  have hlt : ∀ i < n, (T[i]!).toNat < n := fun i hi => by rw [hT i hi]; exact idx_lt g hi
  have hinj : ∀ i < n, ∀ j < n, (T[i]!).toNat = (T[j]!).toNat → i = j := by
    intro i hi j hj e
    rw [hT i hi, hT j hj] at e
    rw [← idx_inv_idx (n := n) g i, e, idx_inv_idx]
  obtain ⟨-, hval⟩ := invT_loop T hlt hinj n le_rfl
  intro j hj
  have hi := idx_lt g⁻¹ hj
  have e : (T[idx n g⁻¹ j]!).toNat = j := by rw [hT _ hi, idx_idx_inv]
  unfold ap
  rw [invT_eq_foldl, ← e, hval _ hi, e, toNat_ofNat_of_lt (by omega)]

theorem ap_invT_of_rep (hn : n < 2 ^ 32) {T : Table} {g : G} (h : Rep n T g) {i : ℕ}
    (hi : i < n) : ap (invT n T) (ap T i) = i := by
  rw [rep_invT hn h _ (by rw [h i hi]; exact idx_lt g hi), h i hi, idx_inv_idx]

theorem invOK_of_rep {P R : Table} {g : G} (hP : Rep n P g) (hR : Rep n R g⁻¹) :
    invOK n P R = true := by
  unfold invOK
  rw [allIn_eq_true]
  intro i _ hi
  rw [beq_iff_eq, hP i hi, hR _ (idx_lt g hi), idx_inv_idx]

theorem invOK_invT_of_rep (hn : n < 2 ^ 32) {T : Table} {g : G} (h : Rep n T g) :
    invOK n T (invT n T) = true :=
  invOK_of_rep h (rep_invT hn h)

theorem invoOK_of_rep {P : Table} {g : G} (hP : Rep n P g) (hg : g * g = 1) :
    invoOK n P = true := by
  unfold invoOK
  rw [allIn_eq_true]
  intro i _ hi
  rw [beq_iff_eq, hP i hi, hP _ (idx_lt g hi), ← idx_mul, hg, idx_one]

theorem permOK_of_rep (hn : n < 2 ^ 32) {T : Table} {g : G} (h : Rep n T g) :
    permOK n T = true := by
  have hR := rep_invT hn h
  unfold permOK
  rw [allIn_eq_true]
  intro i _ hi
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · rw [h i hi]; exact idx_lt g hi
  · rw [hR i hi]; exact idx_lt g⁻¹ hi
  · rw [h i hi, hR _ (idx_lt g hi), idx_inv_idx]
  · rw [hR i hi, h _ (idx_lt g⁻¹ hi), idx_idx_inv]

theorem tabsOK_of_rep (hn : n < 2 ^ 32) {ts : Array Table} {gs : ℕ → G}
    (h : ∀ i < ts.size, Rep n ts[i]! (gs i)) : tabsOK n ts = true := by
  unfold tabsOK
  rw [Array.all_eq_true]
  intro i hi
  have := permOK_of_rep hn (h i hi)
  rwa [getElem!_pos ts i hi] at this

theorem eqTab_of_rep {S T : Table} {g : G} (hS : Rep n S g) (hT : Rep n T g) :
    eqTab n S T = true := by
  unfold eqTab
  rw [allIn_eq_true]
  intro i _ hi
  rw [beq_iff_eq, hS i hi, hT i hi]

theorem commOK_of_rep [MulAction G (Fin degree)] {P Q : Table} {g h : G} (hP : Rep degree P g)
    (hQ : Rep degree Q h) (hgh : g * h = h * g) : commOK P Q = true := by
  unfold commOK
  rw [allIn_eq_true]
  intro i _ hi
  rw [beq_iff_eq, hQ i hi, hP _ (idx_lt h hi), hP i hi, hQ _ (idx_lt g hi), ← idx_mul, ← idx_mul,
    hgh]

private theorem getElem!_set!' {α : Type*} [Inhabited α] (a : Array α) (k r : ℕ) (v : α)
    (hr : r < a.size) : (a.set! k v)[r]! = if k = r then v else a[r]! := by
  rw [Array.set!_eq_setIfInBounds, getElem!_pos (a.setIfInBounds k v) r (by simpa using hr),
    Array.getElem_setIfInBounds hr, getElem!_pos a r hr]

theorem stepT_size (n : ℕ) (st : Array Table × Bool) (ins : Instr) :
    (stepT n st ins).1.size = st.1.size := by
  cases ins <;> simp [stepT]

theorem runSLP_size (n : ℕ) (prog : List Instr) (regsT : Array Table) :
    (runSLP n prog regsT).1.size = regsT.size := by
  unfold runSLP
  suffices ∀ st : Array Table × Bool, (prog.foldl (stepT n) st).1.size = st.1.size from this _
  induction prog with
  | nil => intro st; rfl
  | cons ins prog ih =>
    intro st
    rw [List.foldl_cons, ih, stepT_size]

private theorem foldl_stepT_rep' (hn : n < 2 ^ 32) (prog : List Instr) (st : Array Table × Bool)
    (regsG : ℕ → G) (hprog : ∀ ins ∈ prog, instrRegsLt st.1.size ins)
    (hregs : ∀ r < st.1.size, Rep n st.1[r]! (regsG r)) :
    (prog.foldl (stepT n) st).2 = st.2 ∧
      ∀ r < st.1.size, Rep n (prog.foldl (stepT n) st).1[r]! (runSLPG prog regsG r) := by
  induction prog generalizing st regsG with
  | nil => exact ⟨rfl, hregs⟩
  | cons ins prog ih =>
    rw [List.foldl_cons]
    have hins := hprog ins List.mem_cons_self
    have hsz := stepT_size n st ins
    have hflag : (stepT n st ins).2 = st.2 := by
      cases ins with
      | mu i j k => rfl
      | pwr e i k => rfl
      | iv i k =>
        simp only [stepT]
        rw [invOK_invT_of_rep hn (hregs i hins.1), Bool.and_true]
    have hstep : ∀ r < st.1.size, Rep n (stepT n st ins).1[r]! (stepG regsG ins r) := by
      intro r hr
      cases ins with
      | mu i j k =>
        simp only [stepT, stepG, getElem!_set!' _ _ _ _ hr, Function.update_apply]
        by_cases hkr : k = r
        · subst hkr
          rw [ite_eq_left rfl, ite_eq_left rfl]
          exact Rep.compT (hregs i hins.1) (hregs j hins.2.1)
        · rw [ite_eq_right hkr, ite_eq_right (Ne.symm hkr)]
          exact hregs r hr
      | pwr e i k =>
        simp only [stepT, stepG, getElem!_set!' _ _ _ _ hr, Function.update_apply]
        by_cases hkr : k = r
        · subst hkr
          rw [ite_eq_left rfl, ite_eq_left rfl]
          exact Rep.powT hn (hregs i hins.1) e
        · rw [ite_eq_right hkr, ite_eq_right (Ne.symm hkr)]
          exact hregs r hr
      | iv i k =>
        simp only [stepT, stepG, getElem!_set!' _ _ _ _ hr, Function.update_apply]
        by_cases hkr : k = r
        · subst hkr
          rw [ite_eq_left rfl, ite_eq_left rfl]
          exact rep_invT hn (hregs i hins.1)
        · rw [ite_eq_right hkr, ite_eq_right (Ne.symm hkr)]
          exact hregs r hr
    have := ih (stepT n st ins) (stepG regsG ins)
      (fun ins' hins' => hsz ▸ hprog ins' (List.mem_cons_of_mem _ hins'))
      (fun r hr => hstep r (hsz ▸ hr))
    refine ⟨this.1.trans hflag, fun r hr => ?_⟩
    exact this.2 r (hsz.symm ▸ hr)

theorem runSLP_rep' (hn : n < 2 ^ 32) (prog : List Instr) (regsT : Array Table) (regsG : ℕ → G)
    (hprog : ∀ ins ∈ prog, instrRegsLt regsT.size ins)
    (hregs : ∀ r < regsT.size, Rep n regsT[r]! (regsG r)) :
    (runSLP n prog regsT).2 = true ∧ (runSLP n prog regsT).1.size = regsT.size ∧
      ∀ r < regsT.size, Rep n (runSLP n prog regsT).1[r]! (runSLPG prog regsG r) := by
  obtain ⟨h1, h2⟩ := foldl_stepT_rep' hn prog (regsT, true) regsG hprog hregs
  exact ⟨h1, runSLP_size n prog regsT, h2⟩

theorem runSLP_flag (hn : n < 2 ^ 32) (prog : List Instr) (regsT : Array Table) (regsG : ℕ → G)
    (hprog : ∀ ins ∈ prog, instrRegsLt regsT.size ins)
    (hregs : ∀ r < regsT.size, Rep n regsT[r]! (regsG r)) : (runSLP n prog regsT).2 = true :=
  (runSLP_rep' hn prog regsT regsG hprog hregs).1

end CFSG.KS.RouteP

end
