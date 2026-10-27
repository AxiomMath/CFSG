module

public import CFSG.Sporadic.Th.TableSpec
public import Certificates.Data.RouteP.Bridge

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model

open Equiv CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native

variable {n : ℕ}

theorem eqTab_iff {S T : Table} : eqTab n S T = true ↔ ∀ i < n, ap S i = ap T i := by
  unfold eqTab
  rw [allIn_eq_true]
  constructor
  · intro h i hi
    simpa using h i (Nat.zero_le _) hi
  · intro h i _ hi
    simp [h i hi]

theorem rep_of_eqTab {G : Type*} [Group G] [MulAction G (Fin n)] {S T : Table} {g : G}
    (hS : Rep n S g) (h : eqTab n S T = true) : Rep n T g := fun i hi => by
  rw [← (eqTab_iff.1 h) i hi, hS i hi]

theorem rep_unique {T : Table} {g h : Perm (Fin n)} (hg : Rep n T g) (hh : Rep n T h) : g = h := by
  apply Equiv.ext
  intro i
  apply Fin.ext
  have h1 := hg i.val i.isLt
  have h2 := hh i.val i.isLt
  rw [idx_of_lt _ i.isLt] at h1 h2
  simpa using h1.symm.trans h2

noncomputable def permOfTab (n : ℕ) (T : Table) : Perm (Fin n) :=
  Classical.epsilon fun g => Rep n T g

theorem permOK_spec {T : Table} (h : permOK n T = true) :
    Rep n T (permOfTab n T) ∧ invOK n T (invT n T) = true := by
  unfold permOK at h
  have hp := allIn_eq_true.1 h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hp
  let g : Perm (Fin n) :=
    { toFun := fun i => ⟨ap T i.1, (hp i.1 (Nat.zero_le _) i.2).1.1.1⟩
      invFun := fun i => ⟨ap (invT n T) i.1, (hp i.1 (Nat.zero_le _) i.2).1.1.2⟩
      left_inv := fun i => Fin.ext (hp i.1 (Nat.zero_le _) i.2).1.2
      right_inv := fun i => Fin.ext (hp i.1 (Nat.zero_le _) i.2).2 }
  have hrep : Rep n T g := fun i hi => by
    rw [idx_of_lt g hi]
    rfl
  refine ⟨Classical.epsilon_spec (p := fun g => Rep n T g) ⟨g, hrep⟩, ?_⟩
  unfold invOK
  rw [allIn_eq_true]
  intro i _ hi
  simpa using (hp i (Nat.zero_le _) hi).1.2

theorem rep_permOfTab {T : Table} (h : permOK n T = true) : Rep n T (permOfTab n T) :=
  (permOK_spec h).1

theorem permOK_of_tabsOK {ts : Array Table} (h : tabsOK n ts = true) {i : ℕ} (hi : i < ts.size) :
    permOK n ts[i]! = true := by
  unfold tabsOK at h
  rw [Array.all_eq_true] at h
  have := h i hi
  rwa [getElem!_pos ts i hi]

@[expose] noncomputable def letterPerm {G : Type*} [Group G] (π : ℕ → G) (m : ℕ) (l : ℤ) : G :=
  if 0 < l ∧ (l - 1).toNat < m then π (l - 1).toNat
  else if l < 0 ∧ (-l - 1).toNat < m then (π (-l - 1).toNat)⁻¹ else 1

theorem rep_letterTab {G : Type*} [Group G] [MulAction G (Fin n)] (hn : n < 2 ^ 32)
    {gs : Array Table} {π : ℕ → G} (hrep : ∀ l < gs.size, Rep n gs[l]! (π l))
    (hinv : ∀ l < gs.size, invOK n gs[l]! (invT n gs[l]!) = true) (l : ℤ) :
    Rep n (letterTab n gs (gs.map (invT n)) l) (letterPerm π gs.size l) := by
  unfold letterTab letterPerm
  by_cases h1 : 0 < l ∧ (l - 1).toNat < gs.size
  · rw [if_pos h1, if_pos h1]
    exact hrep _ h1.2
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : l < 0 ∧ (-l - 1).toNat < gs.size
    · have h2' : l < 0 ∧ (-l - 1).toNat < (gs.map (invT n)).size := by
        simpa [Array.size_map] using h2
      rw [if_pos h2', if_pos h2]
      have hk : (-l - 1).toNat < gs.size := h2.2
      have e : (gs.map (invT n))[(-l - 1).toNat]! = invT n (gs[(-l - 1).toNat]!) := by
        rw [getElem!_pos _ _ (by rw [Array.size_map]; exact hk), Array.getElem_map,
          getElem!_pos gs _ hk]
      rw [e]
      exact Rep.inv_of_invOK (hrep _ hk) (hinv _ hk)
    · have h2' : ¬(l < 0 ∧ (-l - 1).toNat < (gs.map (invT n)).size) := by
        simpa [Array.size_map] using h2
      rw [if_neg h2', if_neg h2]
      exact Rep.idT hn

theorem rep_wordT_letters {G : Type*} [Group G] [MulAction G (Fin n)] (hn : n < 2 ^ 32)
    {gs : Array Table} {π : ℕ → G} (hrep : ∀ l < gs.size, Rep n gs[l]! (π l))
    (hinv : ∀ l < gs.size, invOK n gs[l]! (invT n gs[l]!) = true) (w : List ℤ) :
    Rep n (wordT n (letterTab n gs (gs.map (invT n))) w) (wordG (letterPerm π gs.size) w) :=
  Rep.wordT hn w fun l _ => rep_letterTab hn hrep hinv l

theorem wordG_eq_one_of_relatorsOK (hn : n < 2 ^ 32) {gs : Array Table} {π : ℕ → Perm (Fin n)}
    (hrep : ∀ l < gs.size, Rep n gs[l]! (π l))
    (hinv : ∀ l < gs.size, invOK n gs[l]! (invT n gs[l]!) = true) {ws : List (List ℤ)}
    (h : relatorsOK n gs (gs.map (invT n)) ws = true) {w : List ℤ} (hw : w ∈ ws) :
    wordG (letterPerm π gs.size) w = 1 := by
  unfold relatorsOK at h
  have h1 := List.all_eq_true.1 h w hw
  exact rep_unique (rep_of_eqTab (rep_wordT_letters hn hrep hinv w) h1) (Rep.idT hn)

theorem ap_zero_of_fixOK {gs : Array Table} (h : fixOK gs = true) {i : ℕ}
    (hi : i ∈ [0, 1, 2, 3, 4, 5, 6, 7, 9, 10]) : ap gs[i]! 0 = 0 := by
  unfold fixOK at h
  simpa using List.all_eq_true.1 h i hi

theorem ap_zero_of_moveOK {gs : Array Table} (h : moveOK gs = true) : ap gs[21]! 0 ≠ 0 := by
  unfold moveOK at h
  simpa using h

theorem slpOK_spec {G : Type*} [Group G] [MulAction G (Fin n)] (hn : n < 2 ^ 32)
    {xs ms : Array Table} {xg : ℕ → G} (hx : ∀ i < 11, Rep n xs[i]! (xg i))
    (h : slpOK n xs ms = true) :
    xs.size = 11 ∧ ms.size = 2 ∧
      Rep n ms[0]! (runSLPG (compileSLP 11 (slpLines bridgeGensText))
        (fun r => if r < 11 then xg r else 1) 13) ∧
      Rep n ms[1]! (runSLPG (compileSLP 11 (slpLines bridgeGensText))
        (fun r => if r < 11 then xg r else 1) 14) := by
  unfold slpOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hxs, hlt⟩, hprog⟩, hok⟩, hms⟩, h0⟩, h1⟩ := h
  generalize slpLines bridgeGensText = ls at *
  set regs : Array Table := xs ++ Array.replicate (ls.size + 1) (idT n) with hregs
  have hget1 : ∀ r, r < 11 → regs[r]! = xs[r]! := by
    intro r hr
    rw [hregs, getElem!_pos _ r (by simp; omega), getElem!_pos xs r (by omega)]
    exact Array.getElem_append_left (by omega)
  have hget2 : ∀ r, 11 ≤ r → r < regs.size → regs[r]! = idT n := by
    intro r hr hr2
    rw [hregs] at hr2 ⊢
    rw [getElem!_pos _ r hr2, Array.getElem_append_right (by omega)]
    simp
  have hrepr : ∀ r < regs.size, Rep n regs[r]! (if r < 11 then xg r else 1) := by
    intro r hr
    by_cases hr11 : r < 11
    · rw [if_pos hr11, hget1 r hr11]
      exact hx r hr11
    · rw [if_neg hr11, hget2 r (by omega) hr]
      exact Rep.idT hn
  have hprog' : ∀ ins ∈ compileSLP 11 ls, instrRegsLt regs.size ins := by
    intro ins hins
    have := List.all_eq_true.1 hprog ins hins
    cases ins <;> simp_all [instrRegsLt]
  obtain ⟨-, hres⟩ := runSLP_rep hn (compileSLP 11 ls) regs
    (fun r => if r < 11 then xg r else 1) hprog' hrepr hok
  exact ⟨hxs, hms, rep_of_eqTab (hres 13 (by omega)) h0, rep_of_eqTab (hres 14 hlt) h1⟩

theorem treeCheck_spec {G : Type*} [Group G] [MulAction G (Fin n)] {g₁ g₂ : Table} {x y : G}
    (h1 : Rep n g₁ x) (h2 : Rep n g₂ y) (h : treeCheck n g₁ g₂ = true) (hn : 0 < n) :
    ∀ p : Fin n, ∃ g ∈ Subgroup.closure ({x, y} : Set G), g • (⟨0, hn⟩ : Fin n) = p := by
  unfold treeCheck at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨-, hok⟩ := h
  obtain ⟨-, -, hpts, -, -, htree⟩ := treeOK_spec h1 h2 hok
  set r := localBFS n 0 g₁ g₂ with hr
  let f : Fin n → Fin n := fun k => ⟨ap r.1 k.1, (hpts k.1 k.2).1⟩
  have hinj : Function.Injective f := by
    intro k k' hkk'
    have e := congrArg (fun u : Fin n => ap r.2.2 u.val) hkk'
    simp only [f, (hpts k.1 k.2).2, (hpts k'.1 k'.2).2] at e
    exact Fin.ext e
  intro p
  obtain ⟨k, hk⟩ := Finite.surjective_of_injective hinj p
  refine ⟨treeElt r.2.1 (lettersG x y) k.1, treeElt_mem _ _ (fun s => ?_) _, ?_⟩
  · unfold lettersG
    split_ifs
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
  · apply Fin.ext
    have := htree k.1 k.2
    rw [idx_of_lt _ hn] at this
    rw [this]
    exact congrArg Fin.val hk

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model
