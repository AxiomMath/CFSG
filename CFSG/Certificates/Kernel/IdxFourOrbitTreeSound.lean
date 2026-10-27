module

public import Certificates.Data.Kernel.IdxFourOrbitTreeK
public import CFSG.Certificates.Kernel.IdxFourChainSound
public import CFSG.GF2Type.Smith1979.IdxFourModelOrbitInputs
public import CFSG.GF2Type.Smith1979.IdxFourModelBasic

public section

namespace CFSG.KC.IF4O

open CFSG.KC.IF4C CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.Viol
open CFSG.GF2Type.Smith1979.IdxFour

theorem nbeq (a b : Nat) : Nat.beq a b = (a == b) :=
  Bool.eq_iff_iff.2 (by rw [Nat.beq_eq, beq_iff_eq])

theorem wtK_eq (n : Nat) : wtK n = Orb.wtN n := rfl

theorem peK_eq (n : Nat) : peK n = Orb.prodExpN n := rfl

theorem o378K_eq (n : Nat) : o378K n = Orb.inO378b n := by
  simp only [o378K, Orb.inO378b, nbeq, wtK_eq, peK_eq]

theorem singK_eq (n : Nat) : singK n = (Orb.inO378b n || Orb.inO1701b n) := by
  have key : ∀ w p : Nat, (Nat.beq w 2 || Nat.beq w 4 || Nat.beq w 6) =
      (((w == 2) || ((w == 6) && (p == 0))) || ((w == 4) || ((w == 6) && (p != 0)))) := by
    intro w p
    simp only [nbeq]
    by_cases e : p = 0 <;>
      rcases (by omega : w = 2 ∨ w = 4 ∨ w = 6 ∨ (w ≠ 2 ∧ w ≠ 4 ∧ w ≠ 6)) with
        rfl | rfl | rfl | ⟨h2, h4, h6⟩ <;> simp_all [beq_false_of_ne]
  exact key (Orb.wtN n) (Orb.prodExpN n)

theorem inO378b_eq_false {n : Nat} (h : Orb.inO1701b n = true) : Orb.inO378b n = false := by
  have key : ∀ w p : Nat, ((w == 4) || ((w == 6) && (p != 0))) = true →
      ((w == 2) || ((w == 6) && (p == 0))) = false := by
    intro w p
    by_cases e : p = 0 <;>
      rcases (by omega : w = 2 ∨ w = 4 ∨ w = 6 ∨ (w ≠ 2 ∧ w ≠ 4 ∧ w ≠ 6)) with
        rfl | rfl | rfl | ⟨h2, h4, h6⟩ <;> simp_all [beq_false_of_ne]
  exact key (Orb.wtN n) (Orb.prodExpN n) h

@[expose] noncomputable def rootK (n : Nat) : Nat := bif o378K n then 3 else 15

theorem exists_E0_of_rows {G : Nat} (h0 : rowsP (look G 0) = a3Rows)
    (h1 : rowsP (look G 1) = a5Rows) (h2 : rowsP (look G 2) = y3Rows) :
    ∀ g < 3, ∃ U ∈ E0, IsP U (look G g) := by
  have key : ∀ {g : Nat} {r : Array ℕ}, r ∈ e0Gens → rowsP (look G g) = r →
      ∃ U ∈ E0, IsP U (look G g) := fun {g r} hr h =>
    ⟨_, gen_mem gensOK_e0Gens hr, fun v => by rw [eqvOf_apply, linP_eq_of_rowsP h]⟩
  intro g hg
  interval_cases g
  · exact key (by simp [e0Gens]) h0
  · exact key (by simp [e0Gens]) h1
  · exact key (by simp [e0Gens]) h2

theorem reach_of_treeOK {G D : Nat} (hT : treeOK G D = true)
    (hG : ∀ g < 3, ∃ U ∈ E0, IsP U (look G g)) :
    ∀ n < 4096, singK n = true → ∃ U ∈ E0, U (vecOf (rootK n)) = vecOf n := by
  have hN := (allBelow_iff 4096 _).1 hT
  suffices h : ∀ d n, depT D n = d → n < 4096 → singK n = true →
      ∃ U ∈ E0, U (vecOf (rootK n)) = vecOf n from fun n hn hs => h _ n rfl hn hs
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro n hd hn hs
  by_cases h3 : n = 3
  · subst h3
    have hr : rootK 3 = 3 := by decide +kernel
    exact ⟨1, one_mem _, by rw [hr]; rfl⟩
  by_cases h15 : n = 15
  · subst h15
    have hr : rootK 15 = 15 := by decide +kernel
    exact ⟨1, one_mem _, by rw [hr]; rfl⟩
  have hnode := hN n hn
  simp only [nodeOK, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', Nat.beq_eq,
    Nat.blt_eq, hs, h3, h15] at hnode
  obtain ⟨⟨⟨⟨hg, hp⟩, hc⟩, hdp⟩, he⟩ := hnode.resolve_left (by simp)
  have hcl : o378K (parT D n) = o378K n := by
    cases h1 : o378K (parT D n) <;> cases h2 : o378K n <;> simp_all
  have hroot : rootK (parT D n) = rootK n := by rw [rootK, rootK, hcl]
  have hplt : parT D n < 4096 := lt_of_le_of_lt (Nat.and_le_right (n := f24 D n)) (by norm_num)
  obtain ⟨U, hU, hUe⟩ := ih _ (hd ▸ hdp) (parT D n) rfl hplt hp
  obtain ⟨A, hA, hAP⟩ := hG _ hg
  refine ⟨A * U, mul_mem hA hU, ?_⟩
  rw [LinearEquiv.mul_apply, ← hroot, hUe, hAP.apply_code, he]

theorem exists_E0_of_inO378b {G D : Nat} (hT : treeOK G D = true)
    (hG : ∀ g < 3, ∃ U ∈ E0, IsP U (look G g)) (v : V12) (hv : Orb.inO378b (codeOf v) = true) :
    ∃ U ∈ E0, U (vecOf 3) = v := by
  have hs : singK (codeOf v) = true := by rw [singK_eq, hv, Bool.true_or]
  obtain ⟨U, hU, h⟩ := reach_of_treeOK hT hG _ (codeOf_lt v) hs
  have hr : rootK (codeOf v) = 3 := by rw [rootK, o378K_eq, hv]; rfl
  rw [hr, vecOf_codeOf] at h
  exact ⟨U, hU, h⟩

theorem exists_E0_of_inO1701b {G D : Nat} (hT : treeOK G D = true)
    (hG : ∀ g < 3, ∃ U ∈ E0, IsP U (look G g)) (v : V12) (hv : Orb.inO1701b (codeOf v) = true) :
    ∃ U ∈ E0, U (vecOf 15) = v := by
  have hs : singK (codeOf v) = true := by rw [singK_eq, hv, Bool.or_true]
  obtain ⟨U, hU, h⟩ := reach_of_treeOK hT hG _ (codeOf_lt v) hs
  have hr : rootK (codeOf v) = 15 := by rw [rootK, o378K_eq, inO378b_eq_false hv]; rfl
  rw [hr, vecOf_codeOf] at h
  exact ⟨U, hU, h⟩

end CFSG.KC.IF4O

end
