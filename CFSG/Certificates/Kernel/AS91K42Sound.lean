module

public import Certificates.Data.Kernel.AS91K42
public import CFSG.Certificates.Kernel.HJ12KTSound

public section

namespace Certificates.Kernel.AS91K42

open Certificates.Kernel.HJ12K CFSG.KC.Mat12P CFSG.Quasithin.H13.AS91.Two
  CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.IdxFour.Orb

theorem appN_rows {g : Array ℕ} {c : List ℕ} (hg : g.toList = c) (hl : c.length = 12)
    (hb : ∀ x ∈ c, x < 4096) : appN g = mvNR c := by
  subst hg
  funext n
  rw [← native_appN, GammaUList.appN_eq hl hb n, appL_eq_mvNR]

theorem appN_gam : gamGens.map appN = gamF := by
  rw [gamGens, gamF, List.map_cons, List.map_cons, List.map_nil,
    appN_rows (g := m1Rows) (c := m1L) rfl (by decide) (by decide),
    appN_rows (g := m2Rows) (c := m2L) rfl (by decide) (by decide)]

theorem appN_nGens : nGensI.map appN = nF := by
  rw [nGensI, nF, List.map_cons, List.map_cons, List.map_cons, List.map_cons, List.map_cons,
    List.map_cons, List.map_nil,
    appN_rows (g := m1Rows) (c := m1L) rfl (by decide) (by decide),
    appN_rows (g := m2Rows) (c := m2L) rfl (by decide) (by decide),
    appN_rows (g := sRows) (c := sL) rfl (by decide) (by decide),
    appN_rows (g := m2InvRows) (c := m2IL) rfl (by decide) (by decide),
    appN_rows (g := sInvRows) (c := sIL) rfl (by decide) (by decide)]

theorem rows_lt {g : Array ℕ} (hg : g.toList.all (fun x => Nat.blt x 4096) = true) :
    ∀ x ∈ g, x < 4096 := by
  intro x hx
  have h := List.all_eq_true.1 hg x (Array.mem_toList_iff.2 hx)
  rwa [Nat.blt_eq] at h

theorem gam_lt : ∀ g ∈ gamGens, ∀ n, appN g n < 4096 := by
  intro g hg n
  simp only [gamGens, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · exact StepA.appN_lt (rows_lt (by decide)) n
  · exact StepA.appN_lt (rows_lt (by decide)) n

theorem orbitList_eq {gs : List (Array ℕ)} {fs : List (ℕ → ℕ)} (hfs : gs.map appN = fs) (v : ℕ) :
    orbitList gs v = closO fs 4096 [v] (Nat.shiftLeft 1 v) [] := by
  rw [orbitList, hfs, ← native_bfsClosure]
  refine bfsClosure_O _ 4096 [v] [] _ _ fun k => ?_
  rw [Std.HashSet.contains_insert, Std.HashSet.contains_empty, Bool.or_false]
  change _ = (1 <<< v).testBit k
  rw [Nat.one_shiftLeft, Nat.testBit_two_pow]
  by_cases h : v = k <;> simp [h]

theorem all_range_congr {N : ℕ} {p q : ℕ → Bool} (h : ∀ n < N, p n = q n) :
    (List.range N).all p = (List.range N).all q := by
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  exact ⟨fun hp n hn => (h n (List.mem_range.1 hn)) ▸ hp n hn,
    fun hq n hn => (h n (List.mem_range.1 hn)).symm ▸ hq n hn⟩

theorem orbitSetOK_of {gs : List (Array ℕ)} {fs : List (ℕ → ℕ)} (hfs : gs.map appN = fs)
    (hlt : ∀ g ∈ gs, ∀ n, appN g n < 4096) {v : ℕ} (hv : v < 4096) {P : ℕ → Bool} {Pm : ℕ}
    (hP : ∀ n < 4096, P n = bitQ Pm n) (h : orbOK fs v Pm = true) : orbitSetOK gs v P = true := by
  simp only [orbOK, Bool.and_eq_true] at h
  obtain ⟨hm, hpv, hall⟩ := h
  have hm' := Nat.eq_of_beq_eq_true hm
  rw [orbitSetOK, orbitList_eq hfs]
  simp only [Std.HashSet.contains_ofList, contains_bitQ, hm', Bool.and_eq_true]
  refine ⟨(hP v hv).trans hpv, ?_⟩
  rw [all_range_congr (q := fun n => !(bitQ Pm n) || (bitQ Pm n && fs.all fun f => bitQ Pm (f n)))
    fun n hn => ?_]
  · exact hall
  have e : (gs.all fun g => P (appN g n)) = fs.all fun f => bitQ Pm (f n) := by
    rw [← hfs, Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
    simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    exact ⟨fun h g hg => by rw [← hP _ (hlt g hg n)]; exact h g hg,
      fun h g hg => by rw [hP _ (hlt g hg n)]; exact h g hg⟩
  rw [hP n hn, e]

theorem q0b_eq (h : q0OK = true) : ∀ n < 4096, q0b n = bitQ q0M n := by
  intro n hn
  have h' := List.all_eq_true.1 h n (List.mem_range.2 hn)
  exact beq_iff_eq.1 h'

theorem inO1b_eq : inO1b = bitQ o1Mask := funext fun n => (bitQ_eq _ _).symm

theorem inO2b_eq : inO2b = bitQ o2Mask := funext fun n => (bitQ_eq _ _).symm

theorem orbitOK42_of (hq : q0OK = true) (h1 : orbOK gamF 3 o1Mask = true)
    (h2 : orbOK gamF 5 o2Mask = true) (h3 : orbOK gamF 1 q0M = true) (hi : invK = true)
    (hp : partK = true) (hc : cntK = true) : orbitOK42 () = true := by
  have hq' := q0b_eq hq
  have e1 : orbitSetOK gamGens 3 inO1b = true :=
    orbitSetOK_of appN_gam gam_lt (by decide) (fun n _ => by rw [inO1b_eq]) h1
  have e2 : orbitSetOK gamGens 5 inO2b = true :=
    orbitSetOK_of appN_gam gam_lt (by decide) (fun n _ => by rw [inO2b_eq]) h2
  have e3 : orbitSetOK gamGens 1 q0b = true := orbitSetOK_of appN_gam gam_lt (by decide) hq' h3
  have e4 : ((List.range 4096).all fun n => nGensI.all fun g =>
      (!inO1b n || inO1b (appN g n)) && (!inO2b n || inO2b (appN g n))) = true := by
    rw [inO1b_eq, inO2b_eq]
    rw [invK, ← appN_nGens] at hi
    simpa only [List.all_map, Function.comp_def] using hi
  have e5 : ((List.range 4096).all fun n =>
      let k := ([q0b n, inO1b n, inO2b n].filter id).length
      if n == 0 then k == 0 else k == 1) = true := by
    rw [inO1b_eq, inO2b_eq, all_range_congr fun n hn => by rw [hq' n hn]]
    exact hp
  simp only [cntK, Bool.and_eq_true] at hc
  simp only [orbitOK42, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨e1, e2⟩, e3⟩, e4⟩, e5⟩, by rw [inO1b_eq]; exact hc.1⟩, by rw [inO2b_eq]; exact hc.2⟩

end Certificates.Kernel.AS91K42
