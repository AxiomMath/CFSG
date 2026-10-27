module

public import Certificates.Data.Kernel.SporLatSigmaL
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatLat

public section

namespace CFSG.KC.SLSig

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.K1.SporadicPerm

theorem gensIn_iff_gensInL {Lab : Type} [DecidableEq Lab] [Hashable Lab] [Inhabited Lab]
    {act : Array ℕ → Lab → Lab} {Δ : Lab} {D : LatData Lab} {j jj : ℕ} {mt : List (Array ℕ)}
    {lbl : List Lab} (hmt : D.mt[j]! = mt) (hlbl : D.Om[jj]!.lbl.toList = lbl) :
    GensIn act Δ D j jj ↔ gensInL act Δ mt lbl = true := by
  subst hmt hlbl
  simp only [GensIn, gensInL, List.all_eq_true, List.contains_iff_mem, Array.mem_toList_iff]
  refine forall₂_congr fun t _ => ⟨fun ⟨x, hx, e⟩ => ?_, fun h => ?_⟩
  · rw [getElem!_pos _ x hx] at e
    exact Array.mem_iff_getElem.mpr ⟨x, hx, e⟩
  · obtain ⟨x, hx, e⟩ := Array.mem_iff_getElem.mp h
    exact ⟨x, hx, by rw [getElem!_pos _ x hx, e]⟩

section Tables

variable {Γ : Type} [Group Γ] {n : ℕ} [MulAction Γ (Fin n)]

theorem ctabL_tab (g h : Γ) : ctabL (tab n g) (tab n h) = tab n (g * h) := (tab_mul g h).symm

theorem tab_one_eq : tab n (1 : Γ) = List.range n := by
  unfold tab
  simp

theorem eq_one_of_tab [FaithfulSMul Γ (Fin n)] {g : Γ} (h : tab n g = List.range n) : g = 1 := by
  refine base_of_faithful (n := n) g fun b hb => ?_
  have hb' : b < n := List.mem_range.mp hb
  unfold act
  rw [h]
  simp [List.getD_eq_getElem?_getD, hb']

omit [MulAction Γ (Fin n)] in
theorem mul_mul_eq_one {e : Γ} (he : orderOf e = 3) : e * (e * e) = 1 := by
  rw [← pow_three]
  have := pow_orderOf_eq_one e
  rwa [he] at this

theorem isOrd3L_of_orderOf [FaithfulSMul Γ (Fin n)] {e : Γ} (he : orderOf e = 3) :
    isOrd3L n (tab n e) = true := by
  have h1 : e ≠ 1 := fun h => by rw [h, orderOf_one] at he; omega
  unfold isOrd3L
  rw [Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · rw [Bool.not_eq_true', beq_eq_false_iff_ne]
    exact fun h => h1 (eq_one_of_tab h)
  · rw [beq_iff_eq, ctabL_tab, ctabL_tab, mul_mul_eq_one he, tab_one_eq]

theorem wordTabT_eq (tabs : Array (Array ℕ)) (w : List ℕ) :
    wordTabT tabs n w = (wordTabA tabs n w).toList := by
  simp [wordTabT, wordTabA, Array.toList_range]

end Tables

section Sound

variable {Γ : Type} [Group Γ] [Finite Γ] {n : ℕ} [MulAction Γ (Fin n)]
  {Lab : Type} [DecidableEq Lab] [Hashable Lab] [Inhabited Lab] (C : LatCtx Γ n Lab)

theorem sTabs_toList : C.D.sTabs.map Array.toList = C.sg.map (tab n) := by
  rw [← C.hsg]
  simp [genTabs]

theorem tab_mem_of_closed {LS : List (List ℕ)}
    (hS : sylowClosedL n (C.D.sTabs.map Array.toList) LS = true) {s : Γ} (hs : s ∈ C.S) :
    tab n s ∈ LS := by
  simp only [sylowClosedL, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at hS
  rw [← C.hSeq] at hs
  have hs' : s ∈ Submonoid.closure {x | x ∈ C.sg} := by
    rw [← Subgroup.closure_toSubmonoid_of_finite]; exact hs
  clear hs
  induction hs' using Submonoid.closure_induction_left with
  | one => rw [tab_one_eq]; exact hS.1
  | mul_left x hx y _ ih =>
    rw [← ctabL_tab]
    have hx' : tab n x ∈ C.D.sTabs.map Array.toList := by
      rw [sTabs_toList]; exact List.mem_map.mpr ⟨x, hx, rfl⟩
    exact hS.2 _ ih _ hx'

theorem tab_mem_memberTabsL {LS : List (List ℕ)}
    (hS : sylowClosedL n (C.D.sTabs.map Array.toList) LS = true) {j : ℕ} (hj : j < C.J) {g : Γ}
    (hg : g ∈ C.Y j) : tab n g ∈ memberTabsL n C.D LS j := by
  obtain ⟨i, hi, hgi⟩ := (C.Y_mem_iff hj g).mp hg
  set els := (C.sg ++ C.gens j).toArray with hels
  set pw := C.D.Om[j]!.pathWord i i with hpw
  have hreach := (C.hOm hj).reach C.hlaw C.hΔ els (genTabs_hel' _) i i le_rfl hi
  have hlt : ∀ l ∈ pw, l < els.size := by
    intro l hl
    have := (C.hOm hj).pathWord_lt i i hi l hl
    rwa [genTabs_size] at this
  have hs : (evalElt els pw)⁻¹ * g ∈ C.S :=
    (lab_eq_iff C.hlaw C.hΔ _ _).mp (by rw [hreach, hgi])
  have hT : wordTabT (C.D.sTabs ++ C.D.mt[j]!).toArray n pw = tab n (evalElt els pw) := by
    have := wordTabA_eq els (genTabs n (C.sg ++ C.gens j)).toArray (genTabs_hel _) pw hlt
    rw [C.Y_letters hj] at this
    rw [wordTabT_eq, this]
  unfold memberTabsL
  refine List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi, ?_⟩
  refine List.mem_map.mpr ⟨tab n ((evalElt els pw)⁻¹ * g), tab_mem_of_closed C hS hs, ?_⟩
  rw [hT, ctabL_tab, mul_inv_cancel_left]

theorem sigmaCheckL_sound [FaithfulSMul Γ (Fin n)] {act : List ℕ → Lab → Lab}
    {lbl : ℕ → List Lab} {js ks : List ℕ} (hjs : ∀ j ∈ js, j < C.J) (hks : ∀ k ∈ ks, k < C.J)
    (hact : ∀ g : Γ, act (tab n g) C.Δ = lab n C.A C.Δ g)
    (hlbl : ∀ j ∈ js, lbl j = C.D.Om[j]!.lbl.toList)
    (h : sigmaCheckL act n C.Δ C.D lbl js ks = true) :
    ∀ j ∈ js, ∀ k ∈ ks, ∀ e x σ : Γ, e ∈ C.Y j → orderOf e = 3 → x ∈ C.Y k → x ∉ C.Y j →
      orderOf x = 3 → e * x = x * e → σ ∈ C.S → σ * e * σ⁻¹ = e⁻¹ → σ * x * σ⁻¹ = x → False := by
  intro j hj k hk e x σ he he3 hx hxj hx3 hcomm hσ hinv hcen
  simp only [sigmaCheckL, sigPairOK, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
    Bool.not_eq_true', beq_eq_false_iff_ne] at h
  obtain ⟨hclosed, hall⟩ := h
  have hmemE : tab n e ∈ ord3TabsL n C.D (sylowListL n (C.D.sTabs.map Array.toList)) j :=
    List.mem_filter.mpr ⟨tab_mem_memberTabsL C hclosed (hjs j hj) he, isOrd3L_of_orderOf he3⟩
  have hmemX : tab n x ∈ ord3TabsL n C.D (sylowListL n (C.D.sTabs.map Array.toList)) k :=
    List.mem_filter.mpr ⟨tab_mem_memberTabsL C hclosed (hks k hk) hx, isOrd3L_of_orderOf hx3⟩
  have h1 := hall j hj k hk _ hmemE _ hmemX
  have hinv' : σ * e = (e * e) * σ := by
    rw [mul_inv_eq_iff_eq_mul] at hinv
    rw [hinv, inv_eq_of_mul_eq_one_right (mul_mul_eq_one he3)]
  have hcen' : σ * x = x * σ := mul_inv_eq_iff_eq_mul.mp hcen
  rcases h1 with (h1 | h1) | h1
  · exact h1 (by rw [ctabL_tab, ctabL_tab, hcomm])
  · apply hxj
    have h2 : lab n C.A C.Δ x ∈ C.D.Om[j]!.lbl := by
      rw [hact, hlbl j hj, List.contains_iff_mem, Array.mem_toList_iff] at h1
      exact h1
    obtain ⟨i, hi, hie⟩ := Array.mem_iff_getElem.mp h2
    refine (C.Y_mem_iff (hjs j hj) x).mpr ⟨i, hi, ?_⟩
    rw [getElem!_pos _ i hi, hie]
  · rcases h1 _ (tab_mem_of_closed C hclosed hσ) with h2 | h2
    · exact h2 (by rw [ctabL_tab, ctabL_tab, ctabL_tab, hinv'])
    · exact h2 (by rw [ctabL_tab, ctabL_tab, hcen'])

end Sound

end CFSG.KC.SLSig

end
