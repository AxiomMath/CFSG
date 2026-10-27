module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.HNFInputs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.HNFWords
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.HNFTree
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.HNFOrb
public import CFSG.Sporadic.HNSchreier.ArchEq
public import CFSG.Open.MonsterY443Defs

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open CFSG.Sporadic.HNSchreier CFSG.ONSchreier CFSG.ONSchreier.Native
  CFSG.Sporadic.HNSchreier.Native

@[expose] noncomputable def hnfAB : ℕ → ↥JH := fun h => if h = 0 then aJ else bJ

@[expose] noncomputable def hnfG1 : ↥JH := wordProd hnfAB hnfW1

@[expose] noncomputable def hnfG2 : ↥JH := wordProd hnfAB hnfW2

@[expose] noncomputable def hnfGen : ℕ → ↥JH := fun h =>
  if h = 0 then aJ else if h = 1 then hnfG1 else hnfG2

@[expose] noncomputable def hnfC0 : Subgroup ↥JH := Subgroup.closure {aJ, hnfG1, hnfG2}

section Tables

attribute [local irreducible] pword pcomp pinvCand


theorem hnfBytes_eq : hnfBytes = archBytes := archBytes_eq.symm

theorem prep_arch0 : PRep hnfN (hnfArch archBytes 0) (permHom aJ) := by
  intro x
  rw [hnfArch, getElem!_ofFn_nat _ x.2]
  have h := congrArg (fun f : X → X => (f x : ℕ)) (qArch_zero_eq)
  exact h

theorem prep_arch1 : PRep hnfN (hnfArch archBytes 1) (permHom bJ) := by
  intro x
  rw [hnfArch, getElem!_ofFn_nat _ x.2]
  have h := congrArg (fun f : X → X => (f x : ℕ)) (qArch_one_eq)
  exact h

theorem hnfW1_ok : plettersOK 2 hnfW1 = true := by decide

theorem hnfW2_ok : plettersOK 2 hnfW2 = true := by decide

structure TabHyp (tA tAi tB tBi g1 g2 : Array Nat) : Prop where
  A : PRep hnfN tA (permHom aJ)
  B : PRep hnfN tB (permHom bJ)
  g1_eq : g1 = pword hnfN #[tA, tB] #[tAi, tBi] hnfW1
  g2_eq : g2 = pword hnfN #[tA, tB] #[tAi, tBi] hnfW2

variable {tA tAi tB tBi g1 g1i g2 g2i : Array Nat}

theorem TabHyp.prep (h : TabHyp tA tAi tB tBi g1 g2)
    (hok : hnfTabsOK tA tAi tB tBi g1 g1i g2 g2i = true) :
    PRep hnfN tA (permHom aJ) ∧ PRep hnfN tAi (permHom aJ)⁻¹ ∧
    PRep hnfN tB (permHom bJ) ∧ PRep hnfN tBi (permHom bJ)⁻¹ ∧
    PRep hnfN g1 (permHom hnfG1) ∧ PRep hnfN g1i (permHom hnfG1)⁻¹ ∧
    PRep hnfN g2 (permHom hnfG2) ∧ PRep hnfN g2i (permHom hnfG2)⁻¹ := by
  unfold hnfTabsOK at hok
  simp only [Bool.and_eq_true] at hok
  obtain ⟨⟨⟨hA, hB⟩, hG1⟩, hG2⟩ := hok
  have hAi := prep_inv_of_pisInv h.A hA
  have hBi := prep_inv_of_pisInv h.B hB
  have hS : ∀ k < 2, PRep hnfN (#[tA, tB] : Array (Array Nat))[k]! (permHom (hnfAB k)) := by
    intro k hk
    interval_cases k
    · exact h.A
    · exact h.B
  have hSi : ∀ k < 2, PRep hnfN (#[tAi, tBi] : Array (Array Nat))[k]! (permHom (hnfAB k))⁻¹ := by
    intro k hk
    interval_cases k
    · exact hAi
    · exact hBi
  have h1 : PRep hnfN g1 (permHom hnfG1) := by
    rw [h.g1_eq]
    exact prep_pword_prod permHom hnfAB hS hSi hnfW1 hnfW1_ok
  have h2 : PRep hnfN g2 (permHom hnfG2) := by
    rw [h.g2_eq]
    exact prep_pword_prod permHom hnfAB hS hSi hnfW2 hnfW2_ok
  exact ⟨h.A, hAi, h.B, hBi, h1, prep_inv_of_pisInv h1 hG1, h2, prep_inv_of_pisInv h2 hG2⟩

end Tables

section State

attribute [local irreducible] pword pcomp pinvCand

@[expose] noncomputable def hnfSt (pts : Array Nat) (ω : ↥JH) : Array Nat :=
  pts.map fun p => if h : p < hnfN then ((permHom ω ⟨p, h⟩ : X) : ℕ) else 0

theorem hnfSt_size (pts : Array Nat) (ω : ↥JH) : (hnfSt pts ω).size = pts.size := by
  unfold hnfSt
  simp

theorem hnfSt_getElem {pts : Array Nat} {ω : ↥JH} {j : ℕ} (hj : j < pts.size)
    (hp : pts[j]! < hnfN) :
    (hnfSt pts ω)[j]! = ((permHom ω ⟨pts[j]!, hp⟩ : X) : ℕ) := by
  have hj' : j < (hnfSt pts ω).size := by rw [hnfSt_size]; exact hj
  rw [getElem!_pos (hnfSt pts ω) j hj']
  have e : (hnfSt pts ω)[j] = (fun p => if h : p < hnfN then ((permHom ω ⟨p, h⟩ : X) : ℕ)
      else 0) pts[j] := by
    unfold hnfSt
    simp
  rw [e]
  have e2 : pts[j]! = pts[j] := getElem!_pos pts j hj
  simp only [e2] at hp ⊢
  rw [dite_eq_left hp]

theorem hnfStep_getElem {G : Array (Array Nat)} {idx : Array (Array Nat)} {k : ℕ}
    {S : Array Nat} {j : ℕ} (hj : j < (idx[k]!).size) :
    (hnfStep G idx k S)[j]! = (G[k]!)[S[(idx[k]!)[j]!]!]! := by
  unfold hnfStep
  rw [getElem!_pos _ j (by simpa using hj), Array.getElem_map, ← getElem!_pos (idx[k]!) j hj]

theorem hnfSt_step {G Ginv : Array (Array Nat)} {pts pos : Array Nat}
    {idx : Array (Array Nat)} (hP : hnfPtsOK G Ginv pts pos idx = true) {k : ℕ} (hk : k < 3)
    {c : ↥JH} (hG : PRep hnfN G[k]! (permHom c)) (hGi : PRep hnfN Ginv[k]! (permHom c)⁻¹)
    (hsz : (idx[k]!).size = pts.size) (ω : ↥JH) :
    hnfSt pts (conjBy c ω) = hnfStep G idx k (hnfSt pts ω) := by
  unfold hnfPtsOK at hP
  simp only [Bool.and_eq_true, beq_iff_eq] at hP
  obtain ⟨-, hall⟩ := hP
  apply Array.ext
  · rw [hnfSt_size, hnfStep, Array.size_map, hsz]
  · intro j hj1 hj2
    have hj : j < pts.size := by rw [hnfSt_size] at hj1; exact hj1
    have hj' := allBelowN_spec hall hj
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hj'
    obtain ⟨⟨hpt, -⟩, hg⟩ := hj'
    have hgk := allBelowN_spec hg hk
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hgk
    obtain ⟨⟨hidx, hpts⟩, -⟩ := hgk
    have hq0 : pts[(idx[k]!)[j]!]! = (((permHom c)⁻¹ ⟨pts[j]!, hpt⟩ : X) : ℕ) :=
      hpts.trans (hGi ⟨pts[j]!, hpt⟩)
    have hqlt : pts[(idx[k]!)[j]!]! < hnfN := hq0 ▸ ((permHom c)⁻¹ ⟨pts[j]!, hpt⟩).2
    have hq : (⟨pts[(idx[k]!)[j]!]!, hqlt⟩ : X) = (permHom c)⁻¹ ⟨pts[j]!, hpt⟩ :=
      Fin.ext hq0
    have hsj : j < (idx[k]!).size := by rw [hsz]; exact hj
    have hm : (hnfSt pts ω)[(idx[k]!)[j]!]! < hnfN := by
      rw [hnfSt_getElem hidx hqlt]
      exact (permHom ω ⟨pts[(idx[k]!)[j]!]!, hqlt⟩).2
    have hfin : (⟨(hnfSt pts ω)[(idx[k]!)[j]!]!, hm⟩ : X) =
        permHom ω ((permHom c)⁻¹ ⟨pts[j]!, hpt⟩) := by
      apply Fin.ext
      show (hnfSt pts ω)[(idx[k]!)[j]!]! = _
      rw [hnfSt_getElem hidx hqlt, hq]
    rw [← getElem!_pos (hnfSt pts (conjBy c ω)) j hj1, hnfSt_getElem hj hpt,
      ← getElem!_pos (hnfStep G idx k (hnfSt pts ω)) j hj2, hnfStep_getElem hsj,
      hG.apply hm]
    refine Eq.trans ?_ (congrArg (fun y : X => ((permHom c) y : ℕ)) hfin).symm
    simp [conjBy_def, map_mul, map_inv, Equiv.Perm.mul_apply]

end State

section Core

attribute [local irreducible] pword pcomp pinvCand

@[expose] noncomputable def hnfRep (g : List ℤ) : ↥JH := conjBy (wordProd hnfAB g) aJ

theorem wordProd_hnfAB_one : wordProd hnfAB [1] = aJ := by
  simp [wordProd, letterVal, hnfAB]

theorem plettersOK_iff {j : ℕ} {w : List ℤ} :
    plettersOK j w = true ↔ ∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ j := by
  simp [plettersOK, List.all_eq_true]

theorem plettersOK_rep {g : List ℤ} (hg : plettersOK 2 g = true) :
    plettersOK 2 (g ++ [1] ++ hnfInvWord g) = true := by
  rw [plettersOK_iff] at hg ⊢
  intro l hl
  simp only [List.mem_append, hnfInvWord, List.mem_map, List.mem_reverse,
    List.mem_singleton] at hl
  rcases hl with (hl | rfl) | ⟨m, hm, rfl⟩
  · exact hg l hl
  · exact ⟨by norm_num, by norm_num⟩
  · have := hg m hm
    exact ⟨by omega, by omega⟩

variable {tA tAi tB tBi g1 g1i g2 g2i : Array Nat}

theorem hnfRepTab_prep (h : TabHyp tA tAi tB tBi g1 g2)
    (hok : hnfTabsOK tA tAi tB tBi g1 g1i g2 g2i = true) {g : List ℤ}
    (hg : plettersOK 2 g = true) :
    PRep hnfN (hnfRepTab #[tA, tB] #[tAi, tBi] g) (permHom (hnfRep g)) := by
  obtain ⟨hA, hAi, hB, hBi, -⟩ := h.prep hok
  have hS : ∀ k < 2, PRep hnfN (#[tA, tB] : Array (Array Nat))[k]! (permHom (hnfAB k)) := by
    intro k hk
    interval_cases k
    · exact hA
    · exact hB
  have hSi : ∀ k < 2, PRep hnfN (#[tAi, tBi] : Array (Array Nat))[k]! (permHom (hnfAB k))⁻¹ := by
    intro k hk
    interval_cases k
    · exact hAi
    · exact hBi
  have hne : ∀ l ∈ g, l ≠ 0 := fun l hl => (plettersOK_iff.1 hg l hl).1
  have e := prep_pword_prod permHom hnfAB hS hSi _ (plettersOK_rep hg)
  have hinv : wordProd hnfAB (hnfInvWord g) = (wordProd hnfAB g)⁻¹ :=
    wordProd_invWord hnfAB g hne
  have e2 : wordProd hnfAB (g ++ [1] ++ hnfInvWord g) = hnfRep g := by
    rw [wordProd_append, wordProd_append, wordProd_hnfAB_one, hinv]
    rfl
  rw [e2] at e
  exact e

end Core

section Orbit

attribute [local irreducible] pword pcomp pinvCand


@[expose] noncomputable def hnfAct (k : ℕ) (ω : ↥JH) : ↥JH := conjBy (hnfGen k) ω

theorem finite_JH : Finite ↥JH := Finite.of_injective permHom permHom_injective

theorem hnfGen_mem {k : ℕ} (hk : k < 3) : hnfGen k ∈ hnfC0 := by
  interval_cases k
  · exact Subgroup.subset_closure (by simp [hnfGen])
  · exact Subgroup.subset_closure (by simp [hnfGen, hnfG1])
  · exact Subgroup.subset_closure (by simp [hnfGen, hnfG2])

theorem reach_mem_conjOrb {β ω : ↥JH} (h : HNFReach 3 hnfAct β ω) : ω ∈ conjOrb hnfC0 β := by
  induction h with
  | base => exact mem_conjOrb_self _ _
  | step hg _ ih => exact conj_mem_conjOrb ih (hnfGen_mem hg)

theorem ptsOK_lt {G Ginv : Array (Array Nat)} {pts pos : Array Nat} {idx : Array (Array Nat)}
    (hP : hnfPtsOK G Ginv pts pos idx = true) {j : ℕ} (hj : j < pts.size) : pts[j]! < hnfN := by
  unfold hnfPtsOK at hP
  simp only [Bool.and_eq_true, beq_iff_eq] at hP
  have := allBelowN_spec hP.2 hj
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
  exact this.1.1


variable {tA tAi tB tBi g1 g1i g2 g2i : Array Nat}

theorem hnfGen_zero : hnfGen 0 = aJ := by simp [hnfGen]

theorem hnfGen_one : hnfGen 1 = hnfG1 := by simp [hnfGen]

theorem hnfGen_two : hnfGen 2 = hnfG2 := by simp [hnfGen]

theorem hnfOrbitCore_sound (h : TabHyp tA tAi tB tBi g1 g2) {seed : ℕ} {g : List ℤ}
    (hg : plettersOK 2 g = true) {kp : List ℕ} {moves : List (ℕ × ℕ)} {N : ℕ}
    (hc : hnfOrbitCore tA tAi tB tBi g1 g1i g2 g2i seed g kp moves N = true) :
    N ≤ (conjOrb hnfC0 (hnfRep g)).ncard := by
  have := finite_JH
  unfold hnfOrbitCore at hc
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨⟨htab, hpts⟩, hwalk⟩ := hc
  obtain ⟨hA, hAi, hB, hBi, hg1, hg1i, hg2, hg2i⟩ := h.prep htab
  set G : Array (Array Nat) := #[tA, g1, g2] with hGdef
  set Ginv : Array (Array Nat) := #[tAi, g1i, g2i] with hGidef
  set pts := orbitPts G seed with hptsdef
  set pos := hnfPos pts with hposdef
  set idx : Array (Array Nat) :=
    #[hnfIdx tAi pts pos, hnfIdx g1i pts pos, hnfIdx g2i pts pos] with hidxdef
  have hGp : ∀ k < 3, PRep hnfN G[k]! (permHom (hnfGen k)) := by
    intro k hk
    interval_cases k
    · rw [hnfGen_zero]; exact hA
    · rw [hnfGen_one]; exact hg1
    · rw [hnfGen_two]; exact hg2
  have hGip : ∀ k < 3, PRep hnfN Ginv[k]! (permHom (hnfGen k))⁻¹ := by
    intro k hk
    interval_cases k
    · rw [hnfGen_zero]; exact hAi
    · rw [hnfGen_one]; exact hg1i
    · rw [hnfGen_two]; exact hg2i
  have hsz : ∀ k < 3, (idx[k]!).size = pts.size := by
    intro k hk
    interval_cases k
    · simp [hidxdef, hnfIdx]
    · simp [hidxdef, hnfIdx]
    · simp [hidxdef, hnfIdx]
  have hstep : ∀ k < 3, ∀ ω : ↥JH, hnfSt pts (hnfAct k ω) = hnfStep G idx k (hnfSt pts ω) :=
    fun k hk ω => hnfSt_step hpts hk (hGp k hk) (hGip k hk) (hsz k hk) ω
  have hrep := hnfRepTab_prep h htab hg
  have hroot : (pts.map fun p => (hnfRepTab #[tA, tB] #[tAi, tBi] g)[p]!) =
      hnfSt pts (hnfRep g) := by
    apply Array.ext
    · simp [hnfSt_size]
    · intro j hj1 hj2
      have hj : j < pts.size := by simpa using hj1
      have hp := ptsOK_lt hpts hj
      rw [← getElem!_pos _ j hj1, ← getElem!_pos _ j hj2, hnfSt_getElem hj hp]
      have e : (pts.map fun p => (hnfRepTab #[tA, tB] #[tAi, tBi] g)[p]!)[j]! =
          (hnfRepTab #[tA, tB] #[tAi, tBi] g)[pts[j]!]! := by
        rw [getElem!_pos _ j hj1, Array.getElem_map, ← getElem!_pos pts j hj]
      rw [e]
      exact hrep.apply hp
  rw [hroot] at hwalk
  obtain ⟨L, hnd, hlen, hreach⟩ := hnfWalk_sound' (act := hnfAct) hstep (hnfRep g) moves N hwalk
  have hsub : (L.toFinset : Set ↥JH) ⊆ conjOrb hnfC0 (hnfRep g) := by
    intro x hx
    exact reach_mem_conjOrb (hreach x (by simpa using hx))
  have := Set.ncard_le_ncard hsub
  rw [Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd, hlen] at this
  exact this

theorem hnfTabHyp_archive :
    TabHyp (hnfArch hnfBytes 0) (pinvCand hnfN (hnfArch hnfBytes 0)) (hnfArch hnfBytes 1)
      (pinvCand hnfN (hnfArch hnfBytes 1))
      (pword hnfN #[hnfArch hnfBytes 0, hnfArch hnfBytes 1]
        #[pinvCand hnfN (hnfArch hnfBytes 0), pinvCand hnfN (hnfArch hnfBytes 1)] hnfW1)
      (pword hnfN #[hnfArch hnfBytes 0, hnfArch hnfBytes 1]
        #[pinvCand hnfN (hnfArch hnfBytes 0), pinvCand hnfN (hnfArch hnfBytes 1)] hnfW2) :=
  ⟨by rw [hnfBytes_eq]; exact prep_arch0, by rw [hnfBytes_eq]; exact prep_arch1, rfl, rfl⟩

theorem hnfOrbitCheck_sound {seed : ℕ} {g : List ℤ} (hg : plettersOK 2 g = true) {kp : List ℕ}
    {moves : List (ℕ × ℕ)} {N : ℕ} (hc : hnfOrbitCheck hnfBytes seed g kp moves N = true) :
    N ≤ (conjOrb hnfC0 (hnfRep g)).ncard :=
  hnfOrbitCore_sound hnfTabHyp_archive hg hc

end Orbit

end CFSG.EvenSporadicStandard.Solomon78
