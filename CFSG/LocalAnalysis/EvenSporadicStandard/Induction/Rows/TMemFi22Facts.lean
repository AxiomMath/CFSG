module

public import CFSG.Sporadic.Schreier.RuCore
public import Certificates.Certificate27101
public import CFSG.Sporadic.FischerOddCore.Fi22ExtBase

public noncomputable section

namespace CFSG.EvenSporadicStandard.Induction.TMemFi22Cert

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer
  CFSG.Sporadic.FischerOddCore CFSG.Sporadic.RuSchreier CFSG.Certificates

theorem rep_getD_two {n : Nat} {t₀ t₁ : Array Nat} {g₀ g₁ : Equiv.Perm (Fin n)}
    (h₀ : Rep n t₀ g₀) (h₁ : Rep n t₁ g₁) :
    ∀ h < 2, Rep n #[t₀, t₁][h]! ([g₀, g₁].getD h 1) := by
  intro h hh
  interval_cases h
  · simpa using h₀
  · simpa using h₁

theorem rep_getD_two_inv {n : Nat} {t₀ t₁ : Array Nat} {g₀ g₁ : Equiv.Perm (Fin n)}
    (h₀ : Rep n t₀ g₀⁻¹) (h₁ : Rep n t₁ g₁⁻¹) :
    ∀ h < 2, Rep n #[t₀, t₁][h]! ([g₀, g₁].getD h 1)⁻¹ := by
  intro h hh
  interval_cases h
  · simpa using h₀
  · simpa using h₁

theorem eq_of_forest {α : Type*} {c₁ c₂ x y : Equiv.Perm α} {isRoot : α → Prop} {par : α → α}
    {dep lab : α → Nat}
    (htree : ∀ p, isRoot p ∨ (dep p = dep (par p) + 1 ∧
      ((lab p = 1 ∧ c₁ (par p) = p) ∨ (lab p = 2 ∧ c₂ (par p) = p))))
    (hx₁ : x * c₁ = c₁ * x) (hx₂ : x * c₂ = c₂ * x) (hy₁ : y * c₁ = c₁ * y)
    (hy₂ : y * c₂ = c₂ * y) (hroot : ∀ p, isRoot p → x p = y p) : x = y := by
  have key : ∀ d, ∀ p, dep p = d → x p = y p := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro p hp
      rcases htree p with hr | ⟨hd, hc⟩
      · exact hroot p hr
      · have hq : x (par p) = y (par p) := ih (dep (par p)) (by omega) (par p) rfl
        rcases hc with ⟨-, h⟩ | ⟨-, h⟩
        · rw [← h]
          have e1 : x (c₁ (par p)) = c₁ (x (par p)) :=
            congrArg (fun g : Equiv.Perm α => g (par p)) hx₁
          have e2 : y (c₁ (par p)) = c₁ (y (par p)) :=
            congrArg (fun g : Equiv.Perm α => g (par p)) hy₁
          rw [e1, e2, hq]
        · rw [← h]
          have e1 : x (c₂ (par p)) = c₂ (x (par p)) :=
            congrArg (fun g : Equiv.Perm α => g (par p)) hx₂
          have e2 : y (c₂ (par p)) = c₂ (y (par p)) :=
            congrArg (fun g : Equiv.Perm α => g (par p)) hy₂
          rw [e1, e2, hq]
  exact Equiv.ext fun p => key _ p rfl

theorem tmFi22Check_parts :
    fcBasicCheck = true ∧ fcTreeCheck = true ∧ fcConsCheck = true := by
  have h := Certificates.certificate27101
  simp only [tmFi22Check, Bool.and_eq_true] at h
  obtain ⟨⟨hb, ht⟩, hc⟩ := h
  exact ⟨hb, ht, hc⟩

theorem fc_basic :
    isInvA 3510 (fi22ChainGen 0) (invCand 3510 (fi22ChainGen 0)) = true ∧
    isInvA 3510 (fi22ChainGen 1) (invCand 3510 (fi22ChainGen 1)) = true ∧
    isInvA 3510 fcT2 (invCand 3510 fcT2) = true ∧
    lettersOK 2 fcWord1 = true ∧ lettersOK 2 fcWord2 = true ∧
    (∀ w ∈ fcCons1, lettersOK 2 w = true) ∧ (∀ w ∈ fcCons2, lettersOK 2 w = true) ∧
    (∀ w ∈ fcCons3, lettersOK 2 w = true) ∧
    isInvA 3510 fcC1 (invCand 3510 fcC1) = true ∧ isInvA 3510 fcC2 (invCand 3510 fcC2) = true ∧
    eqA 3510 (compA 3510 fcC1 fcT2) (compA 3510 fcT2 fcC1) = true ∧
    eqA 3510 (compA 3510 fcC2 fcT2) (compA 3510 fcT2 fcC2) = true ∧
    fcR1 < 3510 ∧ fcR2 < 3510 ∧ fcR3 < 3510 ∧ fcR1 ≠ fcR2 ∧ fcR1 ≠ fcR3 ∧
    fcT2[fcR1]! = fcR1 ∧ fcT2[fcR2]! = fcR2 ∧ fcT2[fcR3]! = fcT2R3 ∧
    fcT2R3 < 3510 ∧ fcT2R3 ≠ fcR3 := by
  obtain ⟨hb, -⟩ := tmFi22Check_parts
  simp only [fcBasicCheck, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc] at hb
  obtain ⟨h0, h1, h2, hl1, hl2, hw1, hw2, hw3, hi1, hi2, hc1, hc2, hr1, hr2, hr3, hr12, hr13,
    ht1, ht2, ht3, hlt, hne⟩ := hb
  exact ⟨h0, h1, h2, hl1, hl2, fun w hw => List.all_eq_true.1 hw1 w hw,
    fun w hw => List.all_eq_true.1 hw2 w hw, fun w hw => List.all_eq_true.1 hw3 w hw, hi1, hi2,
    hc1, hc2, hr1, hr2, hr3, hr12, hr13, ht1, ht2, ht3, hlt, hne⟩

theorem fc_tree :
    ∀ p < 3510, (fcPar[p]! = p ∧ fcDep[p]! = 0 ∧ (p = fcR1 ∨ p = fcR2 ∨ p = fcR3)) ∨
      (fcPar[p]! < 3510 ∧ fcDep[p]! = fcDep[fcPar[p]!]! + 1 ∧
        ((fcLab[p]! = 1 ∧ fcC1[fcPar[p]!]! = p) ∨ (fcLab[p]! = 2 ∧ fcC2[fcPar[p]!]! = p))) := by
  obtain ⟨-, ht, -⟩ := tmFi22Check_parts
  unfold fcTreeCheck at ht
  intro p hp
  have := allLt_spec ht hp
  simpa only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc,
    or_assoc] using this

theorem fc_cons :
    (fcTabs fcCons1).all (fun t => t[fcR1]! == fcR1) = true ∧
    fcFixCover (fcTabs fcCons1) [fcR1] = true ∧
    (fcTabs fcCons2).all (fun t => t[fcR2]! == fcR2) = true ∧
    fcFixCover (fcTabs fcCons2) [fcR1, fcR2] = true ∧
    (fcTabs fcCons3).all (fun t => t[fcR3]! == fcR3) = true ∧
    fcFixCover (fcTabs fcCons3) [fcR1, fcR3, fcT2R3] = true := by
  obtain ⟨-, -, hc⟩ := tmFi22Check_parts
  simpa only [fcConsCheck, Bool.and_eq_true, and_assoc] using hc

def fcc1 : Equiv.Perm (Fin 3510) := evalSigned [fi22GenPerm 0, fi22GenPerm 1] fcWord1

def fcc2 : Equiv.Perm (Fin 3510) := evalSigned [fi22GenPerm 0, fi22GenPerm 1] fcWord2

theorem fi22GenPerm_mem {k : Nat} (hk : k < 2) : fi22GenPerm k ∈ fi22P := by
  have h : fi22Chain.original.get ⟨k, hk⟩ ∈ fi22P :=
    Subgroup.subset_closure (schreier_vector_get_mem_toList fi22Chain.original ⟨k, hk⟩)
  rwa [fi22Chain_original_get] at h

theorem mem_gens_fi22 : ∀ g ∈ [fi22GenPerm 0, fi22GenPerm 1], g ∈ fi22P := by
  intro g hg
  rcases List.mem_pair.1 hg with rfl | rfl
  · exact fi22GenPerm_mem (by norm_num)
  · exact fi22GenPerm_mem (by norm_num)

theorem fcc1_mem : fcc1 ∈ fi22P := evalSigned_mem mem_gens_fi22 _

theorem fcc2_mem : fcc2 ∈ fi22P := evalSigned_mem mem_gens_fi22 _

section Reps

theorem rep_fcA0 : Rep 3510 (fi22ChainGen 0) (fi22GenPerm 0) := (rep_permOfArr fc_basic.1).1

theorem rep_fcA0i : Rep 3510 (invCand 3510 (fi22ChainGen 0)) (fi22GenPerm 0)⁻¹ :=
  rep_inv_of_isInvA rep_fcA0 fc_basic.1

theorem rep_fcA1 : Rep 3510 (fi22ChainGen 1) (fi22GenPerm 1) := (rep_permOfArr fc_basic.2.1).1

theorem rep_fcA1i : Rep 3510 (invCand 3510 (fi22ChainGen 1)) (fi22GenPerm 1)⁻¹ :=
  rep_inv_of_isInvA rep_fcA1 fc_basic.2.1

theorem rep_fcGen2 : ∀ h < 2, Rep 3510 fcGen2[h]! ([fi22GenPerm 0, fi22GenPerm 1].getD h 1) :=
  rep_getD_two rep_fcA0 rep_fcA1

theorem rep_fcGen2i :
    ∀ h < 2, Rep 3510 fcGen2i[h]! ([fi22GenPerm 0, fi22GenPerm 1].getD h 1)⁻¹ :=
  rep_getD_two_inv rep_fcA0i rep_fcA1i

theorem rep_fcC1 : Rep 3510 fcC1 fcc1 := by
  unfold fcC1 fcc1
  exact rep_wordA_evalSigned rep_fcGen2 rep_fcGen2i fcWord1 fc_basic.2.2.2.1

theorem rep_fcC2 : Rep 3510 fcC2 fcc2 := by
  unfold fcC2 fcc2
  exact rep_wordA_evalSigned rep_fcGen2 rep_fcGen2i fcWord2 fc_basic.2.2.2.2.1

theorem rep_fcC1i : Rep 3510 (invCand 3510 fcC1) fcc1⁻¹ :=
  rep_inv_of_isInvA rep_fcC1 fc_basic.2.2.2.2.2.2.2.2.1

theorem rep_fcC2i : Rep 3510 (invCand 3510 fcC2) fcc2⁻¹ :=
  rep_inv_of_isInvA rep_fcC2 fc_basic.2.2.2.2.2.2.2.2.2.1

theorem rep_fcGenC : ∀ h < 2, Rep 3510 fcGenC[h]! ([fcc1, fcc2].getD h 1) :=
  rep_getD_two rep_fcC1 rep_fcC2

theorem rep_fcGenCi : ∀ h < 2, Rep 3510 fcGenCi[h]! ([fcc1, fcc2].getD h 1)⁻¹ :=
  rep_getD_two_inv rep_fcC1i rep_fcC2i

theorem rep_fcT2 : Rep 3510 fcT2 (fi22ExtRep 2) := (rep_permOfArr fc_basic.2.2.1).1

theorem fcc1_comm : fcc1 * fi22ExtRep 2 = fi22ExtRep 2 * fcc1 :=
  eq_of_eqA (rep_compA rep_fcC1 rep_fcT2) (rep_compA rep_fcT2 rep_fcC1)
    fc_basic.2.2.2.2.2.2.2.2.2.2.1

theorem fcc2_comm : fcc2 * fi22ExtRep 2 = fi22ExtRep 2 * fcc2 :=
  eq_of_eqA (rep_compA rep_fcC2 rep_fcT2) (rep_compA rep_fcT2 rep_fcC2)
    fc_basic.2.2.2.2.2.2.2.2.2.2.2.1

end Reps

section Central

theorem fix_mem_cand {ws : List (List Int)} {cand : List Nat} {r : Nat} (hr : r < 3510)
    (hws : ∀ w ∈ ws, lettersOK 2 w = true)
    (hfix : (fcTabs ws).all (fun t => t[r]! == r) = true)
    (hcov : fcFixCover (fcTabs ws) cand = true) {x : Equiv.Perm (Fin 3510)}
    (hx₁ : x * fcc1 = fcc1 * x) (hx₂ : x * fcc2 = fcc2 * x) :
    ((x ⟨r, hr⟩ : Fin 3510) : Nat) ∈ cand := by
  have hS : ∀ w ∈ ws, Rep 3510 (wordA 3510 fcGenC fcGenCi w) (evalSigned [fcc1, fcc2] w) :=
    fun w hw => rep_wordA_evalSigned rep_fcGenC rep_fcGenCi w (hws w hw)
  have hcent : ∀ g ∈ [fcc1, fcc2],
      g ∈ Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin 3510))) := by
    intro g hg
    rw [Subgroup.mem_centralizer_singleton_iff]
    rcases List.mem_pair.1 hg with rfl | rfl
    · exact hx₁.symm
    · exact hx₂.symm
  have hcomm : ∀ w ∈ ws, evalSigned [fcc1, fcc2] w * x = x * evalSigned [fcc1, fcc2] w := fun w _ =>
    Subgroup.mem_centralizer_singleton_iff.1 (evalSigned_mem hcent w)
  have hfixw : ∀ w ∈ ws, evalSigned [fcc1, fcc2] w ⟨r, hr⟩ = ⟨r, hr⟩ := by
    intro w hw
    have h1 : (wordA 3510 fcGenC fcGenCi w)[r]! = r := by
      have := (List.all_eq_true.1 hfix) (wordA 3510 fcGenC fcGenCi w)
        (by unfold fcTabs; exact List.mem_map.2 ⟨w, hw, rfl⟩)
      simpa using this
    have h2 := hS w hw ⟨r, hr⟩
    rw [h1] at h2
    exact Fin.ext h2.symm
  have hqfix : ∀ w ∈ ws, (wordA 3510 fcGenC fcGenCi w)[((x ⟨r, hr⟩ : Fin 3510) : Nat)]! =
      ((x ⟨r, hr⟩ : Fin 3510) : Nat) := by
    intro w hw
    rw [hS w hw (x ⟨r, hr⟩)]
    have h1 : evalSigned [fcc1, fcc2] w (x ⟨r, hr⟩) = x (evalSigned [fcc1, fcc2] w ⟨r, hr⟩) :=
      congrArg (fun g : Equiv.Perm (Fin 3510) => g ⟨r, hr⟩) (hcomm w hw)
    rw [h1, hfixw w hw]
  have hall : (fcTabs ws).all (fun t => t[((x ⟨r, hr⟩ : Fin 3510) : Nat)]! ==
      ((x ⟨r, hr⟩ : Fin 3510) : Nat)) = true := by
    refine List.all_eq_true.2 fun t ht => ?_
    unfold fcTabs at ht
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 ht
    exact beq_iff_eq.2 (hqfix w hw)
  unfold fcFixCover at hcov
  have h := allLt_spec hcov (x ⟨r, hr⟩).2
  rw [hall] at h
  simpa using h

def fcParF (p : Fin 3510) : Fin 3510 :=
  if h : fcPar[p.val]! < 3510 then ⟨fcPar[p.val]!, h⟩ else p

theorem fc_htree :
    ∀ p : Fin 3510, ((p : Nat) = fcR1 ∨ (p : Nat) = fcR2 ∨ (p : Nat) = fcR3) ∨
      (fcDep[p.val]! = fcDep[(fcParF p).val]! + 1 ∧
        ((fcLab[p.val]! = 1 ∧ fcc1 (fcParF p) = p) ∨
          (fcLab[p.val]! = 2 ∧ fcc2 (fcParF p) = p))) := by
  intro p
  rcases fc_tree p.val p.2 with ⟨-, -, hr⟩ | ⟨hlt, hd, hc⟩
  · exact Or.inl hr
  · right
    have hpar : (fcParF p).val = fcPar[p.val]! := by
      simp only [fcParF, hlt, dite_true]
    refine ⟨by rw [hpar]; exact hd, ?_⟩
    rcases hc with ⟨hl, hq⟩ | ⟨hl, hq⟩
    · refine Or.inl ⟨hl, Fin.ext ?_⟩
      have := rep_fcC1 (fcParF p)
      rw [hpar] at this
      rw [← this]
      exact hq
    · refine Or.inr ⟨hl, Fin.ext ?_⟩
      have := rep_fcC2 (fcParF p)
      rw [hpar] at this
      rw [← this]
      exact hq

theorem fc_central (x : Equiv.Perm (Fin 3510)) (hx₁ : x * fcc1 = fcc1 * x)
    (hx₂ : x * fcc2 = fcc2 * x) : x = 1 ∨ x = fi22ExtRep 2 := by
  obtain ⟨-, -, -, -, -, hw1, hw2, hw3, -, -, -, -, hr1, hr2, hr3, hr12, hr13, ht1, ht2, ht3, -,
    hne⟩ := fc_basic
  obtain ⟨hf1, hc1, hf2, hc2, hf3, hc3⟩ := fc_cons
  have x1 := fix_mem_cand hr1 hw1 hf1 hc1 hx₁ hx₂
  have x2 := fix_mem_cand hr2 hw2 hf2 hc2 hx₁ hx₂
  have x3 := fix_mem_cand hr3 hw3 hf3 hc3 hx₁ hx₂
  have hx1 : x ⟨fcR1, hr1⟩ = ⟨fcR1, hr1⟩ := Fin.ext (by simpa using x1)
  have hx2 : x ⟨fcR2, hr2⟩ = ⟨fcR2, hr2⟩ := by
    have h2 : ((x ⟨fcR2, hr2⟩ : Fin 3510) : Nat) = fcR1 ∨
        ((x ⟨fcR2, hr2⟩ : Fin 3510) : Nat) = fcR2 := by simpa using x2
    rcases h2 with h | h
    · exfalso
      have h1 : x ⟨fcR2, hr2⟩ = x ⟨fcR1, hr1⟩ := by rw [hx1]; exact Fin.ext h
      exact hr12 (congrArg Fin.val (x.injective h1)).symm
    · exact Fin.ext h
  have hx3 : ((x ⟨fcR3, hr3⟩ : Fin 3510) : Nat) = fcR3 ∨
      ((x ⟨fcR3, hr3⟩ : Fin 3510) : Nat) = fcT2R3 := by
    have h3 : ((x ⟨fcR3, hr3⟩ : Fin 3510) : Nat) = fcR1 ∨
        ((x ⟨fcR3, hr3⟩ : Fin 3510) : Nat) = fcR3 ∨
        ((x ⟨fcR3, hr3⟩ : Fin 3510) : Nat) = fcT2R3 := by simpa using x3
    rcases h3 with h | h | h
    · exfalso
      have h1 : x ⟨fcR3, hr3⟩ = x ⟨fcR1, hr1⟩ := by rw [hx1]; exact Fin.ext h
      exact hr13 (congrArg Fin.val (x.injective h1)).symm
    · exact Or.inl h
    · exact Or.inr h
  have hT1 : fi22ExtRep 2 ⟨fcR1, hr1⟩ = ⟨fcR1, hr1⟩ :=
    Fin.ext ((rep_fcT2 ⟨fcR1, hr1⟩).symm.trans ht1)
  have hT2 : fi22ExtRep 2 ⟨fcR2, hr2⟩ = ⟨fcR2, hr2⟩ :=
    Fin.ext ((rep_fcT2 ⟨fcR2, hr2⟩).symm.trans ht2)
  have hT3 : ((fi22ExtRep 2 ⟨fcR3, hr3⟩ : Fin 3510) : Nat) = fcT2R3 :=
    (rep_fcT2 ⟨fcR3, hr3⟩).symm.trans ht3
  have hroot : ∀ p : Fin 3510, ((p : Nat) = fcR1 ∨ (p : Nat) = fcR2 ∨ (p : Nat) = fcR3) →
      p = ⟨fcR1, hr1⟩ ∨ p = ⟨fcR2, hr2⟩ ∨ p = ⟨fcR3, hr3⟩ := by
    rintro p (h | h | h)
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Or.inl (Fin.ext h))
    · exact Or.inr (Or.inr (Fin.ext h))
  rcases hx3 with h | h
  · left
    refine eq_of_forest
      (isRoot := fun p => (p : Nat) = fcR1 ∨ (p : Nat) = fcR2 ∨ (p : Nat) = fcR3)
      (par := fcParF) (dep := fun p => fcDep[p.val]!) (lab := fun p => fcLab[p.val]!) fc_htree
      hx₁ hx₂ (by rw [one_mul, mul_one]) (by rw [one_mul, mul_one]) ?_
    intro p hp
    rcases hroot p hp with rfl | rfl | rfl
    · rw [hx1]; rfl
    · rw [hx2]; rfl
    · rw [Equiv.Perm.one_apply]; exact Fin.ext h
  · right
    refine eq_of_forest
      (isRoot := fun p => (p : Nat) = fcR1 ∨ (p : Nat) = fcR2 ∨ (p : Nat) = fcR3)
      (par := fcParF) (dep := fun p => fcDep[p.val]!) (lab := fun p => fcLab[p.val]!) fc_htree
      hx₁ hx₂ fcc1_comm.symm fcc2_comm.symm ?_
    intro p hp
    rcases hroot p hp with rfl | rfl | rfl
    · rw [hx1, hT1]
    · rw [hx2, hT2]
    · exact Fin.ext (h.trans hT3.symm)

end Central

theorem tmFi22_facts :
    ∃ c₁ c₂ : Equiv.Perm (Fin 3510), c₁ ∈ fi22P ∧ c₂ ∈ fi22P ∧
      c₁ * fi22ExtRep 2 = fi22ExtRep 2 * c₁ ∧ c₂ * fi22ExtRep 2 = fi22ExtRep 2 * c₂ ∧
      ∀ x : Equiv.Perm (Fin 3510), x * c₁ = c₁ * x → x * c₂ = c₂ * x →
        x = 1 ∨ x = fi22ExtRep 2 :=
  ⟨fcc1, fcc2, fcc1_mem, fcc2_mem, fcc1_comm, fcc2_comm, fc_central⟩

end CFSG.EvenSporadicStandard.Induction.TMemFi22Cert
