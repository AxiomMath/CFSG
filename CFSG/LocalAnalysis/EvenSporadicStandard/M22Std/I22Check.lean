module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.Cov8

public section

namespace CFSG.EvenSporadicStandard.M22Std

open CFSG.QuasithinUnique.Ch1.M22Cover CFSG.QuasithinUnique.Ch1.TitsCover
open CFSG.Monster.B CFSG.Monster.B.Co2.Native
open CFSG.Monster.B.Co2 (rep_compA rep_idA eqA_iff eq_of_eqA allLt_iff rep_inv_of_isInvA)

@[expose] def i22hWord : List ℕ := [0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0,
  1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0]

@[expose] def i22aVert : ℕ := 79

@[expose] def i22cj (u g v : Array ℕ) : Array ℕ := compA 22 (compA 22 u g) v

@[expose] def i22inS (T : Array (Array ℕ)) (n : ℕ) (g : Array ℕ) : Bool :=
  !allLt n fun v => !eqA 22 T[v]! g

@[expose] def i22isCore (T : Array (Array ℕ)) (n : ℕ) (h hi g : Array ℕ) : Bool :=
  i22inS T n g && i22inS T n (i22cj hi g h) && i22inS T n (i22cj h g hi)

@[expose] def i22Check (_ : Unit := ()) : Bool :=
  let T := covData.elaTab
  let n := covData.nV
  let h := wordArrP i22hWord
  let hi := invCand 22 h
  let z := compA 22 T[79]! T[79]!
  let a := T[i22aVert]!
  let ai := invCand 22 a
  (n == 128) && isInvA 22 h hi &&
  eqA 22 (compA 22 h z) (compA 22 z h) &&
  eqA 22 (compA 22 (compA 22 h h) h) (idA 22) &&
  !eqA 22 h (idA 22) &&
  aV.all (fun v => eqA 22 (compA 22 T[v]! T[v]!) z) &&
  rootsV.all (fun v => !i22inS T n (i22cj hi T[v]! h) || aV.contains v) &&
  aV.contains i22aVert && i22isCore T n h hi a && isInvA 22 a ai &&
  aV.any (fun w => eqA 22 (i22cj (compA 22 a h) ai hi) T[w]!) &&
  allLt 3 (fun i => isInvA 22 (covData.xa (fo i)) (invCand 22 (covData.xa (fo i)))) &&
  allLt n (fun v => !i22isCore T n h hi T[v]! ||
    allLt 3 fun i => i22isCore T n h hi
      (i22cj (covData.xa (fo i)) T[v]! (invCand 22 (covData.xa (fo i)))))

@[expose] noncomputable def i22el (v : ℕ) : Equiv.Perm (Fin 22) := covData.tab.el covData.x v

@[expose] noncomputable def i22hP : Equiv.Perm (Fin 22) := wordP i22hWord

@[expose] noncomputable def i22zP : Equiv.Perm (Fin 22) := i22el 79 * i22el 79

@[expose] def i22InS (g : Equiv.Perm (Fin 22)) : Prop := ∃ v < covData.nV, i22el v = g

@[expose] noncomputable def i22IsCore (g : Equiv.Perm (Fin 22)) : Prop :=
  i22InS g ∧ i22InS (i22hP⁻¹ * g * i22hP) ∧ i22InS (i22hP * g * i22hP⁻¹)

theorem rep_i22h : Co2.Rep 22 (wordArrP i22hWord) i22hP := rep_wordArrP i22hWord

theorem i22inS_iff {g : Array ℕ} {G : Equiv.Perm (Fin 22)}
    (hx : ∀ i, Co2.Rep 22 (covData.xa i) (covData.x i))
    (hg : Co2.Rep 22 g G) : i22inS covData.elaTab covData.nV g = true ↔ i22InS G := by
  unfold i22inS i22InS
  rw [Bool.not_eq_true', ← Bool.not_eq_true, allLt_iff]
  push Not
  constructor
  · rintro ⟨v, hv, hne⟩
    refine ⟨v, hv, ?_⟩
    have : eqA 22 covData.elaTab[v]! g = true := by simpa using hne
    exact eq_of_eqA (covData.rep_el hx hv) hg this
  · rintro ⟨v, hv, hveq⟩
    refine ⟨v, hv, ?_⟩
    have : eqA 22 covData.elaTab[v]! g = true := (eqA_iff (covData.rep_el hx hv) hg).2 hveq
    simpa using this

theorem i22isCore_iff {g : Array ℕ} {G : Equiv.Perm (Fin 22)}
    (hx : ∀ i, Co2.Rep 22 (covData.xa i) (covData.x i))
    (hhi : Co2.Rep 22 (invCand 22 (wordArrP i22hWord)) i22hP⁻¹) (hg : Co2.Rep 22 g G) :
    i22isCore covData.elaTab covData.nV (wordArrP i22hWord) (invCand 22 (wordArrP i22hWord)) g =
      true ↔ i22IsCore G := by
  have hh : Co2.Rep 22 (wordArrP i22hWord) i22hP := rep_i22h
  have hc1 : Co2.Rep 22 (i22cj (invCand 22 (wordArrP i22hWord)) g (wordArrP i22hWord))
      (i22hP⁻¹ * G * i22hP) := rep_compA (rep_compA hhi hg) hh
  have hc2 : Co2.Rep 22 (i22cj (wordArrP i22hWord) g (invCand 22 (wordArrP i22hWord)))
      (i22hP * G * i22hP⁻¹) := rep_compA (rep_compA hh hg) hhi
  have e1 : i22isCore covData.elaTab covData.nV (wordArrP i22hWord)
      (invCand 22 (wordArrP i22hWord)) g =
      (i22inS covData.elaTab covData.nV g &&
        i22inS covData.elaTab covData.nV (i22cj (invCand 22 (wordArrP i22hWord)) g
          (wordArrP i22hWord)) &&
        i22inS covData.elaTab covData.nV (i22cj (wordArrP i22hWord) g
          (invCand 22 (wordArrP i22hWord)))) := by rw [i22isCore]
  have e2 : i22IsCore G = (i22InS G ∧ i22InS (i22hP⁻¹ * G * i22hP) ∧
      i22InS (i22hP * G * i22hP⁻¹)) := by rw [i22IsCore]
  rw [e1, e2, Bool.and_eq_true, Bool.and_eq_true, i22inS_iff hx hg, i22inS_iff hx hc1,
    i22inS_iff hx hc2]
  exact ⟨fun ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩, fun ⟨a, b, c⟩ => ⟨⟨a, b⟩, c⟩⟩

theorem i22_aV_lt : ∀ v ∈ aV, v < 128 := by decide

theorem i22_rootsV_lt : ∀ v ∈ rootsV, v < 128 := by decide

structure I22Facts : Prop where
  nV : covData.nV = 128
  h_comm : i22hP * i22zP = i22zP * i22hP
  h_cube : i22hP * i22hP * i22hP = 1
  h_ne : i22hP ≠ 1
  aV_root : ∀ v ∈ aV, i22el v * i22el v = i22zP
  uniq : ∀ v ∈ rootsV, i22InS (i22hP⁻¹ * i22el v * i22hP) → v ∈ aV
  a_aV : i22aVert ∈ aV
  a_core : i22IsCore (i22el i22aVert)
  a_comm : ∃ w ∈ aV, i22el i22aVert * i22hP * (i22el i22aVert)⁻¹ * i22hP⁻¹ = i22el w
  core_norm : ∀ v < covData.nV, i22IsCore (i22el v) →
    ∀ i : Fin 3, i22IsCore (covData.x i * i22el v * (covData.x i)⁻¹)

theorem i22Check_sound (hck : i22Check () = true) : I22Facts := by
  have hx : ∀ i, Co2.Rep 22 (covData.xa i) (covData.x i) := fun i => covData.xa_rep i
  unfold i22Check at hck
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.not_eq_true'] at hck
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hnV, hinv⟩, hcomm⟩, hcube⟩, hne⟩, haV⟩, huniq⟩, haaV⟩, hcore⟩, hainv⟩, hacomm⟩,
    hxinv⟩, hnorm⟩ := hck
  have hrep : ∀ v, v < covData.nV → Co2.Rep 22 covData.elaTab[v]! (i22el v) :=
    fun v hv => covData.rep_el hx hv
  have hlt : ∀ v ∈ aV, v < covData.nV := fun v hv => by
    rw [hnV]; exact i22_aV_lt v hv
  have hltr : ∀ v ∈ rootsV, v < covData.nV := fun v hv => by
    rw [hnV]; exact i22_rootsV_lt v hv
  have h79 : 79 < covData.nV := by rw [hnV]; norm_num
  have hh : Co2.Rep 22 (wordArrP i22hWord) i22hP := rep_i22h
  have hhi : Co2.Rep 22 (invCand 22 (wordArrP i22hWord)) i22hP⁻¹ := rep_inv_of_isInvA hh hinv
  have hz : Co2.Rep 22 (compA 22 covData.elaTab[79]! covData.elaTab[79]!) i22zP :=
    rep_compA (hrep 79 h79) (hrep 79 h79)
  have haa : i22aVert ∈ aV := by simpa using haaV
  have hav : i22aVert < covData.nV := hlt _ haa
  refine ⟨hnV, ?_, ?_, ?_, ?_, ?_, haa, ?_, ?_, ?_⟩
  · exact eq_of_eqA (rep_compA hh hz) (rep_compA hz hh) hcomm
  · exact eq_of_eqA (rep_compA (rep_compA hh hh) hh) rep_idA hcube
  · intro h1
    have : eqA 22 (wordArrP i22hWord) (idA 22) = true := (eqA_iff hh rep_idA).2 h1
    rw [this] at hne
    exact absurd hne (by decide)
  · intro v hv
    have := List.all_eq_true.1 haV v hv
    exact eq_of_eqA (rep_compA (hrep v (hlt v hv)) (hrep v (hlt v hv))) hz this
  · intro v hv hin
    have := List.all_eq_true.1 huniq v hv
    have hc : Co2.Rep 22 (i22cj (invCand 22 (wordArrP i22hWord)) covData.elaTab[v]!
        (wordArrP i22hWord)) (i22hP⁻¹ * i22el v * i22hP) :=
      rep_compA (rep_compA hhi (hrep v (hltr v hv))) hh
    have hs := (i22inS_iff hx hc).2 hin
    rw [hs] at this
    simpa using this
  · exact (i22isCore_iff hx hhi (hrep _ hav)).1 hcore
  · have hai : Co2.Rep 22 (invCand 22 covData.elaTab[i22aVert]!) (i22el i22aVert)⁻¹ :=
      rep_inv_of_isInvA (hrep _ hav) hainv
    obtain ⟨w, hw, hwe⟩ := List.any_eq_true.1 hacomm
    refine ⟨w, hw, ?_⟩
    have hc : Co2.Rep 22 (i22cj (compA 22 covData.elaTab[i22aVert]! (wordArrP i22hWord))
        (invCand 22 covData.elaTab[i22aVert]!) (invCand 22 (wordArrP i22hWord)))
        (i22el i22aVert * i22hP * (i22el i22aVert)⁻¹ * i22hP⁻¹) :=
      rep_compA (rep_compA (rep_compA (hrep _ hav) hh) hai) hhi
    exact eq_of_eqA hc (hrep w (hlt w hw)) hwe
  · intro v hv hcv i
    have hxi : ∀ i : Fin 3, Co2.Rep 22 (covData.xa (fo i)) (covData.x i) := fun i => by
      rw [fo_val]; exact hx i
    have hxinv' : ∀ i : Fin 3, Co2.Rep 22 (invCand 22 (covData.xa (fo i))) (covData.x i)⁻¹ :=
      fun i => rep_inv_of_isInvA (hxi i) (allLt_iff.1 hxinv i.1 i.2)
    have h1 := allLt_iff.1 hnorm v hv
    have hcv : i22isCore covData.elaTab covData.nV (wordArrP i22hWord)
        (invCand 22 (wordArrP i22hWord)) covData.elaTab[v]! = true :=
      (i22isCore_iff hx hhi (hrep v hv)).2 hcv
    rw [hcv] at h1
    simp only [Bool.not_true, Bool.false_or] at h1
    have h2 := allLt_iff.1 h1 i.1 i.2
    have hc : Co2.Rep 22 (i22cj (covData.xa (fo i)) covData.elaTab[v]!
        (invCand 22 (covData.xa (fo i)))) (covData.x i * i22el v * (covData.x i)⁻¹) :=
      rep_compA (rep_compA (hxi i) (hrep v hv)) (hxinv' i)
    exact (i22isCore_iff hx hhi hc).1 (by simpa [Fin.eta] using h2)

end CFSG.EvenSporadicStandard.M22Std
