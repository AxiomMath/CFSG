module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Pf5CovChk
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Pf5Words
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Sp6CoverCheck
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711PfCover

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.CovK

open CFSG.Certificates.Native CFSG.Monster.B.Co2.Native CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.SmallOddCore
  CFSG.ComponentClassification.J2Cover
open CFSG.CosetTable PkG CFSG.EvenSmallLie.SympSix CFSG.LieType.Multipliers CFSG.RankThree.PerfectCover
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Sp6Cover
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Sp6CoverData
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Co3 CFSG.EvenSmallLie.Sp6

set_option linter.unusedSectionVars false

@[expose] noncomputable def GBase (l : ℕ) : Equiv.Perm (Fin 240) :=
  if l < 3 then dP l else if l < 6 then (dP (l - 3))⁻¹ else 1

section Cert


@[expose] def arrChk (L : ℕ) (a : Array ℕ) : Bool :=
  (List.range 240).all fun i => dg 256 L i == a[i]!

@[expose] def invLitChk (p q : ℕ) : Bool :=
  (List.range 240).all fun i => decide (dg 256 q i < 240) && dg 256 p (dg 256 q i) == i

theorem baseGl_lt : ∀ k < 6, baseGl.getD k (one 256 240) < 256 ^ 240 := by decide +kernel

theorem baseD0 : arrChk (baseGl.getD 0 (one 256 240)) yS[0]! = true := by decide +kernel
theorem baseD1 : arrChk (baseGl.getD 1 (one 256 240)) yS[1]! = true := by decide +kernel
theorem baseD2 : arrChk (baseGl.getD 2 (one 256 240)) yS[2]! = true := by decide +kernel
theorem baseI0 : invLitChk (baseGl.getD 0 (one 256 240)) (baseGl.getD 3 (one 256 240)) = true := by
  decide +kernel
theorem baseI1 : invLitChk (baseGl.getD 1 (one 256 240)) (baseGl.getD 4 (one 256 240)) = true := by
  decide +kernel
theorem baseI2 : invLitChk (baseGl.getD 2 (one 256 240)) (baseGl.getD 5 (one 256 240)) = true := by
  decide +kernel

theorem rep_of_arrChk {a : Array ℕ} {L : ℕ} {g : Equiv.Perm (Fin 240)} (hL : L < 256 ^ 240)
    (h : arrChk L a = true) (hg : CFSG.Monster.B.Co2.Rep 240 a g) : Rep 256 240 L g := by
  refine ⟨hL, fun i => ?_⟩
  have := (List.all_eq_true.1 h) i (List.mem_range.2 i.2)
  rw [beq_iff_eq] at this
  rw [this]
  exact hg i

theorem rep_inv_of_chk {p q : ℕ} {g : Equiv.Perm (Fin 240)} (hq : q < 256 ^ 240)
    (hp : Rep 256 240 p g) (h : invLitChk p q = true) : Rep 256 240 q g⁻¹ := by
  refine Rep.inv_of_lit hq hp (fun i hi => ?_) (fun i hi => ?_)
  · have := (List.all_eq_true.1 h) i (List.mem_range.2 hi)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.1
  · have := (List.all_eq_true.1 h) i (List.mem_range.2 hi)
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    exact this.2

theorem rep_d {k : ℕ} (hk : k < 3) {L : ℕ} (hL : L < 256 ^ 240) (h : arrChk L yS[k]! = true) :
    Rep 256 240 L (dP k) :=
  rep_of_arrChk hL h (d_rep hk).1

theorem rep_dinv {k : ℕ} (hk : k < 3) {p q : ℕ} (hp : p < 256 ^ 240) (hq : q < 256 ^ 240)
    (h : arrChk p yS[k]! = true) (hi : invLitChk p q = true) : Rep 256 240 q (dP k)⁻¹ :=
  rep_inv_of_chk hq (rep_d hk hp h) hi

theorem prep_base (l : ℕ) : Rep 256 240 (baseGl.getD l (one 256 240)) (GBase l) := by
  by_cases h1 : l < 3
  · have e : GBase l = dP l := by simp [GBase, h1]
    rw [e]
    have h : arrChk (baseGl.getD l (one 256 240)) yS[l]! = true := by
      have : l = 0 ∨ l = 1 ∨ l = 2 := by omega
      rcases this with rfl | rfl | rfl
      exacts [baseD0, baseD1, baseD2]
    exact rep_d h1 (baseGl_lt l (by omega)) h
  · by_cases h2 : l < 6
    · have e : GBase l = (dP (l - 3))⁻¹ := by simp [GBase, h1, h2]
      rw [e]
      have hp : arrChk (baseGl.getD (l - 3) (one 256 240)) yS[l - 3]! = true := by
        have : l - 3 = 0 ∨ l - 3 = 1 ∨ l - 3 = 2 := by omega
        rcases this with h | h | h <;> rw [h]
        exacts [baseD0, baseD1, baseD2]
      have hi : invLitChk (baseGl.getD (l - 3) (one 256 240)) (baseGl.getD l (one 256 240)) = true := by
        have : l = 3 ∨ l = 4 ∨ l = 5 := by omega
        rcases this with rfl | rfl | rfl
        exacts [baseI0, baseI1, baseI2]
      exact rep_dinv (k := l - 3) (by omega) (baseGl_lt (l - 3) (by omega)) (baseGl_lt l h2) hp hi
    · have e : GBase l = 1 := by simp [GBase, h1, h2]
      rw [e]
      have : baseGl.getD l (one 256 240) = one 256 240 :=
        getD_default' _ _ _ (by simp [baseGl]; omega)
      rw [this]
      exact Rep.one (by norm_num) (by norm_num)

end Cert

section Cert2


@[expose] noncomputable def LGl : ℕ → Equiv.Perm (Fin 240) := LG letterWords GBase

theorem prepL (l : ℕ) : Rep 256 240 (GLt.getD l (one 256 240)) (LGl l) := by
  have := prep_LG (by norm_num : 0 < 256) (by norm_num : 240 ≤ 256) prep_base letterWords l
  rwa [GLt_eq] at this

theorem prepW (w : List ℕ) : Rep 256 240 (evalW 256 240 GLt w) (permW LGl w) := by
  have := prep_permW (by norm_num : 0 < 256) (by norm_num : 240 ≤ 256) prep_base letterWords w
  rwa [GLt_eq] at this

theorem invL_fix : ∀ l, 13 ≤ l → invL l = l := fun l hl => by
  unfold invL
  exact getD_default' _ _ _ (by simpa using hl)

theorem hIL : ∀ l, LGl (invL l) = (LGl l)⁻¹ := by
  refine LG_inv (by norm_num : 0 < 256) (by norm_num : 240 ≤ 256) prep_base letterWords
    (invL := invL) 13 (by decide) invL_fix ?_
  intro l hl
  have h := List.all_eq_true.1 invChk_true l (List.mem_range.2 hl)
  rw [beq_iff_eq] at h
  rw [GLt_eq]
  exact h

theorem GBase_mem (l : ℕ) : GBase l ∈ ySub := by
  unfold GBase
  split_ifs with h1 h2
  · exact dP_mem h1
  · exact ySub.inv_mem (dP_mem (by omega))
  · exact ySub.one_mem

theorem LGl_mem (l : ℕ) : LGl l ∈ ySub := permW_mem GBase GBase_mem _

@[expose] noncomputable def hY (w : List ℕ) : ↥ySub := ⟨permW LGl w, permW_mem LGl LGl_mem w⟩

theorem hY_val (w : List ℕ) : (hY w : Equiv.Perm (Fin 240)) = permW LGl w := rfl

theorem hY_cons (l : ℕ) (w : List ℕ) : hY (l :: w) = hY [l] * hY w :=
  Subtype.ext (by
    show permW LGl (l :: w) = permW LGl [l] * permW LGl w
    rw [permW_cons, permW_single])

theorem hY_mem_of_letters {K : Subgroup ↥ySub} {w : List ℕ} (h : ∀ l ∈ w, hY [l] ∈ K) :
    hY w ∈ K := by
  induction w with
  | nil => exact K.one_mem
  | cons l w ih =>
    rw [hY_cons]
    exact K.mul_mem (h l (List.mem_cons_self ..))
      (ih fun l' hl' => h l' (List.mem_cons_of_mem _ hl'))

theorem hY_inv_letter (l : ℕ) : hY [invL l] = (hY [l])⁻¹ :=
  Subtype.ext (by
    show permW LGl [invL l] = (permW LGl [l])⁻¹
    rw [permW_single, permW_single, hIL])

end Cert2

section Cert3


@[expose] noncomputable def e3 (i : Fin 3) : ↥ySub := hY [6 + i.val]

theorem invL_six (i : Fin 3) : invL (6 + i.val) = 9 + i.val := by fin_cases i <;> rfl

theorem e3_inv (i : Fin 3) : (e3 i)⁻¹ = hY [9 + i.val] := by
  have h := hY_inv_letter (6 + i.val)
  rw [invL_six] at h
  exact h.symm

theorem coe_lift_e3 (w : List (Fin 3 × Bool)) :
    ((FreeGroup.lift e3 (FreeGroup.mk w) : ↥ySub) : Equiv.Perm (Fin 240)) =
      permW LGl (toLetters w) := by
  rw [FreeGroup.lift_mk]
  have h := map_list_prod ySub.subtype (w.map fun x => cond x.2 (e3 x.1) (e3 x.1)⁻¹)
  have h1 : ((((w.map fun x => cond x.2 (e3 x.1) (e3 x.1)⁻¹).prod : ↥ySub)) :
      Equiv.Perm (Fin 240)) = ((w.map fun x => cond x.2 (e3 x.1) (e3 x.1)⁻¹).map
        ySub.subtype).prod := h
  rw [h1, List.map_map]
  unfold permW toLetters
  rw [List.map_map]
  congr 1
  refine List.map_congr_left fun x _ => ?_
  rcases x with ⟨i, b⟩
  have e2 : ((e3 i : ↥ySub) : Equiv.Perm (Fin 240)) = LGl (6 + i.val) := by
    show permW LGl [6 + i.val] = _
    rw [permW_single]
  have e1 : ((e3 i : ↥ySub) : Equiv.Perm (Fin 240))⁻¹ = LGl (9 + i.val) := by
    rw [e2, ← invL_six i, hIL]
  cases b
  · simp [e1]
  · simp [e2]

theorem z_comm_d {k : ℕ} (hk : k < 3) : LGl 12 * LGl k = LGl k * LGl 12 := by
  have h := zChk_true
  unfold zChk at h
  simp only [Bool.and_eq_true] at h
  have h2 := List.all_eq_true.1 h.2 k (List.mem_range.2 hk)
  rw [beq_iff_eq] at h2
  have h3 : comp 256 240 (GLt.getD 12 (one 256 240)) (GLt.getD k (one 256 240)) =
      comp 256 240 (GLt.getD k (one 256 240)) (GLt.getD 12 (one 256 240)) := h2
  have a := (prepL 12).comp (by norm_num : 0 < 256) (prepL k)
  have b := (prepL k).comp (by norm_num : 0 < 256) (prepL 12)
  rw [h3] at a
  exact Rep.unique a b

theorem z_central (y : ↥ySub) : hY [12] * y = y * hY [12] := by
  have hK : Subgroup.centralizer ({hY [12]} : Set ↥ySub) = ⊤ := by
    apply eq_top_of_dY
    intro k hk
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    have hd : LGl k = dP k := by
      show permW GBase (letterWords.getD k []) = _
      have : k = 0 ∨ k = 1 ∨ k = 2 := by omega
      rcases this with rfl | rfl | rfl
      · show permW GBase [0] = _
        rw [permW_single]; simp [GBase]
      · show permW GBase [1] = _
        rw [permW_single]; simp [GBase]
      · show permW GBase [2] = _
        rw [permW_single]; simp [GBase]
    show (dP k) * permW LGl [12] = permW LGl [12] * dP k
    rw [permW_single, ← hd]
    exact (z_comm_d hk).symm
  have : y ∈ Subgroup.centralizer ({hY [12]} : Set ↥ySub) := by rw [hK]; exact Subgroup.mem_top y
  exact (Subgroup.mem_centralizer_singleton_iff.1 this).symm

theorem rels_val : ∀ r ∈ rels, permW LGl (toLetters r) = 1 ∨ permW LGl (toLetters r) = LGl 12 := by
  intro r hr
  have h := List.all_eq_true.1 relChk_true r hr
  simp only [Bool.or_eq_true, beq_iff_eq] at h
  rcases h with h | h
  · left
    have h1 := prepW (toLetters r)
    rw [h] at h1
    exact Rep.unique h1 (Rep.one (by norm_num) (by norm_num))
  · right
    have h1 := prepW (toLetters r)
    rw [h] at h1
    exact Rep.unique h1 (prepL 12)

theorem lift_rel_val (w : List (Fin 3 × Bool)) (hw : w ∈ rels) :
    FreeGroup.lift e3 (FreeGroup.mk w) = 1 ∨ FreeGroup.lift e3 (FreeGroup.mk w) = hY [12] := by
  rcases rels_val w hw with h | h
  · left
    apply Subtype.ext
    rw [coe_lift_e3, h]
    rfl
  · right
    apply Subtype.ext
    rw [coe_lift_e3, h]
    show _ = permW LGl [12]
    rw [permW_single]

theorem relators_hold : ∀ r ∈ coverRelators (wordSet rels)
    (fun i : Fin 3 => FreeGroup.mk (commWords (coverPairs i))), FreeGroup.lift e3 r = 1 := by
  rw [lift_coverRelators_eq_one_iff]
  refine ⟨?_, ?_⟩
  · intro i r hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
    rcases lift_rel_val w hw with h | h
    · rw [h]; simp
    · rw [h, commutatorElement_eq_one_iff_mul_comm]
      exact (z_central _).symm
  · intro i
    apply Subtype.ext
    rw [coe_lift_e3]
    have h := List.all_eq_true.1 fixChk_true i (List.mem_finRange i)
    rw [beq_iff_eq] at h
    have h1 := prepW (toLetters (commWords (coverPairs i)))
    rw [h] at h1
    have h2 := Rep.unique h1 (prepL (6 + i.val))
    rw [h2]
    show _ = permW LGl [6 + i.val]
    rw [permW_single]

@[expose] noncomputable def psi : PresentedCover (wordSet rels)
    (fun i : Fin 3 => FreeGroup.mk (commWords (coverPairs i))) →* ↥ySub :=
  PresentedGroup.toGroup (f := e3) relators_hold

theorem psi_of (i : Fin 3) : psi (PresentedGroup.of i) = e3 i := PresentedGroup.toGroup.of _

theorem dLetters : ((List.range 3).all fun k => (dWords.getD k []).all fun l =>
    decide (6 ≤ l ∧ l ≤ 11)) = true := by decide +kernel

theorem dY_eq_hY {k : ℕ} (hk : k < 3) : dY k hk = hY (dWords.getD k []) := by
  have h := List.all_eq_true.1 dChk_true k (List.mem_range.2 hk)
  rw [beq_iff_eq] at h
  have h1 := prepW (dWords.getD k [])
  rw [h] at h1
  have h2 := Rep.unique h1 (prep_base k)
  apply Subtype.ext
  rw [hY_val, h2]
  have hk' : GBase k = dP k := by simp [GBase, hk]
  rw [hk']

theorem psi_surj : Function.Surjective psi := by
  rw [← MonoidHom.range_eq_top]
  apply eq_top_of_dY
  intro k hk
  rw [dY_eq_hY hk]
  apply hY_mem_of_letters
  intro l hl
  have hlet : 6 ≤ l ∧ l ≤ 11 := by
    have := List.all_eq_true.1 (List.all_eq_true.1 dLetters k (List.mem_range.2 hk)) l hl
    simpa using this
  by_cases h6 : l < 9
  · have : hY [l] = e3 ⟨l - 6, by omega⟩ := by
      simp only [e3]
      congr 2
      omega
    rw [this, ← psi_of]
    exact MonoidHom.mem_range.2 ⟨_, rfl⟩
  · have hinv : hY [l] = (e3 ⟨l - 9, by omega⟩)⁻¹ := by
      rw [e3_inv]
      congr 2
      simp
      omega
    rw [hinv, ← psi_of]
    exact Subgroup.inv_mem _ (MonoidHom.mem_range.2 ⟨_, rfl⟩)

theorem card_P : Finite (PresentedCover (wordSet rels)
      (fun i : Fin 3 => FreeGroup.mk (commWords (coverPairs i)))) ∧
    Nat.card (PresentedCover (wordSet rels)
      (fun i : Fin 3 => FreeGroup.mk (commWords (coverPairs i)))) ≤ 2 * 1451520 := by
  obtain ⟨hfin, hle⟩ := card_cover_le
  have hS : coverRelators (wordSet rels)
      (fun i : Fin 3 => FreeGroup.mk (commWords (coverPairs i))) = wordSet coverWs :=
    coverRelators_wordSet rels _
  refine ⟨?_, ?_⟩
  · show Finite (PresentedGroup _)
    rw [hS]
    exact hfin
  · show Nat.card (PresentedGroup _) ≤ _
    rw [hS]
    exact hle

theorem psi_bij : Function.Bijective psi := by
  haveI := card_P.1
  exact psi_surj.bijective_of_nat_card_le (by rw [card_ySub]; exact card_P.2)

theorem hPres : IsPresentation sympGenX (wordSet rels) := isPresentation_co3X36

theorem hwComm (i : Fin 3) :
    FreeGroup.mk (commWords (coverPairs i)) ∈ commutator (FreeGroup (Fin 3)) :=
  mk_commWords_mem_commutator _

theorem hwgComm (i : Fin 3) :
    FreeGroup.lift sympGenX (FreeGroup.mk (commWords (coverPairs i))) = sympGenX i :=
  lift_commWords i

noncomputable def hopfEquiv : PresentedCover (wordSet rels)
    (fun i : Fin 3 => FreeGroup.mk (commWords (coverPairs i))) ≃* ModSp1 :=
  presentedCoverEquiv hPres hwComm hwgComm

noncomputable def psiEquiv : PresentedCover (wordSet rels)
    (fun i : Fin 3 => FreeGroup.mk (commWords (coverPairs i))) ≃* ↥ySub :=
  MulEquiv.ofBijective psi psi_bij

noncomputable def modSp1Equiv : ModSp1 ≃* ↥ySub := hopfEquiv.symm.trans psiEquiv

noncomputable def qYc : ↥ySub →* ModSp0 :=
  (coverMap hPres hwgComm).comp psiEquiv.symm.toMonoidHom

theorem qYc_surjective : Function.Surjective qYc := fun x => by
  obtain ⟨p, hp⟩ := coverMap_surjective hPres hwgComm x
  refine ⟨psi p, ?_⟩
  have h : psiEquiv.symm (psi p) = p := psiEquiv.symm_apply_apply p
  simp only [qYc, MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe]
  rw [h]
  exact hp

theorem qYc_e3 (i : Fin 3) : qYc (e3 i) = sympGenX i := by
  have h : psiEquiv.symm (e3 i) = PresentedGroup.of i := by
    apply psiEquiv.injective
    rw [MulEquiv.apply_symm_apply]
    exact (psi_of i).symm
  simp only [qYc, MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, h,
    coverMap_of]

theorem qYc_ker_central : qYc.ker ≤ Subgroup.center ↥ySub := by
  intro x hx
  have hx' : psiEquiv.symm x ∈ (coverMap hPres hwgComm).ker := by
    exact MonoidHom.mem_ker.2 (MonoidHom.mem_ker.1 hx)
  have hc := coverMap_ker_le_center hPres hwgComm hx'
  rw [Subgroup.mem_center_iff] at hc ⊢
  intro g
  have := hc (psiEquiv.symm g)
  have h2 := congrArg psiEquiv this
  simpa using h2

theorem Y_perfect : Group.IsPerfect ↥ySub := by
  haveI := presentedCover_isPerfect (R := wordSet rels) hwComm
  rw [Group.isPerfect_def, eq_top_iff]
  intro y _
  obtain ⟨x, rfl⟩ := psi_surj y
  have h : psi x ∈ (commutator (PresentedCover (wordSet rels)
      (fun i : Fin 3 => FreeGroup.mk (commWords (coverPairs i))))).map psi :=
    ⟨x, by rw [Group.IsPerfect.commutator_eq_top]; trivial, rfl⟩
  rw [commutator_def, Subgroup.map_commutator] at h
  exact Subgroup.commutator_mono le_top le_top h

end Cert3

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.CovK
