module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Ext.Arr
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Ext.CertCheck
public import Certificates.Certificate450210

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP

open CFSG.Monster.Code CFSG.Quasithin.H.Mathieu CFSG.Sporadic.Bridge
  CFSG.Sporadic.Bridge.TwoGen Certificates.RouteP.M24Defect

theorem W11_mul_self (w : W11) : w * w = 1 := by
  apply Multiplicative.toAdd.injective
  funext i
  simp [CharTwo.add_self_eq_zero]

noncomputable def maskOf (w : W11) : ℕ := (toW_surj 11 w).choose

theorem maskOf_lt (w : W11) : maskOf w < 2 ^ 11 := (toW_surj 11 w).choose_spec.1

theorem toW_maskOf (w : W11) : toW 11 (maskOf w) = w := (toW_surj 11 w).choose_spec.2

theorem toW_xorMasks (n : ℕ) : ∀ l : List ℕ, toW n (xorMasks l) = (l.map (toW n)).prod
  | [] => by simp [xorMasks, toW_zero]
  | m :: l => by
    simp only [xorMasks, toW_xor, toW_xorMasks n l, List.map_cons, List.prod_cons]

theorem toW_actM_matA {h : ↥AutPerm} {a : Array ℕ} (ha : HasArr (h : Equiv.Perm (Fin 24)) a)
    (x : ℕ) : toW 11 (actM (matA a) x) = rho11 AutPerm le_rfl h (toW 11 x) := by
  have hlen : (matA a).length = 11 := length_matOf 11 _
  have h1 : actM (matA a) x = actM (matA a) (x % 2 ^ 11) := by
    have := actM_mod (matA a) x
    rw [hlen] at this
    exact this.symm
  rw [h1, matA, actM_matOf (xorLin_act11 a) 11 _ (Nat.mod_lt _ (by norm_num)),
    ← rho11_toW AutPerm le_rfl h ha, toW_mod]

theorem bp_dualAct_matA (a : Array ℕ) (m w : ℕ) :
    bp (dualAct (matA a) m) w = bp m (actM (matA a) w) :=
  bp_dualAct (length_matOf 11 _) m w

theorem actM_matA_eq (a : Array ℕ) {w : ℕ} (hw : w < 2 ^ 11) :
    actM (matA a) w = act11 a w :=
  actM_matOf (xorLin_act11 a) 11 w hw

theorem forall₂_map_eq {α β γ : Type*} {R : α → β → Prop} {f : β → γ} {g : α → γ}
    (h : ∀ a b, R a b → f b = g a) {l : List α} {l' : List β} (hl : List.Forall₂ R l l') :
    l'.map f = l.map g := by
  induction hl with
  | nil => rfl
  | cons hab _ ih => simp only [List.map_cons, h _ _ hab, ih]

theorem relWords_length : relWords.length = 7 := rfl

theorem getElem_relWords_mem {i : ℕ} (hi : i < 7) : relWords[i]! ∈ relWords := by
  rw [getElem!_pos relWords i (by rw [relWords_length]; exact hi)]
  exact List.getElem_mem _

theorem exists_relWords_getElem {r : List (ℕ × Bool)} (hr : r ∈ relWords) :
    ∃ i < 7, r = relWords[i]! := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hr
  rw [relWords_length] at hi
  exact ⟨i, hi, (getElem!_pos relWords i (by rw [relWords_length]; exact hi)).symm⟩

theorem toW_lamApply (z : ℕ × ℕ) {i : ℕ} (hi : i < 7) :
    toW 11 (lamApply z i) =
      ((walkEdges gens (relWords[i]!) 1).map fun e =>
        rho11 AutPerm le_rfl e.1 (if e.2 = 0 then toW 11 z.1 else toW 11 z.2)).prod := by
  have hmem := getElem_relWords_mem hi
  have hF₂ := edgeStates_forall₂ (relWords[i]!) (relWords_letters _ hmem) HA.one 1 HAOK.one
  have key : ∀ (e : HA × ℕ) (e' : ↥AutPerm × ℕ),
      (HAOK e.1 e'.1 ∧ e.2 = e'.2 ∧ e.2 < 2) →
      rho11 AutPerm le_rfl e'.1 (if e'.2 = 0 then toW 11 z.1 else toW 11 z.2) =
        toW 11 (actM (matA e.1.fwd) (if e.2 = 0 then z.1 else z.2)) := by
    rintro e e' ⟨hst, he, -⟩
    rw [toW_actM_matA hst.1, he]
    split_ifs <;> rfl
  unfold lamApply
  rw [toW_xorMasks, List.map_map]
  exact congrArg List.prod (forall₂_map_eq key hF₂).symm

theorem sum_bp_contribs (tab : Array (List (ℕ × Bool))) (ψ : ℕ → ℕ) (hψ : ∀ κ, ψ κ < 2 ^ 11)
    (m : ℕ) : ∀ E : List (HA × ℕ),
    ((E.map fun e => (keyOf e.1 e.2, dualAct (matA (kArr tab e.1)) m)).map
        fun c => bp c.2 (ψ c.1)).sum =
      bp m (xorMasks (E.map fun e => act11 (kArr tab e.1) (ψ (keyOf e.1 e.2))))
  | [] => by simp [xorMasks, bp_zero_right]
  | e :: E => by
    simp only [List.map_cons, List.sum_cons, xorMasks, bp_xor_right]
    rw [bp_dualAct_matA, actM_matA_eq _ (hψ _), sum_bp_contribs tab ψ hψ m E]

section Soundness

variable {N N₀ : Type*} [Group N] [Group N₀]
  {X : ExtData (rho11 AutPerm le_rfl) N} {X₀ : ExtData (rho11 AutPerm le_rfl) N₀}

noncomputable def psiMask (D : DefectData X X₀ K22 gens) (κ : ℕ) : ℕ :=
  maskOf (D.psi (κ / 2) (κ % 2))

noncomputable def defMask (D : DefectData X X₀ K22 gens) (i : ℕ) : ℕ :=
  maskOf (D.defect (relWords[i]!))

variable (D : DefectData X X₀ K22 gens)

theorem edge_toW (hL : treeLetters (treeTab ()) = true) {e : HA × ℕ} {e' : ↥AutPerm × ℕ}
    (hR : HAOK e.1 e'.1 ∧ e.2 = e'.2 ∧ e.2 < 2) :
    rho11 AutPerm le_rfl (kOf qFun trFun e'.1) (D.psi (qFun e'.1) e'.2) =
      toW 11 (act11 (kArr (treeTab ()) e.1) (psiMask D (keyOf e.1 e.2))) := by
  obtain ⟨hst, he, he2⟩ := hR
  have hkey1 : keyOf e.1 e.2 / 2 = qFun e'.1 := by
    rw [keyOf, ptIdx_eq hst]
    omega
  have hkey2 : keyOf e.1 e.2 % 2 = e'.2 := by
    rw [keyOf, ptIdx_eq hst]
    omega
  rw [psiMask, hkey1, hkey2, ← rho11_toW AutPerm le_rfl _ (hasArr_kOf hL hst), toW_maskOf]

theorem walk_toW (hrels : relsOK = true) (hL : treeLetters (treeTab ()) = true)
    (hq : D.q = qFun) (htr : D.tr = trFun) (p : ℕ) {i : ℕ} (hi : i < 7) :
    toW 11 (act11 (wordA (tword (treeTab ()) p)) (defMask D i)) =
      toW 11 (xorMasks ((edgeStates (relWords[i]!) (startHA (treeTab ()) p)).map fun e =>
        act11 (kArr (treeTab ()) e.1) (psiMask D (keyOf e.1 e.2)))) := by
  have hmem := getElem_relWords_mem hi
  have hw1 : wordProd gens (relWords[i]!) = 1 := wordProd_relWords hrels _ hmem
  have hwalk := D.walk_eq W11_mul_self (relWords[i]!) hw1 (trFun p)
  rw [hq, htr] at hwalk
  have hF₂ := edgeStates_forall₂ (relWords[i]!) (relWords_letters _ hmem) (startHA (treeTab ()) p)
    (trFun p) (haOK_startHA hL p)
  have hlhs : rho11 AutPerm le_rfl (trFun p) (D.defect (relWords[i]!)) =
      toW 11 (act11 (wordA (tword (treeTab ()) p)) (defMask D i)) := by
    rw [← rho11_toW AutPerm le_rfl (trFun p)
      (hasArr_wordProd (tword (treeTab ()) p) (treeLetters_spec hL p)), defMask, toW_maskOf]
  have hrhs : ((walkEdges gens (relWords[i]!) (trFun p)).map fun e =>
      rho11 AutPerm le_rfl (kOf qFun trFun e.1) (D.psi (qFun e.1) e.2)).prod =
      toW 11 (xorMasks ((edgeStates (relWords[i]!) (startHA (treeTab ()) p)).map fun e =>
        act11 (kArr (treeTab ()) e.1) (psiMask D (keyOf e.1 e.2)))) := by
    rw [toW_xorMasks, List.map_map]
    exact congrArg List.prod (forall₂_map_eq (fun e e' hR => edge_toW D hL hR) hF₂)
  exact hlhs.symm.trans (hwalk.trans hrhs)

theorem defMask_lt (i : ℕ) : defMask D i < 2 ^ 11 := maskOf_lt _

theorem psiMask_lt (κ : ℕ) : psiMask D κ < 2 ^ 11 := maskOf_lt _

theorem hsys_of_defectData (hrels : relsOK = true) (hL : treeLetters (treeTab ()) = true)
    (hq : D.q = qFun) (htr : D.tr = trFun) (p : ℕ) {i : ℕ} (hi : i < 7) (m : ℕ) :
    bp (fpart (treeTab ()) p m) (defMask D i) =
      ((contribs (treeTab ()) p i m).map fun c => bp c.2 (psiMask D c.1)).sum := by
  have h1 := walk_toW D hrels hL hq htr p hi
  have h1' : bvec 11 (act11 (wordA (tword (treeTab ()) p)) (defMask D i)) =
      bvec 11 (xorMasks ((edgeStates (relWords[i]!) (startHA (treeTab ()) p)).map fun e =>
        act11 (kArr (treeTab ()) e.1) (psiMask D (keyOf e.1 e.2)))) :=
    congrArg Multiplicative.toAdd h1
  have h2 : bp m (act11 (wordA (tword (treeTab ()) p)) (defMask D i)) =
      bp m (xorMasks ((edgeStates (relWords[i]!) (startHA (treeTab ()) p)).map fun e =>
        act11 (kArr (treeTab ()) e.1) (psiMask D (keyOf e.1 e.2)))) := by
    unfold bp
    rw [h1']
  have hl : bp (fpart (treeTab ()) p m) (defMask D i) =
      bp m (act11 (wordA (tword (treeTab ()) p)) (defMask D i)) := by
    rw [fpart, bp_dualAct_matA, actM_matA_eq _ (defMask_lt D i)]
  exact hl.trans (h2.trans (sum_bp_contribs (treeTab ()) (psiMask D) (psiMask_lt D) m _).symm)

theorem exists_changeLifts (hq : D.q = qFun) (htr : D.tr = trFun) :
    ∃ z : ℕ → N, (∀ i, X.π (z i) = 1) ∧
      ∀ r ∈ relWords, X.eT (wordProd (fun i => z i * D.xt i) r) = X₀.eT (wordProd D.xt₀ r) := by
  have hcheck : checkAll () = true := Certificates.certificate450210
  obtain ⟨hrels, -, hL, -⟩ := checkAll_spec hcheck
  obtain ⟨z, hz⟩ := exists_lam_of_checkAll hcheck (defMask D) (psiMask D)
    (fun p i m _ _ _ hi _ => hsys_of_defectData D hrels hL hq htr p hi m)
  let zW : ℕ → W11 := fun j => if j = 0 then toW 11 z.1 else toW 11 z.2
  have hfox : ∀ i < 7, D.defect (relWords[i]!) =
      ((walkEdges gens (relWords[i]!) 1).map fun e => rho11 AutPerm le_rfl e.1 (zW e.2)).prod := by
    intro i hi
    rw [← toW_maskOf (D.defect (relWords[i]!)), ← toW_lamApply z hi]
    exact congrArg Multiplicative.ofAdd (hz i hi)
  choose zN hzπ hzeT using fun j => X.eT_surj (zW j)
  refine ⟨zN, hzπ, fun r hr => ?_⟩
  obtain ⟨i, hi, rfl⟩ := exists_relWords_getElem hr
  have hw1 : wordProd gens (relWords[i]!) = 1 :=
    wordProd_relWords hrels _ (getElem_relWords_mem hi)
  obtain ⟨-, heT⟩ := eT_wordProd_changeLift X W11_mul_self D.xt_π hzπ (relWords[i]!) hw1
  have hd : D.defect (relWords[i]!) =
      X.eT (wordProd D.xt (relWords[i]!)) * X₀.eT (wordProd D.xt₀ (relWords[i]!)) := rfl
  have hcancel : ∀ a b : W11, a * (a * b) = b := fun a b => by
    rw [← mul_assoc, W11_mul_self, one_mul]
  rw [heT]
  simp only [hzeT]
  refine (congrArg (fun t => X.eT (wordProd D.xt (relWords[i]!)) * t) (hfox i hi)).symm.trans ?_
  exact (congrArg (fun t => X.eT (wordProd D.xt (relWords[i]!)) * t) hd).trans (hcancel _ _)

end Soundness

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP
