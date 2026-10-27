module

public import Certificates.Data.Kernel.EvenSporU42.Defs
public import CFSG.Certificates.Kernel.SporSch.ChainKOdd
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.U42SmallIndexInputs

public section

namespace CFSG.KC.EvenSporU42

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw.Orb CFSG.KS.SporSch.MOC CFSG.Sporadic.Schreier
open CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.U42SmallIndex

abbrev R (P : Nat) (g : Equiv.Perm (Fin 45)) : Prop := PRep 45 6 P g

abbrev L2 (LK : List Nat) (L : List (Equiv.Perm (Fin 45))) : Prop := List.Forall₂ R LK L

variable {P Q : Nat} {g h : Equiv.Perm (Fin 45)}

theorem R_mul (hP : R P g) (hQ : R Q h) : R (mulH P Q) (g * h) :=
  prep_pcomp (by norm_num) hP hQ

theorem R_inv (hP : R P g) : R (invH P) g⁻¹ := (prep_pinvS (by norm_num) hP).1

theorem R_one : R oneH 1 := prep_pidn (by norm_num) (by norm_num)

theorem R_tab (hP : R P g) : R P (tab g) := by rwa [tab_eq]

theorem pgH_eq (hP : R P g) (x : Fin 45) : pgH P x = g x := hP x

theorem eqH_eq (hP : R P g) (hQ : R Q h) : eqH P Q = decide (g = h) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  unfold eqH
  rw [List.all_eq_true]
  constructor
  · intro H
    ext x
    have := H x.val (List.mem_range.2 x.2)
    rw [Nat.beq_eq, pgH_eq hP x, pgH_eq hQ x] at this
    exact this
  · rintro rfl i hi
    rw [Nat.beq_eq, pgH_eq hP ⟨i, List.mem_range.1 hi⟩, pgH_eq hQ ⟨i, List.mem_range.1 hi⟩]

theorem commH_eq (hP : R P g) (hQ : R Q h) : commH P Q = decide (g * h = h * g) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  unfold commH
  rw [List.all_eq_true]
  constructor
  · intro H
    ext x
    have := H x.val (List.mem_range.2 x.2)
    rw [Nat.beq_eq, pgH_eq hQ x, pgH_eq hP x, pgH_eq hP (h x), pgH_eq hQ (g x)] at this
    simpa only [Equiv.Perm.mul_apply] using this
  · intro e i hi
    have hx := congrArg (fun f => (f ⟨i, List.mem_range.1 hi⟩ : Nat)) e
    simp only [Equiv.Perm.mul_apply] at hx
    rw [Nat.beq_eq, pgH_eq hQ ⟨i, List.mem_range.1 hi⟩, pgH_eq hP ⟨i, List.mem_range.1 hi⟩,
      pgH_eq hP (h _), pgH_eq hQ (g _)]
    exact hx

theorem memH_eq (hP : R P g) {LK : List Nat} {L : List (Equiv.Perm (Fin 45))} (hL : L2 LK L) :
    memH P LK = decide (g ∈ L) := by
  induction hL with
  | nil => simp [memH]
  | @cons Q h LK L hQ _ ih =>
    unfold memH at ih ⊢
    rw [List.any_cons, ih, eqH_eq hP hQ]
    simp [List.mem_cons]

theorem all_tr {LK : List Nat} {L : List (Equiv.Perm (Fin 45))} (hL : L2 LK L)
    {fK : Nat → Bool} {f : Equiv.Perm (Fin 45) → Bool} (hf : ∀ P g, R P g → fK P = f g) :
    LK.all fK = L.all f := by
  induction hL with
  | nil => rfl
  | cons hQ _ ih => rw [List.all_cons, List.all_cons, ih, hf _ _ hQ]

theorem any_tr {LK : List Nat} {L : List (Equiv.Perm (Fin 45))} (hL : L2 LK L)
    {fK : Nat → Bool} {f : Equiv.Perm (Fin 45) → Bool} (hf : ∀ P g, R P g → fK P = f g) :
    LK.any fK = L.any f := by
  induction hL with
  | nil => rfl
  | cons hQ _ ih => rw [List.any_cons, List.any_cons, ih, hf _ _ hQ]

theorem filter_tr {LK : List Nat} {L : List (Equiv.Perm (Fin 45))} (hL : L2 LK L)
    {fK : Nat → Bool} {f : Equiv.Perm (Fin 45) → Bool} (hf : ∀ P g, R P g → fK P = f g) :
    L2 (LK.filter fK) (L.filter f) := by
  induction hL with
  | nil => exact List.Forall₂.nil
  | @cons Q h LK L hQ _ ih =>
    rw [List.filter_cons, List.filter_cons, hf _ _ hQ]
    split
    · exact List.Forall₂.cons hQ ih
    · exact ih

theorem L2_snoc {LK : List Nat} {L : List (Equiv.Perm (Fin 45))} (hL : L2 LK L) (hP : R P g) :
    L2 (LK ++ [P]) (L ++ [g]) := by
  induction hL with
  | nil => exact List.Forall₂.cons hP List.Forall₂.nil
  | cons hQ _ ih => exact List.Forall₂.cons hQ ih

theorem foldl_tr {σK σ : Type} (S : σK → σ → Prop) {fK : σK → Nat → σK}
    {f : σ → Equiv.Perm (Fin 45) → σ} (hf : ∀ aK a P g, S aK a → R P g → S (fK aK P) (f a g)) :
    ∀ {LK : List Nat} {L : List (Equiv.Perm (Fin 45))}, L2 LK L → ∀ {aK : σK} {a : σ}, S aK a →
      S (LK.foldl fK aK) (L.foldl f a) := by
  intro LK L hL
  induction hL with
  | nil => exact fun h => h
  | cons hQ _ ih => exact fun h => ih (hf _ _ _ _ h hQ)

theorem closureStep_tr {GK : List Nat} {G : List (Equiv.Perm (Fin 45))} (hG : L2 GK G)
    {SK : List Nat} {S : List (Equiv.Perm (Fin 45))} (hS : L2 SK S) :
    L2 (closureStepH GK SK) (closureStep G S) := by
  unfold closureStepH closureStep
  refine foldl_tr L2 (fun aK a X x ha hX => ?_) hS hS
  refine foldl_tr L2 (fun bK b Y y hb hY => ?_) hG ha
  have hm : R (mulH Y X) (tab (y * x)) := R_tab (R_mul hY hX)
  rw [memH_eq hm hb]
  by_cases hc : tab (y * x) ∈ b
  · simp only [hc, decide_true, if_true]
    exact hb
  · simp only [hc, decide_false, Bool.false_eq_true, if_false]
    exact L2_snoc hb hm

theorem closureList_tr {GK : List Nat} {G : List (Equiv.Perm (Fin 45))} (hG : L2 GK G) :
    ∀ (k : Nat) {SK : List Nat} {S : List (Equiv.Perm (Fin 45))}, L2 SK S →
      L2 (closureListH GK k SK) (closureList G k S)
  | 0, _, _, hS => hS
  | k + 1, _, _, hS => closureList_tr hG k (closureStep_tr hG hS)

variable {BL PC : List Nat} {PA PB Z : Nat}

theorem pcl_tr (hpa : R PA pa) (hpb : R PB pb) :
    L2 (closureListH [PA, PB] 30 [oneH]) pcl :=
  closureList_tr (List.Forall₂.cons hpa (List.Forall₂.cons hpb List.Forall₂.nil)) 30
    (List.Forall₂.cons R_one List.Forall₂.nil)

theorem pl_tr (hB : L2 BL bl) (hPC : L2 PC pcl) : L2 (plH BL PC) pl :=
  filter_tr hB fun _ _ hP => memH_eq hP hPC

theorem plMul_tr {PL : List Nat} (hPL : L2 PL pl) : plMulH PL = plMulCheck :=
  all_tr hPL fun _ _ hX => all_tr hPL fun _ _ hY => memH_eq (R_mul hX hY) hPL

theorem plExp_tr {PL : List Nat} (hPL : L2 PL pl) : plExpH PL = plExpCheck :=
  all_tr hPL fun _ x hX => by rw [eqH_eq (R_mul hX (R_mul hX hX)) R_one, pow_three]

theorem blNorm_tr {PL : List Nat} (hB : L2 BL bl) (hPL : L2 PL pl) : blNormH BL PL = blNormCheck :=
  all_tr hB fun _ _ hX => all_tr hPL fun _ _ hP => memH_eq (R_mul (R_mul hX hP) (R_inv hX)) hPL

theorem cosetReps_tr {PL : List Nat} (hPL : L2 PL pl) {TK : List Nat}
    {T : List (Equiv.Perm (Fin 45))} (hT : L2 TK T) : L2 (cosetRepsH PL TK) (cosetReps T) := by
  unfold cosetRepsH cosetReps
  refine foldl_tr L2 (fun aK a X x ha hX => ?_) hT List.Forall₂.nil
  rw [any_tr ha fun _ _ hR => memH_eq (R_mul hX (R_inv hR)) hPL]
  split
  · exact ha
  · exact L2_snoc ha hX

theorem conjSet_tr (hB : L2 BL bl) {A : Nat} {a : Equiv.Perm (Fin 45)} (hA : R A a) :
    L2 (conjSetH BL A) (conjSet a) :=
  filter_tr hB fun _ _ hX => by
    rw [eqH_eq (R_mul (R_mul hX hA) (R_inv hX)) hA,
      eqH_eq (R_mul (R_mul hX hA) (R_inv hX)) (R_inv hA)]

theorem cosetCheck_tr {PL : List Nat} (hB : L2 BL bl) (hPL : L2 PL pl) {A : Nat}
    {a : Equiv.Perm (Fin 45)} (hA : R A a) : cosetCheckH BL PL A = cosetCheck a := by
  have hT := conjSet_tr hB hA
  have hR := cosetReps_tr hPL hT
  unfold cosetCheckH cosetCheck
  simp only
  rw [hR.length_eq, all_tr hT fun _ _ hX => any_tr hR fun _ _ hY =>
    memH_eq (R_mul hX (R_inv hY)) hPL]

theorem zData_tr {PL : List Nat} (hB : L2 BL bl) (hPL : L2 PL pl) (hz : R Z z0) :
    zDataH BL PL Z = zDataCheck z0 := by
  unfold zDataH zDataCheck
  rw [eqH_eq hz R_one, decide_not,
    any_tr hPL fun _ _ hX => any_tr hPL fun _ _ hY =>
      eqH_eq hz (R_mul (R_mul (R_mul hX hY) (R_inv hX)) (R_inv hY)),
    all_tr hPL fun _ _ hA => by
      rw [eqH_eq hA R_one, eqH_eq hA hz, eqH_eq (R_inv hA) hz, cosetCheck_tr hB hPL hA]]

theorem checks_of (hB : L2 BL bl) (hpa : R PA pa) (hpb : R PB pb) (hz : R Z z0)
    (h : allH BL (closureListH [PA, PB] 30 [oneH]) Z = true) :
    bl.length = 648 ∧ pl.length = 27 ∧ plMulCheck = true ∧ plExpCheck = true ∧
      blNormCheck = true ∧ zDataCheck z0 = true := by
  have hPL := pl_tr hB (pcl_tr hpa hpb)
  unfold allH at h
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  refine ⟨hB.length_eq ▸ h1, hPL.length_eq ▸ h2, plMul_tr hPL ▸ h3, plExp_tr hPL ▸ h4,
    blNorm_tr hB hPL ▸ h5, zData_tr hB hPL hz ▸ h6⟩

end CFSG.KC.EvenSporU42

end
