module

public import CFSG.Certificates.Kernel.M3BFib.Fib0Sound
public import Certificates.Data.Kernel.M3BSyl.Walk

public section

set_option linter.unusedSectionVars false

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.KC.M3BS

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF
open CFSG.KC.M3BF (enc dig3 vm vz GoodRow GoodMat vecK Ins insWT slpNodes slpWT idRows)
open Timmesfeld.M3B (WT LM matOf mone mmul mpow mOfRows)

@[expose] noncomputable def toMatK (A : MatK) : Matrix (Fin 12) (Fin 12) (ZMod 3) :=
  Matrix.of fun i j => vz (A.getD i 0) j

theorem vmK_eq (w : ℕ) (B : MatK) : vmK w B = M3BF.mvK w B := rfl

theorem mmK_eq (A B : MatK) : mmK A B = M3BF.mmK A B := rfl

theorem vecK_eq (A : MatK) (w : Fin 12 → ZMod 3) : vecK A w = Matrix.vecMul w (toMatK A) := by
  funext i
  simp only [vecK, Matrix.vecMul, dotProduct, toMatK, Matrix.of_apply]

theorem vz_vmK {B : MatK} (hB : GoodMat B) (w : ℕ) :
    vz (vmK w B) = Matrix.vecMul (vz w) (toMatK B) := by
  rw [vmK_eq, M3BF.vz_mvK hB, vecK_eq]

theorem goodRow_vmK (w : ℕ) (B : MatK) : GoodRow (vmK w B) := M3BF.goodRow_red _

theorem goodMat_mmK {A : MatK} (B : MatK) (hA : A.length = 12) : GoodMat (mmK A B) :=
  M3BF.goodMat_mmK hA

theorem toMatK_mmK {A B : MatK} (hA : A.length = 12) (hB : GoodMat B) :
    toMatK (mmK A B) = toMatK A * toMatK B := by
  ext j i
  have e : (mmK A B).getD j 0 = vmK (A.getD j 0) B :=
    M3BF.getD_map_lt (f := fun r => vmK r B) (d := 0) (by rw [hA]; exact j.isLt)
  have := congrFun (vz_vmK hB (A.getD j 0)) i
  simp only [toMatK, Matrix.of_apply, Matrix.mul_apply] at this ⊢
  rw [e, this]
  simp only [Matrix.vecMul, dotProduct, toMatK, Matrix.of_apply]

theorem goodMat_idK : GoodMat idK := M3BF.goodMat_idRows

theorem toMatK_idK : toMatK idK = 1 := by
  have h : ∀ i j : Fin 12, vz (idRows.getD i 0) j = if i = j then 1 else 0 := by
    decide +kernel
  ext i j
  simp only [toMatK, Matrix.of_apply, Matrix.one_apply]
  exact h i j

theorem goodMat_of_goodK {A : MatK} (h : goodK A = true) : GoodMat A := M3BF.goodMat_of_goodM h

theorem goodRow_inj {a b : ℕ} (ha : GoodRow a) (hb : GoodRow b) (h : vz a = vz b) : a = b := by
  suffices hd : dig3 a = dig3 b by
    calc a = enc (dig3 a) := ha.symm
      _ = enc (dig3 b) := by rw [hd]
      _ = b := hb
  refine List.ext_getElem (by rw [M3BF.dig3_length, M3BF.dig3_length]) fun k h1 h2 => ?_
  have hk : k < 12 := by rwa [M3BF.dig3_length] at h1
  have e := congrFun h ⟨k, hk⟩
  simp only [vz] at e
  rw [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at e
  have l1 := M3BF.dig3_lt a _ (List.getElem_mem h1)
  have l2 := M3BF.dig3_lt b _ (List.getElem_mem h2)
  have := congrArg ZMod.val e
  rwa [ZMod.val_cast_of_lt l1, ZMod.val_cast_of_lt l2] at this

@[expose] def Rep (A : MatK) (w : WT) : Prop :=
  GoodMat A ∧ toMatK A = toMatrix (matOf (LM ()) w)

theorem cast_ofNat3 (n : ℕ) :
    ((n : ℕ) : ZMod 3) = CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF.toZ (Fin.ofNat 3 n) := by
  apply ZMod.val_injective
  rw [ZMod.val_natCast, toZ_val]
  rfl

theorem rows_rep {R : List (List ℕ)} (h : rowsOK R = true) :
    GoodMat (R.map enc) ∧ toMatK (R.map enc) = toMatrix (mOfRows R) := by
  unfold rowsOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Nat.blt_eq] at h
  obtain ⟨hl, hr⟩ := h
  refine ⟨⟨by rw [List.length_map, hl], fun r hr' => ?_⟩, ?_⟩
  · obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hr'
    exact M3BF.goodRow_enc (hr s hs).1 (hr s hs).2
  · ext i j
    have hi : (i : ℕ) < R.length := by rw [hl]; exact i.isLt
    have hs := hr _ (List.getElem_mem hi)
    rw [toMatrix_apply, mget_mOfRows]
    simp only [toMatK, Matrix.of_apply]
    rw [M3BF.getD_map_lt (d := []) hi, List.getD_eq_getElem _ [] hi, M3BF.vz_enc hs.1 hs.2]
    exact cast_ofNat3 _

theorem rep_letter (hl : letChk = true) (i : ℕ) : Rep (letK.getD i idK) (.gen i) := by
  unfold letChk at hl
  simp only [Bool.and_eq_true] at hl
  obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := hl
  have e : matOf (LM ()) (.gen i) = (LM ()).getD i mone := rfl
  rw [Rep, e]
  rcases i with _ | _ | _ | _ | i
  · exact rows_rep h0
  · exact rows_rep h1
  · exact rows_rep h2
  · exact rows_rep h3
  · have h2 : (LM ()).getD (i + 4) mone = mone := by
      unfold LM
      simp [Array.getD]
    have h3 : letK.getD (i + 4) idK = idK := by
      unfold letK
      simp
    rw [h2, h3, toMatK_idK, toMatrix_mone]
    exact ⟨goodMat_idK, rfl⟩

theorem rep_getD {As : List MatK} {ws : List WT} (h : List.Forall₂ Rep As ws) {d : MatK} {w : WT}
    (hd : Rep d w) : ∀ i, Rep (As.getD i d) (ws.getD i w) := by
  induction h with
  | nil => intro i; simpa using hd
  | cons hab _ ih =>
    intro i
    cases i with
    | zero => simpa using hab
    | succ i => simpa using ih i

theorem rep_headD {As : List MatK} {ws : List WT} (h : List.Forall₂ Rep As ws) {d : MatK} {w : WT}
    (hd : Rep d w) : Rep (As.headD d) (ws.headD w) := by
  cases h with
  | nil => exact hd
  | cons hab _ => exact hab

theorem rep_mm {A B : MatK} {a b : WT} (hA : Rep A a) (hB : Rep B b) : Rep (mmK A B) (.mul a b) := by
  refine ⟨goodMat_mmK B hA.1.1, ?_⟩
  rw [toMatK_mmK hA.1.1 hB.1, hA.2, hB.2, _root_.Timmesfeld.M3B.matOf, toMatrix_mmul]

theorem rep_pow {A : MatK} {a : WT} (hA : Rep A a) : ∀ k, Rep (mpowK A k) (.pow a k)
  | 0 => by
    refine ⟨goodMat_idK, ?_⟩
    change toMatK idK = toMatrix (mpow (matOf (LM ()) a) 0)
    rw [toMatK_idK, mpow, toMatrix_mone]
  | k + 1 => by
    have ih := rep_pow hA k
    refine ⟨goodMat_mmK A ih.1.1, ?_⟩
    change toMatK (mmK (mpowK A k) A) = toMatrix (mpow (matOf (LM ()) a) (k + 1))
    rw [toMatK_mmK ih.1.1 hA.1, ih.2, hA.2, mpow, toMatrix_mmul]
    rfl

theorem rep_ins {L : List MatK} (hL : ∀ i, Rep (L.getD i idK) (.gen i)) (ins : Ins)
    {acc : List MatK} {ws : List WT} (h : List.Forall₂ Rep acc ws) :
    Rep (insK L ins acc) (insWT ins ws) := by
  obtain ⟨o, x, y⟩ := ins
  have hd : Rep (L.getD 0 idK) (WT.gen 0) := hL 0
  rcases o with _ | _ | o
  · exact hL x
  · exact rep_mm (rep_getD h hd x) (rep_getD h hd y)
  · exact rep_pow (rep_getD h hd x) y

theorem nodes_rep {L : List MatK} (hL : ∀ i, Rep (L.getD i idK) (.gen i)) :
    ∀ P : List Ins, List.Forall₂ Rep (nodesK L P) (slpNodes P)
  | [] => List.Forall₂.nil
  | ins :: P => List.Forall₂.cons (rep_ins hL ins (nodes_rep hL P)) (nodes_rep hL P)

theorem matSLP_rep {L : List MatK} (hL : ∀ i, Rep (L.getD i idK) (.gen i)) (P : List Ins) :
    Rep (matSLP L P) (slpWT P) :=
  rep_headD (nodes_rep hL P) (hL 0)

theorem node_rep {L : List MatK} (hL : ∀ i, Rep (L.getD i idK) (.gen i)) (P : List Ins) {i : ℕ}
    (hi : i < (nodesK L P).length) :
    Rep ((nodesK L P).getD i idK) ((slpNodes P).getD i (.gen 0)) := by
  have := rep_getD (nodes_rep hL P) (hL 0) i
  rwa [List.getD_eq_getElem _ _ hi, ← List.getD_eq_getElem _ idK hi] at this

@[expose] def nfL {G : Type*} [Monoid G] (Us : List G) (es : List ℕ) : G :=
  (List.zipWith (fun u e => u ^ e) Us es).prod

@[expose] def RepU (A : MatK) (u : GL (Fin 12) (ZMod 3)) : Prop :=
  GoodMat A ∧ toMatK A = (u : Matrix (Fin 12) (Fin 12) (ZMod 3))

theorem nfPow_rep {g : MatK} {u : GL (Fin 12) (ZMod 3)} (hg : RepU g u) :
    ∀ (e : ℕ) (acc : MatK), GoodMat acc →
      GoodMat (Nat.rec (motive := fun _ => MatK) acc (fun _ a => mmK a g) e) ∧
      toMatK (Nat.rec (motive := fun _ => MatK) acc (fun _ a => mmK a g) e) =
        toMatK acc * ((u ^ e : GL (Fin 12) (ZMod 3)) : Matrix (Fin 12) (Fin 12) (ZMod 3))
  | 0, acc, h => ⟨h, by simp⟩
  | e + 1, acc, h => by
    obtain ⟨h1, h2⟩ := nfPow_rep hg e acc h
    refine ⟨goodMat_mmK g h1.1, ?_⟩
    change toMatK (mmK (Nat.rec (motive := fun _ => MatK) acc (fun _ a => mmK a g) e) g) = _
    rw [toMatK_mmK h1.1 hg.1, h2, hg.2, pow_succ, Units.val_mul, Matrix.mul_assoc]

theorem nfAcc_rep : ∀ {gs : List MatK} {Us : List (GL (Fin 12) (ZMod 3))},
    List.Forall₂ RepU gs Us → ∀ (es : List ℕ) (acc : MatK), GoodMat acc →
      GoodMat (nfAcc gs es acc) ∧
      toMatK (nfAcc gs es acc) = toMatK acc * ((nfL Us es : GL (Fin 12) (ZMod 3)) :
        Matrix (Fin 12) (Fin 12) (ZMod 3))
  | [], [], .nil, es, acc, h => ⟨h, by simp [nfL, nfAcc]⟩
  | _ :: _, _ :: _, .cons _ _, [], acc, h => ⟨h, by simp [nfL, nfAcc]⟩
  | g :: gs, u :: Us, .cons hgu hr, e :: es, acc, h => by
    have hp := nfPow_rep hgu e acc h
    obtain ⟨h1, h2⟩ := nfAcc_rep hr es _ hp.1
    refine ⟨h1, ?_⟩
    change toMatK (nfAcc gs es (Nat.rec (motive := fun _ => MatK) acc (fun _ a => mmK a g) e)) = _
    rw [h2, hp.2, Matrix.mul_assoc]
    simp [nfL, Units.val_mul]

theorem nfK_rep {gs : List MatK} {Us : List (GL (Fin 12) (ZMod 3))} (h : List.Forall₂ RepU gs Us)
    (es : List ℕ) : RepU (nfK gs es) (nfL Us es) := by
  obtain ⟨h1, h2⟩ := nfAcc_rep h es idK goodMat_idK
  exact ⟨h1, by rw [nfK, h2, toMatK_idK, Matrix.one_mul]⟩

theorem nfVPow_rep {g : MatK} {u : GL (Fin 12) (ZMod 3)} (hg : RepU g u) :
    ∀ (e : ℕ) (w : ℕ), GoodRow w →
      GoodRow (Nat.rec (motive := fun _ => ℕ) w (fun _ a => vmK a g) e) ∧
      vz (Nat.rec (motive := fun _ => ℕ) w (fun _ a => vmK a g) e) =
        Matrix.vecMul (vz w) ((u ^ e : GL (Fin 12) (ZMod 3)) : Matrix (Fin 12) (Fin 12) (ZMod 3))
  | 0, w, h => ⟨h, by simp⟩
  | e + 1, w, h => by
    obtain ⟨h1, h2⟩ := nfVPow_rep hg e w h
    refine ⟨goodRow_vmK _ g, ?_⟩
    change vz (vmK (Nat.rec (motive := fun _ => ℕ) w (fun _ a => vmK a g) e) g) = _
    rw [vz_vmK hg.1, h2, hg.2, Matrix.vecMul_vecMul, pow_succ, Units.val_mul]

theorem nfV_rep : ∀ {gs : List MatK} {Us : List (GL (Fin 12) (ZMod 3))},
    List.Forall₂ RepU gs Us → ∀ (es : List ℕ) (w : ℕ), GoodRow w →
      GoodRow (nfV gs es w) ∧
      vz (nfV gs es w) = Matrix.vecMul (vz w) ((nfL Us es : GL (Fin 12) (ZMod 3)) :
        Matrix (Fin 12) (Fin 12) (ZMod 3))
  | [], [], .nil, es, w, h => ⟨h, by simp [nfL, nfV]⟩
  | _ :: _, _ :: _, .cons _ _, [], w, h => ⟨h, by simp [nfL, nfV]⟩
  | g :: gs, u :: Us, .cons hgu hr, e :: es, w, h => by
    have hp := nfVPow_rep hgu e w h
    obtain ⟨h1, h2⟩ := nfV_rep hr es _ hp.1
    refine ⟨h1, ?_⟩
    change vz (nfV gs es (Nat.rec (motive := fun _ => ℕ) w (fun _ a => vmK a g) e)) = _
    rw [h2, hp.2, Matrix.vecMul_vecMul]
    simp [nfL, Units.val_mul]

end CFSG.KC.M3BS

end
