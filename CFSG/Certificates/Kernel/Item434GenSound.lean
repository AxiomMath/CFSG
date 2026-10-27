module

public import Certificates.Data.Kernel.Item434Gen
public import Certificates.Data.Item434SporWords
public import CFSG.Certificates.Kernel.Misc.ArrEnumUnpack
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CFSG.KC.Item434Gen

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KC.Misc.ArrEnum
open CFSG.Monster.B.Co2.Native CFSG.RankThree.PartTwo.Sec4.Item434SporGen
open CFSG.Certificates.Native (rawInvs)

variable {n w : Nat}

theorem allLt_eq_allN {k : Nat} {f g : Nat → Bool} (h : ∀ i < k, f i = g i) :
    allLt k f = allN k g := by
  apply Bool.eq_iff_iff.2
  rw [CFSG.Monster.B.Co2.allLt_iff, CFSG.KS.Raw.Orb.allN_iff]
  exact ⟨fun h' i hi => (h i hi) ▸ h' i hi, fun h' i hi => (h i hi).symm ▸ h' i hi⟩

theorem getElem!_map_toArray {α β : Type} [Inhabited β] (f : α → β) (l : List α) [Inhabited α]
    {j : Nat} (hj : j < l.length) : (l.map f).toArray[j]! = f (l.getD j default) := by
  rw [getElem!_pos _ j (by simpa using hj)]
  simp [List.getD, List.getElem?_eq_getElem hj]

theorem map_getElem! {α β : Type} [Inhabited α] [Inhabited β] (f : α → β) (a : Array α) {i : Nat}
    (h : i < a.size) : (a.map f)[i]! = f a[i]! := by
  rw [getElem!_pos (a.map f) i (by simpa using h), Array.getElem_map, getElem!_pos a i h]

variable (hw : szOK n w = true)
include hw

theorem powN_unpack {p : Nat} (hp : PP n w p) :
    ∀ k, powN n (unpack n w p) k = unpack n w (pwK n w p k)
  | 0 => idA_eq hw
  | k + 1 => by
    have e1 : pwK n w p (k + 1) = pcomp n w (mask w) p (pwK n w p k) :=
      CFSG.KS.PF.strictN_eqP (ppow n w (mask w) (pidn n w) p k) (fun q => pcomp n w (mask w) p q)
    have e2 : powN n (unpack n w p) (k + 1) = compA n (unpack n w p) (powN n (unpack n w p) k) :=
      rfl
    rw [e2, powN_unpack hp k, e1, compA_PP hp (pp_ppow hw hp k)]

theorem pp_pNK {e₁ e₂ : Nat} (h₁ : PP n w e₁) (h₂ : PP n w e₂) (ab : Nat × Nat) :
    PP n w (pNK n w e₁ e₂ ab) :=
  (pp_ppow hw h₁ ab.1).mul (pp_ppow hw h₂ ab.2)

theorem pN_unpack {e₁ e₂ : Nat} (h₁ : PP n w e₁) (h₂ : PP n w e₂) (ab : Nat × Nat) :
    pN n (unpack n w e₁) (unpack n w e₂) ab = unpack n w (pNK n w e₁ e₂ ab) := by
  unfold pN pNK
  rw [powN_unpack hw h₁, powN_unpack hw h₂, compA_PP (pp_ppow hw h₁ _) (pp_ppow hw h₂ _)]

theorem isInvA_PP {p : Nat} (hp : PP n w p) :
    isInvA n (unpack n w p) (invCand n (unpack n w p)) = true := by
  have h := invEqK_sound (CFSG.KS.PinvS.permOK_pinvS hp.1 hp.2)
  rw [h.1]
  exact h.2

theorem isInvA_of_permOK {p r : Nat} (h : permOK n w (mask w) (n * w) p r = true) :
    isInvA n (unpack n w p) (invCand n (unpack n w p)) = true := by
  have h' := invEqK_sound h
  rw [h'.1]
  exact h'.2

theorem e9_eq {e₁ e₂ : Nat} (h₁ : PP n w e₁) (h₂ : PP n w e₂) :
    e9Check n (unpack n w e₁) (unpack n w e₂) = e9K n w e₁ e₂ := by
  unfold e9Check commN e9K
  rw [isInvA_PP hw h₁, isInvA_PP hw h₂, powN_unpack hw h₁, powN_unpack hw h₂,
    powN_unpack hw h₁, idA_eq hw, eqA_PP (pp_ppow hw h₁ 3) (PP.id hw),
    eqA_PP (pp_ppow hw h₂ 3) (PP.id hw), compA_PP h₁ h₂, compA_PP h₂ h₁,
    eqA_PP (h₁.mul h₂) (h₂.mul h₁), eqA_PP h₁ (PP.id hw), eqA_PP h₂ (PP.id hw), eqA_PP h₂ h₁,
    eqA_PP h₂ (pp_ppow hw h₁ 2)]
  simp only [Bool.true_and]

theorem sig_eq {Sg : Array (Array Nat)} {S : Nat → Nat} {k : Nat} (hsz : Sg.size = k)
    (hS : ∀ i < k, Sg[i]! = unpack n w (S i)) (hP : ∀ i < k, PP n w (S i)) {e₁ e₂ : Nat}
    (h₁ : PP n w e₁) (h₂ : PP n w e₂) (ords : List Nat) (ps : List (Nat × Nat)) :
    sigCheck n Sg ords ps (unpack n w e₁) (unpack n w e₂) = sigK n w S k ords ps e₁ e₂ := by
  unfold sigCheck sigK
  rw [hsz]
  refine allLt_eq_allN fun i hi => ?_
  have hp := hP i hi
  have hq := pp_pNK hw h₁ h₂ (ps.getD i (0, 0))
  unfold commN
  rw [hS i hi, pN_unpack hw h₁ h₂, powN_unpack hw hp, idA_eq hw,
    eqA_PP (pp_ppow hw hp _) (PP.id hw), compA_PP hp hq, compA_PP hq hp,
    eqA_PP (hp.mul hq) (hq.mul hp), eqA_PP hq (PP.id hw)]

theorem heis_eq {x xi y yi z : Nat} (hx : permOK n w (mask w) (n * w) x xi = true)
    (hxi : permOK n w (mask w) (n * w) xi x = true) (hy : permOK n w (mask w) (n * w) y yi = true)
    (hyi : permOK n w (mask w) (n * w) yi y = true) (hz : cmK n w x xi y yi = z) :
    cmA n (unpack n w x) (unpack n w y) = unpack n w z ∧ PP n w z ∧
      heisCheck n (unpack n w x) (unpack n w y) = heisK n w x y z := by
  have px := pp_of_permOK hw hx
  have pxi := pp_of_permOK hw hxi
  have py := pp_of_permOK hw hy
  have pyi := pp_of_permOK hw hyi
  have ecm : cmA n (unpack n w x) (unpack n w y) = unpack n w z := by
    unfold cmA
    rw [(invEqK_sound hx).1, (invEqK_sound hy).1, compA_PP px py, compA_PP pxi pyi,
      compA_PP (px.mul py) (pxi.mul pyi), ← hz]
    rfl
  have pz : PP n w z := by
    rw [← hz]
    exact (px.mul py).mul (pxi.mul pyi)
  refine ⟨ecm, pz, ?_⟩
  unfold heisCheck commN heisK
  rw [ecm, isInvA_PP hw px, isInvA_PP hw py, powN_unpack hw px, powN_unpack hw py, idA_eq hw,
    eqA_PP (pp_ppow hw px 3) (PP.id hw), eqA_PP (pp_ppow hw py 3) (PP.id hw), compA_PP pz px,
    compA_PP px pz, compA_PP pz py, compA_PP py pz, eqA_PP (pz.mul px) (px.mul pz),
    eqA_PP (pz.mul py) (py.mul pz), eqA_PP pz (PP.id hw)]
  simp only [Bool.true_and]

theorem wab_eq {a ai b bi v : Nat} {wd : List Int} (ha : permOK n w (mask w) (n * w) a ai = true)
    (hb : permOK n w (mask w) (n * w) b bi = true)
    (h : wordEqK n w (mask w) (pidn n w) (twoK a b) (twoK ai bi) 2 wd v = true) :
    wab n (unpack n w a) (unpack n w b) wd = unpack n w v ∧ CFSG.Monster.B.Co2.Native.lettersOK 2 wd = true := by
  have e : #[invCand n (unpack n w a), invCand n (unpack n w b)] =
      rawInvs n #[unpack n w a, unpack n w b] := by
    simp [rawInvs]
  have hS : (#[unpack n w a, unpack n w b] : Array (Array Nat)).size = 2 ∧
      ∀ j < 2, (#[unpack n w a, unpack n w b] : Array (Array Nat))[j]! = unpack n w (twoK a b j) := by
    refine ⟨rfl, fun j hj => ?_⟩
    match j, hj with
    | 0, _ => simp [twoK]
    | 1, _ => simp [twoK]
  have hp : allN 2 (fun j => permOK n w (mask w) (n * w) (twoK a b j) (twoK ai bi j)) = true := by
    refine CFSG.KS.Raw.Orb.allN_iff.2 fun j hj => ?_
    match j, hj with
    | 0, _ => exact ha
    | 1, _ => exact hb
  have := wordEqK_sound hS hp h
  unfold wab
  rw [e]
  exact this

theorem fix_sound {a ai b bi e₁ e₂ k : Nat} {S SI : Nat → Nat} {c : FixData}
    (ha : permOK n w (mask w) (n * w) a ai = true) (hb : permOK n w (mask w) (n * w) b bi = true)
    (hk : c.sw.length = k)
    (hsw : ∀ j < k, wordEqK n w (mask w) (pidn n w) (twoK a b) (twoK ai bi) 2 (c.sw.getD j [])
      (S j) = true)
    (hSI : allN k (fun j => permOK n w (mask w) (n * w) (S j) (SI j)) = true)
    (hwa : wordEqK n w (mask w) (pidn n w) S SI k c.wa a = true)
    (hwb : wordEqK n w (mask w) (pidn n w) S SI k c.wb b = true)
    (h₁ : PP n w e₁) (h₂ : PP n w e₂) (he9 : e9K n w e₁ e₂ = true)
    (hsig : sigK n w S k c.ords c.ps e₁ e₂ = true) :
    c.check n (unpack n w a) (unpack n w b) (unpack n w e₁) (unpack n w e₂) = true := by
  have hperm : ∀ j < k, permOK n w (mask w) (n * w) (S j) (SI j) = true :=
    CFSG.KS.Raw.Orb.allN_iff.1 hSI
  have hval : ∀ j < k, wab n (unpack n w a) (unpack n w b) (c.sw.getD j []) = unpack n w (S j) ∧
      CFSG.Monster.B.Co2.Native.lettersOK 2 (c.sw.getD j []) = true := fun j hj => wab_eq hw ha hb (hsw j hj)
  unfold FixData.check fixWordsCheck
  dsimp only
  generalize hG : wabs n (unpack n w a) (unpack n w b) c.sw = Sg
  have hsz : Sg.size = k := by
    rw [← hG, ← hk]
    simp [wabs]
  have hSg : ∀ j < k, Sg[j]! = unpack n w (S j) := by
    intro j hj
    rw [← hG, wabs, getElem!_map_toArray _ _ (by omega)]
    exact (hval j hj).1
  have hSk : Sg.size = k ∧ ∀ j < k, Sg[j]! = unpack n w (S j) := ⟨hsz, hSg⟩
  have hi : Sg.map (invCand n) = rawInvs n Sg := rfl
  obtain ⟨ea, la⟩ := wordEqK_sound hSk hSI hwa
  obtain ⟨eb, lb⟩ := wordEqK_sound hSk hSI hwb
  have hwords : wordsOK 2 c.sw = true := by
    unfold CFSG.RankThree.PartTwo.Sec4.Item434SporGen.wordsOK
    rw [List.all_eq_true]
    intro x hx
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hx
    have := (hval j (by omega)).2
    rwa [List.getD_eq_getElem _ _ hj] at this
  have hinv : allLt Sg.size (fun i => isInvA n Sg[i]! (Sg.map (invCand n))[i]!) = true := by
    rw [CFSG.Monster.B.Co2.allLt_iff]
    intro i hi'
    rw [map_getElem! _ _ hi', hSg i (by omega)]
    exact isInvA_of_permOK hw (hperm i (by omega))
  rw [isInvA_of_permOK hw ha, isInvA_of_permOK hw hb, hwords, hinv, hi, hsz, la, lb, ea, eb,
    eqK_sound (Nat.beq_refl a), eqK_sound (Nat.beq_refl b), e9_eq hw h₁ h₂, he9,
    sig_eq hw hsz hSg (fun j hj => pp_of_permOK hw (hperm j hj)) h₁ h₂, hsig]
  rfl

theorem ex27E2_0 (x y : Array Nat) : ex27E2 n x y 0 = x := by
  have _ := hw
  rfl

theorem ex27E2_1 (x y : Array Nat) : ex27E2 n x y 1 = y := by
  have _ := hw
  rfl

theorem ex27E2_2 (x y : Array Nat) : ex27E2 n x y 2 = compA n x y := by
  have _ := hw
  rfl

theorem ex27E2_3 (x y : Array Nat) : ex27E2 n x y 3 = compA n x (powN n y 2) := by
  have _ := hw
  rfl

theorem ex27_sound {a ai b bi x xi y yi z w₂ w₃ : Nat} {xw yw : List Int} {c₀ c₁ c₂ c₃ : FixData}
    (ha : permOK n w (mask w) (n * w) a ai = true) (hb : permOK n w (mask w) (n * w) b bi = true)
    (hx : wordEqK n w (mask w) (pidn n w) (twoK a b) (twoK ai bi) 2 xw x = true)
    (hy : wordEqK n w (mask w) (pidn n w) (twoK a b) (twoK ai bi) 2 yw y = true)
    (hxp : permOK n w (mask w) (n * w) x xi = true) (hxi : permOK n w (mask w) (n * w) xi x = true)
    (hyp : permOK n w (mask w) (n * w) y yi = true) (hyi : permOK n w (mask w) (n * w) yi y = true)
    (hz : Nat.beq (cmK n w x xi y yi) z = true) (hh : heisK n w x y z = true)
    (hw₂ : Nat.beq (pcK n w x y) w₂ = true) (hw₃ : Nat.beq (pcK n w x (pwK n w y 2)) w₃ = true)
    (h₀ : c₀.check n (unpack n w a) (unpack n w b) (unpack n w z) (unpack n w x) = true)
    (h₁ : c₁.check n (unpack n w a) (unpack n w b) (unpack n w z) (unpack n w y) = true)
    (h₂ : c₂.check n (unpack n w a) (unpack n w b) (unpack n w z) (unpack n w w₂) = true)
    (h₃ : c₃.check n (unpack n w a) (unpack n w b) (unpack n w z) (unpack n w w₃) = true) :
    ex27Check n (unpack n w a) (unpack n w b) xw yw c₀ c₁ c₂ c₃ = true := by
  obtain ⟨ex, lx⟩ := wab_eq hw ha hb hx
  obtain ⟨ey, ly⟩ := wab_eq hw ha hb hy
  obtain ⟨ecm, -, eh⟩ := heis_eq hw hxp hxi hyp hyi (Nat.eq_of_beq_eq_true hz)
  have px := pp_of_permOK hw hxp
  have py := pp_of_permOK hw hyp
  have e2 : ex27E2 n (unpack n w x) (unpack n w y) 2 = unpack n w w₂ := by
    rw [ex27E2_2 hw, compA_PP px py, ← Nat.eq_of_beq_eq_true hw₂]
  have e3 : ex27E2 n (unpack n w x) (unpack n w y) 3 = unpack n w w₃ := by
    rw [ex27E2_3 hw, powN_unpack hw py, compA_PP px (pp_ppow hw py 2),
      ← Nat.eq_of_beq_eq_true hw₃]
  unfold ex27Check
  dsimp only
  rw [ex, ey, isInvA_of_permOK hw ha, isInvA_of_permOK hw hb, lx, ly, eh, hh, ecm, e2, e3,
    ex27E2_0 hw, ex27E2_1 hw, h₀, h₁, h₂, h₃]
  rfl

end CFSG.KC.Item434Gen

end
