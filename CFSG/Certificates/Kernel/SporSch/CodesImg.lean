module

public import CFSG.Certificates.Kernel.SporSch.MathieuOC2Sound
public import CFSG.Certificates.Kernel.J2CoverSound

public section

namespace CFSG.KS.SporSch.CodesImg

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MEnum CFSG.KS.SporSch.MOC
open CFSG.KC.Child3 CFSG.KC.J2Cover CFSG.ComponentClassification.J2Cover
open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.Th.Native CFSG.Monster.B.Mathieu
open CFSG.KS.Mathieu (icode)

variable {n w : Nat}

private theorem strictN_id (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

private theorem strictB_id (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

private theorem bAnd_true {a b : Bool} (h : bAnd(a, b) = true) : a = true ∧ b = true := by
  cases a <;> simp_all

theorem evalCodes_img (hsz : szOK n w = true) {gs : List (Equiv.Perm (Fin n))} {P Pi : Nat → Nat}
    (hg : ∀ j < gs.length, imageList (gs.getD j 1) = (unpack n w (P j)).toList)
    (hp : ∀ j < gs.length, permOK n w (mask w) (n * w) (P j) (Pi j) = true)
    (hid : imageList (1 : Equiv.Perm (Fin n)) = (unpack n w (pidn n w)).toList) :
    ∀ {wd : List Int}, lettersK gs.length wd = true →
      imageList (evalCodes gs wd) = (unpack n w (wordK n w (mask w) (pidn n w) P Pi wd)).toList
  | [], _ => hid
  | z :: wd, h => by
    have hc : lettersK gs.length (z :: wd) = bAnd(Nat.blt (nat_lit 0) (icode z),
        bAnd(Nat.ble (Nat.shiftRight (icode z) (nat_lit 1)) gs.length, lettersK gs.length wd)) := by
      change strictB (icode z) (fun c => bAnd(Nat.blt (nat_lit 0) c,
        bAnd(Nat.ble (Nat.shiftRight c (nat_lit 1)) gs.length, lettersK gs.length wd))) = _
      exact strictB_id _ _
    obtain ⟨h1, h⟩ := bAnd_true (hc ▸ h)
    obtain ⟨h2, h3⟩ := bAnd_true h
    have ih := evalCodes_img hsz hg hp hid h3
    have hw : wordK n w (mask w) (pidn n w) P Pi (z :: wd) = pcomp n w (mask w)
        (nIf(Nat.beq (Nat.land (icode z) (nat_lit 1)) (nat_lit 0),
          P (Nat.sub (Nat.shiftRight (icode z) (nat_lit 1)) (nat_lit 1)),
          Pi (Nat.sub (Nat.shiftRight (icode z) (nat_lit 1)) (nat_lit 1))))
        (wordK n w (mask w) (pidn n w) P Pi wd) := by
      change strictN (wordK n w (mask w) (pidn n w) P Pi wd) (fun T => strictN (icode z)
        (fun c => pcomp n w (mask w) (nIf(Nat.beq (Nat.land c (nat_lit 1)) (nat_lit 0),
          P (Nat.sub (Nat.shiftRight c (nat_lit 1)) (nat_lit 1)),
          Pi (Nat.sub (Nat.shiftRight c (nat_lit 1)) (nat_lit 1)))) T)) = _
      simp only [strictN_id]
    have shr : ∀ a b : Nat, Nat.shiftRight a b = a / 2 ^ b := Nat.shiftRight_eq_div_pow
    have h1' := Nat.blt_eq.mp h1
    have h2' := Nat.ble_eq.mp h2
    rw [shr, Nat.pow_one] at h2'
    have land1 : ∀ c : Nat, Nat.land c 1 = c % 2 := Nat.and_one_is_mod
    have sub : ∀ a b : Nat, Nat.sub a b = a - b := fun _ _ => rfl
    rw [hw, shr, Nat.pow_one, land1, sub]
    unfold evalCodes
    cases z with
    | ofNat k =>
      have ek : icode (Int.ofNat k) = k + k := rfl
      have hk1 : 0 < k := by
        have := h1'
        rw [ek] at this
        omega
      have hk2 : k - 1 < gs.length := by
        have := h2'
        rw [ek] at this
        omega
      rw [ek]
      have hk : (k + k) % 2 = 0 := by omega
      have hd : (k + k) / 2 - 1 = k - 1 := by omega
      have hpos : (0 : Int) < Int.ofNat k := Int.ofNat_lt.mpr hk1
      rw [hk, hd]
      simp only [hpos, ↓reduceIte]
      have et : (Int.ofNat k).toNat = k := rfl
      rw [et]
      exact mulK_rep hsz (hg (k - 1) hk2) ih
    | negSucc k =>
      have ek : icode (Int.negSucc k) = k + 1 + (k + 1) + 1 := rfl
      have hk2 : k < gs.length := by
        have := h2'
        rw [ek] at this
        omega
      rw [ek]
      have hk : (k + 1 + (k + 1) + 1) % 2 = 1 := by omega
      have hd : (k + 1 + (k + 1) + 1) / 2 - 1 = k := by omega
      have hneg : ¬ (0 : Int) < Int.negSucc k :=
        Int.not_lt.mpr (Int.le_of_lt (Int.negSucc_lt_zero k))
      rw [hk, hd]
      simp only [hneg, ↓reduceIte]
      have et : (-Int.negSucc k).toNat - 1 = k := rfl
      rw [et]
      exact mulK_rep hsz (invK_rep (hg k hk2) (hp k hk2)) ih

theorem toTable_eq_arrTable_of_img {g : Equiv.Perm (Fin n)} {P : Nat}
    (h : imageList g = (unpack n w P).toList) : toTable g = arrTable n (unpack n w P) := by
  unfold toTable arrTable
  congr 1
  funext i
  have hs : (unpack n w P).size = n := by simp [unpack]
  have hi : i.val < (unpack n w P).size := by rw [hs]; exact i.isLt
  have hl : i.val < (imageList g).length := by simp [imageList]
  have e := List.getElem_of_eq h hl
  simp only [imageList, List.getElem_ofFn, Array.getElem_toList, Fin.eta] at e
  rw [getElem!_pos (unpack n w P) i.val hi, ← e]

theorem repsOK_of_img {g N cap : Nat} {gs reps : List (Equiv.Perm (Fin n))}
    {X : List Table} {GP GIP CI E P L K S SI : Nat → Nat} {CS OFF : List Nat}
    (hgl : gs.length = g)
    (hg : ∀ j < g, imageList (gs.getD j 1) = (unpack n w (GP j)).toList)
    (hp : ∀ j < g, permOK n w (mask w) (n * w) (GP j) (GIP j) = true)
    (hgc : ∀ l < g, canonK n w (mask w) (n * w) (GP l) = true ∧
      canonK n w (mask w) (n * w) (GIP l) = true)
    (hr : reps.length = CS.length)
    (hri : ∀ i < CS.length, imageList (reps.getD i 1) = (unpack n w (E (lget OFF i))).toList)
    (hoff : offOK CS OFF N = true) (hpos : CFSG.KC.J2Cover.allL (fun c => Nat.blt 0 c) CS = true)
    (hx : X.length = N)
    (h : ∀ j < N, repK n w GP GIP g CS OFF CI E P L K S SI N cap j = true) :
    repsOK n (gs.map toTable).toArray ((gs.map (·⁻¹)).map toTable).toArray X (reps.map toTable)
        cap = true ∧
      repSizes n (gs.map toTable).toArray ((gs.map (·⁻¹)).map toTable).toArray
        (reps.map toTable) cap = CS := by
  have hgt : ∀ l < g, ((gs.map toTable).toArray)[l]! = arrTable n (unpack n w (GP l)) ∧
      (((gs.map (·⁻¹)).map toTable).toArray)[l]! = arrTable n (unpack n w (GIP l)) := by
    intro l hl
    have hl' : l < gs.length := hgl ▸ hl
    have e1 : ((gs.map toTable).toArray)[l]! = toTable (gs.getD l 1) := by
      rw [List.getD_eq_getElem _ _ hl', getElem!_pos _ _ (by simpa using hl')]
      simp
    have e2 : (((gs.map (·⁻¹)).map toTable).toArray)[l]! = toTable (gs.getD l 1)⁻¹ := by
      rw [List.getD_eq_getElem _ _ hl', getElem!_pos _ _ (by simpa using hl')]
      simp
    rw [e1, e2]
    exact ⟨toTable_eq_arrTable_of_img (hg l hl),
      toTable_eq_arrTable_of_img (invK_rep (hg l hl) (hp l hl))⟩
  have hgs : (gs.map toTable).toArray.size = g ∧ ((gs.map (·⁻¹)).map toTable).toArray.size = g ∧
      ∀ l < g, ((gs.map toTable).toArray)[l]! = arrTable n (unpack n w (GP l)) ∧
        (((gs.map (·⁻¹)).map toTable).toArray)[l]! = arrTable n (unpack n w (GIP l)) :=
    ⟨by simp [hgl], by simp [hgl], hgt⟩
  have hreps : reps.map toTable =
      (List.range CS.length).map fun i => arrTable n (unpack n w (E (lget OFF i))) := by
    apply List.ext_getElem
    · simp [hr]
    · intro i h1 h2
      have hi : i < CS.length := by simpa using h2
      have hi' : i < reps.length := hr ▸ hi
      have e := toTable_eq_arrTable_of_img (hri i hi)
      rw [List.getD_eq_getElem _ _ hi'] at e
      simp [e]
  exact ⟨repsOK_sound hgs hgc hreps hoff hpos hx h, repSizes_sound hgs hgc hreps hoff hpos h⟩

end CFSG.KS.SporSch.CodesImg

end
