module

public import Certificates.Data.Kernel.Misc.G24P0
public import CFSG.Certificates.Kernel.Misc.G24Sound
public import CFSG.Certificates.Kernel.Misc.Spec.F2Blow
import CFSG.Certificates.Kernel.Misc.Spec.RowsArr
import CFSG.Certificates.Kernel.Spor.PK.MiscBase

public section

namespace CFSG.KC.Misc.G24

open CFSG.LieType.Multipliers.G24 CFSG.Fischer CFSG.KC.Misc.Spec

@[expose] def g24Mat (GR : List (List (List Nat))) (w : List (Fin 6 × Bool)) :
    Matrix (Fin 14) (Fin 14) F4 :=
  toMat 14 (wordArrOf (genArrsOf (GR.map (List.map strOf))) w)

private theorem asciiK_iff' {rs : List (List ℕ)} :
    asciiK rs = true ↔ ∀ r ∈ rs, ∀ c ∈ r, c < 128 := by
  unfold asciiK
  rw [CFSG.KS.PK.allLL_iff]
  refine forall_congr' fun r => forall_congr' fun _ => ?_
  rw [CFSG.KS.PK.allL_lqt_iff]
  simp only [Nat.blt_eq]

private theorem digitsOf_eq' (rs : List (List ℕ)) :
    digitsOf rs = rs.map (List.map fun c => (c - 48) % 4) := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    show _ :: digitsOf rs = _
    rw [ih]
    refine congrArg₂ List.cons ?_ rfl
    induction r with
    | nil => rfl
    | cons c r ihr =>
      show _ :: _ = _ :: _
      rw [ihr]
      rfl

private theorem toNat_ofNat_lt' {c : ℕ} (hc : c < 128) : (Char.ofNat c).toNat = c := by
  rw [Char.toNat_ofNat, if_pos]
  exact Or.inl (by omega)

private theorem toMat_rowsArr_f4 {rows : List (List ℕ)} (ha : asciiK rows = true)
    (hs : shape4 (digitsOf rows) = true) :
    toMat 14 (rowsArr f4Digit rows) = digMat (digitsOf rows) := by
  obtain ⟨h1, h2⟩ := (shape4_iff _).1 hs
  rw [digitsOf_eq'] at h1 h2
  have hrow : ∀ r ∈ rows, r.length = 14 := fun r hr => by
    have := (h2 (r.map fun c => (c - 48) % 4) (List.mem_map_of_mem hr)).1
    simpa using this
  have hlen : rows.length = 14 := by simpa using h1
  have hascii := asciiK_iff'.1 ha
  have hmem : ∀ i < 14, rows.getD i [] ∈ rows := by
    intro i hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    simp
  ext i j
  have hi : i.val < 14 := i.isLt
  have hj : j.val < (rows.getD i.val []).length := by rw [hrow _ (hmem _ hi)]; exact j.isLt
  have e1 : toMat 14 (rowsArr f4Digit rows) i j = f4Digit (Char.ofNat
      ((rows.getD i.val []).getD j.val 0)) := by
    show ((rowsArr f4Digit rows).getD i.val #[]).getD j.val 0 = _
    exact getD_rowsArr f4Digit rows hj
  have hc : (rows.getD i.val []).getD j.val 0 < 128 :=
    hascii _ (hmem _ hi) _ (getD_mem_of_lt hj)
  have e2 : ((digitsOf rows).getD i.val []).getD j.val 0 =
      ((rows.getD i.val []).getD j.val 0 - 48) % 4 := by
    rw [digitsOf_eq']
    have : (rows.map (List.map fun c => (c - 48) % 4)).getD i.val [] =
        (rows.getD i.val []).map fun c => (c - 48) % 4 :=
      List.getD_map rows [] (n := i.val) (List.map fun c => (c - 48) % 4)
    rw [this]
    generalize rows.getD i.val [] = r at hj ⊢
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  rw [e1]
  show _ = (⟨⟨((digitsOf rows).getD i.val []).getD j.val 0 % 4, _⟩⟩ : F4)
  unfold f4Digit
  congr 1
  refine Fin.ext ?_
  simp only [e2, toNat_ofNat_lt' hc]
  omega

private theorem genArrsOf_getD' (GR : List (List (List ℕ))) (i : ℕ) :
    (genArrsOf (GR.map (List.map strOf))).getD i #[] = rowsArr f4Digit (GR.getD i []) := by
  have h : genArrsOf (GR.map (List.map strOf)) = GR.map (rowsArr f4Digit) := by
    unfold genArrsOf
    rw [List.map_map]
    rfl
  rw [h]
  exact List.getD_map GR [] (n := i) (rowsArr f4Digit)

theorem g24F4_word {GR : List (List (List Nat))} {Gb : List Nat} {RS XS YS : List (List Nat)}
    {PS : List (List (List Nat × List Nat))} {XL YL : List (List (List Nat))}
    (h : g24F4K GR Gb RS PS XS YS XL YL = true) (w : List (Fin 6 × Bool)) :
    pkMat 28 (wordF4 Gb (encG w)) = blowMat (g24Mat GR w) := by
  unfold g24F4K at h
  simp only [CFSG.KS.PK.andB_eq, Bool.and_eq_true, Nat.beq_eq, CFSG.KS.PK.allN_lqt_iff] at h
  obtain ⟨-, hgen, -⟩ := h
  set gs := genArrsOf (GR.map (List.map strOf)) with hgs
  have hG : ∀ i < 6, pkMat 28 (Gb.getD i 0) = blowMat (toMat 14 (gs.getD i #[])) := by
    intro i hi
    obtain ⟨⟨ha, hs⟩, hb⟩ := hgen i hi
    rw [hgs, genArrsOf_getD', ← nthLL_eq, toMat_rowsArr_f4 ha hs, ← nthV_eq, ← hb, pkMat_blow14 hs]
  rw [pkMat_wordF4 hG w, g24Mat]
  unfold wordArrOf
  rw [show one14 = ofMat (1 : Matrix (Fin 14) (Fin 14) F4) from rfl, foldr_mulArr, toMat_ofMat]

theorem eq_of_pkMat_eq {n x y : ℕ} (hx : x < 2 ^ (n * n)) (hy : y < 2 ^ (n * n))
    (h : pkMat n x = pkMat n y) : x = y := by
  apply Nat.eq_of_testBit_eq
  intro q
  by_cases hq : q < n * n
  · have hn : 0 < n := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hq
    have hi : q / n < n := Nat.div_lt_of_lt_mul hq
    have hj : q % n < n := Nat.mod_lt _ hn
    have e := congrFun (congrFun h ⟨q / n, hi⟩) ⟨q % n, hj⟩
    simp only [pkMat, Matrix.of_apply, Nat.div_add_mod] at e
    cases hxq : x.testBit q <;> cases hyq : y.testBit q <;> simp_all
  · have hle : 2 ^ (n * n) ≤ 2 ^ q := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hx hle),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hy hle)]

theorem g24P0_sound {GR : List (List (List Nat))} {Gb : List Nat} {RS XS YS : List (List Nat)}
    {PS : List (List (List Nat × List Nat))} {XL YL : List (List (List Nat))}
    {p1 p2 zx zy : List Nat} (h44 : g24F4K GR Gb RS PS XS YS XL YL = true)
    (h : g24P0K Gb p1 p2 zx zy = true) :
    g24Mat GR (parseWord (strOf p1)) ^ 3 = 1 ∧ g24Mat GR (parseWord (strOf p2)) ^ 3 = 1 ∧
      g24Mat GR (parseWord (strOf p1)) * g24Mat GR (parseWord (strOf p2)) *
        g24Mat GR (parseWord (strOf p1)) ^ 2 * g24Mat GR (parseWord (strOf p2)) ^ 2 =
          g24Mat GR (parseWord (strOf zx) ++ parseWord (strOf zy)) ∧
      g24Mat GR (parseWord (strOf zx) ++ parseWord (strOf zy)) *
          g24Mat GR (parseWord (strOf p1)) =
        g24Mat GR (parseWord (strOf p1)) *
          g24Mat GR (parseWord (strOf zx) ++ parseWord (strOf zy)) ∧
      g24Mat GR (parseWord (strOf zx) ++ parseWord (strOf zy)) *
          g24Mat GR (parseWord (strOf p2)) =
        g24Mat GR (parseWord (strOf p2)) *
          g24Mat GR (parseWord (strOf zx) ++ parseWord (strOf zy)) ∧
      g24Mat GR (parseWord (strOf zx) ++ parseWord (strOf zy)) ≠ 1 := by
  set P1 := g24Mat GR (parseWord (strOf p1))
  set P2 := g24Mat GR (parseWord (strOf p2))
  set Z := g24Mat GR (parseWord (strOf zx) ++ parseWord (strOf zy))
  have e1 : pkMat 28 (wordF4 Gb (parseK p1)) = blowMat P1 := by
    rw [parseK_eq]
    exact g24F4_word h44 _
  have e2 : pkMat 28 (wordF4 Gb (parseK p2)) = blowMat P2 := by
    rw [parseK_eq]
    exact g24F4_word h44 _
  have eZ : pkMat 28 (wordF4 Gb (appN (parseK zx) (parseK zy))) = blowMat Z := by
    rw [appN_eq, parseK_eq, parseK_eq, encG, encG, ← List.map_append]
    exact g24F4_word h44 (parseWord (strOf zx) ++ parseWord (strOf zy))
  have eI : pkMat 28 (oneF2 28) = blowMat 1 := by rw [pkMat_oneF2, blowMat_one]
  have em : ∀ {X Y : ℕ} {A B : Matrix (Fin 14) (Fin 14) F4}, pkMat 28 X = blowMat A →
      pkMat 28 Y = blowMat B → pkMat 28 (mulF2 28 X Y) = blowMat (A * B) := by
    intro X Y A B hX hY
    rw [pkMat_mulF2, hX, hY, blowMat_mul]
  have eq : ∀ {X Y : ℕ} {A B : Matrix (Fin 14) (Fin 14) F4}, pkMat 28 X = blowMat A →
      pkMat 28 Y = blowMat B → X = Y → A = B := by
    intro X Y A B hX hY hXY
    exact blowMat_injective (by rw [← hX, ← hY, hXY])
  unfold g24P0K at h
  simp only [CFSG.KS.PK.letB_eq, CFSG.KS.PK.andB_eq, CFSG.KS.PK.notB_eq, Bool.and_eq_true,
    Nat.beq_eq, Nat.blt_eq] at h
  obtain ⟨h1, h2, h3, h4, h5, ⟨hZlt, hIlt⟩, h6⟩ := h
  have hQ1 := em e1 e1
  have hQ2 := em e2 e2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [pow_three]
    exact eq (em e1 hQ1) eI h1
  · rw [pow_three]
    exact eq (em e2 hQ2) eI h2
  · rw [sq, sq]
    exact eq (em (em (em e1 e2) hQ1) hQ2) eZ h3
  · exact eq (em eZ e1) (em e1 eZ) h4
  · exact eq (em eZ e2) (em e2 eZ) h5
  · intro hZ1
    have hf : Nat.beq (wordF4 Gb (appN (parseK zx) (parseK zy))) (oneF2 28) = false := by
      cases hb : Nat.beq (wordF4 Gb (appN (parseK zx) (parseK zy))) (oneF2 28)
      · rfl
      · rw [hb] at h6
        exact absurd h6 (by decide)
    rw [shl1_eq] at hZlt hIlt
    exact Nat.ne_of_beq_eq_false hf
      (eq_of_pkMat_eq (n := 28) hZlt hIlt (by rw [eZ, eI, hZ1]))

end CFSG.KC.Misc.G24

end
