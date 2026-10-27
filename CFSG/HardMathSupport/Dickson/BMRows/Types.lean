module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporRows
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1415ASporRows
public import CFSG.LocalAnalysis.GLTheoremA.CatA.SporAltSporRows
import CFSG.HardMathSupport.Dickson.BMRows.TypesHSOrd
import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporThreeSmall

public section

namespace CFSG.HardMathSupport.Dickson.BMRows

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.HardMathSupport.Solomon.Coordinator (SporadicOrdersTable LieOrderBridge sporOrd)

theorem card_of_catalogIs_sporadic (hOrd : SporadicOrdersTable) {T : Type} [Group T]
    {s : TauCeti.SporadicName} (h : catalogIs T (· = .sporadic s)) : Nat.card T = sporOrd s := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  obtain rfl : i = .sporadic s := hi
  exact (Nat.card_congr e.toEquiv).trans (hOrd s)

theorem kLevel_le_two_of_catalogIs {p : ℕ} {T : Type} [Group T] {P : TauCeti.CFSGIndex → Prop}
    (h : catalogIs T P) (hP : ∀ i, P i → k2 p i) : kLevel p T ≤ 2 := by
  obtain ⟨i, hi, he⟩ := h
  have h2 : catalogIs T (k2 p) := ⟨i, hP i hi, he⟩
  unfold kLevel
  split_ifs with h1 h3 h4 <;> first | omega | exact absurd h2 h3

theorem notL227_of_card {T : Type} [Group T] (hc : Nat.card T ≠ 9828) :
    ¬ catalogIs T (onLie (isL2 27)) :=
  fun hL => hc (card_of_catalogIs_L227 hL)

theorem qtypeOK_of_card_all (hb : LieOrderBridge) {p : ℕ} {T : Type} [Group T] [Finite T] {N : ℕ}
    (hT : Nat.card T = N) (hN0 : 0 < N) (hNlt : N < 2 ^ 200)
    (hN : ∀ q ∈ N.primeFactorsList, q ≠ 2 → ∀ k < 200, q ^ k ∣ N → q ^ (3 * k) ≤ N)
    (h3 : N ≠ 360 ∧ N ≠ 504 ∧ N ≠ 25920) (h5 : N ≠ 60) : I1416QRows.QTypeOK p T :=
  I1416QRows.qtypeOK_of_card hb hT hN0 hNlt (fun q hq h2 _ => hN q hq h2) (fun _ => h3)
    (fun _ => h5)

theorem card_of_catalogIs_Fi22 (hOrd : SporadicOrdersTable) {T : Type} [Group T]
    (h : catalogIs T (· = .sporadic .Fi22)) : Nat.card T = 64561751654400 :=
  (card_of_catalogIs_sporadic hOrd h).trans (by norm_num [sporOrd])

theorem card_of_catalogIs_HS (hOrd : SporadicOrdersTable) {T : Type} [Group T]
    (h : catalogIs T (· = .sporadic .HS)) : Nat.card T = 44352000 :=
  (card_of_catalogIs_sporadic hOrd h).trans (by norm_num [sporOrd])

theorem card_of_catalogIs_He (hOrd : SporadicOrdersTable) {T : Type} [Group T]
    (h : catalogIs T (· = .sporadic .He)) : Nat.card T = 4030387200 :=
  (card_of_catalogIs_sporadic hOrd h).trans (by norm_num [sporOrd])

theorem card_of_catalogIs_HN (hOrd : SporadicOrdersTable) {T : Type} [Group T]
    (h : catalogIs T (· = .sporadic .HN)) : Nat.card T = 273030912000000 :=
  (card_of_catalogIs_sporadic hOrd h).trans (by norm_num [sporOrd, orderHN])

theorem card_of_catalogIs_Th (hOrd : SporadicOrdersTable) {T : Type} [Group T]
    (h : catalogIs T (· = .sporadic .Th)) : Nat.card T = 90745943887872000 :=
  (card_of_catalogIs_sporadic hOrd h).trans (by norm_num [sporOrd, orderTh])

theorem card_of_catalogIs_Fi24Prime (hOrd : SporadicOrdersTable) {T : Type} [Group T]
    (h : catalogIs T (· = .sporadic .Fi24Prime)) : Nat.card T = 1255205709190661721292800 :=
  (card_of_catalogIs_sporadic hOrd h).trans (by norm_num [sporOrd, orderFi24Prime])

theorem not_isChevSimple_of_card_fi22 (hb : LieOrderBridge) {T : Type} [Group T] [Finite T]
    (hc : Nat.card T = 64561751654400) (q : ℕ) : ¬ IsChevSimple q T :=
  I1416QRows.not_isChevSimple_of_not_lieOrder hb hc
    (fun _ hd => CFSG.HardMathSupport.Solomon.Coordinator.I1420.lieOrderFormula_ne_fi22Ord hd)
    (by norm_num) (by norm_num) (by norm_num) q

theorem not_isChevSimple_of_card_hs (hb : LieOrderBridge) {T : Type} [Group T] [Finite T]
    (hc : Nat.card T = 44352000) (q : ℕ) : ¬ IsChevSimple q T :=
  I1416QRows.not_isChevSimple_of_not_lieOrder hb hc
    (fun _ hd => HSLie.lieOrderFormula_ne_hsOrd hd) (by norm_num) (by norm_num) (by norm_num) q

theorem typeOK_of_card_fi22 (hb : LieOrderBridge) {p : ℕ} {T : Type} [Group T]
    (hc : Nat.card T = 64561751654400) : I1416Rows.TypeOK p T := by
  have : Finite T := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  exact I1416Rows.typeOK_of_not_chev (not_isChevSimple_of_card_fi22 hb hc 2)

theorem qtypeOK_of_card_fi22 (hb : LieOrderBridge) {p : ℕ} {T : Type} [Group T]
    (hc : Nat.card T = 64561751654400) : I1416QRows.QTypeOK p T := by
  have : Finite T := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  exact I1416QRows.qtypeOK_of_not_chev fun q _ _ _ => not_isChevSimple_of_card_fi22 hb hc q

theorem typeOK_of_card_hs (hb : LieOrderBridge) {p : ℕ} {T : Type} [Group T]
    (hc : Nat.card T = 44352000) : I1416Rows.TypeOK p T := by
  have : Finite T := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  exact I1416Rows.typeOK_of_not_chev (not_isChevSimple_of_card_hs hb hc 2)

theorem qtypeOK_of_card_hs (hb : LieOrderBridge) {p : ℕ} {T : Type} [Group T]
    (hc : Nat.card T = 44352000) : I1416QRows.QTypeOK p T := by
  have : Finite T := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  exact I1416QRows.qtypeOK_of_not_chev fun q _ _ _ => not_isChevSimple_of_card_hs hb hc q

theorem typeOK_of_card_he (hb : LieOrderBridge) {p : ℕ} {T : Type} [Group T]
    (hc : Nat.card T = 4030387200) : I1416Rows.TypeOK p T := by
  have : Finite T := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  exact I1416Rows.typeOK_of_not_chev (I1416Rows.not_isChevSimple_two_of_card hb (a := 10)
    (m := 3935925) (hc.trans (by norm_num)) (Nat.odd_iff.2 (by norm_num)) (by norm_num)
    (by norm_num))

theorem qtypeOK_of_card_he (hb : LieOrderBridge) {p : ℕ} {T : Type} [Group T]
    (hc : Nat.card T = 4030387200) : I1416QRows.QTypeOK p T := by
  have : Finite T := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  exact qtypeOK_of_card_all hb hc (by norm_num) (by norm_num)
    (by simp only [Nat.primeFactorsList_ofNat]; decide +kernel) (by norm_num) (by norm_num)

theorem typeOK_of_card_hn (hb : LieOrderBridge) {p : ℕ} {T : Type} [Group T]
    (hc : Nat.card T = 273030912000000) : I1416Rows.TypeOK p T := by
  have : Finite T := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  exact I1416Rows.typeOK_of_not_chev (I1416Rows.not_isChevSimple_two_of_card hb (a := 14)
    (m := 16664484375) (hc.trans (by norm_num)) (Nat.odd_iff.2 (by norm_num)) (by norm_num)
    (by norm_num))

theorem qtypeOK_of_card_hn (hb : LieOrderBridge) {p : ℕ} {T : Type} [Group T]
    (hc : Nat.card T = 273030912000000) : I1416QRows.QTypeOK p T := by
  have : Finite T := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  exact qtypeOK_of_card_all hb hc (by norm_num) (by norm_num)
    (by simp only [Nat.primeFactorsList_ofNat]; decide +kernel) (by norm_num) (by norm_num)

theorem typeOK_of_card_th (hb : LieOrderBridge) {p : ℕ} {T : Type} [Group T]
    (hc : Nat.card T = 90745943887872000) : I1416Rows.TypeOK p T := by
  have : Finite T := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  exact I1416Rows.typeOK_of_not_chev (I1416Rows.not_isChevSimple_two_of_card hb (a := 15)
    (m := 2769346432125) (hc.trans (by norm_num)) (Nat.odd_iff.2 (by norm_num)) (by norm_num)
    (by norm_num))

theorem qtypeOK_of_card_th (hb : LieOrderBridge) {p : ℕ} {T : Type} [Group T]
    (hc : Nat.card T = 90745943887872000) : I1416QRows.QTypeOK p T := by
  have : Finite T := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  exact qtypeOK_of_card_all hb hc (by norm_num) (by norm_num)
    (by simp only [Nat.primeFactorsList_ofNat]; decide +kernel) (by norm_num) (by norm_num)

theorem typeOK_of_card_fi24Prime (hb : LieOrderBridge) {p : ℕ} {T : Type} [Group T]
    (hc : Nat.card T = 1255205709190661721292800) : I1416Rows.TypeOK p T := by
  have : Finite T := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  exact I1416Rows.typeOK_of_not_chev (I1416Rows.not_isChevSimple_two_of_card hb (a := 21)
    (m := 598528723330813275) (hc.trans (by norm_num)) (Nat.odd_iff.2 (by norm_num))
    (by norm_num) (by norm_num))

theorem qtypeOK_of_card_fi24Prime (hb : LieOrderBridge) {p : ℕ} {T : Type} [Group T]
    (hc : Nat.card T = 1255205709190661721292800) : I1416QRows.QTypeOK p T := by
  have : Finite T := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  exact qtypeOK_of_card_all hb hc (by norm_num) (by norm_num)
    (by simp only [Nat.primeFactorsList_ofNat]; decide +kernel) (by norm_num) (by norm_num)

theorem typeOK_B3 (hOrd : SporadicOrdersTable) (hb : LieOrderBridge) {p : ℕ} :
    ∀ (T : Type) [Group T], catalogIs T (· = .sporadic .Fi22) → I1416Rows.TypeOK p T :=
  fun _ _ h => typeOK_of_card_fi22 hb (card_of_catalogIs_Fi22 hOrd h)

theorem qtypeOK_B3 (hOrd : SporadicOrdersTable) (hb : LieOrderBridge) {p : ℕ} :
    ∀ (T : Type) [Group T], catalogIs T (· = .sporadic .Fi22) → I1416QRows.QTypeOK p T :=
  fun _ _ h => qtypeOK_of_card_fi22 hb (card_of_catalogIs_Fi22 hOrd h)

theorem atypeOK_B3 (hOrd : SporadicOrdersTable) {p : ℕ} :
    ∀ (T : Type) [Group T], catalogIs T (· = .sporadic .Fi22) → I1415Rows.ATypeOK p T :=
  fun _ _ h => I1415Rows.atypeOK_of_card_eq (card_of_catalogIs_Fi22 hOrd h)

theorem stypeOK_B3 (hOrd : SporadicOrdersTable) {p : ℕ} :
    ∀ (T : Type) [Group T], catalogIs T (· = .sporadic .Fi22) → SporAltRows.STypeOK p T :=
  fun _ _ h => SporAltRows.stypeOK_of_card_eq (card_of_catalogIs_Fi22 hOrd h)

theorem kLevel_B3 :
    ∀ (T : Type) [Group T], catalogIs T (· = .sporadic .Fi22) → kLevel 3 T ≤ 2 :=
  fun _ _ h => kLevel_le_two_of_catalogIs h (by rintro i rfl; exact rfl)

theorem notL227_B3 (hOrd : SporadicOrdersTable) :
    ∀ (T : Type) [Group T], catalogIs T (· = .sporadic .Fi22) →
      ¬ catalogIs T (onLie (isL2 27)) :=
  fun _ _ h => notL227_of_card (by rw [card_of_catalogIs_Fi22 hOrd h]; norm_num)

theorem typeOK_B5 (hOrd : SporadicOrdersTable) (hb : LieOrderBridge) {p : ℕ} :
    ∀ (T : Type) [Group T], catalogIs T (· = .sporadic .HS) → I1416Rows.TypeOK p T :=
  fun _ _ h => typeOK_of_card_hs hb (card_of_catalogIs_HS hOrd h)

theorem qtypeOK_B5 (hOrd : SporadicOrdersTable) (hb : LieOrderBridge) {p : ℕ} :
    ∀ (T : Type) [Group T], catalogIs T (· = .sporadic .HS) → I1416QRows.QTypeOK p T :=
  fun _ _ h => qtypeOK_of_card_hs hb (card_of_catalogIs_HS hOrd h)

theorem atypeOK_B5 (hOrd : SporadicOrdersTable) {p : ℕ} :
    ∀ (T : Type) [Group T], catalogIs T (· = .sporadic .HS) → I1415Rows.ATypeOK p T :=
  fun _ _ h => I1415Rows.atypeOK_of_card_eq (card_of_catalogIs_HS hOrd h)

theorem kLevel_B5 :
    ∀ (T : Type) [Group T], catalogIs T (· = .sporadic .HS) → kLevel 5 T ≤ 2 :=
  fun _ _ h => kLevel_le_two_of_catalogIs h (by rintro i rfl; exact rfl)

theorem typeOK_M3 (hOrd : SporadicOrdersTable) (hb : LieOrderBridge) {p : ℕ} :
    ∀ (T : Type) [Group T],
      catalogIs T (fun i => i = .sporadic .Fi24Prime ∨ i = .sporadic .Th) →
        I1416Rows.TypeOK p T := by
  rintro T _ ⟨i, hi | hi, he⟩
  · exact typeOK_of_card_fi24Prime hb (card_of_catalogIs_Fi24Prime hOrd ⟨i, hi, he⟩)
  · exact typeOK_of_card_th hb (card_of_catalogIs_Th hOrd ⟨i, hi, he⟩)

theorem qtypeOK_M3 (hOrd : SporadicOrdersTable) (hb : LieOrderBridge) {p : ℕ} :
    ∀ (T : Type) [Group T],
      catalogIs T (fun i => i = .sporadic .Fi24Prime ∨ i = .sporadic .Th) →
        I1416QRows.QTypeOK p T := by
  rintro T _ ⟨i, hi | hi, he⟩
  · exact qtypeOK_of_card_fi24Prime hb (card_of_catalogIs_Fi24Prime hOrd ⟨i, hi, he⟩)
  · exact qtypeOK_of_card_th hb (card_of_catalogIs_Th hOrd ⟨i, hi, he⟩)

theorem atypeOK_M3 (hOrd : SporadicOrdersTable) {p : ℕ} :
    ∀ (T : Type) [Group T],
      catalogIs T (fun i => i = .sporadic .Fi24Prime ∨ i = .sporadic .Th) →
        I1415Rows.ATypeOK p T := by
  rintro T _ ⟨i, hi | hi, he⟩
  · exact I1415Rows.atypeOK_of_card_eq (card_of_catalogIs_Fi24Prime hOrd ⟨i, hi, he⟩)
  · exact I1415Rows.atypeOK_of_card_eq (card_of_catalogIs_Th hOrd ⟨i, hi, he⟩)

theorem stypeOK_M3 (hOrd : SporadicOrdersTable) {p : ℕ} :
    ∀ (T : Type) [Group T],
      catalogIs T (fun i => i = .sporadic .Fi24Prime ∨ i = .sporadic .Th) →
        SporAltRows.STypeOK p T := by
  rintro T _ ⟨i, hi | hi, he⟩
  · exact SporAltRows.stypeOK_of_card_eq (card_of_catalogIs_Fi24Prime hOrd ⟨i, hi, he⟩)
  · exact SporAltRows.stypeOK_of_card_eq (card_of_catalogIs_Th hOrd ⟨i, hi, he⟩)

theorem kLevel_M3 :
    ∀ (T : Type) [Group T],
      catalogIs T (fun i => i = .sporadic .Fi24Prime ∨ i = .sporadic .Th) → kLevel 3 T ≤ 2 :=
  fun _ _ h => kLevel_le_two_of_catalogIs h (by rintro i (rfl | rfl) <;> exact Or.inl rfl)

theorem notL227_M3 (hOrd : SporadicOrdersTable) :
    ∀ (T : Type) [Group T],
      catalogIs T (fun i => i = .sporadic .Fi24Prime ∨ i = .sporadic .Th) →
        ¬ catalogIs T (onLie (isL2 27)) := by
  rintro T _ ⟨i, hi | hi, he⟩
  · exact notL227_of_card (by rw [card_of_catalogIs_Fi24Prime hOrd ⟨i, hi, he⟩]; norm_num)
  · exact notL227_of_card (by rw [card_of_catalogIs_Th hOrd ⟨i, hi, he⟩]; norm_num)

theorem typeOK_M5 (hOrd : SporadicOrdersTable) (hb : LieOrderBridge) {p : ℕ} :
    ∀ (T : Type) [Group T], catalogIs T (· = .sporadic .HN) → I1416Rows.TypeOK p T :=
  fun _ _ h => typeOK_of_card_hn hb (card_of_catalogIs_HN hOrd h)

theorem qtypeOK_M5 (hOrd : SporadicOrdersTable) (hb : LieOrderBridge) {p : ℕ} :
    ∀ (T : Type) [Group T], catalogIs T (· = .sporadic .HN) → I1416QRows.QTypeOK p T :=
  fun _ _ h => qtypeOK_of_card_hn hb (card_of_catalogIs_HN hOrd h)

theorem atypeOK_M5 (hOrd : SporadicOrdersTable) {p : ℕ} :
    ∀ (T : Type) [Group T], catalogIs T (· = .sporadic .HN) → I1415Rows.ATypeOK p T :=
  fun _ _ h => I1415Rows.atypeOK_of_card_eq (card_of_catalogIs_HN hOrd h)

theorem kLevel_M5 :
    ∀ (T : Type) [Group T], catalogIs T (· = .sporadic .HN) → kLevel 5 T ≤ 2 :=
  fun _ _ h => kLevel_le_two_of_catalogIs h (by rintro i rfl; exact rfl)

theorem typeOK_M7 (hOrd : SporadicOrdersTable) (hb : LieOrderBridge) {p : ℕ} :
    ∀ (T : Type) [Group T], catalogIs T (· = .sporadic .He) → I1416Rows.TypeOK p T :=
  fun _ _ h => typeOK_of_card_he hb (card_of_catalogIs_He hOrd h)

theorem qtypeOK_M7 (hOrd : SporadicOrdersTable) (hb : LieOrderBridge) {p : ℕ} :
    ∀ (T : Type) [Group T], catalogIs T (· = .sporadic .He) → I1416QRows.QTypeOK p T :=
  fun _ _ h => qtypeOK_of_card_he hb (card_of_catalogIs_He hOrd h)

theorem atypeOK_M7 (hOrd : SporadicOrdersTable) {p : ℕ} :
    ∀ (T : Type) [Group T], catalogIs T (· = .sporadic .He) → I1415Rows.ATypeOK p T :=
  fun _ _ h => I1415Rows.atypeOK_of_card_eq (card_of_catalogIs_He hOrd h)

theorem kLevel_M7 :
    ∀ (T : Type) [Group T], catalogIs T (· = .sporadic .He) → kLevel 7 T ≤ 2 :=
  fun _ _ h => kLevel_le_two_of_catalogIs h (by rintro i rfl; exact rfl)

end CFSG.HardMathSupport.Dickson.BMRows
