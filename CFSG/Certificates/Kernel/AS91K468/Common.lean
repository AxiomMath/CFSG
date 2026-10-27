module

public import Certificates.Data.Kernel.AS91K468.K47
public import CFSG.Certificates.Kernel.HJ12KTSound
public import CFSG.GF2Type.Smith1979.GammaU.PairBridge
public import CFSG.Quasithin.H13.AS91Sec4SevenInputs

public section

namespace Certificates.Kernel.AS91K468

open CFSG.KC.Mat12P CFSG.KC.Mat8P Certificates.Kernel.HJ12K CFSG.Quasithin.H13.AS91.Two
open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA
  CFSG.GF2Type.Smith1979.GammaU.Enum

theorem mulRS (X Y : ℕ) : mulR (unpackA X) (unpackA Y) = unpackA (mulQ X Y) := mulR_unpackA X Y

theorem appNS (X n : ℕ) : appN (unpackA X) n = mvNR (unpackQ X) n := appN_unpackA X n

theorem idRS : idR = unpackA oneQ := idR_eq

theorem enumS (gs : List ℕ) : enumGrp (gs.map unpackA) = (enumQ gs).map unpackA := by
  rw [← native_enumGrp]
  exact (enumGrp_eq gs).1

theorem enumS_lt (gs : List ℕ) : ∀ q ∈ enumQ gs, q < 2 ^ 144 := (enumGrp_eq gs).2

theorem closedS (gs X : List ℕ) (hX : ∀ q ∈ X, q < 2 ^ 144) :
    closedCheck (gs.map unpackA) (X.map unpackA) = closedQ gs X := closedCheck_eq gs X hX

theorem gensS (gs : List ℕ) (h : gensOKQ gs = true) : gensOKb (gs.map unpackA) = true :=
  gensOKN_of gs h

theorem beqS {X Y : ℕ} (hX : X < 2 ^ 144) (hY : Y < 2 ^ 144) :
    (unpackA X == unpackA Y) = Nat.beq X Y := by
  rw [beq_unpackA hX hY, nat_beq]

theorem containsS {L : List ℕ} (hL : ∀ q ∈ L, q < 2 ^ 144) {y : ℕ} (hy : y < 2 ^ 144) :
    (L.map unpackA).contains (unpackA y) = L.contains y := contains_map hL hy

theorem ofListS {L : List ℕ} (hL : ∀ q ∈ L, q < 2 ^ 144) {y : ℕ} (hy : y < 2 ^ 144) :
    (Std.HashSet.ofList (L.map unpackA)).contains (unpackA y) = L.contains y := by
  rw [Std.HashSet.contains_ofList, contains_map hL hy]

theorem dedupS {X : List ℕ} (hX : ∀ q ∈ X, q < 2 ^ 144) (n : ℕ) (h1 : nodupP X = true)
    (h2 : Nat.beq X.length n = true) : ((X.map unpackA).dedup.length == n) = true := by
  rw [dedup_length hX h1, nat_beq, h2]

theorem mulQ_lt' (X Y : ℕ) : mulQ X Y < 2 ^ 144 := mulQ_lt X Y

theorem allc {α : Type} {L : List α} {p q : α → Bool} (h : ∀ x ∈ L, p x = q x) :
    L.all p = L.all q := by
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  exact ⟨fun H x hx => (h x hx) ▸ H x hx, fun H x hx => (h x hx).symm ▸ H x hx⟩

theorem anyc {α : Type} {L : List α} {p q : α → Bool} (h : ∀ x ∈ L, p x = q x) :
    L.any p = L.any q := by
  rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
  exact ⟨fun ⟨x, hx, e⟩ => ⟨x, hx, (h x hx) ▸ e⟩, fun ⟨x, hx, e⟩ => ⟨x, hx, (h x hx).symm ▸ e⟩⟩

theorem all_mapL {α β : Type} {L : List α} {f : α → β} {p : β → Bool} {q : α → Bool}
    (h : ∀ x ∈ L, p (f x) = q x) : (L.map f).all p = L.all q := by
  rw [List.all_map]
  exact allc fun x hx => h x hx

theorem any_mapL {α β : Type} {L : List α} {f : α → β} {p : β → Bool} {q : α → Bool}
    (h : ∀ x ∈ L, p (f x) = q x) : (L.map f).any p = L.any q := by
  rw [List.any_map]
  exact anyc fun x hx => h x hx

theorem pRows_eq : pRows = pQ.map unpackA := by decide +kernel

theorem p2Rows_eq : p2Rows = p2Q.map unpackA := by decide +kernel

theorem gZRows_eq : gZRows = gZQ.map unpackA := by decide +kernel

theorem ebRows_eq : ebRows = ebQ.map unpackA := by decide +kernel

theorem iRows_eq : iRows = iQ.map unpackA := by decide +kernel

theorem fGen_eq : fGen = fGQ.map unpackA := by decide +kernel

theorem p2Q_lt : ∀ q ∈ p2Q, q < 2 ^ 144 := by decide +kernel

theorem ebQ_lt : ∀ q ∈ ebQ, q < 2 ^ 144 := by decide +kernel

theorem iQ_lt : ∀ q ∈ iQ, q < 2 ^ 144 := by decide +kernel

theorem fGQ_lt : ∀ q ∈ fGQ, q < 2 ^ 144 := by decide +kernel

theorem fRows_eq (i : ℕ) : fRows i = (fRQ i).map unpackA := by
  rw [fRows, fRQ, List.map_cons, ← iRows_eq, fGen_eq, idRS, List.getD_map]

theorem fRQ_lt (i : ℕ) : ∀ q ∈ fRQ i, q < 2 ^ 144 := by
  intro q hq
  rcases List.mem_cons.1 hq with rfl | hq
  · rw [List.getD_eq_getElem?_getD]
    rcases h : fGQ[i]? with _ | a
    · exact oneQ_lt
    · exact fGQ_lt a (List.mem_of_getElem? h)
  · exact iQ_lt q hq

theorem w1_contains (y : ℕ) : w1List.contains y = bitQ w1M y := contains_bitQ w1List y

end Certificates.Kernel.AS91K468
