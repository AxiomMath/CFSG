module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.AutETableSound

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open AutETable

@[expose] def autECheck (n : ℕ) (mul : ℕ → ℕ → ℕ) : Bool :=
  let M := tab2 n mul
  let gw := mkGens n M
  autChk n M gw.1 (gw.2.map fun o => o.getD [])

theorem autEFact_of_table {H : Type*} [Group H] {n : ℕ} {elt : ℕ → H} {mul : ℕ → ℕ → ℕ}
    (hlt : ∀ a b, a < n → b < n → mul a b < n)
    (hmul : ∀ a b, a < n → b < n → elt (mul a b) = elt a * elt b)
    (hinj : ∀ a b, a < n → b < n → elt a = elt b → a = b)
    (hsurj : ∀ h : H, ∃ a < n, elt a = h) (h0 : elt 0 = 1) (hn : 0 < n)
    (hchk : autECheck n mul = true) : AutEFact H :=
  autEFact_of_chk (M := tab2 n mul) (elt := elt)
    ⟨hn, fun a b ha hb => by rw [mt_tab2 mul ha hb]; exact hlt a b ha hb,
      fun a b ha hb => by rw [mt_tab2 mul ha hb]; exact hmul a b ha hb, hinj, hsurj, h0⟩ hchk

end CFSG.EvenSporadicStandard.Fin76b
