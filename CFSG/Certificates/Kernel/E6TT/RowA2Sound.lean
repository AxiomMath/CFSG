module

public import CFSG.Certificates.Kernel.E6TT.RowKSound
public import Certificates.Data.Kernel.E6TT.RowA2

public section

namespace CFSG.KC.E6TT

open Certificates.Data.E6TableT (Vec)
open Certificates.Data.E6TableTTwo (cosetW)

theorem rowKA2_sound {Hs : List (List Nat)} {Os : List (List (List Nat))} {b : List Vec}
    (h : rowKA2 Hs Os b = true) : rowK 0 Hs Os b = true := by
  unfold rowKA2 at h
  simp only [strictB_eqE] at h
  have hbody : rowA2Body Hs Os b [(piK Hs b).getD 0 0, (piK Hs b).getD 1 0,
      (piK Hs b).getD 2 0] (cosetW b) = true := by
    rcases bIf_cases h with ⟨hc, h1⟩ | ⟨hc, h1⟩ <;> rw [hc] <;> exact h1
  unfold rowA2Body at hbody
  obtain ⟨h3, h4⟩ := bAnd_true hbody
  obtain ⟨hp, hall⟩ := bAnd_true h4
  have hall' : (List.range 3).all (rowA2 Hs Os b [(piK Hs b).getD 0 0, (piK Hs b).getD 1 0,
      (piK Hs b).getD 2 0] (cosetW b)) = true := hall
  have hlen : Hs.length = 3 := Nat.eq_of_beq_eq_true h3
  have hπ : [(piK Hs b).getD 0 0, (piK Hs b).getD 1 0, (piK Hs b).getD 2 0] = piK Hs b := by
    have hl : (piK Hs b).length = 3 := by rw [piK, List.length_map, hlen]
    obtain ⟨a, c, d, he⟩ := List.length_eq_three.1 hl
    rw [he]
    rfl
  rw [hπ] at hp hall'
  have e : rowK 0 Hs Os b = (permK (piK Hs b) Hs.length &&
      (List.range Hs.length).all (rowA2 Hs Os b (piK Hs b) (cosetW b))) := rfl
  rw [e, Bool.and_eq_true]
  exact ⟨by rw [hlen]; exact hp, by rw [hlen]; exact hall'⟩

end CFSG.KC.E6TT

end
