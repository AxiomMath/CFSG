module

public import CFSG.Certificates.Kernel.Spor.RawOrbOutSound

public section

namespace CFSG.KS.Raw.Orb

open CFSG.KC.Enum CFSG.KS CFSG.Monster.B.Co2.Native CFSG.Monster.B.Co2
  CFSG.Certificates.Native CFSG.Certificates CFSG.Certificates.ChainArrays CFSG.KS.Raw

variable {n w kS kO nb BP NS CH : Nat} {PS PSI LR : Nat → Nat} {S : Array (Array Nat)}
  {base : Array Nat} {W : Array (List Int)} (hd : Hd n S base kO W)
  (hb : Binds n w PS kS nb BP S base)
  (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
  (ho : OrbsOK n w PS PSI LR kS nb BP NS CH) (hN : n ≤ NS * CH)
  (hcard : Nat.card (Gen n S kO) ≤ (rawOrbitSizes n S base).prod)
include hd hb hp ho hN hcard

theorem not_agree_of_outK {l : Nat} (hl : l < nb) {X : Nat} {ρ σ : Equiv.Perm (Fin n)}
    (hX : PRep n w X ρ) {iw : List Int}
    (h : outK n w (mask w) (n * w) (pidn n w) PS PSI kS BP l (LR l) iw X = true)
    (hσ : σ ∈ Gen n S kO)
    (hag : ∀ t ≤ l, ∀ hbn : base[t]! < n, σ ⟨base[t]!, hbn⟩ = ρ ⟨base[t]!, hbn⟩) : False := by
  have hb0 := hb
  obtain ⟨-, hw, hn, hS, -, -, hbt⟩ := hb0
  unfold outK at h
  rw [strictB_eq, bAnd_eq, Bool.and_eq_true, bAnd_eq, Bool.and_eq_true, strictB_eq] at h
  obtain ⟨hlet, hfix, hout⟩ := h
  have hn' : n < 16777216 := by omega
  have h32 : n < 2 ^ 32 := by omega
  obtain ⟨hW, -⟩ := prep_wordK (gs := fun h => permOfArr n S[h]!) hn' hw
    (fun h hh => (prep_PS hb hp hh).1) (fun h hh => (prep_PS hb hp hh).2) iw hlet
  set ω := Quiver.SchreierGraph.evalWord (fun h : Fin kS => permOfArr n S[(h : Nat)]!)
    (toLetters kS iw)
  have hω : ω ∈ Gen n S kO := by
    refine (Subgroup.closure_le _).2 ?_ (Quiver.SchreierGraph.evalWord_mem_closure _ _)
    rintro _ ⟨i, rfl⟩
    exact S_mem_Gen hd i.val (by rw [hS]; exact i.2)
  have hq := prep_pcomp h32 hW hX
  set q := pcomp n w (mask w) (wordK n w (mask w) (pidn n w) PS PSI iw) X
  refine not_mem_Fix_of_out hd hb hp ho hN hcard hl
    (g := ω * σ) ⟨Subgroup.mul_mem _ hω hσ, fun t ht hbn => ?_⟩ fun hbn => ?_
  · apply Fin.ext
    have e := hq ⟨base[t]!, hbn⟩
    have hf := Nat.eq_of_beq_eq_true (by
      have := allN_iff.1 hfix t ht
      rwa [strictB_eq] at this)
    rw [Equiv.Perm.mul_apply, hag t (by omega) hbn, ← Equiv.Perm.mul_apply, ← e]
    change pg w (mask w) q base[t]! = base[t]!
    rw [hbt t (by omega)]
    exact hf
  · have e := hq ⟨base[l]!, hbn⟩
    have hle := Nat.le_of_ble_eq_true hout
    rw [Equiv.Perm.mul_apply, hag l le_rfl hbn, ← Equiv.Perm.mul_apply]
    change rcnt (LR l) ≤ rpos w (mask w) (n * w) (LR l) ((ω * ρ) ⟨base[l]!, hbn⟩ : Nat)
    rw [← e]
    change rcnt (LR l) ≤ rpos w (mask w) (n * w) (LR l) (pg w (mask w) q base[l]!)
    rw [hbt l hl]
    exact hle

end CFSG.KS.Raw.Orb

end
