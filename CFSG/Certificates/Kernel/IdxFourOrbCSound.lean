module

public import Certificates.Data.Kernel.IdxFourOrbCK
public import CFSG.Certificates.Kernel.IdxFourReachSound

public section

namespace CFSG.KC.IF4V

open CFSG.KC.IF4C CFSG.KC.IF4O CFSG.KC.IF4L CFSG.KC.IF4W CFSG.GF2Type.Smith1979.GammaU
open CFSG.GF2Type.Smith1979.IdxFour

theorem o1701K_eq (n : Nat) : o1701K n = Orb.inO1701b n := by
  simp only [o1701K, Orb.inO1701b, nbeq, wtK_eq, peK_eq, bne]

theorem inCK_eq (n : Nat) : inCK n = (Orb.inO1701b n && !f0b n 3) := by
  rw [inCK, o1701K_eq, CFSG.KC.IF4T.f0K_eq]

theorem cntBelow_eq (f : Nat → Bool) :
    ∀ n, cntBelow n f = ((Finset.range n).filter fun k => f k = true).card
  | 0 => rfl
  | n + 1 => by
    have ih := cntBelow_eq f n
    change (bif f n then Nat.succ (cntBelow n f) else cntBelow n f) = _
    rw [Finset.range_add_one, Finset.filter_insert, ih]
    cases h : f n
    · rfl
    · rw [if_pos rfl, Finset.card_insert_of_notMem (by simp)]
      rfl

theorem ncard_orbit_of_orbCOK {G D L : Nat} {K : Subgroup (V12 ≃ₗ[ZMod 2] V12)}
    (hT : orbCOK G D L = true) (hG : ∀ g < 2, ∃ U ∈ K, IsP U (look G g)) (v : V12)
    (hv : inCK (codeOf v) = true) : 64 ≤ Set.ncard {u : V12 | ∃ U ∈ K, U v = u} := by
  have hi : labK L (codeOf v) < 4 := Nat.lt_succ_of_le Nat.and_le_right
  set i := labK L (codeOf v)
  have hO := (allBelow_iff 4 _).1 hT i hi
  simp only [orbCi, Bool.and_eq_true, Nat.ble_eq] at hO
  obtain ⟨hR, hc⟩ := hO
  have hreach := reach_of_reachOK hR hG
  have hpv : predK L i (codeOf v) = true := by simp [predK, hv, i]
  obtain ⟨U₀, hU₀, hU₀v⟩ := hreach _ (codeOf_lt v) hpv
  rw [vecOf_codeOf] at hU₀v
  set S := (Finset.range 4096).filter fun k => predK L i k = true
  have hS : 64 ≤ S.card := cntBelow_eq _ 4096 ▸ hc
  have hlt : ∀ m ∈ S, m < 4096 := fun m hm => Finset.mem_range.1 (Finset.mem_filter.1 hm).1
  have hinj : Set.InjOn vecOf (↑S : Set ℕ) := fun a ha b hb h => vecOf_inj (hlt a ha) (hlt b hb) h
  have hsub : (↑(S.image vecOf) : Set V12) ⊆ {u : V12 | ∃ U ∈ K, U v = u} := by
    intro u hu
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hu
    obtain ⟨W, hW, hWm⟩ := hreach m (hlt m hm) (Finset.mem_filter.1 hm).2
    refine ⟨W * U₀⁻¹, mul_mem hW (inv_mem hU₀), ?_⟩
    rw [LinearEquiv.mul_apply, ← hU₀v, ← hWm]
    simp
  calc 64 ≤ S.card := hS
    _ = (S.image vecOf).card := (Finset.card_image_of_injOn hinj).symm
    _ = (↑(S.image vecOf) : Set V12).ncard := (Set.ncard_coe_finset _).symm
    _ ≤ _ := Set.ncard_le_ncard hsub (Set.toFinite _)

end CFSG.KC.IF4V

end
