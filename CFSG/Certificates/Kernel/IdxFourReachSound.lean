module

public import Certificates.Data.Kernel.IdxFourReachK
public import CFSG.Certificates.Kernel.IdxFourOrbitTreeSound
public import CFSG.Certificates.Kernel.IdxFourTcosetSound

public section

namespace CFSG.KC.IF4W

open CFSG.KC.IF4C CFSG.KC.IF4O CFSG.KC.IF4L CFSG.GF2Type.Smith1979.GammaU
open CFSG.GF2Type.Smith1979.IdxFour

theorem inOmK_eq (n : Nat) : inOmK n = Orb.inOmegab n := by
  simp only [inOmK, Orb.inOmegab, o378K_eq, CFSG.KC.IF4T.f0K_eq, nbeq, bne]

theorem reach_of_reachOK {G D r k : Nat} {P : Nat → Bool} {K : Subgroup (V12 ≃ₗ[ZMod 2] V12)}
    (hT : reachOK G D r k P = true) (hG : ∀ g < k, ∃ U ∈ K, IsP U (look G g)) :
    ∀ n < 4096, P n = true → ∃ U ∈ K, U (vecOf r) = vecOf n := by
  have hN := (allBelow_iff 4096 _).1 hT
  suffices h : ∀ d n, depT D n = d → n < 4096 → P n = true →
      ∃ U ∈ K, U (vecOf r) = vecOf n from fun n hn hs => h _ n rfl hn hs
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro n hd hn hs
  by_cases hr : n = r
  · subst hr
    exact ⟨1, one_mem _, rfl⟩
  have hnode := hN n hn
  simp only [nodeP, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', Nat.beq_eq,
    Nat.blt_eq, hs, hr] at hnode
  obtain ⟨⟨⟨hg, hp⟩, hdp⟩, he⟩ := hnode.resolve_left (by simp)
  have hplt : parT D n < 4096 := lt_of_le_of_lt (Nat.and_le_right (n := f24 D n)) (by norm_num)
  obtain ⟨U, hU, hUe⟩ := ih _ (hd ▸ hdp) (parT D n) rfl hplt hp
  obtain ⟨A, hA, hAP⟩ := hG _ hg
  refine ⟨A * U, mul_mem hA hU, ?_⟩
  rw [LinearEquiv.mul_apply, hUe, hAP.apply_code, he]

theorem exists_of_reachOK {G D r k : Nat} {P : Nat → Bool} {K : Subgroup (V12 ≃ₗ[ZMod 2] V12)}
    (hT : reachOK G D r k P = true) (hG : ∀ g < k, ∃ U ∈ K, IsP U (look G g)) (v : V12)
    (hv : P (codeOf v) = true) : ∃ U ∈ K, U (vecOf r) = v := by
  obtain ⟨U, hU, h⟩ := reach_of_reachOK hT hG _ (codeOf_lt v) hv
  rw [vecOf_codeOf] at h
  exact ⟨U, hU, h⟩

end CFSG.KC.IF4W

end
