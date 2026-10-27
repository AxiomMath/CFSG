module

public import CFSG.Certificates.Kernel.PCentExtCheck

public section

namespace CFSG.KC.PCent

open CFSG.KC.Enum (pg pcomp pidn allN)
open CFSG.KS (mask pinvS)
open CFSG.KC.BfsPin (PP)
open scoped commutatorElement

variable {n w : Nat}

theorem eq_bot_of_card_checks {Mg Dg : Nat → Nat} {nm x m : Nat} {RO : List Rec}
    {L : List (Nat × List Nat × List (List Nat) × List Rec)} {WS : List (List Nat)}
    {M : Subgroup (Equiv.Perm (Fin n))}
    (hsz : CFSG.KS.Raw.szOK n w = true) (hm : (L.map fun lv => lv.2.2.2.length).prod = m)
    (hcM : Nat.card M ≤ m)
    (hMg : ∀ k < nm, PP n w (Mg k) ∧ toPerm n w (Mg k) ∈ M)
    (hL : stabLowK n w Mg nm L = true) (hbase : baseInK L (maskK RO) = true)
    (hW : ∀ k < 2, ∃ a b, PP n w a ∧ PP n w b ∧ toPerm n w a ∈ M ∧ toPerm n w b ∈ M ∧
      Dg k = commP n w a b)
    (hN : normK n w Mg nm Dg 2 WS = true) (hO : oddOrbK n w Dg 2 x (maskK RO) RO = true) :
    ∀ Q : Subgroup (Equiv.Perm (Fin n)), IsPGroup 2 Q → Q ≤ ⁅M, M⁆ →
      ⁅M, M⁆ ≤ Subgroup.normalizer (Q : Set (Equiv.Perm (Fin n))) → Q = ⊥ := by
  set M0 := Subgroup.closure (gens n w Mg nm)
  set D := Subgroup.closure (gens n w Dg 2)
  have hMgP : ∀ k < nm, PP n w (Mg k) := fun k hk => (hMg k hk).1
  have hDgP : ∀ k < 2, PP n w (Dg k) := fun k hk => by
    obtain ⟨a, b, ha, hb, -, -, e⟩ := hW k hk
    rw [e]
    exact PP_commP ha hb
  have hM0M : M0 ≤ M := by
    rw [Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    exact (hMg k hk).2
  have hprod : m ≤ Nat.card M0 := hm ▸ prod_le_card_of_stabLowK hsz hMgP hL
  have hM0 : M0 = M := Subgroup.eq_of_le_of_card_ge hM0M (hcM.trans hprod)
  have hm0 : 0 < m := lt_of_lt_of_le Nat.card_pos hcM
  have hMM : ⁅M, M⁆ ≤ M := Subgroup.commutator_le.2 fun a ha b hb => by
    rw [commutatorElement_def]
    exact M.mul_mem (M.mul_mem (M.mul_mem ha hb) (M.inv_mem ha)) (M.inv_mem hb)
  have hDle : D ≤ ⁅M, M⁆ := by
    rw [Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    obtain ⟨a, b, ha, hb, haM, hbM, e⟩ := hW k hk
    rw [SetLike.mem_coe, e, toPerm_commP ha hb]
    exact Subgroup.commutator_mem_commutator haM hbM
  have hMD : ⁅M, M⁆ ≤ D := by
    rw [← hM0]
    exact normK_sound hsz hMgP hDgP hN
  have hDeq : ⁅M, M⁆ = D := le_antisymm hMD hDle
  intro Q hQ hQle hnorm
  rw [hDeq] at hQle hnorm
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2) (G := Q)).1 hQ
  have hQn : ∀ d ∈ D, ∀ q ∈ Q, d * q * d⁻¹ ∈ Q := fun d hd q hq =>
    (Subgroup.mem_normalizer_iff.1 (hnorm hd) q).1 hq
  have hfix := fix_of_oddOrbK hDgP hO hQle hQn hk
  have hQM0 : Q ≤ M0 := by
    rw [hM0]
    exact hQle.trans (hDeq ▸ hMM)
  have hb := stabLowK_bound hsz hMgP hL Q hQM0 fun g hg lv hlv hb => by
    have e := allL_iff.1 hbase lv.1 (List.mem_map_of_mem hlv)
    rw [testBit_maskK] at e
    have := hfix g hg ⟨lv.1, hb⟩ (mem_ptsOf.2 e)
    rwa [Equiv.Perm.smul_def] at this
  rw [hm] at hb
  change m * Nat.card Q ≤ Nat.card M0 at hb
  rw [hM0] at hb
  have h1 : Nat.card Q ≤ 1 := by
    have h2 : m * Nat.card Q ≤ m * 1 := by
      rw [Nat.mul_one]
      exact hb.trans hcM
    exact Nat.le_of_mul_le_mul_left h2 hm0
  exact Subgroup.eq_bot_of_card_le Q h1

end CFSG.KC.PCent

end
