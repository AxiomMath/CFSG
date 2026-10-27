module

public import CFSG.GH74.Generic.BProg.B3.S3HLOTr

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup Equiv Equiv.Perm
open scoped commutatorElement

theorem false_of_bigAlt' {Y : Type} [Group Y] [Finite Y] (hY : Gen4 Y)
    {H Lb : Subgroup Y} (hH : IsComponent H) {n : ℕ} (hn9 : 9 ≤ n) (hn11 : n ≤ 11)
    (hdc : IsDoubleCoverOfAlt ↥H n) {s : Y} (hs : orderOf s = 2) (hsN : s ∈ normalizer (H : Set Y))
    (hLb : IsPCompIn 2 (centralizer ({s} : Set Y) ⊓ H) Lb)
    (hLlay : pLayerOf 2 (centralizer ({s} : Set Y) ⊓ H) = Lb)
    (hLsl2 : HasSL2Model (↥Lb ⧸ pPrimeCore 2 ↥Lb) (fun q => Odd q ∧ 5 ≤ q)) (hne : Lb ≠ H) : False := by
  have hTr := @transpExcl'
  classical
  obtain ⟨-, hZ, he⟩ := hdc
  have hss : s * s = 1 := by
    rw [← pow_two]
    have := pow_orderOf_eq_one s
    rwa [hs] at this
  obtain ⟨q, hqodd, hq5, -, hLqdvd⟩ := S3HLOCard.sl2Quot_card_data hLsl2
  have hLbH : Lb ≤ H := hLb.1.trans inf_le_right
  have hperf : ⁅Lb, Lb⁆ = Lb := GLS.C3.Layer1.Bk.perfect_of_isPCompIn hLb
  have hncLb : ∃ a ∈ Lb, ∃ b ∈ Lb, a * b ≠ b * a :=
    S3SL2Basic.exists_noncomm_of_perfect hperf
      (by have := S3SL2Basic.sl2_card_ge hq5; have := S3HLOCard.le_card_of_dvd hLqdvd; omega)
  have hns : ∃ h ∈ H, s * h ≠ h * s := by
    by_contra hcon
    push Not at hcon
    exact hne (S3SL2Basic.eq_of_centralizes hH.1 hcon hLb hncLb)
  obtain ⟨S⟩ := exists_altSetting hH.1 (by omega) he hss hsN hns
  have hlc : ∀ l : ↥H, (l : Y) ∈ Lb → s * (l : Y) = (l : Y) * s := fun l hl =>
    (mem_centralizer_iff.1 (hLb.1 hl).1 s rfl)
  have hker2 : IsPGroup 2 S.π.ker := by
    rw [S.ker_eq]
    exact IsPGroup.of_card (n := 1) (by rw [hZ]; norm_num)
  by_cases hsH : s ∈ H
  ·
    let sH : ↥H := ⟨s, hsH⟩
    have hsH2 : sH * sH = 1 := Subtype.ext hss
    set σ₁ : Perm (Fin n) := ((S.π sH : alternatingGroup (Fin n)) : Perm (Fin n)) with hσ₁def
    have hσ₁ : σ₁ * σ₁ = 1 := by
      have : S.π sH * S.π sH = 1 := by rw [← map_mul, hsH2, map_one]
      simpa [hσ₁def] using congrArg Subtype.val this
    have hσ₁1 : σ₁ ≠ 1 := by
      intro h1
      have : S.π sH = 1 := Subtype.ext h1
      have hc : sH ∈ center ↥H := (S.mem_ker_iff sH).1 this
      obtain ⟨h, hh, hne'⟩ := hns
      exact hne' (congrArg Subtype.val ((Subgroup.mem_center_iff.1 hc ⟨h, hh⟩).symm))
    have hc : ∀ l : ↥H, (l : Y) ∈ Lb →
        σ₁ * (S.π l : Perm (Fin n)) = (S.π l : Perm (Fin n)) * σ₁ := by
      intro l hl
      have h1 : sH * l = l * sH := Subtype.ext (hlc l hl)
      have := congrArg (fun z => ((S.π z : alternatingGroup (Fin n)) : Perm (Fin n))) h1
      simpa [hσ₁def, map_mul] using this
    have hcon := S3HLOCard.constraint_of_commuting' S hLbH hZ hqodd hq5 hLqdvd hσ₁ hσ₁1 hc
    set k := σ₁.cycleType.card with hk
    have hsupp : σ₁.support.card = 2 * k := S3SL2Perm.card_support_involution hσ₁
    have hle : σ₁.support.card ≤ n := by
      have := Finset.card_le_univ σ₁.support
      simpa using this
    have hk1 : 1 ≤ k := by
      rw [hk, Nat.one_le_iff_ne_zero]
      intro h0
      rw [Multiset.card_eq_zero] at h0
      exact hσ₁1 (Equiv.Perm.cycleType_eq_zero.1 h0)
    have hsign : Perm.sign σ₁ = 1 :=
      (Equiv.Perm.mem_alternatingGroup).1 (S.π sH).2
    have hk_even : Even k := by
      have h1 := S3SL2Perm.sign_involution hσ₁
      rw [hsign] at h1
      exact (neg_one_pow_eq_one_iff_even (by decide)).1 h1.symm
    have hk2 : k = 2 := by
      obtain ⟨m, hm⟩ := hk_even
      omega
    have h4 : σ₁.support.card = 4 := by omega
    obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, hσ₁abcd⟩ :=
      S3SL2Perm.exists_swap_mul_swap hσ₁ h4
    have : Group.IsPerfect ↥H := hH.1.1
    have hsq := S45.LAlt.sq_ne_one_of_lift_swap_mul_swap (P := ↥H) (n := n) (by omega) S.π S.surj
      (by rw [S.ker_eq]) hker2 (by rw [S.ker_eq]; intro h; rw [h] at hZ; simp at hZ) hab hac had hbc hbd
      hcd (x := sH) (by rw [← hσ₁def]; exact hσ₁abcd)
    exact hsq (by rw [pow_two]; exact hsH2)
  ·
    have hn8 : 8 ≤ n := by omega
    rcases Int.units_eq_one_or (Perm.sign S.σ) with heven | hodd
    · exact S3SL2AltGen4.not_gen4_of_outer S hn8 hss hsH 1 (by simp) (by simp [heven])
        (fun i => by simp) hY
    · by_cases hn10 : 10 ≤ n
      · have ha : (⟨8, by omega⟩ : Fin n) ≠ ⟨9, by omega⟩ := by simp [Fin.ext_iff]
        exact S3SL2AltGen4.not_gen4_of_outer S hn8 hss hsH (swap ⟨8, by omega⟩ ⟨9, by omega⟩)
          (swap_mul_self _ _) (by rw [Perm.sign_swap ha, hodd])
          (fun i => S3SL2AltV.swap_mul_vEmb hn8 i (by simp) (by simp)) hY
      · have hn : n = 9 := by omega
        subst hn
        have hc : ∀ l : ↥H, (l : Y) ∈ Lb →
            S.σ * (S.π l : Perm (Fin 9)) = (S.π l : Perm (Fin 9)) * S.σ := fun l hl =>
          S.commute_of_centralizes (hlc l hl)
        have hcon := S3HLOCard.constraint_of_commuting' S hLbH hZ hqodd hq5 hLqdvd S.σ_sq S.σ_ne hc
        set k := S.σ.cycleType.card with hk
        have hsupp : S.σ.support.card = 2 * k := S3SL2Perm.card_support_involution S.σ_sq
        have hle : S.σ.support.card ≤ 9 := by
          have := Finset.card_le_univ S.σ.support
          simpa using this
        have hk1 : 1 ≤ k := by
          rw [hk, Nat.one_le_iff_ne_zero]
          intro h0
          rw [Multiset.card_eq_zero] at h0
          exact S.σ_ne (Equiv.Perm.cycleType_eq_zero.1 h0)
        have hk_odd : Odd k := by
          have h1 := S3SL2Perm.sign_involution S.σ_sq
          rw [hodd] at h1
          exact (neg_one_pow_eq_neg_one_iff_odd (by decide)).1 h1.symm
        have hk1' : k = 1 := by
          obtain ⟨m, hm⟩ := hk_odd
          omega
        have h2 : S.σ.support.card = 2 := by omega
        obtain ⟨a, b, hab, hσab⟩ := Equiv.Perm.card_support_eq_two.1 h2
        exact hTr S hH.1 hZ hss hsH ⟨a, b, hab, hσab⟩ hLb hLlay hLsl2

end CFSG.GH74.Generic.BProg.B3
